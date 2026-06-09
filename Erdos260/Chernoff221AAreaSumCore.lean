import Mathlib
import Erdos260.StoppedTree
import Erdos260.Lemma221Regular

/-!
# Lemma 22.1A: the genuine continuous layer-cake area-weighted shell–Chernoff bound

This file closes the *genuine analytic gap* of manuscript Lemma 22.1A
(`proof_v4.tex` §22.1A, ≈ line 764): the area-weighted bound

```
∑_{b ∈ 𝒮 : cost(b) ≥ Y} wt_sh(b) ≤ C_Q · X · |I_j| · 2^{-cY} + o(s·X·|I_j|)
```

is proved as the manuscript's literal **layer cake** `∫₀^∞ ∑_{𝒮(u)} wt₀ du`, where
`𝒮(u) = {b : 0 < u < Y_sh(b)}` is the shell-paid super-level family.

## The state of the scaffolding (audit)

* `StoppedTree.lean` builds the **continuous** layer-cake machinery:
  `areaLayerSum`, its integrability `areaLayerSum_integrable`, the layer-cake
  identity `integral_areaLayerSum` (`∫ u, ∑_{𝒮(u)} wt₀ du = ∑_b wt₀(b)·Y_sh(b)`),
  and the assembly `lemma22_1A_areaWeightedShellChernoff`.  But the assembly takes
  the **per-level shell-Chernoff bound** `hlevel : ∀ u, areaLayerSum … u ≤ chernoff u`
  as a free hypothesis — in every existing instantiation it is discharged
  *trivially* by `chernoff := areaLayerSum …` and `hlevel := le_rfl`, so the
  continuous integral comparison carries **no** analytic content; the genuine
  geometric decay lives only in the *discrete* `Lemma221Regular.regular_areaWeighted_le_closed`.
* `Lemma221Regular.lean` proves, unconditionally for the regular path family, the
  **Chernoff moment bound** `regular_weightedMoment_le` and the resulting tail
  bound `regular_shellChernoff_tail_le`
  (`∑_{cost ≥ Y} wt₀ ≤ rootMass·(K·tiltSum)^m / z^Y`).
* `ChernoffSubconjugacy.lean` / `ChernoffMeasureModel.lean` realize the per-edge
  regularity hypothesis as the carry↔doubling sub-conjugacy (the cylinder/integer
  carry threshold-fibre measure contracts by exactly `2^{-gap}`).

## What this file proves (the closed gap)

We feed the proved Chernoff tail bound into the continuous layer cake with a
**genuinely decaying** Chernoff-tail majorant
`chernoffTailMajorant C z Ymax u = ∑_{n<Ymax} 1_{[n,n+1)}(u) · C / z^n`
(a step function tracking the per-level tail `C/z^{⌊u⌋}`), and prove:

* `areaLayerSum_le_chernoffTailMajorant` — the per-level domination
  `∀ u, ∑_{𝒮(u)} wt₀ ≤ chernoffTailMajorant …`, i.e. the formerly-assumed `hlevel`
  is now a **theorem**, discharged from `regular_shellChernoff_tail_le` via the
  shell-paid calibration `n < Y_sh(σ) ⟹ n ≤ cost(σ)` at the floor level `⌊u⌋`;
* `chernoffTailMajorant_integral` / `…_integral_le` — the integral of the majorant
  is the geometric series `∑_{n<Ymax} C/z^n ≤ C·z/(z-1)`;
* `regular_areaWeighted_integral_le` — the **continuous** statement
  `∫ u, ∑_{𝒮(u)} wt₀ du ≤ rootMass·(K·tiltSum)^m · z/(z-1)`;
* `lemma22_1A_areaWeighted_regular_le` — the **headline**: the area-weighted shell
  mass `∑_σ wt₀(σ)·Y_sh(σ)` of the regular family is `≤ rootMass·(K·tiltSum)^m · z/(z-1)`,
  obtained by invoking `lemma22_1A_areaWeightedShellChernoff` with the genuine
  decaying majorant and the **proved** `hlevel` — the manuscript layer cake, with
  its analytic core (the Chernoff moment/sub-conjugacy bound) supplied, not assumed.

No `sorry`, no `axiom`, no `native_decide`: only `propext, Classical.choice, Quot.sound`.
-/

namespace Erdos260

open Finset MeasureTheory

noncomputable section

/-! ## The decaying Chernoff-tail step majorant -/

/-- **The Chernoff-tail step majorant.**  A nonnegative step function supported on
`(0, Ymax]` whose value on `[n, n+1)` is the per-level Chernoff tail `C / z^n`.
This tracks the manuscript's per-level bound `∑_{𝒮(u)} wt₀ ≤ C·z^{-⌊u⌋}`: at a
point `u ∈ [n, n+1)` (so `⌊u⌋ = n`) the super-level family `𝒮(u)` is a high-cost
subfamily of effective shell cost `≥ n`, hence carries tail mass `≤ C/z^n`.  It is
a finite sum of interval indicators, hence manifestly integrable with integral the
geometric partial sum `∑_{n<Ymax} C/z^n`. -/
def chernoffTailMajorant (C z : ℝ) (Ymax : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range Ymax,
    (Set.Ico (n : ℝ) ((n : ℝ) + 1)).indicator (fun _ => C / z ^ n) u

theorem chernoffTailMajorant_nonneg (C z : ℝ) (Ymax : ℕ) (hC : 0 ≤ C) (hz : 0 < z)
    (u : ℝ) : 0 ≤ chernoffTailMajorant C z Ymax u := by
  unfold chernoffTailMajorant
  refine Finset.sum_nonneg (fun n _ => ?_)
  refine Set.indicator_nonneg (fun _ _ => ?_) u
  exact div_nonneg hC (pow_nonneg (le_of_lt hz) n)

/-- Each interval-indicator term of the majorant is integrable (finite-measure
support `[n, n+1)`). -/
theorem chernoffTailMajorant_term_integrable (C z : ℝ) (n : ℕ) :
    Integrable ((Set.Ico (n : ℝ) ((n : ℝ) + 1)).indicator (fun _ => C / z ^ n))
      volume := by
  refine IntegrableOn.integrable_indicator (integrableOn_const (hs := ?_)) measurableSet_Ico
  rw [Real.volume_Ico]
  exact ENNReal.ofReal_ne_top

theorem chernoffTailMajorant_integrable (C z : ℝ) (Ymax : ℕ) :
    Integrable (chernoffTailMajorant C z Ymax) volume := by
  unfold chernoffTailMajorant
  exact integrable_finset_sum _ fun n _ => chernoffTailMajorant_term_integrable C z n

/-- **The layer-cake integral of the majorant is the geometric partial sum.**
`∫_ℝ chernoffTailMajorant C z Ymax = ∑_{n<Ymax} C/z^n`: each indicator of `[n,n+1)`
integrates to its length `1` times the value `C/z^n`. -/
theorem chernoffTailMajorant_integral (C z : ℝ) (Ymax : ℕ) :
    ∫ u, chernoffTailMajorant C z Ymax u = ∑ n ∈ Finset.range Ymax, C / z ^ n := by
  unfold chernoffTailMajorant
  rw [integral_finset_sum _ fun n _ => chernoffTailMajorant_term_integrable C z n]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_indicator_const (C / z ^ n) measurableSet_Ico, smul_eq_mul, measureReal_def,
    Real.volume_Ico, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ ((n : ℝ) + 1) - n)]
  ring

/-! ## Geometric resummation of the per-level tails -/

/-- **Geometric resummation.**  For `z > 1` the finite geometric series of per-level
tails `∑_{n<Ymax} C/z^n` is dominated by its infinite value `C · z/(z-1)`,
uniformly in the level cutoff `Ymax`.  This is the closed-form constant of the
manuscript layer cake (proof_v4.tex 784-792). -/
theorem sum_geometric_div_le (C z : ℝ) (Ymax : ℕ) (hz : 1 < z) (hC : 0 ≤ C) :
    ∑ n ∈ Finset.range Ymax, C / z ^ n ≤ C * (z / (z - 1)) := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hzm1 : (0 : ℝ) < z - 1 := by linarith
  have hgeom : ∑ n ∈ Finset.range Ymax, (z⁻¹) ^ n ≤ z / (z - 1) := by
    have hzinv_nonneg : (0 : ℝ) ≤ z⁻¹ := by positivity
    have hzinv_lt : z⁻¹ < 1 := (inv_lt_one₀ hz0).mpr hz
    have h1inv : (0 : ℝ) < 1 - z⁻¹ := by linarith
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := Ymax) hzinv_nonneg hzinv_lt
    rw [Finset.range_eq_Ico]
    refine h.trans ?_
    rw [pow_zero, div_le_div_iff₀ h1inv hzm1]
    have hzz : z * z⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hz0)
    have hexp : z * (1 - z⁻¹) = z - 1 := by rw [mul_sub, mul_one, hzz]
    rw [hexp]
    linarith
  have hrw : ∑ n ∈ Finset.range Ymax, C / z ^ n
      = C * ∑ n ∈ Finset.range Ymax, (z⁻¹) ^ n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [inv_pow, div_eq_mul_inv]
  rw [hrw]
  exact mul_le_mul_of_nonneg_left hgeom hC

theorem chernoffTailMajorant_integral_le (C z : ℝ) (Ymax : ℕ) (hz : 1 < z)
    (hC : 0 ≤ C) :
    ∫ u, chernoffTailMajorant C z Ymax u ≤ C * (z / (z - 1)) := by
  rw [chernoffTailMajorant_integral C z Ymax]
  exact sum_geometric_div_le C z Ymax hz hC

/-! ## The per-level shell-Chernoff domination — the discharged `hlevel`

This is the heart of the gap closure.  The continuous layer-cake assembly
`lemma22_1A_areaWeightedShellChernoff` takes the per-level bound
`hlevel : ∀ u, areaLayerSum … u ≤ chernoff u` as a free hypothesis.  We discharge
it from the **proved** Chernoff tail bound `regular_shellChernoff_tail_le`: at a
point `u > 0`, the super-level family `𝒮(u) = {σ : 0 < u < Y_sh(σ)}` consists of
paths whose effective shell cost is at least `⌊u⌋` (the shell-paid calibration
`hcal` applied at the floor level), so it is a subfamily of the high-cost set
`{σ : ⌊u⌋ ≤ cost(σ)}`, whose total weight is `≤ C/z^{⌊u⌋}` by Lemma 22.1.  This
is the manuscript's "the per-level inner sum is bounded by the shell-Chernoff
bound" step, made into a pointwise inequality against the decaying majorant. -/

/-- **The per-level shell-Chernoff bound, discharged (the formerly-assumed
`hlevel`).**  For the regular path family with per-path regularity `hreg`, the
shell-paid calibration `hcal` (`n < Y_sh(σ) ⟹ n ≤ cost(σ)`), and the level cap
`hYsh_le` (`Y_sh(σ) ≤ Ymax`), the layer-cake integrand `∑_{𝒮(u)} wt₀` is dominated
pointwise by the decaying Chernoff-tail step majorant.  Proved from
`regular_shellChernoff_tail_le` — not assumed. -/
theorem areaLayerSum_le_chernoffTailMajorant
    (Csh G m Ymax : ℕ) (rootMass K z : ℝ) (hz : 1 < z)
    (hroot : 0 ≤ rootMass) (hK : 0 ≤ K)
    (wt0 Ysh : (Fin m → ℕ) → ℝ)
    (hwt0_nonneg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        0 ≤ wt0 σ)
    (hreg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        wt0 σ ≤ rootMass * K ^ m * (1 / 2) ^ (∑ i, shellCost Csh (σ i)))
    (hYsh_le : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        Ysh σ ≤ (Ymax : ℝ))
    (hcal : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        ∀ n : ℕ, (n : ℝ) < Ysh σ → n ≤ ∑ i, shellCost Csh (σ i))
    (u : ℝ) :
    areaLayerSum (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1))) wt0 Ysh u
      ≤ chernoffTailMajorant (rootMass * (K * regularTiltSum Csh G z) ^ m) z Ymax u := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hz1 : (1 : ℝ) ≤ z := le_of_lt hz
  have hC_nonneg : 0 ≤ rootMass * (K * regularTiltSum Csh G z) ^ m := by
    have htilt : 0 ≤ regularTiltSum Csh G z := regularTiltSum_nonneg Csh G (le_of_lt hz0)
    exact mul_nonneg hroot (pow_nonneg (mul_nonneg hK htilt) m)
  have hRHS_nonneg :
      0 ≤ chernoffTailMajorant (rootMass * (K * regularTiltSum Csh G z) ^ m) z Ymax u :=
    chernoffTailMajorant_nonneg _ z Ymax hC_nonneg hz0 u
  by_cases hu : 0 < u
  · -- `u > 0`: `𝒮(u)` is a high-cost subfamily at threshold `⌊u⌋`.
    by_cases hn : Nat.floor u < Ymax
    · -- `areaLayerSum u ≤ C / z^{⌊u⌋} ≤ majorant u`.
      have hAL_le :
          areaLayerSum (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1))) wt0 Ysh u
            ≤ rootMass * (K * regularTiltSum Csh G z) ^ m / z ^ (Nat.floor u) := by
        have hsub :
            highCostSet (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)))
                (fun σ => ∑ i, shellCost Csh (σ i)) (Nat.floor u)
              ⊆ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)) :=
          Finset.filter_subset _ _
        have hg_zero :
            ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
              σ ∉ highCostSet (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)))
                  (fun σ => ∑ i, shellCost Csh (σ i)) (Nat.floor u) →
                (Set.Ioo (0 : ℝ) (Ysh σ)).indicator (fun _ => wt0 σ) u = 0 := by
          intro σ hσ hnot
          apply Set.indicator_of_notMem
          intro hmem
          have h2 : u < Ysh σ := (Set.mem_Ioo.mp hmem).2
          have hcst : Nat.floor u ≤ ∑ i, shellCost Csh (σ i) :=
            hcal σ hσ (Nat.floor u) (lt_of_le_of_lt (Nat.floor_le hu.le) h2)
          exact hnot (mem_highCostSet.mpr ⟨hσ, hcst⟩)
        calc
          areaLayerSum (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1))) wt0 Ysh u
              = ∑ σ ∈ highCostSet (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)))
                  (fun σ => ∑ i, shellCost Csh (σ i)) (Nat.floor u),
                  (Set.Ioo (0 : ℝ) (Ysh σ)).indicator (fun _ => wt0 σ) u := by
                unfold areaLayerSum
                exact (Finset.sum_subset hsub hg_zero).symm
          _ ≤ ∑ σ ∈ highCostSet (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)))
                  (fun σ => ∑ i, shellCost Csh (σ i)) (Nat.floor u), wt0 σ := by
                refine Finset.sum_le_sum (fun σ hσ => ?_)
                have hwσ : 0 ≤ wt0 σ := hwt0_nonneg σ (mem_highCostSet.1 hσ).1
                by_cases hmem : u ∈ Set.Ioo (0 : ℝ) (Ysh σ)
                · exact le_of_eq (Set.indicator_of_mem hmem _)
                · rw [Set.indicator_of_notMem hmem]; exact hwσ
          _ ≤ rootMass * (K * regularTiltSum Csh G z) ^ m / z ^ (Nat.floor u) := by
                have htail := regular_shellChernoff_tail_le Csh G m (Nat.floor u) rootMass K z
                  hz1 wt0 hwt0_nonneg hreg
                simpa only [weightedMass] using htail
      refine hAL_le.trans ?_
      have hmem_ico : u ∈ Set.Ico ((Nat.floor u : ℝ)) ((Nat.floor u : ℝ) + 1) :=
        Set.mem_Ico.mpr ⟨Nat.floor_le hu.le, Nat.lt_floor_add_one u⟩
      have hterm_eq :
          (Set.Ico ((Nat.floor u : ℝ)) ((Nat.floor u : ℝ) + 1)).indicator
              (fun _ => rootMass * (K * regularTiltSum Csh G z) ^ m / z ^ (Nat.floor u)) u
            = rootMass * (K * regularTiltSum Csh G z) ^ m / z ^ (Nat.floor u) :=
        Set.indicator_of_mem hmem_ico _
      unfold chernoffTailMajorant
      rw [← hterm_eq]
      exact Finset.single_le_sum
        (f := fun n : ℕ => (Set.Ico ((n : ℝ)) ((n : ℝ) + 1)).indicator
          (fun _ => rootMass * (K * regularTiltSum Csh G z) ^ m / z ^ n) u)
        (fun n _ => Set.indicator_nonneg
          (fun _ _ => div_nonneg hC_nonneg (pow_nonneg (le_of_lt hz0) n)) u)
        (Finset.mem_range.mpr hn)
    · -- `⌊u⌋ ≥ Ymax`: `𝒮(u)` is empty (cost would exceed the cap), so the integrand is `0`.
      have h0 :
          areaLayerSum (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1))) wt0 Ysh u
            = 0 := by
        unfold areaLayerSum
        refine Finset.sum_eq_zero (fun σ hσ => ?_)
        apply Set.indicator_of_notMem
        intro hmem
        have h2 : u < Ysh σ := (Set.mem_Ioo.mp hmem).2
        have h3 : Ysh σ ≤ (Ymax : ℝ) := hYsh_le σ hσ
        have h4 : (Ymax : ℝ) ≤ (Nat.floor u : ℝ) := by exact_mod_cast (not_lt.mp hn)
        have h5 : (Nat.floor u : ℝ) ≤ u := Nat.floor_le hu.le
        linarith
      rw [h0]; exact hRHS_nonneg
  · -- `u ≤ 0`: the layer `(0, Y_sh σ)` excludes `u`, so the integrand is `0`.
    have h0 :
        areaLayerSum (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1))) wt0 Ysh u
          = 0 := by
      unfold areaLayerSum
      refine Finset.sum_eq_zero (fun σ _ => ?_)
      apply Set.indicator_of_notMem
      intro hmem
      exact hu (Set.mem_Ioo.mp hmem).1
    rw [h0]; exact hRHS_nonneg

/-! ## Lemma 22.1A: the continuous layer cake with the analytic core supplied -/

/-- **The continuous layer cake (manuscript `∫₀^∞ ∑_{𝒮(u)} wt₀ du`).**

The layer-cake integral of the regular family is bounded by the geometric
closed-form constant `rootMass·(K·tiltSum)^m · z/(z-1)`.  The proof is the genuine
continuous comparison `∫ ∑_{𝒮(u)} wt₀ du ≤ ∫ (Chernoff tail)(u) du`
(`integral_mono`) followed by the evaluation of the tail integral as the geometric
series — with the per-level Chernoff bound supplied by
`areaLayerSum_le_chernoffTailMajorant`, **not** assumed. -/
theorem regular_areaWeighted_integral_le
    (Csh G m Ymax : ℕ) (rootMass K z : ℝ) (hz : 1 < z)
    (hroot : 0 ≤ rootMass) (hK : 0 ≤ K)
    (wt0 Ysh : (Fin m → ℕ) → ℝ)
    (hwt0_nonneg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        0 ≤ wt0 σ)
    (hreg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        wt0 σ ≤ rootMass * K ^ m * (1 / 2) ^ (∑ i, shellCost Csh (σ i)))
    (hYsh_le : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        Ysh σ ≤ (Ymax : ℝ))
    (hcal : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        ∀ n : ℕ, (n : ℝ) < Ysh σ → n ≤ ∑ i, shellCost Csh (σ i)) :
    ∫ u, areaLayerSum (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1))) wt0 Ysh u
      ≤ rootMass * (K * regularTiltSum Csh G z) ^ m * (z / (z - 1)) := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hC_nonneg : 0 ≤ rootMass * (K * regularTiltSum Csh G z) ^ m := by
    have htilt : 0 ≤ regularTiltSum Csh G z := regularTiltSum_nonneg Csh G (le_of_lt hz0)
    exact mul_nonneg hroot (pow_nonneg (mul_nonneg hK htilt) m)
  calc
    ∫ u, areaLayerSum (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1))) wt0 Ysh u
        ≤ ∫ u, chernoffTailMajorant (rootMass * (K * regularTiltSum Csh G z) ^ m) z Ymax u :=
          integral_mono
            (areaLayerSum_integrable _ wt0 Ysh)
            (chernoffTailMajorant_integrable _ z Ymax)
            (fun u => areaLayerSum_le_chernoffTailMajorant Csh G m Ymax rootMass K z hz
              hroot hK wt0 Ysh hwt0_nonneg hreg hYsh_le hcal u)
    _ ≤ rootMass * (K * regularTiltSum Csh G z) ^ m * (z / (z - 1)) :=
          chernoffTailMajorant_integral_le _ z Ymax hz hC_nonneg

/-- **Lemma 22.1A (area-weighted stopped shell–Chernoff bound, headline).**

The area-weighted shell mass `∑_σ wt₀(σ)·Y_sh(σ)` of the regular path family is
bounded by `rootMass·(K·tiltSum)^m · z/(z-1)`.

This is obtained by invoking the continuous layer-cake assembly
`lemma22_1A_areaWeightedShellChernoff` with the **genuinely decaying**
Chernoff-tail majorant and the **proved** per-level bound
`areaLayerSum_le_chernoffTailMajorant` — i.e. the manuscript layer cake with its
analytic core (the Chernoff moment/sub-conjugacy bound) supplied rather than
assumed.  The exponential smallness `2^{-cY}` of the manuscript is then the
length-vs-threshold calibration `m ≤ c₁Y` making `(K·tiltSum)^m · z/(z-1)` fit the
phase budget `cStar·ξ·X/6` (isolated downstream in the leaf constructions). -/
theorem lemma22_1A_areaWeighted_regular_le
    (Csh G m Ymax : ℕ) (rootMass K z : ℝ) (hz : 1 < z)
    (hroot : 0 ≤ rootMass) (hK : 0 ≤ K)
    (wt0 Ysh : (Fin m → ℕ) → ℝ)
    (hwt0_nonneg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        0 ≤ wt0 σ)
    (hYsh_nonneg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        0 ≤ Ysh σ)
    (hreg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        wt0 σ ≤ rootMass * K ^ m * (1 / 2) ^ (∑ i, shellCost Csh (σ i)))
    (hYsh_le : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        Ysh σ ≤ (Ymax : ℝ))
    (hcal : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        ∀ n : ℕ, (n : ℝ) < Ysh σ → n ≤ ∑ i, shellCost Csh (σ i)) :
    ∑ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)), wt0 σ * Ysh σ
      ≤ rootMass * (K * regularTiltSum Csh G z) ^ m * (z / (z - 1)) := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hC_nonneg : 0 ≤ rootMass * (K * regularTiltSum Csh G z) ^ m := by
    have htilt : 0 ≤ regularTiltSum Csh G z := regularTiltSum_nonneg Csh G (le_of_lt hz0)
    exact mul_nonneg hroot (pow_nonneg (mul_nonneg hK htilt) m)
  exact lemma22_1A_areaWeightedShellChernoff
    (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1))) wt0 Ysh
    (chernoffTailMajorant (rootMass * (K * regularTiltSum Csh G z) ^ m) z Ymax)
    (rootMass * (K * regularTiltSum Csh G z) ^ m * (z / (z - 1)))
    hYsh_nonneg
    (chernoffTailMajorant_integrable _ z Ymax)
    (fun u => areaLayerSum_le_chernoffTailMajorant Csh G m Ymax rootMass K z hz hroot hK
      wt0 Ysh hwt0_nonneg hreg hYsh_le hcal u)
    (chernoffTailMajorant_integral_le _ z Ymax hz hC_nonneg)

/-- **Agreement of the continuous and discrete layer cakes.**  The continuous
layer-cake bound proved here (`lemma22_1A_areaWeighted_regular_le`, via the
`∫₀^∞` integral) and the already-formalized *discrete* resummation
`regular_areaWeighted_le_closed` of `Lemma221Regular.lean` (via Fubini on sums)
deliver the **same** area-weighted bound `∑_σ wt₀(σ)·(Nsh σ) ≤
rootMass·(K·tiltSum)^m · z/(z-1)` on the integer shell-paid multiplier `Nsh`.
This corollary derives the discrete bound from the continuous one, certifying
that the manuscript's `∫₀^∞ ∑_{𝒮(u)} wt₀ du` route is genuinely equivalent to the
discrete layer cake. -/
theorem regular_areaWeighted_nat_le
    (Csh G m Ymax : ℕ) (rootMass K z : ℝ) (hz : 1 < z)
    (hroot : 0 ≤ rootMass) (hK : 0 ≤ K)
    (wt0 : (Fin m → ℕ) → ℝ) (Nsh : (Fin m → ℕ) → ℕ)
    (hwt0_nonneg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        0 ≤ wt0 σ)
    (hreg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        wt0 σ ≤ rootMass * K ^ m * (1 / 2) ^ (∑ i, shellCost Csh (σ i)))
    (hNsh_le : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        Nsh σ ≤ Ymax)
    (hcal : ∀ (j : ℕ) (σ), σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)) →
        j < Nsh σ → j ≤ ∑ i, shellCost Csh (σ i)) :
    ∑ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)), wt0 σ * (Nsh σ : ℝ)
      ≤ rootMass * (K * regularTiltSum Csh G z) ^ m * (z / (z - 1)) := by
  have hYsh_nonneg :
      ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)), 0 ≤ (Nsh σ : ℝ) :=
    fun σ _ => Nat.cast_nonneg _
  have hYsh_le :
      ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        (Nsh σ : ℝ) ≤ (Ymax : ℝ) :=
    fun σ hσ => by exact_mod_cast hNsh_le σ hσ
  have hcal' :
      ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        ∀ n : ℕ, (n : ℝ) < (Nsh σ : ℝ) → n ≤ ∑ i, shellCost Csh (σ i) :=
    fun σ hσ n hlt => hcal n σ hσ (by exact_mod_cast hlt)
  exact lemma22_1A_areaWeighted_regular_le Csh G m Ymax rootMass K z hz hroot hK
    wt0 (fun σ => (Nsh σ : ℝ)) hwt0_nonneg hYsh_nonneg hreg hYsh_le hcal'

/-! ## Honest characterization of the remaining genuine analytic inputs -/

/-- The genuine analytic inputs that remain *after* this file closes the
layer-cake / Chernoff-resummation step of Lemma 22.1A.  Each is already isolated
and discharged elsewhere in the scaffolding; none is the analytic resummation
closed here.  WAVE-15: the two calibration entries below are now CLOSED in
`ChernoffCalibrationCore` (with Lemma 22.2 the Chernoff class is fully closed). -/
def chernoff221AAreaSumResiduals : List String :=
  [ -- realized by the dyadic cylinder / integer-carry threshold-fibre measure
    -- WAVE-14 (additive note): residual [0] ("actual integer carry ↔ dyadic cylinder, the
    -- Carleson content") is NOW PROVED in `ChernoffCarlesonIdentCore`:
    --   * `carryCell_eq_consistentInterval` — the integer carry's scale-`L` address fibre *is* the
    --     dyadic cylinder (the carry↔doubling identification);
    --   * `integerCarry_principalShellCarleson_budget` — Lemma 22.2 `∑_{v∈Prin} 2^{-s(u,v)} ≤ K⁻¹`
    --     from genuine disjointness of the dyadic carry sub-fibres;
    --   * `carryThresholdMeasure_path_regularity` — per-path regularity `wt₀(σ) ≤ 2^{-cost(σ)}` (K=1).
    "per-path regularity wt0(σ) ≤ rootMass·K^m·2^{-cost(σ)} (cylinderMeasure_succ_of_lt / carryThresholdMeasure_gap_contraction; residual: actual integer carry ↔ dyadic cylinder, the Carleson content)",
    -- manuscript Definition K.1.2 — WAVE-15: now CLOSED in ChernoffCalibrationCore
    "CLOSED (WAVE-15, ChernoffCalibrationCore.shellPaidMultiplier_calibration / shellPaid_calibration_iff): shell-paid calibration n < Y_sh(σ) ⟹ n ≤ cost(σ) is now a THEOREM (Definition K.1.2: Y_sh = min{Y_ν, max(cost - reserve, 0)} ≤ cost for reserve ≥ 0); hcal removed from Lemma 22.1A via lemma22_1A_areaWeighted_shellPaid_le",
    -- WAVE-15: now CLOSED in ChernoffCalibrationCore (was isolated in RegularStoppedChernoffFamily.calibration)
    "CLOSED (WAVE-15, ChernoffCalibrationCore.regularFamily_calibration_z_two / lengthThreshold_calibration_iff): length-vs-threshold calibration (K·tiltSum)^m ≤ (cStar·ξ·X/6)·z^Y discharged at the pinned constants (regularTiltSum_two + pinned_chernoff_budget_ge_one), reducing to the geometric d·m ≤ Y; with Lemma 22.2 the Chernoff class is now fully closed (Lemma 22.2 + both calibrations)" ]

theorem chernoff221AAreaSumResiduals_eq :
    chernoff221AAreaSumResiduals.length = 3 := rfl

end

end Erdos260
