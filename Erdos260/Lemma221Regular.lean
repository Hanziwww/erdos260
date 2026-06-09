import Mathlib
import Erdos260.StoppedInduction
import Erdos260.StoppedTree
import Erdos260.AppendixG_Chernoff

/-!
# Lemma 22.1 (faithful analytic core): the regular-path shell-Chernoff moment and tail

This file proves the analytic heart of manuscript Lemma 22.1 (`proof_v4.tex`
lines 721-748) as a genuine, unconditional theorem: no `sorry`, no `axiom`, and
no manuscript hypothesis beyond the *definition* of a regular path.

A regular length-`m` path over the bounded gap alphabet `{0, …, G}` satisfies, by
the manuscript definition of a regular edge/path (proof_v4.tex 717-719, 732-734),
the mass bound
`weight(π) ≤ rootMass · K^m · 2^{-cost(π)}`,  where  `cost(π) = ∑ s(e)`.

We prove the tilted-moment factorization
`∑_π weight(π)·z^{cost(π)} ≤ rootMass · (K · tiltSum)^m`,
where `tiltSum = ∑_{h ≤ G} (z/2)^{s(h)}` is the convergent regular-edge tilt sum
(`regular_edge_tilt_sum_le`, already in `StoppedTree`).  This is the previously
missing combinatorial step of Lemma 22.1: the per-edge tilt bound multiplies
across the `m` edges of the tree, and the sum over the length-`m` path family
factors as the `m`-th power of the single-edge tilt sum.

Combining with the generic Chernoff inequality
`shellChernoff_bound_of_moment_bound` (already in `StoppedInduction`) yields the
manuscript tail bound
`∑_{π : cost ≥ Y} weight(π) ≤ rootMass · (K·tiltSum)^m / z^Y`.

The remaining content of Lemma 22.1 — that the carry stopped branches *are*
regular with these masses — is the genuinely geometric input (the definition of
regularity in the manuscript dynamics); it is not asserted here.
-/

namespace Erdos260

open Finset

noncomputable section

/-- The regular-edge tilt sum over the bounded gap alphabet `{0, …, G}`:
`∑_{h ≤ G} (z/2)^{shellCost Csh h}`.  This is the single-edge factor of the
Lemma 22.1 moment computation. -/
def regularTiltSum (Csh G : ℕ) (z : ℝ) : ℝ :=
  ∑ h ∈ Finset.range (G + 1), (z / 2) ^ shellCost Csh h

theorem regularTiltSum_nonneg (Csh G : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ regularTiltSum Csh G z := by
  unfold regularTiltSum
  refine Finset.sum_nonneg ?_
  intro h _
  have : 0 ≤ z / 2 := by linarith
  positivity

/-- The regular-edge tilt sum is bounded uniformly in the gap cutoff `G`, by the
finiteness of the geometric tail for `z < 2`.  This is the convergence input of
Lemma 22.1 (proof_v4.tex 744-748), supplied by `regular_edge_tilt_sum_le`. -/
theorem regularTiltSum_le (Csh G : ℕ) {z : ℝ} (hz0 : 0 ≤ z) (hz2 : z < 2) :
    regularTiltSum Csh G z ≤ ((Csh : ℝ) + 1) + (1 - z / 2)⁻¹ := by
  unfold regularTiltSum shellCost
  have hw0 : 0 ≤ z / 2 := by linarith
  have hw1 : z / 2 < 1 := by linarith
  exact regular_edge_tilt_sum_le hw0 hw1 Csh (G + 1)

/-- **Lemma 22.1 (regular-path mass bound, faithful).**

The manuscript definition of a regular edge `u → v` is `|Ω_v| ≤ K·|Ω_u|·2^{-s(e)}`
(proof_v4.tex 717-719).  Telescoping along the `m` edges of a path gives the
per-path mass bound `|Ω_π| ≤ |Ω_root|·K^m·2^{-cost(π)}` (proof_v4.tex 732-734),
which is exactly the regularity hypothesis consumed by the moment factorization
below.  Here `mass k` is `|Ω|` of the length-`k` prefix and `σ k` is the gap
height of the `k`-th edge.  This is a pure, unconditional telescoping. -/
theorem regular_path_mass_le_of_edge
    (Csh : ℕ) (K rootMass : ℝ) (hK : 0 ≤ K)
    (σ : ℕ → ℕ) (mass : ℕ → ℝ)
    (hmass0 : mass 0 ≤ rootMass) :
    ∀ m, (∀ k, k < m → mass (k + 1) ≤ K * mass k * (1 / 2) ^ shellCost Csh (σ k)) →
      mass m ≤ rootMass * K ^ m * (1 / 2) ^ (∑ k ∈ Finset.range m, shellCost Csh (σ k)) := by
  intro m
  induction m with
  | zero => intro _; simpa using hmass0
  | succ n ih =>
    intro hedge
    have ihn := ih (fun k hk => hedge k (by omega))
    have hstep := hedge n (by omega)
    have hfac_nonneg : 0 ≤ K * (1 / 2) ^ shellCost Csh (σ n) := by positivity
    calc mass (n + 1)
        ≤ K * mass n * (1 / 2) ^ shellCost Csh (σ n) := hstep
      _ = (K * (1 / 2) ^ shellCost Csh (σ n)) * mass n := by ring
      _ ≤ (K * (1 / 2) ^ shellCost Csh (σ n))
            * (rootMass * K ^ n
              * (1 / 2) ^ (∑ k ∈ Finset.range n, shellCost Csh (σ k))) :=
            mul_le_mul_of_nonneg_left ihn hfac_nonneg
      _ = rootMass * K ^ (n + 1)
            * (1 / 2) ^ (∑ k ∈ Finset.range (n + 1), shellCost Csh (σ k)) := by
            rw [Finset.sum_range_succ, pow_succ, pow_add]
            ring

/-- **Lemma 22.1 (moment form, faithful).**

For the family of regular length-`m` paths over the gap alphabet `{0,…,G}`, with
the manuscript per-path regularity `weight σ ≤ rootMass · K^m · (1/2)^{cost σ}`
(`cost σ = ∑ᵢ shellCost Csh (σ i)`), the tilted exponential moment is bounded by
`rootMass · (K · tiltSum)^m`.

The proof multiplies the per-edge tilt bound across the `m` edges and uses the
product-of-sums factorization `∑_σ ∏ᵢ f(σ i) = (∑_h f h)^m`. -/
theorem regular_weightedMoment_le
    (Csh G m : ℕ) (rootMass K z : ℝ)
    (hz0 : 0 ≤ z)
    (weight : (Fin m → ℕ) → ℝ)
    (hreg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        weight σ ≤ rootMass * K ^ m * (1 / 2) ^ (∑ i, shellCost Csh (σ i))) :
    weightedMoment (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)))
        weight (fun σ => ∑ i, shellCost Csh (σ i)) z
      ≤ rootMass * (K * regularTiltSum Csh G z) ^ m := by
  classical
  unfold weightedMoment regularTiltSum
  -- Per-path step: weight σ · z^{cost σ} ≤ rootMass · ∏ᵢ (K · (z/2)^{s(σ i)}).
  have hstep : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
      weight σ * z ^ (∑ i, shellCost Csh (σ i))
        ≤ rootMass * ∏ i : Fin m, (K * (z / 2) ^ shellCost Csh (σ i)) := by
    intro σ hσ
    have hzc : (0 : ℝ) ≤ z ^ (∑ i, shellCost Csh (σ i)) := by positivity
    have hprod :
        rootMass * (K ^ m * (z / 2) ^ (∑ i, shellCost Csh (σ i)))
          = rootMass * ∏ i : Fin m, (K * (z / 2) ^ shellCost Csh (σ i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← Finset.prod_pow_eq_pow_sum]
    calc weight σ * z ^ (∑ i, shellCost Csh (σ i))
        ≤ (rootMass * K ^ m * (1 / 2) ^ (∑ i, shellCost Csh (σ i)))
            * z ^ (∑ i, shellCost Csh (σ i)) :=
          mul_le_mul_of_nonneg_right (hreg σ hσ) hzc
      _ = rootMass * (K ^ m
            * ((1 / 2) ^ (∑ i, shellCost Csh (σ i)) * z ^ (∑ i, shellCost Csh (σ i)))) := by
            ring
      _ = rootMass * (K ^ m * (z / 2) ^ (∑ i, shellCost Csh (σ i))) := by
            rw [← mul_pow]
            congr 2
            ring
      _ = rootMass * ∏ i : Fin m, (K * (z / 2) ^ shellCost Csh (σ i)) := hprod
  calc ∑ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
          weight σ * z ^ (∑ i, shellCost Csh (σ i))
      ≤ ∑ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
          rootMass * ∏ i : Fin m, (K * (z / 2) ^ shellCost Csh (σ i)) :=
        Finset.sum_le_sum hstep
    _ = rootMass * ∑ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
          ∏ i : Fin m, (K * (z / 2) ^ shellCost Csh (σ i)) := by
        rw [Finset.mul_sum]
    _ = rootMass * ∏ i : Fin m, ∑ h ∈ Finset.range (G + 1),
          (K * (z / 2) ^ shellCost Csh h) := by
        congr 1
        exact (Finset.prod_univ_sum (fun _ : Fin m => Finset.range (G + 1))
          (fun (_ : Fin m) (h : ℕ) => K * (z / 2) ^ shellCost Csh h)).symm
    _ = rootMass * (K * ∑ h ∈ Finset.range (G + 1), (z / 2) ^ shellCost Csh h) ^ m := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.mul_sum]

/-- **Lemma 22.1 (tail form, faithful).**

The total regular-path mass above the shell-cost threshold `Y` is bounded by the
Chernoff tail `rootMass · (K·tiltSum)^m / z^Y`.  This is the boxed inequality
(22.1) with the constant `2^{-c'Y}` realized as `(K·tiltSum)^m / z^Y`; the final
exponential smallness follows from the length calibration `m ≤ c₁Y` (which makes
`(K·tiltSum)^m` sub-exponential against `z^Y`). -/
theorem regular_shellChernoff_tail_le
    (Csh G m Y : ℕ) (rootMass K z : ℝ)
    (hz : 1 ≤ z)
    (weight : (Fin m → ℕ) → ℝ)
    (hweight_nonneg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        0 ≤ weight σ)
    (hreg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        weight σ ≤ rootMass * K ^ m * (1 / 2) ^ (∑ i, shellCost Csh (σ i))) :
    weightedMass
        (highCostSet (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)))
          (fun σ => ∑ i, shellCost Csh (σ i)) Y) weight
      ≤ rootMass * (K * regularTiltSum Csh G z) ^ m / z ^ Y := by
  have hz0 : (0 : ℝ) ≤ z := by linarith
  exact shellChernoff_bound_of_moment_bound hweight_nonneg hz
    (regular_weightedMoment_le Csh G m rootMass K z hz0 weight hreg)

/-- **Budget bridge.**  If the calibrated moment fits the phase budget, i.e.
`rootMass · (K·tiltSum)^m ≤ budget · z^Y` (the manuscript form of `m ≤ c₁Y`),
then the regular shell-Chernoff tail is at most `budget`.  This is the exact
shape consumed by the Chernoff phase slot `Regular ≤ cStar·ξ·X/6`. -/
theorem regular_shellChernoff_tail_le_budget
    (Csh G m Y : ℕ) (rootMass K z budget : ℝ)
    (hz : 1 ≤ z)
    (weight : (Fin m → ℕ) → ℝ)
    (hweight_nonneg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        0 ≤ weight σ)
    (hreg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        weight σ ≤ rootMass * K ^ m * (1 / 2) ^ (∑ i, shellCost Csh (σ i)))
    (hcal : rootMass * (K * regularTiltSum Csh G z) ^ m ≤ budget * z ^ Y) :
    weightedMass
        (highCostSet (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)))
          (fun σ => ∑ i, shellCost Csh (σ i)) Y) weight
      ≤ budget := by
  have hzY : (0 : ℝ) < z ^ Y := by
    have : (0 : ℝ) < z := by linarith
    positivity
  have htail := regular_shellChernoff_tail_le Csh G m Y rootMass K z
    hz weight hweight_nonneg hreg
  have hcal' : rootMass * (K * regularTiltSum Csh G z) ^ m / z ^ Y ≤ budget := by
    rw [div_le_iff₀ hzY]
    exact hcal
  exact htail.trans hcal'

/-- **Lemma 22.1b (per-level shell-Chernoff bound, faithful).**

The superlevel family `𝒮(u) = {b : Y_sh(b) > u}` of the regular path family has
total base mass at most the Chernoff tail.  The only extra input is the
shell-paid calibration `Y_sh(b) > u ⟹ cost(b) ≥ Y` (Definition K.1.2: membership
in `𝒮(u)` forces effective new-shell cost at least the threshold), which makes
`𝒮(u)` a high-cost subfamily so Lemma 22.1 applies.  This is exactly the per-level
input `hlevel` consumed by the layer-cake `lemma22_1A_areaWeightedShellChernoff`. -/
theorem regular_shellChernoff_perLevel_le
    (Csh G m Y : ℕ) (rootMass K z : ℝ) (u : ℝ)
    (hz : 1 ≤ z)
    (wt0 Ysh : (Fin m → ℕ) → ℝ)
    (hwt0_nonneg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        0 ≤ wt0 σ)
    (hreg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        wt0 σ ≤ rootMass * K ^ m * (1 / 2) ^ (∑ i, shellCost Csh (σ i)))
    (hsuper : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        u < Ysh σ → Y ≤ ∑ i, shellCost Csh (σ i)) :
    ∑ σ ∈ (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1))).filter
        (fun σ => u < Ysh σ), wt0 σ
      ≤ rootMass * (K * regularTiltSum Csh G z) ^ m / z ^ Y := by
  have hsubset :
      (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1))).filter (fun σ => u < Ysh σ)
        ⊆ highCostSet (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)))
            (fun σ => ∑ i, shellCost Csh (σ i)) Y := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [mem_highCostSet]
    exact ⟨hσ.1, hsuper σ hσ.1 hσ.2⟩
  have hmono :
      ∑ σ ∈ (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1))).filter
          (fun σ => u < Ysh σ), wt0 σ
        ≤ ∑ σ ∈ highCostSet (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)))
            (fun σ => ∑ i, shellCost Csh (σ i)) Y, wt0 σ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro σ hσ _
    exact hwt0_nonneg σ (mem_highCostSet.1 hσ).1
  refine hmono.trans ?_
  exact regular_shellChernoff_tail_le Csh G m Y rootMass K z hz wt0 hwt0_nonneg hreg

/-- **Explicit exponential decay (faithful `2^{-c'Y}` form).**

The length condition `m ≤ c₁Y` of Lemma 22.1 forces the moment exponent
`B^m = (K·tiltSum)^m` to undershoot the threshold power `z^Y`.  Quantitatively,
if `B^m ≤ z^a` with `a ≤ Y`, the tail decays like `z^{-(Y-a)}`: this is the
manuscript's boxed `2^{-c'Y}` with `c' = (Y-a)/Y` and base `z`. -/
theorem regular_tail_decay
    (m Y a : ℕ) (rootMass B z : ℝ)
    (hz : 1 ≤ z) (hroot : 0 ≤ rootMass)
    (hBm : B ^ m ≤ z ^ a) (haY : a ≤ Y) :
    rootMass * B ^ m / z ^ Y ≤ rootMass / z ^ (Y - a) := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hza : (0 : ℝ) < z ^ a := by positivity
  have hzY : (0 : ℝ) < z ^ Y := by positivity
  have hzYa : (0 : ℝ) < z ^ (Y - a) := by positivity
  have hsplit : z ^ Y = z ^ a * z ^ (Y - a) := by
    rw [← pow_add]; congr 1; omega
  have h1 : rootMass * B ^ m ≤ rootMass * z ^ a :=
    mul_le_mul_of_nonneg_left hBm hroot
  have hstep : rootMass * B ^ m / z ^ Y ≤ rootMass * z ^ a / z ^ Y :=
    (div_le_div_iff_of_pos_right hzY).mpr h1
  have heq : rootMass * z ^ a / z ^ Y = rootMass / z ^ (Y - a) := by
    rw [hsplit]
    field_simp
  rw [heq] at hstep
  exact hstep

/-- **Lemma 22.1A (area-weighted stopped shell-Chernoff bound, faithful).**

The area-weighted shell mass `∑_b wt0(b)·Y_sh(b)` of the regular family is bounded
by the layered Chernoff sum `∑_{j<Ymax} rootMass·(K·tiltSum)^m / z^j`.  The proof
is the manuscript's layer cake (proof_v4.tex 784-792), here in discrete form for
the integer shell-paid multiplier `Y_sh = Nsh`: write `Nsh(b) = ∑_{j<Nsh(b)} 1`,
swap the order of summation, and bound each level `∑_{b : Nsh(b)>j} wt0(b)` by
Lemma 22.1 (each level is a high-cost subfamily, via the shell-paid calibration
`Nsh(b) > j ⟹ cost(b) ≥ j`).  The level sum decays geometrically in `j`. -/
theorem regular_areaWeighted_le
    (Csh G m Ymax : ℕ) (rootMass K z : ℝ) (hz : 1 ≤ z)
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
      ≤ ∑ j ∈ Finset.range Ymax,
          rootMass * (K * regularTiltSum Csh G z) ^ m / z ^ j := by
  classical
  set paths := Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)) with hpaths
  -- Per-level bound: each level is a high-cost subfamily, so Lemma 22.1 applies.
  have hlevel : ∀ j : ℕ,
      ∑ σ ∈ paths.filter (fun σ => j < Nsh σ), wt0 σ
        ≤ rootMass * (K * regularTiltSum Csh G z) ^ m / z ^ j := by
    intro j
    have hsub : paths.filter (fun σ => j < Nsh σ)
        ⊆ highCostSet paths (fun σ => ∑ i, shellCost Csh (σ i)) j := by
      intro σ hσ
      rw [Finset.mem_filter] at hσ
      rw [mem_highCostSet]
      exact ⟨hσ.1, hcal j σ hσ.1 hσ.2⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun σ hσ _ => hwt0_nonneg σ (mem_highCostSet.1 hσ).1)) ?_
    exact regular_shellChernoff_tail_le Csh G m j rootMass K z hz wt0 hwt0_nonneg hreg
  -- Discrete layer cake.
  have hrange : ∀ σ ∈ paths,
      Finset.range (Nsh σ) = (Finset.range Ymax).filter (fun j => j < Nsh σ) := by
    intro σ hσ
    ext j
    simp only [Finset.mem_range, Finset.mem_filter]
    constructor
    · intro hj; exact ⟨lt_of_lt_of_le hj (hNsh_le σ hσ), hj⟩
    · intro h; exact h.2
  calc ∑ σ ∈ paths, wt0 σ * (Nsh σ : ℝ)
      = ∑ σ ∈ paths, ∑ _j ∈ Finset.range (Nsh σ), wt0 σ := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
    _ = ∑ σ ∈ paths, ∑ _j ∈ (Finset.range Ymax).filter (fun j => j < Nsh σ), wt0 σ := by
        refine Finset.sum_congr rfl (fun σ hσ => ?_)
        rw [hrange σ hσ]
    _ = ∑ σ ∈ paths, ∑ j ∈ Finset.range Ymax, (if j < Nsh σ then wt0 σ else 0) := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [Finset.sum_filter]
    _ = ∑ j ∈ Finset.range Ymax, ∑ σ ∈ paths, (if j < Nsh σ then wt0 σ else 0) :=
        Finset.sum_comm
    _ = ∑ j ∈ Finset.range Ymax, ∑ σ ∈ paths.filter (fun σ => j < Nsh σ), wt0 σ := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_filter]
    _ ≤ ∑ j ∈ Finset.range Ymax,
          rootMass * (K * regularTiltSum Csh G z) ^ m / z ^ j :=
        Finset.sum_le_sum (fun j _ => hlevel j)

/-- **Lemma 22.1A (closed-form area-weighted bound, faithful).**

Resumming the layered Chernoff sum of `regular_areaWeighted_le`: for `z > 1` the
finite geometric series `∑_{j<Ymax} (1/z)^j` is dominated by its infinite value
`(1 - 1/z)⁻¹ = z/(z-1)` (`geom_sum_Ico_le_of_lt_one`).  Hence the area-weighted
shell mass `∑_b wt0(b)·Nsh(b)` of the regular family admits the closed-form bound
`rootMass · (K·tiltSum)^m · z/(z-1)` — the genuine geometric resummation of the
manuscript layer cake (proof_v4.tex 784-792), with the dependence on the level
cutoff `Ymax` eliminated. -/
theorem regular_areaWeighted_le_closed
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
  have hz1 : (1 : ℝ) ≤ z := le_of_lt hz
  have hz0 : (0 : ℝ) < z := by linarith
  have hzm1 : (0 : ℝ) < z - 1 := by linarith
  have hbase := regular_areaWeighted_le Csh G m Ymax rootMass K z hz1 wt0 Nsh
    hwt0_nonneg hreg hNsh_le hcal
  refine hbase.trans ?_
  set C := rootMass * (K * regularTiltSum Csh G z) ^ m with hC
  have hC_nonneg : 0 ≤ C := by
    have htilt : 0 ≤ regularTiltSum Csh G z := regularTiltSum_nonneg Csh G (le_of_lt hz0)
    rw [hC]
    exact mul_nonneg hroot (pow_nonneg (mul_nonneg hK htilt) m)
  -- Geometric resummation: ∑_{j<Ymax} (z⁻¹)^j ≤ (1 - z⁻¹)⁻¹ = z/(z-1).
  have hgeom : ∑ j ∈ Finset.range Ymax, (z⁻¹) ^ j ≤ z / (z - 1) := by
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
  -- Factor the common nonnegative constant out of the layered sum.
  have hrw : ∑ j ∈ Finset.range Ymax, C / z ^ j
      = C * ∑ j ∈ Finset.range Ymax, (z⁻¹) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [inv_pow, div_eq_mul_inv]
  rw [hrw]
  exact mul_le_mul_of_nonneg_left hgeom hC_nonneg

/-- **Lemma 22.1 (moment form from per-edge regularity, faithful).**

This ties the per-edge telescoping `regular_path_mass_le_of_edge` to the moment
factorization `regular_weightedMoment_le`.  Suppose each length-`m` path `σ` over
the gap alphabet `{0,…,G}` carries a mass sequence `mass σ : ℕ → ℝ` with
`mass σ 0 ≤ rootMass`, whose final value is the path weight (`weight σ = mass σ m`),
and such that every edge `k` obeys the *manuscript regular-edge bound*
`|Ω_{k+1}| ≤ K·|Ω_k|·2^{-s(e_k)}` with edge gap `σ ⟨k,·⟩` (proof_v4.tex 717-719).
Then the tilted moment is bounded by `rootMass·(K·tiltSum)^m`.

The proof lifts each `Fin m`-indexed path to its canonical `ℕ`-indexed gap
sequence, telescopes via `regular_path_mass_le_of_edge`, and matches the cost sum
`∑_{k<m} s(e_k) = ∑_{i:Fin m} s(σ i)` to feed `regular_weightedMoment_le`.  No new
manuscript hypothesis is introduced: per-EDGE regularity *implies* the per-PATH
mass bound that the moment factorization consumes. -/
theorem regular_weightedMoment_le_of_edge
    (Csh G m : ℕ) (rootMass K z : ℝ)
    (hz0 : 0 ≤ z) (hK : 0 ≤ K)
    (weight : (Fin m → ℕ) → ℝ) (mass : (Fin m → ℕ) → ℕ → ℝ)
    (hmass0 : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        mass σ 0 ≤ rootMass)
    (hweight : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        weight σ = mass σ m)
    (hedge : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        ∀ (k : ℕ) (hk : k < m),
          mass σ (k + 1) ≤ K * mass σ k * (1 / 2) ^ shellCost Csh (σ ⟨k, hk⟩)) :
    weightedMoment (Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)))
        weight (fun σ => ∑ i, shellCost Csh (σ i)) z
      ≤ rootMass * (K * regularTiltSum Csh G z) ^ m := by
  apply regular_weightedMoment_le Csh G m rootMass K z hz0 weight
  intro σ hσ
  -- The canonical ℕ-indexed gap sequence of the path `σ`.
  set g : ℕ → ℕ := fun k => if h : k < m then σ ⟨k, h⟩ else 0 with hg
  have hgk : ∀ (k : ℕ) (hk : k < m), g k = σ ⟨k, hk⟩ := by
    intro k hk
    simp only [hg]
    exact dif_pos hk
  -- Telescope the per-edge regularity along the path.
  have hpath := regular_path_mass_le_of_edge Csh K rootMass hK g (mass σ) (hmass0 σ hσ) m
    (by
      intro k hk
      rw [hgk k hk]
      exact hedge σ hσ k hk)
  -- Match the ℕ-indexed cost sum with the `Fin m` cost sum.
  have hcost : (∑ k ∈ Finset.range m, shellCost Csh (g k)) = ∑ i, shellCost Csh (σ i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => shellCost Csh (g k)) m]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrArg (shellCost Csh) (hgk (i : ℕ) i.isLt)
  rw [hweight σ hσ, ← hcost]
  exact hpath

/-! ## Honest reduction of the Chernoff phase to regularity + calibration

The structure below is the genuine, irreducible *geometric* input of Lemma 22.1:
a regular length-`m` stopped-path family over a bounded gap alphabet, with the
manuscript per-path mass bound and the length-vs-threshold calibration `m ≤ c₁Y`
in its quantitative form.  From it we build a real `ChernoffPathData` whose
`moment_bound` is **proved** (via `regular_weightedMoment_le`), not assumed — so
the Chernoff phase mass `Regular ≤ cStar·ξ·X/6` follows.  This converts the
opaque manuscript `moment_bound`/`manuscript_bound` hypotheses into a single
faithful statement: *the relevant paths are regular*. -/

/-- The regular stopped-path Chernoff family: the honest geometric content of
Lemma 22.1, packaged for the Chernoff phase slot. -/
structure RegularStoppedChernoffFamily (cStar ξ X : ℝ) where
  Csh : ℕ
  G : ℕ
  m : ℕ
  Y : ℕ
  rootMass : ℝ
  K : ℝ
  z : ℝ
  z_ge_one : 1 ≤ z
  weight : (Fin m → ℕ) → ℝ
  weight_nonneg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
      0 ≤ weight σ
  /-- Manuscript regularity: `|Ω_π| ≤ |Ω_root|·K^m·2^{-cost(π)}` (proof_v4.tex 732-734). -/
  regular : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
      weight σ ≤ rootMass * K ^ m * (1 / 2) ^ (∑ i, shellCost Csh (σ i))
  /-- Length-vs-threshold calibration `m ≤ c₁Y`, in quantitative form. -/
  calibration :
      rootMass * (K * regularTiltSum Csh G z) ^ m ≤ (cStar * ξ * X / 6) * z ^ Y

/-- Build a genuine `ChernoffPathData` from a regular family.  The
`moment_bound` field is discharged by the proved factorization
`regular_weightedMoment_le`, and `manuscript_bound` by the calibration. -/
def RegularStoppedChernoffFamily.toChernoffPathData
    {cStar ξ X : ℝ} (fam : RegularStoppedChernoffFamily cStar ξ X) :
    ChernoffPathData cStar ξ X where
  α := Fin fam.m → ℕ
  paths := Fintype.piFinset (fun _ : Fin fam.m => Finset.range (fam.G + 1))
  weight := fam.weight
  cost := fun σ => ∑ i, shellCost fam.Csh (σ i)
  Y := fam.Y
  m := fam.m
  z := fam.z
  root := fam.rootMass
  A := fam.K * regularTiltSum fam.Csh fam.G fam.z
  weight_nonneg := fam.weight_nonneg
  z_ge_one := fam.z_ge_one
  moment_bound := by
    have hz0 : (0 : ℝ) ≤ fam.z := by linarith [fam.z_ge_one]
    exact regular_weightedMoment_le fam.Csh fam.G fam.m fam.rootMass fam.K fam.z
      hz0 fam.weight fam.regular
  manuscript_bound := by
    have hzY : (0 : ℝ) < fam.z ^ fam.Y := by
      have : (0 : ℝ) < fam.z := by linarith [fam.z_ge_one]
      positivity
    rw [div_le_iff₀ hzY]
    exact fam.calibration

/-- **Chernoff phase mass from regularity (faithful).**  For a regular stopped
family, the Chernoff phase contribution `Regular` exists and fits the phase
budget `cStar·ξ·X/6`, with a fully proved moment bound. -/
theorem chernoffPathSpace_of_regularFamily
    {cStar ξ X : ℝ} (fam : RegularStoppedChernoffFamily cStar ξ X) :
    ∃ Regular : ℝ, 0 ≤ Regular ∧ Regular ≤ cStar * ξ * X / 6 :=
  chernoffPathSpace fam.toChernoffPathData

end

end Erdos260
