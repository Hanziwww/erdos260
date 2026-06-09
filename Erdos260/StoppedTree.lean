import Mathlib
import Erdos260.LiftState

/-!
# Lemma 22.1: convergence of the regular-edge tilt sum

The shell-Chernoff bound (Lemma 22.1 of `proof_v2.tex`) tilts the regular-path
moment by `z^{∑ s(e)}` with `1 < z < 2` and reduces to the finiteness of the
per-edge sum
\[
  \sum_{h \ge 1} 2^{-s(h)} z^{s(h)} \quad\text{with } s(h)=\max(h-C_{\mathrm{sh}},0).
\]
Writing `w = z/2 ∈ (0,1)`, the per-edge sum is `∑_h w^{s(h)}`, and the
manuscript claim is exactly that this is **finite, uniformly in the path
length** (so the `(\cdot)^m` factor stays controlled).

Here `s(h) = max(h - C_sh, 0)` is Lean's natural truncated subtraction
`h - C_sh : ℕ`.  We prove the uniform bound
\[
  \sum_{h < N} w^{h - C} \le (C+1) + (1-w)^{-1},
\]
independent of the cutoff `N`.  This is the previously-absent convergence step
of Lemma 22.1, an unconditional real theorem.
-/

namespace Erdos260

open Finset

noncomputable section

/-- **Lemma 22.1 regular-edge convergence.**  For `0 ≤ w < 1` and any shell
cutoff `C`, the tilt sum `∑_{h < N} w^{max(h - C, 0)}` is bounded, uniformly in
`N`, by `(C + 1) + (1 - w)⁻¹`.  The `h ≤ C` part contributes the flat `C + 1`;
the `h > C` part is a geometric tail `≤ (1 - w)⁻¹`. -/
theorem regular_edge_tilt_sum_le {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) (C N : ℕ) :
    ∑ h ∈ Finset.range N, w ^ (h - C) ≤ ((C : ℝ) + 1) + (1 - w)⁻¹ := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun h => h ≤ C)]
  have hlow :
      ∑ h ∈ (Finset.range N).filter (fun h => h ≤ C), w ^ (h - C) ≤ (C : ℝ) + 1 := by
    have hterm :
        ∀ h ∈ (Finset.range N).filter (fun h => h ≤ C), w ^ (h - C) = (1 : ℝ) := by
      intro h hh
      rw [Finset.mem_filter] at hh
      have hzero : h - C = 0 := by omega
      rw [hzero, pow_zero]
    rw [Finset.sum_congr rfl hterm]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsub : (Finset.range N).filter (fun h => h ≤ C) ⊆ Finset.range (C + 1) := by
      intro h hh
      rw [Finset.mem_filter] at hh
      rw [Finset.mem_range]
      omega
    have hcard :
        ((Finset.range N).filter (fun h => h ≤ C)).card ≤ C + 1 := by
      have h := Finset.card_le_card hsub
      simpa [Finset.card_range] using h
    have : (((Finset.range N).filter (fun h => h ≤ C)).card : ℝ) ≤ (C : ℝ) + 1 := by
      exact_mod_cast hcard
    linarith
  have hhigh :
      ∑ h ∈ (Finset.range N).filter (fun h => ¬ h ≤ C), w ^ (h - C) ≤ (1 - w)⁻¹ := by
    have hinj :
        ∀ x ∈ (Finset.range N).filter (fun h => ¬ h ≤ C),
        ∀ y ∈ (Finset.range N).filter (fun h => ¬ h ≤ C),
          x - C = y - C → x = y := by
      intro x hx y hy hxy
      rw [Finset.mem_filter] at hx hy
      omega
    rw [← Finset.sum_image hinj]
    exact finset_geom_sum_le hw0 hw1
  linarith

/-! ## Lemma 22.1A: area-weighted stopped shell–Chernoff bound

`∑_{b∈𝒮} wt_sh(b) ≤ C_Q X|I_j| 2^{-cY} + o(sX|I_j|)`  (eq. 22.1a).

The manuscript proof is a **layer cake**:
`∑_b wt_sh(b) = ∫₀^∞ ∑_{b∈𝒮(u)} wt₀(b) du`, where `𝒮(u) = {b : Y_sh(b) > u}`,
and the per-level inner sum is bounded by Lemma 22.1 (the shell-Chernoff bound,
with the reserve `C_res L` chosen in Convention 2.0 so that the active floor
`c_Y L ≤ Y ≤ C_Y L` gives the uniform `2^{-cY}` factor — `manuscriptCres`,
`manuscriptCY`).

We model the area-weighted shell mass as `∑_b wt₀(b)·Y_sh(b)` and prove the
**layer-cake assembly unconditionally** (the integral representation and the
monotone-integral bound).  The per-level shell-Chernoff bound `hlevel` is the
Lemma-22.1 input, taken as a hypothesis (it is the deep analytic step). -/

open MeasureTheory

/-- The layer-cake integrand `∑_{b∈𝒮(u)} wt₀(b) = ∑_{b : 0<u<Y_sh(b)} wt₀(b)`,
modelled as a finite sum of indicators of `(0, Y_sh b)`. -/
def areaLayerSum {ι : Type*} (S : Finset ι) (wt0 Ysh : ι → ℝ) (u : ℝ) : ℝ :=
  ∑ b ∈ S, (Set.Ioo (0 : ℝ) (Ysh b)).indicator (fun _ => wt0 b) u

theorem areaLayerSum_nonneg {ι : Type*} (S : Finset ι) (wt0 Ysh : ι → ℝ) (u : ℝ)
    (hwt0 : ∀ b ∈ S, 0 ≤ wt0 b) : 0 ≤ areaLayerSum S wt0 Ysh u := by
  unfold areaLayerSum
  refine Finset.sum_nonneg (fun b hb => ?_)
  exact Set.indicator_nonneg (fun _ _ => hwt0 b hb) u

/-- Each layer-cake indicator term is integrable (finite-measure support). -/
theorem areaLayer_indicator_integrable {ι : Type*} (wt0 Ysh : ι → ℝ) (b : ι) :
    Integrable ((Set.Ioo (0 : ℝ) (Ysh b)).indicator (fun _ => wt0 b)) volume := by
  refine IntegrableOn.integrable_indicator (integrableOn_const (hs := ?_)) measurableSet_Ioo
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

theorem areaLayerSum_integrable {ι : Type*} (S : Finset ι) (wt0 Ysh : ι → ℝ) :
    Integrable (areaLayerSum S wt0 Ysh) volume := by
  unfold areaLayerSum
  exact integrable_finset_sum S fun b _ => areaLayer_indicator_integrable wt0 Ysh b

/-- **Layer-cake identity.** `∫_ℝ (∑_{b∈𝒮(u)} wt₀(b)) du = ∑_b wt₀(b)·Y_sh(b)`:
each indicator of `(0, Y_sh b)` integrates to its length `Y_sh b`. -/
theorem integral_areaLayerSum {ι : Type*} (S : Finset ι) (wt0 Ysh : ι → ℝ)
    (hYsh : ∀ b ∈ S, 0 ≤ Ysh b) :
    ∫ u, areaLayerSum S wt0 Ysh u = ∑ b ∈ S, wt0 b * Ysh b := by
  unfold areaLayerSum
  rw [integral_finset_sum S fun b _ => areaLayer_indicator_integrable wt0 Ysh b]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [integral_indicator_const (wt0 b) measurableSet_Ioo, smul_eq_mul, measureReal_def,
    Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [hYsh b hb])]
  ring

/--
**Lemma 22.1A (area-weighted stopped shell–Chernoff bound).**

`∑_{b∈𝒮} wt₀(b)·Y_sh(b) ≤ bound`, where `bound` is the integrated per-level
Chernoff tail `∫₀^∞ chernoff(u) du` (eq. 22.1a's `C_Q X|I_j|2^{-cY}+o(sX|I_j|)`).

The layer-cake identity and the monotone-integral comparison are proved
unconditionally; the per-level shell-Chernoff bound `hlevel` (each layer
`∑_{b∈𝒮(u)} wt₀(b) ≤ chernoff(u)`) is the Lemma-22.1 input.
-/
theorem lemma22_1A_areaWeightedShellChernoff
    {ι : Type*} (S : Finset ι) (wt0 Ysh : ι → ℝ) (chernoff : ℝ → ℝ) (bound : ℝ)
    (hYsh : ∀ b ∈ S, 0 ≤ Ysh b)
    (hchernoff_int : Integrable chernoff volume)
    (hlevel : ∀ u, areaLayerSum S wt0 Ysh u ≤ chernoff u)
    (hbound : ∫ u, chernoff u ≤ bound) :
    ∑ b ∈ S, wt0 b * Ysh b ≤ bound := by
  rw [← integral_areaLayerSum S wt0 Ysh hYsh]
  calc ∫ u, areaLayerSum S wt0 Ysh u
      ≤ ∫ u, chernoff u :=
        integral_mono (areaLayerSum_integrable S wt0 Ysh) hchernoff_int hlevel
    _ ≤ bound := hbound

end

end Erdos260
