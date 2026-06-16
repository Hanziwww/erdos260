import Erdos260.Constants

/-!
# K.4 constants Q-calibration (the deferred "future-wave task")

`proof_v4_repaired_core_v37.tex` (remark after Prop 24.3, ~lines 1466–1471) flags that
the genuine fixed-period density floor is `1/(3Q)` (so `ρ_D` must be Q-dependent,
`ρ_D(q₀)=1/(4q₀)`), but that the **orthogonal §K.4 smallness budget**
`2(c₀ε) ≤ (ξ/6)ρ_D` and the dense-marker compatibility `C_Q·c_*/(ρ_D·κ) < ξ` then
require *matching Q-dependent local constants* `c₀(Q)/κ(Q)` (with `κ < 1/(40Q)`),
calling this calibration "a separate, future-wave task … not addressed".

This module discharges the **feasibility** of that calibration: with the explicit
q₀-dependent witnesses
```
  κ(q₀)   := κ / q₀          (so κ(q₀) < 1/(40 q₀), matching the manuscript bound)
  ρ_D(q₀) := ρ_D / q₀ = 1/(4 q₀)
  c_*(q₀) := c_* / q₀²        (compensates ρ_D(q₀)·κ(q₀) = κ ρ_D / q₀²)
  c₀(q₀)  := c₀ / q₀
```
**every** K.4 budget inequality holds for **every** `q₀ ≥ 1`, with the SAME margins as
the pinned `q₀ = 1` case (`Constants.manuscript_densePackCompatible` etc.).
The cancellation `c_*(q₀)/(ρ_D(q₀)κ(q₀)) = c_*/(ρ_D κ)` is the crux.

We also record the **necessity** (`pinned_cStar_step6_fails_at_four`): with the *pinned*
q₀-independent `c_*` the step-6 ratio grows like q₀² and already fails at q₀ = 4, so the
q₀-scaling is genuinely required — exactly the manuscript's point.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

/-! ## 1. Q-dependent constants -/

/-- Sparse-shell density-contradiction constant `c₀ = 17/2²⁴` (Appendix U / H). -/
def manuscriptC0sparse : ℝ := 17 / 2 ^ 24

/-- Q-dependent order constant `κ(q₀) := κ / q₀`  (`q₀` = odd part of `Q`). -/
def kappaQ (q0 : ℕ) : ℝ := manuscriptKappa / (q0 : ℝ)

/-- Q-dependent dense-marker density `ρ_D(q₀) := ρ_D / q₀ = 1/(4 q₀)`. -/
def rhoDQcal (q0 : ℕ) : ℝ := manuscriptRhoD / (q0 : ℝ)

/-- Q-dependent failure constant `c_*(q₀) := c_* / q₀²`. -/
def cStarQ (q0 : ℕ) : ℝ := manuscriptCstarSmall / (q0 : ℝ) ^ 2

/-- Q-dependent sparse constant `c₀(q₀) := c₀ / q₀`. -/
def c0Q (q0 : ℕ) : ℝ := manuscriptC0sparse / (q0 : ℝ)

/-! ## 2. Pinned (q₀ = 1) base inequalities -/

theorem manuscriptKappa_lt_inv_40 : manuscriptKappa < 1 / 40 := by
  unfold manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps; norm_num

theorem manuscriptC0sparse_pos : 0 < manuscriptC0sparse := by
  unfold manuscriptC0sparse; norm_num

/-- Pinned Tower/density budget `2·c₀·ε ≤ (ξ/6)·ρ_D`. -/
theorem towerBudget_pinned :
    2 * manuscriptC0sparse * manuscriptEps ≤ manuscriptXi / 6 * manuscriptRhoD := by
  unfold manuscriptC0sparse manuscriptEps manuscriptXi manuscriptRhoD; norm_num

/-- Pinned descent-accumulator budget `C_*·C_Q·c_* < c_pr/4`. -/
theorem descentAccum_pinned :
    manuscriptCstar * manuscriptCQ * manuscriptCstarSmall < manuscriptCpr / 4 := by
  unfold manuscriptCstar manuscriptCQ manuscriptCstarSmall manuscriptKappa
    manuscriptCdrop manuscriptC1 manuscriptEps manuscriptXi manuscriptCpr
  norm_num

/-! ## 3. Q-dependent budgets hold for every q₀ ≥ 1 -/

/-- (a) `κ(q₀) < 1/(40 q₀)` for every `q₀ ≥ 1` — the manuscript's order bound. -/
theorem kappaQ_lt_inv_40 {q0 : ℕ} (h : 0 < q0) : kappaQ q0 < 1 / (40 * (q0 : ℝ)) := by
  have hq : (0 : ℝ) < q0 := Nat.cast_pos.mpr h
  have hinv : (0 : ℝ) < 1 / (q0 : ℝ) := by positivity
  have key : manuscriptKappa * (1 / (q0 : ℝ)) < (1 / 40) * (1 / (q0 : ℝ)) :=
    mul_lt_mul_of_pos_right manuscriptKappa_lt_inv_40 hinv
  unfold kappaQ
  calc manuscriptKappa / (q0 : ℝ) = manuscriptKappa * (1 / (q0 : ℝ)) := by ring
    _ < (1 / 40) * (1 / (q0 : ℝ)) := key
    _ = 1 / (40 * (q0 : ℝ)) := by ring

/-- (b) Dense-marker compatibility (K.4 step 6) for every `q₀ ≥ 1`:
    `c_*(q₀)/(ρ_D(q₀)·κ(q₀)) < ξ`.  The q₀² cancels, so this reduces *exactly* to the
    pinned `Constants.manuscript_densePackCompatible` — same margin at every Q. -/
theorem densePackCompatibleQ {q0 : ℕ} (h : 0 < q0) :
    cStarQ q0 / (rhoDQcal q0 * kappaQ q0) < manuscriptXi := by
  have hq : (0 : ℝ) < q0 := Nat.cast_pos.mpr h
  have hq0 : (q0 : ℝ) ≠ 0 := ne_of_gt hq
  have hrho : manuscriptRhoD ≠ 0 := ne_of_gt manuscriptRhoD_pos
  have hkap : manuscriptKappa ≠ 0 := ne_of_gt manuscriptKappa_pos
  have hcancel : cStarQ q0 / (rhoDQcal q0 * kappaQ q0)
      = manuscriptCstarSmall / (manuscriptRhoD * manuscriptKappa) := by
    unfold cStarQ rhoDQcal kappaQ
    field_simp
  rw [hcancel]
  exact manuscript_densePackCompatible

/-- (c) Tower/density smallness budget `2·c₀(q₀)·ε ≤ (ξ/6)·ρ_D(q₀)` for every `q₀ ≥ 1`. -/
theorem towerBudgetQ {q0 : ℕ} (h : 0 < q0) :
    2 * c0Q q0 * manuscriptEps ≤ manuscriptXi / 6 * rhoDQcal q0 := by
  have hq : (0 : ℝ) < q0 := Nat.cast_pos.mpr h
  have hinv : (0 : ℝ) ≤ 1 / (q0 : ℝ) := by positivity
  have key := mul_le_mul_of_nonneg_right towerBudget_pinned hinv
  unfold c0Q rhoDQcal
  calc 2 * (manuscriptC0sparse / (q0 : ℝ)) * manuscriptEps
      = (2 * manuscriptC0sparse * manuscriptEps) * (1 / (q0 : ℝ)) := by ring
    _ ≤ (manuscriptXi / 6 * manuscriptRhoD) * (1 / (q0 : ℝ)) := key
    _ = manuscriptXi / 6 * (manuscriptRhoD / (q0 : ℝ)) := by ring

/-- (d) Descent-accumulator budget `C_*·C_Q·c_*(q₀) < c_pr/4` for every `q₀ ≥ 1`. -/
theorem descentAccumQ {q0 : ℕ} (h : 0 < q0) :
    manuscriptCstar * manuscriptCQ * cStarQ q0 < manuscriptCpr / 4 := by
  have hq : (1 : ℝ) ≤ (q0 : ℝ) := by exact_mod_cast h
  have hsq : (1 : ℝ) ≤ (q0 : ℝ) ^ 2 := by nlinarith [hq]
  have hcs0 : (0 : ℝ) ≤ manuscriptCstarSmall := le_of_lt manuscriptCstarSmall_pos
  have hle : cStarQ q0 ≤ manuscriptCstarSmall := by
    unfold cStarQ; exact div_le_self hcs0 hsq
  have hcoef : (0 : ℝ) ≤ manuscriptCstar * manuscriptCQ := by
    have h1 := le_of_lt manuscriptCstar_pos
    have h2 := le_of_lt manuscriptCQ_pos
    positivity
  calc manuscriptCstar * manuscriptCQ * cStarQ q0
      ≤ manuscriptCstar * manuscriptCQ * manuscriptCstarSmall :=
        mul_le_mul_of_nonneg_left hle hcoef
    _ < manuscriptCpr / 4 := descentAccum_pinned

/-! ## 4. The bundled feasibility theorem -/

/-- **K.4 Q-calibration feasibility (all Q).**  With the explicit q₀-dependent
    constants `κ(q₀)=κ/q₀`, `ρ_D(q₀)=ρ_D/q₀=1/(4q₀)`, `c_*(q₀)=c_*/q₀²`, `c₀(q₀)=c₀/q₀`,
    *all four* K.4 budget inequalities hold for *every* `q₀ ≥ 1`:
      (a) order bound `κ(q₀) < 1/(40 q₀)`;
      (b) dense-marker step 6 `c_*(q₀)/(ρ_D(q₀)·κ(q₀)) < ξ`;
      (c) Tower/density budget `2·c₀(q₀)·ε ≤ (ξ/6)·ρ_D(q₀)`;
      (d) descent accumulator `C_*·C_Q·c_*(q₀) < c_pr/4`.
    Thus the constants hierarchy the manuscript deferred is simultaneously satisfiable
    at every `Q`, closing the *feasibility* half of the deferred calibration. -/
theorem k4_calibration_feasible_all_Q {q0 : ℕ} (h : 0 < q0) :
    kappaQ q0 < 1 / (40 * (q0 : ℝ))
      ∧ cStarQ q0 / (rhoDQcal q0 * kappaQ q0) < manuscriptXi
      ∧ 2 * c0Q q0 * manuscriptEps ≤ manuscriptXi / 6 * rhoDQcal q0
      ∧ manuscriptCstar * manuscriptCQ * cStarQ q0 < manuscriptCpr / 4 :=
  ⟨kappaQ_lt_inv_40 h, densePackCompatibleQ h, towerBudgetQ h, descentAccumQ h⟩

/-- Sanity: at `q₀ = 1` the calibration recovers the pinned constants. -/
theorem calibration_recovers_pinned :
    kappaQ 1 = manuscriptKappa ∧ rhoDQcal 1 = manuscriptRhoD
      ∧ cStarQ 1 = manuscriptCstarSmall ∧ c0Q 1 = manuscriptC0sparse := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [kappaQ, rhoDQcal, cStarQ, c0Q]

/-! ## 5. Necessity: the pinned (q₀-independent) `c_*` does NOT survive

   With the *pinned* `c_*` the step-6 ratio `c_*/(ρ_D(q₀)κ(q₀))` grows like `q₀²`
   (= `(pinned ratio)·q₀²`), so it already reaches `ξ` at `q₀ = 4` and fails for
   `q₀ ≥ 4` — exactly why the q₀-scaling of `c_*` (and `c₀`) is mandatory. -/
theorem pinned_cStar_step6_fails_at_four :
    ¬ (manuscriptCstarSmall / (rhoDQcal 4 * kappaQ 4) < manuscriptXi) := by
  have hk : (0 : ℝ) < manuscriptKappa := manuscriptKappa_pos
  have hprod : rhoDQcal 4 * kappaQ 4 = manuscriptKappa / 64 := by
    unfold rhoDQcal kappaQ manuscriptRhoD; push_cast; ring
  have hcs : manuscriptCstarSmall = manuscriptXi * (manuscriptKappa / 64) := by
    unfold manuscriptCstarSmall; ring
  have heq : manuscriptCstarSmall / (rhoDQcal 4 * kappaQ 4) = manuscriptXi := by
    rw [hprod, hcs, mul_div_assoc,
      div_self (ne_of_gt (div_pos hk (by norm_num))), mul_one]
  rw [heq]
  exact lt_irrefl _

/-! ## 6. Axiom-cleanliness audit -/

theorem k4CalibrationResiduals_nonempty :
    (["K.4 Q-calibration feasibility CLOSED: kappaQ/rhoDQcal/cStarQ/c0Q witnesses, " ++
      "all four budgets for every q0 >= 1, pinned recovered at q0 = 1, " ++
      "pinned c_* shown to fail at q0 = 4."] : List String) ≠ [] := by decide

/-! ## 7. Axiom-cleanliness audit -/

#print axioms kappaQ_lt_inv_40
#print axioms densePackCompatibleQ
#print axioms towerBudgetQ
#print axioms descentAccumQ
#print axioms k4_calibration_feasible_all_Q
#print axioms pinned_cStar_step6_fails_at_four

end

end Erdos260
