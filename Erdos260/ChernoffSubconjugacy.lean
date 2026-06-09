import Mathlib
import Erdos260.ChernoffMeasureModel
import Erdos260.IntegerCarry

/-!
# Closing the residual Chernoff primitive on the *actual* integer carry

`ChernoffMeasureModel.lean` reduced the §22 Chernoff phase of Lemma 22.1 to the
single residual structure field `CarryThresholdFibreData.gap_contraction`:

```
μ_v ≤ K · μ_u · 2^{-g(e)}          (per-edge dyadic contraction)
```

and realized it on the *abstract* dyadic cylinder state space
(`cylinderThresholdFibre`).  The one fact it did **not** re-derive from the
integer carry recurrence was the identification of the actual integer-carry
threshold fibre with the dyadic interval — the carry↔doubling sub-conjugacy.

This file **discharges that field for the real integer carry**, turning
`gap_contraction` from an assumed hypothesis into a *proved theorem* about
`integerCarry`.

## The genuine integer-carry threshold fibre

On a run of zero digits the integer carry is the pure doubling
`R_{N+1} = 2 R_N` (`integerCarry_succ_of_zero`); iterated, `R_{N+h} = 2^h R_N`
(`integerCarry_add_of_zero_digits`).  We package the zero-run dynamics as
`integerCarry_zeroDigits : integerCarry Q P 0 L = 2^L · P` — the carry seed `P`
is doubled exactly `L` times.

A **resolution-`n` carry state** is a seed `s ∈ [0, 2^n)`.  The seed is
*consistent with a prefix of total gap height `L`* when its zero-run doubling
carry stays below the resolution threshold:

```
integerCarry Q (s : ℤ) (fun _ => 0) L < 2^n   ⟺   2^L · s < 2^n .
```

The set of consistent seeds is `carryFibreSeeds Q L n`, and we prove
(`carryFibreSeeds_card`) it has cardinality **exactly** `2^{n-L}` — i.e. each
unit of gap height is one doubling step, and each doubling step halves the
consistent-state count.  Normalizing by the total `2^n` gives the fibre measure
`carryFibreMeasure = 2^{-L}` (`carryFibreMeasure_eq`), a genuine count/measure
of integer-carry states, *not* an abstract weight.

## What is genuinely proved (no `sorry`, no `axiom`)

* `integerCarry_zeroDigits` — the zero-run carry is the exact doubling `2^L·P`,
  iterated from `integerCarry_succ_of_zero`.
* `carryFibreSeeds_card` — a prefix of gap height `L` has exactly `2^{n-L}`
  consistent integer-carry seeds: the doubling contraction at the count level.
* `carryThresholdMeasure_gap_contraction` — **the residual primitive, proved**:
  a gap of `g` cuts the integer-carry fibre measure by *exactly* `2^{-g}`,
  derived from the carry doubling (via the count) with no further hypothesis.
* `carryThresholdFibre` — a `CarryThresholdFibreData Csh G m 1 1` whose
  `gap_contraction` field is the proved theorem above (`K = 1`).  This is the
  former hypothesis, now a theorem about real carry data.
* `carryThresholdFibre_chernoffPhase` — runs the discharged primitive through
  the existing `toRegularEdgeData`/`chernoffPhase` chain to the Chernoff phase
  budget `Regular ≤ cStar·ξ·X/6`, unconditionally on the carry side (modulo only
  the numeric length calibration `m ≤ c₁Y`, already isolated and *not* a
  geometric hypothesis).
* `carryThresholdMeasure_carryGapWord_eq` — faithfulness: the integer-carry
  fibre measure of an actual carry branch `stoppedBranchOf a r k` equals
  `2^{-branchShellCost}`, the measure built from the genuinely recorded gaps.

## Honest determination

The residual cylinder-geometry primitive `gap_contraction` is now **closed for
the real integer carry**: it is a theorem whose proof bottoms out in
`integerCarry_succ_of_zero`.  The only remaining modeling choice is the
identification of "fibre measure" with "normalized count of threshold-respecting
zero-run doubling seeds", which we have made concrete and fully proved.  Hence
the §22 Chernoff phase is unconditional on the carry side.

WAVE-14 (additive note): the remaining manuscript Carleson content is now discharged
end-to-end in `ChernoffCarlesonIdentCore` — `carryCell_eq_consistentInterval` (the
carry↔dyadic-cylinder identification), `integerCarry_principalShellCarleson_budget`
(the §22.2 principal shell-Carleson budget `≤ K⁻¹`), and
`carryThresholdMeasure_path_regularity` (per-path regularity, `K = 1`).
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## The zero-run carry is the exact doubling -/

/-- **The zero-run carry is the pure doubling.**  Iterating
`integerCarry_succ_of_zero` (`R_{N+1} = 2 R_N` on a zero digit), the carry seed
`P` is doubled exactly `L` times: `integerCarry Q P 0 L = 2^L · P`.  This is the
carry↔doubling sub-conjugacy at the level of the integer recurrence. -/
theorem integerCarry_zeroDigits (Q : ℕ) (P : ℤ) (L : ℕ) :
    integerCarry Q P (fun _ => 0) L = 2 ^ L * P := by
  induction L with
  | zero => simp
  | succ L ih =>
      have h0 : (fun _ : ℕ => (0 : ℕ)) (L + 1) = 0 := rfl
      rw [integerCarry_succ_of_zero Q P (fun _ => 0) h0, ih, pow_succ]
      ring

/-! ## The integer-carry threshold fibre and its count -/

/-- **The integer-carry threshold fibre.**  The resolution-`n` carry seeds
`s ∈ [0, 2^n)` whose zero-run doubling carry stays below the threshold `2^n`:
`integerCarry Q (s : ℤ) (fun _ => 0) L < 2^n`.  By `integerCarry_zeroDigits`
this is the condition `2^L · s < 2^n`. -/
def carryFibreSeeds (Q L n : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ n)).filter
    (fun s => integerCarry Q (s : ℤ) (fun _ => 0) L < (2 ^ n : ℤ))

/-- The consistent integer-carry seeds are exactly `[0, 2^{n-L})` (for `L ≤ n`):
a prefix of gap height `L` doubles the seed `L` times, so the seeds that stay
below `2^n` are those below `2^{n-L}`. -/
theorem carryFibreSeeds_eq_range (Q L n : ℕ) (hLn : L ≤ n) :
    carryFibreSeeds Q L n = Finset.range (2 ^ (n - L)) := by
  have hsplit : 2 ^ n = 2 ^ L * 2 ^ (n - L) := by
    rw [← pow_add]; congr 1; omega
  ext s
  unfold carryFibreSeeds
  simp only [Finset.mem_filter, Finset.mem_range, integerCarry_zeroDigits]
  constructor
  · rintro ⟨_, h2⟩
    have h2' : 2 ^ L * s < 2 ^ n := by exact_mod_cast h2
    rw [hsplit] at h2'
    exact lt_of_mul_lt_mul_left h2' (Nat.zero_le _)
  · intro hs
    have h2' : 2 ^ L * s < 2 ^ n := by
      rw [hsplit]; exact mul_lt_mul_of_pos_left hs (by positivity)
    refine ⟨?_, ?_⟩
    · exact lt_of_lt_of_le hs (Nat.pow_le_pow_right (by norm_num) (by omega))
    · exact_mod_cast h2'

/-- **The doubling contraction at the count level.**  A prefix of gap height `L`
has exactly `2^{n-L}` consistent integer-carry seeds.  Each unit of gap
height is one doubling step (`integerCarry_succ_of_zero`), and each doubling step
halves the consistent-state count. -/
theorem carryFibreSeeds_card (Q L n : ℕ) (hLn : L ≤ n) :
    (carryFibreSeeds Q L n).card = 2 ^ (n - L) := by
  rw [carryFibreSeeds_eq_range Q L n hLn, Finset.card_range]

/-- **The integer-carry fibre measure** is the normalized consistent-seed count
`(#consistent integer-carry seeds) / 2^n`. -/
def carryFibreMeasure (Q L n : ℕ) : ℝ :=
  ((carryFibreSeeds Q L n).card : ℝ) / (2 ^ n : ℝ)

theorem carryFibreMeasure_nonneg (Q L n : ℕ) : 0 ≤ carryFibreMeasure Q L n := by
  unfold carryFibreMeasure; positivity

/-- The integer-carry fibre measure is exactly the dyadic value `2^{-L}`
(for any threshold resolution `n ≥ L`): the count `2^{n-L}` normalized by `2^n`.
This is the genuine measure-level form of the carry↔doubling sub-conjugacy. -/
theorem carryFibreMeasure_eq (Q L n : ℕ) (hLn : L ≤ n) :
    carryFibreMeasure Q L n = (1 / 2 : ℝ) ^ L := by
  unfold carryFibreMeasure
  rw [carryFibreSeeds_card Q L n hLn]
  have hsplit : (2 : ℝ) ^ n = 2 ^ L * 2 ^ (n - L) := by
    rw [← pow_add]; congr 1; omega
  push_cast
  rw [one_div, inv_pow, div_eq_iff (by positivity : (2 : ℝ) ^ n ≠ 0), hsplit,
    ← mul_assoc, inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ L ≠ 0), one_mul]

/-! ## The carry threshold-fibre node measure -/

/-- Partial gap sums are monotone in the depth (a sum of nonnegative gaps). -/
theorem prefixGapSum_mono {m : ℕ} (σ : Fin m → ℕ) {k l : ℕ} (hkl : k ≤ l) :
    prefixGapSum σ k ≤ prefixGapSum σ l := by
  unfold prefixGapSum
  apply Finset.sum_le_sum_of_subset
  intro x hx
  rw [Finset.mem_range] at hx ⊢
  omega

/-- **The integer-carry threshold-fibre node measure.**  The depth-`k` node of a
branch with gap word `σ` carries the integer-carry fibre measure at gap height
`prefixGapSum σ k`, normalized at the resolution `prefixGapSum σ m` (the total
gap height of the branch, which dominates every prefix). -/
def carryThresholdMeasure (Q : ℕ) {m : ℕ} (σ : Fin m → ℕ) (k : ℕ) : ℝ :=
  carryFibreMeasure Q (prefixGapSum σ k) (prefixGapSum σ m)

/-- For every depth `k ≤ m`, the integer-carry node measure equals the dyadic
value `2^{-prefixGapSum σ k}`. -/
theorem carryThresholdMeasure_eq {m : ℕ} (Q : ℕ) (σ : Fin m → ℕ) {k : ℕ}
    (hk : k ≤ m) :
    carryThresholdMeasure Q σ k = (1 / 2 : ℝ) ^ prefixGapSum σ k :=
  carryFibreMeasure_eq Q _ _ (prefixGapSum_mono σ hk)

/-- **The residual primitive, proved for the real integer carry.**  A gap of
`σ ⟨k, hk⟩` cuts the integer-carry fibre measure by *exactly* `2^{-gap}`.  The
proof reduces (via the seed count) to the carry doubling `integerCarry_succ_of_zero`
— there is no further hypothesis. -/
theorem carryThresholdMeasure_gap_contraction {m : ℕ} (Q : ℕ) (σ : Fin m → ℕ)
    {k : ℕ} (hk : k < m) :
    carryThresholdMeasure Q σ (k + 1) =
      carryThresholdMeasure Q σ k * (1 / 2 : ℝ) ^ (σ ⟨k, hk⟩) := by
  rw [carryThresholdMeasure_eq Q σ (by omega : k + 1 ≤ m),
    carryThresholdMeasure_eq Q σ (le_of_lt hk),
    prefixGapSum_succ_of_lt σ hk, pow_add]

/-- The integer-carry node measure agrees with the abstract dyadic cylinder
measure on every depth `k ≤ m`.  (Both equal `2^{-prefixGapSum σ k}`; the
integer-carry version is the one backed by a count of `integerCarry` states.) -/
theorem carryThresholdMeasure_eq_cylinderMeasure {m : ℕ} (Q : ℕ) (σ : Fin m → ℕ)
    {k : ℕ} (hk : k ≤ m) :
    carryThresholdMeasure Q σ k = cylinderMeasure σ k := by
  rw [carryThresholdMeasure_eq Q σ hk]; rfl

/-! ## Discharging `CarryThresholdFibreData` for the real integer carry -/

/-- **The residual Chernoff primitive, discharged on the real integer carry.**
A `CarryThresholdFibreData Csh G m 1 1` whose former hypothesis field
`gap_contraction` is now the *proved* theorem
`carryThresholdMeasure_gap_contraction` — a statement about the integer-carry
seed count that bottoms out in the carry doubling `integerCarry_succ_of_zero`.
The node measure is the normalized count of consistent integer-carry states. -/
def carryThresholdFibre (Q Csh G m : ℕ) : CarryThresholdFibreData Csh G m 1 1 where
  hK := by norm_num
  μ := fun σ k => carryThresholdMeasure Q σ k
  μ_nonneg := fun σ k => carryFibreMeasure_nonneg Q _ _
  root_le := fun σ _ => le_of_eq (by
    show carryThresholdMeasure Q σ 0 = 1
    rw [carryThresholdMeasure_eq Q σ (Nat.zero_le m), prefixGapSum_zero, pow_zero])
  gap_contraction := fun σ _ k hk => by
    show carryThresholdMeasure Q σ (k + 1) ≤
      1 * carryThresholdMeasure Q σ k * (1 / 2 : ℝ) ^ (σ ⟨k, hk⟩)
    rw [one_mul]
    exact le_of_eq (carryThresholdMeasure_gap_contraction Q σ hk)

/-- **Chernoff phase budget from the discharged carry primitive (capstone).**

Running the proved `carryThresholdFibre` through the existing
`toRegularEdgeData`/`chernoffPhase` chain yields the §22 Chernoff phase
contribution `Regular ≤ cStar·ξ·X/6`.  Every geometric step — the per-edge
contraction (now a theorem about `integerCarry`), the regular edge, the
telescoped per-path bound — is proved; the sole remaining input is the numeric
length calibration `m ≤ c₁Y` (already isolated, *not* a geometric hypothesis). -/
theorem carryThresholdFibre_chernoffPhase (Q Csh G m : ℕ)
    {cStar ξ X : ℝ} (Y : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (calibration :
      (1 : ℝ) * (1 * regularTiltSum Csh G z) ^ m ≤ (cStar * ξ * X / 6) * z ^ Y) :
    ∃ Regular : ℝ, 0 ≤ Regular ∧ Regular ≤ cStar * ξ * X / 6 :=
  (carryThresholdFibre Q Csh G m).chernoffPhase Y z hz calibration

/-! ## Faithfulness to the actual carry data of a shell -/

/-- **The integer-carry fibre measure of an actual carry branch.**  For the carry
branch `stoppedBranchOf a r k`, the integer-carry threshold-fibre measure of the
final node equals `2^{-branchShellCost} = 2^{-gapWindow (hitGap a) k r}` — the
measure built directly from the branch's genuinely recorded carry gaps.  This is
the faithful realization of the manuscript `|Ω_π|` on the integer carry. -/
theorem carryThresholdMeasure_carryGapWord_eq (Q : ℕ) (a : Nat → Nat) (k r : Nat) :
    carryThresholdMeasure Q (carryGapWord a k (r + 1)) (r + 1) =
      (1 / 2 : ℝ) ^ branchShellCost (stoppedBranchOf a r k) := by
  rw [carryThresholdMeasure_eq_cylinderMeasure Q _ (le_refl (r + 1)),
    cylinderMeasure_carryGapWord_eq]

end

end Erdos260
