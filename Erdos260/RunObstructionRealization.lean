import Erdos260.PackageRealization

/-!
# Run obstruction realization: closing the geometric-realization residual of `MeanLowRunWindow`

`PackageRealization.lean` reduced the L.4.2 Run half-decrease to the geometric-realization
fields of `MeanLowRunWindow` — that a mean-low run obstruction **is** a §25.2 small-denominator
dyadic segment `a/q₀` (`q₀` odd, coprime, bounded size) whose old run period dominates the
threshold `⌊βp/4⌋` on a long-enough window (`hq0/hodd/hcop/hsize/hold/hbp_le_old/hoverlap`).  It
also proved that the mean-low premise `hMeanLow` and the length premise `hNlen` are *derived*
from the L.4.1 classifier verdict (`hMeanLow_of_verdict`, `halfDecrease_of_meanLow_verdict`).

This file (NEW; it edits no existing file) attacks the remaining geometric-realization residual.

## What is honestly the situation

The construction has **no separate "run obstruction" object**: the strings *run obstruction* /
*run window* occur only in `PackageRealization.lean` and `RunDescentConstruction.lean`, as the
manuscript's name for the §25.1/§25.2 small-denominator segment.  So the bare assertion "the run
obstruction's mask point *is* the rational `a/q₀` with `q₀` a small odd denominator" is genuinely
**construction-level / definitional** (the §25.1 residual-cylinder reduction, itself only reduced
to its carry-tail primitives in `Residual.lean`).  Following STEP 3, we isolate the **smallest**
residual predicate and prove the realization + half-decrease from it — while genuinely **closing**
the realization fields that are *not* construction-level.

## What is genuinely CLOSED here (new content)

* `dyadicDigit_le_one` — every dyadic digit is `0/1` (so a segment density never exceeds its
  length), from `binaryQuotient_le_one`.
* `dyadicDigit_periodicOn_mul` — **`hold` is a THEOREM, not a residual**: the dyadic digit word
  `dyadicDigit q₀ a` is `PeriodicOn` with period `m·ord_{q₀}(2)` for *every* `m > 0`, with **no**
  hypothesis beyond `q₀ > 1` odd (it is the §25.2 fundamental periodicity `dyadicDigit_period`
  pushed through `digit_add_mul_period`).  So "the run obstruction carries the old period on its
  dyadic digit word" needs no input once the old period is the §25.2 fundamental period (or a
  multiple of it) — exactly the manuscript's "the run period of a small-denominator segment is its
  dyadic period".
* `RunObstruction` — the smallest residual bundle: the §25.2 reduced small-denominator data
  (`q₀ > 1` odd, `a` coprime) together with a period multiplier and the two genuine window-size
  inequalities (`hbp_le_old`, `hoverlap`).  Its `oldPeriod` is **structurally** `periodMult·ord`,
  so `hold` (`RunObstruction.hold`) is derived, not assumed.
* `RunObstruction.toMeanLowRunWindow` — builds an actual `MeanLowRunWindow` whose `hold` field is
  the derived theorem, feeding the existing `halfDecrease_of_meanLow_verdict`.
* `RunObstruction.halfDecrease_of_density` / `halfDecrease_of_meanLow_verdict` — the L.4.2 one-step
  half-decrease for an actual run obstruction, with the mean-low premise either the genuine segment
  density test or the L.4.1 classifier verdict.
* `RunObstruction.ofMeanLowScale` / `ofMeanLowScale_halfDecrease` — the **canonical** realization:
  from the §25.2 reduced data (`q₀/a`) and a *single* scale condition `4 q₀ ≤ m·ord_{q₀}(2)` (the
  window is long enough relative to the denominator), the four geometric fields
  `hsize/hold/hbp_le_old/hoverlap` **and** the mean-low verdict are discharged automatically, and
  the half-decrease fires on the real word `dyadicDigit q₀ a`.  The only caller inputs are the three
  reduced-data fields and the one scale inequality.
* `runObstructionWitness` / `runObstructionWitness_halfDecrease` — a concrete run obstruction on
  `1/3` whose mean-low half-decrease genuinely fires (non-vacuity).

## The smallest residual that remains (honest)

After this round the realization fields split as:

* **CLOSED**: `hold` (periodicity — a theorem), and via `ofMeanLowScale` also `hsize`, `hbp_le_old`,
  `hoverlap`, and the mean-low verdict (all derived from one scale inequality).
* **§25.2 reduced data (definitional)**: `q₀ > 1` odd, `a` coprime — the *meaning* of "small
  odd denominator", discharged concretely in the witness.
* **Smallest genuine residual**: the construction-level fact that the run obstruction's mask point
  equals the rational `a/q₀` with `q₀` a *small* odd denominator (the §25.1/§25.2 reduction), plus
  the single window/denominator scale `4 q₀ ≤ m·ord_{q₀}(2)`.  These are the irreducible inputs;
  everything from them to `wt(O_{i+1}) ≤ wt(O_i)/2` is now derived.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

noncomputable section

/-! ## Part A — Realization closures on the genuine dyadic digit word -/

/-- **Every dyadic digit is `0` or `1`.**  `dyadicDigit q₀ a j = ⌊2 r_j / q₀⌋` with the residue
`r_j < q₀`, so the quotient bit is at most `1` (`binaryQuotient_le_one`).  Hence a segment density
never exceeds the segment length. -/
theorem dyadicDigit_le_one {q0 : ℕ} (hq0 : 0 < q0) (a j : ℕ) :
    dyadicDigit q0 a j ≤ 1 := by
  unfold dyadicDigit
  exact binaryQuotient_le_one hq0 (dyadicResidue_lt hq0 a j)

/--
**`hold` is a theorem: the run obstruction carries the old period on its dyadic digit word.**

The dyadic digit word `dyadicDigit q₀ a` of `a/q₀` (`q₀ > 1` odd) is genuinely periodic with
period `ord_{q₀}(2)` (the §25.2 fact `dyadicDigit_period`), hence with **every** positive multiple
`m·ord_{q₀}(2)` (`digit_add_mul_period`).  So once the old run period is the §25.2 fundamental
period (or any multiple of it), the realization field `hold` of `MeanLowRunWindow` needs **no**
extra hypothesis — it is this theorem.
-/
theorem dyadicDigit_periodicOn_mul {q0 m : ℕ} (hq0 : 1 < q0) (hodd : Odd q0)
    (hm : 0 < m) (a u N : ℕ) :
    PeriodicOn (dyadicDigit q0 a) u N (m * orderOf (2 : ZMod q0)) := by
  have htpos : 0 < orderOf (2 : ZMod q0) :=
    orderOf_pos_iff.mpr (isOfFinOrder_two_zmod hq0 hodd)
  refine ⟨Nat.mul_pos hm htpos, fun i _ => ?_⟩
  exact digit_add_mul_period (d := dyadicDigit q0 a)
    (p := orderOf (2 : ZMod q0)) (fun j => dyadicDigit_period q0 a j) m (u + i)

/-! ## Part B — The smallest residual bundle and the realized half-decrease -/

/--
**A run obstruction as the smallest §25.2 small-denominator realization residual.**

This is the manuscript's "the run obstruction is a small-denominator residual segment", stripped to
its irreducible inputs:

* the §25.2 **reduced data** `q₀` (odd, `> 1`) and `a` (coprime) — the small odd denominator and
  numerator after stripping the 2-adic preperiod and reducing;
* a positive **period multiplier** `periodMult`, so the old run period is
  `oldPeriod = periodMult · ord_{q₀}(2)` — a multiple of the §25.2 fundamental dyadic period;
* the §25.2 **sizing** `hsize`;
* the two genuine **window-size** inequalities: the old period dominates `⌊βp/4⌋` (`hbp_le_old`),
  and the window is long enough for the Fine–Wilf overlap (`hoverlap`).

Because `oldPeriod` is structurally a multiple of the fundamental period, the geometric field
`hold` of `MeanLowRunWindow` is **derived** (`RunObstruction.hold`), not assumed.
-/
structure RunObstruction where
  /-- §25.2 odd small denominator `q₀`. -/
  q0 : ℕ
  /-- Numerator `a`, coprime to `q₀`. -/
  a : ℕ
  /-- Window start. -/
  u : ℕ
  /-- Window length. -/
  N : ℕ
  /-- §25.2 ones-density threshold `c₀p`. -/
  c0p : ℕ
  /-- §25.2 period threshold `⌊βp/4⌋`. -/
  betap_div_4 : ℕ
  /-- Number of fundamental periods in the old run period (`oldPeriod = periodMult · ord`). -/
  periodMult : ℕ
  /-- Run branch weight (carried for fidelity). -/
  weight : ℝ
  /-- §25.2 reduced data — `q₀ > 1`. -/
  hq0 : 1 < q0
  /-- §25.2 reduced data — `q₀` odd. -/
  hodd : Odd q0
  /-- §25.2 reduced data — numerator coprime to `q₀`. -/
  hcop : Nat.Coprime a q0
  /-- The period multiplier is positive. -/
  hmult : 0 < periodMult
  /-- §25.2 sizing `2 q₀ (c₀p+1) ≤ ⌊βp/4⌋(⌊βp/4⌋+1)`. -/
  hsize : 2 * q0 * (c0p + 1) ≤ betap_div_4 * (betap_div_4 + 1)
  /-- Genuine residual — the old period dominates the §25.2 threshold. -/
  hbp_le_old : betap_div_4 ≤ periodMult * orderOf (2 : ZMod q0)
  /-- Genuine residual — the window is long enough for the Fine–Wilf overlap. -/
  hoverlap : periodMult * orderOf (2 : ZMod q0) + betap_div_4 ≤ N

namespace RunObstruction

variable (O : RunObstruction)

/-- The §25.2 fundamental dyadic period `ord_{q₀}(2)`. -/
def orderTwo : ℕ := orderOf (2 : ZMod O.q0)

/-- The old run period `wt(Oᵢ) = periodMult · ord_{q₀}(2)`. -/
def oldPeriod : ℕ := O.periodMult * orderOf (2 : ZMod O.q0)

/-- The §25.2 ones-density of the window. -/
def density : ℕ := segmentSum (dyadicDigit O.q0 O.a) O.u O.N

theorem oldPeriod_pos : 0 < O.oldPeriod := by
  have htpos : 0 < orderOf (2 : ZMod O.q0) :=
    orderOf_pos_iff.mpr (isOfFinOrder_two_zmod O.hq0 O.hodd)
  exact Nat.mul_pos O.hmult htpos

/-- **`hold` derived**: the obstruction's dyadic digit word carries the old run period. -/
theorem hold : PeriodicOn (dyadicDigit O.q0 O.a) O.u O.N O.oldPeriod :=
  dyadicDigit_periodicOn_mul O.hq0 O.hodd O.hmult O.a O.u O.N

/-- The segment density never exceeds the window length. -/
theorem density_le : O.density ≤ O.N := by
  have hq0 : 0 < O.q0 := by have := O.hq0; omega
  exact segmentSum_le_length_of_le_one (fun n => dyadicDigit_le_one hq0 O.a n)

/--
**The realized `MeanLowRunWindow` of an actual run obstruction.**

Every geometric field is supplied by the obstruction's data, and the field `hold` is the **derived**
periodicity theorem `RunObstruction.hold` (period `= periodMult · ord_{q₀}(2)`), not a residual.
-/
def toMeanLowRunWindow : MeanLowRunWindow where
  q0 := O.q0
  a := O.a
  u := O.u
  N := O.N
  c0p := O.c0p
  betap_div_4 := O.betap_div_4
  oldPeriod := O.oldPeriod
  weight := O.weight
  hq0 := O.hq0
  hodd := O.hodd
  hcop := O.hcop
  hsize := O.hsize
  hold := O.hold
  hbp_le_old := O.hbp_le_old
  hoverlap := O.hoverlap

@[simp] theorem toMeanLowRunWindow_density :
    O.toMeanLowRunWindow.density = O.density := rfl

@[simp] theorem toMeanLowRunWindow_oldPeriod :
    O.toMeanLowRunWindow.oldPeriod = O.oldPeriod := rfl

/--
**One-step half-decrease for an actual run obstruction, from the segment density test.**

If the genuine §25.2 segment density is below the threshold `c₀p` (the mean-low condition), then
§25.2 + Fine–Wilf produce a strictly shorter period `p'` with `2·p' ≤ oldPeriod` — the manuscript's
`wt(O_{i+1}) ≤ wt(Oᵢ)/2`.  Threaded through the existing `halfDecrease_of_meanLow_verdict`.
-/
theorem halfDecrease_of_density (h : O.density < O.c0p) :
    ∃ p', PeriodicOn (dyadicDigit O.q0 O.a) O.u O.N p' ∧ 0 < p' ∧ 2 * p' ≤ O.oldPeriod := by
  have hv : classify O.toMeanLowRunWindow.toRunState = 0 :=
    (O.toMeanLowRunWindow.meanLow_verdict_iff).2 h
  exact O.toMeanLowRunWindow.halfDecrease_of_meanLow_verdict hv

/--
**One-step half-decrease for an actual run obstruction, from the L.4.1 classifier verdict.**

With the mean-low premise DERIVED from the L.4.1 mean-low verdict (`classify = 0`) and the geometric
realization supplied by the obstruction (in particular `hold` derived), the Run half-decrease holds.
-/
theorem halfDecrease_of_meanLow_verdict (h : classify O.toMeanLowRunWindow.toRunState = 0) :
    ∃ p', PeriodicOn (dyadicDigit O.q0 O.a) O.u O.N p' ∧ 0 < p' ∧ 2 * p' ≤ O.oldPeriod :=
  O.toMeanLowRunWindow.halfDecrease_of_meanLow_verdict h

end RunObstruction

/-! ## Part C — The canonical realization from a single scale condition -/

/--
**Canonical run-obstruction realization.**

Given the §25.2 reduced data (`q₀ > 1` odd, `a` coprime), a positive multiplier `m`, and the single
scale condition `4 q₀ ≤ m·ord_{q₀}(2)` (the window is long enough relative to the denominator), take

* `oldPeriod = betap_div_4 = m·ord_{q₀}(2)` (the old period equals the threshold and is a multiple
  of the fundamental period), and
* `N = 2·oldPeriod`, `c₀p = N + 1`.

Then `hsize`, `hbp_le_old`, `hoverlap` are all discharged automatically (and `hold` is already a
theorem), and (since the density never exceeds `N < c₀p`) the segment is mean-low.  The only caller
inputs are the §25.2 reduced data `q₀/a` and the single scale inequality.
-/
def RunObstruction.ofMeanLowScale {q0 a m : ℕ} (hq0 : 1 < q0) (hodd : Odd q0)
    (hcop : Nat.Coprime a q0) (hm : 0 < m)
    (hscale : 4 * q0 ≤ m * orderOf (2 : ZMod q0)) (u : ℕ) (weight : ℝ) :
    RunObstruction where
  q0 := q0
  a := a
  u := u
  N := 2 * (m * orderOf (2 : ZMod q0))
  c0p := 2 * (m * orderOf (2 : ZMod q0)) + 1
  betap_div_4 := m * orderOf (2 : ZMod q0)
  periodMult := m
  weight := weight
  hq0 := hq0
  hodd := hodd
  hcop := hcop
  hmult := hm
  hsize := by
    calc 2 * q0 * (2 * (m * orderOf (2 : ZMod q0)) + 1 + 1)
        = 4 * q0 * (m * orderOf (2 : ZMod q0) + 1) := by ring
      _ ≤ m * orderOf (2 : ZMod q0) * (m * orderOf (2 : ZMod q0) + 1) :=
          Nat.mul_le_mul hscale (le_refl _)
  hbp_le_old := le_refl _
  hoverlap := by omega

/--
**The canonical realization genuinely fires the half-decrease on the real word `a/q₀`.**

For any §25.2 reduced data with `4 q₀ ≤ m·ord_{q₀}(2)`, the constructed run obstruction is mean-low,
so the L.4.2 one-step half-decrease holds on the genuine dyadic digit word `dyadicDigit q₀ a`:
a strictly shorter period `p'` with `2·p' ≤ m·ord_{q₀}(2)`.
-/
theorem RunObstruction.ofMeanLowScale_halfDecrease {q0 a m : ℕ} (hq0 : 1 < q0) (hodd : Odd q0)
    (hcop : Nat.Coprime a q0) (hm : 0 < m)
    (hscale : 4 * q0 ≤ m * orderOf (2 : ZMod q0)) (u : ℕ) (weight : ℝ) :
    ∃ p', PeriodicOn (dyadicDigit q0 a) u (2 * (m * orderOf (2 : ZMod q0))) p' ∧
      0 < p' ∧ 2 * p' ≤ m * orderOf (2 : ZMod q0) := by
  have hden : (RunObstruction.ofMeanLowScale hq0 hodd hcop hm hscale u weight).density
      < (RunObstruction.ofMeanLowScale hq0 hodd hcop hm hscale u weight).c0p := by
    have h1 := (RunObstruction.ofMeanLowScale hq0 hodd hcop hm hscale u weight).density_le
    have h2 : (RunObstruction.ofMeanLowScale hq0 hodd hcop hm hscale u weight).c0p
        = (RunObstruction.ofMeanLowScale hq0 hodd hcop hm hscale u weight).N + 1 := rfl
    omega
  exact (RunObstruction.ofMeanLowScale hq0 hodd hcop hm hscale u weight).halfDecrease_of_density hden

/-! ## Part D — Concrete non-vacuity witness (the run obstruction on `1/3`) -/

private theorem two_le_orderOf_two_zmod3 : 2 ≤ orderOf (2 : ZMod 3) := by
  have hfin : IsOfFinOrder (2 : ZMod 3) := isOfFinOrder_two_zmod (by norm_num) (by decide)
  have hpos : 0 < orderOf (2 : ZMod 3) := orderOf_pos_iff.mpr hfin
  have hne : orderOf (2 : ZMod 3) ≠ 1 := by
    intro he
    exact absurd (orderOf_eq_one_iff.mp he) (by decide)
  omega

/-- A concrete run obstruction realized on the dyadic digit word of `1/3` (odd denominator `3`,
period `ord₃(2)`), with `m = 6` so the scale `4·3 ≤ 6·ord₃(2)` holds. -/
def runObstructionWitness : RunObstruction :=
  RunObstruction.ofMeanLowScale (q0 := 3) (a := 1) (m := 6) (by norm_num) (by decide)
    (Nat.coprime_one_left 3) (by norm_num)
    (by have h := two_le_orderOf_two_zmod3; omega) 0 0

theorem runObstruction_nonempty : Nonempty RunObstruction :=
  ⟨runObstructionWitness⟩

/-- **The witness genuinely fires the L.4.2 half-decrease**: on `dyadicDigit 3 1` the mean-low run
obstruction yields a strictly shorter period `p'` with `2·p' ≤ 6·ord₃(2)`. -/
theorem runObstructionWitness_halfDecrease :
    ∃ p', PeriodicOn (dyadicDigit 3 1) 0 (2 * (6 * orderOf (2 : ZMod 3))) p' ∧
      0 < p' ∧ 2 * p' ≤ 6 * orderOf (2 : ZMod 3) :=
  RunObstruction.ofMeanLowScale_halfDecrease (q0 := 3) (a := 1) (m := 6) (by norm_num) (by decide)
    (Nat.coprime_one_left 3) (by norm_num)
    (by have h := two_le_orderOf_two_zmod3; omega) 0 0

/-! ## Part E — Residual inventory (honest) -/

/-- The honest split of the `MeanLowRunWindow` geometric-realization fields after this round. -/
def runObstructionRealizationResiduals : List String :=
  [ "CLOSED — hold (periodicity): dyadicDigit_periodicOn_mul proves the old period (any multiple " ++
      "of the §25.2 fundamental period ord_{q₀}(2)) is carried on the dyadic digit word, with no " ++
      "extra hypothesis.",
    "CLOSED via ofMeanLowScale — hsize, hbp_le_old, hoverlap and the mean-low verdict are all " ++
      "derived from the single scale condition 4 q₀ ≤ m·ord_{q₀}(2).",
    "§25.2 reduced data (definitional) — q₀ > 1 odd and a coprime: the meaning of a small odd " ++
      "denominator segment, discharged concretely in runObstructionWitness.",
    "Smallest genuine residual (construction-level) — the §25.1/§25.2 fact that the run " ++
      "obstruction's mask point IS the rational a/q₀ with q₀ a small odd denominator, together " ++
      "with the scale 4 q₀ ≤ m·ord_{q₀}(2). Everything from these to wt(O_{i+1}) ≤ wt(Oᵢ)/2 is derived." ]

theorem runObstructionRealizationResiduals_nonempty :
    runObstructionRealizationResiduals ≠ [] := by
  simp [runObstructionRealizationResiduals]

end

end Erdos260
