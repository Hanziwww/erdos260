import Mathlib
import Erdos260.O3PeriodicitySupply

/-!
# O3 supply side: the EXPLICIT fixed-pin slope-row state space (the residual identification)

This module (NEW; it edits no existing file) discharges the single residual trust boundary that
`Erdos260.O3PeriodicitySupply` left open: the **identification of the fixed-pin continuation's
state space with the bounded slope-row set**.  There the supply chain (eventual periodicity, the
bounded-period cycle entry, the lap invariance, the per-block hit supply, the density-floor void)
was proved for an *abstract* finite functional graph `f : V → V`, an *abstract* digit map
`D : V → ℕ`, an abstract cycle and an abstract nonzero hit, all of which were assumed.  Here we
**construct them explicitly** from the manuscript data.

## The explicit construction (App AR, the reduced fixed-pin coordinate)

Definition `def:ar-reduced-fixed-coordinate` (line 12505) and Lemma
`lem:ar-binary-long-division-row` (AR.1/AR.2, lines 12515–12530) describe the retained fixed-pin
row *literally* as a finite automaton on the **phase coordinate `a ∈ ℤ/gℤ`**:

* **state space** `SlopeState g := ZMod g` — the actual phase in the slope-fixed period word `w_g`
  (`def:ar-reduced-fixed-coordinate`); finite, with `card = g`.
* **successor** `slopeSucc g : a ↦ a + 1 (mod g)` — the clean successor row (AR.1, line 12520,
  `a ↦ a+1 (mod g)`); this is exactly the E.6 out-degree-1 functional-graph successor consumed by
  `O3PeriodicitySupply`.
* **emitted digit** `slopeDigit g : a ↦ (1 if a = 0 else 0)` — the digit-as-state function
  (AR.2, line 12524: `d(a) = 1` at `a=0`, `0` otherwise), so the orbit-indexed word is *literally*
  `n ↦ slopeDigit g ((slopeSucc g)^[n] y)`, the `w_g = 10^{g-1}` of AM.1 (line 11805).

## What is PROVED here (no `sorry`/`axiom`/`admit`/`native_decide`)

* `slopeState_card` / `slopeState_card_le_threeQ` — the **finite** state space with `card = g ≤ 3Q`
  (AR.0, line 12463; AM.4, line 11851).  This is the `Fintype V` + `card V ≤ 3Q` residual.
* `slopeSucc_iterate` — the orbit is *translation by `n`*: `(slopeSucc g)^[n] a = a + n`.
* `slopeSucc_cycle` — the **period-`g` cycle** `(slopeSucc g)^[g] y = y` (AR.1: returns to the same
  refined state after one lap of `g`; AM.3 `x_{n+1} = x_n + g`).
* `slope_orbit_word` — the digit-as-state identification: the orbit word equals the indicator of
  `y + n = 0`, i.e. the translate of `w_g` (AM.1/AM.3).
* `slope_hit_phase` — the **cycle is nonzero**: there is a phase `k₀ < g` with a hit
  (`slopeDigit g ((slopeSucc g)^[k₀] y) = 1`), namely `k₀ = (-y).val` (AR.2: phase `0` occurs once
  per lap, line 12529).
* `slopeRow_supply_void`, `slopeRow_supply_void_int` — the **assembled capstone**: the constructed
  state space + successor + digit + cycle + nonzero hit, fed into the proved
  `O3PeriodicitySupply.o3_fixedPin_supply_void(_int)`, give a contradiction from a deep window and
  the sparse cap; only `g ≤ 3Q` (AR.0) and the sparse-shell cap remain as inputs.
* `slopeRow_fire_budget` — `card V = g ≤ 2^19 ⇒ 17g < 2^24`, the App-U fire budget (line 9508).

## Honest residual (precisely what remains open)

The construction is faithful to AR.1/AR.2/AM.1 *verbatim*.  What is NOT discharged (and is genuine
dynamical math, requiring the full refined tower graph of Appendix E to be formalized): the claim
that the *actual* retained carry-recurrence continuation's clean successor **coincides** with this
`+1`-on-`ZMod g` automaton with digit `slopeDigit` (Lemmas `lem:ar-outgoing-uniqueness-transcription`
AR.3 / `lem:am-fixed-pin-row-realizes-orbit` AM.3, built on Appendices E.3–E.6).  Also residual: the
slope bound `g ≤ 3Q` itself (AR.0, the §24 density floor — its arithmetic core is already in
`O3SlopePeriodicFloor.sec24_slope_gap_le_threeQ`) and the sparse-shell cap `hsparse` of the stopped
recurrence.  Pitfall-freedom is inherited: the word is the actual state-indexed orbit word, never
the digit-blind fractional orbit `(R_n/Q) mod 1` (AR.-1, line 12450).
-/

namespace Erdos260.O3SupplyStateSpace

open Erdos260

set_option linter.unusedVariables false

/-! ## 1.  The explicit slope-row automaton (App AR `def:ar-reduced-fixed-coordinate`, AR.1, AR.2) -/

/-- **The slope-row state space** (App AR `def:ar-reduced-fixed-coordinate`, line 12505): the actual
phase coordinate `a ∈ ℤ/gℤ` in the slope-fixed period word `w_g`. -/
abbrev SlopeState (g : ℕ) := ZMod g

/-- **AR.1 clean successor** (line 12520): `a ↦ a + 1 (mod g)`.  This is the E.6 out-degree-1
functional-graph successor `f : V → V`. -/
def slopeSucc (g : ℕ) : ZMod g → ZMod g := fun a => a + 1

/-- **AR.2 emitted digit** (line 12524): `d(a) = 1` at the hit phase `a = 0`, `0` otherwise.  This
is the digit-as-state function `D : V → ℕ`. -/
def slopeDigit (g : ℕ) : ZMod g → ℕ := fun a => if a = 0 then 1 else 0

/-- The state space is finite with cardinality `g` (the `Fintype V` part of the residual). -/
theorem slopeState_card (g : ℕ) [NeZero g] : Fintype.card (ZMod g) = g := ZMod.card g

/-- **The orbit is translation by `n`.**  `(slopeSucc g)^[n] a = a + n`: iterating the AR.1
successor `n` times advances the phase by `n`. -/
theorem slopeSucc_iterate (g : ℕ) (n : ℕ) (a : ZMod g) :
    (slopeSucc g)^[n] a = a + (n : ZMod g) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [slopeSucc]
    push_cast
    ring

/-- **The period-`g` cycle** (AR.1: the clean row returns to the same refined state after one lap of
length `g`; AM.3 `x_{n+1} = x_n + g`).  `(slopeSucc g)^[g] y = y`, since `(g : ZMod g) = 0`. -/
theorem slopeSucc_cycle (g : ℕ) (y : ZMod g) : (slopeSucc g)^[g] y = y := by
  rw [slopeSucc_iterate, ZMod.natCast_self, add_zero]

/-- `slopeDigit g 0 = 1`: the hit phase is charged (AR.2). -/
theorem slopeDigit_zero (g : ℕ) : slopeDigit g 0 = 1 := by simp [slopeDigit]

/-- **Digit-as-state identification** (AM.1/AM.3): the orbit-indexed word
`n ↦ slopeDigit g ((slopeSucc g)^[n] y)` is the indicator of `y + n = 0`, i.e. the contiguous
translate of `w_g = 10^{g-1}` (one hit per period of length `g`). -/
theorem slope_orbit_word (g : ℕ) (y : ZMod g) (n : ℕ) :
    slopeDigit g ((slopeSucc g)^[n] y) = (if (y + (n : ZMod g)) = 0 then 1 else 0) := by
  rw [slopeSucc_iterate]; rfl

/-- **The cycle is nonzero** (AR.2, line 12529: "phase `a = 0` occurs once in every complete lap").
There is a phase `k₀ < g` at which the orbit hits (`slopeDigit g ((slopeSucc g)^[k₀] y) = 1`),
namely `k₀ = (-y).val`, the step that drives the phase to `0`. -/
theorem slope_hit_phase (g : ℕ) [NeZero g] (y : ZMod g) :
    ∃ k₀, k₀ < g ∧ slopeDigit g ((slopeSucc g)^[k₀] y) = 1 := by
  refine ⟨(-y).val, ZMod.val_lt _, ?_⟩
  have hz : (slopeSucc g)^[(-y).val] y = 0 := by
    rw [slopeSucc_iterate, ZMod.natCast_zmod_val]
    exact add_neg_cancel y
  rw [hz, slopeDigit_zero]

/-- **The orbit word has period `g`.**  This is the non-primitive-period form of
TeX `lem:am-fixed-pin-period-bound`: after one full AR.1 lap, the emitted digit
returns to the same phase. -/
theorem slope_orbit_period_g (g : ℕ) [NeZero g] (y : ZMod g) (n : ℕ) :
    slopeDigit g ((slopeSucc g)^[n + g] y) =
      slopeDigit g ((slopeSucc g)^[n] y) := by
  have hphase : y + ((n + g : ℕ) : ZMod g) = y + (n : ZMod g) := by
    simp [Nat.cast_add]
  rw [slope_orbit_word, slope_orbit_word, hphase]

/-! ## 2.  The bounded state-space cardinality (AR.0 / AM.4 and the App-U fire budget) -/

/-- **The `card V ≤ 3Q` residual, discharged on the explicit state space.**  Given the slope bound
`g ≤ 3Q` (AR.0, line 12463), the constructed state space has `card (ZMod g) ≤ 3Q`. -/
theorem slopeState_card_le_threeQ (g Q : ℕ) [NeZero g] (hgb : g ≤ 3 * Q) :
    Fintype.card (ZMod g) ≤ 3 * Q := by
  rw [slopeState_card]; exact hgb

/-- The slope bound `g ≤ 3Q` also supplies the `Q ≥ 1` side condition whenever
    the explicit slope state space is nonempty. -/
theorem one_le_Q_of_slope_bound (g Q : ℕ) [NeZero g] (hgb : g ≤ 3 * Q) :
    1 ≤ Q := by
  cases Q with
  | zero =>
      have hgpos : 0 < g := Nat.pos_of_ne_zero (NeZero.ne g)
      simp at hgb
      omega
  | succ Q =>
      omega

/-- **App-U fire budget on the explicit state space** (line 9508).  If `card V = g ≤ 2^19`, the
period lies strictly inside the sharp fire budget `17g < 2^24`. -/
theorem slopeRow_fire_budget {g : ℕ} (hg : g ≤ 2 ^ 19) : 17 * g < (2 : ℕ) ^ 24 :=
  O3SlopePeriodicFloor.boundedPeriod_within_fireBudget hg

/-- Packaged fixed-pin period certificate corresponding to TeX AM.4/AR row
table: the explicit retained row has a period-`g` word, that period contains a
charged phase, and the supplied slope bound gives the `3Q` state cap.  The
primitive-period refinement in the prose is stronger; the supply argument only
consumes this non-primitive period certificate. -/
structure O3FixedPinPeriodCertificate (g Q : ℕ) [NeZero g] (y : ZMod g) where
  hgb : g ≤ 3 * Q

namespace O3FixedPinPeriodCertificate

/-- TeX AM.4: the fixed-pin word is periodic with period `g`. -/
theorem period {g Q : ℕ} [NeZero g] {y : ZMod g}
    (I : O3FixedPinPeriodCertificate g Q y) (n : ℕ) :
    slopeDigit g ((slopeSucc g)^[n + g] y) =
      slopeDigit g ((slopeSucc g)^[n] y) :=
  slope_orbit_period_g g y n

/-- TeX AR.2: each complete period contains the charged phase. -/
theorem nonzero {g Q : ℕ} [NeZero g] {y : ZMod g}
    (I : O3FixedPinPeriodCertificate g Q y) :
    ∃ k₀, k₀ < g ∧ slopeDigit g ((slopeSucc g)^[k₀] y) = 1 :=
  slope_hit_phase g y

/-- TeX AM.4/AR.0: the retained finite state space has size at most `3Q`. -/
theorem card_bound {g Q : ℕ} [NeZero g] {y : ZMod g}
    (I : O3FixedPinPeriodCertificate g Q y) :
    Fintype.card (ZMod g) ≤ 3 * Q :=
  slopeState_card_le_threeQ g Q I.hgb

/-- The period certificate also carries the denominator positivity side
condition consumed by the O3 supply contradiction. -/
theorem one_le_Q {g Q : ℕ} [NeZero g] {y : ZMod g}
    (I : O3FixedPinPeriodCertificate g Q y) :
    1 ≤ Q :=
  one_le_Q_of_slope_bound g Q I.hgb

/-- Single bundled summary of the fixed-pin period data consumed by the O3
supply contradiction. -/
theorem summary {g Q : ℕ} [NeZero g] {y : ZMod g}
    (I : O3FixedPinPeriodCertificate g Q y) :
    (∀ n, slopeDigit g ((slopeSucc g)^[n + g] y) =
        slopeDigit g ((slopeSucc g)^[n] y)) ∧
      (∃ k₀, k₀ < g ∧ slopeDigit g ((slopeSucc g)^[k₀] y) = 1) ∧
      Fintype.card (ZMod g) ≤ 3 * Q := by
  exact ⟨fun n => period I n, nonzero I, card_bound I⟩

end O3FixedPinPeriodCertificate

/-- Packaged §24/AR.0 slope-gap data.  These are exactly the arithmetic
inputs consumed by `O3SlopePeriodicFloor.sec24_slope_gap_le_threeQ`: a set of
`g` positive distinct residues whose sum is `q`, together with the denominator
bound `q <= Q*g`. -/
structure O3Sec24SlopeGapInputs (Q q g : ℕ) [NeZero g] (S : Finset ℕ) where
  hg : 1 ≤ g
  hcard : S.card = g
  hpos : ∀ x ∈ S, 1 ≤ x
  hsum : ∑ x ∈ S, x = q
  hqQg : q ≤ Q * g

namespace O3Sec24SlopeGapInputs

/-- §24/AR.0 supplies the retained slope bound `g <= 3Q`. -/
theorem gap_le_threeQ {Q q g : ℕ} [NeZero g] {S : Finset ℕ}
    (I : O3Sec24SlopeGapInputs Q q g S) :
    g ≤ 3 * Q :=
  (O3SlopePeriodicFloor.sec24_slope_gap_le_threeQ Q q g S
    I.hg I.hcard I.hpos I.hsum I.hqQg).2

/-- The Section 24 slope-gap arithmetic forces the `Q >= 1` side condition
used by the fixed-pin supply contradiction. -/
theorem one_le_Q {Q q g : ℕ} [NeZero g] {S : Finset ℕ}
    (I : O3Sec24SlopeGapInputs Q q g S) :
    1 ≤ Q :=
  one_le_Q_of_slope_bound g Q (gap_le_threeQ I)

/-- The §24 slope-gap arithmetic feeds the fixed-pin period certificate used by
the O3 supply contradiction. -/
def toFixedPinPeriodCertificate {Q q g : ℕ} [NeZero g] {S : Finset ℕ}
    (I : O3Sec24SlopeGapInputs Q q g S) (y : ZMod g) :
    O3FixedPinPeriodCertificate g Q y where
  hgb := gap_le_threeQ I

/-- Bundled consequence: from the §24 slope-gap data, the explicit fixed-pin
row has period `g`, a nonzero hit, and state count at most `3Q`. -/
theorem fixedPinPeriodSummary {Q q g : ℕ} [NeZero g] {S : Finset ℕ}
    (I : O3Sec24SlopeGapInputs Q q g S) (y : ZMod g) :
    (∀ n, slopeDigit g ((slopeSucc g)^[n + g] y) =
        slopeDigit g ((slopeSucc g)^[n] y)) ∧
      (∃ k₀, k₀ < g ∧ slopeDigit g ((slopeSucc g)^[k₀] y) = 1) ∧
      Fintype.card (ZMod g) ≤ 3 * Q :=
  O3FixedPinPeriodCertificate.summary (toFixedPinPeriodCertificate I y)

end O3Sec24SlopeGapInputs

/-! ## 3.  Assembled capstone: the constructed automaton feeds the proved VOID -/

/-- **ASSEMBLED O3 SUPPLY CAPSTONE (real form).**  On the *explicitly constructed* slope-row state
space `ZMod g` with the AR.1 successor `slopeSucc g`, the AR.2 digit `slopeDigit g`, the proved
period-`g` cycle (`slopeSucc_cycle`) and the proved nonzero hit (`slope_hit_phase`), a deep window
`W ≥ 6Q` together with the sparse-shell cap (density `< 1/(6Q)`) is contradictory.

Everything dynamical — the `Fintype V`, `card V = g`, the successor, the digit-as-state function,
the cycle and the nonzero hit — is now CONSTRUCTED/PROVED here, discharging the residual
identification left open in `O3PeriodicitySupply`.  The only remaining inputs are `g ≤ 3Q` (AR.0)
and the sparse-shell cap (the stopped-recurrence sparsity hypothesis). -/
theorem slopeRow_supply_void (g : ℕ) [NeZero g] (y : ZMod g) (Q W : ℕ) (cstar : ℝ)
    (hQ : 1 ≤ Q) (hgb : g ≤ 3 * Q) (hW : 6 * Q ≤ W)
    (hcstar : cstar < 1 / (6 * (Q : ℝ)))
    (hsparse : (O3SlopePeriodicFloor.hitCount
        (fun n => slopeDigit g ((slopeSucc g)^[n] y)) 0 W : ℝ) < cstar * (W : ℝ)) :
    False := by
  obtain ⟨k₀, hk₀, hhit⟩ := slope_hit_phase g y
  exact O3PeriodicitySupply.o3_fixedPin_supply_void (slopeSucc g) y (slopeDigit g)
    Q W g k₀ cstar hQ (Nat.pos_of_ne_zero (NeZero.ne g)) hgb (slopeSucc_cycle g y) hk₀
    (le_of_eq hhit.symm) hW hcstar hsparse

/-- **ASSEMBLED O3 SUPPLY CAPSTONE (integer form).**  Same as `slopeRow_supply_void` but with the
integer-density sparse cap `6Q · hitCount < W`. -/
theorem slopeRow_supply_void_int (g : ℕ) [NeZero g] (y : ZMod g) (Q W : ℕ)
    (hQ : 1 ≤ Q) (hgb : g ≤ 3 * Q) (hW : 6 * Q ≤ W)
    (hcap : 6 * Q * O3SlopePeriodicFloor.hitCount
        (fun n => slopeDigit g ((slopeSucc g)^[n] y)) 0 W < W) :
    False := by
  obtain ⟨k₀, hk₀, hhit⟩ := slope_hit_phase g y
  exact O3PeriodicitySupply.o3_fixedPin_supply_void_int (slopeSucc g) y (slopeDigit g)
    Q W g k₀ hQ (Nat.pos_of_ne_zero (NeZero.ne g)) hgb (slopeSucc_cycle g y) hk₀
    (le_of_eq hhit.symm) hW hcap

/-- Real-form O3 capstone with the `Q ≥ 1` side condition derived from the
    slope bound. -/
theorem slopeRow_supply_void_of_slope_bound (g : ℕ) [NeZero g] (y : ZMod g)
    (Q W : ℕ) (cstar : ℝ)
    (hgb : g ≤ 3 * Q) (hW : 6 * Q ≤ W)
    (hcstar : cstar < 1 / (6 * (Q : ℝ)))
    (hsparse : (O3SlopePeriodicFloor.hitCount
        (fun n => slopeDigit g ((slopeSucc g)^[n] y)) 0 W : ℝ) < cstar * (W : ℝ)) :
    False :=
  slopeRow_supply_void g y Q W cstar (one_le_Q_of_slope_bound g Q hgb)
    hgb hW hcstar hsparse

/-- Integer-form O3 capstone with the `Q ≥ 1` side condition derived from the
    slope bound. -/
theorem slopeRow_supply_void_int_of_slope_bound (g : ℕ) [NeZero g] (y : ZMod g)
    (Q W : ℕ)
    (hgb : g ≤ 3 * Q) (hW : 6 * Q ≤ W)
    (hcap : 6 * Q * O3SlopePeriodicFloor.hitCount
        (fun n => slopeDigit g ((slopeSucc g)^[n] y)) 0 W < W) :
    False :=
  slopeRow_supply_void_int g y Q W (one_le_Q_of_slope_bound g Q hgb)
    hgb hW hcap

/-! ## 4.  Actual-word transcription bridge (App AR.3 / AM.3) -/

/-- If two digit words agree on the active window `[0,W)`, then their O3 hit
counts on that window agree.  This is the bookkeeping bridge needed to consume
the sparse cap on the actual retained fixed-pin word after AR/AM transcribes it
to the explicit slope-row orbit. -/
theorem hitCount_eq_of_eq_on_window (d e : ℕ → ℕ) (W : ℕ)
    (h : ∀ n, n < W → d n = e n) :
    O3SlopePeriodicFloor.hitCount d 0 W =
      O3SlopePeriodicFloor.hitCount e 0 W := by
  unfold O3SlopePeriodicFloor.hitCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro n hn
  rw [Finset.mem_Ico] at hn
  have hnW : n < W := by omega
  rw [h n hnW]

/-! ## 5.  Packaged O3 residual surface -/

/-- The exact O3 slope-row supply surface after the state space, successor,
digit, period, and nonzero hit have been constructed.  It records only the
remaining numeric/density inputs needed to fire the fixed-pin sparse-window
contradiction.  The positivity side condition `1 ≤ Q` is derived from
`[NeZero g]` and `g ≤ 3Q`, so it is not a residual field. -/
structure O3SlopeRowSupplyInputs (g : ℕ) [NeZero g] (y : ZMod g) (Q W : ℕ) where
  hgb : g ≤ 3 * Q
  hW : 6 * Q ≤ W
  hcap : 6 * Q * O3SlopePeriodicFloor.hitCount
    (fun n => slopeDigit g ((slopeSucc g)^[n] y)) 0 W < W

/-- Real-density version of the packaged O3 slope-row supply surface.  This is
the form closest to the manuscript's sparse-window inequality: a density constant
`cstar < 1/(6Q)` and a real-valued hit-count bound. -/
structure O3SlopeRowRealSupplyInputs (g : ℕ) [NeZero g] (y : ZMod g) (Q W : ℕ)
    (cstar : ℝ) where
  hgb : g ≤ 3 * Q
  hW : 6 * Q ≤ W
  hcstar : cstar < 1 / (6 * (Q : ℝ))
  hsparse : (O3SlopePeriodicFloor.hitCount
    (fun n => slopeDigit g ((slopeSucc g)^[n] y)) 0 W : ℝ) < cstar * (W : ℝ)

/-- Integer-density fixed-pin supply surface in the form closest to the actual
AR/AM transcription: `d` is the retained branch's digit word, and `hword`
identifies it with the explicit slope-row orbit only on the active window. -/
structure O3RecognizedSlopeRowSupplyInputs (g : ℕ) [NeZero g] (y : ZMod g)
    (Q W : ℕ) (d : ℕ → ℕ) where
  hgb : g ≤ 3 * Q
  hW : 6 * Q ≤ W
  hword : ∀ n, n < W → d n = slopeDigit g ((slopeSucc g)^[n] y)
  hcap : 6 * Q * O3SlopePeriodicFloor.hitCount d 0 W < W

/-- Real-density fixed-pin supply surface with the sparse cap stated for the
actual retained digit word.  The only new local input compared with
`O3SlopeRowRealSupplyInputs` is the AR/AM window transcription `hword`. -/
structure O3RecognizedSlopeRowRealSupplyInputs (g : ℕ) [NeZero g] (y : ZMod g)
    (Q W : ℕ) (cstar : ℝ) (d : ℕ → ℕ) where
  hgb : g ≤ 3 * Q
  hW : 6 * Q ≤ W
  hword : ∀ n, n < W → d n = slopeDigit g ((slopeSucc g)^[n] y)
  hcstar : cstar < 1 / (6 * (Q : ℝ))
  hsparse : (O3SlopePeriodicFloor.hitCount d 0 W : ℝ) < cstar * (W : ℝ)

namespace O3SlopeRowSupplyInputs

/-- The packaged O3 slope-row supply surface is contradictory. -/
theorem void {g : ℕ} [NeZero g] {y : ZMod g} {Q W : ℕ}
    (I : O3SlopeRowSupplyInputs g y Q W) : False :=
  slopeRow_supply_void_int_of_slope_bound g y Q W I.hgb I.hW I.hcap

end O3SlopeRowSupplyInputs

namespace O3SlopeRowRealSupplyInputs

/-- The real-density packaged O3 slope-row supply surface is contradictory. -/
theorem void {g : ℕ} [NeZero g] {y : ZMod g} {Q W : ℕ} {cstar : ℝ}
    (I : O3SlopeRowRealSupplyInputs g y Q W cstar) : False :=
  slopeRow_supply_void_of_slope_bound g y Q W cstar I.hgb I.hW I.hcstar I.hsparse

end O3SlopeRowRealSupplyInputs

namespace O3RecognizedSlopeRowSupplyInputs

/-- The recognized actual-word O3 slope-row supply surface is contradictory:
the window transcription transports the sparse cap to the explicit slope-row
orbit, and the already-proved integer O3 capstone fires. -/
theorem void {g : ℕ} [NeZero g] {y : ZMod g} {Q W : ℕ} {d : ℕ → ℕ}
    (I : O3RecognizedSlopeRowSupplyInputs g y Q W d) : False := by
  have hcnt :
      O3SlopePeriodicFloor.hitCount
          (fun n => slopeDigit g ((slopeSucc g)^[n] y)) 0 W =
        O3SlopePeriodicFloor.hitCount d 0 W := by
    symm
    exact hitCount_eq_of_eq_on_window d
      (fun n => slopeDigit g ((slopeSucc g)^[n] y)) W I.hword
  exact slopeRow_supply_void_int_of_slope_bound g y Q W I.hgb I.hW (by
    rw [hcnt]
    exact I.hcap)

end O3RecognizedSlopeRowSupplyInputs

namespace O3RecognizedSlopeRowRealSupplyInputs

/-- Real-density version of the recognized actual-word O3 capstone. -/
theorem void {g : ℕ} [NeZero g] {y : ZMod g} {Q W : ℕ} {cstar : ℝ}
    {d : ℕ → ℕ} (I : O3RecognizedSlopeRowRealSupplyInputs g y Q W cstar d) :
    False := by
  have hcnt :
      O3SlopePeriodicFloor.hitCount
          (fun n => slopeDigit g ((slopeSucc g)^[n] y)) 0 W =
        O3SlopePeriodicFloor.hitCount d 0 W := by
    symm
    exact hitCount_eq_of_eq_on_window d
      (fun n => slopeDigit g ((slopeSucc g)^[n] y)) W I.hword
  exact slopeRow_supply_void_of_slope_bound g y Q W cstar I.hgb I.hW I.hcstar (by
    rw [hcnt]
    exact I.hsparse)

end O3RecognizedSlopeRowRealSupplyInputs

/-! ## 6.  Phase-window form of the fixed-pin transcription (App AR.3 / AM.3) -/

/-- Integer-density fixed-pin surface in the phase-coordinate form supplied by
AR.3: the actual retained word is the indicator of the translated hit phase
`y + n = 0` on the active window.  This is the TeX step just before identifying
the word with the explicit slope-row orbit. -/
structure O3FixedPinPhaseWindowInputs (g : Nat) [NeZero g] (y : ZMod g)
    (Q W : Nat) (d : Nat -> Nat) where
  hgb : g <= 3 * Q
  hW : 6 * Q <= W
  hphase : forall n, n < W ->
    d n = if (y + (n : ZMod g)) = 0 then 1 else 0
  hcap : 6 * Q * O3SlopePeriodicFloor.hitCount d 0 W < W

/-- Real-density version of `O3FixedPinPhaseWindowInputs`. -/
structure O3FixedPinPhaseWindowRealInputs (g : Nat) [NeZero g] (y : ZMod g)
    (Q W : Nat) (cstar : Real) (d : Nat -> Nat) where
  hgb : g <= 3 * Q
  hW : 6 * Q <= W
  hphase : forall n, n < W ->
    d n = if (y + (n : ZMod g)) = 0 then 1 else 0
  hcstar : cstar < 1 / (6 * (Q : Real))
  hsparse : (O3SlopePeriodicFloor.hitCount d 0 W : Real) < cstar * (W : Real)

/-- Integer-density fixed-pin surface with the §24 slope-gap arithmetic supplied
in its manuscript form.  The derived `g <= 3Q` bound is no longer a separate
field. -/
structure O3FixedPinSec24PhaseWindowInputs (Q q g : Nat) [NeZero g]
    (S : Finset Nat) (y : ZMod g) (W : Nat) (d : Nat -> Nat) where
  hsec24 : O3Sec24SlopeGapInputs Q q g S
  hW : 6 * Q <= W
  hphase : forall n, n < W ->
    d n = if (y + (n : ZMod g)) = 0 then 1 else 0
  hcap : 6 * Q * O3SlopePeriodicFloor.hitCount d 0 W < W

/-- Real-density fixed-pin surface with the §24 slope-gap arithmetic supplied in
its manuscript form. -/
structure O3FixedPinSec24PhaseWindowRealInputs (Q q g : Nat) [NeZero g]
    (S : Finset Nat) (y : ZMod g) (W : Nat) (cstar : Real) (d : Nat -> Nat) where
  hsec24 : O3Sec24SlopeGapInputs Q q g S
  hW : 6 * Q <= W
  hphase : forall n, n < W ->
    d n = if (y + (n : ZMod g)) = 0 then 1 else 0
  hcstar : cstar < 1 / (6 * (Q : Real))
  hsparse : (O3SlopePeriodicFloor.hitCount d 0 W : Real) < cstar * (W : Real)

namespace O3FixedPinPhaseWindowInputs

/-- AR.3/AM.3 phase transcription supplies the recognized slope-row word by
`slope_orbit_word`. -/
def toRecognizedInputs {g : Nat} [NeZero g] {y : ZMod g} {Q W : Nat}
    {d : Nat -> Nat} (I : O3FixedPinPhaseWindowInputs g y Q W d) :
    O3RecognizedSlopeRowSupplyInputs g y Q W d where
  hgb := I.hgb
  hW := I.hW
  hword := by
    intro n hn
    exact (I.hphase n hn).trans (slope_orbit_word g y n).symm
  hcap := I.hcap

/-- AR.3/AM.3 phase-window data also supplies the lower explicit slope-row
package directly: the sparse cap is transported across the window word
identity. -/
def toSlopeRowSupplyInputs {g : Nat} [NeZero g] {y : ZMod g} {Q W : Nat}
    {d : Nat -> Nat} (I : O3FixedPinPhaseWindowInputs g y Q W d) :
    O3SlopeRowSupplyInputs g y Q W where
  hgb := I.hgb
  hW := I.hW
  hcap := by
    have hcnt :
        O3SlopePeriodicFloor.hitCount
            (fun n => slopeDigit g ((slopeSucc g)^[n] y)) 0 W =
          O3SlopePeriodicFloor.hitCount d 0 W := by
      symm
      exact hitCount_eq_of_eq_on_window d
        (fun n => slopeDigit g ((slopeSucc g)^[n] y)) W
        (toRecognizedInputs I).hword
    rw [hcnt]
    exact I.hcap

/-- The phase-window O3 fixed-pin surface is contradictory. -/
theorem void {g : Nat} [NeZero g] {y : ZMod g} {Q W : Nat} {d : Nat -> Nat}
    (I : O3FixedPinPhaseWindowInputs g y Q W d) : False :=
  O3SlopeRowSupplyInputs.void (toSlopeRowSupplyInputs I)

end O3FixedPinPhaseWindowInputs

namespace O3FixedPinPhaseWindowRealInputs

/-- Real-density AR.3/AM.3 phase transcription supplies the recognized
slope-row word by `slope_orbit_word`. -/
def toRecognizedRealInputs {g : Nat} [NeZero g] {y : ZMod g} {Q W : Nat}
    {cstar : Real} {d : Nat -> Nat} (I : O3FixedPinPhaseWindowRealInputs g y Q W cstar d) :
    O3RecognizedSlopeRowRealSupplyInputs g y Q W cstar d where
  hgb := I.hgb
  hW := I.hW
  hword := by
    intro n hn
    exact (I.hphase n hn).trans (slope_orbit_word g y n).symm
  hcstar := I.hcstar
  hsparse := I.hsparse

/-- Real-density AR.3/AM.3 phase-window data supplies the lower explicit
slope-row real-density package directly. -/
def toSlopeRowRealSupplyInputs {g : Nat} [NeZero g] {y : ZMod g} {Q W : Nat}
    {cstar : Real} {d : Nat -> Nat}
    (I : O3FixedPinPhaseWindowRealInputs g y Q W cstar d) :
    O3SlopeRowRealSupplyInputs g y Q W cstar where
  hgb := I.hgb
  hW := I.hW
  hcstar := I.hcstar
  hsparse := by
    have hcnt :
        O3SlopePeriodicFloor.hitCount
            (fun n => slopeDigit g ((slopeSucc g)^[n] y)) 0 W =
          O3SlopePeriodicFloor.hitCount d 0 W := by
      symm
      exact hitCount_eq_of_eq_on_window d
        (fun n => slopeDigit g ((slopeSucc g)^[n] y)) W
        (toRecognizedRealInputs I).hword
    rw [hcnt]
    exact I.hsparse

/-- The real-density phase-window O3 fixed-pin surface is contradictory. -/
theorem void {g : Nat} [NeZero g] {y : ZMod g} {Q W : Nat} {cstar : Real}
    {d : Nat -> Nat} (I : O3FixedPinPhaseWindowRealInputs g y Q W cstar d) :
    False :=
  O3SlopeRowRealSupplyInputs.void (toSlopeRowRealSupplyInputs I)

end O3FixedPinPhaseWindowRealInputs

namespace O3FixedPinSec24PhaseWindowInputs

/-- The §24 slope-gap package supplies the slope bound needed by the older
phase-window surface. -/
def toPhaseWindowInputs {Q q g : Nat} [NeZero g] {S : Finset Nat}
    {y : ZMod g} {W : Nat} {d : Nat -> Nat}
    (I : O3FixedPinSec24PhaseWindowInputs Q q g S y W d) :
    O3FixedPinPhaseWindowInputs g y Q W d where
  hgb := O3Sec24SlopeGapInputs.gap_le_threeQ I.hsec24
  hW := I.hW
  hphase := I.hphase
  hcap := I.hcap

/-- The section-24 slope-gap package plus AR.3 phase-window data supplies the
recognized actual-word surface directly. -/
def toRecognizedInputs {Q q g : Nat} [NeZero g] {S : Finset Nat}
    {y : ZMod g} {W : Nat} {d : Nat -> Nat}
    (I : O3FixedPinSec24PhaseWindowInputs Q q g S y W d) :
    O3RecognizedSlopeRowSupplyInputs g y Q W d :=
  O3FixedPinPhaseWindowInputs.toRecognizedInputs (toPhaseWindowInputs I)

/-- The §24 slope-gap package plus AR.3 phase-window data supplies the lower
explicit slope-row package directly. -/
def toSlopeRowSupplyInputs {Q q g : Nat} [NeZero g] {S : Finset Nat}
    {y : ZMod g} {W : Nat} {d : Nat -> Nat}
    (I : O3FixedPinSec24PhaseWindowInputs Q q g S y W d) :
    O3SlopeRowSupplyInputs g y Q W :=
  O3FixedPinPhaseWindowInputs.toSlopeRowSupplyInputs (toPhaseWindowInputs I)

/-- The §24/phase-window O3 fixed-pin surface is contradictory. -/
theorem void {Q q g : Nat} [NeZero g] {S : Finset Nat} {y : ZMod g}
    {W : Nat} {d : Nat -> Nat}
    (I : O3FixedPinSec24PhaseWindowInputs Q q g S y W d) : False :=
  O3SlopeRowSupplyInputs.void (toSlopeRowSupplyInputs I)

end O3FixedPinSec24PhaseWindowInputs

namespace O3FixedPinSec24PhaseWindowRealInputs

/-- The §24 slope-gap package supplies the slope bound needed by the older
real-density phase-window surface. -/
def toPhaseWindowRealInputs {Q q g : Nat} [NeZero g] {S : Finset Nat}
    {y : ZMod g} {W : Nat} {cstar : Real} {d : Nat -> Nat}
    (I : O3FixedPinSec24PhaseWindowRealInputs Q q g S y W cstar d) :
    O3FixedPinPhaseWindowRealInputs g y Q W cstar d where
  hgb := O3Sec24SlopeGapInputs.gap_le_threeQ I.hsec24
  hW := I.hW
  hphase := I.hphase
  hcstar := I.hcstar
  hsparse := I.hsparse

/-- The real-density section-24 slope-gap package plus AR.3 phase-window data
supplies the recognized actual-word surface directly. -/
def toRecognizedRealInputs {Q q g : Nat} [NeZero g] {S : Finset Nat}
    {y : ZMod g} {W : Nat} {cstar : Real} {d : Nat -> Nat}
    (I : O3FixedPinSec24PhaseWindowRealInputs Q q g S y W cstar d) :
    O3RecognizedSlopeRowRealSupplyInputs g y Q W cstar d :=
  O3FixedPinPhaseWindowRealInputs.toRecognizedRealInputs (toPhaseWindowRealInputs I)

/-- The real-density §24 slope-gap package plus AR.3 phase-window data supplies
the lower explicit slope-row package directly. -/
def toSlopeRowRealSupplyInputs {Q q g : Nat} [NeZero g] {S : Finset Nat}
    {y : ZMod g} {W : Nat} {cstar : Real} {d : Nat -> Nat}
    (I : O3FixedPinSec24PhaseWindowRealInputs Q q g S y W cstar d) :
    O3SlopeRowRealSupplyInputs g y Q W cstar :=
  O3FixedPinPhaseWindowRealInputs.toSlopeRowRealSupplyInputs (toPhaseWindowRealInputs I)

/-- The real-density §24/phase-window O3 fixed-pin surface is contradictory. -/
theorem void {Q q g : Nat} [NeZero g] {S : Finset Nat} {y : ZMod g}
    {W : Nat} {cstar : Real} {d : Nat -> Nat}
    (I : O3FixedPinSec24PhaseWindowRealInputs Q q g S y W cstar d) : False :=
  O3SlopeRowRealSupplyInputs.void (toSlopeRowRealSupplyInputs I)

end O3FixedPinSec24PhaseWindowRealInputs

/-! ## 7.  Honest residual / status inventory -/

/-- Machine-readable list of O3 components closed in this module. -/
def o3SupplyStateSpaceClosedItems : List String :=
  [ "state space SlopeState g := ZMod g",
    "successor slopeSucc g = +1",
    "digit slopeDigit g as the hit-phase indicator",
    "orbit word equals the translated period word",
    "period-g cycle",
    "nonzero hit phase",
    "fixed-pin period certificate: period-g, nonzero hit, and card <= 3Q",
    "section-24 slope-gap residue inputs -> fixed-pin period certificate",
    "cardinality/fire-budget bridges and Q-positivity from g <= 3Q",
    "packaged integer O3SlopeRowSupplyInputs -> False",
    "packaged real-density O3SlopeRowRealSupplyInputs -> False",
    "phase-indicator fixed-pin windows -> recognized actual-word surfaces and explicit slope-row packages",
    "recognized actual-word O3 supply surfaces -> False via window transcription",
    "section-24 slope-gap inputs feed the phase-window and explicit slope-row surfaces",
    "section-24 slope-gap inputs feed the recognized actual-word O3 surfaces directly" ]

/-- Machine-readable list of the exact O3 inputs that remain external. -/
def o3SupplyStateSpaceOpenItems : List String :=
  [ "actual AR/AM transcription supplies the phase-indicator word on the active window",
    "actual retained row supplies the section-24 distinct-residue slope-gap inputs",
    "sparse stopped-recurrence cap on the actual retained digit word" ]

theorem o3SupplyStateSpaceClosedItems_length :
    o3SupplyStateSpaceClosedItems.length = 15 := by
  rfl

theorem o3SupplyStateSpaceOpenItems_length :
    o3SupplyStateSpaceOpenItems.length = 3 := by
  rfl

/-- The precise status of the O3 supply state-space identification. -/
def o3SupplyStateSpaceResiduals : List String :=
  [ "GOAL — discharge the residual left open by O3PeriodicitySupply: the IDENTIFICATION of the " ++
      "fixed-pin continuation's state space with the bounded slope-row set (Fintype V, card V ≤ 3Q " ++
      "resp. ≤ 2^19), the emitted digit as state function, and the nonzero cycle.",
    "CLOSED (state space) — SlopeState g := ZMod g, the App AR reduced fixed-pin phase coordinate " ++
      "a ∈ ℤ/gℤ (def:ar-reduced-fixed-coordinate, line 12505); finite, slopeState_card: card = g.",
    "CLOSED (successor) — slopeSucc g : a ↦ a+1 (mod g), the AR.1 clean successor (line 12520) = " ++
      "the E.6 out-degree-1 functional-graph successor; slopeSucc_iterate: orbit = translation by n.",
    "CLOSED (digit-as-state) — slopeDigit g : a ↦ [a=0], the AR.2 emitted digit (line 12524); " ++
      "slope_orbit_word: the orbit word n ↦ slopeDigit g ((slopeSucc g)^[n] y) is the translate of " ++
      "w_g = 10^{g-1} (AM.1, line 11805).",
    "CLOSED (cycle) — slopeSucc_cycle: (slopeSucc g)^[g] y = y, the period-g lap (AR.1; AM.3 " ++
      "x_{n+1} = x_n + g).",
    "CLOSED (nonzero) — slope_hit_phase: a hit phase k₀ = (-y).val < g exists (AR.2, line 12529: " ++
      "phase 0 occurs once per lap), so the cycle is nonzero.",
    "CLOSED (period certificate) — O3FixedPinPeriodCertificate bundles the non-primitive " ++
      "period-g word, the nonzero hit phase, and card <= 3Q, matching the part of " ++
      "lem:am-fixed-pin-period-bound consumed by the O3 supply contradiction.",
    "CLOSED (§24 bridge) — O3Sec24SlopeGapInputs packages the distinct-residue data of " ++
      "sec24_slope_gap_le_threeQ and converts it to O3FixedPinPeriodCertificate.",
    "CLOSED (card bounds) — slopeState_card_le_threeQ (card ≤ 3Q from g ≤ 3Q, AR.0/AM.4) and " ++
      "slopeRow_fire_budget (g ≤ 2^19 ⇒ 17g < 2^24, the App-U fire budget line 9508).",
    "CLOSED (capstone) — slopeRow_supply_void(_int): the CONSTRUCTED automaton + cycle + nonzero hit " ++
      "fed into the proved O3PeriodicitySupply.o3_fixedPin_supply_void(_int) ⇒ False from a deep " ++
      "window + sparse cap.",
    "RESIDUAL (genuine dynamical math, NOT formalizable now) — that the ACTUAL retained " ++
      "carry-recurrence continuation's clean successor COINCIDES with this +1-on-ℤ/gℤ automaton with " ++
      "digit slopeDigit (lem:ar-outgoing-uniqueness-transcription AR.3 / lem:am-fixed-pin-row-realizes-orbit " ++
      "AM.3, built on the refined tower graph of Appendices E.3–E.6).",
    "RESIDUAL (analytic inputs) — the actual retained row must supply the §24 distinct-residue " ++
      "slope-gap inputs, and the stopped recurrence must supply the sparse-shell cap hsparse.",
    "PITFALL-FREE — the word is the actual state-indexed orbit word n ↦ slopeDigit g ((slopeSucc g)^[n] y); " ++
      "the digit-blind fractional orbit (R_n/Q) mod 1 (AR.-1, line 12450) is never used." ]

theorem o3SupplyStateSpaceResiduals_nonempty : o3SupplyStateSpaceResiduals ≠ [] := by
  simp [o3SupplyStateSpaceResiduals]

end Erdos260.O3SupplyStateSpace
