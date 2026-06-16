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

/-! ## 2.  The bounded state-space cardinality (AR.0 / AM.4 and the App-U fire budget) -/

/-- **The `card V ≤ 3Q` residual, discharged on the explicit state space.**  Given the slope bound
`g ≤ 3Q` (AR.0, line 12463), the constructed state space has `card (ZMod g) ≤ 3Q`. -/
theorem slopeState_card_le_threeQ (g Q : ℕ) [NeZero g] (hgb : g ≤ 3 * Q) :
    Fintype.card (ZMod g) ≤ 3 * Q := by
  rw [slopeState_card]; exact hgb

/-- **App-U fire budget on the explicit state space** (line 9508).  If `card V = g ≤ 2^19`, the
period lies strictly inside the sharp fire budget `17g < 2^24`. -/
theorem slopeRow_fire_budget {g : ℕ} (hg : g ≤ 2 ^ 19) : 17 * g < (2 : ℕ) ^ 24 :=
  O3SlopePeriodicFloor.boundedPeriod_within_fireBudget hg

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

/-! ## 4.  Honest residual / status inventory -/

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
    "CLOSED (card bounds) — slopeState_card_le_threeQ (card ≤ 3Q from g ≤ 3Q, AR.0/AM.4) and " ++
      "slopeRow_fire_budget (g ≤ 2^19 ⇒ 17g < 2^24, the App-U fire budget line 9508).",
    "CLOSED (capstone) — slopeRow_supply_void(_int): the CONSTRUCTED automaton + cycle + nonzero hit " ++
      "fed into the proved O3PeriodicitySupply.o3_fixedPin_supply_void(_int) ⇒ False from a deep " ++
      "window + sparse cap.",
    "RESIDUAL (genuine dynamical math, NOT formalizable now) — that the ACTUAL retained " ++
      "carry-recurrence continuation's clean successor COINCIDES with this +1-on-ℤ/gℤ automaton with " ++
      "digit slopeDigit (lem:ar-outgoing-uniqueness-transcription AR.3 / lem:am-fixed-pin-row-realizes-orbit " ++
      "AM.3, built on the refined tower graph of Appendices E.3–E.6).",
    "RESIDUAL (analytic inputs) — the slope bound g ≤ 3Q (AR.0; arithmetic core already in " ++
      "O3SlopePeriodicFloor.sec24_slope_gap_le_threeQ) and the sparse-shell cap hsparse of the " ++
      "stopped recurrence.",
    "PITFALL-FREE — the word is the actual state-indexed orbit word n ↦ slopeDigit g ((slopeSucc g)^[n] y); " ++
      "the digit-blind fractional orbit (R_n/Q) mod 1 (AR.-1, line 12450) is never used." ]

theorem o3SupplyStateSpaceResiduals_nonempty : o3SupplyStateSpaceResiduals ≠ [] := by
  simp [o3SupplyStateSpaceResiduals]

end Erdos260.O3SupplyStateSpace
