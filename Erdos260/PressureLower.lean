import Mathlib
import Erdos260.CarryRecurrence
import Erdos260.Constants
import Erdos260.Pressure

/-!
# Phases 2 + 3: pressure lower bound and low-excess upper bound

These two phases together discharge the lower-bound conjunct of
`AtomicWitnessProp` defined in [Erdos260.TheoremA].

## Phase 2 — `gapWindowMassLower`

We derive the manuscript inequality (`proof_v2.tex`, Lemma 21.1, line 297):
```
∑_{a_k ∈ [X, 2X]} W_k^(r) ≥ (r+1) X − O_Q(r L²)
```
from a `CarryRecurrenceData` instance (which carries the per-instance
window-sum lower bound supplied by the carry recurrence) and the
finite-Finset identity `gapWindowMass_hitGap_eq_sum_span`.

We then re-package the result into the exact form `hM` required by
`lemma21_1_pressureLowerBound` in `Pressure.lean`:
```
c_pr * X * (r + 1) + Low ≤ gapWindowMass starts (hitGap a) r
                          - (starts.card : ℝ) * T
```

## Phase 3 — `lowExcessUpper`

The low-excess layer bound from `proof_v2.tex` lines 306--309 says that
the contribution to `highExcessMass` from starts whose window excess is
less than `Y = εL` is at most `c_0 ε² X L² = o(rXL)`.  We expose this
through the `CarryRecurrenceData.lowExcessBound` field directly,
plus the form `hlow` required by `lemma21_1_pressureLowerBound`.

The two phases together hand `lemma21_1_pressureLowerBound` (already
real algebra in `Pressure.lean`) the inputs needed to conclude
`c_pr · X · (r+1) ≤ highExcessMass (highExcessStarts …)`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ### Phase 2: gap-window mass lower bound -/

/--
**Lemma 21.1 lower-bound input from `CarryRecurrenceData`.**

Given the carry-recurrence data (Phase 0 bundle), the gap-window mass
on the chosen `starts` satisfies the manuscript pressure inequality.

This is a real linear-arithmetic packaging step over
`windowSum_lower_bound` and `gapWindowMass_hitGap_eq_sum_span`.

Mathematical statement: for any `cpr` with `(r + 1) X ≥ cpr X (r + 1) + Low + (starts.card) T + gapBoundError`,
```
cpr * X * (r + 1) + Low ≤
    gapWindowMass starts (hitGap a) r − (starts.card : ℝ) * T.
```

The dispatch condition is the manuscript's numerical compatibility
`cpr ≤ 1` ∧ `(starts.card) T + Low + boundError ≤ X` (which holds for
the pinned `c_pr = 1/2`, `Low = c_0 ε² X L²`, etc., after K.4).
-/
theorem gapWindowMassLower
    {d a : Nat -> Nat} {r X L : ℕ}
    {starts : Finset Nat} {T Y : ℝ}
    (data : CarryRecurrenceData d a r X L starts T Y)
    {cpr Low : ℝ}
    (hAlloc :
      cpr * (X : ℝ) * ((r : ℝ) + 1) + Low + (starts.card : ℝ) * T +
          data.gapBoundError <=
        ((r : ℝ) + 1) * (X : ℝ)) :
    cpr * (X : ℝ) * ((r : ℝ) + 1) + Low <=
      gapWindowMass starts (hitGap a) r - (starts.card : ℝ) * T := by
  have hlower := windowSum_lower_bound data.hits (X := X) (boundError := data.gapBoundError)
    data.windowSumLower
  linarith

/-! ### Phase 3: low-excess upper bound -/

/--
**Lemma 21.1 low-excess upper-bound input from `CarryRecurrenceData`.**

The `CarryRecurrenceData.lowExcessUpper` field is exactly the manuscript
input `hlow` of `lemma21_1_pressureLowerBound`, with the explicit name
`Low := data.lowExcessBound`.  No additional algebra is needed.

This re-export is the Phase 3 deliverable.
-/
theorem lowExcessUpper
    {d a : Nat -> Nat} {r X L : ℕ}
    {starts : Finset Nat} {T Y : ℝ}
    (data : CarryRecurrenceData d a r X L starts T Y) :
    highExcessMass
      (starts \ highExcessStarts starts (hitGap a) r T Y)
      (hitGap a) r T <= data.lowExcessBound :=
  data.lowExcessUpper

/-! ### Combined Phases 2 + 3: feeding `lemma21_1_pressureLowerBound` -/

/--
**Pressure lower bound from Phase 0 carry data.**

The combination of Phases 2 and 3.  Given a `CarryRecurrenceData` and
the manuscript numerical compatibility `hAlloc`, the high-excess mass
on the high-excess starts is at least `cpr · X · (r + 1)`.

This is a direct application of `lemma21_1_pressureLowerBound` (real
algebra in `Pressure.lean`) with `hM := gapWindowMassLower …` and
`hlow := lowExcessUpper …`.
-/
theorem pressureLowerBound_from_carry
    {d a : Nat -> Nat} {r X L : ℕ}
    {starts : Finset Nat} {T Y cpr : ℝ}
    (data : CarryRecurrenceData d a r X L starts T Y)
    (hAlloc :
      cpr * (X : ℝ) * ((r : ℝ) + 1) + data.lowExcessBound +
          (starts.card : ℝ) * T + data.gapBoundError <=
        ((r : ℝ) + 1) * (X : ℝ)) :
    cpr * (X : ℝ) * ((r : ℝ) + 1) <=
      highExcessMass (highExcessStarts starts (hitGap a) r T Y)
        (hitGap a) r T :=
  lemma21_1_pressureLowerBound
    (gapWindowMassLower data hAlloc)
    (lowExcessUpper data)

end

end Erdos260
