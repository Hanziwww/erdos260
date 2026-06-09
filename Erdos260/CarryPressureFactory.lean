import Mathlib
import Erdos260.ClosureFactory
import Erdos260.PressureLower

/-!
# Carry-to-pressure factory interface

This file isolates the exact missing bridge between the carry recurrence
side of Lemma 21.1 and the per-failure phase-mass lower bound used by the
final closure certificate.

The existing library already proves the real-arithmetic part

`CarryRecurrenceData + hAlloc -> highExcessMass lower bound`.

What is not yet in the library is the manuscript decomposition of that
high-excess mass into the six charged phase masses.  We make that remaining
field explicit as `highExcess_le_phaseMass`.
-/

namespace Erdos260

open Finset

noncomputable section

/--
Carry/pressure data tied to a fixed `ClosurePhaseData` instance.

The final field is the currently missing manuscript bridge: after the
stopped-induction decomposition, the high-excess mass controlled by
Lemma 21.1 must be charged into the six phase masses.
-/
structure CarryPressureBridge
    (cPr : ℝ) {cStar ξ : ℝ} (X : Nat)
    (phaseData : ClosurePhaseData cStar ξ (X : ℝ)) where
  d : Nat -> Nat
  a : Nat -> Nat
  r : Nat
  L : Nat
  starts : Finset Nat
  T : ℝ
  Y : ℝ
  carry : CarryRecurrenceData d a r X L starts T Y
  hAlloc :
    cPr * (X : ℝ) * ((r : ℝ) + 1) + carry.lowExcessBound +
        (starts.card : ℝ) * T + carry.gapBoundError <=
      ((r : ℝ) + 1) * (X : ℝ)
  highExcess_le_phaseMass :
    highExcessMass (highExcessStarts starts (hitGap a) r T Y)
        (hitGap a) r T <=
      ClosurePhaseMass phaseData

/--
The carry-pressure bridge yields the lower-bound conjunct required by
`PerFailureFactory`, once the high-excess mass has been charged into the
six phase masses.
-/
theorem closurePressureLowerBound_of_carryBridge
    {cPr cStar ξ : ℝ} {X : Nat}
    {phaseData : ClosurePhaseData cStar ξ (X : ℝ)}
    (hcPr_nonneg : 0 <= cPr)
    (bridge : CarryPressureBridge cPr X phaseData) :
    ClosurePressureLowerBound cPr phaseData := by
  unfold ClosurePressureLowerBound
  have hPressureHigh :
      cPr * (X : ℝ) * ((bridge.r : ℝ) + 1) <=
        highExcessMass
          (highExcessStarts bridge.starts (hitGap bridge.a) bridge.r bridge.T bridge.Y)
          (hitGap bridge.a) bridge.r bridge.T :=
    pressureLowerBound_from_carry bridge.carry bridge.hAlloc
  have hScale : cPr * (X : ℝ) <= cPr * (X : ℝ) * ((bridge.r : ℝ) + 1) := by
    have hX_nonneg : 0 <= (X : ℝ) := by exact_mod_cast Nat.zero_le X
    have hbase_nonneg : 0 <= cPr * (X : ℝ) := mul_nonneg hcPr_nonneg hX_nonneg
    have hone_le : (1 : ℝ) <= (bridge.r : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le bridge.r)
    calc
      cPr * (X : ℝ) = cPr * (X : ℝ) * 1 := by ring
      _ <= cPr * (X : ℝ) * ((bridge.r : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hone_le hbase_nonneg
  exact hScale.trans (hPressureHigh.trans bridge.highExcess_le_phaseMass)

end

end Erdos260
