import Mathlib
import Erdos260.CarryDataFactory
import Erdos260.PerFailureAssembly

/-!
# High-excess bridge factory

This file isolates the central Appendix I/J bridge:

`highExcessMass ... <= ClosurePhaseMass phaseData`.

Given carry data from a failing shell and this high-excess bound, the
existing arithmetic immediately constructs the `CarryPressureBridge` required
by `PerFailureAssemblyData`.
-/

namespace Erdos260

open Finset

noncomputable section

/--
The stopped-induction decomposition of high excess into the six phase masses.
-/
structure HighExcessChargeData
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr) where
  highExcess_le_phaseMass :
    highExcessMass
        (highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T <=
      ClosurePhaseMass phases.toClosurePhaseData

/-- Build the pressure bridge from carry data and the charged decomposition. -/
def HighExcessChargeData.toCarryPressureBridge
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell cPr}
    (data : HighExcessChargeData phases carryData) :
    CarryPressureBridge cPr shell.X phases.toClosurePhaseData :=
  carryData.toBridge data.highExcess_le_phaseMass

/-- Assemble a per-failure object from phases, carry data, and high-excess data. -/
def PerFailureAssemblyData.ofHighExcessCharge
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (chargeData : HighExcessChargeData phases carryData) :
    PerFailureAssemblyData cPr cStar ξ shell.X where
  phases := phases
  carryBridge := chargeData.toCarryPressureBridge

/-- Per-shell provider for the Appendix I/J high-excess bridge. -/
structure HighExcessChargeProvider where
  constants : Erdos260Constants
  data :
    ∀ (shell : FailingDyadicShell)
      (_hcQ : shell.cQ = constants.cQ)
      (phases : SixPhaseFactoryData constants.cStar constants.ξ (shell.X : ℝ))
      (carryData : CarryDataFromFailure shell constants.cPr),
        HighExcessChargeData phases carryData

def HighExcessChargeProvider.assemblyData
    (provider : HighExcessChargeProvider)
    {shell : FailingDyadicShell}
    (hcQ : shell.cQ = provider.constants.cQ)
    (phases : SixPhaseFactoryData provider.constants.cStar provider.constants.ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell provider.constants.cPr) :
    PerFailureAssemblyData provider.constants.cPr provider.constants.cStar
      provider.constants.ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (provider.data shell hcQ phases carryData)

end

end Erdos260
