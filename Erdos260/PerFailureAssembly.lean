import Mathlib
import Erdos260.AppendixK3_CNL
import Erdos260.CarryPressureFactory
import Erdos260.LocalGeometryFactory
import Erdos260.PackageLedgerFactory

/-!
# Per-failure assembly

This module assembles the six phase-data factories and the carry/pressure
bridge into the canonical `PerFailureFactory`.

It is intentionally thin: all hard mathematical content lives in the input
factory structures.  The theorem here verifies that once those pieces are
available for a failing shell, the final per-failure certificate follows.
-/

namespace Erdos260

open Finset

noncomputable section

/--
All six Phase 4--9 data producers for a single failing shell.
-/
structure SixPhaseFactoryData (cStar ξ X : ℝ) where
  chernoff : ChernoffPathData cStar ξ X
  cnl : CNLClusterEncodingData cStar ξ X
  tower : TowerTransientFactoryData cStar ξ X
  densePack : DensePackFactoryData cStar ξ X
  returnPkg : ReturnFactoryData cStar ξ X
  run : RunFactoryData cStar ξ X

/-- Convert the six phase factories into the common phase-data bundle. -/
def SixPhaseFactoryData.toClosurePhaseData
    {cStar ξ X : ℝ}
    (data : SixPhaseFactoryData cStar ξ X) :
    ClosurePhaseData cStar ξ X where
  chernoff := data.chernoff
  cnl := data.cnl.toCNLEntropyData
  tower := data.tower.toTowerPackageData
  densePack := data.densePack.toDensePackData
  returnPkg := data.returnPkg.toReturnPackageData
  run := data.run.toRunPackageData

/--
Full per-failure assembly data.

For a fixed Nat shell `X`, this adds the carry/pressure bridge to the six
phase producers.  The bridge is stated against the exact phase data generated
from the producers, so its conclusion is definitionally the lower-bound field
required by `PerFailureFactory`.
-/
structure PerFailureAssemblyData (cPr cStar ξ : ℝ) (X : Nat) where
  phases : SixPhaseFactoryData cStar ξ (X : ℝ)
  carryBridge :
    CarryPressureBridge cPr X phases.toClosurePhaseData

/-- Assemble all phase data and the pressure bridge into `PerFailureFactory`. -/
def PerFailureAssemblyData.toFactory
    {cPr cStar ξ : ℝ} {X : Nat}
    (hcPr_nonneg : 0 <= cPr)
    (data : PerFailureAssemblyData cPr cStar ξ X) :
    PerFailureFactory cPr cStar ξ (X : ℝ) where
  phaseData := data.phases.toClosurePhaseData
  pressureLowerBound :=
    closurePressureLowerBound_of_carryBridge hcPr_nonneg data.carryBridge

/-- Direct route from per-failure assembly data to the canonical certificate. -/
def PerFailureAssemblyData.toCertificate
    {cPr cStar ξ : ℝ} {X : Nat}
    (hcPr_nonneg : 0 <= cPr)
    (data : PerFailureAssemblyData cPr cStar ξ X) :
    Erdos260PerFailureCertificate cPr cStar ξ (X : ℝ) :=
  (data.toFactory hcPr_nonneg).toCertificate

end

end Erdos260
