import Erdos260.P9V3Closure
import Erdos260.DensePackClass3GenuineLeaf
import Erdos260.DescentDepthNoLargeRunCore

/-!
# DensePack V3 closure bridge

This module packages the existing DensePack endpoint-density and active-window
machinery into the four `P9V3RunResidual` DensePack fields:

* endpoint density gives the endpoint-disjoint count;
* the shared `WindowInteriorResidual` gives the uniform reach and containment;
* the K.1.2 active-floor lower bound gives the V3 unit-charge scale.

The sharper bridge below derives endpoint density from the upper-band descent
package, leaving only the shared window-interior residual and the K.1.2
active-floor calibration on the DensePack V3 line.
-/

namespace Erdos260

open Finset

noncomputable section

/-- The sharp DensePack residue needed to fill the V3/P9 DensePack fields for a
fixed routed budget. -/
structure DensePackV3Residue
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) where
  /-- K.1 coarea hit-density at each DensePack terminal endpoint. -/
  density : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx
  /-- Shared active-window interior containment for the budget. -/
  windowInterior : WindowInteriorResidual budget
  /-- K.1.2 active-floor calibration in floor form. -/
  floor : ∀ ctx : ActualFailureContext,
    densePackActiveFloor ctx - 1 ≤ ctx.n24CarryData.T

namespace DensePackV3Residue

variable {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}

/-- Endpoint density supplies the V3 DensePack endpoint-disjoint count for any
budget, since `densePackMarkers` is definitionally the actual shell marker set. -/
theorem densePackCount (R : DensePackV3Residue budget) :
    ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card ≤ (densePackMarkers budget ctx).card :=
  densePackCount_ofEndpointDensity budget R.density

/-- The V3 DensePack reach is the maximal shell-interior reach `K - 1`. -/
abbrev windowReach (_R : DensePackV3Residue budget) :
    ActualFailureContext → Nat :=
  densePackWindowReach

/-- The maximal DensePack reach lies inside the support shell. -/
theorem hReach (R : DensePackV3Residue budget) :
    ∀ ctx : ActualFailureContext,
      R.windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
  densePackWindowReach_add_one_le

/-- Shared window interior supplies the V3 DensePack containment field. -/
theorem hContain (R : DensePackV3Residue budget) :
    ∀ ctx : ActualFailureContext, ∀ k,
      k ∈ genuineDensePackStarts ctx →
        k + ctx.n24CarryData.r
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + R.windowReach ctx :=
  R.windowInterior.densePackContain

/-- The active-floor lower bound supplies the V3 DensePack scale field. -/
theorem hScale (R : DensePackV3Residue budget) :
    ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : Real) + 1) * (densePackDyadicG0 ctx : Real)
        - ctx.n24CarryData.T ≤ 1 :=
  densePackScaleField_of_floorLe R.floor

/-- The same residue can also feed the class-3 genuine-leaf constructor. -/
def toClass3GenuineResidue (R : DensePackV3Residue budget) :
    DensePackClass3GenuineResidue :=
  DensePackClass3GenuineResidue.ofWindowInterior budget R.density R.windowInterior R.floor

end DensePackV3Residue

/-- The remaining DensePack-local V3 residue once endpoint density is supplied
by the upper-band descent package. -/
structure DensePackV3WindowFloorResidue
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) where
  /-- Shared active-window interior containment for the budget. -/
  windowInterior : WindowInteriorResidual budget
  /-- K.1.2 active-floor calibration in floor form. -/
  floor : ∀ ctx : ActualFailureContext,
    densePackActiveFloor ctx - 1 ≤ ctx.n24CarryData.T

/-- Upper-band descent data plus the explicit dense endpoint window bounds
produce the endpoint density used by DensePack V3. -/
theorem densePackEndpointDensity_of_upperBandSource
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X) :
    ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx :=
  fun ctx => densePackEndpointDensity_of_matchedDescentWindows ctx
    (denseWindowLo ctx) (denseWindowHi ctx)
    ((upperBandSource ctx).toUpperBandMatchData.toMatchedDescentWindows)

namespace DensePackV3WindowFloorResidue

variable {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}

/-- Restore the older three-field residue by deriving endpoint density from the
upper-band descent package. -/
def toDensePackV3Residue
    (R : DensePackV3WindowFloorResidue budget)
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X) :
    DensePackV3Residue budget where
  density := densePackEndpointDensity_of_upperBandSource upperBandSource denseWindowLo denseWindowHi
  windowInterior := R.windowInterior
  floor := R.floor

/-- Endpoint-disjoint count with endpoint density discharged by the upper-band
descent package. -/
theorem densePackCount
    (R : DensePackV3WindowFloorResidue budget)
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X) :
    ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card ≤ (densePackMarkers budget ctx).card :=
  (R.toDensePackV3Residue upperBandSource denseWindowLo denseWindowHi).densePackCount

/-- The V3 DensePack reach is the maximal shell-interior reach `K - 1`. -/
abbrev windowReach (_R : DensePackV3WindowFloorResidue budget) :
    ActualFailureContext → Nat :=
  densePackWindowReach

/-- The maximal DensePack reach lies inside the support shell. -/
theorem hReach (R : DensePackV3WindowFloorResidue budget) :
    ∀ ctx : ActualFailureContext,
      R.windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
  densePackWindowReach_add_one_le

/-- Shared window interior supplies the V3 DensePack containment field. -/
theorem hContain (R : DensePackV3WindowFloorResidue budget) :
    ∀ ctx : ActualFailureContext, ∀ k,
      k ∈ genuineDensePackStarts ctx →
        k + ctx.n24CarryData.r
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + R.windowReach ctx :=
  R.windowInterior.densePackContain

/-- The active-floor lower bound supplies the V3 DensePack scale field. -/
theorem hScale (R : DensePackV3WindowFloorResidue budget) :
    ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : Real) + 1) * (densePackDyadicG0 ctx : Real)
        - ctx.n24CarryData.T ≤ 1 :=
  densePackScaleField_of_floorLe R.floor

/-- The reduced residue can feed the class-3 genuine-leaf constructor once the
upper-band descent package supplies endpoint density. -/
def toClass3GenuineResidue
    (R : DensePackV3WindowFloorResidue budget)
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X) :
    DensePackClass3GenuineResidue :=
  (R.toDensePackV3Residue upperBandSource denseWindowLo denseWindowHi).toClass3GenuineResidue

end DensePackV3WindowFloorResidue

/-- The smallest DensePack-local residue needed by the current P9/V3 surface once
endpoint density is supplied by descent: the shared active-window interior plus
the exact scale field consumed by `P9V3RunResidual`.  This avoids carrying the
stronger floor formulation when only the V3 scale field is needed downstream. -/
structure DensePackV3WindowScaleResidue
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) where
  /-- Shared active-window interior containment for the budget. -/
  windowInterior : WindowInteriorResidual budget
  /-- The exact DensePack scale field expected by the V3/P9 residual. -/
  hScale : ∀ ctx : ActualFailureContext,
    ((ctx.n24CarryData.r : Real) + 1) * (densePackDyadicG0 ctx : Real)
      - ctx.n24CarryData.T ≤ 1

namespace DensePackV3WindowScaleResidue

variable {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}

/-- The previous window/floor residue is stronger than the P9/V3-local
window/scale residue. -/
def ofWindowFloorResidue (R : DensePackV3WindowFloorResidue budget) :
    DensePackV3WindowScaleResidue budget where
  windowInterior := R.windowInterior
  hScale := R.hScale

/-- Endpoint-disjoint count with endpoint density discharged by the upper-band
descent package. -/
theorem densePackCount
    (_R : DensePackV3WindowScaleResidue budget)
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X) :
    ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card ≤ (densePackMarkers budget ctx).card :=
  densePackCount_ofEndpointDensity budget
    (densePackEndpointDensity_of_upperBandSource upperBandSource denseWindowLo denseWindowHi)

/-- The V3 DensePack reach is the maximal shell-interior reach `K - 1`. -/
abbrev windowReach (_R : DensePackV3WindowScaleResidue budget) :
    ActualFailureContext → Nat :=
  densePackWindowReach

/-- The maximal DensePack reach lies inside the support shell. -/
theorem hReach (R : DensePackV3WindowScaleResidue budget) :
    ∀ ctx : ActualFailureContext,
      R.windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
  densePackWindowReach_add_one_le

/-- Shared window interior supplies the V3 DensePack containment field. -/
theorem hContain (R : DensePackV3WindowScaleResidue budget) :
    ∀ ctx : ActualFailureContext, ∀ k,
      k ∈ genuineDensePackStarts ctx →
        k + ctx.n24CarryData.r
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + R.windowReach ctx :=
  R.windowInterior.densePackContain

end DensePackV3WindowScaleResidue

namespace P9V3RunResidual

/-- Fill the four DensePack fields of `P9V3RunResidual` from the existing
endpoint-density/window-interior/active-floor DensePack residue. -/
def ofDensePackV3
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (cnl : Class1CNLInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (densePack : DensePackV3Residue
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)) :
    P9V3RunResidual where
  towerCount := towerCount
  runResidual := runResidual
  returnCharge := returnCharge
  chernoff := chernoff
  cnl := cnl
  densePackCount := densePack.densePackCount
  windowReach := densePack.windowReach
  hReach := densePack.hReach
  hContain := densePack.hContain
  hScale := densePack.hScale

/-- Fill the DensePack fields of `P9V3RunResidual` from the reduced
window/floor residue, deriving endpoint density from the upper-band descent
package. -/
def ofDensePackV3Descent
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (cnl : Class1CNLInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (densePack : DensePackV3WindowFloorResidue
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)) :
    P9V3RunResidual where
  towerCount := towerCount
  runResidual := runResidual
  returnCharge := returnCharge
  chernoff := chernoff
  cnl := cnl
  densePackCount := densePack.densePackCount upperBandSource denseWindowLo denseWindowHi
  windowReach := densePack.windowReach
  hReach := densePack.hReach
  hContain := densePack.hContain
  hScale := densePack.hScale

/-- Fill the DensePack fields of `P9V3RunResidual` from the minimal P9/V3-local
window/scale residue, deriving endpoint density from the upper-band descent
package. -/
def ofDensePackV3ScaleDescent
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (cnl : Class1CNLInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (densePack : DensePackV3WindowScaleResidue
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)) :
    P9V3RunResidual where
  towerCount := towerCount
  runResidual := runResidual
  returnCharge := returnCharge
  chernoff := chernoff
  cnl := cnl
  densePackCount := densePack.densePackCount upperBandSource denseWindowLo denseWindowHi
  windowReach := densePack.windowReach
  hReach := densePack.hReach
  hContain := densePack.hContain
  hScale := densePack.hScale

end P9V3RunResidual

/-- P9/V3 endpoint with DensePack reduced to the sharp existing residue:
endpoint density, shared window interior, and active-floor calibration. -/
theorem erdos260_p9V3_of_densePackV3
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (cnl : Class1CNLInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (densePack : DensePackV3Residue
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)) :
    Erdos260Statement :=
  erdos260_p9V3_of_runResidual
    (P9V3RunResidual.ofDensePackV3 towerCount runResidual returnCharge
      chernoff cnl densePack)

/-- P9/V3 endpoint with DensePack density discharged by the upper-band descent
package; the DensePack-local residue is only window interior plus active-floor
calibration. -/
theorem erdos260_p9V3_of_densePackV3_descent
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (cnl : Class1CNLInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (densePack : DensePackV3WindowFloorResidue
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)) :
    Erdos260Statement :=
  erdos260_p9V3_of_runResidual
    (P9V3RunResidual.ofDensePackV3Descent towerCount runResidual returnCharge
      chernoff cnl upperBandSource denseWindowLo denseWindowHi densePack)

/-- P9/V3 endpoint with DensePack density discharged by the upper-band descent
package and the DensePack-local residue reduced to exactly the P9 fields:
window interior plus scale. -/
theorem erdos260_p9V3_of_densePackV3_scaleDescent
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (cnl : Class1CNLInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (densePack : DensePackV3WindowScaleResidue
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)) :
    Erdos260Statement :=
  erdos260_p9V3_of_runResidual
    (P9V3RunResidual.ofDensePackV3ScaleDescent towerCount runResidual returnCharge
      chernoff cnl upperBandSource denseWindowLo denseWindowHi densePack)

/-- Machine-readable status of the DensePack V3 bridge. -/
def densePackV3ClosureStatus : List String :=
  [ "CLOSED BRIDGE: DensePackV3Residue.densePackCount derives the V3 endpoint-disjoint count from densePackEndpointDensity.",
    "CLOSED BRIDGE: densePackEndpointDensity_of_upperBandSource derives densePackEndpointDensity from upperBandSource + denseWindowLo/Hi via UpperBandMatchData.toMatchedDescentWindows.",
    "SHRUNK RESIDUE: DensePackV3WindowFloorResidue removes density from the DensePack-local V3 residue; density belongs to the descent/upper-band package.",
    "CLOSED BRIDGE: DensePackV3Residue.windowReach/hReach use densePackWindowReach = |supportShell|-1 and densePackWindowReach_add_one_le.",
    "CLOSED BRIDGE: DensePackV3Residue.hContain is WindowInteriorResidual.densePackContain.",
    "CLOSED BRIDGE: DensePackV3Residue.hScale is densePackScaleField_of_floorLe.",
    "SHRUNK P9/V3 RESIDUE: DensePackV3WindowScaleResidue keeps only windowInterior + hScale after descent supplies density.",
    "P9 BRIDGE: P9V3RunResidual.ofDensePackV3 fills exactly the four DensePack fields of P9V3RunResidual.",
    "P9 BRIDGE: P9V3RunResidual.ofDensePackV3Descent fills the DensePack fields from upperBandSource+denseWindowLo/Hi plus DensePackV3WindowFloorResidue.",
    "P9 BRIDGE: P9V3RunResidual.ofDensePackV3ScaleDescent fills the DensePack fields from upperBandSource+denseWindowLo/Hi plus DensePackV3WindowScaleResidue.",
    "REMAINING DENSEPACK-LOCAL P9/V3 RESIDUALS: windowInterior : WindowInteriorResidual budget; hScale : ∀ ctx, ((r+1)·densePackDyadicG0 ctx) - T ≤ 1. DESCENT RESIDUALS FOR DENSITY: upperBandSource, denseWindowLo, denseWindowHi." ]

theorem densePackV3ClosureStatus_nonempty : densePackV3ClosureStatus ≠ [] := by
  simp [densePackV3ClosureStatus]

#print axioms DensePackV3Residue.densePackCount
#print axioms DensePackV3Residue.hReach
#print axioms DensePackV3Residue.hContain
#print axioms DensePackV3Residue.hScale
#print axioms DensePackV3Residue.toClass3GenuineResidue
#print axioms DensePackV3WindowFloorResidue.densePackCount
#print axioms DensePackV3WindowFloorResidue.hReach
#print axioms DensePackV3WindowFloorResidue.hContain
#print axioms DensePackV3WindowFloorResidue.hScale
#print axioms DensePackV3WindowFloorResidue.toClass3GenuineResidue
#print axioms DensePackV3WindowScaleResidue.ofWindowFloorResidue
#print axioms DensePackV3WindowScaleResidue.densePackCount
#print axioms DensePackV3WindowScaleResidue.hReach
#print axioms DensePackV3WindowScaleResidue.hContain
#print axioms P9V3RunResidual.ofDensePackV3
#print axioms P9V3RunResidual.ofDensePackV3Descent
#print axioms P9V3RunResidual.ofDensePackV3ScaleDescent
#print axioms erdos260_p9V3_of_densePackV3
#print axioms erdos260_p9V3_of_densePackV3_descent
#print axioms erdos260_p9V3_of_densePackV3_scaleDescent

end

end Erdos260
