import Mathlib
import Erdos260.GlobalRunAssembly
import Erdos260.RefinedTowerConstruction

/-!
# Global tower assembly

This module grounds the Tower phase one layer further.  Instead of carrying the
L.3 charged-summability bound as a single raw field, the local data carries the
proof-v4 transient-summability certificate: tower exits are routed into the
next-layer Run/Return/DensePack/CNL-tail classes, then absorbed into the tower
budget.
-/

namespace Erdos260

open Finset

noncomputable section

/-- L.3 routed tower-exit mass certificate. -/
structure TowerExitRoutingData
    (entryExitSet : Finset TowerExit) (chargedWeight : TowerExit -> Real)
    (routedRun routedReturn routedDensePack routedCNLTail smallError : Real) where
  routed :
    (∑ b ∈ entryExitSet, chargedWeight b) <=
      routedRun + routedReturn + routedDensePack + routedCNLTail + smallError

namespace TowerExitRoutingData

/-- Project the L.3 routed tower-exit mass estimate. -/
theorem routed_bound
    {entryExitSet : Finset TowerExit} {chargedWeight : TowerExit -> Real}
    {routedRun routedReturn routedDensePack routedCNLTail smallError : Real}
    (data :
      TowerExitRoutingData entryExitSet chargedWeight routedRun routedReturn
        routedDensePack routedCNLTail smallError) :
    (∑ b ∈ entryExitSet, chargedWeight b) <=
      routedRun + routedReturn + routedDensePack + routedCNLTail + smallError :=
  data.routed

end TowerExitRoutingData

/-- L.3 absorption certificate for routed tower exits that become Run outputs. -/
structure TowerRunAbsorptionData (routedRun absorbedRun : Real) where
  absorbRun :
    routedRun <= absorbedRun

/-- L.3 absorption certificate for routed tower exits that become Return outputs. -/
structure TowerReturnAbsorptionData (routedReturn absorbedReturn : Real) where
  absorbReturn :
    routedReturn <= absorbedReturn

/-- L.3 absorption certificate for routed tower exits that become DensePack outputs. -/
structure TowerDensePackAbsorptionData
    (routedDensePack absorbedDensePack : Real) where
  absorbDensePack :
    routedDensePack <= absorbedDensePack

/-- L.3 absorption certificate for routed tower exits that become clean CNL-tail outputs. -/
structure TowerCNLTailAbsorptionData (routedCNLTail absorbedCNLTail : Real) where
  absorbCNLTail :
    routedCNLTail <= absorbedCNLTail

/-- L.3 total budget certificate for the absorbed routed tower outputs. -/
structure TowerAbsorbedBudgetData
    (absorbedRun absorbedReturn absorbedDensePack absorbedCNLTail : Real)
    (outputBoundConstant nextLayerMass : Real) where
  absorbedTotal :
    absorbedRun + absorbedReturn + absorbedDensePack + absorbedCNLTail <=
      outputBoundConstant * nextLayerMass

/-- L.3 absorption certificate for the routed tower outputs. -/
structure TowerRoutedAbsorptionData
    (routedRun routedReturn routedDensePack routedCNLTail : Real)
    (absorbedRun absorbedReturn absorbedDensePack absorbedCNLTail : Real)
    (outputBoundConstant nextLayerMass : Real) where
  run :
    TowerRunAbsorptionData routedRun absorbedRun
  returnPkg :
    TowerReturnAbsorptionData routedReturn absorbedReturn
  densePack :
    TowerDensePackAbsorptionData routedDensePack absorbedDensePack
  cnlTail :
    TowerCNLTailAbsorptionData routedCNLTail absorbedCNLTail
  budget :
    TowerAbsorbedBudgetData absorbedRun absorbedReturn absorbedDensePack
      absorbedCNLTail outputBoundConstant nextLayerMass

namespace TowerRoutedAbsorptionData

/-- L.3 absorption of routed tower exits into the next-layer budget. -/
theorem absorb_bound
    {routedRun routedReturn routedDensePack routedCNLTail : Real}
    {absorbedRun absorbedReturn absorbedDensePack absorbedCNLTail : Real}
    {outputBoundConstant nextLayerMass : Real}
    (data :
      TowerRoutedAbsorptionData routedRun routedReturn routedDensePack
        routedCNLTail absorbedRun absorbedReturn absorbedDensePack
        absorbedCNLTail outputBoundConstant nextLayerMass) :
    routedRun + routedReturn + routedDensePack + routedCNLTail <=
      outputBoundConstant * nextLayerMass := by
  linarith [data.run.absorbRun, data.returnPkg.absorbReturn,
    data.densePack.absorbDensePack, data.cnlTail.absorbCNLTail,
    data.budget.absorbedTotal]

end TowerRoutedAbsorptionData

/-- L.3 tower transient summability certificate: routed exits plus absorption. -/
structure TowerTransientSummabilityData
    (entryExitSet : Finset TowerExit) (chargedWeight : TowerExit -> Real)
    (routedRun routedReturn routedDensePack routedCNLTail smallError : Real)
    (absorbedRun absorbedReturn absorbedDensePack absorbedCNLTail : Real)
    (outputBoundConstant nextLayerMass : Real) where
  routing :
    TowerExitRoutingData entryExitSet chargedWeight routedRun routedReturn
      routedDensePack routedCNLTail smallError
  absorption :
    TowerRoutedAbsorptionData routedRun routedReturn routedDensePack
      routedCNLTail absorbedRun absorbedReturn absorbedDensePack
      absorbedCNLTail outputBoundConstant nextLayerMass

namespace TowerTransientSummabilityData

/-- The absorbed routed exits are bounded by the next-layer tower budget. -/
theorem absorb_bound
    {entryExitSet : Finset TowerExit} {chargedWeight : TowerExit -> Real}
    {routedRun routedReturn routedDensePack routedCNLTail smallError : Real}
    {absorbedRun absorbedReturn absorbedDensePack absorbedCNLTail : Real}
    {outputBoundConstant nextLayerMass : Real}
    (data :
      TowerTransientSummabilityData entryExitSet chargedWeight routedRun
        routedReturn routedDensePack routedCNLTail smallError absorbedRun
        absorbedReturn absorbedDensePack absorbedCNLTail outputBoundConstant
        nextLayerMass) :
    routedRun + routedReturn + routedDensePack + routedCNLTail <=
      outputBoundConstant * nextLayerMass :=
  data.absorption.absorb_bound

/-- L.3 tower transient routed summability bound from the proof-v4 exit split. -/
theorem summable_bound
    {entryExitSet : Finset TowerExit} {chargedWeight : TowerExit -> Real}
    {routedRun routedReturn routedDensePack routedCNLTail smallError : Real}
    {absorbedRun absorbedReturn absorbedDensePack absorbedCNLTail : Real}
    {outputBoundConstant nextLayerMass : Real}
    (data :
      TowerTransientSummabilityData entryExitSet chargedWeight routedRun
        routedReturn routedDensePack routedCNLTail smallError absorbedRun
        absorbedReturn absorbedDensePack absorbedCNLTail outputBoundConstant
        nextLayerMass) :
    (∑ b ∈ entryExitSet, chargedWeight b) <=
      outputBoundConstant * nextLayerMass + smallError := by
  linarith [data.routing.routed, data.absorb_bound]

end TowerTransientSummabilityData

/-- Proof-v4 Tower output package: the E.2-E.4 carry-fibre recurrent-cycle
witness together with the L.3 transient routed-summability certificate. -/
structure TowerOutputPackageData
    (entryExitSet : Finset TowerExit) (chargedWeight : TowerExit -> Real)
    (routedRun routedReturn routedDensePack routedCNLTail smallError : Real)
    (absorbedRun absorbedReturn absorbedDensePack absorbedCNLTail : Real)
    (outputBoundConstant nextLayerMass : Real) where
  cycle : CarryFibreCycleData
  summability :
    TowerTransientSummabilityData entryExitSet chargedWeight routedRun
      routedReturn routedDensePack routedCNLTail smallError absorbedRun
      absorbedReturn absorbedDensePack absorbedCNLTail outputBoundConstant
      nextLayerMass

/--
Proof-v4 aligned Tower local data.

The raw `TowerTransientFactoryData.hSummable` field is derived from the Tower
output package:

* the E.2-E.4 carry-fibre recurrent-cycle witness used by the refined tower
  construction;
* the L.3 tower-exit routed mass bound into Run, Return, DensePack, CNL-tail,
  plus lower-order error;
* separate absorption of those routed outputs into the next-layer tower budget.
-/
structure GroundedTowerLocalData (cStar xi X : Real) where
  entryExitSet : Finset TowerExit
  chargedWeight : TowerExit -> {x : Real // 0 <= x}
  outputBoundConstant : Real
  nextLayerMass : Real
  smallError : Real
  routedRun : Real
  routedReturn : Real
  routedDensePack : Real
  routedCNLTail : Real
  absorbedRun : Real
  absorbedReturn : Real
  absorbedDensePack : Real
  absorbedCNLTail : Real
  towerPackage_input :
    TowerOutputPackageData entryExitSet
      (fun b : TowerExit => (chargedWeight b : Real))
      routedRun routedReturn routedDensePack routedCNLTail smallError
      absorbedRun absorbedReturn absorbedDensePack absorbedCNLTail
      outputBoundConstant nextLayerMass
  hSmall :
    outputBoundConstant * nextLayerMass + smallError <= cStar * xi * X / 6

/--
L.3/E.2-E.4 tower leaf before it is packed as grounded Tower local data:
the recurrent-cycle witness, routed exit estimate, and routed-output absorption
are kept separate.
-/
structure TowerLocalLeafInputData (cStar xi X : Real) where
  entryExitSet : Finset TowerExit
  chargedWeight : TowerExit -> {x : Real // 0 <= x}
  outputBoundConstant : Real
  nextLayerMass : Real
  smallError : Real
  routedRun : Real
  routedReturn : Real
  routedDensePack : Real
  routedCNLTail : Real
  absorbedRun : Real
  absorbedReturn : Real
  absorbedDensePack : Real
  absorbedCNLTail : Real
  cycle : CarryFibreCycleData
  routing :
    TowerExitRoutingData entryExitSet (fun b : TowerExit => (chargedWeight b : Real))
      routedRun routedReturn routedDensePack routedCNLTail smallError
  absorption :
    TowerRoutedAbsorptionData routedRun routedReturn routedDensePack
      routedCNLTail absorbedRun absorbedReturn absorbedDensePack
      absorbedCNLTail outputBoundConstant nextLayerMass
  hSmall :
    outputBoundConstant * nextLayerMass + smallError <= cStar * xi * X / 6

/-- L.3 final scalar smallness comparison for the tower transient package. -/
structure TowerSmallnessInputData
    (outputBoundConstant nextLayerMass smallError cStar xi X : Real) where
  hSmall :
    outputBoundConstant * nextLayerMass + smallError <= cStar * xi * X / 6

/--
L.3/E.2-E.4 tower leaf with the recurrent-cycle, routing, routed-output
absorption, and final scalar smallness certificates kept as separate proof-v4
inputs.
-/
structure TowerSeparatedLocalLeafInputData (cStar xi X : Real) where
  entryExitSet : Finset TowerExit
  chargedWeight : TowerExit -> {x : Real // 0 <= x}
  outputBoundConstant : Real
  nextLayerMass : Real
  smallError : Real
  routedRun : Real
  routedReturn : Real
  routedDensePack : Real
  routedCNLTail : Real
  absorbedRun : Real
  absorbedReturn : Real
  absorbedDensePack : Real
  absorbedCNLTail : Real
  cycle : CarryFibreCycleData
  routing :
    TowerExitRoutingData entryExitSet (fun b : TowerExit => (chargedWeight b : Real))
      routedRun routedReturn routedDensePack routedCNLTail smallError
  absorption :
    TowerRoutedAbsorptionData routedRun routedReturn routedDensePack
      routedCNLTail absorbedRun absorbedReturn absorbedDensePack
      absorbedCNLTail outputBoundConstant nextLayerMass
  smallness :
    TowerSmallnessInputData outputBoundConstant nextLayerMass smallError
      cStar xi X

namespace TowerLocalLeafInputData

/-- Pack the separated L.3/E.2-E.4 tower leaf as grounded Tower local data. -/
def toGroundedTowerLocalData
    {cStar xi X : Real}
    (data : TowerLocalLeafInputData cStar xi X) :
    GroundedTowerLocalData cStar xi X where
  entryExitSet := data.entryExitSet
  chargedWeight := data.chargedWeight
  outputBoundConstant := data.outputBoundConstant
  nextLayerMass := data.nextLayerMass
  smallError := data.smallError
  routedRun := data.routedRun
  routedReturn := data.routedReturn
  routedDensePack := data.routedDensePack
  routedCNLTail := data.routedCNLTail
  absorbedRun := data.absorbedRun
  absorbedReturn := data.absorbedReturn
  absorbedDensePack := data.absorbedDensePack
  absorbedCNLTail := data.absorbedCNLTail
  towerPackage_input := {
    cycle := data.cycle
    summability := {
      routing := data.routing
      absorption := data.absorption } }
  hSmall := data.hSmall

end TowerLocalLeafInputData

namespace TowerSeparatedLocalLeafInputData

/-- Bundle the separated L.3 tower subcertificates into the existing local
Tower leaf. -/
def toTowerLocalLeafInputData
    {cStar xi X : Real}
    (data : TowerSeparatedLocalLeafInputData cStar xi X) :
    TowerLocalLeafInputData cStar xi X where
  entryExitSet := data.entryExitSet
  chargedWeight := data.chargedWeight
  outputBoundConstant := data.outputBoundConstant
  nextLayerMass := data.nextLayerMass
  smallError := data.smallError
  routedRun := data.routedRun
  routedReturn := data.routedReturn
  routedDensePack := data.routedDensePack
  routedCNLTail := data.routedCNLTail
  absorbedRun := data.absorbedRun
  absorbedReturn := data.absorbedReturn
  absorbedDensePack := data.absorbedDensePack
  absorbedCNLTail := data.absorbedCNLTail
  cycle := data.cycle
  routing := data.routing
  absorption := data.absorption
  hSmall := data.smallness.hSmall

/-- Convert the separated L.3 tower leaf to grounded Tower local data. -/
def toGroundedTowerLocalData
    {cStar xi X : Real}
    (data : TowerSeparatedLocalLeafInputData cStar xi X) :
    GroundedTowerLocalData cStar xi X :=
  data.toTowerLocalLeafInputData.toGroundedTowerLocalData

end TowerSeparatedLocalLeafInputData

/-- Recover the separated L.3/E.2-E.4 tower leaf carried by grounded Tower data. -/
def GroundedTowerLocalData.toLocalLeafInputData
    {cStar xi X : Real}
    (data : GroundedTowerLocalData cStar xi X) :
    TowerLocalLeafInputData cStar xi X where
  entryExitSet := data.entryExitSet
  chargedWeight := data.chargedWeight
  outputBoundConstant := data.outputBoundConstant
  nextLayerMass := data.nextLayerMass
  smallError := data.smallError
  routedRun := data.routedRun
  routedReturn := data.routedReturn
  routedDensePack := data.routedDensePack
  routedCNLTail := data.routedCNLTail
  absorbedRun := data.absorbedRun
  absorbedReturn := data.absorbedReturn
  absorbedDensePack := data.absorbedDensePack
  absorbedCNLTail := data.absorbedCNLTail
  cycle := data.towerPackage_input.cycle
  routing := data.towerPackage_input.summability.routing
  absorption := data.towerPackage_input.summability.absorption
  hSmall := data.hSmall

/-- The real-valued tower-exit weights underlying the nonnegative mass data. -/
def GroundedTowerLocalData.chargedWeightReal
    {cStar xi X : Real} (data : GroundedTowerLocalData cStar xi X) :
    TowerExit -> Real :=
  fun b => data.chargedWeight b

/-- Tower-exit weights are nonnegative by type. -/
theorem GroundedTowerLocalData.chargedWeight_nonneg
    {cStar xi X : Real} (data : GroundedTowerLocalData cStar xi X) :
    forall b, b ∈ data.entryExitSet -> 0 <= data.chargedWeightReal b := by
  intro b _hb
  exact (data.chargedWeight b).property

/-- E.2-E.4 carry-fibre cycle witness carried by the grounded Tower package. -/
def GroundedTowerLocalData.cycle
    {cStar xi X : Real} (data : GroundedTowerLocalData cStar xi X) :
    CarryFibreCycleData :=
  data.towerPackage_input.cycle

/-- The carried cycle witness assembles a coherent recurrent SCC. -/
theorem GroundedTowerLocalData.cycleData
    {cStar xi X : Real} (data : GroundedTowerLocalData cStar xi X) :
    ∃ S : RefinedRecurrentSCC, RefinedTowerCycleData S :=
  data.cycle.cycleData

/-- L.3 tower-exit routing certificate in the proof-v4 output split shape. -/
def GroundedTowerLocalData.routing
    {cStar xi X : Real} (data : GroundedTowerLocalData cStar xi X) :
    TowerExitRoutingData data.entryExitSet data.chargedWeightReal
      data.routedRun data.routedReturn data.routedDensePack data.routedCNLTail
      data.smallError := by
  simpa [GroundedTowerLocalData.chargedWeightReal] using
    data.towerPackage_input.summability.routing

/-- L.3 routed-output absorption certificate in the proof-v4 next-layer shape. -/
def GroundedTowerLocalData.absorption
    {cStar xi X : Real} (data : GroundedTowerLocalData cStar xi X) :
    TowerRoutedAbsorptionData data.routedRun data.routedReturn
      data.routedDensePack data.routedCNLTail data.absorbedRun
      data.absorbedReturn data.absorbedDensePack data.absorbedCNLTail
      data.outputBoundConstant data.nextLayerMass := by
  simpa [GroundedTowerLocalData.chargedWeightReal] using
    data.towerPackage_input.summability.absorption

/-- L.3 tower transient summability certificate, assembled from the routed
exit and absorption inputs. -/
def GroundedTowerLocalData.summability
    {cStar xi X : Real} (data : GroundedTowerLocalData cStar xi X) :
    TowerTransientSummabilityData data.entryExitSet data.chargedWeightReal
      data.routedRun data.routedReturn data.routedDensePack data.routedCNLTail
      data.smallError data.absorbedRun data.absorbedReturn data.absorbedDensePack
      data.absorbedCNLTail data.outputBoundConstant data.nextLayerMass := by
  simpa [GroundedTowerLocalData.chargedWeightReal] using
    data.towerPackage_input.summability

/-- L.3 routed tower-exit mass estimate for the grounded tower package. -/
theorem GroundedTowerLocalData.routing_bound
    {cStar xi X : Real} (data : GroundedTowerLocalData cStar xi X) :
    (∑ b ∈ data.entryExitSet, data.chargedWeightReal b) <=
      data.routedRun + data.routedReturn + data.routedDensePack +
        data.routedCNLTail + data.smallError := by
  exact data.routing.routed_bound

/-- L.3 absorption of routed tower exits into the next-layer budget. -/
theorem GroundedTowerLocalData.absorb_bound
    {cStar xi X : Real} (data : GroundedTowerLocalData cStar xi X) :
    data.routedRun + data.routedReturn + data.routedDensePack +
        data.routedCNLTail <=
      data.outputBoundConstant * data.nextLayerMass := by
  exact data.summability.absorb_bound

/-- L.3 tower transient routed summability bound from the proof-v4 exit split. -/
theorem GroundedTowerLocalData.summable_bound
    {cStar xi X : Real} (data : GroundedTowerLocalData cStar xi X) :
    (∑ b ∈ data.entryExitSet, data.chargedWeightReal b) <=
      data.outputBoundConstant * data.nextLayerMass + data.smallError := by
  exact data.summability.summable_bound

/-- Final smallness of the grounded tower transient package. -/
theorem GroundedTowerLocalData.tower_bound
    {cStar xi X : Real} (data : GroundedTowerLocalData cStar xi X) :
    (∑ b ∈ data.entryExitSet, data.chargedWeightReal b) <=
      cStar * xi * X / 6 :=
  data.summable_bound.trans data.hSmall

namespace TowerLocalLeafInputData

/-- Final L.3 tower transient bound projected directly from the tower leaf. -/
theorem tower_bound
    {cStar xi X : Real} (data : TowerLocalLeafInputData cStar xi X) :
    (∑ b ∈ data.entryExitSet, (data.chargedWeight b : Real)) <=
      cStar * xi * X / 6 :=
  data.toGroundedTowerLocalData.tower_bound

end TowerLocalLeafInputData

namespace TowerSeparatedLocalLeafInputData

/-- Final L.3 tower transient bound projected directly from the separated
tower leaf. -/
theorem tower_bound
    {cStar xi X : Real} (data : TowerSeparatedLocalLeafInputData cStar xi X) :
    (∑ b ∈ data.entryExitSet, (data.chargedWeight b : Real)) <=
      cStar * xi * X / 6 :=
  data.toGroundedTowerLocalData.tower_bound

end TowerSeparatedLocalLeafInputData

/-- Convert L.3-routed tower data into the existing transient tower package. -/
def GroundedTowerLocalData.toTowerTransientFactoryData
    {cStar xi X : Real}
    (data : GroundedTowerLocalData cStar xi X) :
    TowerTransientFactoryData cStar xi X where
  entryExitSet := data.entryExitSet
  chargedWeight := data.chargedWeightReal
  chargedWeight_nonneg := data.chargedWeight_nonneg
  outputBoundConstant := data.outputBoundConstant
  nextLayerMass := data.nextLayerMass
  smallError := data.smallError
  hSummable := data.summable_bound
  hSmall := data.hSmall

/--
Core global assembly where all seven phase/carry/high-excess slots currently
have proof-v4 grounded interfaces.
-/
structure GlobalAssemblyCoreGroundedAllCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCarryLocalData shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (hcQ : shell.cQ = erdos260Constants.cQ)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        GroundedHighExcessLocalData phases ((carry shell hcQ).toCarryData)

/-- Convert the fully grounded-current interface to per-failure assembly. -/
def GlobalAssemblyCoreGroundedAllCurrentInputs.toGlobalPerFailureAssembly
    (data : GlobalAssemblyCoreGroundedAllCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro Q d hQ hd hnonterm hrational
    exact (canonicalThresholds Q d hQ hd hnonterm hrational).startThreshold
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic _hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    have hcQ : shell.cQ = erdos260Constants.cQ := rfl
    let phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (X : Real) := {
      chernoff := (data.chernoff shell hcQ).toChernoffPathData
      cnl := (data.cnl shell hcQ).toCNLClusterEncodingData
      tower := (data.tower shell hcQ).toTowerTransientFactoryData
      densePack := (data.densePack shell hcQ).toDensePackFactoryData
      returnPkg := (data.returnPkg shell hcQ).toReturnFactoryData
      run := (data.run shell hcQ).toRunFactoryData }
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases
        ((data.carry shell hcQ).toCarryData)
        ((data.highExcess shell hcQ phases).toHighExcessChargeData)

/--
Erdos 260 from the current fully-grounded global interface: carry, Chernoff,
CNL, DensePack, Tower, Return, Run, and high-excess all enter through their
proof-v4-aligned constructor layers.
-/
theorem erdos260_final_core_grounded_current
    (data : GlobalAssemblyCoreGroundedAllCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

end

end Erdos260
