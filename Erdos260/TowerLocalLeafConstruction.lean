import Mathlib
import Erdos260.GlobalTowerAssembly
import Erdos260.RefinedTowerConstruction
import Erdos260.GlobalCarryShellAssembly
import Erdos260.Constants

/-!
# L.3 tower separated local leaf construction
-/

namespace Erdos260

open Finset

noncomputable section

/-- Public constructor for the faithful L.3/I.3 tower local leaf route. -/
def towerSeparatedLocalLeafFromInput
    {cStar xi X : Real}
    (data : TowerSeparatedLocalLeafInputData cStar xi X) :
    TowerSeparatedLocalLeafInputData cStar xi X :=
  data

/-- Build the faithful L.3 tower leaf from the proof-v4 tower output package
and the final scalar smallness comparison. -/
def towerSeparatedLocalLeafFromOutputPackage
    {cStar xi X : Real}
    {entryExitSet : Finset TowerExit}
    {chargedWeight : TowerExit -> {x : Real // 0 <= x}}
    {outputBoundConstant nextLayerMass smallError : Real}
    {routedRun routedReturn routedDensePack routedCNLTail : Real}
    {absorbedRun absorbedReturn absorbedDensePack absorbedCNLTail : Real}
    (package :
      TowerOutputPackageData entryExitSet
        (fun b : TowerExit => (chargedWeight b : Real))
        routedRun routedReturn routedDensePack routedCNLTail smallError
        absorbedRun absorbedReturn absorbedDensePack absorbedCNLTail
        outputBoundConstant nextLayerMass)
    (smallness :
      TowerSmallnessInputData outputBoundConstant nextLayerMass smallError
        cStar xi X) :
    TowerSeparatedLocalLeafInputData cStar xi X where
  entryExitSet := entryExitSet
  chargedWeight := chargedWeight
  outputBoundConstant := outputBoundConstant
  nextLayerMass := nextLayerMass
  smallError := smallError
  routedRun := routedRun
  routedReturn := routedReturn
  routedDensePack := routedDensePack
  routedCNLTail := routedCNLTail
  absorbedRun := absorbedRun
  absorbedReturn := absorbedReturn
  absorbedDensePack := absorbedDensePack
  absorbedCNLTail := absorbedCNLTail
  cycle := package.cycle
  routing := package.summability.routing
  absorption := package.summability.absorption
  smallness := smallness

/-- Proof-v4 named route for L.3.1 / Proposition I.3.1.

The caller supplies the concrete tower output package, including the E.2--E.4
cycle witness and routed summability certificate, together with the final scalar
smallness comparison. -/
def towerSeparatedLocalLeafFromClosedL31I31
    {cStar xi X : Real}
    {entryExitSet : Finset TowerExit}
    {chargedWeight : TowerExit -> {x : Real // 0 <= x}}
    {outputBoundConstant nextLayerMass smallError : Real}
    {routedRun routedReturn routedDensePack routedCNLTail : Real}
    {absorbedRun absorbedReturn absorbedDensePack absorbedCNLTail : Real}
    (package :
      TowerOutputPackageData entryExitSet
        (fun b : TowerExit => (chargedWeight b : Real))
        routedRun routedReturn routedDensePack routedCNLTail smallError
        absorbedRun absorbedReturn absorbedDensePack absorbedCNLTail
        outputBoundConstant nextLayerMass)
    (smallness :
      TowerSmallnessInputData outputBoundConstant nextLayerMass smallError
        cStar xi X) :
    TowerSeparatedLocalLeafInputData cStar xi X :=
  towerSeparatedLocalLeafFromOutputPackage package smallness

namespace TowerOutputPackageData

/-- Build the proof-v4 tower output package from the separated L.3/I.3
subcertificates: the E.2-E.4 recurrent-cycle witness, the routed tower-exit
estimate, and the routed-output absorption certificate. -/
def ofCycleRoutingAbsorption
    {entryExitSet : Finset TowerExit}
    {chargedWeight : TowerExit -> Real}
    {outputBoundConstant nextLayerMass smallError : Real}
    {routedRun routedReturn routedDensePack routedCNLTail : Real}
    {absorbedRun absorbedReturn absorbedDensePack absorbedCNLTail : Real}
    (cycle : CarryFibreCycleData)
    (routing :
      TowerExitRoutingData entryExitSet chargedWeight routedRun routedReturn
        routedDensePack routedCNLTail smallError)
    (absorption :
      TowerRoutedAbsorptionData routedRun routedReturn routedDensePack
        routedCNLTail absorbedRun absorbedReturn absorbedDensePack
        absorbedCNLTail outputBoundConstant nextLayerMass) :
    TowerOutputPackageData entryExitSet chargedWeight routedRun routedReturn
      routedDensePack routedCNLTail smallError absorbedRun absorbedReturn
      absorbedDensePack absorbedCNLTail outputBoundConstant nextLayerMass where
  cycle := cycle
  summability := {
    routing := routing
    absorption := absorption }

end TowerOutputPackageData

/-- Manuscript-shaped package input for the L.3/I.3 tower separated leaf.

This record exposes exactly the proof-v4 objects that build the tower leaf:
the finite entry/exit family, its charged weights, the routed output package,
the four absorption bounds packaged inside `TowerOutputPackageData`, and the
final scalar smallness comparison. -/
structure TowerClosedL31I31PackageInputData
    (cStar xi X : Real) where
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
  package :
    TowerOutputPackageData entryExitSet
      (fun b : TowerExit => (chargedWeight b : Real))
      routedRun routedReturn routedDensePack routedCNLTail smallError
      absorbedRun absorbedReturn absorbedDensePack absorbedCNLTail
      outputBoundConstant nextLayerMass
  smallness :
    TowerSmallnessInputData outputBoundConstant nextLayerMass smallError
      cStar xi X

namespace TowerClosedL31I31PackageInputData

/-- Build the manuscript-shaped tower package from the separated L.3/I.3
subcertificates, matching the four assertions in the proof-v4 tower output
estimate. -/
def ofCycleRoutingAbsorption
    {cStar xi X : Real}
    {entryExitSet : Finset TowerExit}
    {chargedWeight : TowerExit -> {x : Real // 0 <= x}}
    {outputBoundConstant nextLayerMass smallError : Real}
    {routedRun routedReturn routedDensePack routedCNLTail : Real}
    {absorbedRun absorbedReturn absorbedDensePack absorbedCNLTail : Real}
    (cycle : CarryFibreCycleData)
    (routing :
      TowerExitRoutingData entryExitSet
        (fun b : TowerExit => (chargedWeight b : Real))
        routedRun routedReturn routedDensePack routedCNLTail smallError)
    (absorption :
      TowerRoutedAbsorptionData routedRun routedReturn routedDensePack
        routedCNLTail absorbedRun absorbedReturn absorbedDensePack
        absorbedCNLTail outputBoundConstant nextLayerMass)
    (smallness :
      TowerSmallnessInputData outputBoundConstant nextLayerMass smallError
        cStar xi X) :
    TowerClosedL31I31PackageInputData cStar xi X where
  entryExitSet := entryExitSet
  chargedWeight := chargedWeight
  outputBoundConstant := outputBoundConstant
  nextLayerMass := nextLayerMass
  smallError := smallError
  routedRun := routedRun
  routedReturn := routedReturn
  routedDensePack := routedDensePack
  routedCNLTail := routedCNLTail
  absorbedRun := absorbedRun
  absorbedReturn := absorbedReturn
  absorbedDensePack := absorbedDensePack
  absorbedCNLTail := absorbedCNLTail
  package :=
    TowerOutputPackageData.ofCycleRoutingAbsorption
      cycle routing absorption
  smallness := smallness

/-- Project the manuscript-shaped L.3/I.3 tower package to the separated local
leaf consumed by Appendix N. -/
def toTowerSeparatedLocalLeafInputData
    {cStar xi X : Real}
    (data : TowerClosedL31I31PackageInputData cStar xi X) :
    TowerSeparatedLocalLeafInputData cStar xi X :=
  towerSeparatedLocalLeafFromClosedL31I31 data.package data.smallness

end TowerClosedL31I31PackageInputData

/-- Public route from the manuscript-shaped L.3/I.3 package record. -/
def towerSeparatedLocalLeafFromClosedL31I31Package
    {cStar xi X : Real}
    (data : TowerClosedL31I31PackageInputData cStar xi X) :
    TowerSeparatedLocalLeafInputData cStar xi X :=
  data.toTowerSeparatedLocalLeafInputData

/-- Public route from separated L.3/I.3 tower subcertificates to the
manuscript-shaped tower package record. -/
def towerClosedL31I31PackageFromCycleRoutingAbsorption
    {cStar xi X : Real}
    {entryExitSet : Finset TowerExit}
    {chargedWeight : TowerExit -> {x : Real // 0 <= x}}
    {outputBoundConstant nextLayerMass smallError : Real}
    {routedRun routedReturn routedDensePack routedCNLTail : Real}
    {absorbedRun absorbedReturn absorbedDensePack absorbedCNLTail : Real}
    (cycle : CarryFibreCycleData)
    (routing :
      TowerExitRoutingData entryExitSet
        (fun b : TowerExit => (chargedWeight b : Real))
        routedRun routedReturn routedDensePack routedCNLTail smallError)
    (absorption :
      TowerRoutedAbsorptionData routedRun routedReturn routedDensePack
        routedCNLTail absorbedRun absorbedReturn absorbedDensePack
        absorbedCNLTail outputBoundConstant nextLayerMass)
    (smallness :
      TowerSmallnessInputData outputBoundConstant nextLayerMass smallError
        cStar xi X) :
    TowerClosedL31I31PackageInputData cStar xi X :=
  TowerClosedL31I31PackageInputData.ofCycleRoutingAbsorption
    cycle routing absorption smallness

/-- Project an already-grounded proof-v4 L.3/I.3 tower package into the
separated tower leaf required by the Appendix N endpoint. -/
def towerSeparatedLocalLeafFromGroundedClosedL31I31
    {cStar xi X : Real}
    (data : GroundedTowerLocalData cStar xi X) :
    TowerSeparatedLocalLeafInputData cStar xi X :=
  towerSeparatedLocalLeafFromClosedL31I31
    data.towerPackage_input
    { hSmall := data.hSmall }

/-- Remaining concrete L.3/I.3 data needed before a no-input tower local leaf
provider can be installed. -/
def towerSeparatedLocalLeafOpenItems : List String :=
  [ "construct the finite entry/exit tower event family and charged tower weights",
    "build the E.2-E.4 carry-fibre recurrent-cycle witness",
    "prove the L.3 routed-exit estimate into run, return, dense-pack, and CNL-tail destinations",
    "prove the four absorption bounds and final tower smallness budget, then use towerSeparatedLocalLeafFromOutputPackage" ]

theorem towerSeparatedLocalLeafOpenItems_nonempty :
    towerSeparatedLocalLeafOpenItems = [] -> False := by
  intro h
  simp [towerSeparatedLocalLeafOpenItems] at h

end

end Erdos260
