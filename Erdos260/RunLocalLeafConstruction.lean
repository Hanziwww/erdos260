import Mathlib
import Erdos260.GlobalRunAssembly
import Erdos260.GlobalCarryShellAssembly
import Erdos260.Constants

/-!
# L.4.1/L.4.2 run separated local leaf construction
-/

namespace Erdos260

open Finset

noncomputable section

/-- Public constructor for the faithful L.4.1/L.4.2/I.5.2 run route. -/
def runSeparatedLocalLeafFromInput
    {cStar xi X : Real}
    (data : RunSeparatedLocalLeafInputData cStar xi X) :
    RunSeparatedLocalLeafInputData cStar xi X :=
  data

/-- Build the faithful Run leaf from the proof-v4 L.4.1/L.4.2 output package
and the final scalar smallness comparison. -/
def runSeparatedLocalLeafFromOutputPackage
    {cStar xi X : Real}
    {runMass nextTower nextReturn nextDensePack twoNegcY Ij smallError : Real}
    {meanLow localSpike boundary : Real}
    {chainWeight : Nat -> {x : Real // 0 <= x}}
    {chainLength : Nat}
    (package :
      RunOutputPackageData runMass nextTower nextReturn nextDensePack
        twoNegcY X Ij smallError meanLow localSpike boundary
        (fun n : Nat => (chainWeight n : Real)) chainLength)
    (smallness :
      RunSmallnessInputData cStar xi X nextTower nextReturn nextDensePack
        twoNegcY Ij smallError) :
    RunSeparatedLocalLeafInputData cStar xi X where
  runMass := runMass
  nextTower := nextTower
  nextReturn := nextReturn
  nextDensePack := nextDensePack
  twoNegcY := twoNegcY
  Ij := Ij
  smallError := smallError
  meanLow := meanLow
  localSpike := localSpike
  boundary := boundary
  chainWeight := chainWeight
  chainLength := chainLength
  trichotomy := package.trichotomy
  periodHalf := package.periodHalf
  smallness := smallness

/-- Proof-v4 named route for L.4.1--L.4.2 / Proposition I.5.2.

The caller supplies the run trichotomy, period-halving package, and final scalar
smallness comparison, matching the manuscript route for the separated run leaf. -/
def runSeparatedLocalLeafFromClosedL41L42I52
    {cStar xi X : Real}
    {runMass nextTower nextReturn nextDensePack twoNegcY Ij smallError : Real}
    {meanLow localSpike boundary : Real}
    {chainWeight : Nat -> {x : Real // 0 <= x}}
    {chainLength : Nat}
    (package :
      RunOutputPackageData runMass nextTower nextReturn nextDensePack
        twoNegcY X Ij smallError meanLow localSpike boundary
        (fun n : Nat => (chainWeight n : Real)) chainLength)
    (smallness :
      RunSmallnessInputData cStar xi X nextTower nextReturn nextDensePack
        twoNegcY Ij smallError) :
    RunSeparatedLocalLeafInputData cStar xi X :=
  runSeparatedLocalLeafFromOutputPackage package smallness

namespace RunOutputPackageData

/-- Build the proof-v4 run output package from the separated L.4.1/L.4.2
subcertificates: deterministic trichotomy/absorption and direct period
half-decrease along the shortening chain. -/
def ofTrichotomyHalfDecrease
    {runMass nextTower nextReturn nextDensePack twoNegcY X Ij smallError : Real}
    {meanLow localSpike boundary : Real}
    {chainWeight : Nat -> Real}
    {chainLength : Nat}
    (trichotomy :
      RunTrichotomyAbsorptionData runMass nextTower nextReturn nextDensePack
        twoNegcY X Ij smallError meanLow localSpike boundary chainWeight
        chainLength)
    (chain_half :
      forall n : Nat, chainWeight (n + 1) <= chainWeight n / 2) :
    RunOutputPackageData runMass nextTower nextReturn nextDensePack twoNegcY X
      Ij smallError meanLow localSpike boundary chainWeight chainLength where
  trichotomy := trichotomy
  periodHalf := { chain_half := chain_half }

end RunOutputPackageData

/-- Manuscript-shaped package input for the L.4.1-L.4.2/I.5.2 run leaf.

The record exposes the run output quantities, chain weights, trichotomy and
period-halving package, and the scalar smallness comparison that turns them
into the separated Appendix N run leaf. -/
structure RunClosedL41L42I52PackageInputData
    (cStar xi X : Real) where
  runMass : Real
  nextTower : Real
  nextReturn : Real
  nextDensePack : Real
  twoNegcY : Real
  Ij : Real
  smallError : Real
  meanLow : Real
  localSpike : Real
  boundary : Real
  chainWeight : Nat -> {x : Real // 0 <= x}
  chainLength : Nat
  package :
    RunOutputPackageData runMass nextTower nextReturn nextDensePack
      twoNegcY X Ij smallError meanLow localSpike boundary
      (fun n : Nat => (chainWeight n : Real)) chainLength
  smallness :
    RunSmallnessInputData cStar xi X nextTower nextReturn nextDensePack
      twoNegcY Ij smallError

namespace RunClosedL41L42I52PackageInputData

/-- Build the manuscript-shaped run package from the separated L.4.1/L.4.2
subcertificates: the deterministic trichotomy/absorption package, direct
period half-decrease, and final scalar smallness comparison. -/
def ofTrichotomyHalfDecrease
    {cStar xi X : Real}
    {runMass nextTower nextReturn nextDensePack twoNegcY Ij smallError : Real}
    {meanLow localSpike boundary : Real}
    {chainWeight : Nat -> {x : Real // 0 <= x}}
    {chainLength : Nat}
    (trichotomy :
      RunTrichotomyAbsorptionData runMass nextTower nextReturn nextDensePack
        twoNegcY X Ij smallError meanLow localSpike boundary
        (fun n : Nat => (chainWeight n : Real)) chainLength)
    (chain_half :
      forall n : Nat,
        (chainWeight (n + 1) : Real) <= (chainWeight n : Real) / 2)
    (smallness :
      RunSmallnessInputData cStar xi X nextTower nextReturn nextDensePack
        twoNegcY Ij smallError) :
    RunClosedL41L42I52PackageInputData cStar xi X where
  runMass := runMass
  nextTower := nextTower
  nextReturn := nextReturn
  nextDensePack := nextDensePack
  twoNegcY := twoNegcY
  Ij := Ij
  smallError := smallError
  meanLow := meanLow
  localSpike := localSpike
  boundary := boundary
  chainWeight := chainWeight
  chainLength := chainLength
  package :=
    RunOutputPackageData.ofTrichotomyHalfDecrease
      trichotomy chain_half
  smallness := smallness

/-- Project the manuscript-shaped run package to the separated local leaf
consumed by Appendix N. -/
def toRunSeparatedLocalLeafInputData
    {cStar xi X : Real}
    (data : RunClosedL41L42I52PackageInputData cStar xi X) :
    RunSeparatedLocalLeafInputData cStar xi X :=
  runSeparatedLocalLeafFromClosedL41L42I52 data.package data.smallness

end RunClosedL41L42I52PackageInputData

/-- Public route from the manuscript-shaped L.4.1-L.4.2/I.5.2 package record. -/
def runSeparatedLocalLeafFromClosedL41L42I52Package
    {cStar xi X : Real}
    (data : RunClosedL41L42I52PackageInputData cStar xi X) :
    RunSeparatedLocalLeafInputData cStar xi X :=
  data.toRunSeparatedLocalLeafInputData

/-- Public route from separated L.4.1/L.4.2/I.5.2 subcertificates to the
manuscript-shaped run package record. -/
def runClosedL41L42I52PackageFromTrichotomyHalfDecrease
    {cStar xi X : Real}
    {runMass nextTower nextReturn nextDensePack twoNegcY Ij smallError : Real}
    {meanLow localSpike boundary : Real}
    {chainWeight : Nat -> {x : Real // 0 <= x}}
    {chainLength : Nat}
    (trichotomy :
      RunTrichotomyAbsorptionData runMass nextTower nextReturn nextDensePack
        twoNegcY X Ij smallError meanLow localSpike boundary
        (fun n : Nat => (chainWeight n : Real)) chainLength)
    (chain_half :
      forall n : Nat,
        (chainWeight (n + 1) : Real) <= (chainWeight n : Real) / 2)
    (smallness :
      RunSmallnessInputData cStar xi X nextTower nextReturn nextDensePack
        twoNegcY Ij smallError) :
    RunClosedL41L42I52PackageInputData cStar xi X :=
  RunClosedL41L42I52PackageInputData.ofTrichotomyHalfDecrease
    trichotomy chain_half smallness

/-- Project an already-grounded proof-v4 L.4.1--L.4.2/I.5.2 run package into
the separated run leaf required by the Appendix N endpoint. -/
def runSeparatedLocalLeafFromGroundedClosedL41L42I52
    {cStar xi X : Real}
    (data : GroundedRunLocalData cStar xi X) :
    RunSeparatedLocalLeafInputData cStar xi X :=
  runSeparatedLocalLeafFromClosedL41L42I52
    data.runPackage_input
    { hSmall := data.hSmall }

/-- Remaining concrete L.4.1/L.4.2/I.5.2 data needed before a no-input run
local leaf provider can be installed. -/
def runSeparatedLocalLeafOpenItems : List String :=
  [ "construct the run-chain weight family and chain length",
    "prove the run trichotomy into tower, return, dense-pack, and tail terms",
    "prove the period-halving estimate along the run chain",
    "combine local spike, mean-low, boundary, and chain-root terms through runSeparatedLocalLeafFromOutputPackage" ]

theorem runSeparatedLocalLeafOpenItems_nonempty :
    runSeparatedLocalLeafOpenItems = [] -> False := by
  intro h
  simp [runSeparatedLocalLeafOpenItems] at h

theorem runSeparatedLocalLeafOpenItems_length :
    runSeparatedLocalLeafOpenItems.length = 4 := by
  rfl

theorem runSeparatedLocalLeafOpenItems_eq :
    runSeparatedLocalLeafOpenItems =
      [ "construct the run-chain weight family and chain length",
        "prove the run trichotomy into tower, return, dense-pack, and tail terms",
        "prove the period-halving estimate along the run chain",
        "combine local spike, mean-low, boundary, and chain-root terms through runSeparatedLocalLeafFromOutputPackage" ] := by
  rfl

end

end Erdos260
