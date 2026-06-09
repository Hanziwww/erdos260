import Mathlib
import Erdos260.AppendixL2_Return
import Erdos260.AppendixL4_Run
import Erdos260.TowerFactory

/-!
# L.2 / L.4 package factory interface

This file groups the Return and Run package factory interfaces that are still
consumed by the current per-failure assembly.  Historical charged-ledger
bookkeeping lives in the ledger modules themselves; it is no longer a provider
field of the closure endpoint.
-/

namespace Erdos260

open Finset

noncomputable section

/-- Return L.2.2 data in the exact shape needed by `ReturnPackageData`. -/
structure ReturnFactoryData (cStar ξ X : ℝ) where
  ordinaryShort : ℝ
  semiperiodic : ℝ
  olc : ℝ
  nonlocalLong : ℝ
  c1 : ℝ
  c2 : ℝ
  c3 : ℝ
  c4 : ℝ
  s : ℝ
  ij : ℝ
  smallError : ℝ
  hOrdinaryShort :
    ordinaryShort <= c1 * ξ * s * X * ij + smallError / 4
  hSemiperiodic :
    semiperiodic <= c2 * ξ * s * X * ij + smallError / 4
  hOLC :
    olc <= c3 * ξ * s * X * ij + smallError / 4
  hNonlocalLong :
    nonlocalLong <= c4 * ξ * s * X * ij + smallError / 4
  hSmall :
    (c1 + c2 + c3 + c4) * ξ * s * X * ij + smallError <= cStar * ξ * X / 6

/-- The total return mass `ordinaryShort + semiperiodic + olc + nonlocalLong`
(the manuscript Return-phase mass; definitionally `= termReturn` on the induced phase
data).  Naming the four-piece sum lets the per-shell nonnegativity hypothesis of the
charge providers be stated and discharged cleanly. -/
def ReturnFactoryData.massSum {cStar ξ X : ℝ} (data : ReturnFactoryData cStar ξ X) : ℝ :=
  data.ordinaryShort + data.semiperiodic + data.olc + data.nonlocalLong

def ReturnFactoryData.toReturnPackageData
    {cStar ξ X : ℝ}
    (data : ReturnFactoryData cStar ξ X) :
    ReturnPackageData cStar ξ X where
  ordinaryShort := data.ordinaryShort
  semiperiodic := data.semiperiodic
  olc := data.olc
  nonlocalLong := data.nonlocalLong
  c1 := data.c1
  c2 := data.c2
  c3 := data.c3
  c4 := data.c4
  s := data.s
  ij := data.ij
  smallError := data.smallError
  hOrdinaryShort := data.hOrdinaryShort
  hSemiperiodic := data.hSemiperiodic
  hOLC := data.hOLC
  hNonlocalLong := data.hNonlocalLong
  hSmall := data.hSmall

theorem nonRunReturnBound_of_factory
    {cStar ξ X : ℝ}
    (data : ReturnFactoryData cStar ξ X) :
    data.ordinaryShort + data.semiperiodic + data.olc + data.nonlocalLong <=
      cStar * ξ * X / 6 :=
  nonRunReturnBound data.toReturnPackageData

/--
Run L.4 data in the exact shape needed by `RunPackageData`.

The `trichotomy` field names the remaining combinatorial proof that every run
branch is routed to the displayed right-hand side.
-/
structure RunFactoryData (cStar ξ X : ℝ) where
  runMass : ℝ
  nextTower : ℝ
  nextReturn : ℝ
  nextDensePack : ℝ
  twoNegcY : ℝ
  Ij : ℝ
  smallError : ℝ
  trichotomy :
    runMass <=
      nextTower + nextReturn + nextDensePack + X * Ij * twoNegcY + smallError
  hSmall :
    nextTower + nextReturn + nextDensePack + X * Ij * twoNegcY + smallError <=
      cStar * ξ * X / 6

def RunFactoryData.toRunPackageData
    {cStar ξ X : ℝ}
    (data : RunFactoryData cStar ξ X) :
    RunPackageData cStar ξ X where
  runMass := data.runMass
  nextTower := data.nextTower
  nextReturn := data.nextReturn
  nextDensePack := data.nextDensePack
  twoNegcY := data.twoNegcY
  Ij := data.Ij
  smallError := data.smallError
  hRun := data.trichotomy
  hSmall := data.hSmall

theorem runBound_of_factory
    {cStar ξ X : ℝ}
    (data : RunFactoryData cStar ξ X) :
    data.runMass <= cStar * ξ * X / 6 :=
  runBound data.toRunPackageData

/-- Per-shell provider for the L.2 return package data. -/
structure ReturnDataProvider where
  constants : Erdos260Constants
  data :
    ∀ shell : FailingDyadicShell,
      shell.cQ = constants.cQ ->
        ReturnFactoryData constants.cStar constants.ξ (shell.X : ℝ)

theorem ReturnDataProvider.bound
    (provider : ReturnDataProvider)
    {shell : FailingDyadicShell}
    (hcQ : shell.cQ = provider.constants.cQ) :
    let data := provider.data shell hcQ
    data.ordinaryShort + data.semiperiodic + data.olc + data.nonlocalLong <=
      provider.constants.cStar * provider.constants.ξ * (shell.X : ℝ) / 6 := by
  dsimp
  exact nonRunReturnBound_of_factory (provider.data shell hcQ)

/-- Per-shell provider for the L.4 run package data. -/
structure RunDataProvider where
  constants : Erdos260Constants
  data :
    ∀ shell : FailingDyadicShell,
      shell.cQ = constants.cQ ->
        RunFactoryData constants.cStar constants.ξ (shell.X : ℝ)

theorem RunDataProvider.bound
    (provider : RunDataProvider)
    {shell : FailingDyadicShell}
    (hcQ : shell.cQ = provider.constants.cQ) :
    let data := provider.data shell hcQ
    data.runMass <=
      provider.constants.cStar * provider.constants.ξ * (shell.X : ℝ) / 6 := by
  dsimp
  exact runBound_of_factory (provider.data shell hcQ)

end

end Erdos260
