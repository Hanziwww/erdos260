import Mathlib
import Erdos260.AppendixL3_Tower
import Erdos260.CarryDataFactory

/-!
# Refined tower and L.3 factory interface

This file names the remaining tower obligations separately from the already
proved arithmetic wrapper `towerPackageBound`.
-/

namespace Erdos260

open Finset

noncomputable section

/--
The geometric content needed to use Theorem E.6.

After the E.6 proof in `RefinedTower.lean`, the cycle witness is a real
theorem of any coherent refined recurrent SCC.  `RefinedTowerCycleData` remains
as a standalone target for the refined tower construction; the final L.3 tower
package below only carries the charged transient summability data consumed by
`TowerPackageData`.
-/
abbrev RefinedTowerCycleData (S : RefinedRecurrentSCC) : Prop := S.Coherent

theorem RefinedTowerCycleData.outgoingUnique
    {S : RefinedRecurrentSCC} (data : RefinedTowerCycleData S)
    {v w₁ w₂ : RefinedVertex}
    (hv : v ∈ S.vertices) (hw₁ : w₁ ∈ S.vertices) (hw₂ : w₂ ∈ S.vertices)
    (h₁ : S.edge v w₁) (h₂ : S.edge v w₂) :
    w₁ = w₂ :=
  theoremE5_outgoingUnique data hv hw₁ hw₂ h₁ h₂

theorem RefinedTowerCycleData.simpleCycle
    {S : RefinedRecurrentSCC} (data : RefinedTowerCycleData S) :
    S.IsSimpleCycle :=
  theoremE6_recurrentSCCSimpleCycle S data

theorem RefinedTowerCycleData.recurrentSCCSimpleCycle
    {S : RefinedRecurrentSCC} (data : RefinedTowerCycleData S) :
    S.IsSimpleCycle :=
  data.simpleCycle

/--
The L.3 tower transient-excursion package in the shape needed by
`TowerPackageData`.
-/
structure TowerTransientFactoryData (cStar ξ X : ℝ) where
  entryExitSet : Finset TowerExit
  chargedWeight : TowerExit -> ℝ
  chargedWeight_nonneg : ∀ b ∈ entryExitSet, 0 <= chargedWeight b
  outputBoundConstant : ℝ
  nextLayerMass : ℝ
  smallError : ℝ
  hSummable :
    ∑ b ∈ entryExitSet, chargedWeight b <=
      outputBoundConstant * nextLayerMass + smallError
  hSmall :
    outputBoundConstant * nextLayerMass + smallError <= cStar * ξ * X / 6

/-- Convert L.3 tower-transient data into Phase-7 package data. -/
def TowerTransientFactoryData.toTowerPackageData
    {cStar ξ X : ℝ}
    (data : TowerTransientFactoryData cStar ξ X) :
    TowerPackageData cStar ξ X where
  entryExitSet := data.entryExitSet
  chargedWeight := data.chargedWeight
  chargedWeight_nonneg := data.chargedWeight_nonneg
  outputBoundConstant := data.outputBoundConstant
  nextLayerMass := data.nextLayerMass
  smallError := data.smallError
  hSummable := data.hSummable
  hSmall := data.hSmall

/-- Phase-7 tower bound obtained from the explicit L.3 factory data. -/
theorem towerPackageBound_of_transientFactory
    {cStar ξ X : ℝ}
    (data : TowerTransientFactoryData cStar ξ X) :
    ∃ Tower : ℝ,
      0 <= Tower ∧
      Tower <= cStar * ξ * X / 6 :=
  towerPackageBound data.toTowerPackageData

/-- Per-shell provider for the refined tower / L.3 tower transient data. -/
structure TowerDataProvider where
  constants : Erdos260Constants
  data :
    ∀ shell : FailingDyadicShell,
      shell.cQ = constants.cQ ->
        TowerTransientFactoryData constants.cStar constants.ξ (shell.X : ℝ)

theorem TowerDataProvider.bound
    (provider : TowerDataProvider)
    {shell : FailingDyadicShell}
    (hcQ : shell.cQ = provider.constants.cQ) :
    ∃ Tower : ℝ,
      0 <= Tower ∧
      Tower <= provider.constants.cStar * provider.constants.ξ * (shell.X : ℝ) / 6 :=
  towerPackageBound_of_transientFactory (provider.data shell hcQ)

end

end Erdos260
