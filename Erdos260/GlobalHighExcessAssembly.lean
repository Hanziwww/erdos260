import Mathlib
import Erdos260.AppendixI_PackageBounds
import Erdos260.GlobalClosureAssembly

/-!
# Global high-excess assembly

This module supplies a proof-v4 aligned interface for the remaining
`GlobalAssemblyCoreInputs.highExcessCharge` slot.

The old global slot asks directly for `HighExcessChargeData`.  The structure
below instead exposes the data used by the grounded Appendix I/N route:
carry-packaged hit-gap data, the I.9 branch-mass reindexing target, the
N.2.1/N.2.2 reduced-record window-drop package, and the grounded phase-class
absorption into the six phase masses.
-/

namespace Erdos260

open MeasureTheory Finset

noncomputable section

/--
Proof-v4 aligned local data for constructing the central high-excess charge.

The only mass identity exposed here is the faithful I.9 branch-mass identity;
the raw `highExcessMass = totalMass` equality is recovered internally by the
already-proved reindexing theorem.
-/
structure GroundedHighExcessLocalData
    {shell : FailingDyadicShell} {cPr cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryData : CarryDataFromFailure shell cPr) where
  Branch : Type
  Labels : Type
  instBranch : DecidableEq Branch
  instLabels : DecidableEq Labels
  instFintypeLabels : Fintype Labels
  Q : Nat
  instQ : NeZero Q
  B : Nat
  P : Int
  hP :
    realWeightedValue (natBinaryAsReal shell.d) =
      (P : Real) / (shell.Q : Real)
  hX_eq : shell.X = 2 ^ carryData.L
  hX_pos : 1 <= shell.X
  hB : shell.Q * 4 <= 2 ^ B
  hKr : carryData.r + 1 <= (supportShell shell.d shell.X).card
  VarDrop : Real
  Cmul : Real
  Y : Real
  D : Real -> AppendixN.FirstCrossingRecordData Branch Q Labels
  branches : Finset Branch
  dropDensity : Real -> Real
  dropMass : Real -> Branch -> Nat -> Real
  hdrop_nonneg : forall T b e, 0 <= dropMass T b e
  crossingIndic : Real -> Nat -> Real
  hindic_nonneg : forall T e, 0 <= crossingIndic T e
  hlift_le : forall T b e, dropMass T b e <= crossingIndic T e
  support : Real -> Nat -> Finset Branch
  hsupp : forall T e, support T e ⊆ branches
  hzero : forall T e, forall b, b ∈ branches -> b ∉ support T e -> dropMass T b e = 0
  hle : forall T e, (D T).loIdx e <= (D T).hiIdx e
  hinj :
    forall T (e : Nat), forall b, b ∈ support T e -> forall b', b' ∈ support T e ->
      (D T).record e b = (D T).record e b' ->
        (D T).startResidue b = (D T).startResidue b' -> b = b'
  s : Nat
  K : Finset Nat
  A : Set Real
  totalMass : Real
  termMass : Real
  absorbedBound : Real
  densePackClass : Finset Nat
  hDensePackClass :
    densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints
  chernoffClass : Finset phases.toClosurePhaseData.chernoff.α
  hChernoffClass :
    chernoffClass ⊆
      highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y
  towerClass : Finset TowerExit
  hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet
  O_E : Real
  O_CNL : Real
  O_V : Real
  hBranchMass_eq :
    branchWeightedMass
        ((highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y).image
            (stoppedBranchOf carryData.a carryData.r))
        (windowExcessWeight carryData.T)
      = totalMass
  hsplit : totalMass = termMass + VarDrop
  hterm : termMass <= absorbedBound
  hK : forall k, k ∈ K -> s <= k
  hKwin :
    forall k, k ∈ K ->
      k + 1 < carryData.carry.hits.firstIndexAbove shell.X + carryData.r
  hCmulY : 0 <= Cmul * Y
  hA : MeasurableSet A
  hdrop_int : IntegrableOn dropDensity A volume
  hvar : VarDrop <= Cmul * Y * ∫ T in A, dropDensity T ∂volume
  hdensity :
    forall T, T ∈ A -> dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e
  hindic :
    forall T, T ∈ A -> forall e,
      crossingIndic T e =
        AppendixN.crossingIndicator (T + Y)
          (AppendixN.windowSum (fun n => (hitGap carryData.a n : Real)) s) e
  hAbsorbed :
    absorbedBound <=
      (densePackClass.card : Real)
        + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
        + O_E + O_CNL
        + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b)
  hWindow :
    (Cmul * ((Q * Fintype.card Labels * Q : Nat) : Real) * Y *
        (2 * ((carryData.L + B + 1 : Nat) : Real) * (K.card : Real))) <= O_V
  hE : O_E <= termReturn phases.toClosurePhaseData
  hCNL : O_CNL <= termCnl phases.toClosurePhaseData
  hV : O_V <= termRun phases.toClosurePhaseData

/-- The I.9 branch-weighted mass attached to the carry-selected high-excess starts. -/
def groundedHighExcessBranchMass
    {shell : FailingDyadicShell} {cPr : Real}
    (carryData : CarryDataFromFailure shell cPr) : Real :=
  branchWeightedMass
    ((highExcessStarts carryData.starts (hitGap carryData.a)
      carryData.r carryData.T carryData.Y).image
        (stoppedBranchOf carryData.a carryData.r))
    (windowExcessWeight carryData.T)

/--
High-excess local data with the I.9 branch-mass reindexing no longer exposed as
an input field.  The total mass used by the C1-VD split is definitionally the
actual branch-weighted mass of the carry-selected high-excess starts.
-/
structure BranchMassGroundedHighExcessLocalData
    {shell : FailingDyadicShell} {cPr cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryData : CarryDataFromFailure shell cPr) where
  Branch : Type
  Labels : Type
  instBranch : DecidableEq Branch
  instLabels : DecidableEq Labels
  instFintypeLabels : Fintype Labels
  Q : Nat
  instQ : NeZero Q
  B : Nat
  P : Int
  hP :
    realWeightedValue (natBinaryAsReal shell.d) =
      (P : Real) / (shell.Q : Real)
  hX_eq : shell.X = 2 ^ carryData.L
  hX_pos : 1 <= shell.X
  hB : shell.Q * 4 <= 2 ^ B
  hKr : carryData.r + 1 <= (supportShell shell.d shell.X).card
  VarDrop : Real
  Cmul : Real
  Y : Real
  D : Real -> AppendixN.FirstCrossingRecordData Branch Q Labels
  branches : Finset Branch
  dropDensity : Real -> Real
  dropMass : Real -> Branch -> Nat -> Real
  hdrop_nonneg : forall T b e, 0 <= dropMass T b e
  crossingIndic : Real -> Nat -> Real
  hindic_nonneg : forall T e, 0 <= crossingIndic T e
  hlift_le : forall T b e, dropMass T b e <= crossingIndic T e
  support : Real -> Nat -> Finset Branch
  hsupp : forall T e, support T e ⊆ branches
  hzero : forall T e, forall b, b ∈ branches -> b ∉ support T e -> dropMass T b e = 0
  hle : forall T e, (D T).loIdx e <= (D T).hiIdx e
  hinj :
    forall T (e : Nat), forall b, b ∈ support T e -> forall b', b' ∈ support T e ->
      (D T).record e b = (D T).record e b' ->
        (D T).startResidue b = (D T).startResidue b' -> b = b'
  s : Nat
  K : Finset Nat
  A : Set Real
  termMass : Real
  absorbedBound : Real
  densePackClass : Finset Nat
  hDensePackClass :
    densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints
  chernoffClass : Finset phases.toClosurePhaseData.chernoff.α
  hChernoffClass :
    chernoffClass ⊆
      highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y
  towerClass : Finset TowerExit
  hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet
  O_E : Real
  O_CNL : Real
  O_V : Real
  hsplit : groundedHighExcessBranchMass carryData = termMass + VarDrop
  hterm : termMass <= absorbedBound
  hK : forall k, k ∈ K -> s <= k
  hKwin :
    forall k, k ∈ K ->
      k + 1 < carryData.carry.hits.firstIndexAbove shell.X + carryData.r
  hCmulY : 0 <= Cmul * Y
  hA : MeasurableSet A
  hdrop_int : IntegrableOn dropDensity A volume
  hvar : VarDrop <= Cmul * Y * ∫ T in A, dropDensity T ∂volume
  hdensity :
    forall T, T ∈ A -> dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e
  hindic :
    forall T, T ∈ A -> forall e,
      crossingIndic T e =
        AppendixN.crossingIndicator (T + Y)
          (AppendixN.windowSum (fun n => (hitGap carryData.a n : Real)) s) e
  hAbsorbed :
    absorbedBound <=
      (densePackClass.card : Real)
        + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
        + O_E + O_CNL
        + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b)
  hWindow :
    (Cmul * ((Q * Fintype.card Labels * Q : Nat) : Real) * Y *
        (2 * ((carryData.L + B + 1 : Nat) : Real) * (K.card : Real))) <= O_V
  hE : O_E <= termReturn phases.toClosurePhaseData
  hCNL : O_CNL <= termCnl phases.toClosurePhaseData
  hV : O_V <= termRun phases.toClosurePhaseData

/-- Forget the branch-mass-normalized high-excess data to the existing grounded route. -/
def BranchMassGroundedHighExcessLocalData.toGroundedHighExcessLocalData
    {shell : FailingDyadicShell} {cPr cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryData : CarryDataFromFailure shell cPr}
    (data : BranchMassGroundedHighExcessLocalData phases carryData) :
    GroundedHighExcessLocalData phases carryData where
  Branch := data.Branch
  Labels := data.Labels
  instBranch := data.instBranch
  instLabels := data.instLabels
  instFintypeLabels := data.instFintypeLabels
  Q := data.Q
  instQ := data.instQ
  B := data.B
  P := data.P
  hP := data.hP
  hX_eq := data.hX_eq
  hX_pos := data.hX_pos
  hB := data.hB
  hKr := data.hKr
  VarDrop := data.VarDrop
  Cmul := data.Cmul
  Y := data.Y
  D := data.D
  branches := data.branches
  dropDensity := data.dropDensity
  dropMass := data.dropMass
  hdrop_nonneg := data.hdrop_nonneg
  crossingIndic := data.crossingIndic
  hindic_nonneg := data.hindic_nonneg
  hlift_le := data.hlift_le
  support := data.support
  hsupp := data.hsupp
  hzero := data.hzero
  hle := data.hle
  hinj := data.hinj
  s := data.s
  K := data.K
  A := data.A
  totalMass := groundedHighExcessBranchMass carryData
  termMass := data.termMass
  absorbedBound := data.absorbedBound
  densePackClass := data.densePackClass
  hDensePackClass := data.hDensePackClass
  chernoffClass := data.chernoffClass
  hChernoffClass := data.hChernoffClass
  towerClass := data.towerClass
  hTowerClass := data.hTowerClass
  O_E := data.O_E
  O_CNL := data.O_CNL
  O_V := data.O_V
  hBranchMass_eq := by rfl
  hsplit := data.hsplit
  hterm := data.hterm
  hK := data.hK
  hKwin := data.hKwin
  hCmulY := data.hCmulY
  hA := data.hA
  hdrop_int := data.hdrop_int
  hvar := data.hvar
  hdensity := data.hdensity
  hindic := data.hindic
  hAbsorbed := data.hAbsorbed
  hWindow := data.hWindow
  hE := data.hE
  hCNL := data.hCNL
  hV := data.hV

/-- Convert proof-v4 aligned local data into the old high-excess charge slot. -/
def GroundedHighExcessLocalData.toHighExcessChargeData
    {shell : FailingDyadicShell} {cPr cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryData : CarryDataFromFailure shell cPr}
    (data : GroundedHighExcessLocalData phases carryData) :
    HighExcessChargeData phases carryData := by
  letI : DecidableEq data.Branch := data.instBranch
  letI : DecidableEq data.Labels := data.instLabels
  letI : Fintype data.Labels := data.instFintypeLabels
  letI : NeZero data.Q := data.instQ
  exact
    HighExcessChargeData.ofC1VDClosure_grounded_lowerLabelRecordDensity_carryHitGap_branchMass
      (Branch := data.Branch) (Labels := data.Labels) (Q := data.Q)
      (B := data.B) (P := data.P)
      phases carryData
      data.hP data.hX_eq data.hX_pos data.hB data.hKr
      data.VarDrop data.Cmul data.Y data.D data.branches
      data.dropDensity data.dropMass data.hdrop_nonneg
      data.crossingIndic data.hindic_nonneg data.hlift_le
      data.support data.hsupp data.hzero data.hle data.hinj
      data.s data.K data.A data.totalMass data.termMass data.absorbedBound
      data.hDensePackClass data.hChernoffClass data.hTowerClass
      data.hBranchMass_eq data.hsplit data.hterm
      data.hK data.hKwin data.hCmulY data.hA data.hdrop_int
      data.hvar data.hdensity data.hindic
      data.hAbsorbed data.hWindow data.hE data.hCNL data.hV

/-- Convert branch-mass-normalized high-excess data into the old high-excess charge slot. -/
def BranchMassGroundedHighExcessLocalData.toHighExcessChargeData
    {shell : FailingDyadicShell} {cPr cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryData : CarryDataFromFailure shell cPr}
    (data : BranchMassGroundedHighExcessLocalData phases carryData) :
    HighExcessChargeData phases carryData :=
  data.toGroundedHighExcessLocalData.toHighExcessChargeData

/--
Global provider for the proof-v4 aligned high-excess route.  It has the same
outer quantification as `HighExcessChargeProvider`, but its payload is the
grounded branch-mass/N.2 data rather than a raw `HighExcessChargeData`.
-/
structure GroundedHighExcessChargeProvider where
  constants : Erdos260Constants
  data :
    forall (shell : FailingDyadicShell)
      (_hcQ : shell.cQ = constants.cQ)
      (phases : SixPhaseFactoryData constants.cStar constants.ξ
        (shell.X : Real))
      (carryData : CarryDataFromFailure shell constants.cPr),
        GroundedHighExcessLocalData phases carryData

/-- Forget the proof-v4 aligned provider to the legacy high-excess provider. -/
def GroundedHighExcessChargeProvider.toHighExcessChargeProvider
    (provider : GroundedHighExcessChargeProvider) :
    HighExcessChargeProvider where
  constants := provider.constants
  data := by
    intro shell hcQ phases carryData
    exact
      (provider.data shell hcQ phases carryData).toHighExcessChargeData

/--
Core global assembly with the high-excess slot replaced by the grounded
proof-v4 route.
-/
structure GlobalAssemblyCoreGroundedHighExcessInputs where
  carryData :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ -> shell.aboveCarryThreshold ->
        CarryDataFromFailure shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        RunFactoryData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  /-- **Phase-mass nonnegativity (manuscript §I / J.1.1 charging).** Forwarded into the
  `GlobalAssemblyCoreInputs.returnRunMassNonneg` slot. -/
  returnRunMassNonneg :
    forall (shell : FailingDyadicShell) (hcQ : shell.cQ = erdos260Constants.cQ),
      0 ≤ (returnPkg shell hcQ).massSum + (run shell hcQ).runMass
  highExcess :
    forall (shell : FailingDyadicShell)
      (_hcQ : shell.cQ = erdos260Constants.cQ)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real))
      (carryData : CarryDataFromFailure shell erdos260Constants.cPr),
        GroundedHighExcessLocalData phases carryData

/--
Forget the grounded high-excess interface to the existing reduced core inputs.
-/
def GlobalAssemblyCoreGroundedHighExcessInputs.toCoreInputs
    (data : GlobalAssemblyCoreGroundedHighExcessInputs) :
    GlobalAssemblyCoreInputs where
  carryData := data.carryData
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  returnRunMassNonneg := data.returnRunMassNonneg
  highExcessCharge := by
    intro shell hcQ phases carryData _hphases
    exact
      (data.highExcess shell hcQ phases carryData).toHighExcessChargeData

/--
Erdos 260 from the reduced core interface whose high-excess slot is supplied by
the grounded proof-v4 branch-mass/N.2 route.
-/
theorem erdos260_final_core_grounded_highExcess
    (data : GlobalAssemblyCoreGroundedHighExcessInputs) :
    Erdos260Statement :=
  erdos260_final_core data.toCoreInputs

end

end Erdos260
