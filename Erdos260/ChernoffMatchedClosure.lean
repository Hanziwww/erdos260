import Erdos260.P9V3Closure
import Erdos260.Chernoff221ASeedClosure
import Erdos260.Chernoff221AAreaClosureCore
import Erdos260.ChernoffClass0GenuineLeaf
import Erdos260.ActiveWindowContainmentCore

/-!
# V3 Chernoff matched closure boundary

This module isolates the sharp class-0 Chernoff surface needed by
`P9V3RunResidual`.

The current V3 residual asks for a `Class0ChernoffInjection` over
`faithfulCapacityPhases (v3Budget ...) ctx`. The constructor
`Class0ChernoffInjection.ofChargeWindowAreaCap` already discharges the
active-window gap and multiplier bookkeeping once the genuine matched charge
seed is supplied: map, high-cost membership, injectivity, active-window
containment, and the 22.1A area-positive cap.

The same faithful target family is the fixed four-path Section 22 model leaf,
so any such faithful-family injection forces `|routedFibre ... 0| <= 4`. This
file therefore does not manufacture an unconditional faithful injection. Instead
it packages the exact seed core usable by P9/V3 and records the obstruction.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## 1. The matched Chernoff seed needed by V3 -/

/-- The sharp class-0 Chernoff matched seed for a routed budget.

This is the exact residual consumed by
`Class0ChernoffInjection.ofChargeWindowAreaCap`: the J.1.7 charge map into the
faithful high-cost family, K.1.3 injectivity, active-window containment, and the
area-positive cap. The gap field, residual multiplier, nonnegativity, and final
domination are derived by the existing constructor. -/
structure ChernoffMatchedSeedForBudget
    (budget : forall ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) where
  /-- The matched Section 22 path assigned to each class-0 start. -/
  chargeOf : forall ctx : ActualFailureContext,
    Nat -> ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.α
  /-- Assigned paths lie in the faithful high-cost family. -/
  hmaps : forall ctx : ActualFailureContext,
    forall k, k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0 ->
      chargeOf ctx k ∈ highCostSet
        ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.paths
        ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.cost
        ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.Y
  /-- Distinct class-0 starts receive distinct assigned paths. -/
  hinj : forall ctx : ActualFailureContext,
    forall x, x ∈ routedFibre ctx.n24CarryData (budget ctx).route 0 ->
      forall y, y ∈ routedFibre ctx.n24CarryData (budget ctx).route 0 ->
        chargeOf ctx x = chargeOf ctx y -> x = y
  /-- The active-window containment of each class-0 descent window. -/
  hwin : forall ctx : ActualFailureContext,
    forall k, k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0 ->
      exists r0 : Nat, r0 + 1 <= (supportShell ctx.shell.d ctx.shell.X).card /\
        k + ctx.n24CarryData.r
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + r0
  /-- The 22.1A area-positive cap at the dyadic shell gap scale. -/
  hcapPos : forall ctx : ActualFailureContext,
    forall k, k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0 ->
      ((ctx.n24CarryData.r : Real) + 1) * (class0ShellGapScale ctx : Real) - ctx.n24CarryData.T
        <= ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.weight
            (chargeOf ctx k)

namespace ChernoffMatchedSeedForBudget

variable {budget : forall ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}

/-- The matched seed builds the full V3 `Class0ChernoffInjection`. -/
def toInjection (S : ChernoffMatchedSeedForBudget budget) :
    Class0ChernoffInjection budget :=
  Class0ChernoffInjection.ofChargeWindowAreaCap budget
    S.chargeOf S.hmaps S.hinj S.hwin S.hcapPos

/-- The matched seed closes the class-0 Chernoff ledger field. -/
theorem hChernoffField (S : ChernoffMatchedSeedForBudget budget) :
    forall ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 0
        <= termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  S.toInjection.hChernoffField

/-- The faithful-family matched seed forces the fixed four-path count. -/
theorem fibre_card_le_four (S : ChernoffMatchedSeedForBudget budget)
    (ctx : ActualFailureContext) :
    (routedFibre ctx.n24CarryData (budget ctx).route 0).card <= 4 := by
  have h := S.toInjection.fibre_card_le ctx
  rwa [class0_highCostFamily_card] at h

end ChernoffMatchedSeedForBudget

/-! ## 2. Faithful-family obstruction -/

namespace Class0ChernoffInjection

variable {budget : forall ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}

/-- Any V3 `Class0ChernoffInjection` over the faithful family forces `|fibre_0| <= 4`. -/
theorem fibre_card_le_four (R : Class0ChernoffInjection budget)
    (ctx : ActualFailureContext) :
    (routedFibre ctx.n24CarryData (budget ctx).route 0).card <= 4 := by
  have h := R.fibre_card_le ctx
  rwa [class0_highCostFamily_card] at h

end Class0ChernoffInjection

/-- The exact faithful matching equivalence: a high-cost injective assignment exists iff the
class-0 fibre has at most four starts. -/
theorem faithfulChernoffMatching_iff_le_four
    (budget : forall ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    (exists f : Nat -> (faithfulChern budget ctx).α,
        (forall k, k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0 ->
          f k ∈ highCostSet (faithfulChern budget ctx).paths
            (faithfulChern budget ctx).cost (faithfulChern budget ctx).Y)
        /\ Set.InjOn f (routedFibre ctx.n24CarryData (budget ctx).route 0 : Set Nat))
      <-> (routedFibre ctx.n24CarryData (budget ctx).route 0).card <= 4 :=
  faithful_matching_iff_le_four budget ctx

/-- No faithful-family V3 Chernoff injection can exist on a context with five class-0 starts. -/
theorem no_class0ChernoffInjection_of_five_le
    {budget : forall ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (ctx : ActualFailureContext)
    (hwide : 5 <= (routedFibre ctx.n24CarryData (budget ctx).route 0).card) :
    Nonempty (Class0ChernoffInjection budget) -> False := by
  rintro ⟨R⟩
  have hle := R.fibre_card_le_four ctx
  omega

/-- No matched seed for the faithful family can exist on a context with five class-0 starts. -/
theorem no_chernoffMatchedSeedForBudget_of_five_le
    {budget : forall ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (ctx : ActualFailureContext)
    (hwide : 5 <= (routedFibre ctx.n24CarryData (budget ctx).route 0).card) :
    Nonempty (ChernoffMatchedSeedForBudget budget) -> False := by
  rintro ⟨S⟩
  have hle := S.fibre_card_le_four ctx
  omega

/-! ## 3. The multiplicity-aware area-family replacement -/

/-- The class-0 active-window field of the matched seed, discharged from the shared
`WindowInteriorResidual`.  This is only the containment component; it does not create a faithful
four-path injection. -/
theorem WindowInteriorResidual.chernoffMatchedHwin
    {budget : forall ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (R : WindowInteriorResidual budget) :
    forall ctx : ActualFailureContext,
      forall k, k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0 ->
        exists r0 : Nat, r0 + 1 <= (supportShell ctx.shell.d ctx.shell.X).card /\
          k + ctx.n24CarryData.r
            < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + r0 :=
  R.chernoffHwin

/-- Multiplicity-aware class-0 Chernoff area seed over the genuine stopped-branch §22 family.

This is the replacement for a faithful four-path `ChernoffMatchedSeedForBudget`: the matching target
is the actual carry stopped-branch family `genuineCarryChern`, whose high-cost set can scale with the
shell.  It therefore avoids the false `|routedFibre_0| <= 4` consequence while retaining the exact
J.1.7/K.1.3 matching shape and the 22.1A Kraft area input. -/
structure ChernoffGenuineAreaSeedForBudget
    (budget : forall ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) where
  /-- The §22 stopped-tree antichain/Kraft measure-sum. -/
  hK : forall ctx : ActualFailureContext, chernoffClass0KraftSum ctx <= 1
  /-- The genuine high-cost stopped-branch family is nonempty. -/
  hne : forall ctx : ActualFailureContext,
    (highCostSet (genuineCarryChern ctx (hK ctx)).paths
      (genuineCarryChern ctx (hK ctx)).cost
      (genuineCarryChern ctx (hK ctx)).Y).Nonempty
  /-- The I.4.2 progress count into the genuine, shell-scaling stopped-branch family. -/
  hcard : forall ctx : ActualFailureContext,
    (routedFibre ctx.n24CarryData (budget ctx).route 0).card <=
      (highCostSet (genuineCarryChern ctx (hK ctx)).paths
        (genuineCarryChern ctx (hK ctx)).cost
        (genuineCarryChern ctx (hK ctx)).Y).card
  /-- Matched J.1.7 per-path area domination against the order-rank genuine family matching. -/
  hdom : forall ctx : ActualFailureContext,
    forall k, k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0 ->
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        <= (genuineCarryChern ctx (hK ctx)).weight
            (finRankMatch (routedFibre ctx.n24CarryData (budget ctx).route 0)
              (highCostSet (genuineCarryChern ctx (hK ctx)).paths
                (genuineCarryChern ctx (hK ctx)).cost
                (genuineCarryChern ctx (hK ctx)).Y)
              (hne ctx) k)

namespace ChernoffGenuineAreaSeedForBudget

variable {budget : forall ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}

/-- The genuine stopped-branch area seed builds the family-generic matched charge. -/
def toMatchedCharge (S : ChernoffGenuineAreaSeedForBudget budget) :
    Chernoff221AAreaMatchedCharge budget (fun ctx => genuineCarryChern ctx (S.hK ctx)) :=
  chernoffClass0_genuine_of_kraftCountDom budget S.hK S.hne S.hcard S.hdom

/-- The genuine matched charge bounds class-0 routed mass by the genuine §22 area family sum. -/
theorem hAreaBound (S : ChernoffGenuineAreaSeedForBudget budget) :
    forall ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 0
        <= chernoffAreaFamilySum (genuineCarryChern ctx (S.hK ctx)) :=
  fun ctx => S.toMatchedCharge.hAreaBound ctx

/-- The genuine §22 area family sum is bounded by `1` from the Kraft input. -/
theorem hAreaBound_le_one (S : ChernoffGenuineAreaSeedForBudget budget)
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 0 <= 1 :=
  chernoffClass0_routedMass_le_one_of_kraft budget S.hK S.toMatchedCharge ctx

/-- The exact ctx-pinned P9/V3 Chernoff ledger field, proved without a faithful four-path injection. -/
theorem hChernoffField (S : ChernoffGenuineAreaSeedForBudget budget) :
    forall ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 0
        <= termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  fun ctx => chernoffClass0_hChernoffField_of_kraft budget S.hK S.toMatchedCharge ctx

end ChernoffGenuineAreaSeedForBudget

/-! ## 4. P9 ledger bridge using the genuine area-family Chernoff seed -/

/-- P9/V3 run residual with class 0 supplied by the genuine stopped-branch area seed.

Unlike `P9V3RunChernoffMatchedSeedResidual`, this does not assemble an
`Erdos260MinimalResidualV3`, because that structure still asks for faithful four-path class-0
fields.  It instead targets the ctx-pinned ledger API directly, where the class-0 ledger inequality
is the only required output. -/
structure P9V3RunGenuineChernoffAreaResidual where
  towerCount : forall ctx : ActualFailureContext, Class2ActiveFloorCount ctx
  runResidual : forall ctx : ActualFailureContext, RunClass5LeafResidual ctx
  returnCharge : forall ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx
  chernoff : ChernoffGenuineAreaSeedForBudget
    (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)
  cnl : Class1CNLInjection
    (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)
  densePackCount : forall ctx : ActualFailureContext,
    (genuineDensePackStarts ctx).card
      <= (densePackMarkers
        (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge) ctx).card
  windowReach : ActualFailureContext -> Nat
  hReach : forall ctx : ActualFailureContext,
    windowReach ctx + 1 <= (supportShell ctx.shell.d ctx.shell.X).card
  hContain : forall ctx : ActualFailureContext, forall k, k ∈ genuineDensePackStarts ctx ->
    k + ctx.n24CarryData.r
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx
  hScale : forall ctx : ActualFailureContext,
    ((ctx.n24CarryData.r : Real) + 1) * (densePackDyadicG0 ctx : Real) - ctx.n24CarryData.T <= 1

namespace P9V3RunGenuineChernoffAreaResidual

/-- The routed V3 budget associated to the genuine-area Chernoff residual. -/
def budget (R : P9V3RunGenuineChernoffAreaResidual) :
    forall ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  v3Budget R.towerCount (p9V3RunChainOfResidual R.runResidual) R.returnCharge

/-- DensePack ledger field for the associated budget. -/
theorem hDensePackField (R : P9V3RunGenuineChernoffAreaResidual) :
    forall ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (R.budget ctx).route 3
        <= termDensePack (faithfulCapacityPhases R.budget ctx).toClosurePhaseData :=
  hDensePack_field_ofCardLe R.budget
    (fun ctx => by
      simp [budget, v3Budget_route])
    R.densePackCount densePackDyadicG0
    (densePackGap_ofContainment R.budget
      (fun ctx => by
        simp [budget, v3Budget_route])
      R.windowReach R.hReach R.hContain)
    R.hScale

/-- The ctx-pinned P9 ledger residual obtained from the genuine-area Chernoff seed. -/
def toLedger (R : P9V3RunGenuineChernoffAreaResidual) : P9CtxPinnedLedgerResidual where
  budget := R.budget
  hChernoff := R.chernoff.hChernoffField
  hCnl := R.cnl.hCnlField
  hDensePack := R.hDensePackField
  hTRT := seedHTRT R.budget
  hOldRes := fun ctx => by
    simpa [budget, v3Budget_route] using
      (show routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 6
          <= ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k from by
        rw [genuineChargeRoute_routed6_zero ctx]
        exact oldResL65_branchMass_nonneg ctx)

/-- P9 endpoint through the ctx-pinned ledger API using the genuine §22 area-family class-0 seed. -/
theorem toStatement (R : P9V3RunGenuineChernoffAreaResidual) : Erdos260Statement :=
  R.toLedger.toStatement

end P9V3RunGenuineChernoffAreaResidual

/-- P9/V3 endpoint with class 0 supplied by the genuine stopped-branch area family rather than a
faithful four-path injection. -/
theorem erdos260_p9V3_of_genuineChernoffArea
    (R : P9V3RunGenuineChernoffAreaResidual) : Erdos260Statement :=
  R.toStatement

/-! ## 3. V3/P9 bridges from the matched seed -/

/-- Assemble `Erdos260MinimalResidualV3` with Chernoff supplied as the sharp matched seed. -/
def erdos260MinimalResidualV3_ofChernoffMatchedSeed
    (towerCount : forall ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : forall ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : forall ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : ChernoffMatchedSeedForBudget (v3Budget towerCount runChain returnCharge))
    (cnl : Class1CNLInjection (v3Budget towerCount runChain returnCharge))
    (densePackCount : forall ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card
        <= (densePackMarkers (v3Budget towerCount runChain returnCharge) ctx).card)
    (windowReach : ActualFailureContext -> Nat)
    (hReach : forall ctx : ActualFailureContext,
      windowReach ctx + 1 <= (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : forall ctx : ActualFailureContext, forall k, k ∈ genuineDensePackStarts ctx ->
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : forall ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : Real) + 1) * (densePackDyadicG0 ctx : Real) - ctx.n24CarryData.T <= 1) :
    Erdos260MinimalResidualV3 :=
  erdos260MinimalResidualV3_ofClassData towerCount runChain returnCharge
    chernoff.toInjection cnl densePackCount windowReach hReach hContain hScale

/-- Erdős #260 from V3 class data with Chernoff supplied as the sharp matched seed. -/
theorem erdos260_of_classData_chernoffMatchedSeed
    (towerCount : forall ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : forall ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : forall ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : ChernoffMatchedSeedForBudget (v3Budget towerCount runChain returnCharge))
    (cnl : Class1CNLInjection (v3Budget towerCount runChain returnCharge))
    (densePackCount : forall ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card
        <= (densePackMarkers (v3Budget towerCount runChain returnCharge) ctx).card)
    (windowReach : ActualFailureContext -> Nat)
    (hReach : forall ctx : ActualFailureContext,
      windowReach ctx + 1 <= (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : forall ctx : ActualFailureContext, forall k, k ∈ genuineDensePackStarts ctx ->
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : forall ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : Real) + 1) * (densePackDyadicG0 ctx : Real) - ctx.n24CarryData.T <= 1) :
    Erdos260Statement :=
  erdos260_of_minimalResidualV3
    (erdos260MinimalResidualV3_ofChernoffMatchedSeed towerCount runChain returnCharge
      chernoff cnl densePackCount windowReach hReach hContain hScale)

/-- P9/V3 residual with Chernoff sharpened to the seed consumed by
`Class0ChernoffInjection.ofChargeWindowAreaCap`. -/
structure P9V3RunChernoffMatchedSeedResidual where
  towerCount : forall ctx : ActualFailureContext, Class2ActiveFloorCount ctx
  runResidual : forall ctx : ActualFailureContext, RunClass5LeafResidual ctx
  returnCharge : forall ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx
  chernoff : ChernoffMatchedSeedForBudget
    (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)
  cnl : Class1CNLInjection
    (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)
  densePackCount : forall ctx : ActualFailureContext,
    (genuineDensePackStarts ctx).card
      <= (densePackMarkers
        (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge) ctx).card
  windowReach : ActualFailureContext -> Nat
  hReach : forall ctx : ActualFailureContext,
    windowReach ctx + 1 <= (supportShell ctx.shell.d ctx.shell.X).card
  hContain : forall ctx : ActualFailureContext, forall k, k ∈ genuineDensePackStarts ctx ->
    k + ctx.n24CarryData.r
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx
  hScale : forall ctx : ActualFailureContext,
    ((ctx.n24CarryData.r : Real) + 1) * (densePackDyadicG0 ctx : Real) - ctx.n24CarryData.T <= 1

namespace P9V3RunChernoffMatchedSeedResidual

/-- The full V3 Chernoff injection produced from the matched seed. -/
def chernoffInjection (R : P9V3RunChernoffMatchedSeedResidual) :
    Class0ChernoffInjection
      (v3Budget R.towerCount (p9V3RunChainOfResidual R.runResidual) R.returnCharge) :=
  R.chernoff.toInjection

/-- Convert the sharpened Chernoff-seed residual to the current P9/V3 run residual. -/
def toP9V3RunResidual (R : P9V3RunChernoffMatchedSeedResidual) :
    P9V3RunResidual where
  towerCount := R.towerCount
  runResidual := R.runResidual
  returnCharge := R.returnCharge
  chernoff := R.chernoffInjection
  cnl := R.cnl
  densePackCount := R.densePackCount
  windowReach := R.windowReach
  hReach := R.hReach
  hContain := R.hContain
  hScale := R.hScale

/-- Assemble the V3 minimal residual from the P9 run-leaf residual and Chernoff matched seed. -/
def toMinimalResidualV3 (R : P9V3RunChernoffMatchedSeedResidual) :
    Erdos260MinimalResidualV3 :=
  R.toP9V3RunResidual.toMinimalResidualV3

/-- Convert the Chernoff-seed residual into the ctx-pinned P9 routing residual. -/
def toP9CtxPinnedRoutingZero (R : P9V3RunChernoffMatchedSeedResidual) :
    P9CtxPinnedRoutingZeroResidual :=
  R.toP9V3RunResidual.toP9CtxPinnedRoutingZero

/-- The P9 endpoint from the Chernoff matched seed. -/
theorem toStatement (R : P9V3RunChernoffMatchedSeedResidual) : Erdos260Statement :=
  R.toP9V3RunResidual.toStatement

end P9V3RunChernoffMatchedSeedResidual

/-- P9/V3 endpoint with Chernoff supplied as the sharp matched seed. -/
theorem erdos260_p9V3_of_chernoffMatchedSeed
    (R : P9V3RunChernoffMatchedSeedResidual) : Erdos260Statement :=
  R.toStatement

/-- V3-specialized obstruction for the current P9 run-leaf budget. -/
theorem no_p9V3_class0ChernoffInjection_of_five_le
    (towerCount : forall ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : forall ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnCharge : forall ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (ctx : ActualFailureContext)
    (hwide : 5 <=
      (routedFibre ctx.n24CarryData
        (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge ctx).route 0).card) :
    Nonempty (Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)) -> False :=
  no_class0ChernoffInjection_of_five_le ctx hwide

/-! ## 4. Machine-readable status -/

/-- Status of the V3 matched-Chernoff closure attempt. -/
def chernoffMatchedClosureStatus : List String :=
  [ "BRIDGE PROVED: ChernoffMatchedSeedForBudget.toInjection builds Class0ChernoffInjection via Class0ChernoffInjection.ofChargeWindowAreaCap.",
    "BRIDGE PROVED: ChernoffMatchedSeedForBudget.hChernoffField closes the class-0 ledger once the seed map, membership, injectivity, active-window containment, and area-positive cap are supplied.",
    "BRIDGE PROVED: erdos260MinimalResidualV3_ofChernoffMatchedSeed and P9V3RunChernoffMatchedSeedResidual.toStatement make the seed usable in V3/P9 assembly.",
    "OBSTRUCTION PROVED: any faithful-family Class0ChernoffInjection, and any such matched seed, forces |routedFibre_0| <= 4.",
    "SHARP RESIDUAL: a genuine P9/V3 Chernoff close still needs the J.1.7/K.1.3 map into the faithful high-cost family plus active-window containment and the 22.1A area-positive cap.",
    "NOT FULLY CLOSED: faithful_matching_iff_le_four shows an unconditional faithful-family provider would imply the forbidden fixed four-count in deep shells." ]

theorem chernoffMatchedClosureStatus_nonempty :
    chernoffMatchedClosureStatus != [] := by
  simp [chernoffMatchedClosureStatus]

#print axioms ChernoffMatchedSeedForBudget.toInjection
#print axioms ChernoffMatchedSeedForBudget.hChernoffField
#print axioms ChernoffMatchedSeedForBudget.fibre_card_le_four
#print axioms Class0ChernoffInjection.fibre_card_le_four
#print axioms faithfulChernoffMatching_iff_le_four
#print axioms no_class0ChernoffInjection_of_five_le
#print axioms no_chernoffMatchedSeedForBudget_of_five_le
#print axioms erdos260MinimalResidualV3_ofChernoffMatchedSeed
#print axioms erdos260_of_classData_chernoffMatchedSeed
#print axioms P9V3RunChernoffMatchedSeedResidual.toP9V3RunResidual
#print axioms P9V3RunChernoffMatchedSeedResidual.toStatement
#print axioms erdos260_p9V3_of_chernoffMatchedSeed
#print axioms no_p9V3_class0ChernoffInjection_of_five_le

end

end Erdos260
