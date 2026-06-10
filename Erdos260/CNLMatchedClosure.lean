import Erdos260.P9V3Closure
import Erdos260.CNLUnconditionalProvider

/-!
# V3 clean-CNL matched closure boundary

This module separates the two CNL surfaces that currently coexist in the
development.

* The factory provider `cnlUnconditionalProvider` supplies a per-shell
  `CNLClusterEncodingData`: a Kraft family sum and shell-budget datum.
* The V3/P9 route needs a matched, fibre-indexed class-1 charge assignment over
  `ctx.n24CarryData`: map, membership, injectivity, and per-codeword charge for
  the routed class-1 fibre.

The bridge below is the genuine V3 matched-charge bridge: if such fibre-indexed
data is supplied, it constructs the V3 minimal residual and the P9 endpoint.  The
obstruction theorems record why the existing one-step `Class1CNLInjection` field
cannot be manufactured from the factory provider alone: it implies the fixed
one-step alphabet count `|fibre_1| <= |selectedTransitions| <= 14`, while the
proved honest CNL count is only the shell-window / bounded-multiplicity shape.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## 1. The matched CNL charge datum actually needed by V3 -/

/-- The genuine fibre-indexed clean-CNL matched charge surface for a routed budget.

This is the exact data consumed by the V3 `cnlG/cnlMem/cnlInj/cnlCharge` fields:
each routed class-1 start is assigned a surviving clean-CNL transition, the
assignment is injective on the routed fibre, and the start's own window excess is
dominated by that transition's Kraft rate. -/
structure CNLMatchedChargeDataForBudget
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) where
  /-- The matched codeword assignment for class-1 starts. -/
  g : ∀ ctx : ActualFailureContext, ℕ → CNLTransition
  /-- Assigned codewords are surviving clean-CNL transitions for the shell. -/
  hmem : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
      g ctx k ∈ selectedTransitions (liftTransitionsOfShell ctx)
  /-- Distinct class-1 starts receive distinct assigned codewords. -/
  hinj : ∀ ctx : ActualFailureContext,
    ∀ k₁ ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
      ∀ k₂ ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        g ctx k₁ = g ctx k₂ → k₁ = k₂
  /-- The matched per-codeword Kraft domination against the actual carry window. -/
  hcharge : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ (2 : ℝ) ^ (-(bndHeightNatOfShell ctx (g ctx k) : ℝ))
            * (cnlShellFactorOfShell ctx : ℝ) * (ctx.shell.X : ℝ) * (cnlIjOfShell ctx : ℝ)

namespace CNLMatchedChargeDataForBudget

variable {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}

/-- Any existing `Class1CNLInjection` yields the direct matched-charge datum used by V3. -/
def ofInjection (R : Class1CNLInjection budget) : CNLMatchedChargeDataForBudget budget where
  g := R.g
  hmem := R.hmem
  hinj := R.hinj
  hcharge := R.hcharge

/-- The matched-charge datum directly closes the class-1 CNL ledger field. -/
theorem hCnlField (R : CNLMatchedChargeDataForBudget budget) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 1
        ≤ termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  fun ctx => Class1CNLChargeData.hCnl_ofShellCharge budget R.g R.hmem R.hinj R.hcharge ctx

/-- The matched one-step assignment forces the injective one-step count. -/
theorem fibre_card_le (R : CNLMatchedChargeDataForBudget budget) (ctx : ActualFailureContext) :
    (routedFibre ctx.n24CarryData (budget ctx).route 1).card
      ≤ (selectedTransitions (liftTransitionsOfShell ctx)).card :=
  Finset.card_le_card_of_injOn (R.g ctx) (R.hmem ctx) (R.hinj ctx)

/-- Consequently, the one-step matched assignment forces the fixed alphabet bound `<= 14`. -/
theorem fibre_card_le_14 (R : CNLMatchedChargeDataForBudget budget) (ctx : ActualFailureContext) :
    (routedFibre ctx.n24CarryData (budget ctx).route 1).card ≤ 14 :=
  (R.fibre_card_le ctx).trans (cnlFamily_card_le_14 ctx)

end CNLMatchedChargeDataForBudget

/-! ## 2. The multiplicity-aware CNL ledger surface -/

/-- The CNL Kraft cap associated to a shell transition. -/
abbrev cnlShellKraftCap (ctx : ActualFailureContext) (t : CNLTransition) : ℝ :=
  (2 : ℝ) ^ (-(bndHeightNatOfShell ctx t : ℝ))
    * (cnlShellFactorOfShell ctx : ℝ) * (ctx.shell.X : ℝ) * (cnlIjOfShell ctx : ℝ)

/-- Generic CNL close from a fibrewise charged estimate.

This is the multiplicity-aware replacement for the `Finset.sum_image` step in
`routedClassMass_le_termCnl_of_kraftCharge`: the routed fibre may have several
starts over the same codeword, provided the whole preimage of each codeword is
charged by that codeword's Kraft cap. -/
theorem routedClassMass_le_termCnl_of_kraftChargeMultiplicity
    {shell : FailingDyadicShell} {cPr cStar ξ X : ℝ}
    (carryData : CarryDataFromFailure shell cPr)
    (data : ClosurePhaseData cStar ξ X)
    [DecidableEq data.cnl.α]
    (route : ℕ → Fin 7) (i : Fin 7)
    (g : ℕ → data.cnl.α)
    (hmem : ∀ k ∈ routedFibre carryData route i, g k ∈ data.cnl.paths)
    (hcharged : ∀ t ∈ data.cnl.paths,
      (∑ k ∈ (routedFibre carryData route i).filter (fun k => g k = t),
          windowExcess (hitGap carryData.a) k carryData.r carryData.T)
        ≤ (2 : ℝ) ^ (-(data.cnl.c * data.cnl.BNDHeight t))
            * data.cnl.shellFactor * X * data.cnl.Ij) :
    routedClassMassOf carryData route i ≤ termCnl data := by
  let cap : data.cnl.α → ℝ :=
    fun t => (2 : ℝ) ^ (-(data.cnl.c * data.cnl.BNDHeight t))
      * data.cnl.shellFactor * X * data.cnl.Ij
  have hmass := routedClassMassOf_le_chargedArea carryData route i g data.cnl.paths cap hmem hcharged
  refine hmass.trans (le_of_eq ?_)
  have htermCnl : termCnl data
      = (∑ t ∈ data.cnl.paths, (2 : ℝ) ^ (-(data.cnl.c * data.cnl.BNDHeight t)))
          * (data.cnl.shellFactor * X * data.cnl.Ij) := by
    unfold termCnl cleanCNLKraftSum; ring
  rw [htermCnl]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- The honest multiplicity-aware clean-CNL charge surface for a routed budget.

Unlike `CNLMatchedChargeDataForBudget`, this does **not** require an injection of
all class-1 starts into the fixed one-step `CNLTransition` alphabet.  Instead it
asks for the charged preimage over each surviving transition to be bounded by
that transition's Kraft cap, exactly the `O_Q(1)`/bounded-overlap reindexing
shape needed in the deep CNL line. -/
structure CNLMultiChargeDataForBudget
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) where
  /-- The class-1 codeword assignment.  It may be many-to-one. -/
  g : ∀ ctx : ActualFailureContext, ℕ → CNLTransition
  /-- Assigned codewords are surviving clean-CNL transitions for the shell. -/
  hmem : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
      g ctx k ∈ selectedTransitions (liftTransitionsOfShell ctx)
  /-- Multiplicity-aware charged preimage bound for each surviving codeword. -/
  hcharged : ∀ ctx : ActualFailureContext,
    ∀ t ∈ selectedTransitions (liftTransitionsOfShell ctx),
      (∑ k ∈ (routedFibre ctx.n24CarryData (budget ctx).route 1).filter
          (fun k => g ctx k = t),
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T)
        ≤ cnlShellKraftCap ctx t

namespace CNLMultiChargeDataForBudget

variable {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}

/-- A one-step matched charge datum is a special case of the multiplicity-aware surface. -/
def ofMatched (R : CNLMatchedChargeDataForBudget budget) : CNLMultiChargeDataForBudget budget where
  g := R.g
  hmem := R.hmem
  hcharged := fun ctx =>
    perOutput_charged_of_injOn
      (routedFibre ctx.n24CarryData (budget ctx).route 1)
      (fun k => windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T)
      (R.g ctx)
      (selectedTransitions (liftTransitionsOfShell ctx))
      (cnlShellKraftCap ctx)
      (R.hinj ctx)
      (R.hcharge ctx)
      (fun t _ht =>
        mul_nonneg
          (mul_nonneg
            (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (cnlShellFactorOfShell ctx).2)
            ctx.shell.X_nonneg_real)
          (cnlIjOfShell ctx).2)

/-- The multiplicity-aware CNL datum directly closes the class-1 ledger field. -/
theorem hCnlField (R : CNLMultiChargeDataForBudget budget) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 1
        ≤ termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  fun ctx => by
    have hmass :
        routedClassMassOf ctx.n24CarryData (budget ctx).route 1
          ≤ ∑ t ∈ selectedTransitions (liftTransitionsOfShell ctx), cnlShellKraftCap ctx t :=
      routedClassMassOf_le_chargedArea ctx.n24CarryData (budget ctx).route 1
        (R.g ctx) (selectedTransitions (liftTransitionsOfShell ctx)) (cnlShellKraftCap ctx)
        (R.hmem ctx) (R.hcharged ctx)
    have htermCnl : termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData
        = ∑ t ∈ selectedTransitions (liftTransitionsOfShell ctx), cnlShellKraftCap ctx t := by
      rw [termCnl_eq_chargedArea]
      rw [faithfulCnlData_paths]
      exact Finset.sum_congr rfl (fun t _ => by
        unfold cnlShellKraftCap
        simp only [faithfulCnlData_c, faithfulCnlData_BNDHeight, faithfulCnlData_shellFactor,
          faithfulCnlData_Ij, one_mul])
    exact hmass.trans (le_of_eq htermCnl.symm)

/-- The provable deep-shell count shape associated with the multiplicity-aware surface. -/
theorem fibre_card_le_shellWidth_mul_family
    (R : CNLMultiChargeDataForBudget budget) (ctx : ActualFailureContext) :
    (routedFibre ctx.n24CarryData (budget ctx).route 1).card
      ≤ shellWidth ctx * (selectedTransitions (liftTransitionsOfShell ctx)).card :=
  cnl_count_le_shellWidth_mul_family ctx (budget ctx).route

end CNLMultiChargeDataForBudget

/-! ## 3. V3 bridges from the direct matched CNL charge datum -/

/-- Assemble `Erdos260MinimalResidualV3` when CNL is supplied as direct matched charge data. -/
def erdos260MinimalResidualV3_ofMatchedCNL
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection (v3Budget towerCount runChain returnCharge))
    (cnl : CNLMatchedChargeDataForBudget (v3Budget towerCount runChain returnCharge))
    (densePackCount : ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card
        ≤ (densePackMarkers (v3Budget towerCount runChain returnCharge) ctx).card)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Erdos260MinimalResidualV3 where
  towerCount := towerCount
  runChain := runChain
  returnCharge := returnCharge
  chernoffChargeOf := chernoff.chargeOf
  chernoffMaps := chernoff.hmaps
  chernoffInj := chernoff.hinj
  chernoffDom := chernoff.hdom
  cnlG := cnl.g
  cnlMem := cnl.hmem
  cnlInj := cnl.hinj
  cnlCharge := cnl.hcharge
  densePackSupport := fun ctx =>
    DensePackCoareaSupport.ofCardLe (v3Budget towerCount runChain returnCharge) ctx
      (densePackCount ctx)
  densePackG0 := densePackDyadicG0
  densePackGap :=
    densePackGap_ofContainment (v3Budget towerCount runChain returnCharge)
      (v3Budget_route towerCount runChain returnCharge) windowReach hReach hContain
  densePackScale := hScale

/-- Erdős #260 from V3 class data with CNL supplied as direct matched charge data. -/
theorem erdos260_of_classData_matchedCNL
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection (v3Budget towerCount runChain returnCharge))
    (cnl : CNLMatchedChargeDataForBudget (v3Budget towerCount runChain returnCharge))
    (densePackCount : ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card
        ≤ (densePackMarkers (v3Budget towerCount runChain returnCharge) ctx).card)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Erdos260Statement :=
  erdos260_of_minimalResidualV3
    (erdos260MinimalResidualV3_ofMatchedCNL towerCount runChain returnCharge chernoff cnl
      densePackCount windowReach hReach hContain hScale)

/-- P9/V3 residual with the CNL slot sharpened to direct matched charge data. -/
structure P9V3RunMatchedCNLResidual where
  towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx
  runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx
  returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx
  chernoff : Class0ChernoffInjection
    (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)
  cnl : CNLMatchedChargeDataForBudget
    (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)
  densePackCount : ∀ ctx : ActualFailureContext,
    (genuineDensePackStarts ctx).card
      ≤ (densePackMarkers
        (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge) ctx).card
  windowReach : ActualFailureContext → ℕ
  hReach : ∀ ctx : ActualFailureContext,
    windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card
  hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
    k + ctx.n24CarryData.r
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx
  hScale : ∀ ctx : ActualFailureContext,
    ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1

namespace P9V3RunMatchedCNLResidual

/-- Assemble the V3 minimal residual from the P9 run-leaf residual and direct matched CNL data. -/
def toMinimalResidualV3 (R : P9V3RunMatchedCNLResidual) : Erdos260MinimalResidualV3 :=
  erdos260MinimalResidualV3_ofMatchedCNL
    R.towerCount
    (p9V3RunChainOfResidual R.runResidual)
    R.returnCharge
    R.chernoff
    R.cnl
    R.densePackCount
    R.windowReach
    R.hReach
    R.hContain
    R.hScale

/-- Convert the sharpened matched-CNL residual into the ctx-pinned P9 routing residual. -/
def toP9CtxPinnedRoutingZero (R : P9V3RunMatchedCNLResidual) : P9CtxPinnedRoutingZeroResidual :=
  P9CtxPinnedRoutingZeroResidual.ofMinimalResidualV3 R.toMinimalResidualV3

/-- The P9 endpoint from direct matched CNL charge data. -/
theorem toStatement (R : P9V3RunMatchedCNLResidual) : Erdos260Statement :=
  erdos260_capstone_p9CtxPinned R.toP9CtxPinnedRoutingZero

end P9V3RunMatchedCNLResidual

/-- P9/V3 endpoint with CNL supplied as direct matched charge data. -/
theorem erdos260_p9V3_of_matchedCNL
    (R : P9V3RunMatchedCNLResidual) : Erdos260Statement :=
  R.toStatement

/-! ## 3. The one-step matched-injection obstruction -/

/-- Any `Class1CNLInjection` forces the fixed one-step alphabet count `<= 14`. -/
theorem class1CNLInjection_fibre_card_le_14
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (R : Class1CNLInjection budget) (ctx : ActualFailureContext) :
    (routedFibre ctx.n24CarryData (budget ctx).route 1).card ≤ 14 :=
  (R.fibre_card_le ctx).trans (cnlFamily_card_le_14 ctx)

/-- Therefore no one-step `Class1CNLInjection` exists on a context with more than 14 class-1 starts. -/
theorem no_class1CNLInjection_of_gt14
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (ctx : ActualFailureContext)
    (hwide : 14 < (routedFibre ctx.n24CarryData (budget ctx).route 1).card) :
    ¬ Nonempty (Class1CNLInjection budget) := by
  rintro ⟨R⟩
  have hle := class1CNLInjection_fibre_card_le_14 R ctx
  omega

/-- The same obstruction applies to the direct matched-charge datum: it still targets the one-step
`CNLTransition` alphabet. -/
theorem no_matchedCNLChargeData_of_gt14
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (ctx : ActualFailureContext)
    (hwide : 14 < (routedFibre ctx.n24CarryData (budget ctx).route 1).card) :
    ¬ Nonempty (CNLMatchedChargeDataForBudget budget) := by
  rintro ⟨R⟩
  have hle := R.fibre_card_le_14 ctx
  omega

/-- V3-specialized obstruction for the current P9 run-leaf budget. -/
theorem no_p9V3_class1CNLInjection_of_gt14
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (ctx : ActualFailureContext)
    (hwide : 14 <
      (routedFibre ctx.n24CarryData
        (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge ctx).route 1).card) :
    ¬ Nonempty (Class1CNLInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)) :=
  no_class1CNLInjection_of_gt14 ctx hwide

/-! ## 4. Machine-readable status -/

/-- Status of the V3 matched-CNL closure attempt. -/
def cnlMatchedClosureStatus : List String :=
  [ "BRIDGE PROVED: CNLMatchedChargeDataForBudget.hCnlField closes the class-1 ledger directly from matched g/hmem/hinj/hcharge.",
    "BRIDGE PROVED: CNLMultiChargeDataForBudget.hCnlField closes the class-1 ledger from a multiplicity-aware charged-preimage bound over each surviving CNL transition, without manufacturing a one-step injection.",
    "REFINED RESIDUAL: routedClassMass_le_termCnl_of_kraftChargeMultiplicity replaces the Finset.sum_image injection step by the existing J.1.8 fibrewise charged-area summation.",
    "BRIDGE PROVED: erdos260MinimalResidualV3_ofMatchedCNL assembles Erdos260MinimalResidualV3 when the CNL slot is supplied as direct matched charge data.",
    "BRIDGE PROVED: P9V3RunMatchedCNLResidual.toStatement gives the ctx-pinned P9 endpoint from the run-leaf residual plus matched CNL charge data.",
    "OBSTRUCTION PROVED: Class1CNLInjection, and even direct one-step matched data into CNLTransition, force |routedFibre_1| <= |selectedTransitions| <= 14.",
    "MISMATCH: cnlUnconditionalProvider supplies only a per-shell CNLClusterEncodingData/Kraft sum; it does not supply a ctx.n24CarryData-indexed map from the routed class-1 fibre, injectivity on that fibre, or per-start matched window-excess domination.",
    "REMAINING BLOCKER: a genuine deep CNL close needs a length-M/O_Q(1)-to-one codeword target or multiplicity-aware reindexing; the current V3 Class1CNLInjection target is the fixed one-step CNLTransition alphabet." ]

theorem cnlMatchedClosureStatus_nonempty : cnlMatchedClosureStatus ≠ [] := by
  simp [cnlMatchedClosureStatus]

#print axioms CNLMatchedChargeDataForBudget.hCnlField
#print axioms CNLMatchedChargeDataForBudget.fibre_card_le
#print axioms routedClassMass_le_termCnl_of_kraftChargeMultiplicity
#print axioms CNLMultiChargeDataForBudget.ofMatched
#print axioms CNLMultiChargeDataForBudget.hCnlField
#print axioms CNLMultiChargeDataForBudget.fibre_card_le_shellWidth_mul_family
#print axioms erdos260MinimalResidualV3_ofMatchedCNL
#print axioms erdos260_of_classData_matchedCNL
#print axioms P9V3RunMatchedCNLResidual.toMinimalResidualV3
#print axioms P9V3RunMatchedCNLResidual.toStatement
#print axioms erdos260_p9V3_of_matchedCNL
#print axioms class1CNLInjection_fibre_card_le_14
#print axioms no_class1CNLInjection_of_gt14
#print axioms no_matchedCNLChargeData_of_gt14
#print axioms no_p9V3_class1CNLInjection_of_gt14

end

end Erdos260
