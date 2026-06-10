import Erdos260.P9CtxPinnedReduction
import Erdos260.Erdos260V3ClassBundles
import Erdos260.RunLeafUnconditional

/-!
# P9 / V3 ctx-pinned closure boundary

This module records the sharp ctx-pinned P9/V3 bridge that is currently available.

The key point is that the already-closed factory providers
`chernoffProviderUnconditional`, `cnlUnconditionalProvider`, `densePackProvider`,
`returnInputUnconditional`, and `ActualFailureContext.tower` do not by themselves
construct `Erdos260MinimalResidualV3`: V3 asks for matched charge maps and
domination fields over `faithfulCapacityPhases (v3Budget ...) ctx` and
`ctx.n24CarryData`, plus the budget-defining Tower/Return/Run routed slots.

What does compose cleanly is the genuine V3 class-data surface.  This file wires that
surface through the new ctx-pinned P9 endpoint and reduces the Run input from
`RunClass5StageChain` to the sharper `RunClass5LeafResidual`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-- Build the V3 `runChain` field from the sharper Run leaf residual. -/
def p9V3RunChainOfResidual
    (runResidual : forall ctx : ActualFailureContext, RunClass5LeafResidual ctx) :
    forall ctx : ActualFailureContext, RunClass5StageChain ctx :=
  fun ctx => ((runResidual ctx).toLeaf).toChain

/-- The sharp V3-shaped residual currently sufficient for the ctx-pinned P9 route.

This is not a new analytic shortcut.  It keeps the V3 matched-charge obligations in
their native ctx-pinned/canonical-phase form and only shrinks the Run field to the
same `RunClass5LeafResidual` atom used by the compatibility capstone. -/
structure P9V3RunResidual where
  /-- Tower / class 2 active-floor count for the route that defines the V3 budget. -/
  towerCount : forall ctx : ActualFailureContext, Class2ActiveFloorCount ctx
  /-- Run / class 5, reduced to the sharp Section 26 leaf residual. -/
  runResidual : forall ctx : ActualFailureContext, RunClass5LeafResidual ctx
  /-- Return / class 4 per-slice matched charge for the V3 budget. -/
  returnCharge : forall ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx
  /-- Chernoff / class 0 matched charge injection against the canonical V3 phases. -/
  chernoff : Class0ChernoffInjection
    (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)
  /-- Clean-CNL / class 1 matched Kraft charge injection against the canonical V3 phases. -/
  cnl : Class1CNLInjection
    (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)
  /-- DensePack / class 3 K.1.1 endpoint-disjoint count for the canonical V3 budget. -/
  densePackCount : forall ctx : ActualFailureContext,
    (genuineDensePackStarts ctx).card
      <= (densePackMarkers
        (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge) ctx).card
  /-- DensePack active-window reach used to ground the dyadic gap bound. -/
  windowReach : ActualFailureContext -> Nat
  /-- The DensePack reach lies inside the support shell. -/
  hReach : forall ctx : ActualFailureContext,
    windowReach ctx + 1 <= (supportShell ctx.shell.d ctx.shell.X).card
  /-- DensePack active-window containment for the class-3 descent window. -/
  hContain : forall ctx : ActualFailureContext, forall k,
    k ∈ genuineDensePackStarts ctx ->
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx
  /-- DensePack K.1.2 active-floor calibration for the V3 unit charge. -/
  hScale : forall ctx : ActualFailureContext,
    ((ctx.n24CarryData.r : Real) + 1) * (densePackDyadicG0 ctx : Real) - ctx.n24CarryData.T <= 1

namespace P9V3RunResidual

/-- Assemble the corrected V3 minimal residual from the sharp P9/V3 run residual. -/
def toMinimalResidualV3 (R : P9V3RunResidual) : Erdos260MinimalResidualV3 :=
  erdos260MinimalResidualV3_ofClassData
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

/-- The ctx-pinned P9 routing residual obtained from the assembled V3 residual. -/
def toP9CtxPinnedRoutingZero (R : P9V3RunResidual) : P9CtxPinnedRoutingZeroResidual :=
  P9CtxPinnedRoutingZeroResidual.ofMinimalResidualV3 R.toMinimalResidualV3

/-- The ctx-pinned P9 final theorem from the sharp V3-shaped Run residual. -/
theorem toStatement (R : P9V3RunResidual) : Erdos260Statement :=
  erdos260_capstone_p9CtxPinned R.toP9CtxPinnedRoutingZero

end P9V3RunResidual

/-- P9/V3 endpoint with Run reduced to the same sharp Run atom as the compatibility capstone. -/
theorem erdos260_p9V3_of_runResidual
    (R : P9V3RunResidual) : Erdos260Statement :=
  R.toStatement

/-- Machine-readable status of the ctx-pinned P9/V3 closure attempt. -/
def p9V3ClosureStatus : List String :=
  [ "CLOSED BRIDGE: P9V3RunResidual.toMinimalResidualV3 assembles Erdos260MinimalResidualV3.",
    "CLOSED BRIDGE: P9V3RunResidual.toP9CtxPinnedRoutingZero turns that V3 residual into the ctx-pinned P9 routing residual.",
    "ENDPOINT: erdos260_p9V3_of_runResidual proves Erdos260Statement through erdos260_capstone_p9CtxPinned.",
    "RUN SHRINK: the V3 runChain field is reduced to forall ctx, RunClass5LeafResidual ctx.",
    "NOT FULLY CLOSED: closed factory providers do not construct V3 matched maps/domination fields over faithfulCapacityPhases.",
    "BLOCKERS: Tower needs Class2ActiveFloorCount; Return needs Class4ReturnPerSliceCharge; Chernoff/CNL need matched injections; DensePack needs endpoint count, containment, and scale." ]

theorem p9V3ClosureStatus_nonempty : p9V3ClosureStatus != [] := by
  simp [p9V3ClosureStatus]

#print axioms p9V3RunChainOfResidual
#print axioms P9V3RunResidual.toMinimalResidualV3
#print axioms P9V3RunResidual.toP9CtxPinnedRoutingZero
#print axioms P9V3RunResidual.toStatement
#print axioms erdos260_p9V3_of_runResidual

end

end Erdos260
