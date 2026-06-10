import Erdos260.HighExcessRoutingUnconditional
import Erdos260.Erdos260UnconditionalSeedClosureV3
import Erdos260.UnconditionalTheorem

/-!
# P9 ctx-pinned reduction

This module records the next P9 API step: a high-excess routing residual pinned to
`ActualFailureContext`, `ctx.n24CarryData`, and the canonical faithful-capacity phases
`faithfulCapacityPhases budget ctx`.

The point is deliberately not to transport V3 matched-charge closers to the old universal
`HighExcessRoutingResidualProvider`, whose contract ranges over arbitrary `phases` and
arbitrary `carryData`.  Instead, the residual below is consumed directly by final endpoints
whose phase package is the canonical one.
-/

namespace Erdos260

open Finset

noncomputable section

/-- The ctx-pinned ledger residual for P9.

All five ledger bounds are pinned to the canonical data used by the charge-reduced
endpoint: the routed budget, `ctx.n24CarryData`, and
`faithfulCapacityPhases budget ctx`. -/
structure P9CtxPinnedLedgerResidual where
  /-- The shared seven-class routed budget and the class 2/4/5 capacity slots. -/
  budget : forall ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx
  /-- Class 0, Chernoff/shell-paid progress, against the canonical faithful phases. -/
  hChernoff : forall ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 0
      <= termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData
  /-- Class 1, clean-CNL Kraft tail, against the canonical faithful phases. -/
  hCnl : forall ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 1
      <= termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData
  /-- Class 3, DensePack marker mass, against the canonical faithful phases. -/
  hDensePack : forall ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 3
      <= termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData
  /-- Classes 2+4+5, Tower+Return+Run, bounded jointly by N.24 TRT. -/
  hTRT : forall ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 2
        + routedClassMassOf ctx.n24CarryData (budget ctx).route 4
        + routedClassMassOf ctx.n24CarryData (budget ctx).route 5
      <= termTower (faithfulCapacityPhases budget ctx).toClosurePhaseData
        + termReturn (faithfulCapacityPhases budget ctx).toClosurePhaseData
        + termRun (faithfulCapacityPhases budget ctx).toClosurePhaseData
  /-- Class 6, the old-residual leakage class, bounded by the genuine L.6.4 branch mass. -/
  hOldRes : forall ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 6
      <= ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k

namespace P9CtxPinnedLedgerResidual

/-- The ctx-pinned P9 ledger residual is exactly the input surface of the existing
charge-reduced final endpoint after L.6.5 has been closed. -/
theorem toStatement (R : P9CtxPinnedLedgerResidual) : Erdos260Statement :=
  erdos260_charge_reduced_of_routing R.budget R.hChernoff R.hCnl R.hDensePack
    R.hTRT R.hOldRes

end P9CtxPinnedLedgerResidual

/-- Final endpoint from the ctx-pinned P9 ledger residual. -/
theorem erdos260_of_p9CtxPinnedLedger
    (R : P9CtxPinnedLedgerResidual) : Erdos260Statement :=
  R.toStatement

/-- A sharper routed form: per context, a genuine seven-class old-residual routing with
`oldResMass = 0`, pinned to `faithfulCapacityPhases budget ctx` and `ctx.n24CarryData`.

The `route_eq` field ties the routed data to the budget route; without it the routed package
would not necessarily be the one whose class 2/4/5 capacity slots define the faithful phases. -/
structure P9CtxPinnedRoutingZeroResidual where
  /-- The shared seven-class routed budget and the class 2/4/5 capacity slots. -/
  budget : forall ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx
  /-- The per-context canonical seven-class routing, with the old-residual class empty. -/
  routingZero : forall ctx : ActualFailureContext,
    RoutedHighExcessChargeDataOldRes (faithfulCapacityPhases budget ctx) ctx.n24CarryData 0
  /-- The route inside `routingZero` is the route whose capacity slots define `budget`. -/
  route_eq : forall ctx : ActualFailureContext, (routingZero ctx).route = (budget ctx).route

namespace P9CtxPinnedRoutingZeroResidual

/-- Forget the routed package to the five ctx-pinned ledger bounds. -/
def toLedger (R : P9CtxPinnedRoutingZeroResidual) : P9CtxPinnedLedgerResidual where
  budget := R.budget
  hChernoff := fun ctx => by
    simpa [R.route_eq ctx] using (R.routingZero ctx).hChernoff
  hCnl := fun ctx => by
    simpa [R.route_eq ctx] using (R.routingZero ctx).hCnl
  hDensePack := fun ctx => by
    simpa [R.route_eq ctx] using (R.routingZero ctx).hDensePack
  hTRT := fun ctx => by
    simpa [R.route_eq ctx] using (R.routingZero ctx).hTRT
  hOldRes := fun ctx => by
    have h0 : routedClassMassOf ctx.n24CarryData (R.budget ctx).route 6 <= (0 : Real) := by
      simpa [R.route_eq ctx] using (R.routingZero ctx).hOldRes
    have hnonneg : 0 <= ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k :=
      oldResL65_branchMass_nonneg ctx
    exact le_trans h0 hnonneg

/-- The modified actual-assembly bridge for the ctx-pinned P9 route.

This deliberately uses the canonical `faithfulCapacityPhases R.budget ctx` and
`ctx.n24CarryData`, so no transport to the older capstone's arbitrary phase/carry surface is
needed. -/
def toActualInputs (R : P9CtxPinnedRoutingZeroResidual) : GlobalAssemblyActualInputs where
  carryData := fun ctx => ctx.n24CarryData
  chernoff := fun ctx => (faithfulCapacityPhases R.budget ctx).chernoff
  cnl := fun ctx => (faithfulCapacityPhases R.budget ctx).cnl
  densePack := fun ctx => (faithfulCapacityPhases R.budget ctx).densePack
  tower := fun ctx => (faithfulCapacityPhases R.budget ctx).tower
  returnPkg := fun ctx => (faithfulCapacityPhases R.budget ctx).returnPkg
  run := fun ctx => (faithfulCapacityPhases R.budget ctx).run
  highExcessCharge := fun ctx => by
    change HighExcessChargeData (faithfulCapacityPhases R.budget ctx) ctx.n24CarryData
    exact (routingZeroToShell (R.routingZero ctx)).toHighExcessChargeData

/-- Final endpoint from the direct ctx-pinned routed P9 residual, through actual assembly. -/
theorem toStatement (R : P9CtxPinnedRoutingZeroResidual) : Erdos260Statement :=
  erdos260_final_actual R.toActualInputs

/-- The same final endpoint through the ledger bridge. -/
theorem toStatement_viaLedger (R : P9CtxPinnedRoutingZeroResidual) : Erdos260Statement :=
  R.toLedger.toStatement

end P9CtxPinnedRoutingZeroResidual

/-- Modified capstone endpoint consuming a ctx-pinned P9 routing residual directly. -/
theorem erdos260_capstone_p9CtxPinned
    (R : P9CtxPinnedRoutingZeroResidual) : Erdos260Statement :=
  R.toStatement

namespace P9CtxPinnedLedgerResidual

/-- The V3 matched-charge residual discharges the ctx-pinned ledger residual completely. -/
def ofMinimalResidualV3 (R : Erdos260MinimalResidualV3) : P9CtxPinnedLedgerResidual where
  budget := R.budget
  hChernoff := R.hChernoffField
  hCnl := R.hCnlField
  hDensePack := R.hDensePackField
  hTRT := seedHTRT R.budget
  hOldRes := R.hOldResField

end P9CtxPinnedLedgerResidual

namespace P9CtxPinnedRoutingZeroResidual

/-- The V3 matched-charge residual also gives the sharper `oldResMass = 0` routed form.

Here the class-6 vacancy is genuine: `v3Budget` routes by `genuineChargeRoute`, and
`genuineChargeRoute_routed6_zero` proves the old-residual fibre carries no routed mass. -/
def ofMinimalResidualV3 (R : Erdos260MinimalResidualV3) :
    P9CtxPinnedRoutingZeroResidual where
  budget := R.budget
  routingZero := fun ctx =>
    { route := (R.budget ctx).route
      hChernoff := R.hChernoffField ctx
      hCnl := R.hCnlField ctx
      hDensePack := R.hDensePackField ctx
      hTRT := seedHTRT R.budget ctx
      hOldRes := by
        simpa [Erdos260MinimalResidualV3.budget,
          v3Budget_route R.towerCount R.runChain R.returnCharge ctx]
          using (le_of_eq (genuineChargeRoute_routed6_zero ctx)) }
  route_eq := fun _ctx => rfl

end P9CtxPinnedRoutingZeroResidual

/-- V3 proves `Erdos260Statement` through the new ctx-pinned routed P9 API. -/
theorem erdos260_of_minimalResidualV3_via_p9CtxPinned
    (R : Erdos260MinimalResidualV3) : Erdos260Statement :=
  erdos260_capstone_p9CtxPinned (P9CtxPinnedRoutingZeroResidual.ofMinimalResidualV3 R)

/-- Machine-readable status for the ctx-pinned P9 shrink. -/
def p9CtxPinnedReductionStatus : List String :=
  [ "NEW API: P9CtxPinnedLedgerResidual carries the five per-context ledger bounds over " ++
      "budget ctx, ctx.n24CarryData, and faithfulCapacityPhases budget ctx.",
    "SHARPER API: P9CtxPinnedRoutingZeroResidual carries direct RoutedHighExcessChargeDataOldRes " ++
      "for faithfulCapacityPhases budget ctx and ctx.n24CarryData, with route_eq tying it to budget.",
    "FINAL BRIDGE: erdos260_capstone_p9CtxPinned consumes the ctx-pinned routed residual directly " ++
      "through GlobalAssemblyActualInputs using the canonical phases/carry.",
    "V3 REUSE: Erdos260MinimalResidualV3 discharges Chernoff, CNL, DensePack, joint TRT, and class-6 " ++
      "old-residual vacancy for the ctx-pinned residual.",
    "BLOCKER FOR OLD CAPSTONE: no transport is provided from faithfulCapacityPhases budget ctx / " ++
      "ctx.n24CarryData to Erdos260CapstoneResidual.capPhases / ctx.carryData or to arbitrary " ++
      "HighExcessRoutingResidualProvider phases/carryData." ]

theorem p9CtxPinnedReductionStatus_nonempty :
    p9CtxPinnedReductionStatus != [] := by
  simp [p9CtxPinnedReductionStatus]

#print axioms P9CtxPinnedLedgerResidual.toStatement
#print axioms erdos260_of_p9CtxPinnedLedger
#print axioms P9CtxPinnedRoutingZeroResidual.toLedger
#print axioms P9CtxPinnedRoutingZeroResidual.toActualInputs
#print axioms P9CtxPinnedRoutingZeroResidual.toStatement
#print axioms erdos260_capstone_p9CtxPinned
#print axioms P9CtxPinnedLedgerResidual.ofMinimalResidualV3
#print axioms P9CtxPinnedRoutingZeroResidual.ofMinimalResidualV3
#print axioms erdos260_of_minimalResidualV3_via_p9CtxPinned

end

end Erdos260
