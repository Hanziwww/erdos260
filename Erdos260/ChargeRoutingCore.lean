import Erdos260.Erdos260FinalReduced
import Erdos260.ChargeMultiplierClosure

/-!
# The v5 seven-class J.1.1 charge routing, assembled for the FINAL residual surface

This module attacks the **central `routing` field** of `Erdos260FinalResidual`
(`Erdos260FinalReduced.lean`):

```
routing : ∀ ctx : ActualFailureContext,
  RoutedHighExcessChargeDataOldRes
    (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx)
    ctx.n24CarryData (oldResMass ctx)
```

This is the v5 **seven-class J.1.1 priority routing**: it partitions the high-excess
carry starts of `ctx.n24CarryData` into the seven charge classes

```
0  Chernoff / shell-paid progress      3  DensePack          6  old-residual (Ω^oldres)
1  clean-CNL Kraft tail                 4  Return / endpoint / OLC leakage
2  Tower                                5  Run / variation-drop
```

and proves the augmented charge bridge `highExcessMass ≤ ClosurePhaseMass + oldResMass`
through the proved summation skeleton
(`RoutedHighExcessChargeDataOldRes.highExcess_le_phaseMass_add_oldRes`).

## What this file CLOSES (genuinely proved, axiom-clean)

* **The routing-field assembly** `ChargeRoutingResidual.toRoutingField` — the exact
  `Erdos260FinalResidual.routing` field shape, built from the genuine routing plus the
  five per-class capacity bounds, specialised to `assembledFinalPhases …` and
  `ctx.n24CarryData`.  Composed with the sibling residuals it produces a full
  `Erdos260FinalResidual` (`ChargeRoutingResidual.toFinalResidual`) and hence
  `Erdos260Statement` (`erdos260_of_chargeRoutingResidual`).
* **The conservation collapse** `routedClassMassOf_le_highExcessMass` — every routed
  class mass is `≤` the total high-excess mass (the seven masses are nonnegative and
  sum to it, `highExcessMass_eq_sum_routedClassMassOf`).  The Phase-D1 conservation half.
* **A concrete genuine routing reusing the proved classifier** `chargeRouteOfShell` —
  the deterministic `Fin 7` routing built from the proved L.3.1 SCC-band classifier
  `towerClsOfShell` (`TowerL31I31Core.lean`); its Tower(2) and old-residual(6) fibres are
  *empty*, proved outright (`chargeRoute_routed2_zero`, `chargeRoute_routed6_zero`).  This
  is the **v4-degenerate (no old-residual leakage) routing**: it discharges `hOldRes`
  from `0 ≤ oldResMass` and folds the empty Tower fibre out of the joint TRT bound.
* **The finest reduction of the four separable per-class bounds** to per-fibre
  count×multiplier data (`ChargeRoutingFibreResidual`), via the proved
  `routedClassMassOf_le_countMultiplier` (the carry-side twin of
  `densePackMass_le_of_density`).

## What stays OPEN (the genuine deep dynamical residuals, owned by sibling workers)

The five per-class capacity bounds are **not** derivable from any proved phase budget
(`ChargeMultiplierClosure.chargeMultiplierResidual`): the budgets bound the phase *term*
`termX ≤ c⋆ξX/6`, whereas a routing multiplier bounds the routed carry *mass*
`routedClassMassOf ≤ termX` — the orthogonal J.1.1 / N.24 / I.9 *charging* direction
(Appendix L.2 / N.3.3 family/transcript dynamics).  Accordingly the five bounds are
carried as the **minimal named per-class sub-residuals**:

* `hChernoff` (class 0), `hCnl` (class 1), `hDensePack` (class 3) — the three separable
  charged classes;
* `hTRT` (classes 2+4+5) — the joint Tower+Return+Run same-threshold (N.24) bound;
* `hOldRes` (class 6) — the v5 old-residual leakage bound (Lemma L.6.4/L.6.5).

In `ChargeRoutingFibreResidual` the three separable ones (and the old-residual one) are
reduced one further step to per-fibre window-excess multipliers (K.1.2/L.20, linear in
the active floor `Y`), the J.1.1 fibre counts, and the `count·mult ≤ termX` numeric
identifications (K.4); the joint TRT remains the single N.24 same-threshold bound.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The conservation collapse for the `Fin 7` routing (Phase D1, faithful)

For *any* total `Fin 7` routing the seven routed class masses are nonnegative and sum to
the total high-excess mass (`highExcessMass_eq_sum_routedClassMassOf`), so each one is
`≤` the total.  This is the faithful J.1.1 conservation half; it holds with no dynamics. -/

/-- **Each routed class mass is `≤` the total high-excess mass.**  The seven masses are
nonnegative (`routedClassMassOf_nonneg`) and sum to the total
(`highExcessMass_eq_sum_routedClassMassOf`), so any single one is dominated by the total. -/
theorem routedClassMassOf_le_highExcessMass
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7) (i : Fin 7) :
    routedClassMassOf carryData route i
      ≤ highExcessMass (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T := by
  rw [highExcessMass_eq_sum_routedClassMassOf carryData route]
  exact Finset.single_le_sum
    (fun j _ => routedClassMassOf_nonneg carryData route j) (Finset.mem_univ i)

/-! ## 2.  The minimal per-class residual surface and the routing-field assembly

`ChargeRoutingResidual` is the smallest honest contract that produces the
`Erdos260FinalResidual.routing` field: a genuine `Fin 7` routing per failure context
together with the five per-class capacity bounds against the assembled phase terms.  The
parameters mirror exactly the other `Erdos260FinalResidual` fields the routing type
depends on. -/

/-- **The minimal v5 charge-routing residual.**

For each failure context, the genuine seven-class routing `route` plus the five per-class
capacity bounds against the *assembled* phase terms.  Each bound is exactly a field of
`RoutedHighExcessChargeDataOldRes`; this is the faithful minimal interface to the deep
J.1.1 / N.24 / L.6 charging content. -/
structure ChargeRoutingResidual
    (dirtyCM : ∀ _ctx : ActualFailureContext, ℕ)
    (dirtyWindow : ∀ ctx : ActualFailureContext, WindowRunScaleCountBound ctx (dirtyCM ctx))
    (tower : ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (returnPkg : ∀ ctx : ActualFailureContext,
      ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (run : ∀ ctx : ActualFailureContext,
      RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (oldResMass : ∀ _ctx : ActualFailureContext, ℝ) where
  /-- The genuine v5 seven-class J.1.1 routing of each high-excess carry start. -/
  route : ∀ _ctx : ActualFailureContext, ℕ → Fin 7
  /-- **Class 0 — Chernoff / shell-paid progress** (separable). -/
  hChernoff : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (route ctx) 0
      ≤ termChernoff (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
  /-- **Class 1 — clean-CNL Kraft tail** (separable). -/
  hCnl : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (route ctx) 1
      ≤ termCnl (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
  /-- **Class 3 — DensePack marker mass** (separable). -/
  hDensePack : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (route ctx) 3
      ≤ termDensePack (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
  /-- **Classes 2 + 4 + 5 — Tower + Return + Run, bounded jointly** by the N.24
  same-threshold (TRT) compression. -/
  hTRT : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (route ctx) 2
        + routedClassMassOf ctx.n24CarryData (route ctx) 4
        + routedClassMassOf ctx.n24CarryData (route ctx) 5
      ≤ termTower (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
        + termReturn (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
        + termRun (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
  /-- **Class 6 — the v5 old-residual leakage** (Lemma L.6.4 / L.6.5). -/
  hOldRes : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (route ctx) 6 ≤ oldResMass ctx

namespace ChargeRoutingResidual

variable {dirtyCM : ∀ _ctx : ActualFailureContext, ℕ}
    {dirtyWindow : ∀ ctx : ActualFailureContext, WindowRunScaleCountBound ctx (dirtyCM ctx)}
    {tower : ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ)}
    {returnPkg : ∀ ctx : ActualFailureContext,
      ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ)}
    {run : ∀ ctx : ActualFailureContext,
      RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ)}
    {oldResMass : ∀ _ctx : ActualFailureContext, ℝ}

/-- **The routing-field assembly (the central deliverable).**

From the minimal residual surface, build the exact `Erdos260FinalResidual.routing`
field: for each failure context a `RoutedHighExcessChargeDataOldRes` over the assembled
phases and the N.24 carry data, carrying the five per-class bounds.  The augmented
charge bridge `highExcessMass ≤ ClosurePhaseMass + oldResMass` then follows from the
proved summation skeleton. -/
def toRoutingField (R : ChargeRoutingResidual dirtyCM dirtyWindow tower returnPkg run oldResMass) :
    ∀ ctx : ActualFailureContext,
      RoutedHighExcessChargeDataOldRes
        (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx)
        ctx.n24CarryData (oldResMass ctx) :=
  fun ctx =>
    { route := R.route ctx
      hChernoff := R.hChernoff ctx
      hCnl := R.hCnl ctx
      hDensePack := R.hDensePack ctx
      hTRT := R.hTRT ctx
      hOldRes := R.hOldRes ctx }

/-- **The augmented charge bridge for the assembled routing.**  Re-export of the proved
summation skeleton at the constructed routing field: the high-excess mass of the N.24
carry data is dominated by the assembled phase mass plus the old-residual mass. -/
theorem highExcess_le_phaseMass_add_oldRes
    (R : ChargeRoutingResidual dirtyCM dirtyWindow tower returnPkg run oldResMass)
    (ctx : ActualFailureContext) :
    highExcessMass (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
        (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ ClosurePhaseMass
          (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
        + oldResMass ctx :=
  (R.toRoutingField ctx).highExcess_le_phaseMass_add_oldRes

end ChargeRoutingResidual

/-! ## 3.  A concrete genuine routing reusing the proved L.3.1 classifier

The seven-class routing need not be a free primitive: it can be **constructed** from the
proved L.3.1 SCC-band classifier `towerClsOfShell` of `TowerL31I31Core.lean`, which
deterministically routes each high-excess carry start to one of the five tower-exit
destinations by the canonical-gap band index of the genuine E.13 recurrent slope orbit.

We map the five destinations into the seven v5 charge classes (run → Run `5`,
non-run Return → Return `4`, DensePack → DensePack `3`, clean-CNL → CNL `1`, lower-order
remainder → Chernoff/progress `0`).  The resulting routing `chargeRouteOfShell` is a
genuine function of the actual shell geometry — never free data — and routes nothing to
the Tower(`2`) or old-residual(`6`) classes, the **v4-degenerate (no old-residual
leakage)** case in which the v5 trichotomy reduces to the dichotomy. -/

/-- The five Lemma L.3.1 tower-exit destinations mapped into the seven v5 charge classes. -/
def towerExitToFin7 : TowerExitClass → Fin 7
  | .run => 5
  | .returnPkg => 4
  | .densePack => 3
  | .cnlTail => 1
  | .other => 0

/-- **The concrete v5 seven-class routing built from the proved L.3.1 classifier.**

`chargeRouteOfShell ctx k` routes the high-excess carry start `k` by the genuine
canonical-gap band index `towerClsOfShell ctx k` of the shell's recurrent slope orbit,
through `towerExitToFin7`.  A deterministic function of the actual shell — not free data. -/
def chargeRouteOfShell (ctx : ActualFailureContext) : ℕ → Fin 7 :=
  fun k => towerExitToFin7 (towerClsOfShell ctx k)

/-- The concrete routing never assigns the Tower class `2` (the L.3.1 destinations are
charged to where they *exit*; staying-in-tower carries no routed start). -/
theorem chargeRouteOfShell_ne_two (ctx : ActualFailureContext) (k : ℕ) :
    chargeRouteOfShell ctx k ≠ 2 := by
  unfold chargeRouteOfShell towerExitToFin7
  cases towerClsOfShell ctx k <;> decide

/-- The concrete routing never assigns the old-residual class `6` (the v4-degenerate
no-leakage case). -/
theorem chargeRouteOfShell_ne_six (ctx : ActualFailureContext) (k : ℕ) :
    chargeRouteOfShell ctx k ≠ 6 := by
  unfold chargeRouteOfShell towerExitToFin7
  cases towerClsOfShell ctx k <;> decide

/-- **The Tower(`2`) routed mass of the concrete routing is `0`** (its fibre is empty). -/
theorem chargeRoute_routed2_zero (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (chargeRouteOfShell ctx) 2 = 0 := by
  rw [routedClassMassOf_eq_sum_fibre]
  have hempty : routedFibre ctx.n24CarryData (chargeRouteOfShell ctx) 2 = ∅ :=
    Finset.filter_false_of_mem (fun k _ => chargeRouteOfShell_ne_two ctx k)
  rw [hempty]; simp

/-- **The old-residual(`6`) routed mass of the concrete routing is `0`** (its fibre is empty). -/
theorem chargeRoute_routed6_zero (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (chargeRouteOfShell ctx) 6 = 0 := by
  rw [routedClassMassOf_eq_sum_fibre]
  have hempty : routedFibre ctx.n24CarryData (chargeRouteOfShell ctx) 6 = ∅ :=
    Finset.filter_false_of_mem (fun k _ => chargeRouteOfShell_ne_six ctx k)
  rw [hempty]; simp

/-- **The routing field built from the concrete L.3.1 routing (v4-degenerate case).**

With the empty Tower(`2`) and old-residual(`6`) fibres, the joint TRT bound only needs
the Return(`4`)+Run(`5`) masses, and the old-residual bound is `0 ≤ oldResMass`.  The
three separable bounds (Chernoff/CNL/DensePack) and the Return+Run joint bound remain the
genuine residuals. -/
def towerClsRoutingField
    (dirtyCM : ∀ _ctx : ActualFailureContext, ℕ)
    (dirtyWindow : ∀ ctx : ActualFailureContext, WindowRunScaleCountBound ctx (dirtyCM ctx))
    (tower : ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (returnPkg : ∀ ctx : ActualFailureContext,
      ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (run : ∀ ctx : ActualFailureContext,
      RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (oldResMass : ∀ _ctx : ActualFailureContext, ℝ)
    (hOldNonneg : ∀ ctx : ActualFailureContext, 0 ≤ oldResMass ctx)
    (hChernoff : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (chargeRouteOfShell ctx) 0
        ≤ termChernoff (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData)
    (hCnl : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (chargeRouteOfShell ctx) 1
        ≤ termCnl (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData)
    (hDensePack : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (chargeRouteOfShell ctx) 3
        ≤ termDensePack (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData)
    (hReturnRun : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (chargeRouteOfShell ctx) 4
          + routedClassMassOf ctx.n24CarryData (chargeRouteOfShell ctx) 5
        ≤ termTower (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
          + termReturn (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
          + termRun (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData) :
    ChargeRoutingResidual dirtyCM dirtyWindow tower returnPkg run oldResMass where
  route := chargeRouteOfShell
  hChernoff := hChernoff
  hCnl := hCnl
  hDensePack := hDensePack
  hTRT := fun ctx => by
    have h2 := chargeRoute_routed2_zero ctx
    have hRR := hReturnRun ctx
    linarith [h2, hRR]
  hOldRes := fun ctx => by
    have h6 := chargeRoute_routed6_zero ctx
    rw [h6]; exact hOldNonneg ctx

/-! ## 4.  The finest reduction: per-fibre count×multiplier residual

The three separable per-class bounds (and the old-residual one) are reduced one further
step to the manuscript's per-fibre **count×multiplier** mechanism — a per-fibre
window-excess bound (the K.1.2/L.20 residual multiplier, linear in the active floor `Y`),
the J.1.1 fibre count, and the numeric identification `count·mult ≤ termX` — via the
proved `routedClassMassOf_le_countMultiplier`.  The joint Tower+Return+Run class stays the
single N.24 same-threshold bound (it is never separated). -/

/-- **The count×multiplier v5 charge-routing residual.**

Each separable class (`0`,`1`,`3`) and the old-residual class (`6`) is presented at its
finest manuscript granularity: a per-fibre window-excess multiplier, a fibre count, the
nonnegativity of the multiplier, and the `count·mult ≤ termX` identification.  The joint
Tower+Return+Run class (`2`+`4`+`5`) is the single N.24 same-threshold bound. -/
structure ChargeRoutingFibreResidual
    (dirtyCM : ∀ _ctx : ActualFailureContext, ℕ)
    (dirtyWindow : ∀ ctx : ActualFailureContext, WindowRunScaleCountBound ctx (dirtyCM ctx))
    (tower : ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (returnPkg : ∀ ctx : ActualFailureContext,
      ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (run : ∀ ctx : ActualFailureContext,
      RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (oldResMass : ∀ _ctx : ActualFailureContext, ℝ) where
  /-- The genuine v5 seven-class routing. -/
  route : ∀ _ctx : ActualFailureContext, ℕ → Fin 7
  -- class 0 (Chernoff)
  multChernoff : ∀ _ctx : ActualFailureContext, ℝ
  countChernoff : ∀ _ctx : ActualFailureContext, ℝ
  hpoint0 : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (route ctx) 0,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multChernoff ctx
  hnn0 : ∀ ctx : ActualFailureContext, 0 ≤ multChernoff ctx
  hcard0 : ∀ ctx : ActualFailureContext,
    ((routedFibre ctx.n24CarryData (route ctx) 0).card : ℝ) ≤ countChernoff ctx
  hbud0 : ∀ ctx : ActualFailureContext,
    countChernoff ctx * multChernoff ctx
      ≤ termChernoff (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
  -- class 1 (clean-CNL)
  multCnl : ∀ _ctx : ActualFailureContext, ℝ
  countCnl : ∀ _ctx : ActualFailureContext, ℝ
  hpoint1 : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (route ctx) 1,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multCnl ctx
  hnn1 : ∀ ctx : ActualFailureContext, 0 ≤ multCnl ctx
  hcard1 : ∀ ctx : ActualFailureContext,
    ((routedFibre ctx.n24CarryData (route ctx) 1).card : ℝ) ≤ countCnl ctx
  hbud1 : ∀ ctx : ActualFailureContext,
    countCnl ctx * multCnl ctx
      ≤ termCnl (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
  -- class 3 (DensePack)
  multDensePack : ∀ _ctx : ActualFailureContext, ℝ
  countDensePack : ∀ _ctx : ActualFailureContext, ℝ
  hpoint3 : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (route ctx) 3,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multDensePack ctx
  hnn3 : ∀ ctx : ActualFailureContext, 0 ≤ multDensePack ctx
  hcard3 : ∀ ctx : ActualFailureContext,
    ((routedFibre ctx.n24CarryData (route ctx) 3).card : ℝ) ≤ countDensePack ctx
  hbud3 : ∀ ctx : ActualFailureContext,
    countDensePack ctx * multDensePack ctx
      ≤ termDensePack (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
  -- classes 2 + 4 + 5 (joint TRT, N.24 same-threshold)
  hTRT : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (route ctx) 2
        + routedClassMassOf ctx.n24CarryData (route ctx) 4
        + routedClassMassOf ctx.n24CarryData (route ctx) 5
      ≤ termTower (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
        + termReturn (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
        + termRun (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
  -- class 6 (old-residual)
  multOldRes : ∀ _ctx : ActualFailureContext, ℝ
  countOldRes : ∀ _ctx : ActualFailureContext, ℝ
  hpoint6 : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (route ctx) 6,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multOldRes ctx
  hnn6 : ∀ ctx : ActualFailureContext, 0 ≤ multOldRes ctx
  hcard6 : ∀ ctx : ActualFailureContext,
    ((routedFibre ctx.n24CarryData (route ctx) 6).card : ℝ) ≤ countOldRes ctx
  hbud6 : ∀ ctx : ActualFailureContext,
    countOldRes ctx * multOldRes ctx ≤ oldResMass ctx

namespace ChargeRoutingFibreResidual

variable {dirtyCM : ∀ _ctx : ActualFailureContext, ℕ}
    {dirtyWindow : ∀ ctx : ActualFailureContext, WindowRunScaleCountBound ctx (dirtyCM ctx)}
    {tower : ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ)}
    {returnPkg : ∀ ctx : ActualFailureContext,
      ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ)}
    {run : ∀ ctx : ActualFailureContext,
      RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ)}
    {oldResMass : ∀ _ctx : ActualFailureContext, ℝ}

/-- **Discharge the separable per-class bounds via count×multiplier.**

Each separable per-class capacity bound is derived from the per-fibre data through the
proved `routedClassMassOf_le_countMultiplier` chained with the `count·mult ≤ termX`
identification — yielding a `ChargeRoutingResidual`. -/
def toChargeRoutingResidual
    (R : ChargeRoutingFibreResidual dirtyCM dirtyWindow tower returnPkg run oldResMass) :
    ChargeRoutingResidual dirtyCM dirtyWindow tower returnPkg run oldResMass where
  route := R.route
  hChernoff := fun ctx =>
    (routedClassMassOf_le_countMultiplier ctx.n24CarryData (R.route ctx) 0
      (R.hpoint0 ctx) (R.hnn0 ctx) (R.hcard0 ctx)).trans (R.hbud0 ctx)
  hCnl := fun ctx =>
    (routedClassMassOf_le_countMultiplier ctx.n24CarryData (R.route ctx) 1
      (R.hpoint1 ctx) (R.hnn1 ctx) (R.hcard1 ctx)).trans (R.hbud1 ctx)
  hDensePack := fun ctx =>
    (routedClassMassOf_le_countMultiplier ctx.n24CarryData (R.route ctx) 3
      (R.hpoint3 ctx) (R.hnn3 ctx) (R.hcard3 ctx)).trans (R.hbud3 ctx)
  hTRT := R.hTRT
  hOldRes := fun ctx =>
    (routedClassMassOf_le_countMultiplier ctx.n24CarryData (R.route ctx) 6
      (R.hpoint6 ctx) (R.hnn6 ctx) (R.hcard6 ctx)).trans (R.hbud6 ctx)

/-- **The routing field built from the finest per-fibre residual.** -/
def toRoutingField
    (R : ChargeRoutingFibreResidual dirtyCM dirtyWindow tower returnPkg run oldResMass) :
    ∀ ctx : ActualFailureContext,
      RoutedHighExcessChargeDataOldRes
        (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx)
        ctx.n24CarryData (oldResMass ctx) :=
  R.toChargeRoutingResidual.toRoutingField

end ChargeRoutingFibreResidual

/-! ### The joint Tower+Return+Run class reduced to the proved N.3.1 compression

The joint TRT bound `hTRT` is itself reducible one step further, to the manuscript's
Lemma N.3.1 *same-threshold compression* (the proved `AppendixN.TerminalOutputData.compression`,
re-exported by `routedTRT_le_packageTerms_fin7`).  The constructor below builds the
`ChargeRoutingResidual` taking the three separable bounds directly and the joint TRT bound
in its compression form: the J.1.2 / N.1.0 routing-onto-output input `hRouteToOutput` and
the N.3.3 / N.24 absorption input `hAbsorb`.  The same-threshold output family
`comp ctx : AppendixN.TerminalOutputData β σ` ranges over a fixed output type `β`/`σ`
(uniform across failure contexts, the manuscript terminal-output alphabet). -/

/-- **The charge-routing residual with the joint TRT class reduced via N.3.1 compression.**

The three separable bounds (classes `0`,`1`,`3`) and the old-residual bound (class `6`) are
supplied directly; the joint Tower+Return+Run bound is derived from the proved Lemma N.3.1
compression `routedTRT_le_packageTerms_fin7` out of the routing input `hRouteToOutput` and
the absorption input `hAbsorb`. -/
def chargeRoutingResidual_ofCompression
    {β σ : Type*} [DecidableEq σ]
    (dirtyCM : ∀ _ctx : ActualFailureContext, ℕ)
    (dirtyWindow : ∀ ctx : ActualFailureContext, WindowRunScaleCountBound ctx (dirtyCM ctx))
    (tower : ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (returnPkg : ∀ ctx : ActualFailureContext,
      ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (run : ∀ ctx : ActualFailureContext,
      RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (oldResMass : ∀ _ctx : ActualFailureContext, ℝ)
    (route : ∀ _ctx : ActualFailureContext, ℕ → Fin 7)
    (comp : ∀ _ctx : ActualFailureContext, AppendixN.TerminalOutputData β σ)
    (hChernoff : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (route ctx) 0
        ≤ termChernoff (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData)
    (hCnl : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (route ctx) 1
        ≤ termCnl (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData)
    (hDensePack : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (route ctx) 3
        ≤ termDensePack (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData)
    (hRouteToOutput : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (route ctx) 2
          + routedClassMassOf ctx.n24CarryData (route ctx) 4
          + routedClassMassOf ctx.n24CarryData (route ctx) 5
        ≤ ∑ b ∈ (comp ctx).branches, (comp ctx).wtO b)
    (hAbsorb : ∀ ctx : ActualFailureContext,
      (comp ctx).CQ * ((comp ctx).YO * ∑ ζ ∈ (comp ctx).ground, (comp ctx).fibreMass ζ)
        ≤ termTower (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
          + termReturn (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
          + termRun (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData)
    (hOldRes : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (route ctx) 6 ≤ oldResMass ctx) :
    ChargeRoutingResidual dirtyCM dirtyWindow tower returnPkg run oldResMass where
  route := route
  hChernoff := hChernoff
  hCnl := hCnl
  hDensePack := hDensePack
  hTRT := fun ctx =>
    routedTRT_le_packageTerms_fin7 (comp ctx)
      (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx)
      ctx.n24CarryData (route ctx) (hRouteToOutput ctx) (hAbsorb ctx)
  hOldRes := hOldRes

/-! ## 5.  Capstone — the routing field plugs into `Erdos260FinalResidual`

The routing field is the central one of the ten genuine fields of
`Erdos260FinalResidual`.  Bundled with the sibling residuals (the three phase-capacity
packages, the K.2.5 dirty window count, the v5 old-residual mass + its L.6.5 smallness,
and the "choose `c_*` last" constant condition) it produces a full
`Erdos260FinalResidual` and hence `Erdos260Statement` via the proved spine
`erdos260_final_reduced`. -/

namespace ChargeRoutingResidual

variable {dirtyCM : ∀ _ctx : ActualFailureContext, ℕ}
    {dirtyWindow : ∀ ctx : ActualFailureContext, WindowRunScaleCountBound ctx (dirtyCM ctx)}
    {tower : ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ)}
    {returnPkg : ∀ ctx : ActualFailureContext,
      ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ)}
    {run : ∀ ctx : ActualFailureContext,
      RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ)}
    {oldResMass : ∀ _ctx : ActualFailureContext, ℝ}

/-- **Assemble a full `Erdos260FinalResidual` from the charge routing plus the sibling
residuals.**  Confirms the routing-field type matches exactly: it is consumed as the
`.routing` field with no coercion. -/
def toFinalResidual
    (R : ChargeRoutingResidual dirtyCM dirtyWindow tower returnPkg run oldResMass)
    (oldResConst : ∀ _ctx : ActualFailureContext, ℝ)
    (oldResSmall : ∀ ctx : ActualFailureContext,
      oldResMass ctx ≤ oldResConst ctx * (ctx.shell.X : ℝ))
    (constCond : ∀ ctx : ActualFailureContext,
      erdos260Constants.cStar * erdos260Constants.ξ + oldResConst ctx
        < erdos260Constants.cPr) :
    Erdos260FinalResidual where
  dirtyCM := dirtyCM
  dirtyWindow := dirtyWindow
  tower := tower
  returnPkg := returnPkg
  run := run
  oldResMass := oldResMass
  routing := R.toRoutingField
  oldResConst := oldResConst
  oldResSmall := oldResSmall
  constCond := constCond

/-- **Erdős #260 from the v5 seven-class charge routing.**  The constructed routing field,
plus the sibling residuals, drives the proved final spine `erdos260_final_reduced`. -/
theorem erdos260_of_chargeRoutingResidual
    (R : ChargeRoutingResidual dirtyCM dirtyWindow tower returnPkg run oldResMass)
    (oldResConst : ∀ _ctx : ActualFailureContext, ℝ)
    (oldResSmall : ∀ ctx : ActualFailureContext,
      oldResMass ctx ≤ oldResConst ctx * (ctx.shell.X : ℝ))
    (constCond : ∀ ctx : ActualFailureContext,
      erdos260Constants.cStar * erdos260Constants.ξ + oldResConst ctx
        < erdos260Constants.cPr) :
    Erdos260Statement :=
  erdos260_final_reduced (R.toFinalResidual oldResConst oldResSmall constCond)

end ChargeRoutingResidual

/-! ## 6.  Honest residual inventory -/

/-- The precise status of the v5 seven-class routing after this module. -/
def chargeRoutingCoreResiduals : List String :=
  [ "CLOSED (routing-field assembly) — ChargeRoutingResidual.toRoutingField: the exact " ++
      "Erdos260FinalResidual.routing field is built from the genuine Fin 7 routing plus the five " ++
      "per-class bounds, specialised to assembledFinalPhases and ctx.n24CarryData. " ++
      "ChargeRoutingResidual.toFinalResidual / erdos260_of_chargeRoutingResidual confirm it plugs " ++
      "into the final residual surface and drives erdos260_final_reduced.",
    "CLOSED (conservation collapse) — routedClassMassOf_le_highExcessMass: every routed class mass " ++
      "is ≤ the total high-excess mass (nonneg + highExcessMass_eq_sum_routedClassMassOf).",
    "CLOSED (concrete routing, v4-degenerate) — chargeRouteOfShell: the deterministic Fin 7 routing " ++
      "built from the proved L.3.1 SCC-band classifier towerClsOfShell; Tower(2) and old-residual(6) " ++
      "fibres are PROVED empty (chargeRoute_routed2_zero/_routed6_zero), so towerClsRoutingField " ++
      "discharges hOldRes from 0 ≤ oldResMass and folds the empty Tower fibre out of the joint TRT.",
    "REDUCED (separable classes 0/1/3 and old-residual 6) — ChargeRoutingFibreResidual: each is " ++
      "reduced to per-fibre count×multiplier data (K.1.2/L.20 multiplier linear in Y, J.1.1 fibre " ++
      "count, and the count·mult ≤ termX identification) via the proved " ++
      "routedClassMassOf_le_countMultiplier. NOT closed: the identification is the genuine charging.",
    "REDUCED (joint Tower+Return+Run class 2+4+5) — chargeRoutingResidual_ofCompression: the joint " ++
      "TRT bound is reduced to the proved Lemma N.3.1 same-threshold compression " ++
      "(routedTRT_le_packageTerms_fin7) out of the routing input hRouteToOutput (J.1.2/N.1.0) and " ++
      "the absorption input hAbsorb (N.3.3/N.24). NOT closed: those two are the genuine charging.",
    "OPEN (the five per-class capacity bounds) — hChernoff/hCnl/hDensePack (separable), hTRT (joint " ++
      "Tower+Return+Run N.24 same-threshold), hOldRes (L.6.4/L.6.5). These bound the routed carry " ++
      "MASS by the assembled phase TERM — the orthogonal J.1.1/N.24/I.9 charging direction, NOT " ++
      "derivable from any proved phase budget (ChargeMultiplierClosure.chargeMultiplierResidual). " ++
      "They are the deep Appendix L.2/N.3.3 family/transcript dynamics owned by the sibling phase " ++
      "and old-residual workers, carried here as the minimal named per-class sub-residuals." ]

theorem chargeRoutingCoreResiduals_nonempty : chargeRoutingCoreResiduals ≠ [] := by
  simp [chargeRoutingCoreResiduals]

/-! ## 7.  Axiom-cleanliness audit -/

#print axioms routedClassMassOf_le_highExcessMass
#print axioms ChargeRoutingResidual.toRoutingField
#print axioms ChargeRoutingResidual.highExcess_le_phaseMass_add_oldRes
#print axioms chargeRouteOfShell
#print axioms chargeRoute_routed2_zero
#print axioms chargeRoute_routed6_zero
#print axioms towerClsRoutingField
#print axioms ChargeRoutingFibreResidual.toRoutingField
#print axioms chargeRoutingResidual_ofCompression
#print axioms ChargeRoutingResidual.toFinalResidual
#print axioms ChargeRoutingResidual.erdos260_of_chargeRoutingResidual

end

end Erdos260
