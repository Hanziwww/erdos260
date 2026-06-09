import Erdos260.ChargeRoutingCore
import Erdos260.RunL4I52Core
import Erdos260.ReturnCountsCore
import Erdos260.TowerL31I31Core
import Erdos260.PhaseCapacityCore

/-!
# The genuine J.1.1 / I.1 first-obstruction charge routing

`ChargeRoutingCore.lean` builds the concrete routing `chargeRouteOfShell`, which routes
each high-excess carry start through the **single** proved L.3.1 SCC-band classifier
`towerClsOfShell`.  That routing is the *v4-degenerate* case: both its Tower(`2`) and
old-residual(`6`) fibres are forced empty, so the v5 trichotomy collapses to a dichotomy.

This module replaces the single-classifier route by the **genuine first-obstruction
priority composition of the three proved classifiers**

* `towerClsOfShell  : … → TowerExitClass` (L.3.1 SCC canonical-gap band),
* `runClsOfShell    : … → Fin 4`         (L.4 / I.5.2 run window-excess band),
* `returnCls        : … → Fin 3`         (Return / OLC window-excess band),

scanned in the proved J.1.1 class-priority order `3 ▸ 0 ▸ 5 ▸ 4 ▸ 2 ▸ 1`
(matching `CarryRouting.j11Scan`, with the old-residual class `6` omitted — see below),
so that **each high-excess start is assigned to its genuine first exposed obstruction**,
not a free route.

## Genuine content (axiom-clean, no `sorry`/`axiom`/`admit`)

* `genuineChargeRoute` — the first-obstruction priority cascade composing all three proved
  classifiers.  The primary destination is the L.3.1 tower-exit; the `cnlTail` catch-all is
  genuinely refined by the run/return window-excess bands (large run → Run `5`, long return
  → Return `4`, semiperiodic recurrence → Tower `2`, bounded → CleanCNL `1`).
* The full per-class **fibre-membership characterisations**
  `genuineChargeRoute_eq_*_iff` — `genuineChargeRoute ctx k = i ↔ <classifier condition>`,
  i.e. the genuine first-obstruction assignment proved per class.
* `genuineChargeRoute_routed6_zero` — the old-residual(`6`) fibre is **proved empty**.  This
  is *honest, not degenerate*: none of the three available proved classifiers detects
  old-residual leakage (that is the separate Lemma L.6 worker), so this genuine routing is
  the *no-old-residual-leakage* case.  Unlike `chargeRouteOfShell`, the Tower(`2`) fibre is
  **not** forced empty — it is genuinely populated by the semiperiodic return band — so the
  joint Tower+Return+Run class stays the real N.24 same-threshold bound.
* `genuineChargeRoutingResidual` — assembles a `ChargeRoutingResidual` (and hence the exact
  `Erdos260FinalResidual.routing` field, via the proved `toRoutingField`) from the genuine
  route plus the four genuine per-class capacity bounds (Chernoff/CNL/DensePack separable,
  joint TRT), discharging the old-residual bound from the proved empty `6`-fibre.
* `genuineSeparatedPhaseRoutedBudget` — the genuine route packaged into a
  `SeparatedPhaseRoutedBudget` from its three routed-fraction slot bounds.

## What stays a named residual

The per-class capacity bounds (`hChernoff`, `hCnl`, `hDensePack`, joint `hTRT`) bound the
routed carry *mass* by the assembled phase *term* — the orthogonal J.1.1/N.24/I.9 charging
direction, owned by the sibling phase workers — and are carried as hypotheses, exactly as in
`ChargeRoutingCore.towerClsRoutingField`.  No new mass bound is fabricated here.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The genuine first-obstruction priority routing -/

/-- **The genuine v5 seven-class first-obstruction routing.**

A deterministic function of the actual shell geometry, composing the three proved
classifiers in the J.1.1 class-priority order `3 ▸ 0 ▸ 5 ▸ 4 ▸ 2 ▸ 1`:

* `towerClsOfShell ctx k = .densePack` → DensePack `3`;
* `towerClsOfShell ctx k = .other`     → Chernoff / shell-paid progress `0`;
* `towerClsOfShell ctx k = .run`       → Run `5`;
* `towerClsOfShell ctx k = .returnPkg` → Return / endpoint `4`;
* otherwise (`towerClsOfShell ctx k = .cnlTail`, the catch-all tail) the **run/return
  window-excess bands refine the assignment**: a large run (`runClsOfShell ctx k = 1`) is
  routed to Run `5`; a long return (`returnCls ctx k = 2`) to Return `4`; a semiperiodic
  recurrence (`returnCls ctx k = 1`) to the Tower atom `2`; a bounded tail to CleanCNL `1`.

The old-residual class `6` is never assigned — none of the three proved classifiers detects
old-residual leakage (the separate Lemma L.6 obligation), so this is the genuine
no-old-residual-leakage routing. -/
def genuineChargeRoute (ctx : ActualFailureContext) : ℕ → Fin 7 := fun k =>
  if towerClsOfShell ctx k = TowerExitClass.densePack then 3
  else if towerClsOfShell ctx k = TowerExitClass.other then 0
  else if towerClsOfShell ctx k = TowerExitClass.run then 5
  else if towerClsOfShell ctx k = TowerExitClass.returnPkg then 4
  else if runClsOfShell ctx k = 1 then 5
  else if returnCls ctx k = 2 then 4
  else if returnCls ctx k = 1 then 2
  else 1

/-! ## 2.  Totality / well-definedness and the per-`TowerExitClass` values

The routing is a total function `ℕ → Fin 7` by construction (the final `else 1`).  These
value lemmas pin down the genuine destination once the primary L.3.1 classifier is known. -/

/-- DensePack tower-exit → DensePack `3`. -/
theorem genuineChargeRoute_of_densePack (ctx : ActualFailureContext) {k : ℕ}
    (h : towerClsOfShell ctx k = TowerExitClass.densePack) :
    genuineChargeRoute ctx k = 3 := by simp [genuineChargeRoute, h]

/-- `.other` (lower-order remainder) tower-exit → Chernoff / progress `0`. -/
theorem genuineChargeRoute_of_other (ctx : ActualFailureContext) {k : ℕ}
    (h : towerClsOfShell ctx k = TowerExitClass.other) :
    genuineChargeRoute ctx k = 0 := by simp [genuineChargeRoute, h]

/-- Run tower-exit → Run `5`. -/
theorem genuineChargeRoute_of_run (ctx : ActualFailureContext) {k : ℕ}
    (h : towerClsOfShell ctx k = TowerExitClass.run) :
    genuineChargeRoute ctx k = 5 := by simp [genuineChargeRoute, h]

/-- Return tower-exit → Return `4`. -/
theorem genuineChargeRoute_of_returnPkg (ctx : ActualFailureContext) {k : ℕ}
    (h : towerClsOfShell ctx k = TowerExitClass.returnPkg) :
    genuineChargeRoute ctx k = 4 := by simp [genuineChargeRoute, h]

/-- On the `cnlTail` catch-all the genuine route is the run/return window-excess refinement. -/
theorem genuineChargeRoute_of_cnlTail (ctx : ActualFailureContext) {k : ℕ}
    (h : towerClsOfShell ctx k = TowerExitClass.cnlTail) :
    genuineChargeRoute ctx k =
      (if runClsOfShell ctx k = 1 then 5
       else if returnCls ctx k = 2 then 4
       else if returnCls ctx k = 1 then 2 else 1) := by
  simp [genuineChargeRoute, h]

/-- The genuine route **never** assigns the old-residual class `6` (no proved classifier
detects old-residual leakage). -/
theorem genuineChargeRoute_ne_six (ctx : ActualFailureContext) (k : ℕ) :
    genuineChargeRoute ctx k ≠ 6 := by
  unfold genuineChargeRoute
  split_ifs <;> decide

/-! ## 3.  The per-class first-obstruction fibre-membership characterisations

`genuineChargeRoute ctx k = i ↔ <classifier condition>` for each class `i`, i.e. exactly the
genuine first-obstruction assignment.  The conditions carry the J.1.1 priority guards (a
lower-priority class is selected only when no higher-priority obstruction is exposed). -/

/-- **Class 3 (DensePack).** -/
theorem genuineChargeRoute_eq_three_iff (ctx : ActualFailureContext) (k : ℕ) :
    genuineChargeRoute ctx k = 3 ↔ towerClsOfShell ctx k = TowerExitClass.densePack := by
  cases hT : towerClsOfShell ctx k <;> simp [genuineChargeRoute, hT]
  all_goals (split_ifs <;> simp_all)

/-- **Class 0 (Chernoff / shell-paid progress).** -/
theorem genuineChargeRoute_eq_zero_iff (ctx : ActualFailureContext) (k : ℕ) :
    genuineChargeRoute ctx k = 0 ↔ towerClsOfShell ctx k = TowerExitClass.other := by
  cases hT : towerClsOfShell ctx k <;> simp [genuineChargeRoute, hT]
  all_goals (split_ifs <;> simp_all)

/-- **Class 5 (Run).**  The tower exits to Run, or the `cnlTail` tail carries a large run. -/
theorem genuineChargeRoute_eq_five_iff (ctx : ActualFailureContext) (k : ℕ) :
    genuineChargeRoute ctx k = 5 ↔
      towerClsOfShell ctx k = TowerExitClass.run ∨
        (towerClsOfShell ctx k = TowerExitClass.cnlTail ∧ runClsOfShell ctx k = 1) := by
  cases hT : towerClsOfShell ctx k <;> simp [genuineChargeRoute, hT]
  all_goals (split_ifs <;> simp_all)

/-- **Class 4 (Return / endpoint / OLC leakage).**  The tower exits to Return, or the
`cnlTail` tail carries a long (non-run) return. -/
theorem genuineChargeRoute_eq_four_iff (ctx : ActualFailureContext) (k : ℕ) :
    genuineChargeRoute ctx k = 4 ↔
      towerClsOfShell ctx k = TowerExitClass.returnPkg ∨
        (towerClsOfShell ctx k = TowerExitClass.cnlTail ∧ runClsOfShell ctx k ≠ 1 ∧
          returnCls ctx k = 2) := by
  cases hT : towerClsOfShell ctx k <;> simp [genuineChargeRoute, hT]
  all_goals (split_ifs <;> simp_all)

/-- **Class 2 (Tower).**  Genuinely populated: a `cnlTail` tail with a semiperiodic
recurrence (`returnCls = 1`) and no large run. -/
theorem genuineChargeRoute_eq_two_iff (ctx : ActualFailureContext) (k : ℕ) :
    genuineChargeRoute ctx k = 2 ↔
      (towerClsOfShell ctx k = TowerExitClass.cnlTail ∧ runClsOfShell ctx k ≠ 1 ∧
        returnCls ctx k = 1) := by
  cases hT : towerClsOfShell ctx k <;> simp [genuineChargeRoute, hT]
  all_goals (split_ifs <;> simp_all)

/-- **Class 1 (clean-CNL Kraft tail).**  The deliberately-last catch-all: a `cnlTail` tail
with a bounded window excess (`returnCls = 0`) and no large run. -/
theorem genuineChargeRoute_eq_one_iff (ctx : ActualFailureContext) (k : ℕ) :
    genuineChargeRoute ctx k = 1 ↔
      (towerClsOfShell ctx k = TowerExitClass.cnlTail ∧ runClsOfShell ctx k ≠ 1 ∧
        returnCls ctx k ≠ 2 ∧ returnCls ctx k ≠ 1) := by
  cases hT : towerClsOfShell ctx k <;> simp [genuineChargeRoute, hT]
  all_goals (split_ifs <;> simp_all)

/-! ## 4.  The proved-empty old-residual fibre -/

/-- **The old-residual(`6`) routed mass of the genuine routing is `0`** (its fibre is empty,
proved from `genuineChargeRoute_ne_six`). -/
theorem genuineChargeRoute_routed6_zero (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 6 = 0 := by
  rw [routedClassMassOf_eq_sum_fibre]
  have hempty : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 6 = ∅ :=
    Finset.filter_false_of_mem (fun k _ => genuineChargeRoute_ne_six ctx k)
  rw [hempty]; simp

/-! ## 5.  The routing-field assembly from the genuine route

`genuineChargeRoutingResidual` mirrors `ChargeRoutingCore.towerClsRoutingField` but with the
genuine first-obstruction route in place of the single-classifier `chargeRouteOfShell`.  The
Tower(`2`) fibre is **not** folded out (it is genuinely populated), so the joint TRT bound is
supplied in its real `2 + 4 + 5` form; the old-residual bound is discharged from the proved
empty `6`-fibre. -/

/-- **The genuine charge-routing residual.** -/
def genuineChargeRoutingResidual
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
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
        ≤ termChernoff (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData)
    (hCnl : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 1
        ≤ termCnl (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData)
    (hDensePack : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3
        ≤ termDensePack (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData)
    (hTRT : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
          + routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
          + routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
        ≤ termTower (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
          + termReturn (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
          + termRun (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData) :
    ChargeRoutingResidual dirtyCM dirtyWindow tower returnPkg run oldResMass where
  route := genuineChargeRoute
  hChernoff := hChernoff
  hCnl := hCnl
  hDensePack := hDensePack
  hTRT := hTRT
  hOldRes := fun ctx => by
    rw [genuineChargeRoute_routed6_zero ctx]; exact hOldNonneg ctx

/-- **Erdős #260 from the genuine first-obstruction routing.**  The genuine residual feeds
the proved `erdos260_of_chargeRoutingResidual` spine. -/
theorem erdos260_of_genuineChargeRoute
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
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
        ≤ termChernoff (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData)
    (hCnl : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 1
        ≤ termCnl (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData)
    (hDensePack : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3
        ≤ termDensePack (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData)
    (hTRT : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
          + routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
          + routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
        ≤ termTower (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
          + termReturn (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData
          + termRun (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx).toClosurePhaseData)
    (oldResConst : ∀ _ctx : ActualFailureContext, ℝ)
    (oldResSmall : ∀ ctx : ActualFailureContext,
      oldResMass ctx ≤ oldResConst ctx * (ctx.shell.X : ℝ))
    (constCond : ∀ ctx : ActualFailureContext,
      erdos260Constants.cStar * erdos260Constants.ξ + oldResConst ctx
        < erdos260Constants.cPr) :
    Erdos260Statement :=
  (genuineChargeRoutingResidual dirtyCM dirtyWindow tower returnPkg run oldResMass
      hOldNonneg hChernoff hCnl hDensePack hTRT).erdos260_of_chargeRoutingResidual
    oldResConst oldResSmall constCond

/-! ## 6.  The genuine route as a `SeparatedPhaseRoutedBudget` -/

/-- **The genuine route packaged into a `SeparatedPhaseRoutedBudget`.**  The three
routed-fraction slot bounds (Tower / Return / Run, each `≤ c⋆ξX/6`) are supplied for the
genuine route. -/
def genuineSeparatedPhaseRoutedBudget (ctx : ActualFailureContext)
    (hTower : routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6)
    (hReturn : routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6)
    (hRun : routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    SeparatedPhaseRoutedBudget ctx where
  route := genuineChargeRoute ctx
  towerSlot := hTower
  returnSlot := hReturn
  runSlot := hRun

/-! ## 7.  Honest residual inventory -/

/-- The precise status of the genuine first-obstruction routing after this module. -/
def genuineObstructionRoutingResiduals : List String :=
  [ "CLOSED (genuine route) — genuineChargeRoute: the first-obstruction priority cascade " ++
      "composing all three proved classifiers (towerClsOfShell, runClsOfShell, returnCls) in " ++
      "the J.1.1 class-priority order 3▸0▸5▸4▸2▸1, with the cnlTail catch-all genuinely refined " ++
      "by the run/return window-excess bands. A deterministic function of the shell geometry.",
    "CLOSED (fibre membership) — genuineChargeRoute_eq_{three,zero,five,four,two,one}_iff and " ++
      "genuineChargeRoute_ne_six: the full per-class first-obstruction characterisations " ++
      "(genuineChargeRoute ctx k = i ↔ classifier condition), with the J.1.1 priority guards.",
    "CLOSED (empty old-residual fibre, honest) — genuineChargeRoute_routed6_zero: the " ++
      "old-residual(6) routed mass is 0. Honest, not degenerate: none of the three available " ++
      "proved classifiers detects old-residual leakage (the separate Lemma L.6 obligation). " ++
      "The Tower(2) fibre is NOT forced empty — it is genuinely populated by the semiperiodic " ++
      "return band — so the joint Tower+Return+Run class stays the real N.24 bound.",
    "CLOSED (routing-field assembly) — genuineChargeRoutingResidual / erdos260_of_genuineChargeRoute: " ++
      "the genuine route plus the four per-class bounds builds a ChargeRoutingResidual and drives " ++
      "the proved erdos260_of_chargeRoutingResidual spine to Erdos260Statement.",
    "CLOSED (budget packaging) — genuineSeparatedPhaseRoutedBudget: the genuine route as a " ++
      "SeparatedPhaseRoutedBudget from its three routed-fraction slot bounds.",
    "OPEN (per-class capacity bounds) — hChernoff/hCnl/hDensePack (separable) and the joint hTRT " ++
      "(Tower+Return+Run, N.24 same-threshold) bound the routed carry MASS by the assembled phase " ++
      "TERM: the orthogonal J.1.1/N.24/I.9 charging direction, owned by the sibling phase workers, " ++
      "carried here as hypotheses exactly as in ChargeRoutingCore.towerClsRoutingField." ]

theorem genuineObstructionRoutingResiduals_nonempty :
    genuineObstructionRoutingResiduals ≠ [] := by
  simp [genuineObstructionRoutingResiduals]

/-! ## 8.  Axiom-cleanliness audit -/

#print axioms genuineChargeRoute
#print axioms genuineChargeRoute_ne_six
#print axioms genuineChargeRoute_eq_three_iff
#print axioms genuineChargeRoute_eq_zero_iff
#print axioms genuineChargeRoute_eq_five_iff
#print axioms genuineChargeRoute_eq_four_iff
#print axioms genuineChargeRoute_eq_two_iff
#print axioms genuineChargeRoute_eq_one_iff
#print axioms genuineChargeRoute_routed6_zero
#print axioms genuineChargeRoutingResidual
#print axioms erdos260_of_genuineChargeRoute
#print axioms genuineSeparatedPhaseRoutedBudget

end

end Erdos260
