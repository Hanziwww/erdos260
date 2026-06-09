import Mathlib
import Erdos260.CentralChargeBridge
import Erdos260.Erdos260ReducedToCoresV2

/-!
# Erdős #260, the FINAL reduced endpoint on the FAITHFUL central charge bridge

This module is the *final integration* of the Erdős #260 development.  It pivots
the reduced endpoint onto the **manifestly-sound** central charge-bridge spine
`CentralChargeBridge.erdos260_of_centralChargeBridge` and assembles its inputs
from the already-proven phase leaves and cores, producing the **smallest genuine
residual** `Erdos260FinalResidual` and the capstone

```
erdos260_final_reduced : Erdos260FinalResidual → Erdos260Statement.
```

## Why this supersedes `centralDensePack` (the V2 residual)

The V2 residual `Erdos260PhaseCoresV2.centralDensePack` is **circular**: it bounds
the *whole* high-excess carry mass by `manuscriptCstarSmall · X`, which (chained
with the proved Lemma 21.1 pressure floor, via
`towerBudget_residual_forces_X_nonpos`) already forces `X ≤ 0` for *every* failure
context — so the single field `centralDensePack` **alone implies the entire
theorem**.  This is proved as `centralDensePack_isWholeTheorem`
(`CentralChargeBridge.lean`): it is the whole theorem in disguise, not a faithful
reduction.  Accordingly `centralDensePack` is **retired** and appears *nowhere*
as a field of `Erdos260FinalResidual`.

The honest replacement is the four-bound recurrence-I.11′ contradiction
(pressure floor + augmented charge bridge + phase budget + L.6.5 smallness),
packaged as `CentralChargeBridgeResidual`.  Its pressure floor (Lemma 21.1) and
its full phase budget `ClosurePhaseMass ≤ c_⋆·ξ·X` (the sum of the six per-phase
budgets, **including** the I.4.1 DensePack-under-failure step inside
`ClosurePhaseMass_le_budget`) are discharged **internally**; only the genuine
manuscript inputs survive.

## What this module assembles (eliminations backed by proven theorems)

The `phases` field of `CentralChargeBridgeResidual` is assembled per failure
context by `assembledFinalPhases`, with **three of the six phases discharged
outright** from the proven shell leaves:

* **Chernoff (22.1A)** — the *fully unconditional* model leaf
  `chernoff22_1ALeafOfShell` (no Kraft / counting hypothesis);
* **clean CNL (L.1.2 / G.35)** — the *fully closed* concrete leaf
  `cnlLeafFromShellConcrete` (shell factor, interval length, and the G.35 budget
  all supplied from `CNLScalarBudgetCore`);
* **DensePack (I.4.1 / K.1.3)** — the closed grounded leaf
  `appendixNGapCanonicalYActualDensePackToGrounded`.

These three phases are **not** fields of `Erdos260FinalResidual`.

The remaining three phase capacities (**Tower I.3.1**, **Return I.5.1/M.2/J.4/L.6**,
**Run I.5.2**) and the **Dirty K.2.5** package are carried as honest residual
leaf obligations.  The of-shell Tower/Run *budget* leaves
(`towerLeafOfShell`, `runLeafOfShell`) re-index the **entire** high-excess start
set, so their per-phase budget *is itself* the circular full-mass over-claim
(`towerBudget_residual_forces_X_nonpos`); they are therefore **not** used.  The
genuine capacity packages (`TowerSeparatedLocalLeafInputData`,
`ReturnSeparatedLocalLeafInputData`, `RunSeparatedLocalLeafInputData`) are carried
as residual inputs instead — they are inhabited by *genuine partial* phase
families (small capacity), not by the full-mass re-indexing, and so are honest.
The Dirty leaf is carried in its proof-`v4` reduced form: the model absolute
constant `dirtyCM` together with the K.2.5 `WindowRunScaleCountBound` window
count `dirtyWindow`, threaded through the proven core
`dirtyLeafFibreBound_of_window` (`DirtyFibreBoundCore`) — the genuine
model-fidelity residual.

## The genuinely remaining mathematics (the fields of `Erdos260FinalResidual`)

* `tower`, `returnPkg`, `run` — the three remaining per-phase **capacity**
  packages (I.3.1 / I.5.1 / I.5.2);
* `dirtyCM`, `dirtyWindow` — the K.2.5 dirty window-count (model-fidelity caveat);
* `oldResMass` — the v5 L.6.4 old-residual branch mass `OldRes_{s,j}(Y)`;
* `routing` — the v5 **seven-class J.1.1 priority routing**
  (`RoutedHighExcessChargeDataOldRes`): the deep dynamical content (three
  separable charged classes, the joint Tower+Return+Run N.24 TRT bound, and the
  old-residual class), discharging the augmented bridge
  `highExcessMass ≤ ClosurePhaseMass + oldResMass`;
* `oldResConst` — the v5 product constant `C_Q · c_*`;
* `oldResSmall` — the **Lemma L.6.5** density-sensitive smallness
  `oldResMass ≤ (C_Q·c_*)·X`;
* `constCond` — the v5 constant condition `c_⋆·ξ + C_Q·c_* < c_pr`
  ("choose `c_*` last").

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1. The assembled six-phase package (Chernoff / CNL / DensePack closed) -/

/-- **The final assembled six-phase factory package for a failure context.**

The six phase factories of `CentralChargeBridgeResidual.phases`, with **three
phases discharged outright** from the proven shell leaves (Chernoff model leaf,
the fully-closed concrete CNL leaf, the grounded DensePack leaf) and the other
three (**Tower / Return / Run capacity packages**) plus the **Dirty K.2.5**
package supplied as the genuine residual inputs.

The Dirty leaf is threaded through the proven reduction
`dirtyLeafFibreBound_of_window`: the per-dyadic-pair fibre bound is reduced to the
K.2.5 `WindowRunScaleCountBound` window count (the model-fidelity caveat), so the
only Dirty residual data are the absolute constant `CM` and the window-count
proof `hWindow`. -/
def assembledFinalPhases
    (CM : ∀ _ctx : ActualFailureContext, ℕ)
    (hWindow : ∀ ctx : ActualFailureContext, WindowRunScaleCountBound ctx (CM ctx))
    (tower : ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (returnPkg : ∀ ctx : ActualFailureContext,
      ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (run : ∀ ctx : ActualFailureContext,
      RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (ctx : ActualFailureContext) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  actualProofV4LeafPhases ctx
    (chernoff22_1ALeafOfShell ctx)
    (cnlLeafFromShellConcrete ctx)
    (appendixNGapCanonicalYActualDensePackToGrounded ctx.shell ctx.hc0Small
      ctx.shell_startThreshold_le)
    ((dirtyLeafOfShell ctx (CM ctx)
        (dirtyLeafFibreBound_of_window ctx (CM ctx) (hWindow ctx))).toDirtyMultiplicityData)
    (tower ctx)
    (returnPkg ctx)
    (run ctx)

/-! ## 2. The smallest genuine residual surface -/

/-- **The final genuine residual surface of Erdős #260.**

Every field is a genuine, individually-true manuscript estimate (no field is the
whole theorem in disguise — contrast the retired circular `centralDensePack`).
Three of the six phase capacities (Chernoff / clean-CNL / DensePack) are
discharged internally by `assembledFinalPhases`; the pressure floor (Lemma 21.1)
and the full phase budget `ClosurePhaseMass ≤ c_⋆·ξ·X` are discharged internally
by the spine `erdos260_of_centralChargeBridge`.  What remains: -/
structure Erdos260FinalResidual where
  /-- **K.2.5 dirty absolute constant** `CM = C` (model-fidelity caveat). -/
  dirtyCM : ∀ _ctx : ActualFailureContext, ℕ
  /-- **K.2.5 window run-scale count bound** — *few window positions share any
  forward-run scale* (the Fine–Wilf / J.4 / Erdős–Szekeres residual, the genuine
  model-fidelity caveat of the Dirty phase). -/
  dirtyWindow : ∀ ctx : ActualFailureContext, WindowRunScaleCountBound ctx (dirtyCM ctx)
  /-- **Tower I.3.1 capacity package** — the L.3.1 separated tower leaf (genuine
  partial tower family, *not* the circular full-mass re-indexing). -/
  tower : ∀ ctx : ActualFailureContext,
    TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ)
  /-- **Return I.5.1 / M.2 / J.4 / L.6 capacity package** — the separated return leaf. -/
  returnPkg : ∀ ctx : ActualFailureContext,
    ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ)
  /-- **Run I.5.2 capacity package** — the L.4.1 / L.4.2 / I.5.2 separated run leaf. -/
  run : ∀ ctx : ActualFailureContext,
    RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ)
  /-- **L.6.4 old-residual branch mass** `OldRes_{s,j}(Y)` per failure context. -/
  oldResMass : ∀ _ctx : ActualFailureContext, ℝ
  /-- **The v5 seven-class J.1.1 priority routing** discharging the augmented
  charge bridge `highExcessMass ≤ ClosurePhaseMass + oldResMass` — the deep
  dynamical content (three separable charged classes, the joint Tower+Return+Run
  N.24 TRT bound, and the new old-residual class). -/
  routing : ∀ ctx : ActualFailureContext,
    RoutedHighExcessChargeDataOldRes
      (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx)
      ctx.n24CarryData (oldResMass ctx)
  /-- **The v5 product constant** `C_Q · c_*` per failure context. -/
  oldResConst : ∀ _ctx : ActualFailureContext, ℝ
  /-- **Lemma L.6.5 old-residual smallness** `oldResMass ≤ (C_Q·c_*)·X` — the
  smallness carried by the low-density terminal-endpoint count. -/
  oldResSmall : ∀ ctx : ActualFailureContext,
    oldResMass ctx ≤ oldResConst ctx * (ctx.shell.X : ℝ)
  /-- **The v5 constant condition** `c_⋆·ξ + C_Q·c_* < c_pr` ("choose `c_*` last"). -/
  constCond : ∀ ctx : ActualFailureContext,
    erdos260Constants.cStar * erdos260Constants.ξ + oldResConst ctx
      < erdos260Constants.cPr

namespace Erdos260FinalResidual

/-- Package the final residual into the faithful central charge-bridge residual
surface, with the assembled phases and the merged product constant `cStarSmall := 1`. -/
def toCentralChargeBridgeResidual (R : Erdos260FinalResidual) :
    CentralChargeBridgeResidual where
  phases := fun ctx =>
    assembledFinalPhases R.dirtyCM R.dirtyWindow R.tower R.returnPkg R.run ctx
  oldResMass := R.oldResMass
  cQ := R.oldResConst
  cStarSmall := fun _ => 1
  routing := R.routing
  oldResSmall := fun ctx => by simpa only [mul_one] using R.oldResSmall ctx
  constCond := fun ctx => by simpa only [mul_one] using R.constCond ctx

end Erdos260FinalResidual

/-! ## 3. The final reduced capstone -/

/-- **Erdős #260, reduced onto the faithful central charge bridge.**

From the smallest genuine residual surface `Erdos260FinalResidual` — the three
remaining per-phase capacity packages (Tower / Return / Run), the K.2.5 dirty
window count, the v5 seven-class J.1.1 routing, the L.6.4 old-residual mass, the
L.6.5 smallness, and the "choose `c_*` last" constant condition — the faithful
spine `erdos260_of_centralChargeBridge` proves `Erdos260Statement`.

The pressure floor (Lemma 21.1), the full phase budget `ClosurePhaseMass ≤ c_⋆·ξ·X`
(including the I.4.1 DensePack-under-failure step), and three of the six phase
capacities (Chernoff 22.1A, clean-CNL L.1.2/G.35, DensePack I.4.1/K.1.3) are all
discharged **internally**.  The retired circular `centralDensePack`
(`centralDensePack_isWholeTheorem`) appears nowhere.

No `sorry`/`axiom`/`admit`. -/
theorem erdos260_final_reduced (R : Erdos260FinalResidual) : Erdos260Statement :=
  erdos260_of_centralChargeBridge R.toCentralChargeBridgeResidual

/-! ## 4. The retired circular residual (cited, never used) -/

/-- **The retired V2 residual `centralDensePack` is the whole theorem in disguise.**

Cited here to document the retirement: this is exactly `centralDensePack_isWholeTheorem`
(`CentralChargeBridge.lean`), which proves that the *single* V2 field
`Erdos260PhaseCoresV2.centralDensePack` already implies `Erdos260Statement` — it bounds
the **whole** high-excess carry mass by `manuscriptCstarSmall · X`, which collides with
the proved Lemma 21.1 pressure floor (`towerBudget_residual_forces_X_nonpos`) and forces
`X ≤ 0` for every failure context.  It is therefore a degenerate / circular residual,
**not** a faithful reduction, and it appears **nowhere** as a field of
`Erdos260FinalResidual`. -/
theorem centralDensePack_retired_isWholeTheorem
    (h : ∀ ctx : ActualFailureContext,
      highExcessMass
          (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
          (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ manuscriptCstarSmall * (ctx.shell.X : ℝ)) :
    Erdos260Statement :=
  centralDensePack_isWholeTheorem h

/-! ## 5. Axiom-cleanliness audit -/

#print axioms erdos260_final_reduced
#print axioms centralDensePack_retired_isWholeTheorem

end

end Erdos260
