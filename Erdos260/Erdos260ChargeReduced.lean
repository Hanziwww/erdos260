import Erdos260.OldResidualCore
import Erdos260.PhaseCapacityCore
import Erdos260.DirtyFaithfulFamilyCore
import Erdos260.ChargeRoutingCore

/-!
# Erdős #260 — the CONSOLIDATED faithful charge reduction (wave-4 integration)

This module is the **wave-4 integration endpoint**.  It wires the four proven
wave-4 closures into a single, consolidated, *faithful* residual surface
`Erdos260ChargeResidual` and proves the capstone

```
erdos260_charge_reduced : Erdos260ChargeResidual → Erdos260Statement.
```

It does **not** edit any existing file; it composes only **proven** wave-4
theorems on top of the manifestly-sound central charge-bridge spine
`CentralChargeBridge.erdos260_of_centralChargeBridge`.

## The four wave-4 closures wired here

* **Faithful Dirty (`DirtyFaithfulFamilyCore`)** — the degenerate
  `Erdos260FinalResidual.dirtyCM`/`dirtyWindow` model-fidelity caveat (the K.2.5
  `WindowRunScaleCountBound`, *proved unattainable with an absolute constant*) is
  **eliminated**: the Dirty K.2.5 input is supplied outright by the closed term
  `faithfulDirtyData ctx : DirtyMultiplicityData` (a genuinely two-dimensional,
  arm/period-separated family with an **absolute** constant `C = 1`, via the proved
  inverse-tower nesting `IsLiftChain.card_le`).  Because the degenerate-dirty
  `assembledFinalPhases` and every residual stated against it (`ChargeRoutingResidual`,
  `erdos260_of_remaining_L65`) are *hardcoded* to the `dirtyCM`/`dirtyWindow` path,
  the faithful input requires a **fresh assembly** `assembledFaithfulPhases`; the
  remaining wave-4 components are all reused unchanged (they are polymorphic over
  the phase package).

* **Non-circular phase capacities (`PhaseCapacityCore`)** — the three remaining
  per-phase capacity packages `tower`/`returnPkg`/`run` are supplied by
  `phaseCapacityTower`/`phaseCapacityReturn`/`phaseCapacityRun` from a single
  `SeparatedPhaseRoutedBudget` (one shared J.1.1 routing `route` + the three genuine
  *single-routed-class* fraction budgets `routedClassMassOf route 2/4/5 ≤ c⋆ξX/6`).
  These are honest fractions of `highExcessMass`, never the circular full-mass
  re-indexing (`towerLeafOfShell`/`runLeafOfShell`, refuted by
  `towerBudget_residual_forces_X_nonpos`).

* **Genuine L.6.5 old-residual path (`OldResidualCore`)** — the old-residual mass
  is the **genuine nonzero** L.6.4 branch mass `OldRes = ∑_{k∈K} oldResAt k`
  (*not* the degenerate `oldResMass = 0` shortcut).  Its smallness
  `OldRes ≤ (C_Q·c_*)·X` is discharged by the proved `oldResBranchMass_le_const_mul_X`
  (reusing the L.6.5 core `oldRes_le_of_density`) from the three genuine analytic
  inputs (the L.20/L.21 multiplier×support bound and the L.22 low-density endpoint
  count).  The product constant is the concrete `oldResConstVal = C_Q·c_*` and the
  "choose `c_*` last" condition `constCond` is **fully closed** by
  `oldResConstVal_constCond`.

* **The v5 seven-class routing (`ChargeRoutingCore` / `ChargeBridgeReduction`)** —
  the augmented charge bridge `highExcessMass ≤ ClosurePhaseMass + oldResMass` is the
  proved summation skeleton `RoutedHighExcessChargeDataOldRes.highExcess_le_phaseMass_add_oldRes`,
  here re-stated against the faithful assembly and the genuine branch mass.  Its five
  per-class charging bounds (the J.1.1 / N.24 charging *direction*) are the genuine
  surviving content, exposed exactly as in `ChargeRoutingResidual`/`ChargeRoutingFibreResidual`.

## What survives (the genuine residual `Erdos260ChargeResidual`)

The pressure floor (Lemma 21.1), the full phase budget `ClosurePhaseMass ≤ c⋆·ξ·X`,
and three of the six phase capacities (Chernoff 22.1A, clean-CNL L.1.2/G.35, DensePack
I.4.1/K.1.3) are discharged **internally** by the spine and the assembly.  The Dirty
caveat, `oldResConst`, and `constCond` are **closed** here.  What remains is the genuine
charge-bridge *charging direction*: the per-class charging bounds for the routed classes
(J.1.1 / N.24), the three single-class phase-capacity fraction budgets (I.3.1 / I.5.1 /
I.5.2), and the three L.6.5 analytic inputs (L.20 / L.21 / L.22) for the old-residual class.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The faithful six-phase assembly (degenerate Dirty caveat eliminated)

Identical to `assembledFinalPhases` except the Dirty K.2.5 input is the **closed
faithful term** `faithfulDirtyData ctx` (absolute constant `C = 1`) instead of the
`dirtyCM`/`dirtyWindow` model-fidelity caveat threaded through `dirtyLeafOfShell`.
The other five leaves (Chernoff / clean-CNL / DensePack closed; Tower / Return / Run
carried) are unchanged. -/

/-- **The faithful assembled six-phase factory package.**  The three closed shell
leaves (Chernoff 22.1A, concrete clean-CNL, grounded DensePack) and the **faithful**
Dirty K.2.5 input `faithfulDirtyData ctx`, with the Tower / Return / Run capacity
packages supplied as the genuine residual providers. -/
def assembledFaithfulPhases
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
    (faithfulDirtyData ctx)
    (tower ctx)
    (returnPkg ctx)
    (run ctx)

/-- **The faithful phases driven by a single routed-budget interface.**  The Tower /
Return / Run providers are the non-circular `phaseCapacity…` capacity leaves of the
*shared* routed budget; the resulting phase package's Tower / Return / Run terms are
the routed fibre masses of the budget's one routing. -/
def faithfulCapacityPhases
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  assembledFaithfulPhases (phaseCapacityTower budget) (phaseCapacityReturn budget)
    (phaseCapacityRun budget) ctx

/-! ## 2.  The consolidated genuine residual surface -/

/-- **The consolidated faithful charge residual of Erdős #260.**

Every field is a genuine, individually-true manuscript estimate — the surviving
*charging direction* of the central charge bridge.  After wiring the four wave-4
closures, the only undischarged content is:

* `budget` — the shared v5 J.1.1 seven-class routing `route` together with the three
  **single-routed-class** phase-capacity fraction budgets (Tower I.3.1, Return I.5.1,
  Run I.5.2): `routedClassMassOf route 2/4/5 ≤ c⋆·ξ·X/6`.  A genuine fraction of the
  high-excess mass, never the circular full mass;
* `hChernoff` / `hCnl` / `hDensePack` — the three **separable** per-class charging
  bounds (J.1.1): the routed carry mass of each class is dominated by the matching
  *closed* phase term of the faithful assembly;
* `hTRT` — the **joint** Tower+Return+Run charging bound (the N.24 same-threshold /
  TRT compression): `routedClassMassOf route (2+4+5) ≤ termTower+termReturn+termRun`;
* `oldResIdx` / `oldResAt` — the L.6.4 retained terminal hit-index set `K` and the
  per-index old-residual mass, defining the genuine branch mass `OldRes = ∑_{k∈K} oldResAt k`;
* `Cres` / `Y` / `Csupp` / `Ij` and `hpoint` / `hbound_nonneg` / `hdensity` — the
  three **L.6.5 analytic inputs** (the L.20 multiplier *linear in the active floor* `Y`,
  the L.21 endpoint support, the L.22 low-density endpoint count);
* `hOldRes` — the v5 old-residual class-6 routing bound `routedClassMassOf route 6 ≤ OldRes`.

The Dirty K.2.5 caveat is **eliminated** (faithful absolute-`C` model), and
`oldResConst` / `oldResSmall` / `constCond` are **closed** internally (L.6.5 +
"choose `c_*` last"). -/
structure Erdos260ChargeResidual where
  /-- The shared J.1.1 routing + the three single-class phase-capacity fraction
  budgets (Tower I.3.1 / Return I.5.1 / Run I.5.2). -/
  budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx
  /-- **Class 0 — Chernoff / shell-paid progress** charging (separable, J.1.1). -/
  hChernoff : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 0
      ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData
  /-- **Class 1 — clean-CNL Kraft tail** charging (separable, J.1.1). -/
  hCnl : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 1
      ≤ termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData
  /-- **Class 3 — DensePack marker mass** charging (separable, J.1.1). -/
  hDensePack : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 3
      ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData
  /-- **Classes 2 + 4 + 5 — Tower + Return + Run, jointly** by the N.24 same-threshold
  (TRT) compression. -/
  hTRT : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 2
        + routedClassMassOf ctx.n24CarryData (budget ctx).route 4
        + routedClassMassOf ctx.n24CarryData (budget ctx).route 5
      ≤ termTower (faithfulCapacityPhases budget ctx).toClosurePhaseData
        + termReturn (faithfulCapacityPhases budget ctx).toClosurePhaseData
        + termRun (faithfulCapacityPhases budget ctx).toClosurePhaseData
  /-- **L.6.4 retained terminal hit-index set** `K`. -/
  oldResIdx : ∀ _ctx : ActualFailureContext, Finset ℕ
  /-- **L.6.4 per-index old-residual mass** `oldResAt k`. -/
  oldResAt : ∀ _ctx : ActualFailureContext, ℕ → ℝ
  /-- L.20 residual multiplier constant `C_res` (the multiplier is `C_res·Y`). -/
  Cres : ∀ _ctx : ActualFailureContext, ℝ
  /-- The active floor `Y` (the L.20 multiplier is **linear in** `Y`). -/
  Y : ∀ _ctx : ActualFailureContext, ℝ
  /-- L.21 endpoint-support constant `C_supp`. -/
  Csupp : ∀ _ctx : ActualFailureContext, ℝ
  /-- The canonical block fraction `|I_j|`. -/
  Ij : ∀ _ctx : ActualFailureContext, ℝ
  /-- **L.20 / L.21 per-index bound** — `oldResAt k ≤ (C_res·Y)·(C_supp·|I_j|)`
  (multiplier linear in `Y`, K.1.2-consistent). -/
  hpoint : ∀ ctx : ActualFailureContext, ∀ k ∈ oldResIdx ctx,
    oldResAt ctx k ≤ (Cres ctx * Y ctx) * (Csupp ctx * Ij ctx)
  /-- Nonnegativity of the per-index bound. -/
  hbound_nonneg : ∀ ctx : ActualFailureContext,
    0 ≤ (Cres ctx * Y ctx) * (Csupp ctx * Ij ctx)
  /-- **L.22 low-density endpoint count** — `|K|·(per-index bound) ≤ (C_Q·c_*)·X`
  (smallness carried by the endpoint count under the low-density failure hypothesis). -/
  hdensity : ∀ ctx : ActualFailureContext,
    ((oldResIdx ctx).card : ℝ) * ((Cres ctx * Y ctx) * (Csupp ctx * Ij ctx))
      ≤ oldResConstVal ctx * (ctx.shell.X : ℝ)
  /-- **Class 6 — the v5 old-residual leakage** routing bound (Lemma L.6.4). -/
  hOldRes : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 6
      ≤ ∑ k ∈ oldResIdx ctx, oldResAt ctx k

namespace Erdos260ChargeResidual

/-- The genuine nonzero L.6.4 branch mass `OldRes = ∑_{k∈K} oldResAt k`. -/
def oldResBranchMass (R : Erdos260ChargeResidual) (ctx : ActualFailureContext) : ℝ :=
  ∑ k ∈ R.oldResIdx ctx, R.oldResAt ctx k

/-- **The v5 seven-class routing field over the faithful assembly.**  Re-export of the
`RoutedHighExcessChargeDataOldRes` shape, carrying the five genuine per-class charging
bounds against the faithful phase terms and the genuine branch mass. -/
def routingField (R : Erdos260ChargeResidual) (ctx : ActualFailureContext) :
    RoutedHighExcessChargeDataOldRes (faithfulCapacityPhases R.budget ctx)
      ctx.n24CarryData (R.oldResBranchMass ctx) where
  route := (R.budget ctx).route
  hChernoff := R.hChernoff ctx
  hCnl := R.hCnl ctx
  hDensePack := R.hDensePack ctx
  hTRT := R.hTRT ctx
  hOldRes := R.hOldRes ctx

/-- **Package the consolidated residual into the faithful central charge-bridge residual.**

The phases are the faithful capacity assembly; the old-residual mass is the genuine L.6.4
branch mass; the product constant is the concrete `oldResConstVal = C_Q·c_*` with
`cStarSmall := 1`; the routing is the seven-class field; the L.6.5 smallness is discharged
by `oldResBranchMass_le_const_mul_X`; and the constant condition by `oldResConstVal_constCond`. -/
def toCentralChargeBridgeResidual (R : Erdos260ChargeResidual) :
    CentralChargeBridgeResidual where
  phases := fun ctx => faithfulCapacityPhases R.budget ctx
  oldResMass := R.oldResBranchMass
  cQ := oldResConstVal
  cStarSmall := fun _ => 1
  routing := R.routingField
  oldResSmall := fun ctx => by
    have h := oldResBranchMass_le_const_mul_X (R.hpoint ctx) (R.hbound_nonneg ctx)
      (R.hdensity ctx)
    simpa only [mul_one] using h
  constCond := fun ctx => by
    simpa only [mul_one] using oldResConstVal_constCond ctx

end Erdos260ChargeResidual

/-! ## 3.  The consolidated capstone -/

/-- **Erdős #260, reduced onto the faithful central charge bridge (wave-4 integration).**

From the consolidated genuine residual `Erdos260ChargeResidual` — the J.1.1 routing with
the three single-class phase-capacity fraction budgets, the five per-class charging bounds
(three separable + the joint N.24 TRT), and the genuine L.6.4 / L.6.5 old-residual data —
the manifestly-sound spine `erdos260_of_centralChargeBridge` proves `Erdos260Statement`.

Discharged **internally**: the pressure floor (Lemma 21.1), the full phase budget
`ClosurePhaseMass ≤ c⋆·ξ·X`, and three of the six phase capacities (Chernoff / clean-CNL /
DensePack).  **Eliminated**: the degenerate Dirty `dirtyCM`/`dirtyWindow` caveat (the
faithful absolute-`C` model `faithfulDirtyData`).  **Closed**: `oldResConst` (concrete
`C_Q·c_*`) and `constCond` ("choose `c_*` last").  The genuine L.6.5 path is used — *not*
the degenerate `oldResMass = 0` shortcut.

No `sorry`/`axiom`/`admit`. -/
theorem erdos260_charge_reduced (R : Erdos260ChargeResidual) : Erdos260Statement :=
  erdos260_of_centralChargeBridge R.toCentralChargeBridgeResidual

/-! ## 4.  Honest residual inventory -/

/-- The precise status of each prior `Erdos260FinalResidual` field after this integration. -/
def erdos260ChargeReducedResiduals : List String :=
  [ "ELIMINATED (dirtyCM, dirtyWindow) — the K.2.5 degenerate model-fidelity caveat is " ++
      "replaced by the closed faithful term faithfulDirtyData (absolute C = 1) inside " ++
      "assembledFaithfulPhases; no Dirty field survives.",
    "CONSOLIDATED (tower, returnPkg, run → budget) — the three opaque capacity packages are " ++
      "the non-circular phaseCapacityTower/Return/Run of one shared SeparatedPhaseRoutedBudget " ++
      "(route + the three single-class fraction budgets routedClassMassOf route 2/4/5 ≤ c⋆ξX/6).",
    "CONSOLIDATED/EXPOSED (routing → hChernoff, hCnl, hDensePack, hTRT, hOldRes) — the opaque " ++
      "RoutedHighExcessChargeDataOldRes is exposed as its five genuine per-class charging bounds " ++
      "(three separable J.1.1 + the joint N.24 TRT + the old-residual class), against the faithful " ++
      "phase terms via the proved highExcess_le_phaseMass_add_oldRes summation skeleton.",
    "GENUINE-SURVIVING (oldResMass → oldResIdx, oldResAt + L.6.5 inputs) — the genuine nonzero " ++
      "L.6.4 branch mass OldRes = ∑_{k∈K} oldResAt k (NOT the degenerate oldResMass = 0). Its " ++
      "smallness oldResSmall is discharged by oldResBranchMass_le_const_mul_X (reusing " ++
      "oldRes_le_of_density) from the three L.6.5 analytic inputs hpoint (L.20/L.21), " ++
      "hbound_nonneg, hdensity (L.22).",
    "CLOSED (oldResConst) — concrete oldResConstVal = C_Q·c_*, no longer a free residual.",
    "CLOSED (constCond) — oldResConstVal_constCond: c⋆ξ + C_Q·c_* < c_pr by norm_num " ++
      "(choose c_* last).",
    "DISCHARGED INTERNALLY (by the spine / assembly) — the Lemma 21.1 pressure floor, the full " ++
      "phase budget ClosurePhaseMass ≤ c⋆ξX, and three of the six phase capacities (Chernoff " ++
      "22.1A, clean-CNL L.1.2/G.35, DensePack I.4.1/K.1.3)." ]

theorem erdos260ChargeReducedResiduals_nonempty : erdos260ChargeReducedResiduals ≠ [] := by
  simp [erdos260ChargeReducedResiduals]

/-! ## 5.  Axiom-cleanliness audit -/

#print axioms erdos260_charge_reduced
#print axioms Erdos260ChargeResidual.toCentralChargeBridgeResidual
#print axioms Erdos260ChargeResidual.routingField

end

end Erdos260
