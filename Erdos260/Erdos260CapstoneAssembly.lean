import Erdos260.UnconditionalTheorem
import Erdos260.ChernoffUnconditionalProvider
import Erdos260.CNLUnconditionalProvider
import Erdos260.DensePackReturnUnconditionalProvider
import Erdos260.TowerRunUnconditionalProvider
import Erdos260.RunClass5GenuineLeaf
import Erdos260.CarryHighExcessUnconditionalProvider

/-!
# Erdős #260 — the integration capstone (`Erdos260CapstoneAssembly`)

This module (NEW; it edits no existing file) is the **integration capstone** over the six
per-class provider files produced by the sibling workers.  It wires the genuinely-unconditional
providers into the strongest assembly endpoint and isolates the single sharpest honest residual.

## The assembly target — the actual-failure-context interface (`erdos260_final_actual`)

We assemble through `GlobalAssemblyActualInputs` / `erdos260_final_actual`
(`UnconditionalTheorem.lean`), the honest reduction whose providers are indexed by the genuine
`ActualFailureContext` — the *pinned large failing shells* that actually arise from the global
failure argument (its `startThreshold` is the manuscript large threshold
`manuscriptLargeThresholdOf`).  This is the **sharpest** of the two endpoints, strictly stronger
than the all-shells `GlobalAssemblyCoreInputs` / `erdos260_final_core` route, because in the actual
scope:

* the **carry support residual vanishes** — `ActualFailureContext` proves
  `1 ≤ supportCount d X` (`shell_supportCount_pos`) from the manuscript large threshold, so the
  carry datum is the closed `ActualFailureContext.carryData` with **no** `CarryDataSupportResidual`
  (in the all-shells scope the weaker `aboveCarryThreshold` gate leaves that residual genuinely
  open — see `CarryHighExcessUnconditionalProvider`);
* there is **no Tower/Run scope mismatch** — Tower/Run live over `ActualFailureContext` natively,
  so no above-threshold/below-threshold fallback (hence **no degenerate fallback witness**) is
  needed.

## What is genuinely discharged here (no longer a hypothesis)

| provider | how discharged | status |
| --- | --- | --- |
| **Chernoff** (P-Chernoff) | `chernoffProviderUnconditional ctx.shell` | **CLOSED** (unconditional) |
| **CNL** (P3 / Appendix G) | `cnlUnconditionalProvider ctx.shell` | **CLOSED** (unconditional) |
| **DensePack** (Class 3) | `densePackProvider ctx.shell` | **CLOSED** (unconditional, `c0`-pin-free) |
| **Tower** (Class 2) | `ActualFailureContext.tower` (closed E.2–E.4 recurrent cycle) | **CLOSED** |
| **carry** (Lemma 21.1) | `ActualFailureContext.carryData` (support hit from manuscript large threshold) | **CLOSED** |
| **returnRunMassNonneg** | `genuineReturn_massSum_nonneg` + `runFactoryOfSlot_runMass_nonneg` | **CLOSED** |

The three genuinely-unconditional providers (`chernoffProviderUnconditional`,
`cnlUnconditionalProvider`, `densePackProvider`) are wired in directly, so they are **no longer
hypotheses**.  Tower and carry are discharged by the existing closed `ActualFailureContext` data
(the new `TowerRunUnconditionalProvider` Tower datum is itself residual on
`Class2ActiveFloorCount`, so the closed cycle datum is *strictly better* and is used instead).

## The sharpest honest residual (`Erdos260CapstoneResidual`)

Exactly three genuinely-irreducible analytic atoms remain, none degenerate, none faked:

1. **`runLeaf`** — `∀ ctx, RunClass5GenuineLeaf ctx`: the Appendix L.4 Run class-5 data (the I.6S
   charge/stage map, the finite L.4.2 nested-support half-decrease, and the §26 positive-density
   base run-area cover).  Threaded to the genuine `RunFactoryData` via
   `RunClass5GenuineLeaf.toChain` → `RunClass5StageChain.runFloor` → `runFactoryOfSlot`.
2. **`returnInput`** — `∀ ctx, GenuineReturnShellInput ctx.shell`: the Appendix M/I.5.1 reduced
   Return input (`ReturnFactoryReducedInput`: cleaned dirty family + K.2.5 envelope, `2·M_L ≤ s`
   regime, M.2 routing, L.2.2 counts, K.4 smallness) plus the §I/J.1.1 nonnegativity of the three
   non-OLC return masses.  (The all-zero `genuineReturnShellInputTrivial` is **NOT** used.)
3. **`highExcessRouting`** — `HighExcessRoutingResidualProvider`: the roadmap **P9** central-charge
   bridge, i.e. the J.1.1 seven-class first-obstruction priority routing
   (`RoutedHighExcessChargeDataOldRes`, five per-class mass bounds) + the Lemma L.6.5 old-residual
   smallness.  This is the irreducible analytic heart (the bridge type is provably empty for any
   genuine carry datum, `highExcessChargeData_isEmpty`; the only honest inhabitant is the
   contradiction engine `RoutedHighExcessChargeDataOldRes.refutes_failingShell`).

`erdos260_capstone (R : Erdos260CapstoneResidual) : Erdos260Statement` factors through the accepted
canonical reduction `erdos260_final_actual`, so it is exactly as honest a reduction as the existing
endpoint — only sharper, with carry/Chernoff/CNL/DensePack/Tower all closed.

No `sorry`, `admit`, `axiom`, `native_decide`, or new axioms; no degenerate / empty / vacuous /
false-hypothesis witness.  `#print axioms erdos260_capstone` is exactly
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  Return-mass nonnegativity for a genuine per-shell Return input -/

/-- **Return-mass nonnegativity for `GenuineReturnShellInput`.**

`0 ≤ (G.reduced.toFactoryData).massSum`: the OLC slot is the cardinality `|dirtyFamily|`, and the
three non-OLC return masses are nonnegative by the §I / J.1.1 manuscript charging (the genuine
residual's own fields).  This discharges the Return half of the coordinator's `returnRunMassNonneg`
for the genuine per-context Return input (without the all-shells `returnPkgProvider`). -/
theorem genuineReturn_massSum_nonneg {shell : FailingDyadicShell}
    (G : GenuineReturnShellInput shell) :
    0 ≤ (G.reduced.toFactoryData).massSum := by
  have h1 := G.ordinaryShort_nonneg
  have h2 := G.semiperiodic_nonneg
  have h3 := G.nonlocalLong_nonneg
  have h4 : (0 : ℝ) ≤ (G.reduced.dirtyFamily.card : ℝ) := Nat.cast_nonneg _
  have e : (G.reduced.toFactoryData).massSum
      = G.reduced.ordinaryShort + G.reduced.semiperiodic
        + (G.reduced.dirtyFamily.card : ℝ) + G.reduced.nonlocalLong := rfl
  rw [e]; linarith

/-! ## 2.  The per-context provider components (the genuine, non-degenerate phase data) -/

/-- Chernoff phase datum (UNCONDITIONAL provider, `chernoffProviderUnconditional`). -/
def capChernoff (ctx : ActualFailureContext) :
    ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  chernoffProviderUnconditional ctx.shell ctx.shell_cQ

/-- CNL phase datum (UNCONDITIONAL provider, `cnlUnconditionalProvider`). -/
def capCnl (ctx : ActualFailureContext) :
    CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  cnlUnconditionalProvider ctx.shell ctx.shell_cQ

/-- DensePack phase datum (UNCONDITIONAL, `c0`-pin-free provider, `densePackProvider`). -/
def capDensePack (ctx : ActualFailureContext) :
    DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  densePackProvider ctx.shell ctx.shell_cQ

/-- Tower phase datum (CLOSED via the existing E.2–E.4 recurrent-cycle datum
`ActualFailureContext.tower`; strictly better than the residual Tower provider). -/
def capTower (ctx : ActualFailureContext) :
    TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  ctx.tower

/-! ## 3.  The capstone residual and the assembled actual inputs -/

/-- **The sharpest honest residual of Erdős #260** after this integration.

Three genuinely-irreducible analytic atoms; everything else (carry, Chernoff, CNL, DensePack,
Tower, and the Return/Run mass nonnegativity) is closed in `toActualInputs`. -/
structure Erdos260CapstoneResidual where
  /-- **Run (Class 5, Appendix L.4).**  The genuine Run class-5 leaf per context: the I.6S
  charge/stage map, the finite L.4.2 nested-support half-decrease, and the §26 positive-density
  base run-area cover. -/
  runLeaf : ∀ ctx : ActualFailureContext, RunClass5GenuineLeaf ctx
  /-- **Return (Class 4, Appendix M / I.5.1).**  The genuine per-shell reduced Return input plus
  the §I/J.1.1 nonnegativity of the three non-OLC return masses (NOT the degenerate all-zero
  witness). -/
  returnInput : ∀ ctx : ActualFailureContext, GenuineReturnShellInput ctx.shell
  /-- **The central charge bridge (roadmap P9).**  The J.1.1 first-obstruction seven-class routing
  + the Lemma L.6.5 old-residual smallness — the irreducible analytic heart. -/
  highExcessRouting : HighExcessRoutingResidualProvider

namespace Erdos260CapstoneResidual

/-- Return phase datum from the genuine per-context Return input. -/
def capReturn (R : Erdos260CapstoneResidual) (ctx : ActualFailureContext) :
    ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  (R.returnInput ctx).reduced.toFactoryData

/-- Run phase datum from the genuine per-context Run leaf, via the L.4.2 chain → I.5.2 floor →
`runFactoryOfSlot`. -/
def capRun (R : Erdos260CapstoneResidual) (ctx : ActualFailureContext) :
    RunFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  runFactoryOfSlot ctx ((R.runLeaf ctx).toChain).runFloor

/-- The six assembled phases for one failure context — all genuine, none degenerate. -/
def capPhases (R : Erdos260CapstoneResidual) (ctx : ActualFailureContext) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) where
  chernoff := capChernoff ctx
  cnl := capCnl ctx
  tower := capTower ctx
  densePack := capDensePack ctx
  returnPkg := R.capReturn ctx
  run := R.capRun ctx

/-- **Phase-mass nonnegativity (`trtNonneg`)** for the assembled phases — the §I / J.1.1 charging:
the Return and Run phase masses are nonnegative. -/
theorem capPhases_trtNonneg (R : Erdos260CapstoneResidual) (ctx : ActualFailureContext) :
    (R.capPhases ctx).trtNonneg := by
  apply SixPhaseFactoryData.trtNonneg_of_returnRun_nonneg
  have hr : 0 ≤ (R.capReturn ctx).massSum := genuineReturn_massSum_nonneg (R.returnInput ctx)
  have hrun : 0 ≤ (R.capRun ctx).runMass :=
    runFactoryOfSlot_runMass_nonneg ctx ((R.runLeaf ctx).toChain).runFloor
  show 0 ≤ (R.capPhases ctx).returnPkg.massSum + (R.capPhases ctx).run.runMass
  exact add_nonneg hr hrun

/-- **Assemble the full actual-consumption interface** from the capstone residual.

Carry / Chernoff / CNL / DensePack / Tower are closed (the first three by the unconditional
providers, the last two by the closed `ActualFailureContext` data); Return / Run come from the
genuine per-context leaves; the charge bridge comes from the P9 routing residual. -/
def toActualInputs (R : Erdos260CapstoneResidual) : GlobalAssemblyActualInputs where
  carryData := fun ctx => ctx.carryData
  chernoff := capChernoff
  cnl := capCnl
  densePack := capDensePack
  tower := capTower
  returnPkg := R.capReturn
  run := R.capRun
  highExcessCharge := fun ctx =>
    R.highExcessRouting.highExcessChargeField ctx.shell ctx.shell_cQ
      (R.capPhases ctx) ctx.carryData (R.capPhases_trtNonneg ctx)

end Erdos260CapstoneResidual

/-! ## 4.  The capstone theorem -/

/-- **Erdős #260 from the sharpest honest residual.**

`Erdos260Statement` follows from `Erdos260CapstoneResidual` — the genuine Run class-5 leaf, the
genuine reduced Return input, and the P9 central-charge routing residual — with the carry datum,
Chernoff, CNL, DensePack, Tower, and the Return/Run mass nonnegativity all discharged.  Factors
through the accepted canonical reduction `erdos260_final_actual`. -/
theorem erdos260_capstone (R : Erdos260CapstoneResidual) : Erdos260Statement :=
  erdos260_final_actual R.toActualInputs

/-! ## 4b.  The synthesis hub — the three unconditional providers drop into the all-shells core

The carry/high-excess worker's `CarryHighExcessReducedCoreInputs`
(`CarryHighExcessUnconditionalProvider.lean`) is the all-shells synthesis hub composing through
`erdos260_final_core`.  Here we demonstrate, on that hub directly, that the three
genuinely-unconditional providers (`chernoffProviderUnconditional`, `cnlUnconditionalProvider`,
`densePackProvider`) and the **bare-shell** Tower datum drop in, leaving a documented (strictly
larger) all-shells residual.

This route is **weaker** than `erdos260_capstone` above: the all-shells `aboveCarryThreshold` gate
is weaker than the manuscript large threshold, so (i) the carry support residual
`CarryDataSupportResidual` is genuinely open here (it vanishes in the actual scope), and (ii) Tower
is supplied by the bare-shell closed E.2–E.4 cycle while Return/Run remain as raw factory-data
fields (no `ActualFailureContext` is available to reduce them to their sharper leaves).  It is
included to honor the synthesis-hub interface; the sharp endpoint is `erdos260_capstone`. -/

/-- **The bare-shell Tower datum** (the closed E.2–E.4 recurrent cycle, valid for *any* failing
dyadic shell — `towerCycleOfFailingShellClosed` needs only the shell's rationality witness).  This
is the all-shells analogue of `ActualFailureContext.tower`, closing the `tower` field of the
all-shells core with no scale gate. -/
def capBareTower (shell : FailingDyadicShell) (_hcQ : shell.cQ = erdos260Constants.cQ) :
    TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
  towerOfSlope
    (towerCycleOfFailingShellClosed shell shell.hrational.choose
      shell.hrational.choose_spec).toSlopeAtom
    shell.X_nonneg_real

/-- **The all-shells residual** for the synthesis-hub route: carry support, raw Return/Run factory
data with their mass nonnegativity, and the P9 routing.  (Chernoff/CNL/DensePack/Tower are
discharged in `toReducedCoreInputs`.) -/
structure Erdos260AllShellsResidual where
  /-- **Carry support residual** — `1 ≤ supportCount d X` per `aboveCarryThreshold` shell.  Open in
  the all-shells scope (vanishes in the actual scope from the manuscript large threshold). -/
  carrySupport : CarryDataSupportResidual
  /-- **Return factory data** (raw, all-shells; no `ActualFailureContext` to reduce it). -/
  returnPkg : ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
    ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- **Run factory data** (raw, all-shells; no `ActualFailureContext` to reduce it). -/
  run : ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
    RunFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- §I/J.1.1 Return+Run mass nonnegativity. -/
  returnRunMassNonneg :
    ∀ (shell : FailingDyadicShell) (hcQ : shell.cQ = erdos260Constants.cQ),
      0 ≤ (returnPkg shell hcQ).massSum + (run shell hcQ).runMass
  /-- **The central charge bridge (P9).** -/
  highExcessRouting : HighExcessRoutingResidualProvider

/-- Drop the three unconditional providers + the bare-shell Tower into the synthesis hub. -/
def Erdos260AllShellsResidual.toReducedCoreInputs (R : Erdos260AllShellsResidual) :
    CarryHighExcessReducedCoreInputs where
  carrySupport := R.carrySupport
  chernoff := chernoffProviderUnconditional
  cnl := cnlUnconditionalProvider
  densePack := densePackProvider
  tower := capBareTower
  returnPkg := R.returnPkg
  run := R.run
  returnRunMassNonneg := R.returnRunMassNonneg
  highExcessRouting := R.highExcessRouting

/-- **Erdős #260 from the all-shells synthesis hub** (conditional on the strictly larger all-shells
residual).  Demonstrates the three unconditional providers + bare-shell Tower drop into
`CarryHighExcessReducedCoreInputs` and compose through `erdos260_final_core`. -/
theorem erdos260_capstone_allShells (R : Erdos260AllShellsResidual) : Erdos260Statement :=
  erdos260_of_carryHighExcessReduced R.toReducedCoreInputs

/-! ## 5.  Honest residual inventory -/

/-- The precise post-integration status: discharged vs. residual, per provider. -/
def erdos260CapstoneStatus : List String :=
  [ "DISCHARGED (Chernoff) — chernoffProviderUnconditional ctx.shell: genuine §22 path family " ++
      "{0,1}^{L+1} with positive integer-carry weight; unconditional, no hypothesis.",
    "DISCHARGED (CNL) — cnlUnconditionalProvider ctx.shell: genuine clean-CNL cluster encoding " ++
      "(Appendix G / L.1.2), prefactor-free Kraft bound; unconditional, no hypothesis.",
    "DISCHARGED (DensePack) — densePackProvider ctx.shell: genuine c0-pin-free actual-support " ++
      "marker datum (I.4.1/K.1.3 budget via the 16x slack densePack_fortyKappa_le_budget); " ++
      "unconditional on every aboveCarryThreshold shell, which every ActualFailureContext is.",
    "DISCHARGED (Tower) — ActualFailureContext.tower: the closed E.2-E.4 recurrent-cycle datum " ++
      "towerOfSlope (towerCycleOfFailingShellClosed ...). The new TowerRunUnconditionalProvider " ++
      "Tower datum is residual on Class2ActiveFloorCount, so the closed cycle datum is used.",
    "DISCHARGED (carry, Lemma 21.1) — ActualFailureContext.carryData: NO support residual. The " ++
      "manuscript large threshold (the actual interface's startThreshold) supplies the support hit " ++
      "1 <= supportCount d X (shell_supportCount_pos), so carryDataFromStartThreshold-style closure " ++
      "holds outright; the all-shells CarryDataSupportResidual does NOT arise here.",
    "DISCHARGED (returnRunMassNonneg) — genuineReturn_massSum_nonneg + " ++
      "runFactoryOfSlot_runMass_nonneg: 0 <= returnPkg.massSum + run.runMass.",
    "RESIDUAL (Run, Class 5) — runLeaf : forall ctx, RunClass5GenuineLeaf ctx = the I.6S charge " ++
      "map + finite L.4.2 half-decrease + §26 positive-density base run-area cover. Threaded to " ++
      "RunFactoryData via toChain -> RunClass5StageChain.runFloor -> runFactoryOfSlot.",
    "RESIDUAL (Return, Class 4) — returnInput : forall ctx, GenuineReturnShellInput ctx.shell = " ++
      "the proved ReturnFactoryReducedInput + §I/J.1.1 mass nonnegativity. The dirty family is not " ++
      "recoverable from bare shell data; genuineReturnShellInputTrivial is NOT used.",
    "RESIDUAL (P9 central charge bridge) — highExcessRouting : HighExcessRoutingResidualProvider " ++
      "= the J.1.1 seven-class routing (RoutedHighExcessChargeDataOldRes, 5 per-class mass bounds) " ++
      "+ Lemma L.6.5 smallness. The irreducible analytic heart; the bridge is provably empty for " ++
      "genuine carry data, closed only via refutes_failingShell. The constant condition " ++
      "cStar*xi + 1*c_* < cPr is PROVED (manuscript_closure_pressure), NOT a residual." ]

theorem erdos260CapstoneStatus_nonempty : erdos260CapstoneStatus ≠ [] := by
  simp [erdos260CapstoneStatus]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms erdos260_capstone
#print axioms Erdos260CapstoneResidual.toActualInputs
#print axioms genuineReturn_massSum_nonneg
#print axioms Erdos260CapstoneResidual.capPhases_trtNonneg
#print axioms capBareTower
#print axioms erdos260_capstone_allShells
#print axioms Erdos260AllShellsResidual.toReducedCoreInputs

end

end Erdos260
