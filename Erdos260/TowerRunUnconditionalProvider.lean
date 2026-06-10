import Erdos260.PhaseCapacityCore
import Erdos260.TowerRunSeedClosure
import Erdos260.TowerRunDeepCore
import Erdos260.GlobalTowerAssembly
import Erdos260.GlobalRunAssembly

/-!
# The genuine Tower (Class 2 / Appendix E) and Run (Class 5 / Appendix L.4) factory providers

This module (NEW; it edits no existing file) inhabits the two phase factory data the global
assembly consumes — `TowerTransientFactoryData` (the Phase‑7 / I.3.1 tower output estimate) and
`RunFactoryData` (the Phase‑9 / I.5.2 run‑mass ledger) — **genuinely and non‑degenerately**, for the
honest failure interface `ActualFailureContext` (the pinned large failing shells that arise from the
global failure argument, the index type of `GlobalAssemblyActualInputs` /
`erdos260_final_actual`).

Both providers are built from the **single shared routed‑class‑mass slot**
`routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) c ≤ c⋆·ξ·X/6` over the genuine
first‑obstruction route `genuineChargeRoute` — Tower at class `c = 2`, Run at class `c = 5` — through
the sibling capacity leaves `PhaseCapacityCore.towerLeafOfRouted` / `runLeafOfRouted` and the
existing grounded conversion chains.  The two slots are exactly the two cores carried by the shared
`TowerRunSeedClosureData` (`TowerRunSeedClosure.lean`), so the Tower and Run providers are *owned
together*: they share the SDR / carry‑cycle (Tower) and period‑descent (Run) machinery and bottom out
at the same positive‑density failure geometry `ctx.hfailure`.

## What is genuinely constructed here (no `sorry` / `axiom` / `admit` / `native_decide`)

* `towerFactoryOfSlot` — `TowerTransientFactoryData` from the **class‑2 routed slot**.  Its charged
  entry/exit family is the genuine class‑2 tower fibre `routedFibre … 2` re‑indexed by the genuine
  injection `towerExitOf` (`towerFactoryOfSlot_entryExitSet`), charged by the actual carry‑window
  excess; its total charged mass IS `routedClassMassOf … 2` (`towerFactoryOfSlot_termTower`), and the
  recurrent‑cycle witness is the genuine shell‑closed E.2–E.4 cycle.  **No empty family / zero
  mass / synthetic witness.**
* `runFactoryOfSlot` — `RunFactoryData` from the **class‑5 routed slot**.  Its `runMass` IS the
  genuine class‑5 routed mass `routedClassMassOf … 5` (`runFactoryOfSlot_runMass`), bounded by the
  I.5.2 floor; the period‑descent ratio is the genuine `2^{−cY} = (1/2)^Q`.
* `TowerRunGenuineResidual` — the **single shared sharpest residual**, bundling the two genuine
  Appendix E / L.4 leaves `Class2ActiveFloorCount ctx` (the §I.4 active‑floor count, = the class‑2
  tower sub‑mass core) and `RunClass5StageChain ctx` (the L.4.2 period‑descent chain whose `.runFloor`
  is the I.5.2 floor).  Its `.tower` / `.run` are the genuine providers, and `.run_runMass_nonneg`
  is the Run mass nonnegativity the coordinator needs.
* `towerProviderOfSeed` / `runProviderOfSeed` — the same two providers from the shared
  `TowerRunSeedClosureData` (the codebase's existing Tower+Run seed closure), with
  `runProviderOfSeed_runMass_nonneg`.
* Budget sanity: `towerFactoryOfSlot_bound` (`∃ Tower, 0 ≤ Tower ≤ c⋆ξX/6`, the I.3.1 tower output
  estimate) and `runFactoryOfSlot_bound` (`runMass ≤ c⋆ξX/6`, Prop. I.5.2).

## Honest status (the sharpest current residual, per provider)

**REDUCED, not closed.**  Every structural, combinatorial, and budget step downstream of the two
routed‑class slots is discharged genuinely here and in the imported modules.  The single remaining
genuine input of each provider is, *as one Lean type*:

* **Tower** — `Class2ActiveFloorCount ctx` (the §I.4 active‑floor count `#fibre₂·positivePart(2Y) ≤
  ξX/6` + boundary exclusion), which `towerSubMass_of_failure` further reduces to the K.1.1
  endpoint‑disjoint cover + the I.4.1 dense‑marker hit packing + the K.4 smallness, genuinely
  consuming `ctx.hfailure`.
* **Run** — `RunClass5StageChain ctx` (the L.4.2 period‑descent chain: the I.6S charged partition
  `hsum`, the mass half‑decrease `hhalf`, and the I.5.2 base bound `hbase`), further reducible (via
  `RunClass5GenuineLeaf` / `RunBaseAreaCover`, `RunClass5GenuineLeaf.lean`) to the §26 positive‑density
  base run‑area cover, also discharged from `ctx.hfailure`.

These are the manuscript's irreducible Appendix E (I.4.1 dense packing) and Appendix L.4 (I.6S + L.4.2
+ §26) analytic data; no degenerate witness is supplied for either.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## Part A — the two factory data from a single routed‑class slot bound

The Tower and Run factory data are produced from the *single* genuine input each consumes: the
routed‑class‑mass slot `routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) c ≤ c⋆·ξ·X/6`
(Tower `c = 2`, Run `c = 5`).  Everything between the slot and the capstone factory datum is the
already‑proved capacity‑leaf + grounded conversion chain. -/

/--
**The genuine Tower transient factory datum from the class‑2 routed slot.**

Threads the class‑2 routed‑fraction budget through the sibling capacity leaf
`PhaseCapacityCore.towerLeafOfRouted` and the grounded conversion chain
`toGroundedTowerLocalData ∘ toTowerTransientFactoryData`.  The resulting datum is genuinely
non‑degenerate: its charged entry/exit family is the real class‑2 tower fibre re‑indexed by the
genuine injection `towerExitOf`, charged by the actual carry‑window excess, and its cycle witness is
the genuine shell‑closed E.2–E.4 carry cycle.
-/
def towerFactoryOfSlot (ctx : ActualFailureContext)
    (hslot :
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  (towerLeafOfRouted ctx (genuineChargeRoute ctx) hslot).toGroundedTowerLocalData
    |>.toTowerTransientFactoryData

/--
**The genuine Run factory datum from the class‑5 routed slot.**

Threads the class‑5 routed‑fraction budget (the I.5.2 run‑mass floor) through the sibling capacity
leaf `PhaseCapacityCore.runLeafOfRouted` and the grounded conversion chain
`toGroundedRunLocalData ∘ toRunFactoryData`.  The resulting datum's `runMass` is the genuine class‑5
routed mass `routedClassMassOf … 5` (not a synthetic weight).
-/
def runFactoryOfSlot (ctx : ActualFailureContext)
    (hslot :
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    RunFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  (runLeafOfRouted ctx (genuineChargeRoute ctx) hslot).toGroundedRunLocalData
    |>.toRunFactoryData

/-! ### Genuineness certificates (the entry/exit family and the run mass are the real objects) -/

/-- **Non‑degeneracy (Tower).**  The charged entry/exit family of the Tower datum is exactly the
genuine class‑2 tower fibre `routedFibre … 2` re‑indexed by the injection `towerExitOf` — never an
empty / synthetic family. -/
theorem towerFactoryOfSlot_entryExitSet (ctx : ActualFailureContext)
    (hslot :
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    (towerFactoryOfSlot ctx hslot).entryExitSet
      = (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).image towerExitOf := rfl

/-- **The Tower datum charges exactly the class‑2 routed mass (`termTower`).**  The total charged
tower‑exit mass equals the genuine class‑2 routed fraction `routedClassMassOf … 2` — the manuscript
`termTower`, never the full high‑excess carry mass. -/
theorem towerFactoryOfSlot_termTower (ctx : ActualFailureContext)
    (hslot :
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    (∑ b ∈ (towerFactoryOfSlot ctx hslot).entryExitSet,
        (towerFactoryOfSlot ctx hslot).chargedWeight b)
      = routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2 :=
  tower_routedFibre_image_sum ctx (genuineChargeRoute ctx)

/-- **Non‑degeneracy (Run).**  The Run datum's `runMass` is exactly the genuine class‑5 routed mass
`routedClassMassOf … 5` — the actual mean‑low trichotomy class mass, not a synthetic weight. -/
theorem runFactoryOfSlot_runMass (ctx : ActualFailureContext)
    (hslot :
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    (runFactoryOfSlot ctx hslot).runMass
      = routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5 := rfl

/-- **Run mass nonnegativity (from the slot).**  The class‑5 routed mass is a sum of nonnegative
window excesses, hence nonnegative. -/
theorem runFactoryOfSlot_runMass_nonneg (ctx : ActualFailureContext)
    (hslot :
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    0 ≤ (runFactoryOfSlot ctx hslot).runMass := by
  rw [runFactoryOfSlot_runMass]
  exact routedClassMassOf_nonneg ctx.n24CarryData (genuineChargeRoute ctx) 5

/-! ### Budget sanity (the manuscript per‑phase budgets) -/

/-- **Proposition I.3.1 Tower output estimate.**  The tower charged mass fits the Tower slot
`c⋆·ξ·X/6` (in the `towerPackageBound` form `∃ Tower, 0 ≤ Tower ∧ Tower ≤ c⋆·ξ·X/6`). -/
theorem towerFactoryOfSlot_bound (ctx : ActualFailureContext)
    (hslot :
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    ∃ Tower : ℝ, 0 ≤ Tower ∧
      Tower ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  towerPackageBound_of_transientFactory (towerFactoryOfSlot ctx hslot)

/-- **Proposition I.5.2 Run bound.**  The run mass fits the Run slot `c⋆·ξ·X/6`. -/
theorem runFactoryOfSlot_bound (ctx : ActualFailureContext)
    (hslot :
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    (runFactoryOfSlot ctx hslot).runMass
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  runBound_of_factory (runFactoryOfSlot ctx hslot)

/-! ## Part B — the shared sharpest residual and the two providers

`TowerRunGenuineResidual` bundles the two genuine Appendix E / L.4 leaves — `Class2ActiveFloorCount`
(Tower, the §I.4 active‑floor count) and `RunClass5StageChain` (Run, the L.4.2 period‑descent chain) —
as a single per‑context residual.  These are the sharpest cache‑stable single‑Lean‑type cores: each is
one inequality / charged partition over the genuine first‑obstruction fibre, both bottoming out at the
positive‑density failure `ctx.hfailure`. -/

/-- **The shared sharpest Tower + Run residual.**  Per failure context: the genuine §I.4 Tower
class‑2 active‑floor count and the genuine Appendix L.4 Run class‑5 period‑descent chain.  These two
leaves jointly inhabit the Tower and Run factory providers. -/
structure TowerRunGenuineResidual where
  /-- **Tower (Class 2, Appendix E / §I.4).**  The active‑floor count `#fibre₂·positivePart(2Y) ≤
  ξX/6` + boundary exclusion; equivalently the class‑2 routed sub‑mass core `htowerSubMass`. -/
  towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx
  /-- **Run (Class 5, Appendix L.4).**  The L.4.2 period‑descent chain: the I.6S charged partition
  `hsum`, the mass half‑decrease `hhalf`, and the I.5.2 base bound `hbase`; `.runFloor` delivers the
  class‑5 floor `routedClassMassOf … 5 ≤ c⋆·ξ·X/6`. -/
  runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx

namespace TowerRunGenuineResidual

/-- **The genuine Tower provider.**  For every failure context, the §I.4 active‑floor count yields
the class‑2 routed slot (`Class2ActiveFloorCount.htowerSubMass` lifted to `c⋆·ξ·X/6` by
`towerSlot_of_subMass`), which `towerFactoryOfSlot` turns into the genuine Tower transient factory
datum.  This is the `tower` field of `GlobalAssemblyActualInputs`. -/
def tower (R : TowerRunGenuineResidual) :
    ∀ ctx : ActualFailureContext,
      TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  fun ctx => towerFactoryOfSlot ctx (towerSlot_of_subMass ctx (R.towerCount ctx).htowerSubMass)

/-- **The genuine Run provider.**  For every failure context, the Run class‑5 chain yields the
class‑5 routed slot (`RunClass5StageChain.runFloor`, the I.5.2 floor `routedClassMassOf … 5 ≤
c⋆·ξ·X/6`), which `runFactoryOfSlot` turns into the genuine Run factory datum.  This is the `run`
field of `GlobalAssemblyActualInputs`. -/
def run (R : TowerRunGenuineResidual) :
    ∀ ctx : ActualFailureContext,
      RunFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  fun ctx => runFactoryOfSlot ctx (R.runChain ctx).runFloor

/-- **Run mass nonnegativity (the coordinator's required lemma).**  `0 ≤ (R.run ctx).runMass`,
since the run mass is the genuine class‑5 routed mass. -/
theorem run_runMass_nonneg (R : TowerRunGenuineResidual) (ctx : ActualFailureContext) :
    0 ≤ (R.run ctx).runMass :=
  runFactoryOfSlot_runMass_nonneg ctx (R.runChain ctx).runFloor

/-- The Tower provider meets the I.3.1 Tower budget. -/
theorem tower_bound (R : TowerRunGenuineResidual) (ctx : ActualFailureContext) :
    ∃ Tower : ℝ, 0 ≤ Tower ∧
      Tower ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  towerFactoryOfSlot_bound ctx (towerSlot_of_subMass ctx (R.towerCount ctx).htowerSubMass)

/-- The Run provider meets the I.5.2 Run budget. -/
theorem run_bound (R : TowerRunGenuineResidual) (ctx : ActualFailureContext) :
    (R.run ctx).runMass
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  runFactoryOfSlot_bound ctx (R.runChain ctx).runFloor

end TowerRunGenuineResidual

/-! ## Part C — the two providers from the shared `TowerRunSeedClosureData`

The codebase's existing shared Tower+Run seed closure `TowerRunSeedClosureData`
(`TowerRunSeedClosure.lean`) already proves the class‑2 Tower slot (`towerSlot`) and the class‑5 Run
floor (`hrunFloor`).  We expose the two providers directly from it, so a coordinator holding the seed
closure (e.g. via `TowerRunSeedClosureData.ofFailureSeeds`) gets both factory data with no further
work. -/

/-- **The Tower provider from the shared seed closure.** -/
def towerProviderOfSeed (C : TowerRunSeedClosureData) :
    ∀ ctx : ActualFailureContext,
      TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  fun ctx => towerFactoryOfSlot ctx (C.towerSlot ctx)

/-- **The Run provider from the shared seed closure.** -/
def runProviderOfSeed (C : TowerRunSeedClosureData) :
    ∀ ctx : ActualFailureContext,
      RunFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  fun ctx => runFactoryOfSlot ctx (C.hrunFloor ctx)

/-- **Run mass nonnegativity for the seed‑closure Run provider.** -/
theorem runProviderOfSeed_runMass_nonneg (C : TowerRunSeedClosureData)
    (ctx : ActualFailureContext) :
    0 ≤ (runProviderOfSeed C ctx).runMass :=
  runFactoryOfSlot_runMass_nonneg ctx (C.hrunFloor ctx)

/-! ## Part D — honest residual inventory -/

/-- The precise per‑provider status of the Tower (Class 2) and Run (Class 5) factory data after this
module. -/
def towerRunUnconditionalProviderResiduals : List String :=
  [ "CONSTRUCTED (Tower factory) — towerFactoryOfSlot: TowerTransientFactoryData from the class-2 " ++
      "routed slot routedClassMassOf … (genuineChargeRoute ctx) 2 ≤ c⋆ξX/6, via towerLeafOfRouted + " ++
      "toGroundedTowerLocalData + toTowerTransientFactoryData. NON-DEGENERATE: entryExitSet = " ++
      "(routedFibre … 2).image towerExitOf (towerFactoryOfSlot_entryExitSet), termTower = " ++
      "routedClassMassOf … 2 (towerFactoryOfSlot_termTower), genuine shell-closed E.2-E.4 cycle.",
    "CONSTRUCTED (Run factory) — runFactoryOfSlot: RunFactoryData from the class-5 routed slot " ++
      "routedClassMassOf … (genuineChargeRoute ctx) 5 ≤ c⋆ξX/6, via runLeafOfRouted + " ++
      "toGroundedRunLocalData + toRunFactoryData. NON-DEGENERATE: runMass = routedClassMassOf … 5 " ++
      "(runFactoryOfSlot_runMass), the genuine mean-low class mass; ratio 2^{-cY} = (1/2)^Q.",
    "DELIVERED (Run mass nonneg) — runFactoryOfSlot_runMass_nonneg / " ++
      "TowerRunGenuineResidual.run_runMass_nonneg / runProviderOfSeed_runMass_nonneg: " ++
      "0 ≤ runMass = routedClassMassOf … 5 (routedClassMassOf_nonneg).",
    "DELIVERED (budgets) — towerFactoryOfSlot_bound (∃ Tower, 0 ≤ Tower ≤ c⋆ξX/6, Prop. I.3.1) and " ++
      "runFactoryOfSlot_bound (runMass ≤ c⋆ξX/6, Prop. I.5.2).",
    "SHARED RESIDUAL — TowerRunGenuineResidual bundles the two genuine leaves: towerCount " ++
      "(Class2ActiveFloorCount, §I.4 active-floor count) and runChain (RunClass5StageChain, the L.4.2 " ++
      "period-descent chain). .tower / .run are the providers; both share genuineChargeRoute and the " ++
      "positive-density failure ctx.hfailure.",
    "SHARED RESIDUAL (variant) — towerProviderOfSeed / runProviderOfSeed from the codebase's " ++
      "TowerRunSeedClosureData (towerSlot + hrunFloor), reducible to the bare I.4.1/I.5.2 primitives " ++
      "by TowerRunSeedClosureData.ofFailureSeeds.",
    "SHARPEST OPEN (Tower) — Class2ActiveFloorCount ctx (TowerRunDeepCore.lean): the §I.4 active-" ++
      "floor count, further reduced by towerSubMass_of_failure to the K.1.1 cover + I.4.1 dense-" ++
      "marker packing + K.4 smallness (genuinely consuming ctx.hfailure).",
    "SHARPEST OPEN (Run) — RunClass5StageChain ctx (TowerRunMassBoundCore.lean): the L.4.2 period-" ++
      "descent chain (hsum/hhalf/hbase). Further reducible to the 3-field RunClass5GenuineLeaf " ++
      "(I.6S charge map + finite L.4.2 half-decrease + §26 base run-area cover, RunClass5GenuineLeaf.lean).",
    "SCOPE — providers are over ActualFailureContext (the GlobalAssemblyActualInputs index of the " ++
      "honest reduction erdos260_final_actual), the pinned LARGE failing shells where the carry data " ++
      "ctx.n24CarryData and the routed fibres are available; this is the genuine interface, not the " ++
      "all-shells GlobalAssemblyCoreInputs shape (whose small-shell totality filler is degenerate)." ]

theorem towerRunUnconditionalProviderResiduals_nonempty :
    towerRunUnconditionalProviderResiduals ≠ [] := by
  simp [towerRunUnconditionalProviderResiduals]

/-! ## Part E — axiom‑cleanliness audit -/

#print axioms towerFactoryOfSlot
#print axioms runFactoryOfSlot
#print axioms towerFactoryOfSlot_entryExitSet
#print axioms towerFactoryOfSlot_termTower
#print axioms runFactoryOfSlot_runMass
#print axioms runFactoryOfSlot_runMass_nonneg
#print axioms towerFactoryOfSlot_bound
#print axioms runFactoryOfSlot_bound
#print axioms TowerRunGenuineResidual.tower
#print axioms TowerRunGenuineResidual.run
#print axioms TowerRunGenuineResidual.run_runMass_nonneg
#print axioms towerProviderOfSeed
#print axioms runProviderOfSeed
#print axioms runProviderOfSeed_runMass_nonneg

end

end Erdos260
