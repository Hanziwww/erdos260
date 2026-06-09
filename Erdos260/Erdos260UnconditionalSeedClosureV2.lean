import Erdos260.ActiveWindowContainmentCore
import Erdos260.ReturnNestingCountCore
import Erdos260.TowerRunMassBoundCore
import Erdos260.ChernoffChargeMapCore
import Erdos260.CNLKraftCountCore
import Erdos260.DensePackCoverCore

/-!
# Erdős #260 — the CORRECTED, tightened wave-10 seed closure (`Erdos260UnconditionalSeedClosureV2`)

This module (NEW; it edits no existing file) is the **wave-10 integration capstone**.  Six sibling
workers each shrank/closed assigned cores of the wave-9 frontier residual `Erdos260MinimalResidual`
(`Erdos260UnconditionalSeedClosure.lean`).  Here those wave-10 residual cores are bundled into one
**corrected, tightened** minimal residual `Erdos260MinimalResidualV2` and the tightened endpoint

```
erdos260_of_minimalResidualV2 : Erdos260MinimalResidualV2 → Erdos260Statement
```

is assembled, routing through the existing `erdos260_seed_reduced_ofDensePackSeed`.

## Two genuine improvements over the wave-9 `erdos260_of_minimalResidual`

1. **The three active-window containment cores are now ONE shared residual.**  Wave-9 carried the
   Chernoff (Core 8), clean-CNL (Core 10), and DensePack (Core 13) `hwin`/`hContain` existentials as
   three independent opaque fields.  Worker 1 (`ActiveWindowContainmentCore`) proved the carry start
   set IS the dyadic shell index window (`n24Starts_eq_window`, by `rfl`) and `r+1 ≤ K`
   (`r_add_one_le_width`), reducing all three to the single clean geometric **`WindowInteriorResidual`**
   (the routed high-excess starts of each class stay `r+1` below the top of the shell window).  The
   per-class containment fields are then *discharged outright* from it (`chernoffHwin`, `cnlHwin`,
   `densePackContain`).  Here the V2 residual carries that ONE shared `window` field and feeds it to
   the Chernoff (Core 8) and DensePack (Core 13) builders, with Core 10 the same shared geometry.

2. **The clean-CNL Core 11 is the HONEST per-codeword matched Kraft charge — NOT the false
   worst-case collapse.**  Worker 5 (`CNLKraftCountCore`) PROVED `cnl_hbudget_iff_r_zero`: the wave-9
   `Class1CNLSeedCore.hbudget` (the single uniform scalar budget `cnlActiveMult ctx ≤ cnlMinKraftRate
   ctx`) holds **iff `ctx.n24CarryData.r = 0`** — i.e. it is *provably false* for every deep shell
   (`r ≥ 1`, where `cnlActiveMult ≥ 2·carryB Q + 1 ≥ 3 > 1 ≥ cnlMinKraftRate`).  So routing the CNL
   class through `Class1CNLSeedCore.toInjection` (which demands that collapse) makes the residual
   *vacuous* on deep shells.  Instead V2 carries the genuine `Class1CNLInjection` directly — the
   per-codeword **matched** Kraft charge `hcap : mult ≤ 2^{-BND(g k)}·shellFactor·X·|I_j|` (charging
   each class-1 start against *its own* codeword's Kraft rate, `windowExcess_le_cap_chargeOf_on_routedFibre`,
   the rate bounded by the proved Kraft sum `cnlBudgetOfShell`).  Its active-window gap multiplier
   `g₀`/`mult` are genuine residual fields (the *sharp* gap on the contained window), NOT pinned to
   the worst-case `cnlActiveScale`/`cnlActiveMult`, so the residual is satisfiable on deep shells.

## The corrected minimal residual `Erdos260MinimalResidualV2`

| field | wave-10 worker | the irreducible manuscript core(s) it carries |
| --- | --- | --- |
| `returnNesting` | `ReturnNestingCountCore` | `ReturnNestingCountSeed ctx`: the M.2.1 self-referential nesting-level assignment (Core 1) + the K.1.2 active-window gap structure (Core 2). |
| `towerCover` | `TowerRunMassBoundCore` | `Class2DenseMarkerCover ctx`: the I.4.1 dense-marker existence/packing (Core 3), multiplier pinned to the genuine active floor `positivePart (2·Y)`. |
| `runChain` | `TowerRunMassBoundCore` | `RunClass5StageChain ctx`: the I.6S charged summability + L.4.2 half-decrease (Core 4) + the I.5.2 base run output (Core 5). |
| `window` | `ActiveWindowContainmentCore` | `WindowInteriorResidual budget`: the SHARED active-window containment (Cores 8 / 10 / 13 unified) — routed high-excess starts avoid the top `r+1` of the shell window. |
| `chernoffCard` | `ChernoffChargeMapCore` | the I.4.2 progress count `|routedFibre 0| ≤ |highCostSet …| = 4` (Core 6). |
| `chernoffArea` | `ChernoffChargeMapCore` | the 22.1A area calibration `(r+1)·(L+B+1) − T ≤ 1/4` (Core 7). |
| `cnl` | `ChernoffCNLChargeInjectionCore` | `Class1CNLInjection budget`: the L.1.2 cluster-reconstruction charge map (Core 9) + the CORRECTED per-codeword matched Kraft charge `hcap` (Core 11). |
| `densePackSupport` | `DensePackCoverCore` | `DensePackCoareaSupport budget ctx`: the K.1.3/K.1.4 bare coarea support identity (Core 12). |
| `densePackFloor` | `DensePackCoverCore` | the K.1.2 active-floor calibration `T ≥ (r+1)·(L+B+1) − 1` (Core 14). |

The budget is **forced** to `genuineChargeRoute` (it is the combined `buildSeedTRT`'s `.toBudget`).

No `sorry`/`axiom`/`admit`/`native_decide`; no degenerate/empty/full-mass shortcut; the CNL class is
the genuine per-codeword charge, never the `r = 0` collapse.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The combined wave-10 seed budget

The budget is assembled from worker `ReturnNestingCountCore` (the Return Cores 1/2 → a per-context
`ReturnClass4SeedResidual` via `returnSeedOfNesting`) and worker `TowerRunMassBoundCore` (the Tower
Core 3 + Run Cores 4/5 → a `TowerRunSeedClosureData` via `buildTowerRunSeedClosure`), through the
existing `buildSeedTRT`.  Its `.route` is `genuineChargeRoute` by `rfl`. -/

/-- **The combined wave-10 seed budget**, over the genuine first-obstruction route
`genuineChargeRoute`.  Built from the Return nesting+gap seeds (Cores 1/2) and the Tower/Run
mass-bound seeds (Cores 3/4/5). -/
def v2Budget
    (returnNesting : ∀ ctx : ActualFailureContext, ReturnNestingCountSeed ctx)
    (towerCover : ∀ ctx : ActualFailureContext, Class2DenseMarkerCover ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  (buildSeedTRT (returnSeedOfNesting returnNesting)
    (buildTowerRunSeedClosure towerCover runChain)).toBudget

/-- The combined wave-10 seed budget routes through the genuine first-obstruction route. -/
@[simp] theorem v2Budget_route
    (returnNesting : ∀ ctx : ActualFailureContext, ReturnNestingCountSeed ctx)
    (towerCover : ∀ ctx : ActualFailureContext, Class2DenseMarkerCover ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (ctx : ActualFailureContext) :
    (v2Budget returnNesting towerCover runChain ctx).route = genuineChargeRoute ctx := rfl

/-! ## 2.  The corrected, tightened minimal residual -/

/-- **The corrected wave-10 minimal residual of Erdős #260.**

Bundles ONLY the genuine deep manuscript inputs surviving the six wave-10 workers, each as a small
residual core, with the three active-window containment cores UNIFIED into the shared `window`, and
the clean-CNL Core 11 carried as the honest per-codeword matched Kraft charge (the genuine
`Class1CNLInjection`), never the `r = 0`-only worst-case collapse. -/
structure Erdos260MinimalResidualV2 where
  /-- **Return (class 4) — Cores 1/2.**  The M.2.1 self-referential nesting-level assignment +
  the K.1.2 active-window gap structure (`ReturnNestingCountSeed`). -/
  returnNesting : ∀ ctx : ActualFailureContext, ReturnNestingCountSeed ctx
  /-- **Tower (class 2) — Core 3.**  The I.4.1 dense-marker existence/packing cover, multiplier
  pinned to the genuine active floor `positivePart (2·Y)` (`Class2DenseMarkerCover`). -/
  towerCover : ∀ ctx : ActualFailureContext, Class2DenseMarkerCover ctx
  /-- **Run (class 5) — Cores 4/5.**  The L.4.2 half-decreasing stage chain: the I.6S summability +
  half-decrease (Core 4) and the I.5.2 base run output (Core 5) (`RunClass5StageChain`). -/
  runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx
  /-- **Active-window containment (Cores 8 / 10 / 13 UNIFIED) — the shared residual.**  The routed
  high-excess starts of every class (Chernoff, clean-CNL, DensePack) stay `r+1` below the top of the
  dyadic shell index window (`WindowInteriorResidual`).  The three wave-9 per-class `hwin`/`hContain`
  existentials collapse to this ONE clean geometric residual. -/
  window : WindowInteriorResidual (v2Budget returnNesting towerCover runChain)
  /-- **Chernoff (class 0) — Core 6.**  The I.4.2 progress count `|routedFibre 0| ≤ |highCostSet …|`
  (= 4) of the J.1.7 charge into the genuine §22 four-path high-cost family. -/
  chernoffCard : ∀ ctx : ActualFailureContext,
    (routedFibre ctx.n24CarryData ((v2Budget returnNesting towerCover runChain) ctx).route 0).card
      ≤ (highCostSet
          ((faithfulCapacityPhases (v2Budget returnNesting towerCover runChain) ctx).toClosurePhaseData).chernoff.paths
          ((faithfulCapacityPhases (v2Budget returnNesting towerCover runChain) ctx).toClosurePhaseData).chernoff.cost
          ((faithfulCapacityPhases (v2Budget returnNesting towerCover runChain) ctx).toClosurePhaseData).chernoff.Y).card
  /-- **Chernoff (class 0) — Core 7.**  The 22.1A area calibration `(r+1)·(L+B+1) − T ≤ 1/4` (the
  active floor is dominated by the §22 model leaf's minimum high-cost area weight `1/4`). -/
  chernoffArea : ∀ ctx : ActualFailureContext,
    ((ctx.n24CarryData.r : ℝ) + 1) * (class0ShellGapScale ctx : ℝ) - ctx.n24CarryData.T ≤ (1 : ℝ) / 4
  /-- **Clean-CNL (class 1) — Cores 9 & CORRECTED 11.**  The genuine `Class1CNLInjection`: the L.1.2
  cluster-reconstruction charge map `g`/`hmem`/`hinj` (Core 9; the count is derived via
  `fibre_card_le` / `cnl_hcard_of_injOn`), and the HONEST per-codeword matched Kraft charge
  `hcap : mult ≤ 2^{-BND(g k)}·shellFactor·X·|I_j|` (the corrected Core 11), with the active-window
  gap multiplier `g₀`/`mult` genuine residual fields — NOT the wave-9 false collapse
  `cnlActiveMult ≤ cnlMinKraftRate` (which `cnl_hbudget_iff_r_zero` proves false for `r ≥ 1`). -/
  cnl : Class1CNLInjection (v2Budget returnNesting towerCover runChain)
  /-- **DensePack (class 3) — Core 12.**  The bare K.1.3/K.1.4 coarea support identity (the first-stop
  owner + representative marker, with endpoint-disjointness structural) (`DensePackCoareaSupport`). -/
  densePackSupport : ∀ ctx : ActualFailureContext,
    DensePackCoareaSupport (v2Budget returnNesting towerCover runChain) ctx
  /-- **DensePack (class 3) — Core 14.**  The K.1.2 active-floor calibration `T ≥ (r+1)·(L+B+1) − 1`
  (equivalent to the J.D unit charge `windowExcess ≤ 1` via `densePackScale_iff_floorLe`). -/
  densePackFloor : ∀ ctx : ActualFailureContext,
    densePackActiveFloor ctx - 1 ≤ ctx.n24CarryData.T

namespace Erdos260MinimalResidualV2

/-- The combined seed-level Tower+Return+Run data (Cores 1–5), over `genuineChargeRoute`. -/
def trt (R : Erdos260MinimalResidualV2) : SeedTRTData :=
  buildSeedTRT (returnSeedOfNesting R.returnNesting)
    (buildTowerRunSeedClosure R.towerCover R.runChain)

/-- **The class-0 Chernoff injection (Cores 6 + 7 + 8), built from the V2 residual.**  The J.1.7
charge map and area cap are constructed by `Class0ChernoffSeedCore.ofCountWindowArea` from the
progress count (Core 6) and the area calibration (Core 7), with the active-window containment (Core 8)
discharged from the SHARED window interior (`window.chernoffHwin`). -/
def chernoffInjection (R : Erdos260MinimalResidualV2) :
    Class0ChernoffInjection (v2Budget R.returnNesting R.towerCover R.runChain) :=
  (Class0ChernoffSeedCore.ofCountWindowArea
    (v2Budget R.returnNesting R.towerCover R.runChain)
    R.chernoffCard R.window.chernoffHwin R.chernoffArea).toInjection

/-- **The DensePack class-3 seed (Cores 12 + 13 + 14), built from the V2 residual.**  The K.1.3/K.1.4
endpoint-disjoint cover from the coarea support identity (Core 12, `coverField_ofCoareaSupport`); the
active-window containment from the SHARED window interior (Core 13, `window.densePackContain`, maximal
uniform reach `K − 1`); the K.1.2 active-floor calibration from the threshold floor (Core 14,
`densePackScaleField_of_floorLe`). -/
def densePackSeed (R : Erdos260MinimalResidualV2) :
    DensePackK11Seed (v2Budget R.returnNesting R.towerCover R.runChain) where
  cover := coverField_ofCoareaSupport (v2Budget R.returnNesting R.towerCover R.runChain) R.densePackSupport
  windowReach := densePackWindowReach
  hReach := densePackWindowReach_add_one_le
  hContain := R.window.densePackContain
  hScale := densePackScaleField_of_floorLe R.densePackFloor

end Erdos260MinimalResidualV2

/-- **Erdős #260, reduced to the corrected wave-10 minimal residual.**

From `Erdos260MinimalResidualV2` — the genuine route `genuineChargeRoute`; the Return M.2.1 nesting
count + K.1.2 gap (Cores 1/2); the Tower I.4.1 sub-mass (Core 3) + Run I.6S/I.5.2 bounds (Cores 4/5);
the SHARED active-window containment (Cores 8/10/13 unified); the Chernoff 22.1A progress count + area
cap (Cores 6/7); the clean-CNL L.1.2 cluster reconstruction (Core 9) + the HONEST per-codeword matched
Kraft charge (Core 11, NOT the `r=0` collapse); and the DensePack K.1.3/K.1.4 coarea support (Core 12)
+ K.1.2 active-floor calibration (Core 14) — the frontier endpoint `erdos260_seed_reduced_ofDensePackSeed`
proves `Erdos260Statement`.

No `sorry`/`axiom`/`admit`/`native_decide`; the CNL class is the genuine per-codeword charge, never
the worst-case collapse. -/
theorem erdos260_of_minimalResidualV2 (R : Erdos260MinimalResidualV2) : Erdos260Statement :=
  erdos260_seed_reduced_ofDensePackSeed R.trt R.chernoffInjection R.cnl R.densePackSeed

/-! ## 3.  The CNL correction, made explicit

The clean-CNL class is discharged through the genuine per-codeword matched Kraft charge, not the
false worst-case collapse.  The two facts below confirm the corrected path: the L.1.2 count (Core 9)
is *derived* from the carried cluster-reconstruction injection, and the exact CNL ledger field is
produced by the matched charge — neither needs the `r = 0` budget. -/

/-- **The L.1.2 bounded-multiplicity count (Core 9), DERIVED from the V2 CNL injection.**  The class-1
fibre injects into the surviving clean-CNL family via the carried cluster-reconstruction map, so its
count is bounded by the family count — exactly the `cnl_hcard_of_injOn` content
(`Class1CNLInjection.fibre_card_le`), not assumed. -/
theorem Erdos260MinimalResidualV2.cnl_count (R : Erdos260MinimalResidualV2)
    (ctx : ActualFailureContext) :
    (routedFibre ctx.n24CarryData
        ((v2Budget R.returnNesting R.towerCover R.runChain) ctx).route 1).card
      ≤ (selectedTransitions (liftTransitionsOfShell ctx)).card :=
  R.cnl.fibre_card_le ctx

/-- **The exact clean-CNL ledger field, from the per-codeword matched Kraft charge.**  The carried
`Class1CNLInjection` discharges `routedClassMassOf … 1 ≤ termCnl` through the per-codeword charge
domination (`Class1CNLInjection.hcharge` / `hCnlField`), with NO appeal to the false worst-case
budget `cnlActiveMult ≤ cnlMinKraftRate`. -/
theorem Erdos260MinimalResidualV2.cnl_ledger (R : Erdos260MinimalResidualV2)
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData
        ((v2Budget R.returnNesting R.towerCover R.runChain) ctx).route 1
      ≤ termCnl (faithfulCapacityPhases (v2Budget R.returnNesting R.towerCover R.runChain) ctx).toClosurePhaseData :=
  R.cnl.hCnlField ctx

/-- **The clean-CNL Core 10 containment, from the SHARED window interior.**  The class-1 active-window
containment (Core 10) is the same shared `WindowInteriorResidual.cnlInterior` geometry that discharges
Chernoff Core 8 and DensePack Core 13 — the three are one residual. -/
theorem Erdos260MinimalResidualV2.cnl_window_interior (R : Erdos260MinimalResidualV2)
    (ctx : ActualFailureContext) :
    ∀ k ∈ routedFibre ctx.n24CarryData
        ((v2Budget R.returnNesting R.towerCover R.runChain) ctx).route 1,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.window.cnlInterior ctx

/-! ## 4.  The FINAL post-wave-10 irreducible residual surface (one entry per surviving core) -/

/-- The precise per-core status of the corrected wave-10 seed closure: the FINAL irreducible surface
of Erdős #260 after wave-10, every class reduced to its smallest honest manuscript core, with the
three containment cores UNIFIED and the clean-CNL Core 11 the genuine per-codeword matched charge. -/
def erdos260UnconditionalSeedClosureV2Residuals : List String :=
  [ "CORE 1 (Return, class 4 — M.2.1 nesting-level assignment) — returnNesting ctx |>.level/hbound/" ++
      "hchain/hinj (equivalently the crossing-free + consecutive-separation inputs via ofCrossingFree): " ++
      "the self-referential lift-congruent injective level map of the genuine long-return fibre. " ++
      "ABOVE IT PROVED (ReturnNestingCountCore): the M.2.1 count machinery " ++
      "card_le_liftLevelBound_of_liftChainLevels + the Erdős–Szekeres crossing/nesting alternative " ++
      "(liftSep_of_crossingFree_consecutive), giving |routedFibre 4| ≤ liftLevelBound X.",
    "CORE 2 (Return, class 4 — K.1.2 active-window gap) — returnNesting ctx |>.windowReach/hReach/" ++
      "hContain (active-window containment, the hfibre_win residual) + hScale ((r+1)·(L+B+1) − T ≤ 1, " ++
      "the J.D unit-charge active-floor calibration). ABOVE IT PROVED: hgap from the dyadic scale " ++
      "(return_hgap_ofContainment = hitGap_le_densePackDyadicG0_of_window).",
    "CORE 3 (Tower, class 2 — I.4.1 dense-marker existence/packing) — towerCover ctx : " ++
      "Class2DenseMarkerCover (hbdry: 0 ∉ class-2 fibre; hcover: K.1.1 endpoint-disjoint cover " ++
      "|fibre 2| ≤ |𝒟₀|·(2 spread+1); hpack: I.4.1 dense-marker hit packing |𝒟₀|·ρ_D·L ≤ #supportShell; " ++
      "hsmall: K.4 numeric (c₀/ρ_D·L)·(2 spread+1)·(2·Y) ≤ ξ/6). ABOVE IT PROVED (TowerRunMassBoundCore): " ++
      "the K.1.2/L.20 multiplier PINNED to the genuine active floor positivePart (2·Y) " ++
      "(class2_windowExcess_lt_twoY), discharging routedClassMassOf 2 ≤ ξX/6 via towerSubMass_of_failure.",
    "CORE 4 (Run, class 5 — I.6S charged summability) — runChain ctx |>.hsum + hhalf : the class-5 " ++
      "routed mass is the sum of the actual descent-stage masses stageMass i, contracting by 1/2 " ++
      "(the L.4.2 half-decrease, anchored in seedRun_periodDescent_halfDecrease). ABOVE IT PROVED: " ++
      "the geometric envelope stageMass i ≤ stageMass 0·(1/2)^i (stageMass_le_geom), giving " ++
      "RunClass5StageChain.hrunSum.",
    "CORE 5 (Run, class 5 — I.5.2 base run output) — runChain ctx |>.hbase : stageMass 0 = wt(O₀) " ++
      "≤ c⋆ξX/12, the L.4.2 period-descent base output bound.",
    "CORES 8 / 10 / 13 UNIFIED (active-window containment — ONE shared residual) — window : " ++
      "WindowInteriorResidual (chernoffInterior / cnlInterior / densePackInterior): the routed " ++
      "high-excess starts of EACH class stay r+1 below the top of the dyadic shell index window " ++
      "(k + r + 1 < firstIndexAbove X + |supportShell d X|). The three wave-9 per-class hwin/hContain " ++
      "existentials are now ONE clean geometric residual; chernoffHwin (Core 8), cnlHwin (Core 10), " ++
      "densePackContain (Core 13) DISCHARGE the exact original field shapes from it. ABOVE IT PROVED " ++
      "(ActiveWindowContainmentCore): n24Starts_eq_window (starts = the Ico window, by rfl) + " ++
      "r_add_one_le_width (r+1 ≤ K) + the general windowContainment_of_interior; the failing complement " ++
      "is the ≤ r+1 boundary term (windowBoundary_card_le), the manuscript K.1 endpoint-enlargement.",
    "CORE 6 (Chernoff, class 0 — I.4.2 progress count) — chernoffCard : |routedFibre 0| ≤ " ++
      "|highCostSet …| = 4 (class0_highCostFamily_card). ABOVE IT PROVED (ChernoffChargeMapCore): the " ++
      "J.1.7 charge map class0ChargeMap (order-rank matching into the genuinely-nonempty four-path §22 " ++
      "model leaf) with hmaps (22.1A shell-paid embedding) and hinj (K.1.3 disjointness) DERIVED from " ++
      "the count via finRankMatch_mem/finRankMatch_injOn.",
    "CORE 7 (Chernoff, class 0 — 22.1A area-positive cap) — chernoffArea : (r+1)·(L+B+1) − T ≤ 1/4. " ++
      "ABOVE IT PROVED: the genuine §22 area weight 2^{−cost} ≥ 1/4 on the high-cost family " ++
      "(class0_chernoffWeight_ge_quarter, the σ=(1,1) worst case), giving hcapPos via " ++
      "class0_hcapPos_ofArea.",
    "CORE 9 (clean-CNL, class 1 — L.1.2 bounded-multiplicity count) — cnl.g/hmem/hinj : the genuine " ++
      "cluster-reconstruction charge map of the class-1 fibre into the proved-nonempty surviving " ++
      "clean-CNL family selectedTransitions (liftTransitionsOfShell ctx). The L.1.2 count " ++
      "|routedFibre 1| ≤ |family| is DERIVED (Erdos260MinimalResidualV2.cnl_count = " ++
      "Class1CNLInjection.fibre_card_le, the cnl_hcard_of_injOn content), not assumed.",
    "CORE 10 (clean-CNL, class 1 — K.1.2 active-window containment) — = window.cnlInterior " ++
      "(Erdos260MinimalResidualV2.cnl_window_interior). UNIFIED into the shared WindowInteriorResidual " ++
      "above; the same geometry as Chernoff Core 8 and DensePack Core 13.",
    "CORE 11 CORRECTED (clean-CNL, class 1 — G.6/L.20 per-codeword matched Kraft charge) — " ++
      "cnl.hcap : mult ≤ 2^{−BND(g k)}·shellFactor·X·|I_j| (the matched per-codeword Kraft rate, with " ++
      "the active-window gap multiplier g₀/mult genuine residual fields, the SHARP gap on the contained " ++
      "window). This REPLACES the wave-9 worst-case collapse cnlActiveMult ctx ≤ cnlMinKraftRate ctx, " ++
      "which cnl_hbudget_iff_r_zero PROVES holds iff r = 0 — i.e. provably FALSE on every deep shell " ++
      "(r ≥ 1: cnlActiveMult ≥ 2·carryB Q+1 ≥ 3 > 1 ≥ cnlMinKraftRate). The matched charge is bounded " ++
      "by the PROVED Kraft sum cnlBudgetOfShell (2^M·shellFactor·|I_j| ≤ c⋆ξ/6) and is satisfiable on " ++
      "deep shells; windowExcess_le_cap_chargeOf_on_routedFibre turns hcap into the per-element charge, " ++
      "and Class1CNLInjection.hCnlField discharges routedClassMassOf 1 ≤ termCnl (cnl_ledger).",
    "CORE 12 (DensePack, class 3 — K.1.3/K.1.4 coarea support identity) — densePackSupport ctx : " ++
      "DensePackCoareaSupport (owner + markerOf with marker_owned (first-stop section) + marker_lands " ++
      "(K.1.4 landing)). ABOVE IT PROVED (DensePackCoverCore): the terminal endpoint sets are owner " ++
      "fibres so K.1.3 endpoint-disjointness is STRUCTURAL (toEndpointCover), the marker injectivity " ++
      "is the retraction markerOf_injOn, and the count |genuineDensePackStarts| ≤ |densePackMarkers| " ++
      "is derived; densePackCoareaSupport_iff_count shows it is EXACTLY the count (not weaker).",
    "CORE 14 (DensePack, class 3 — K.1.2 active-floor calibration) — densePackFloor : T ≥ " ++
      "densePackActiveFloor ctx − 1 = (r+1)·(L+B+1) − 1 (EXACTLY hScale (r+1)·(L+B+1) − T ≤ 1 via " ++
      "densePackScale_iff_floorLe). ABOVE IT PROVED: it is orthogonal to hAlloc (which bounds T only " ++
      "from above, n24CarryData_threshold_upper) and discharges the J.D unit charge windowExcess ≤ 1 " ++
      "(densePack_unit_charge_of_floorLe).",
    "ASSEMBLED ABOVE THE CORES — v2Budget = buildSeedTRT (returnSeedOfNesting returnNesting) " ++
      "(buildTowerRunSeedClosure towerCover runChain) |>.toBudget (Cores 1–5 → SeedTRTData over " ++
      "genuineChargeRoute, NO free Tower/Run count); chernoffInjection = " ++
      "Class0ChernoffSeedCore.ofCountWindowArea (Cores 6/7 + shared window Core 8) |>.toInjection; " ++
      "cnl carried directly (the genuine Class1CNLInjection, Cores 9/11); densePackSeed from the " ++
      "coarea support (Core 12) + shared window (Core 13) + floor (Core 14); " ++
      "erdos260_seed_reduced_ofDensePackSeed assembles the full Erdos260SeedResidual and reaches " ++
      "Erdos260Statement (joint N.24 TRT compression + class-6 closure inside erdos260_seed_reduced).",
    "ENDPOINT — erdos260_of_minimalResidualV2 : Erdos260MinimalResidualV2 → Erdos260Statement. The " ++
      "route is FORCED to genuineChargeRoute; the three active-window cores are ONE shared " ++
      "WindowInteriorResidual; the clean-CNL Core 11 is the genuine per-codeword matched Kraft charge " ++
      "(NOT the false worst-case collapse). Cores 1,2,3,4,5,6,7,9,11,12,14 + the unified containment " ++
      "8/10/13 are the irreducible manuscript input geometry of a fully unconditional Erdős #260." ]

theorem erdos260UnconditionalSeedClosureV2Residuals_nonempty :
    erdos260UnconditionalSeedClosureV2Residuals ≠ [] := by
  simp [erdos260UnconditionalSeedClosureV2Residuals]

/-! ## 5.  Axiom-cleanliness audit -/

#print axioms v2Budget
#print axioms Erdos260MinimalResidualV2.trt
#print axioms Erdos260MinimalResidualV2.chernoffInjection
#print axioms Erdos260MinimalResidualV2.densePackSeed
#print axioms erdos260_of_minimalResidualV2
#print axioms Erdos260MinimalResidualV2.cnl_count
#print axioms Erdos260MinimalResidualV2.cnl_ledger
#print axioms Erdos260MinimalResidualV2.cnl_window_interior

end

end Erdos260
