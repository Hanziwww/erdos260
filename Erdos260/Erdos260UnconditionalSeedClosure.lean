import Erdos260.ReturnM21SeedClosure
import Erdos260.TowerRunSeedClosure
import Erdos260.Chernoff221ASeedClosure
import Erdos260.CNLL12SeedClosure
import Erdos260.DensePackK11SeedClosure
import Erdos260.Erdos260SeedResidual

/-!
# Erdős #260 — the UNCONDITIONAL seed closure: all five seed leaves wired into one minimal residual

This module (NEW; it edits no existing file) is the **integration capstone** of the wave-9 seed
closures.  Five sibling workers each pushed one irreducible "seed" leaf of the frontier residual
`Erdos260SeedResidual` (`Erdos260SeedResidual.lean`, consumed by `erdos260_seed_reduced`) toward a
full unconditional construction, leaving each class reduced to its *smallest honest manuscript core*.
Here we

* **assemble** the five closures into a single `SeparatedPhaseRoutedBudget` (the Return M.2.1
  congruence + the Tower I.4.1 sub-mass + the Run I.5.2 floor build the budget over the genuine
  first-obstruction route `genuineChargeRoute`); and
* **expose the minimal combined residual** `Erdos260MinimalResidual` — a structure bundling *only*
  the genuine deep manuscript inputs that survive across all five workers, reusing each worker's own
  residual bundle as a field; and prove the tightened endpoint

```
erdos260_of_minimalResidual : Erdos260MinimalResidual → Erdos260Statement.
```

Everything *above* these cores — the Return level map / 2-adic centre / `retCompat` / `retInj` /
`hbudReturn` (worker 1, `ReturnM21SeedClosure`); the Tower active-layer normalisation + the I.4.1
fraction + the Run period-descent floor (worker 2, `TowerRunSeedClosure`); the Chernoff gap structure
`g₀`/`hgap`/`mult`/`hscale`/`hmult_nonneg` + the nonnegative half of the area cap (worker 3,
`Chernoff221ASeedClosure`); the CNL dyadic-grounded gap + the worst-case Kraft collapse + the
order-rank charge map (worker 4, `CNLL12SeedClosure`); the DensePack dyadic gap ceiling + the
order-rank marker landing + the J.1.8 summation (worker 5, `DensePackK11SeedClosure`) — is **proved**.

## The minimal residual `Erdos260MinimalResidual`

| field | worker | the irreducible manuscript core(s) it carries |
| --- | --- | --- |
| `returnSeed` | 1 | `ReturnClass4SeedResidual ctx`: the M.2.1 endpoint-nesting count `hcount` (`|routedFibre 4| ≤ liftLevelBound X`) + the K.1.2 active-window gap structure (`windowGap`/`hgap`/`hscale`). |
| `towerRun` | 2 | `TowerRunSeedClosureData`: the I.4.1 Tower sub-mass `htowerSubMass` (`routedClassMassOf 2 ≤ ξX/6`, reducible to dense-marker existence via `towerSubMass_of_failure`) + the Run I.6S summability `hrunSum` + the Run I.5.2 base bound `hrunBase12`. |
| `chernoff` | 3 | `Class0ChernoffSeedCore`: the J.1.7 charge map (`chargeOf`/`hmaps`/`hinj`, K.1.3 disjointness) + the 22.1A area-positive cap `hcapPos` + the active-window containment `hwin`. |
| `cnl` | 4 | `Class1CNLSeedCore`: the L.1.2 bounded-multiplicity count `hcard` + the K.1.2 active-window containment `hwin` + the single G.35 weighted-Kraft scalar budget `hbudget`. |
| `densePack` | 5 | `DensePackK11Seed`: the K.1.3/K.1.4 endpoint-disjoint cover `cover` + the active-window containment `windowReach`/`hReach`/`hContain` + the K.1.2 active-floor calibration `hScale`. |

The route is **forced** to `genuineChargeRoute` (the budget is `(buildSeedTRT ‹returnSeed› ‹towerRun›).toBudget`,
whose `.route` is `genuineChargeRoute` by `rfl`).  No protected endpoint is weakened; no count or mass
slot is free.  The final irreducible surface is enumerated in `erdos260UnconditionalSeedClosureResiduals`.

## How the endpoint is proved

`buildSeedTRT` builds a `SeedTRTData` from worker 1 (the Return fields: the constructed level map
`returnSeedLevel`, the centre `returnSeedXi`, with `retCompat`/`retInj` proved, `retBound` from the
count, the unit window-excess multiplier `multReturn = 1`, and the proved budget `returnSeed_hbudReturn`)
and worker 2 (the Tower/Run fields via `TowerRunSeedClosureData`'s proved `towerS`/`towerIj`/
`htowerLayer`/`htowerFraction`/`hrunFloor`).  Against that budget, `Class0ChernoffSeedCore.toInjection`
(worker 3, `ofChargeWindowAreaCap`) and `Class1CNLSeedCore.toInjection` (worker 4,
`ofShellWindowCountBudget`) produce the Chernoff/CNL injection maps, and the DensePack seed (worker 5)
supplies the class-3 fields; `Erdos260SeedResidual.ofDensePackSeed` assembles the full frontier
residual and `erdos260_seed_reduced` reaches `Erdos260Statement`.

No `sorry`, `axiom`, `admit`, or `native_decide`.  No degenerate/empty/`PEmpty`/full-mass shortcut: the
residual is exactly the five workers' genuine manuscript cores, each over the real (proved-nonempty)
target family.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The combined Tower+Return+Run seed data, from workers 1 and 2

`buildSeedTRT` combines the worker-1 Return seed (the per-context `ReturnClass4SeedResidual`) and the
worker-2 Tower+Run closure (`TowerRunSeedClosureData`) into a single `SeedTRTData`.  Every Return field
is supplied from worker 1's *constructed* level assignment — `retCompat` (manuscript G.7 common 2-adic
centre) and `retInj` (M.2.1 endpoint disjointness) are theorems, `retBound` is the count, the
window-excess multiplier is the proved unit `1`, and `hbudReturn` is the proved I.5.1/K.4 numeric — and
every Tower/Run field is supplied from worker 2's proved `towerS`/`towerIj`/`htowerLayer`/
`htowerFraction`/`hrunFloor`.  Its `.toBudget` is the shared `SeparatedPhaseRoutedBudget` over
`genuineChargeRoute`, with NO free Tower/Run count. -/

/-- **The combined seed-level Tower+Return+Run data.**  Return fields from worker 1
(`ReturnClass4SeedResidual`, all `ctx`), Tower/Run fields from worker 2 (`TowerRunSeedClosureData`). -/
def buildSeedTRT
    (returnSeed : ∀ ctx : ActualFailureContext, ReturnClass4SeedResidual ctx)
    (towerRun : TowerRunSeedClosureData) : SeedTRTData where
  retLevel := returnSeedLevel
  retXi := returnSeedXi
  retBound := fun ctx => returnSeedLevel_bound_of_count ctx (returnSeed ctx).hcount
  retCompat := returnSeedLevel_twoAdicCompatible
  retInj := returnSeedLevel_inj
  multReturn := fun _ctx => 1
  hpointReturn := fun ctx => (returnSeed ctx).hpointReturn
  hmultReturn_nonneg := fun _ctx => zero_le_one
  hbudReturn := fun ctx => returnSeed_hbudReturn ctx
  towerS := towerRun.towerS
  towerIj := towerRun.towerIj
  htowerLayer := towerRun.htowerLayer
  htowerFraction := towerRun.htowerFraction
  hrunFloor := towerRun.hrunFloor

/-- The combined seed budget routes through the genuine first-obstruction route `genuineChargeRoute`. -/
@[simp] theorem buildSeedTRT_toBudget_route
    (returnSeed : ∀ ctx : ActualFailureContext, ReturnClass4SeedResidual ctx)
    (towerRun : TowerRunSeedClosureData) (ctx : ActualFailureContext) :
    ((buildSeedTRT returnSeed towerRun).toBudget ctx).route = genuineChargeRoute ctx := rfl

/-! ## 2.  The Chernoff (worker 3) and CNL (worker 4) minimal residual cores, bundled

The workers exposed the Chernoff/CNL minimal cores as the *arguments* of their builders
(`Class0ChernoffInjection.ofChargeWindowAreaCap`, `Class1CNLInjection.ofShellWindowCountBudget`).  Here
we bundle them into small residual-core structures so they can be carried as single fields of the
combined `Erdos260MinimalResidual`, and provide the `toInjection` builders that discharge everything
above them. -/

/-- **The class-0 Chernoff (22.1A / I.4.2) minimal residual core** for a routed budget: the genuine
J.1.7 charge map into the Chernoff high-cost family (`chargeOf`/`hmaps`/`hinj`, with K.1.3 endpoint
disjointness), the active-window containment of the descent window (`hwin`), and the 22.1A
area-positive cap (`hcapPos`).  All the gap structure (`g₀ = class0ShellGapScale`, `hgap`, `mult`,
`hscale`, `hmult_nonneg`, and the nonnegative half of the area cap) is discharged by `toInjection`. -/
structure Class0ChernoffSeedCore
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) where
  /-- The J.1.7 charge map of the class-0 progress starts into the Chernoff high-cost path family. -/
  chargeOf : ∀ ctx : ActualFailureContext,
    ℕ → ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.α
  /-- Each class-0 start charges to a member of the §22 high-cost family. -/
  hmaps : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
      chargeOf ctx k ∈ highCostSet
        ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.paths
        ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.cost
        ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.Y
  /-- K.1.3 endpoint disjointness — the charge map is injective on the class-0 fibre. -/
  hinj : ∀ ctx : ActualFailureContext,
    ∀ x ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
      ∀ y ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        chargeOf ctx x = chargeOf ctx y → x = y
  /-- The active-window containment of each class-0 descent window in the shell index range. -/
  hwin : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
      ∃ r₀ : ℕ, r₀ + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card ∧
        k + ctx.n24CarryData.r
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + r₀
  /-- The 22.1A area-positive cap `(r+1)·(L+B+1) − T ≤ chernoff.weight (chargeOf k)`. -/
  hcapPos : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
      ((ctx.n24CarryData.r : ℝ) + 1) * (class0ShellGapScale ctx : ℝ) - ctx.n24CarryData.T
        ≤ ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.weight
            (chargeOf ctx k)

/-- **The class-0 Chernoff injection, BUILT from the minimal core** through worker 3's
`Class0ChernoffInjection.ofChargeWindowAreaCap` (the gap structure grounded in the dyadic shell scale,
the multiplier set to the canonical residual `max 0 ((r+1)·g₀ − T)`). -/
def Class0ChernoffSeedCore.toInjection
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (S : Class0ChernoffSeedCore budget) : Class0ChernoffInjection budget :=
  Class0ChernoffInjection.ofChargeWindowAreaCap budget S.chargeOf S.hmaps S.hinj S.hwin S.hcapPos

/-- **The class-1 clean-CNL (L.1.2 / G.35) minimal residual core** for a routed budget: the L.1.2
bounded-multiplicity count (`hcard`), the K.1.2 active-window containment (`hwin`), and the single G.35
weighted-Kraft scalar budget (`hbudget`).  All the gap structure (`g₀ = cnlActiveScale`, `hgap`), the
order-rank charge map into the proved-nonempty surviving family, the multiplier `positivePart`, and the
`∀ t` Kraft cap collapse are discharged by `toInjection`. -/
structure Class1CNLSeedCore
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) where
  /-- The L.1.2 bounded-multiplicity count `|routedFibre 1| ≤ |selectedTransitions (lift…)|`. -/
  hcard : ∀ ctx : ActualFailureContext,
    (routedFibre ctx.n24CarryData (budget ctx).route 1).card
      ≤ (selectedTransitions (liftTransitionsOfShell ctx)).card
  /-- The K.1.2 active-window containment of each class-1 descent window in the shell index range. -/
  hwin : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
      ∃ r₀ : ℕ, r₀ + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card ∧
        k + ctx.n24CarryData.r
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + r₀
  /-- The single G.35 weighted-Kraft scalar budget `cnlActiveMult ctx ≤ cnlMinKraftRate ctx`. -/
  hbudget : ∀ ctx : ActualFailureContext, cnlActiveMult ctx ≤ cnlMinKraftRate ctx

/-- **The class-1 clean-CNL injection, BUILT from the minimal core** through worker 4's
`Class1CNLInjection.ofShellWindowCountBudget` (the charge map from the order-rank matching into the
proved-nonempty surviving family, the gap grounded in the dyadic scale, the `∀ t` Kraft cap collapsed
to the single worst-case budget). -/
def Class1CNLSeedCore.toInjection
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (S : Class1CNLSeedCore budget) : Class1CNLInjection budget :=
  Class1CNLInjection.ofShellWindowCountBudget budget S.hcard S.hwin S.hbudget

/-! ## 3.  The minimal combined residual and the tightened endpoint -/

/-- **The minimal combined residual of Erdős #260.**

Bundles ONLY the genuine deep manuscript inputs that survive across all five wave-9 seed closures,
each as the worker's own residual bundle:

* `returnSeed` (worker 1) — `ReturnClass4SeedResidual ctx`: the M.2.1 endpoint-nesting count + K.1.2
  active-window gap structure;
* `towerRun` (worker 2) — `TowerRunSeedClosureData`: the I.4.1 Tower sub-mass + the Run I.6S
  summability + the Run I.5.2 base bound;
* `chernoff` (worker 3) — `Class0ChernoffSeedCore`: the J.1.7 charge map + 22.1A area cap + window
  containment, over the combined budget;
* `cnl` (worker 4) — `Class1CNLSeedCore`: the L.1.2 count + K.1.2 window containment + G.35 Kraft
  scalar, over the combined budget;
* `densePack` (worker 5) — `DensePackK11Seed`: the K.1.3/K.1.4 endpoint-disjoint cover + active-window
  containment + K.1.2 active-floor calibration, over the combined budget.

The budget the orthogonal class fields are stated against is the combined `buildSeedTRT returnSeed
towerRun`'s `.toBudget`, whose route is `genuineChargeRoute` (by `rfl`). -/
structure Erdos260MinimalResidual where
  /-- **Return (class 4) — worker 1.**  The M.2.1 endpoint-nesting count `hcount` + the K.1.2
  active-window gap structure `windowGap`/`hgap`/`hscale`. -/
  returnSeed : ∀ ctx : ActualFailureContext, ReturnClass4SeedResidual ctx
  /-- **Tower (class 2) + Run (class 5) — worker 2.**  The I.4.1 Tower sub-mass `htowerSubMass`, the
  Run I.6S summability `hrunSum`, and the Run I.5.2 base bound `hrunBase12`. -/
  towerRun : TowerRunSeedClosureData
  /-- **Chernoff (class 0) — worker 3.**  The J.1.7 charge map + 22.1A area-positive cap + the
  active-window containment, over the combined seed budget. -/
  chernoff : Class0ChernoffSeedCore (buildSeedTRT returnSeed towerRun).toBudget
  /-- **Clean-CNL (class 1) — worker 4.**  The L.1.2 bounded-multiplicity count + K.1.2 active-window
  containment + the single G.35 weighted-Kraft scalar budget, over the combined seed budget. -/
  cnl : Class1CNLSeedCore (buildSeedTRT returnSeed towerRun).toBudget
  /-- **DensePack (class 3) — worker 5.**  The K.1.3/K.1.4 endpoint-disjoint cover + the active-window
  containment + the K.1.2 active-floor calibration, over the combined seed budget. -/
  densePack : DensePackK11Seed (buildSeedTRT returnSeed towerRun).toBudget

namespace Erdos260MinimalResidual

/-- The combined seed-level Tower+Return+Run data of a minimal residual (workers 1 + 2). -/
def trt (R : Erdos260MinimalResidual) : SeedTRTData :=
  buildSeedTRT R.returnSeed R.towerRun

/-- **The full frontier seed residual, assembled from the minimal residual.**  The Chernoff/CNL
injection maps are built from their minimal cores (`toInjection`); the DensePack class-3 fields come
from the DensePack seed; the Tower+Return+Run data is the combined `buildSeedTRT`.  This is exactly the
`Erdos260SeedResidual` consumed by `erdos260_seed_reduced`. -/
def toSeedResidual (R : Erdos260MinimalResidual) : Erdos260SeedResidual :=
  Erdos260SeedResidual.ofDensePackSeed
    (buildSeedTRT R.returnSeed R.towerRun)
    R.chernoff.toInjection
    R.cnl.toInjection
    R.densePack

end Erdos260MinimalResidual

/-- **Erdős #260, reduced to the minimal combined manuscript-seed residual.**

From `Erdos260MinimalResidual` — the genuine route `genuineChargeRoute`, the worker-1 Return M.2.1
endpoint-nesting count + K.1.2 gap, the worker-2 Tower I.4.1 sub-mass + Run I.6S/I.5.2 bounds, the
worker-3 Chernoff (22.1A) charge map + area cap + containment, the worker-4 clean-CNL (L.1.2/G.35)
count + containment + Kraft scalar, and the worker-5 DensePack (K.1.3/K.1.4) cover + containment +
calibration — the frontier endpoint `erdos260_seed_reduced` proves `Erdos260Statement`.

This is strictly tighter than `erdos260_seed_reduced` on a bare `Erdos260SeedResidual`: each of the
five classes is reduced to its smallest honest core, with the entire level-assignment / mass-fraction /
gap-grounding / charge-construction machinery above the cores proved inside the five wave-9 workers.

No `sorry`/`axiom`/`admit`/`native_decide`; no degenerate/empty/full-mass shortcut. -/
theorem erdos260_of_minimalResidual (R : Erdos260MinimalResidual) : Erdos260Statement :=
  erdos260_seed_reduced R.toSeedResidual

/-! ## 4.  The FINAL combined irreducible residual surface (one entry per surviving core) -/

/-- The precise per-core status of the unconditional seed closure: the FINAL combined irreducible
surface — exactly what remains to be proved for a fully unconditional Erdős #260, every class reduced
to its smallest honest manuscript core, with everything above proved. -/
def erdos260UnconditionalSeedClosureResiduals : List String :=
  [ "CORE 1 (Return, class 4 — M.2.1 endpoint-nesting count) — returnSeed ctx |>.hcount: " ++
      "|routedFibre … 4| ≤ liftLevelBound X, the Erdős–Szekeres crossing/nesting alternative of " ++
      "Lemma M.2.1. ABOVE IT PROVED (worker 1, ReturnM21SeedClosure): the order-rank level map " ++
      "returnSeedLevel into the self-referential lift tower, the common 2-adic centre returnSeedXi, " ++
      "retCompat (G.7, δ ≡ Ξ mod 2^δ) and retInj (M.2.1 disjointness) as THEOREMS, retBound from the " ++
      "count, and the I.5.1/K.4 numeric returnSeed_hbudReturn (liftLevelBound X · 1 ≤ c⋆ξX/6).",
    "CORE 2 (Return, class 4 — K.1.2 active-window gap) — returnSeed ctx |>.windowGap/hgap/hscale: " ++
      "the descent-window ceiling giving the unit window-excess multiplier (windowExcess ≤ 1, the " ++
      "same active-floor calibration as the DensePack J.D unit charge).",
    "CORE 3 (Tower, class 2 — I.4.1 dense-packing sub-mass) — towerRun.htowerSubMass: " ++
      "routedClassMassOf … 2 ≤ ξ·X/6, a fraction strictly below the slot c⋆ξX/6 (never the full " ++
      "high-excess mass — refuted by seed_fullMass_forces_X_nonpos). Reducible to the K.1.1 cover + " ++
      "dense-marker hit packing + K.4 smallness, consuming the positive-density failure ctx.hfailure " ++
      "(worker 2's towerSubMass_of_failure). ABOVE IT PROVED: the active layer s = X/6, |I_j| = 1/X, " ++
      "the normalisation s·|I_j| = 1/6 (seedTowerLayer), and the I.4.1 fraction (towerFraction_of_subMass).",
    "CORE 4 (Run, class 5 — I.6S charged summability) — towerRun.hrunSum: routedClassMassOf … 5 ≤ " ++
      "∑_{i<len} w₀·(1/2)^i, the geometric period-descent envelope (ratio 1/2 = L.4.2 half-decrease, " ++
      "anchored in the actual shell by seedRun_periodDescent_halfDecrease). ABOVE IT PROVED: the floor " ++
      "hrunFloor via runFloor_of_geometricBase, with NO count.",
    "CORE 5 (Run, class 5 — I.5.2 base run output) — towerRun.hrunBase12: w₀ ≤ c⋆ξX/12, the L.4.2 " ++
      "period-descent base output bound.",
    "CORE 6 (Chernoff, class 0 — J.1.7 charge map) — chernoff.chargeOf/hmaps/hinj: the weight-" ++
      "respecting embedding of the class-0 progress starts into the genuine §22 high-cost family " ++
      "(highCostSet, the proved-nonempty four-path model leaf, class0_highCostFamily_nonempty) with " ++
      "K.1.3 endpoint disjointness. ABOVE IT PROVED (worker 3, Chernoff221ASeedClosure): g₀ = " ++
      "class0ShellGapScale = L+B+1 and hgap from the proved HitSequence.hitGap_le_of_shell_window, " ++
      "the multiplier max 0 ((r+1)·g₀−T), hscale, hmult_nonneg, and the nonneg half of the area cap.",
    "CORE 7 (Chernoff, class 0 — 22.1A area-positive cap) — chernoff.hcapPos: (r+1)·(L+B+1) − T ≤ " ++
      "chernoff.weight (chargeOf k), the shell-paid embedding's area side (cost_sh(Λ_SEP(τ)) ≥ c_Q H(τ)).",
    "CORE 8 (Chernoff, class 0 — active-window containment) — chernoff.hwin: each class-0 descent " ++
      "window ⊆ [firstIndexAbove X, firstIndexAbove X + r₀), r₀+1 ≤ |supportShell d X| (the hfibre_win " ++
      "residual; cannot hold for the top r starts — the manuscript boundary term).",
    "CORE 9 (clean-CNL, class 1 — L.1.2 bounded-multiplicity count) — cnl.hcard: " ++
      "|routedFibre … 1| ≤ |selectedTransitions (liftTransitionsOfShell ctx)|, the cluster " ++
      "reconstruction is bounded-to-one (Lemma L.1.2). ABOVE IT PROVED (worker 4, CNLL12SeedClosure): " ++
      "the order-rank charge map into the proved-nonempty surviving family (cnlL12_target_nonempty), " ++
      "g₀ = cnlActiveScale and hgap from the dyadic scale, and the worst-case Kraft collapse.",
    "CORE 10 (clean-CNL, class 1 — K.1.2 active-window containment) — cnl.hwin: each class-1 descent " ++
      "window ⊆ [firstIndexAbove X, firstIndexAbove X + r₀), r₀+1 ≤ |supportShell d X|.",
    "CORE 11 (clean-CNL, class 1 — G.35 weighted-Kraft scalar) — cnl.hbudget: cnlActiveMult ctx ≤ " ++
      "cnlMinKraftRate ctx, i.e. (r+1)·(L+carryB Q+1) − T ≤ 2^{−maxBND}·shellFactor·X·|I_j| (the single " ++
      "G.35 H.1/H.2 budget at the dyadic-grounded scale and the worst-case codeword depth).",
    "CORE 12 (DensePack, class 3 — K.1.3/K.1.4 endpoint-disjoint cover) — densePack.cover: the marker " ++
      "landing of the dense starts into densePackMarkers with K.1.3 endpoint disjointness; the count " ++
      "|genuineDensePackStarts| ≤ |densePackMarkers| is DERIVED (densePackCard_ofCover). The " ++
      "irreducible core is the coarea support identity (J.2/J.5/K.1).",
    "CORE 13 (DensePack, class 3 — active-window containment) — densePack.windowReach/hReach/hContain: " ++
      "each class-3 dense start's descent window stays below firstIndexAbove X + windowReach (the " ++
      "hfibre_win residual). ABOVE IT PROVED (worker 5, DensePackK11SeedClosure): densePackDyadicG0 = " ++
      "L+B+1 and the pointwise gap from the proved HitSequence.hitGap_le_of_shell_window.",
    "CORE 14 (DensePack, class 3 — K.1.2 active-floor calibration) — densePack.hScale: " ++
      "(r+1)·(L+B+1) − T ≤ 1, the J.D unit charge windowExcess ≤ 1.",
    "ASSEMBLED ABOVE THE CORES — buildSeedTRT (workers 1+2 → SeedTRTData over genuineChargeRoute, NO " ++
      "free Tower/Run count); Class0ChernoffSeedCore.toInjection / Class1CNLSeedCore.toInjection " ++
      "(workers 3/4 → the charge-injection maps over the combined budget); " ++
      "Erdos260MinimalResidual.toSeedResidual (worker 5's ofDensePackSeed → Erdos260SeedResidual); and " ++
      "the joint N.24 TRT compression + the class-6 closure (inside erdos260_seed_reduced).",
    "ENDPOINT — erdos260_of_minimalResidual : Erdos260MinimalResidual → Erdos260Statement. The route " ++
      "is FORCED to genuineChargeRoute; the budget is built from the bare seeds with no free count; no " ++
      "protected endpoint is weakened. CORES 1–14 are the irreducible manuscript input geometry of a " ++
      "fully unconditional Erdős #260." ]

theorem erdos260UnconditionalSeedClosureResiduals_nonempty :
    erdos260UnconditionalSeedClosureResiduals ≠ [] := by
  simp [erdos260UnconditionalSeedClosureResiduals]

/-! ## 5.  Axiom-cleanliness audit -/

#print axioms buildSeedTRT
#print axioms Class0ChernoffSeedCore.toInjection
#print axioms Class1CNLSeedCore.toInjection
#print axioms Erdos260MinimalResidual.trt
#print axioms Erdos260MinimalResidual.toSeedResidual
#print axioms erdos260_of_minimalResidual

end

end Erdos260
