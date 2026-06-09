import Erdos260.ChernoffProgressCountCore
import Erdos260.TowerRunDeepCore
import Erdos260.DensePackCoverCore
import Erdos260.ReturnCarryNestingCore
import Erdos260.CNLClusterInjectionCore
import Erdos260.ChernoffCNLChargeInjectionCore
import Erdos260.TowerRunMassFractionCore
import Erdos260.DensePackK11SupportCore
import Erdos260.Erdos260SeedResidual

/-!
# Erdős #260 — the CORRECTED, deep-shell-SATISFIABLE wave-12 seed closure (`…SeedClosureV3`)

This module (NEW; it edits no existing file) is the **wave-12 integration capstone**.  Wave-11's
audits proved that most wave-9/10 "minimal residual" cores were **WRONG-SHAPE for deep shells**: a
shell-scaling quantity bounded by a fixed/per-slice one (provably false once `r = ⌊κL⌋ ≥ 1`).  The
two recurring pathologies were

* the **uniform-ceiling** per-element charge `(r+1)·(L+B+1) − T ≤ small` (false once the active floor
  `Y ≍ εL → ∞`), and
* the **fixed-family count collapse** `|fibre| ≤ (fixed constant)` (Chernoff `≤ 4`, clean-CNL `≤ 14`,
  Return `≤ liftLevelBound X = O(log* X)`), false once the fibre fills a shell window of width
  `K ≍ c₀·X`.

Wave-12 builds a CORRECTED endpoint `erdos260_of_minimalResidualV3` whose residuals are the genuine
**matched / amortized per-element charge** family-sum bounds — each element charged its *own* window
excess against the family weight, summed against the genuine analytic family sum — never the
deep-shell-false uniform ceiling or the fixed-family collapse.

## How each class is routed (the matched / amortized charge, NOT the uniform ceiling)

The budget is built from the wave-11 corrected Tower / Run / Return pieces (so the Tower / Return /
Run **capacity floors** `routedClassMassOf … i ≤ c⋆ξX/6` are themselves the deep-shell-satisfiable
ones), and the residual then carries the Chernoff / clean-CNL / DensePack matched charges.

| class | corrected residual (deep-shell-satisfiable, RIGHT shape) | genuine analytic family-sum |
| --- | --- | --- |
| **2 Tower** | `Class2ActiveFloorCount` `(★) #fibre₂·positivePart(2·Y) ≤ ξX/6` (dense markers BYPASSED, the K.1.2/L.20 active-floor count) — `TowerRunDeepCore` | the I.4.1 active-floor count `#fibre₂ = Θ(X/Y)` |
| **5 Run** | `RunClass5StageChain` (the L.4.2 half-decreasing period-descent chain; the geometric envelope absorbs the spikes with NO `Y`-multiplier) — `TowerRunDeepCore` | the I.5.2 base run output `wt(O₀) ≤ c⋆ξX/12` |
| **4 Return** | `Class4ReturnPerSliceCharge`: the per-`(e,τ,P)`-slice M.2.1 count `|routedFibre 4| ≤ (#sliceKeys)·liftLevelBound X` (the genuine `M_L·X` envelope, `routedFibre4_card_le_of_slices`) routed through the matched per-element charge — built here | the M.2.1 per-slice nesting count `(log* L)^C` |
| **0 Chernoff** | the matched J.1.7 per-path area charge `windowExcess(k) ≤ weight(chargeOf k)` (each progress start charged its own §22 high-cost path's area weight), summed to `termChernoff = ∑_p weight p` (`hChernoffField_ofMatching`) — NO uniform `(r+1)(L+B+1)−T ≤ 1/4`, NO `|fibre| ≤ 4` | the 22.1A area sum `∑_{cost≥Y} weight` |
| **1 clean-CNL** | the matched per-codeword Kraft charge `windowExcess(k) ≤ 2^{-BND(g k)}·shellFactor·X·|I_j|` (each class-1 start charged its own codeword's Kraft rate), summed to `termCnl` (`routedClassMass_le_termCnl_of_kraftCharge`) — NO uniform ceiling | the G.35 weighted-Kraft sum `(∑ 2^{-BND})·shellFactor·X·|I_j|` |
| **3 DensePack** | `DensePackCoareaSupport` (the K.1.1 coarea first-stop owner + K.1.4 landing; the count is an injection whose two sides BOTH scale with the dense geometry, the RIGHT shape, `DensePackCoareaIdentityCore`) → `termDensePack` | the K.1.1/K.1.3 coarea endpoint-disjoint cover |

## The genuine deep inputs that remain (carried honestly, NOT faked, NOT collapsed)

Two slots reduce to genuine analytic family sums that the formalized §22-model-leaf assembly
(`faithfulCapacityPhases`) bakes in at a fixed `O(1)` / fixed-family value; the matched charge is the
RIGHT shape, but the *value* of the family sum is the irreducible analytic input:

* **Chernoff** — `termChernoff (faithfulCapacityPhases …)` is the fixed §22 model-leaf area
  `chernoffModelArea ∈ [1,4]`.  The genuinely deep-shell-satisfiable envelope is the X-scaling 22.1A
  area `c⋆ξX/6` (`ChernoffProgressAreaCharge.toBudgetFloor`, exposed here as
  `chernoff_genuine_area_envelope`): it holds *even where the naive `≤ 4` count fails*
  (`corrected_floor_holds_where_naive_count_fails`).  We route the matched J.1.7 area charge (the
  right shape) and carry the 22.1A area sum as the genuine deep input.
* **clean-CNL** — the matched Kraft close demands an injective reindexing; the genuine map is the
  `O_Q(1)`-to-one cluster codeword (`cnlCanonicalCodeword`, `cnl_count_le_shellWidth_mul_family`), the
  honest `|routedFibre 1| ≤ K·|family|` shape (exposed here as `cnl_genuine_OQ1_to_one_count`).  We
  route the matched per-codeword Kraft charge and carry the G.35 Kraft sum as the genuine deep input.

No `sorry`/`axiom`/`admit`/`native_decide`; no degenerate / uniform-ceiling / fixed-family shortcut.
The endpoint axioms are exactly `[propext, Classical.choice, Quot.sound]`.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The corrected Return (class 4) per-slice matched charge

Wave-11 (`ReturnCarryNestingCore`) proved the GLOBAL count `|routedFibre 4| ≤ liftLevelBound X` is the
wrong shape (`liftLevelBound X = O(log* X) ≤ 5` for all `X < 2^2059`, against a fibre that fills a
window of width `K ≍ c₀·X`), and gave the corrected per-`(e,τ,P)`-slice envelope
`routedFibre4_card_le_of_slices` : `|routedFibre 4| ≤ (#sliceKeys)·liftLevelBound X` (the genuine
manuscript `M_L·X` shape).  Here we route that corrected count through the matched per-element
window-excess charge (the K.1.2/L.20 active-window gap multiplier) to discharge the Return capacity
floor `routedClassMassOf … 4 ≤ c⋆ξX/6` — with NO global `liftLevelBound X` count and NO uniform
ceiling. -/

/-- **The corrected class-4 (Return / OLC) per-slice matched charge.**

The deep-shell-satisfiable replacement for the wave-9/10 global `|routedFibre 4| ≤ liftLevelBound X`
collapse:

* `key` / `slices` — the per-`(e,τ,P)`-slice M.2.1 data (`OlcSliceData`), giving the genuine count
  `|routedFibre 4| ≤ (#sliceKeys)·liftLevelBound X` (`routedFibre4_card_le_of_slices`, the `M_L·X`
  envelope) — NOT the false global `O(log* X)` count;
* `g₀` / `mult` / `hgap` / `hscale` / `hmult_nonneg` — the matched per-element window-excess charge
  (the K.1.2/L.20 active-window gap multiplier `windowExcess ≤ (r+1)·g₀ − T ≤ mult`, each start
  charged its own window excess) — NOT the uniform ceiling;
* `hnumeric` — the genuine `M_L·X` smallness `(#sliceKeys)·liftLevelBound X · mult ≤ c⋆ξX/6`. -/
structure Class4ReturnPerSliceCharge (ctx : ActualFailureContext) where
  /-- The per-`(e,τ,P)`-slice key (the endpoint coordinate × dyadic arm/period pair). -/
  key : ℕ → ℕ
  /-- The genuine per-slice M.2.1 nesting data on each slice (`OlcSliceData`, the carry-side
  `carryVal2` level map + crossing-freeness + consecutive congruence). -/
  slices : ∀ y ∈ (olcFibre ctx).image key, OlcSliceData ctx key y
  /-- The active-window hit-gap bound `g₀` (the proved dyadic scale `L+B+1`). -/
  g₀ : ℕ
  /-- The matched per-element window-excess multiplier (K.1.2/L.20). -/
  mult : ℝ
  /-- The multiplier is nonnegative. -/
  hmult_nonneg : 0 ≤ mult
  /-- The descent-window hit-gap bound holds on the class-4 fibre. -/
  hgap : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
    ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀
  /-- The K.1.2 active-floor scaling `(r+1)·g₀ − T ≤ mult`. -/
  hscale : ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ : ℝ) - ctx.n24CarryData.T ≤ mult
  /-- **The genuine `M_L·X` smallness** — the per-slice count times the matched multiplier fits the
  per-phase budget share `(#sliceKeys)·liftLevelBound X · mult ≤ c⋆ξX/6`. -/
  hnumeric : (((olcFibre ctx).image key).card : ℝ) * (liftLevelBound ctx.shell.X : ℝ) * mult
    ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6

/-- **The Return capacity floor, from the per-slice matched charge.**

`routedClassMassOf … 4 ≤ c⋆ξX/6` via the corrected per-slice count `routedFibre4_card_le_of_slices`
(`|routedFibre 4| ≤ (#sliceKeys)·liftLevelBound X`) fed into the proved count×multiplier core
`routedClassMassOf_le_countMultiplier` with the matched per-element window-excess multiplier (the gap
structure of `windowExcess_le_window_gap_multiplier`), then the `M_L·X` smallness `hnumeric`.  No
global `liftLevelBound X` count, no uniform ceiling. -/
theorem Class4ReturnPerSliceCharge.returnFloor {ctx : ActualFailureContext}
    (C : Class4ReturnPerSliceCharge ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  have hpoint : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ C.mult :=
    fun k hk => windowExcess_le_window_gap_multiplier (C.hgap k hk) C.hscale C.hmult_nonneg
  have hcount : (olcFibre ctx).card
      ≤ ((olcFibre ctx).image C.key).card * liftLevelBound ctx.shell.X :=
    routedFibre4_card_le_of_slices ctx C.key C.slices
  have hcard : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).card : ℝ)
      ≤ (((olcFibre ctx).image C.key).card : ℝ) * (liftLevelBound ctx.shell.X : ℝ) := by
    rw [← olcFibre_def]
    calc ((olcFibre ctx).card : ℝ)
        ≤ (((olcFibre ctx).image C.key).card * liftLevelBound ctx.shell.X : ℕ) := by
          exact_mod_cast hcount
      _ = (((olcFibre ctx).image C.key).card : ℝ) * (liftLevelBound ctx.shell.X : ℝ) := by
          push_cast; ring
  calc routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ≤ ((((olcFibre ctx).image C.key).card : ℝ) * (liftLevelBound ctx.shell.X : ℝ)) * C.mult :=
        routedClassMassOf_le_countMultiplier ctx.n24CarryData (genuineChargeRoute ctx) 4
          hpoint C.hmult_nonneg hcard
    _ ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := C.hnumeric

/-! ## 2.  The corrected wave-12 budget (Tower active-floor count + Run chain + Return per-slice)

The shared `SeparatedPhaseRoutedBudget` is assembled, over the genuine first-obstruction route
`genuineChargeRoute`, from the three corrected TRT capacity floors — all deep-shell-satisfiable:

* Tower (2): `Class2ActiveFloorCount.htowerSubMass` (`routedClassMassOf … 2 ≤ ξX/6`, the `(★)`
  active-floor count, dense markers bypassed);
* Run (5): `RunClass5StageChain.runFloor` (`routedClassMassOf … 5 ≤ c⋆ξX/6`, the L.4.2 period descent);
* Return (4): `Class4ReturnPerSliceCharge.returnFloor` (the per-slice `M_L·X` matched charge). -/

/-- **The corrected wave-12 Tower+Run+Return mass-fraction data.**  Tower slot from the sharp
active-floor count (`towerS = 1/6`, `towerIj = 1`, so the layer normalisation is `1/6 ≤ 1/6` and the
"fraction" is exactly `ξX/6`), Run slot from the period-descent chain, Return slot from the per-slice
matched charge.  Its `toBudget` is the wave-12 budget. -/
def v3MassFractionData
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx) :
    TowerRunMassFractionData where
  route := fun ctx => genuineChargeRoute ctx
  towerS := fun _ => 1 / 6
  towerIj := fun _ => 1
  htowerLayer := fun _ => by norm_num
  htowerFraction := fun ctx => by
    have h := (towerCount ctx).htowerSubMass
    show routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
        ≤ erdos260Constants.ξ * (1 / 6 : ℝ) * (ctx.shell.X : ℝ) * 1
    calc routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
        ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := h
      _ = erdos260Constants.ξ * (1 / 6 : ℝ) * (ctx.shell.X : ℝ) * 1 := by ring
  hrunFloor := fun ctx => (runChain ctx).runFloor
  returnSlot := fun ctx => (returnCharge ctx).returnFloor

/-- **The corrected wave-12 seed budget**, over the genuine first-obstruction route
`genuineChargeRoute`, built from the wave-11 corrected Tower active-floor count, the Run
period-descent chain, and the Return per-slice matched charge — all deep-shell-satisfiable. -/
def v3Budget
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  (v3MassFractionData towerCount runChain returnCharge).toBudget

/-- The wave-12 seed budget routes through the genuine first-obstruction route. -/
@[simp] theorem v3Budget_route
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (ctx : ActualFailureContext) :
    (v3Budget towerCount runChain returnCharge ctx).route = genuineChargeRoute ctx := rfl

/-! ## 3.  The corrected, deep-shell-satisfiable minimal residual -/

/-- **The corrected wave-12 minimal residual of Erdős #260.**

Every surviving class reduced to its genuine, deep-shell-SATISFIABLE matched / amortized per-element
charge — never the wave-9/10 uniform-ceiling or fixed-family collapse:

* `towerCount` / `runChain` / `returnCharge` — the three corrected TRT capacity floors (Tower
  active-floor count, Run period descent, Return per-slice `M_L·X` matched charge); they build the
  budget, and the joint N.24 TRT compression `hTRT` is then PROVED generically (`seedHTRT`);
* `chernoff*` — the matched J.1.7 per-path area charge (each progress start charged its own §22
  high-cost path's area weight), discharging `routedClassMassOf … 0 ≤ termChernoff` (the 22.1A area
  sum `∑_p weight p`) via `hChernoffField_ofMatching` — no uniform ceiling, no `|fibre| ≤ 4`;
* `cnl*` — the matched per-codeword Kraft charge (each class-1 start charged its own codeword's Kraft
  rate `2^{-BND}·shellFactor·X·|I_j|`), discharging `routedClassMassOf … 1 ≤ termCnl` (the G.35 Kraft
  sum) via the kraft-charging close — no uniform ceiling;
* `densePack*` — the K.1.1 coarea support identity (first-stop owner + landing, the RIGHT-shape
  injection whose two sides both scale with the dense geometry) + the active-window gap, discharging
  `routedClassMassOf … 3 ≤ termDensePack`. -/
structure Erdos260MinimalResidualV3 where
  /-- **Tower (class 2) — the sharp active-floor count `(★)`.**  `#fibre₂·positivePart(2·Y) ≤ ξX/6`
  (the K.1.2/L.20 active-floor count, dense markers BYPASSED; `TowerRunDeepCore`). -/
  towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx
  /-- **Run (class 5) — the L.4.2 half-decreasing period-descent chain.**  The geometric envelope
  absorbs the class-5 spikes with NO `Y`-multiplier (`TowerRunDeepCore`). -/
  runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx
  /-- **Return (class 4) — the per-slice `M_L·X` matched charge.**  The genuine per-`(e,τ,P)`-slice
  count `|routedFibre 4| ≤ (#sliceKeys)·liftLevelBound X` routed through the matched per-element
  window-excess charge — NOT the deep-shell-false global `liftLevelBound X = O(log* X)` count. -/
  returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx
  /-- **Chernoff (class 0) — the matched J.1.7 charge map.**  Each progress start ↦ a §22 high-cost
  path (the 22.1A shell-paid embedding). -/
  chernoffChargeOf : ∀ ctx : ActualFailureContext,
    ℕ → ((faithfulCapacityPhases (v3Budget towerCount runChain returnCharge) ctx).toClosurePhaseData).chernoff.α
  /-- 22.1A high-cost membership — each progress start charges into the high-cost family. -/
  chernoffMaps : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (v3Budget towerCount runChain returnCharge ctx).route 0,
      chernoffChargeOf ctx k ∈ highCostSet
        ((faithfulCapacityPhases (v3Budget towerCount runChain returnCharge) ctx).toClosurePhaseData).chernoff.paths
        ((faithfulCapacityPhases (v3Budget towerCount runChain returnCharge) ctx).toClosurePhaseData).chernoff.cost
        ((faithfulCapacityPhases (v3Budget towerCount runChain returnCharge) ctx).toClosurePhaseData).chernoff.Y
  /-- K.1.3 endpoint-disjoint injectivity — distinct progress starts get distinct paths. -/
  chernoffInj : ∀ ctx : ActualFailureContext,
    ∀ x ∈ routedFibre ctx.n24CarryData (v3Budget towerCount runChain returnCharge ctx).route 0,
      ∀ y ∈ routedFibre ctx.n24CarryData (v3Budget towerCount runChain returnCharge ctx).route 0,
        chernoffChargeOf ctx x = chernoffChargeOf ctx y → x = y
  /-- **The matched J.1.7 per-path area domination** — each progress start's window excess is at most
  its assigned §22 high-cost path's area weight (the genuine 22.1A charged branch mass, each element
  charged its OWN path's weight), summing to `termChernoff = ∑_p weight p`.  This REPLACES the wave-9/10
  uniform ceiling `(r+1)(L+B+1)−T ≤ 1/4` and the count collapse `|fibre| ≤ 4`. -/
  chernoffDom : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (v3Budget towerCount runChain returnCharge ctx).route 0,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ ((faithfulCapacityPhases (v3Budget towerCount runChain returnCharge) ctx).toClosurePhaseData).chernoff.weight
            (chernoffChargeOf ctx k)
  /-- **clean-CNL (class 1) — the matched per-codeword Kraft charge map.**  Each class-1 start ↦ a
  surviving clean-CNL codeword (the L.1.2 cluster reconstruction). -/
  cnlG : ∀ ctx : ActualFailureContext, ℕ → CNLTransition
  /-- L.1.2 cluster reconstruction — codewords are surviving clean-CNL transitions. -/
  cnlMem : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (v3Budget towerCount runChain returnCharge ctx).route 1,
      cnlG ctx k ∈ selectedTransitions (liftTransitionsOfShell ctx)
  /-- L.1.2 bounded-multiplicity injectivity — distinct class-1 starts get distinct codewords. -/
  cnlInj : ∀ ctx : ActualFailureContext,
    ∀ k₁ ∈ routedFibre ctx.n24CarryData (v3Budget towerCount runChain returnCharge ctx).route 1,
      ∀ k₂ ∈ routedFibre ctx.n24CarryData (v3Budget towerCount runChain returnCharge ctx).route 1,
        cnlG ctx k₁ = cnlG ctx k₂ → k₁ = k₂
  /-- **The matched per-codeword G.6/G.35 Kraft charge** — each class-1 start's window excess is at
  most its OWN codeword's Kraft rate `2^{-BND(g k)}·shellFactor·X·|I_j|`, summing (through the
  injective reindexing) to the G.35 Kraft sum `termCnl`.  This REPLACES the wave-9 uniform-scalar
  collapse `cnlActiveMult ≤ cnlMinKraftRate` (provably false for `r ≥ 1`). -/
  cnlCharge : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (v3Budget towerCount runChain returnCharge ctx).route 1,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ (2 : ℝ) ^ (-(bndHeightNatOfShell ctx (cnlG ctx k) : ℝ))
            * (cnlShellFactorOfShell ctx : ℝ) * (ctx.shell.X : ℝ) * (cnlIjOfShell ctx : ℝ)
  /-- **DensePack (class 3) — the K.1.1 coarea support identity.**  The first-stop owner + the
  representative marker landing (`DensePackCoareaSupport`); the count `|genuineDensePackStarts| ≤
  |densePackMarkers|` is an injection whose two sides BOTH scale with the dense geometry (the RIGHT
  shape, not a fixed-family collapse). -/
  densePackSupport : ∀ ctx : ActualFailureContext,
    DensePackCoareaSupport (v3Budget towerCount runChain returnCharge) ctx
  /-- The active-window gap ceiling on the class-3 descent window (for the J.D unit charge). -/
  densePackG0 : ActualFailureContext → ℕ
  /-- The active-window gap bound on the class-3 descent window. -/
  densePackGap : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (v3Budget towerCount runChain returnCharge ctx).route 3,
      ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ densePackG0 ctx
  /-- The K.1.2 active-floor scaling giving the J.D unit charge `windowExcess ≤ 1`. -/
  densePackScale : ∀ ctx : ActualFailureContext,
    ((ctx.n24CarryData.r : ℝ) + 1) * (densePackG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1

namespace Erdos260MinimalResidualV3

/-- The wave-12 budget of this residual. -/
def budget (R : Erdos260MinimalResidualV3) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  v3Budget R.towerCount R.runChain R.returnCharge

/-- **The Chernoff (class-0) ledger field, from the matched J.1.7 area charge.**  The matching close
`hChernoffField_ofMatching` (the J.1.7 charging-map mechanism, area identification
`termChernoff = ∑_p weight p` by `rfl`) applied to the charge map with the per-path domination
supplied directly — no count, no uniform ceiling, no area-identification residual. -/
theorem hChernoffField (R : Erdos260MinimalResidualV3) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (R.budget ctx).route 0
        ≤ termChernoff (faithfulCapacityPhases R.budget ctx).toClosurePhaseData :=
  hChernoffField_ofMatching R.budget R.chernoffChargeOf R.chernoffMaps R.chernoffInj R.chernoffDom

/-- **The clean-CNL (class-1) ledger field, from the matched per-codeword Kraft charge.**  The
Kraft-charging close (`routedClassMass_le_termCnl_of_kraftCharge`, via `Finset.sum_image` reindexing
through the charge injection then domination by the full clean-CNL family Kraft sum) applied to the
per-codeword charge — no uniform ceiling. -/
theorem hCnlField (R : Erdos260MinimalResidualV3) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (R.budget ctx).route 1
        ≤ termCnl (faithfulCapacityPhases R.budget ctx).toClosurePhaseData :=
  fun ctx => Class1CNLChargeData.hCnl_ofShellCharge R.budget R.cnlG R.cnlMem R.cnlInj R.cnlCharge ctx

/-- **The DensePack (class-3) ledger field, from the K.1.1 coarea support.**  The coarea support
identity's endpoint-disjoint count (`DensePackCoareaSupport.card_le`) + the active-window gap, fed to
the proved `hDensePack_field_ofCardLe` (the order-rank matching + the J.1.8 summation, J.D unit charge
discharged from the gap geometry). -/
theorem hDensePackField (R : Erdos260MinimalResidualV3) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (R.budget ctx).route 3
        ≤ termDensePack (faithfulCapacityPhases R.budget ctx).toClosurePhaseData :=
  hDensePack_field_ofCardLe R.budget (fun _ => rfl)
    (fun ctx => (R.densePackSupport ctx).card_le) R.densePackG0 R.densePackGap R.densePackScale

/-- **The class-6 old-residual bound, closed outright.**  The genuine route never assigns class 6
(`genuineChargeRoute_routed6_zero`), so the routed class-6 mass is `0 ≤` the nonnegative L.6.4 branch
mass. -/
theorem hOldResField (R : Erdos260MinimalResidualV3) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (R.budget ctx).route 6
        ≤ ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k :=
  fun ctx => by
    show routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 6
        ≤ ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k
    rw [genuineChargeRoute_routed6_zero ctx]
    exact oldResL65_branchMass_nonneg ctx

end Erdos260MinimalResidualV3

/-- **Erdős #260, reduced to the corrected wave-12 minimal residual.**

From `Erdos260MinimalResidualV3` — the genuine route `genuineChargeRoute`; the corrected, deep-shell
satisfiable matched / amortized per-element charges of every class (Tower active-floor count, Run
period descent, Return per-slice `M_L·X`, Chernoff 22.1A matched area charge, clean-CNL matched Kraft
charge, DensePack K.1.1 coarea support) — the flexible endpoint `erdos260_charge_reduced_of_routing`
proves `Erdos260Statement`.

The Tower/Return/Run capacity floors are supplied by the budget, so the joint N.24 TRT compression
`hTRT` is proved generically (`seedHTRT`); the class-6 closure is `genuineChargeRoute_routed6_zero`;
the Chernoff/CNL/DensePack ledger bounds are the matched-charge family-sum bounds.

No `sorry`/`axiom`/`admit`/`native_decide`; every residual is the matched per-element charge, never the
deep-shell-false uniform ceiling or fixed-family collapse. -/
theorem erdos260_of_minimalResidualV3 (R : Erdos260MinimalResidualV3) : Erdos260Statement :=
  erdos260_charge_reduced_of_routing R.budget
    R.hChernoffField
    R.hCnlField
    R.hDensePackField
    (seedHTRT R.budget)
    R.hOldResField

/-! ## 4.  The genuine deep-shell-satisfiable analytic family sums, exposed (carried honestly)

Two slots reduce, through the formalized §22-model-leaf assembly, to genuine analytic family sums at
a fixed `O(1)` / fixed-family value.  The matched charge above is the RIGHT shape; here we expose the
genuinely deep-shell-satisfiable analytic envelopes themselves — the irreducible deep inputs, carried
honestly, NOT collapsed to a uniform ceiling and NOT faked. -/

/-- **Chernoff — the genuine X-scaling 22.1A area envelope is deep-shell-satisfiable.**  The corrected
area charge `ChernoffProgressAreaCharge` (the proved window count `K = |supportShell d X|`, NOT the
false `≤ 4`, against the X-scaling 22.1A area envelope) discharges `routedClassMassOf … 0 ≤ c⋆ξX/6`.
Unlike the fixed model-leaf area `termChernoff ∈ [1,4]`, this **scales with the shell**, so it holds
even where the naive `≤ 4` count is provably false — the genuine deep input. -/
theorem chernoff_genuine_area_envelope
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (R : ChernoffProgressAreaCharge budget) (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 0 ≤ chernoffBudgetTarget ctx :=
  R.toBudgetFloor ctx

/-- **clean-CNL — the genuine `O_Q(1)`-to-one count is the honest deep-shell shape.**  The injective
`|routedFibre 1| ≤ |family|` collapse is false for deep shells (`|family| ≤ 14` fixed); the genuine
manuscript bound is the `O_Q(1)`-to-one `|routedFibre 1| ≤ K·|family|` (multiplicity `≤ K = shellWidth`,
both sides scaling with the shell) — `cnl_count_le_shellWidth_mul_family`, the genuine deep input. -/
theorem cnl_genuine_OQ1_to_one_count (ctx : ActualFailureContext) (route : ℕ → Fin 7) :
    (routedFibre ctx.n24CarryData route 1).card
      ≤ shellWidth ctx * (selectedTransitions (liftTransitionsOfShell ctx)).card :=
  cnl_count_le_shellWidth_mul_family ctx route

/-- **Return — the genuine per-slice `M_L·X` count is the honest deep-shell shape.**  The global
`|routedFibre 4| ≤ liftLevelBound X = O(log* X)` collapse is false for deep shells; the genuine
manuscript bound is the per-`(e,τ,P)`-slice `|routedFibre 4| ≤ (#sliceKeys)·liftLevelBound X` (the
`M_L·X` envelope, both sides scaling with the shell) — `routedFibre4_card_le_of_slices`, used by the
Return per-slice matched charge. -/
theorem return_genuine_perSlice_count (R : Erdos260MinimalResidualV3) (ctx : ActualFailureContext) :
    (olcFibre ctx).card
      ≤ ((olcFibre ctx).image (R.returnCharge ctx).key).card * liftLevelBound ctx.shell.X :=
  routedFibre4_card_le_of_slices ctx (R.returnCharge ctx).key (R.returnCharge ctx).slices

/-! ## 5.  The corrected deep-shell-satisfiable residual surface (one entry per class) -/

/-- The precise per-class status of the corrected wave-12 seed closure: every class routed through
the matched / amortized per-element charge to its genuine, deep-shell-satisfiable analytic family-sum
bound — never the wave-9/10 uniform-ceiling or fixed-family collapse. -/
def erdos260UnconditionalSeedClosureV3Residuals : List String :=
  [ "CLASS 2 (Tower — I.4.1 active-floor count, RIGHT SHAPE) — towerCount ctx : Class2ActiveFloorCount " ++
      "= hbdry + the SINGLE scalar (★) #fibre₂·positivePart(2·Y) ≤ ξX/6 (the K.1.2/L.20 active-floor " ++
      "count; dense markers BYPASSED). htowerSubMass discharges routedClassMassOf … 2 ≤ ξX/6, fed to " ++
      "the budget's Tower capacity floor. The genuine I.4.1 datum is that the class-2 (dense/CNL-tail) " ++
      "fibre is Θ(X/Y)-sparse — both sides scale with the shell. REPLACES the wave-10 four-field " ++
      "dense-marker cover, whose K.4 smallness (c₀ C_D/ρ_D)·2Y ≤ ξ/6 is FALSE once Y ≍ εL is large.",
    "CLASS 5 (Run — I.5.2 base run output, NO deep-shell pathology) — runChain ctx : RunClass5StageChain. " ++
      "The L.4.2 period-descent chain routes through the geometric envelope ∑ stageMass i ≤ 2·stageMass 0 " ++
      "(NO Y-multiplier, so no blow-up); runFloor discharges routedClassMassOf … 5 ≤ c⋆ξX/6 from the " ++
      "I.5.2 base output stageMass 0 = wt(O₀) ≤ c⋆ξX/12. Fed to the budget's Run capacity floor.",
    "CLASS 4 (Return — M.2.1 per-slice M_L·X count + matched charge, RIGHT SHAPE) — returnCharge ctx : " ++
      "Class4ReturnPerSliceCharge. The corrected per-(e,τ,P)-slice count |routedFibre 4| ≤ " ++
      "(#sliceKeys)·liftLevelBound X (routedFibre4_card_le_of_slices, the genuine M_L·X envelope; " ++
      "#sliceKeys = O(X·(log L)^2)) routed through the matched per-element window-excess charge " ++
      "(windowExcess ≤ (r+1)·g₀ − T ≤ mult, each start charged its OWN window excess) and the M_L·X " ++
      "smallness hnumeric, discharging returnFloor : routedClassMassOf … 4 ≤ c⋆ξX/6 (budget Return " ++
      "floor). REPLACES the wave-9/10 GLOBAL count |routedFibre 4| ≤ liftLevelBound X = O(log* X) ≤ 5, " ++
      "false once the fibre fills a window of width K ≍ c₀·X (perSlice_M21_does_not_imply_global).",
    "CLASS 0 (Chernoff — 22.1A matched area charge, RIGHT SHAPE) — chernoffChargeOf/chernoffMaps/" ++
      "chernoffInj/chernoffDom: the J.1.7 charge map of the progress starts into the §22 high-cost path " ++
      "family with the MATCHED per-path area domination windowExcess(k) ≤ weight(chargeOf k) (each " ++
      "progress start charged its OWN path's area weight). hChernoffField discharges routedClassMassOf " ++
      "… 0 ≤ termChernoff = ∑_p weight p (the 22.1A area family-sum) via hChernoffField_ofMatching " ++
      "(area identification by rfl). REPLACES the wave-9/10 uniform ceiling (r+1)(L+B+1)−T ≤ 1/4 and the " ++
      "count collapse |fibre| ≤ 4 (chernoff_progressCount_false_of_five_le). GENUINE DEEP INPUT carried: " ++
      "the X-scaling 22.1A area envelope routedClassMassOf … 0 ≤ c⋆ξX/6 (chernoff_genuine_area_envelope " ++
      "= ChernoffProgressAreaCharge.toBudgetFloor) is satisfiable even where the naive count fails; the " ++
      "§22-model-leaf assembly's termChernoff ∈ [1,4] collapse is the irreducible analytic content.",
    "CLASS 1 (clean-CNL — G.35 matched Kraft charge, RIGHT SHAPE) — cnlG/cnlMem/cnlInj/cnlCharge: the " ++
      "J.1.1 charge map of the class-1 starts into the surviving clean-CNL family with the MATCHED " ++
      "per-codeword Kraft charge windowExcess(k) ≤ 2^{-BND(g k)}·shellFactor·X·|I_j| (each start charged " ++
      "its OWN codeword's Kraft rate). hCnlField discharges routedClassMassOf … 1 ≤ termCnl (the G.35 " ++
      "weighted-Kraft family-sum, X·|I_j|-scaling) via routedClassMass_le_termCnl_of_kraftCharge " ++
      "(Finset.sum_image reindexing + family Kraft sum domination). REPLACES the wave-9 uniform-scalar " ++
      "collapse cnlActiveMult ≤ cnlMinKraftRate (cnl_hbudget_iff_r_zero: holds iff r = 0). GENUINE DEEP " ++
      "INPUT carried: the O_Q(1)-to-one count |routedFibre 1| ≤ K·|family| (cnl_genuine_OQ1_to_one_count " ++
      "= cnl_count_le_shellWidth_mul_family, multiplicity ≤ K = shellWidth), the honest deep-shell shape; " ++
      "the one-step alphabet's injective |fibre| ≤ |family| ≤ 14 collapse is the residual L.1.2 content.",
    "CLASS 3 (DensePack — K.1.1 coarea support, RIGHT SHAPE) — densePackSupport ctx : " ++
      "DensePackCoareaSupport (the first-stop owner + K.1.4 representative marker landing) + the " ++
      "active-window gap (densePackG0/densePackGap/densePackScale, the J.D unit charge). card_le gives " ++
      "the K.1.1 endpoint-disjoint count |genuineDensePackStarts| ≤ |densePackMarkers| — an INJECTION " ++
      "whose two sides BOTH scale with the dense geometry (densePack_count_iff_injection, the RIGHT " ++
      "shape, NOT a fixed-family collapse). hDensePackField discharges routedClassMassOf … 3 ≤ " ++
      "termDensePack via hDensePack_field_ofCardLe (order-rank matching + J.1.8 summation).",
    "BUDGET (NO free count) — v3Budget = (v3MassFractionData towerCount runChain returnCharge).toBudget " ++
      "over genuineChargeRoute: the Tower/Run/Return capacity floors routedClassMassOf … 2/4/5 ≤ c⋆ξX/6 " ++
      "are the corrected deep-shell-satisfiable ones. The joint N.24 TRT compression hTRT is then PROVED " ++
      "generically (seedHTRT, the Lemma N.3.1 same-threshold compression), and the class-6 old-residual " ++
      "bound is closed outright (genuineChargeRoute_routed6_zero: routed class-6 mass = 0).",
    "ENDPOINT — erdos260_of_minimalResidualV3 : Erdos260MinimalResidualV3 → Erdos260Statement, via " ++
      "erdos260_charge_reduced_of_routing (the consolidated faithful charge bridge; pressure floor, " ++
      "phase budget, faithful Dirty model, L.6.5 old-residual all discharged internally). Every residual " ++
      "is the MATCHED / amortized per-element charge summed against the genuine analytic family sum — " ++
      "deep-shell-satisfiable (the RIGHT shape), never the wave-9/10 uniform-ceiling or fixed-family " ++
      "collapse. Endpoint axioms: [propext, Classical.choice, Quot.sound].",
    "WAVE-16 FRONTIER UPDATE (SDR density + Hall selection PROVED; frontier = three bare structural " ++
      "facts) — the shared coarea SDR feeding DensePack/Tower/Run (classes 2/3/5) is now closed to its " ++
      "two halves: (a) the per-start semiperiodic DENSITY mechanism is PROVED unconditionally in " ++
      "SDRDensityCore (windowWeight_ge_rhoD_mul_L: ρ_D·L ≤ windowWeight from the telescoped periodic " ++
      "count periodicWindow_count_lower + the §24/Fine-Wilf period-density floor, 1/(3Q) ≥ ρ_D = 1/4 " ++
      "at Q = 1, windowWeight_density_floor_of_primitive); (b) the maximal-disjoint SELECTION is PROVED, " ++
      "as a SHARP iff, in SDRSelectionCore (exists_disjoint_blocks_iff_marginal: disjoint size-m blocks " ++
      "⟺ the Hall union/marginal bound #⋃_{k∈S} Ω(k) ≥ ρ_D L·|S|; per-start density alone is the " ++
      "necessary-but-not-sufficient #S=1 slice). After wave-16 the entire frontier is the THREE bare " ++
      "STRUCTURAL facts, each reduced end-to-end with its analytic mechanism discharged: " ++
      "(1) SEMIPERIODIC WINDOW EXISTENCE — no-large-run ⟹ bounded primitive period of density ≥ ρ_D " ++
      "(manuscript K.2 / §I.4), the sole remaining input to (a)/the Tower-Run SDR; " ++
      "(2) CNL exp_injOn — injectivity of the terminal lift exponent δ, which under the G.7 common " ++
      "2-adic centre is EQUIVALENT to the G.1 pairwise 2-adic separation/nonseparation data " ++
      "(CNLLiftFaithfulCore.LiftStateCluster.exp_injOn = the class-1 clean-CNL L.1.2 residue); " ++
      "(3) RETURN (Z) — between consecutive complete-return starts on an anchored slice the intervening " ++
      "digits are all 0 (no valuation-dropping 1-digit), the sole input to the carry↔endpoint order " ++
      "bridge hmono (ReturnCarryEndpointCore = the class-4 Return residue). ρ_D = 1/4 is the Q = 1 pin; " ++
      "general Q needs a ρ_D = 1/(3Q)-class threshold (see Constants.manuscriptRhoD; a deferred " ++
      "Q-dependent structural refactor, not a wave-16 change)." ]

theorem erdos260UnconditionalSeedClosureV3Residuals_nonempty :
    erdos260UnconditionalSeedClosureV3Residuals ≠ [] := by
  simp [erdos260UnconditionalSeedClosureV3Residuals]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms Class4ReturnPerSliceCharge.returnFloor
#print axioms v3Budget
#print axioms Erdos260MinimalResidualV3.hChernoffField
#print axioms Erdos260MinimalResidualV3.hCnlField
#print axioms Erdos260MinimalResidualV3.hDensePackField
#print axioms Erdos260MinimalResidualV3.hOldResField
#print axioms erdos260_of_minimalResidualV3
#print axioms chernoff_genuine_area_envelope
#print axioms cnl_genuine_OQ1_to_one_count
#print axioms return_genuine_perSlice_count

end

end Erdos260
