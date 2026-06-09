import Erdos260.ReturnM21LiftCongruenceCore
import Erdos260.DensePackK11SupportCore
import Erdos260.TowerRunMassFractionCore
import Erdos260.ChernoffCNLChargeInjectionCore
import Erdos260.OldResL65Core
import Erdos260.Erdos260GenuineChargedLedgerTight

/-!
# Erdős #260 — the SEED-LEVEL endpoint: every residual class reduced to its bare manuscript seed

This module (NEW; it edits no existing file) consolidates the four **wave-8 manuscript-formalized
seed reductions** into a single final endpoint

```
erdos260_seed_reduced : Erdos260SeedResidual → Erdos260Statement,
```

where each field of `Erdos260SeedResidual` is the *smallest* honest residual its worker isolated —
the irreducible manuscript input geometry, with everything above it proved.  This is strictly
tighter than `erdos260_genuine_charged_reduced_tight`
(`Erdos260GenuineChargedLedgerTight.lean`): four further fields shrink to their bare seeds.

## What each class shrinks to (the bare seed) and how it is fed forward

* **Return (class 4) — the M.2.1 / G.7 self-referential lift congruence (`ofTwoAdicLiftLevels`).**
  The tight ledger carried the *derived gap* `level x + 2^(level x) ≤ level y` (`retChain`).  The
  seed carries instead the **2-adic compatible level assignment**: a level map all of whose class-4
  fibre values reduce to a single common 2-adic centre `Ξ` (`TwoAdicCompatible Ξ`, manuscript G.7).
  The gap — hence the full `ReturnOlcRoutingCharge` and the inverse-tower count `liftLevelBound X` —
  is *built* through the proved `genuineReturnOlcRoutingCharge_ofTwoAdic`
  (`ReturnOlcRoutingCharge.ofTwoAdicLiftLevels`, via the proved `twoAdic_separation`).  Threaded into
  the Return routed-fraction slot via the proved `returnSlot_of_charge` and the K.1.2/L.20
  per-element multiplier + the I.5.1 numeric.

* **DensePack (class 3) — the bare K.1.1 endpoint-disjoint count.**  The tight ledger carried the
  three-field marker landing `GenuineDensePackLanding` (`markerOf`/`lands`/`endpointInj`).  The seed
  carries instead the single count `|genuineDensePackStarts ctx| ≤ |densePackPoints|`.  The marker
  landing — hence the class-3 charge and the J.1.8 summation `routedClassMassOf … 3 ≤ termDensePack`
  — is *built* through the proved `hDensePack_field_ofCardLe` (the order-rank matching
  `GenuineDensePackLanding.ofCardLe`), with the J.D unit charge discharged from the active-window gap.

* **Tower (class 2) — the I.4.1 dense-packing mass fraction (no count).**  The tight ledger carried
  the *free* count×multiplier `countTower`/`hbudTower`.  The seed carries instead the genuine I.4.1
  mass bound `routedClassMassOf … 2 ≤ ξ·s·X·|I_j|` + the layer normalisation `s·|I_j| ≤ 1/6`.  The
  Tower routed-fraction slot is produced from the **mass fraction**, with NO free count, through the
  proved `towerMassFraction_slot` (inside `TowerRunMassFractionData.toBudget`).

* **Run (class 5) — the I.5.2 run-mass floor (no count).**  The tight ledger carried the *free*
  count×multiplier `countRun`/`hbudRun`.  The seed carries instead the genuine I.5.2 floor
  `routedClassMassOf … 5 ≤ c⋆ξX/6` (the L.4.2 period-descent output bound), with NO free count.

* **Chernoff (class 0) / clean-CNL (class 1) — the genuine charge-injection maps.**  The seed carries
  the `Class0ChernoffInjection` (the 22.1A shell-paid embedding into the Chernoff high-cost family +
  K.1.3 endpoint disjointness + the area-side weight cap) and the `Class1CNLInjection` (the L.1.2
  cluster reconstruction into the surviving clean-CNL family + bounded-multiplicity injectivity + the
  G.6/G.35 per-codeword Kraft rate).  The per-element charge domination is *derived* from the gap
  geometry inside each producer; `hChernoffField` / `hCnlField` produce the exact `hChernoff` / `hCnl`
  ledger bounds.

## How the endpoint is proved

The four TRT-level seeds (Return congruence, Tower fraction, Run floor) build a single
`SeparatedPhaseRoutedBudget` through the wave-8 producer `TowerRunMassFractionData.toBudget`, with the
route pinned to the genuine first-obstruction route `genuineChargeRoute` and the Return slot supplied
from the M.2.1 congruence.  Against that budget the Chernoff/CNL injection maps and the DensePack
count produce the `hChernoff` / `hCnl` / `hDensePack` bounds; the joint Tower+Return+Run `hTRT` is the
N.24 same-threshold compression (proved generically here); and the class-6 old-residual bound is
closed outright (`genuineChargeRoute_routed6_zero`).  The five bounds + budget feed the consolidated
faithful charge capstone `erdos260_charge_reduced_of_routing` (whose L.6.5 smallness, constants, phase
budgets/capacities, N.24 spine, faithful Dirty model and pressure floor are all discharged
internally).  No protected endpoint is weakened; nothing is fabricated.

No `sorry`, `axiom`, or `admit`.  No degenerate/empty/identity/full-mass shortcut.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The seed-level Tower+Return+Run data (the budget seeds)

`SeedTRTData` carries, per failure context, the three TRT-class seeds that determine the shared
`SeparatedPhaseRoutedBudget` over the genuine route:

* Return (4): the M.2.1 / G.7 **2-adic compatible lift-height congruence** (the `ofTwoAdicLiftLevels`
  inputs), plus the K.1.2/L.20 per-element multiplier and the I.5.1 numeric used to thread the
  *derived* inverse-tower count `liftLevelBound X` into the Return routed-fraction slot;
* Tower (2): the I.4.1 dense-packing **mass fraction** + layer normalisation (NO free count);
* Run (5): the I.5.2 run-mass **floor** (NO free count). -/

/-- **The seed-level Tower+Return+Run data.**  Determines the shared budget from the bare manuscript
seeds: the Return M.2.1 2-adic congruence, the Tower I.4.1 mass fraction, and the Run I.5.2 floor. -/
structure SeedTRTData where
  /-- **Return seed (M.2.1 / G.7).**  The self-referential lift-height level assignment of the
  long-return class-4 starts. -/
  retLevel : ∀ _ctx : ActualFailureContext, ℕ → ℕ
  /-- **Return seed (G.7 common 2-adic centre).**  The single 2-adic centre `Ξ` to which all class-4
  fibre levels reduce. -/
  retXi : ∀ _ctx : ActualFailureContext, ℤ
  /-- **M.2.1 shell-scale bound** — every class-4 start's nesting level sits below the shell `X`. -/
  retBound : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4, retLevel ctx k ≤ ctx.shell.X
  /-- **The M.2.1 self-referential lift congruence (G.7 form, the bare seed)** — every class-4 fibre
  level is `TwoAdicCompatible (retXi ctx)`, i.e. `δ ≡ Ξ (mod 2^{δ})`.  The gap
  `level x + 2^(level x) ≤ level y` is *derived* from this through `twoAdic_separation`. -/
  retCompat : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      TwoAdicCompatible (retXi ctx) (retLevel ctx k)
  /-- **M.2.1 endpoint disjointness** — distinct class-4 starts receive distinct nesting levels. -/
  retInj : ∀ ctx : ActualFailureContext,
    ∀ x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      ∀ y ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
        retLevel ctx x = retLevel ctx y → x = y
  /-- Return (class 4) per-fibre window-excess multiplier (K.1.2/L.20). -/
  multReturn : ∀ _ctx : ActualFailureContext, ℝ
  /-- Every genuine-route class-4 start charges window excess `≤ multReturn`. -/
  hpointReturn : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multReturn ctx
  /-- The Return multiplier is nonnegative. -/
  hmultReturn_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ multReturn ctx
  /-- The I.5.1 numeric `liftLevelBound X · multReturn ≤ c⋆ξX/6` over the *derived* M.2.1 count. -/
  hbudReturn : ∀ ctx : ActualFailureContext,
    (liftLevelBound ctx.shell.X : ℝ) * multReturn ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  /-- The I.4.1 active threshold-layer order `s` (`s ≍ L`). -/
  towerS : ∀ _ctx : ActualFailureContext, ℝ
  /-- The I.4.1 active threshold-layer interval length `|I_j|`. -/
  towerIj : ∀ _ctx : ActualFailureContext, ℝ
  /-- **Layer normalisation** — the single active layer measure `s·|I_j|` is at most the `1/6`
  per-phase budget share. -/
  htowerLayer : ∀ ctx : ActualFailureContext, towerS ctx * towerIj ctx ≤ 1 / 6
  /-- **The I.4.1 dense-packing mass fraction (the bare seed, no count)** — the Tower-routed (class 2)
  mass is at most `ξ·s·X·|I_j|` under the positive-density failure hypothesis. -/
  htowerFraction : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * towerS ctx * (ctx.shell.X : ℝ) * towerIj ctx
  /-- **The I.5.2 run-mass floor (the bare seed, no count)** — the Run-routed (class 5) mass fits
  `c⋆·ξ·X/6` (the L.4.2 period-descent output bound). -/
  hrunFloor : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6

namespace SeedTRTData

/-- **The Return OLC routing charge, BUILT from the 2-adic compatible lift congruence.**  Through the
proved `genuineReturnOlcRoutingCharge_ofTwoAdic` (`ReturnOlcRoutingCharge.ofTwoAdicLiftLevels`, via
the proved `twoAdic_separation`), the M.2.1 / G.7 common-2-adic-centre level assignment produces the
full `ReturnOlcRoutingCharge` for the genuine route — so the inverse-tower count `liftLevelBound X` is
still *derived*. -/
def retCharge (D : SeedTRTData) (ctx : ActualFailureContext) :
    ReturnOlcRoutingCharge (genuineChargeRoute ctx) ctx :=
  genuineReturnOlcRoutingCharge_ofTwoAdic ctx (D.retLevel ctx) (D.retXi ctx)
    (D.retBound ctx) (D.retCompat ctx) (D.retInj ctx)

/-- **The Return routed-fraction slot, from the 2-adic congruence + multiplier + I.5.1 numeric.**
The M.2.1 charge forces the count `|routedFibre 4| ≤ liftLevelBound X` (`fibreCard_le_liftLevelBound`);
`returnSlot_of_charge` (`routedClassMassOf_le_countMultiplier`) then threads it, with the K.1.2/L.20
multiplier and the I.5.1 numeric `hbudReturn`, into `routedClassMassOf … 4 ≤ c⋆ξX/6`. -/
theorem returnSlot (D : SeedTRTData) (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  returnSlot_of_charge ctx (genuineChargeRoute ctx) (D.hpointReturn ctx) (D.hmultReturn_nonneg ctx)
    (show ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).card : ℝ)
        ≤ (liftLevelBound ctx.shell.X : ℝ) from by
      exact_mod_cast (D.retCharge ctx).fibreCard_le_liftLevelBound)
    (D.hbudReturn ctx)

/-- **The wave-8 Tower+Run mass-fraction data, from the seeds.**  Packages the genuine route, the
I.4.1 Tower mass fraction (`towerS`/`towerIj`/`htowerLayer`/`htowerFraction`), the I.5.2 Run floor
(`hrunFloor`), and the Return slot derived from the M.2.1 congruence. -/
def toMassFractionData (D : SeedTRTData) : TowerRunMassFractionData where
  route := fun ctx => genuineChargeRoute ctx
  towerS := D.towerS
  towerIj := D.towerIj
  htowerLayer := D.htowerLayer
  htowerFraction := D.htowerFraction
  hrunFloor := D.hrunFloor
  returnSlot := D.returnSlot

/-- **The shared budget, built from the bare seeds with NO free Tower/Run count.**  The Tower slot is
the I.4.1 mass fraction, the Run slot is the I.5.2 floor (both via `TowerRunMassFractionData.toBudget`,
i.e. the proved `towerMassFraction_slot`), and the Return slot is the M.2.1 congruence-derived slot.
The route is the genuine first-obstruction route `genuineChargeRoute`. -/
def toBudget (D : SeedTRTData) : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  D.toMassFractionData.toBudget

/-- The seed budget routes through `genuineChargeRoute`. -/
@[simp] theorem toBudget_route (D : SeedTRTData) (ctx : ActualFailureContext) :
    (D.toBudget ctx).route = genuineChargeRoute ctx := rfl

end SeedTRTData

/-! ## 2.  The joint N.24 TRT compression bound, for any seed budget

The Tower+Return+Run `hTRT` field of the consolidated residual is the manuscript N.24 same-threshold
compression, proved generically (for any budget) through the genuine Lemma N.3.1 compression
`routedTRT_le_packageTerms_fin7` at the non-degenerate same-threshold output family
`trtSameThresholdOutput` — the same proof as `ChargeClassTRTData.hTRT`, here over an arbitrary budget
so it applies to the mass-fraction seed budget. -/

/-- **The joint N.24 same-threshold TRT compression bound, for any budget.** -/
theorem seedHTRT (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 2
        + routedClassMassOf ctx.n24CarryData (budget ctx).route 4
        + routedClassMassOf ctx.n24CarryData (budget ctx).route 5
      ≤ termTower (faithfulCapacityPhases budget ctx).toClosurePhaseData
        + termReturn (faithfulCapacityPhases budget ctx).toClosurePhaseData
        + termRun (faithfulCapacityPhases budget ctx).toClosurePhaseData := by
  refine routedTRT_le_packageTerms_fin7
    (trtSameThresholdOutput ctx (budget ctx).route)
    (faithfulCapacityPhases budget ctx) ctx.n24CarryData (budget ctx).route ?_ ?_
  · exact le_of_eq (trtSameThresholdOutput_branchSum ctx (budget ctx).route).symm
  · rw [termTower_faithfulCapacityPhases, termReturn_faithfulCapacityPhases,
      termRun_faithfulCapacityPhases]
    exact le_of_eq (trtSameThresholdOutput_groundMass ctx (budget ctx).route)

/-- **The class-6 old-residual bound is closed outright for the seed budget.**  The genuine route
never assigns class 6 (`genuineChargeRoute_routed6_zero`), so the routed class-6 mass is `0`, which is
dominated by the nonnegative genuine L.6.4 branch mass — discharging `hOldRes` from
`erdos260_charge_reduced_of_routing` with no residual. -/
theorem seedHOldRes (D : SeedTRTData) (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (D.toBudget ctx).route 6
      ≤ ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k := by
  rw [D.toBudget_route ctx, genuineChargeRoute_routed6_zero ctx]
  exact oldResL65_branchMass_nonneg ctx

/-! ## 3.  The seed residual — every class reduced to its bare manuscript seed -/

/-- **The seed-level residual of Erdős #260.**

Every surviving class reduced to its smallest honest manuscript seed:

* `trt` — the seed-level Tower+Return+Run data: the Return M.2.1 / G.7 2-adic congruence (the
  `ofTwoAdicLiftLevels` inputs), the Tower I.4.1 dense-packing mass fraction, and the Run I.5.2
  run-mass floor (Tower/Run with NO free count);
* `chernoff` — the class-0 Chernoff (22.1A) charge-injection map (`Class0ChernoffInjection`);
* `cnl` — the class-1 clean-CNL (L.1.2/G.35) charge-injection map (`Class1CNLInjection`);
* `densePackCard` — the bare class-3 K.1.1 endpoint-disjoint count
  `|genuineDensePackStarts ctx| ≤ |densePackPoints|`;
* `densePackG0`/`densePackGap`/`densePackScale` — the active-window gap structure from which the
  class-3 J.D unit charge is discharged. -/
structure Erdos260SeedResidual where
  /-- The seed-level Tower+Return+Run data (Return M.2.1 congruence, Tower I.4.1 fraction, Run I.5.2
  floor). -/
  trt : SeedTRTData
  /-- **Class 0 — Chernoff (22.1A) charge injection.**  The J.1.7 charge map of the progress starts
  into the Chernoff high-cost family with the area-side weight cap and K.1.3 endpoint disjointness. -/
  chernoff : Class0ChernoffInjection trt.toBudget
  /-- **Class 1 — clean-CNL (L.1.2/G.35) charge injection.**  The J.1.1 charge map of the class-1
  starts into the surviving clean-CNL family with the G.6 per-codeword Kraft rate and the L.1.2
  bounded-multiplicity injectivity. -/
  cnl : Class1CNLInjection trt.toBudget
  /-- **Class 3 — the bare K.1.1 endpoint-disjoint count (the seed).**  Each high-excess dense start
  occupies a distinct dense-marker interval: `|genuineDensePackStarts ctx| ≤ |densePackPoints|`. -/
  densePackCard : ∀ ctx : ActualFailureContext,
    (genuineDensePackStarts ctx).card ≤ (densePackMarkers trt.toBudget ctx).card
  /-- The active-window gap ceiling on the class-3 descent window (for the J.D unit charge). -/
  densePackG0 : ActualFailureContext → ℕ
  /-- The active-window gap bound on the class-3 descent window. -/
  densePackGap : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (trt.toBudget ctx).route 3,
      ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ densePackG0 ctx
  /-- The K.1.2 active-floor scaling giving the J.D unit charge `windowExcess ≤ 1`. -/
  densePackScale : ∀ ctx : ActualFailureContext,
    ((ctx.n24CarryData.r : ℝ) + 1) * (densePackG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1

namespace Erdos260SeedResidual

/-- **The class-3 `hDensePack` bound, BUILT from the bare K.1.1 count.**  Through the proved
`hDensePack_field_ofCardLe` (the order-rank matching `GenuineDensePackLanding.ofCardLe` + the J.1.8
summation), the single endpoint-disjoint count and the active-window gap structure produce the exact
`routedClassMassOf … 3 ≤ termDensePack` ledger bound. -/
theorem hDensePack (R : Erdos260SeedResidual) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (R.trt.toBudget ctx).route 3
        ≤ termDensePack (faithfulCapacityPhases R.trt.toBudget ctx).toClosurePhaseData :=
  hDensePack_field_ofCardLe R.trt.toBudget (fun _ctx => rfl) R.densePackCard
    R.densePackG0 R.densePackGap R.densePackScale

end Erdos260SeedResidual

/-! ## 4.  The seed-level endpoint — Erdős #260 from the bare manuscript seeds -/

/-- **Erdős #260, reduced to the bare manuscript-seed residual.**

From `Erdos260SeedResidual` — the genuine route `genuineChargeRoute`, the Return M.2.1 / G.7 2-adic
lift congruence, the Tower I.4.1 dense-packing mass fraction, the Run I.5.2 run-mass floor, the
Chernoff (22.1A) and clean-CNL (L.1.2/G.35) charge-injection maps, and the bare DensePack K.1.1
endpoint-disjoint count — the consolidated faithful charge capstone `erdos260_charge_reduced_of_routing`
proves `Erdos260Statement`.

Each seed is fed through its wave-8 producer:

* Return congruence → `genuineReturnOlcRoutingCharge_ofTwoAdic` → the Return slot (`returnSlot`);
* Tower fraction + Run floor → `TowerRunMassFractionData.toBudget` (the budget, NO free count);
* DensePack count → `hDensePack_field_ofCardLe` → the `hDensePack` bound;
* Chernoff/CNL injections → `hChernoffField` / `hCnlField` → the `hChernoff` / `hCnl` bounds;
* the joint N.24 TRT compression (`seedHTRT`) and the class-6 closure (`seedHOldRes`) are proved here.

The L.6.5 old-residual smallness, the constants, the phase budgets/capacities, the N.24 spine, the
faithful Dirty model and the Lemma 21.1 pressure floor are all discharged internally by
`erdos260_charge_reduced_of_routing`.  No protected endpoint is weakened.

No `sorry`/`axiom`/`admit`. -/
theorem erdos260_seed_reduced (R : Erdos260SeedResidual) : Erdos260Statement :=
  erdos260_charge_reduced_of_routing R.trt.toBudget
    R.chernoff.hChernoffField
    R.cnl.hCnlField
    R.hDensePack
    (seedHTRT R.trt.toBudget)
    (seedHOldRes R.trt)

/-! ## 5.  Honest residual inventory — the bare seeds, everything above them proved -/

/-- The precise per-class status of the seed-level endpoint, naming the bare seed of each class. -/
def seedResiduals : List String :=
  [ "SEED (class 4, Return — M.2.1 / G.7 congruence) — trt.retLevel/retXi/retBound/retCompat/retInj: " ++
      "the 2-adic compatible lift-height level assignment (every class-4 fibre level reduces to one " ++
      "common 2-adic centre Ξ, δ ≡ Ξ mod 2^δ). The gap level x + 2^(level x) ≤ level y, the full " ++
      "ReturnOlcRoutingCharge, and the inverse-tower count liftLevelBound X are all BUILT via the " ++
      "proved genuineReturnOlcRoutingCharge_ofTwoAdic (twoAdic_separation). Smaller than the tight " ++
      "ledger's derived-gap retChain.",
    "SEED (class 3, DensePack — K.1.1 count) — trt-budget densePackCard: the bare endpoint-disjoint " ++
      "count |genuineDensePackStarts ctx| ≤ |densePackPoints|. The three-field marker landing " ++
      "(markerOf/lands/endpointInj) and the class-3 charge are BUILT via the proved " ++
      "hDensePack_field_ofCardLe (the order-rank matching GenuineDensePackLanding.ofCardLe + J.1.8 " ++
      "summation). Smaller than the tight ledger's GenuineDensePackLanding.",
    "SEED (class 2, Tower — I.4.1 fraction, NO count) — trt.towerS/towerIj/htowerLayer/htowerFraction: " ++
      "the genuine I.4.1 dense-packing MASS fraction routedClassMassOf … 2 ≤ ξ·s·X·|I_j| + the layer " ++
      "normalisation s·|I_j| ≤ 1/6. The Tower routed-fraction slot is produced from the mass fraction " ++
      "via TowerRunMassFractionData.toBudget (towerMassFraction_slot), with NO free count. Smaller " ++
      "than the tight ledger's free countTower/hbudTower.",
    "SEED (class 5, Run — I.5.2 floor, NO count) — trt.hrunFloor: the genuine I.5.2 run-mass floor " ++
      "routedClassMassOf … 5 ≤ c⋆ξX/6 (the L.4.2 period-descent output bound). NO free count. Smaller " ++
      "than the tight ledger's free countRun/hbudRun.",
    "SEED (class 0, Chernoff — 22.1A injection) — chernoff : Class0ChernoffInjection: the J.1.7 charge " ++
      "map of the progress starts into the Chernoff high-cost family + the 22.1A area-side weight cap + " ++
      "K.1.3 endpoint disjointness. hChernoffField produces the exact hChernoff bound; the per-path " ++
      "domination is DERIVED from the gap geometry.",
    "SEED (class 1, clean-CNL — L.1.2/G.35 injection) — cnl : Class1CNLInjection: the J.1.1 charge map " ++
      "of the class-1 starts into the surviving clean-CNL family + the G.6/G.35 per-codeword Kraft rate " ++
      "+ L.1.2 bounded-multiplicity injectivity. hCnlField produces the exact hCnl bound; the " ++
      "per-codeword charge is DERIVED from the gap geometry.",
    "PROVED ABOVE THE SEEDS — the Return slot (returnSlot_of_charge over the derived count), the " ++
      "Tower/Run slots (the budget via TowerRunMassFractionData.toBudget), the class-3 charge " ++
      "(hDensePack_field_ofCardLe), the joint N.24 TRT compression (seedHTRT), and the class-6 " ++
      "old-residual closure (seedHOldRes via genuineChargeRoute_routed6_zero). Everything is fed into " ++
      "erdos260_charge_reduced_of_routing.",
    "ENDPOINT — erdos260_seed_reduced : Erdos260SeedResidual → Erdos260Statement. The route is FORCED " ++
      "to genuineChargeRoute; the budget is built from the bare seeds with no free Tower/Run count; no " ++
      "protected endpoint is weakened. The seeds are the irreducible manuscript input geometry." ]

theorem seedResiduals_nonempty : seedResiduals ≠ [] := by
  simp [seedResiduals]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms erdos260_seed_reduced
#print axioms SeedTRTData.retCharge
#print axioms SeedTRTData.returnSlot
#print axioms SeedTRTData.toBudget
#print axioms seedHTRT
#print axioms seedHOldRes
#print axioms Erdos260SeedResidual.hDensePack

end

end Erdos260
