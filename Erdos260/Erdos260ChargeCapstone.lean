import Erdos260.ReturnCaseSplitRebase

/-!
# The charge capstone — the Return lane re-based onto the charge-level interface
(`Erdos260ChargeCapstone`)

This module (NEW; it edits no existing file) performs the re-basing identified by
`ReturnCaseSplitRebase`: the capstone Return lane is moved off the wave-8..12 digit-transport
chain and onto the CHARGE-level interface, so the strictly weaker envelope residual
`SliceDirtyEnvelope` (the (M.1) envelope demanded only on (Z)-failing slices) genuinely enters
the endpoint, and the Q-even lane is folded into one parity-free field.

NAMING NOTE (honest): the brief's name `Erdos260ChargeResidual` is already taken by the
(unrelated) consolidated faithful charge surface of `Erdos260ChargeReduced` (in the same
transitive import closure), so the new surface here is named `Erdos260ReturnChargeResidual`,
with endpoint `erdos260_of_returnChargeResidual`.

## The junction map (goal 1, found exactly)

The wave-12 key surface's Return digit fields feed the final ledger through ONE junction:

* `Erdos260KeyResidual.{returnKeyInjective, returnZeroQEvenFloor}` are transported by the
  wave-12→11→10→9→8 bridges as `ReturnZeroBody`/trajectory shapes
  (`Erdos260KeyCapstone.toSplit` → `Erdos260SplitCapstone.toThirdsExclusion` →
  `ThirdsExclusionLever.toValuation` → `Erdos260ValuationCapstone.toFloorPushV2` →
  `FloorPushV2.toTrajectoryResidual` → `Erdos260TrajectoryCapstone.toPushResidual` →
  `Erdos260PushCapstone.toScaleFloorPush` → `ScaleFloorHarvest`/`Erdos260RigidityCapstone` →
  `DigitSideClosure.toEnum` → `Erdos260EnumCapstone.toCycle`), landing in the wave-3 cycle
  fields `returnZero` / `returnMaxClean` / `returnInterior` / `returnGates`.
* THE JUNCTION is `Erdos260CycleResidual.toSharp`:
  `returnSmall := class4FibreSmall_of_gates returnGates` (the count) and
  `returnDigit := ReturnClass4DigitResidual.ofSelfRefMaxCleanStep (returnZero, returnMaxClean,
  returnInterior)` (the digit triple).  The sharp capstone then builds
  `returnZ := returnZResidualsOfDigitAndCount returnSmall returnDigit` (the Z-residual family,
  where the count supplies `hnumeric` via `return_hnumeric_of_fibre_card_le` and `hgapDiv` is a
  THEOREM at the self-referential key), and the six-atom capstone consumes `returnZ` ONLY
  through `returnChargeOfZResiduals returnZ = fun ctx => (returnZ ctx).toCharge` — i.e. only as
  the family `forall ctx, Class4ReturnPerSliceCharge ctx` inside `sixAtomBudget` (= `v3Budget`).
  The other six-atom fields (`class0Empty`, `class1Empty`, `densePack`) are merely STATED at
  that budget; their proofs (`class0FibreEmpty_of_genuineRoute_pinned`,
  `class1FibreEmpty_of_pinned_arithmetic_sharp`, `DensePackCycleSplitResidual.toRegimeSplit` +
  `toCorrected`) are generic in the budget/charge family.  NOTHING downstream consumes the
  Z-residual family beyond the charge: `hgapDiv` is a theorem on this route, `returnFloor` and
  `perSliceCount` are consequences of the charge, and the `class4Interior`/`hnumeric` content
  is exactly what `ReturnCaseSplitChargeResidual.{class4Interior, hnumeric}` carries.
* Therefore the splice point is the budget's Return slot, and
  `ReturnCaseSplitChargeResidual.toCharge` (the rebase module's charge rebuild from
  `SliceDirtyEnvelope` + interior + numeric, with NO digit field and NO clean-step field)
  plugs in directly.

## The `returnMaxClean` verdict (goal 2, honest)

The charge route needs NO `returnMaxClean` content: `ReturnCaseSplitChargeResidual.ofSelfRefZ`
drops both `hzero` and `hcleanStep`, and `Class4ReturnPerSliceCharge.ofDirtyEnvelope`
manufactures the per-slice M.2.1 data from counts alone (`OlcSliceData.ofCardLe`, the
order-rank tower assignment).  On the OLD route the maxClean fields' sole downstream role was
the clean step `d(max+1) = 0` consumed by `returnCleanRunOfZeroData` to build the anchored
clean-run family behind `OlcSliceData`; on the charge route that construction is REPLACED by
the counting constructor.  The only other in-tree consumers of the maxClean shapes are the
predecessor-surface equivalence records (the wave-9 trajectory forms etc.), none of which lie
on this endpoint's route.  VERDICT: both `returnMaxClean` fields (Q odd parity-reduced, Q even
trajectory) DISAPPEAR from the surface entirely.

## The new surface (goal 2)

`Erdos260ReturnChargeResidual` := the wave-12 key surface with the FOUR Return digit-shaped
fields (`returnKeyInjective`, `returnZeroQEvenFloor`, `returnMaxCleanQOddParityReduced`,
`returnMaxCleanQEven`) replaced by the SINGLE parity-free field
`returnDirtyEnvelope : ReturnDirtyEnvelopeField` — `SliceDirtyEnvelope ctx` under the verbatim
wave-8 guards, at BOTH parities at once (the Q-even lane is folded: the parity hypothesis is
gone, and the Q-even extra dyadic-floor guard `2^{v2(Q)} < W` is dropped because it is FREE
given the carry-valuation guard, `width_gt_of_returnZero_guard`).  The interior and numeric
fields of `ReturnCaseSplitChargeResidual` are supplied by the key surface's KEPT verbatim
fields: `returnInterior` (the K.1 interior under the band-2-free guard) and `returnGates` (the
count gates, which manufacture `hnumeric` through `class4FibreSmall_of_gates` +
`return_hnumeric_of_fibre_card_le`).  12 fields verbatim + 1 new field = 13 fields
(16 - 4 + 1).

## The endpoint (goal 3) and the strictness verdict (honest)

`erdos260_of_returnChargeResidual` composes PUBLIC bridges only: the non-Return lanes walk the
same per-lane discharges the wave-12..3 chain applies (`towerModulusEnumEscape_iff_v2` +
`thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven` + `towerTail_of_order_gt` for Tower;
`runTail_of_order_gt` + `runCycleNumericField_settled` for Run; `class0Tail_of_order_gt` +
`class0Cycle_of_survivor_residue_split` for class 0; `class1Tail_of_band4FreePeriod` +
`class1PairResidual_of_deepOnly` + `class1DeepResidual_of_pairResidual` for class 1; the
DensePack `toGatedClosure → toDatumSplit → toCycleSplit → toRegimeSplit → toCorrected` chain);
the Return lane is spliced at the junction as the charge family
`fun ctx => (chargeData R ctx).toCharge`, with the guard-failing contexts discharged by the
SAME closures the chain uses (`returnCtxAllFour_of_b2FreeDatum`,
`returnGatesZeroCard_of_b2OneSpacedDatum`, `returnZero_of_carryVal2_large`,
`returnZeroBody_of_indexWindowClean` — each mapped through
`sliceDirtyEnvelope_of_returnZeroBody`); the ledger is the ctx-pinned P9 ledger exactly as in
`Erdos260SixAtomResidual.toLedger` (`seedHTRT`, `genuineChargeRoute_routed6_zero`, the
budget-generic Chernoff/CNL/DensePack field lemmas).

STRICTNESS (honest): the weakening witness `returnChargeResidual_of_keyResidual` rebuilds the
new surface from any key provider (`sliceDirtyEnvelope_of_keyInjOn` on the Q-odd lane; the
parity-free master equivalence `returnZeroBody_iff_keyInjOn_uncond` +
`sliceDirtyEnvelope_of_returnZeroBody` on the Q-even lane; the maxClean fields are simply
dropped).  NO CONVERSE IS CLAIMED, and it should not exist as a derivation: the envelope
admits dirty slices with up to `liftLevelBound X` members which `ReturnKeyInjOn` forbids
outright, and the surface retains no clean-step field from which the maxClean digit content
could be rebuilt (the honest `DirtyWindowCountCore` finding shows the in-tree dirty model
cannot even deliver absolute-constant fibre counts).  This is the first capstone surface since
wave 8 whose demanded content is strictly WEAKER in shape than its predecessor, not an
equivalent re-presentation.  (We do not claim a formal independence proof — that would require
a model construction, not attempted here.)

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only — no existing module
is edited (the root import file gains one line).
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The parity-folded dirty-envelope field

The rebase module proved the collapse engine parity-free (`returnZeroBody_iff_keyInjOn_uncond`),
so ONE field serves both parities.  The Q-even lane's extra dyadic-floor guard `2^{v2(Q)} < W`
is dropped: it is free given the carry-valuation guard (`width_gt_of_returnZero_guard`). -/

/-- **The parity-free dirty-envelope field**: under the verbatim wave-8 guards (band-2-free
datum, spaced `b2 = 1` datum, the small-carry regime, index-window separation — NO parity
hypothesis, NO dyadic-floor guard), slices of the self-referential key carrying a dirty
crossing datum obey the (M.1) envelope `|slice| <= liftLevelBound X`.  This is the WHOLE
Return-zero demand of the charge route, replacing all four digit-shaped key fields. -/
def ReturnDirtyEnvelopeField : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    SliceDirtyEnvelope ctx

/-- **The weakening witness at the field level**: the two key-surface returnZero-shaped fields
(Q-odd key injectivity, Q-even dyadic-floor trajectory) supply the parity-free envelope field.
Q odd: injectivity forbids dirty slices outright (`sliceDirtyEnvelope_of_keyInjOn`).  Q even:
the dropped dyadic-floor guard is free (`width_gt_of_returnZero_guard`), the trajectory form
rebuilds `ReturnZeroBody` (`returnZeroBody_iff_belowBandTrajectory_uncond`), and the envelope
follows (`sliceDirtyEnvelope_of_returnZeroBody`).  No converse is claimed. -/
theorem returnDirtyEnvelopeField_of_keyFields
    (hOdd : ReturnKeyInjectiveField) (hEven : ReturnZeroQEvenFloorField) :
    ReturnDirtyEnvelopeField := by
  intro ctx hA hB hC hD
  rcases Nat.mod_two_eq_zero_or_one ctx.Q with hQ | hQ
  · exact sliceDirtyEnvelope_of_returnZeroBody ctx
      ((returnZeroBody_iff_belowBandTrajectory_uncond ctx).mpr
        (hEven ctx hA hB hC hD (width_gt_of_returnZero_guard ctx hC) hQ))
  · exact sliceDirtyEnvelope_of_keyInjOn ctx (hOdd ctx hA hB hC hD hQ)

/-- The parity-free field strengthens the rebase module's named Q-odd-only gap target
`ReturnDirtyEnvelopeQOddField` (the parity hypothesis is simply absorbed). -/
theorem dirtyEnvelopeQOddField_of_envelopeField
    (h : ReturnDirtyEnvelopeField) : ReturnDirtyEnvelopeQOddField :=
  fun ctx hA hB hC hD _hQ => h ctx hA hB hC hD

/-! ## Part 2.  The charge-based capstone surface -/

/-- **The charge-based capstone surface**: the wave-12 key surface
(`Erdos260KeyResidual`) with ALL FOUR Return digit-shaped fields REPLACED by the single
parity-free dirty-envelope field — `returnKeyInjective` and `returnZeroQEvenFloor` fold into
`returnDirtyEnvelope`; `returnMaxCleanQOddParityReduced` and `returnMaxCleanQEven` DISAPPEAR
(the charge route needs no clean-step content: `OlcSliceData.ofCardLe` replaces the anchored
clean-run construction).  The other 12 fields are verbatim wave-12 shapes; `returnInterior`
and `returnGates` now also serve as the interior/numeric suppliers of the per-slice charge. -/
structure Erdos260ReturnChargeResidual where
  /-- Tower / class 2 - enumerated part (`q < 107`), with the free aperiodicity guard. -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    Class2CycleInequality ctx
  /-- Tower / class 2 - tail (`107 ≤ q`), with the free aperiodicity guard. -/
  towerEnumTail : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx →
    107 ≤ (class1SlopeDatum ctx).q →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx)
      ∨ Class2CycleInequality ctx
  /-- Run / class 5 - enumerated part (`q < 64`); verbatim field. -/
  runNumericLow : ∀ ctx : ActualFailureContext,
    (class1SlopeDatum ctx).q < 64 →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 - tail (`64 ≤ q`); verbatim field. -/
  runNumericTail : ∀ ctx : ActualFailureContext,
    64 ≤ (class1SlopeDatum ctx).q →
    ((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx
    ∨ Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Return / class 4 count gates - verbatim field (now ALSO the `hnumeric` supplier of the
  per-slice charge, through `class4FibreSmall_of_gates`). -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 digit Z, BOTH parities - **the charge-level form**: the (M.1) envelope
  demanded only on slices carrying a dirty crossing datum (replaces `returnKeyInjective` AND
  `returnZeroQEvenFloor`; the `returnMaxClean` fields disappear entirely). -/
  returnDirtyEnvelope : ReturnDirtyEnvelopeField
  /-- Return / class 4 K.1 interior - verbatim field (now ALSO the `class4Interior` supplier
  of the per-slice charge). -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- Chernoff / class 0 survivors - verbatim field. -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    Class0SurvivorResidueMiss ctx
  /-- Chernoff / class 0 mid band - verbatim field. -/
  class0Mid : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
    (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
    Class0WindowCycleCheck ctx
  /-- Chernoff / class 0 large moduli (`96 ≤ q`) - verbatim field. -/
  class0BigOrder : ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
    (∃ C, ((Nat.log 2 (class1SlopeDatum ctx).q + 1) * C
          < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
              (class1SlopeDatum ctx).K₀)))
        ∧ ∃ c, C < c ∧ c ≤ (class1SlopeDatum ctx).q
            ∧ (∀ m, 1 ≤ m →
                slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
                  = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
            ∧ ∀ k ∈ ctx.n24CarryData.starts,
                129 * shellLadderDepth ctx + 64
                    ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
                (class1SlopeDatum ctx).q
                  < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
                      (cycleRep c k))
    ∨ Class0WindowCycleCheck ctx
  /-- CNL / class 1 - enumerated deep part (`q < 101`), with the free aperiodicity guard. -/
  class1DeepLow : ∀ ctx : ActualFailureContext,
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    ¬ Class1DatumClosed ctx →
    ¬ Class1GcdWindowMiss ctx →
    (class1SlopeDatum ctx).q < 101 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅
  /-- CNL / class 1 - tail (`101 ≤ q`); verbatim field. -/
  class1DeepTail : ∀ ctx : ActualFailureContext,
    101 ≤ (class1SlopeDatum ctx).q →
    Class1Band4FreePeriod ctx
    ∨ (64 ∣ shellLadderDepth ctx →
        9 ≤ (class1SlopeDatum ctx).q →
        ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
        (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
        ¬ Class1DatumClosed ctx →
        ¬ Class1GcdWindowMiss ctx →
        routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅)
  /-- DensePack / class 3 - verbatim field. -/
  densePackUngated : DensePackUngatedClosureResidual

namespace Erdos260ReturnChargeResidual

/-! ## Part 3.  The non-Return lanes, walked to the junction

Each lane composes EXACTLY the public per-lane discharges the wave-12..3 chain applies to it
(`toThirdsExclusion`'s aperiodicity voiding, `toTrajectoryResidual`'s escape conversion, the
rigidity capstone's tail-order closures, the digit-side/enum case splits).  Nothing is
re-proved. -/

/-- Tower lane → the wave-5 enumeration residual: aperiodicity guard discharged by the master
voiding theorem, the `q = 9` escape guard restored through the pointwise escape equivalence,
the `107 ≤ q` tail closed by the order criterion or the verbatim fallback disjunct. -/
def towerEnum (R : Erdos260ReturnChargeResidual) : TowerModulusEnumerationResidual := by
  intro ctx _hdeep hesc
  have hescV2 : TowerModulusEnumEscapeV2 ctx :=
    (towerModulusEnumEscape_iff_v2 ctx).mp hesc
  have haper : ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx := fun hu7 hwp =>
    thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven ctx hu7 hwp
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 107 with hlt | hge
  · exact R.towerEnumLow ctx hescV2 hlt haper
  · cases R.towerEnumTail ctx hescV2 hge haper with
    | inl ho => exact towerTail_of_order_gt ctx ho.1 ho.2
    | inr hineq => exact hineq

/-- Run lane → the wave-5 settlement hypothesis (the `64 ≤ q` tail closed by the order
criterion or the verbatim fallback). -/
def runNumeric (R : Erdos260ReturnChargeResidual) : RunCycleNumericSettlementHyp := by
  intro ctx _hr
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 64 with hlt | hge
  · exact R.runNumericLow ctx hlt
  · cases R.runNumericTail ctx hge with
    | inl ho => exact Or.inr (runTail_of_order_gt ctx ho.1 ho.2)
    | inr hrun => exact hrun

/-- Class-0 lane → the wave-3 windowed cycle check (survivor congruence misses, the
shallow-meeting mid band, and the order-pruned `96 ≤ q` certificate). -/
def class0Cycle (R : Erdos260ReturnChargeResidual) : ∀ ctx : ActualFailureContext, Class0WindowCycleCheck ctx :=
  class0Cycle_of_survivor_residue_split R.class0Survivor R.class0Mid
    (fun ctx h96 => by
      cases R.class0BigOrder ctx h96 with
      | inl hcert =>
          obtain ⟨C, horder, hcheck⟩ := hcert
          exact class0Tail_of_order_gt ctx C horder hcheck
      | inr hwin => exact hwin)

/-- Class-1 lane → the wave-3 deep residual (aperiodicity guard discharged, the `101 ≤ q` tail
closed by the band-4-free period or the verbatim fallback, the `r = 0` `topStart` field closed
by `class1PairTopStart_settled` inside `class1PairResidual_of_deepOnly`). -/
def class1Deep (R : Erdos260ReturnChargeResidual) : Class1DeepResidual :=
  class1DeepResidual_of_pairResidual (class1PairResidual_of_deepOnly
    (fun ctx _hr hdvd h9 hwin hcl hdc hgcd => by
      have haper : ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx := fun hu7 hwp =>
        thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven ctx hu7 hwp
      rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 101 with hlt | hge
      · exact R.class1DeepLow ctx hdvd h9 hwin hcl hdc hgcd hlt haper
      · cases R.class1DeepTail ctx hge with
        | inl hfree => exact class1Tail_of_band4FreePeriod ctx hfree
        | inr hdeep => exact hdeep hdvd h9 hwin hcl hdc hgcd))

/-! ## Part 4.  The Return lane, spliced at the charge junction

The guard-failing contexts are discharged by the SAME closures the chain's `toEnum`/`toCycle`
bridges fire, each mapped into the envelope through `sliceDirtyEnvelope_of_returnZeroBody`;
the demanded contexts consume the surface's envelope field DIRECTLY — the digit transport of
waves 8..12 is gone from this lane. -/

/-- The wave-3 4-way gate disjunction from the surface gates field (the dead K.1-gate
disjunct restored through `returnGatesBody_iff_ungated`; the closed regimes through the
span-gate closures, exactly as `Erdos260EnumCapstone.toCycle`). -/
def returnGatesCycle (R : Erdos260ReturnChargeResidual) : ∀ ctx : ActualFailureContext, ReturnGatesBody ctx := fun ctx => by
  by_cases hfree : ReturnB2FreeDatum ctx
  · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).1
  · by_cases hone : ReturnB2OneSpacedDatum ctx
    · exact (returnGatesZeroCard_of_b2OneSpacedDatum ctx hone).1
    · by_cases hnum : 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
          < 2 * (129 * shellLadderDepth ctx + 64)
      · exact returnGatesBody_of_reach_numeric ctx hnum
      · exact (returnGatesBody_iff_ungated ctx).mpr
          (R.returnGates ctx hfree hone (not_lt.mp hnum))

/-- The class-4 population bound `|olcFibre| ≤ r + 1` from the gates — the `hnumeric`
supplier of the charge. -/
theorem fibreSmall (R : Erdos260ReturnChargeResidual) : Class4FibreSmall :=
  class4FibreSmall_of_gates R.returnGatesCycle

/-- The per-ctx dirty-slice envelope: guard-failing contexts closed by the chain's own
closures (band-2-free data, spaced `b2 = 1` regimes, the large-carry regime, index-window
separation), each through `sliceDirtyEnvelope_of_returnZeroBody`; demanded contexts from the
surface field. -/
def dirtyEnvelopeAt (R : Erdos260ReturnChargeResidual) (ctx : ActualFailureContext) : SliceDirtyEnvelope ctx := by
  by_cases hfree : ReturnB2FreeDatum ctx
  · exact sliceDirtyEnvelope_of_returnZeroBody ctx
      (returnCtxAllFour_of_b2FreeDatum ctx hfree).2.1
  · by_cases hone : ReturnB2OneSpacedDatum ctx
    · exact sliceDirtyEnvelope_of_returnZeroBody ctx
        (returnGatesZeroCard_of_b2OneSpacedDatum ctx hone).2.1
    · by_cases hex : ∃ k ∈ olcFibre ctx,
          2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card
      · by_cases hcl : ReturnIndexWindowClean ctx
        · exact sliceDirtyEnvelope_of_returnZeroBody ctx
            (returnZeroBody_of_indexWindowClean ctx hcl)
        · exact R.returnDirtyEnvelope ctx hfree hone hex hcl
      · refine sliceDirtyEnvelope_of_returnZeroBody ctx
          (returnZero_of_carryVal2_large ctx fun k hk => ?_)
        by_contra hlt
        exact hex ⟨k, hk, not_le.mp hlt⟩

/-- The per-ctx K.1 interior: the band-2-free regime closed by the chain's own closure, the
rest from the surface field. -/
def interiorAt (R : Erdos260ReturnChargeResidual) (ctx : ActualFailureContext) : ReturnInteriorBody ctx := by
  by_cases hfree : ReturnB2FreeDatum ctx
  · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).2.2.2
  · exact R.returnInterior ctx hfree

/-- **The per-ctx charge-level residual** — the rebase module's
`ReturnCaseSplitChargeResidual` assembled from the surface: the envelope, the interior, and
the count→numeric bridge.  NO digit field, NO clean-step field. -/
def chargeData (R : Erdos260ReturnChargeResidual) (ctx : ActualFailureContext) : ReturnCaseSplitChargeResidual ctx where
  dirtyEnvelope := R.dirtyEnvelopeAt ctx
  class4Interior := R.interiorAt ctx
  hnumeric := return_hnumeric_of_fibre_card_le ctx (returnSelfRefKey ctx) (R.fibreSmall ctx)

/-- **THE SPLICE**: the V3 Return slot — the per-slice charge family, built by the rebase
module's `ReturnCaseSplitChargeResidual.toCharge` (i.e. `Class4ReturnPerSliceCharge.ofDirtyEnvelope`,
the counting constructor `OlcSliceData.ofCardLe` inside) in place of the digit route's
`returnZResidualsOfDigitAndCount`. -/
def returnCharge (R : Erdos260ReturnChargeResidual) : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx :=
  fun ctx => (R.chargeData ctx).toCharge

/-- The Return capacity floor — the SAME class-4 ledger contribution the digit route
delivers, now from the envelope. -/
theorem returnFloor (R : Erdos260ReturnChargeResidual) (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (R.chargeData ctx).returnFloor

/-- The corrected M.2.1 per-slice count, from the envelope. -/
theorem perSliceCount (R : Erdos260ReturnChargeResidual) (ctx : ActualFailureContext) :
    (olcFibre ctx).card
      ≤ ((olcFibre ctx).image (returnSelfRefKey ctx)).card * liftLevelBound ctx.shell.X :=
  (R.chargeData ctx).perSliceCount

/-! ## Part 5.  The budget and the ctx-pinned P9 ledger (the six-atom assembly, charge slot
swapped) -/

/-- The V3 tower count of the budget (the same bridges as `sharpAtomBudget`). -/
def towerCountV3 (R : Erdos260ReturnChargeResidual) : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  p9V3TowerCount_ofShallowDeep
    (towerDeepResidual_ofCountBound (towerCountBound_of_modulusEnumeration R.towerEnum))

/-- The Run max-core family of the budget (the single-numeric split-boundary entry). -/
def runCore (R : Erdos260ReturnChargeResidual) : ∀ ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx :=
  fun ctx => (runSplitOfNumeric (runCycleNumericField_settled R.runNumeric) ctx).toCore

/-- The V3 run chain of the budget. -/
def runChain (R : Erdos260ReturnChargeResidual) : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx :=
  p9V3RunChainOfResidual (runClass5LeafResidual_ofSupportMaxCoreResidual R.runCore)

/-- **The charge budget** — `sixAtomBudget` with the Return slot supplied by the
charge-level family instead of the Z-residual family.  Routes through
`genuineChargeRoute` by `rfl` (it is a `v3Budget`). -/
def budget (R : Erdos260ReturnChargeResidual) : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  v3Budget R.towerCountV3 R.runChain R.returnCharge

/-- Class-0 routed emptiness at the charge budget, from the pinned arithmetic (the
windowed-cycle-check form; the bridge is generic in the budget). -/
theorem class0Empty (R : Erdos260ReturnChargeResidual) : Class0FibreEmpty R.budget :=
  class0FibreEmpty_of_genuineRoute_pinned R.budget (fun _ => rfl)
    (class0Pinned_field_iff_windowCycleCheck.mpr R.class0Cycle)

/-- Class-1 routed emptiness at the charge budget, from the pinned arithmetic (the lemma is
generic in the charge family of the `v3Budget`). -/
theorem class1Empty (R : Erdos260ReturnChargeResidual) : Class1FibreEmpty R.budget :=
  class1FibreEmpty_of_pinned_arithmetic_sharp R.towerCountV3 R.runChain R.returnCharge
    (class1Pinned_of_deepResidual R.class1Deep)

/-- The corrected DensePack residue at the charge budget (the budget-free cycle split walked
through the gated/datum/cycle/regime chain — generic in the budget). -/
def densePackCorrected (R : Erdos260ReturnChargeResidual) : DensePackCorrectedResidue R.budget :=
  (R.densePackUngated.toGatedClosure.toDatumSplit.toCycleSplit.toRegimeSplit R.budget).toCorrected

/-- **The ctx-pinned P9 ledger from the charge surface** — exactly the six-atom capstone's
`toLedger`, with the Return slot of the budget carried by the charge family. -/
def toLedger (R : Erdos260ReturnChargeResidual) : P9CtxPinnedLedgerResidual where
  budget := R.budget
  hChernoff :=
    (ChernoffGenuineAreaKraftSmallResidual.ofClass0FibreEmpty R.budget
      R.class0Empty).hChernoffField
  hCnl := (hCnlField_iff_class1FibreEmpty R.budget).mpr R.class1Empty
  hDensePack := R.densePackCorrected.hDensePackField (fun _ => rfl)
  hTRT := seedHTRT R.budget
  hOldRes := fun ctx => by
    show routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 6
        ≤ ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k
    rw [genuineChargeRoute_routed6_zero ctx]
    exact oldResL65_branchMass_nonneg ctx

/-- The final statement from the charge surface, through the ctx-pinned P9 ledger.
Composition only; nothing re-proved. -/
theorem toStatement (R : Erdos260ReturnChargeResidual) : Erdos260Statement :=
  R.toLedger.toStatement

end Erdos260ReturnChargeResidual

/-- **THE CHARGE-CAPSTONE ENDPOINT**: `Erdos260Statement` from the charge-based surface —
the Return digit lane consumed ONLY as the strictly weaker dirty-slice envelope at the
charge-level junction, both parities folded, no clean-step field anywhere. -/
theorem erdos260_of_returnChargeResidual (R : Erdos260ReturnChargeResidual) :
    Erdos260Statement :=
  R.toStatement

/-! ## Part 6.  Weakening witnesses (the strictness direction that DOES hold) -/

/-- **The weakening witness**: any wave-12 key provider yields the charge surface — the
envelope from the two returnZero-shaped fields (Part 1), the maxClean fields DROPPED, the
other 12 fields verbatim.  No converse is claimed (the envelope admits dirty slices the key
field forbids, and nothing in the new surface carries the dropped clean-step content). -/
def returnChargeResidual_of_keyResidual (R : Erdos260KeyResidual) :
    Erdos260ReturnChargeResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnDirtyEnvelope :=
    returnDirtyEnvelopeField_of_keyFields R.returnKeyInjective R.returnZeroQEvenFloor
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- The weakening witness from the case-split successor surface (whose dirty-singleton fields
are still EQUIVALENT to the key fields — this surface is the first strictly weaker one). -/
def returnChargeResidual_of_caseSplitResidual (R : Erdos260CaseSplitResidual) :
    Erdos260ReturnChargeResidual :=
  returnChargeResidual_of_keyResidual R.toKey

/-- Nonempty transport from the key surface (one direction only — honest). -/
theorem nonempty_returnChargeResidual_of_key
    (h : Nonempty Erdos260KeyResidual) : Nonempty Erdos260ReturnChargeResidual :=
  h.elim fun R => ⟨returnChargeResidual_of_keyResidual R⟩

/-- Nonempty transport from the case-split surface (one direction only — honest). -/
theorem nonempty_returnChargeResidual_of_caseSplit
    (h : Nonempty Erdos260CaseSplitResidual) : Nonempty Erdos260ReturnChargeResidual :=
  h.elim fun R => ⟨returnChargeResidual_of_caseSplitResidual R⟩

/-! ## Part 7.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the charge capstone. -/
def erdos260ChargeCapstoneStatus : List String :=
  [ "SURFACE: Erdos260ReturnChargeResidual = the wave-12 key surface with ALL FOUR Return " ++
      "digit-shaped fields (returnKeyInjective, returnZeroQEvenFloor, " ++
      "returnMaxCleanQOddParityReduced, returnMaxCleanQEven) REPLACED by the SINGLE " ++
      "parity-free field returnDirtyEnvelope : ReturnDirtyEnvelopeField - SliceDirtyEnvelope " ++
      "under the verbatim wave-8 guards, NO parity hypothesis, NO Q-even dyadic-floor guard " ++
      "(free by width_gt_of_returnZero_guard).  The interior and numeric content of the " ++
      "charge comes from the KEPT verbatim fields returnInterior and returnGates.  13 fields " ++
      "(16 - 4 + 1).  NAMING: the brief's Erdos260ChargeResidual is taken by " ++
      "Erdos260ChargeReduced's unrelated surface; this module uses " ++
      "Erdos260ReturnChargeResidual / erdos260_of_returnChargeResidual.",
    "JUNCTION MAP (goal 1): key returnZero fields -> wave-12..8 bridges (toSplit, " ++
      "toThirdsExclusion, toValuation, toFloorPushV2, toTrajectoryResidual, toPushResidual, " ++
      "toScaleFloorPush, toFloorHarvest/toRigidity, toDigitSide, toEnum) -> cycle returnZero/" ++
      "returnMaxClean/returnInterior/returnGates -> THE JUNCTION Erdos260CycleResidual." ++
      "toSharp: returnSmall := class4FibreSmall_of_gates, returnDigit := " ++
      "ReturnClass4DigitResidual.ofSelfRefMaxCleanStep -> sharp toSixAtom: returnZ := " ++
      "returnZResidualsOfDigitAndCount returnSmall returnDigit -> sixAtomBudget consumes " ++
      "returnZ ONLY via returnChargeOfZResiduals (toCharge) - the Return slot of v3Budget.  " ++
      "BEYOND THE CHARGE the Z-family supplies NOTHING the downstream consumes: hgapDiv is a " ++
      "theorem at the self-referential key, hnumeric is the count bridge " ++
      "(return_hnumeric_of_fibre_card_le from Class4FibreSmall), class4Interior transports, " ++
      "and returnFloor/perSliceCount are consequences of the charge.  " ++
      "ReturnCaseSplitChargeResidual.{toCharge, returnFloor, perSliceCount} therefore " ++
      "replaces the whole Z-residual role at the junction.",
    "MAXCLEAN VERDICT (goal 2, honest): the charge route needs NO returnMaxClean - ofSelfRefZ " ++
      "drops hzero AND hcleanStep, and Class4ReturnPerSliceCharge.ofDirtyEnvelope builds the " ++
      "per-slice OlcSliceData from counts alone (OlcSliceData.ofCardLe, the order-rank tower " ++
      "assignment).  The old route consumed maxClean only through returnCleanRunOfZeroData " ++
      "(the anchored clean-run family behind OlcSliceData); that construction is REPLACED by " ++
      "the counting constructor.  The only other in-tree consumers of the maxClean shapes " ++
      "are predecessor-surface equivalence records off this route.  Both returnMaxClean " ++
      "fields DISAPPEAR from the surface.",
    "ENDPOINT (goal 3): erdos260_of_returnChargeResidual via the ctx-pinned P9 ledger - " ++
      "non-Return lanes walked by the chain's own public per-lane discharges " ++
      "(towerModulusEnumEscape_iff_v2 + thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven " ++
      "+ towerTail_of_order_gt -> towerCountBound_of_modulusEnumeration; " ++
      "runTail_of_order_gt -> runCycleNumericField_settled -> runSplitOfNumeric; " ++
      "class0Tail_of_order_gt -> class0Cycle_of_survivor_residue_split -> " ++
      "class0Pinned_field_iff_windowCycleCheck; class1Tail_of_band4FreePeriod -> " ++
      "class1PairResidual_of_deepOnly -> class1DeepResidual_of_pairResidual -> " ++
      "class1Pinned_of_deepResidual; densePack toGatedClosure -> toDatumSplit -> " ++
      "toCycleSplit -> toRegimeSplit -> toCorrected); Return lane spliced as returnCharge " ++
      "ctx := (chargeData ctx).toCharge with the guard-failing contexts discharged by the " ++
      "chain's own closures (returnCtxAllFour_of_b2FreeDatum, " ++
      "returnGatesZeroCard_of_b2OneSpacedDatum, returnZero_of_carryVal2_large, " ++
      "returnZeroBody_of_indexWindowClean) mapped through " ++
      "sliceDirtyEnvelope_of_returnZeroBody; ledger assembled exactly as " ++
      "Erdos260SixAtomResidual.toLedger (ofClass0FibreEmpty.hChernoffField, " ++
      "hCnlField_iff_class1FibreEmpty, hDensePackField, seedHTRT, " ++
      "genuineChargeRoute_routed6_zero + oldResL65_branchMass_nonneg).  The wave-8..12 " ++
      "digit-transport surfaces are NOT on this route.",
    "STRICTNESS VERDICT (honest): returnChargeResidual_of_keyResidual rebuilds the surface " ++
      "from any key provider (Q odd: sliceDirtyEnvelope_of_keyInjOn; Q even: the parity-free " ++
      "collapse returnZeroBody_iff_keyInjOn_uncond via " ++
      "returnZeroBody_iff_belowBandTrajectory_uncond, the dropped dyadic-floor guard free by " ++
      "width_gt_of_returnZero_guard; maxClean dropped).  NO CONVERSE IS PROVIDED, and none " ++
      "should be derivable: the envelope allows dirty slices with up to liftLevelBound X " ++
      "members which ReturnKeyInjOn forbids outright, and no field of the new surface " ++
      "carries the dropped clean-step digit content (the DirtyWindowCountCore finding shows " ++
      "the in-tree dirty model cannot deliver absolute-constant fibre counts).  This is the " ++
      "FIRST capstone surface since wave 8 that is strictly weaker demanded content rather " ++
      "than an equivalent re-presentation.  NOT claimed: a formal independence/" ++
      "non-implication proof (that would need a model construction).",
    "WHAT REMAINS OPEN (sharpest Return form after this pass): ReturnDirtyEnvelopeField - " ++
      "the (M.1) envelope |slice| <= liftLevelBound X demanded ONLY on slices of the " ++
      "self-referential key that carry a dirty crossing datum, at any parity, under the " ++
      "wave-8 guards.  Plus the unchanged non-Return lanes (tower enum tails, run numerics, " ++
      "class-0 cycle checks, class-1 deep emptiness, densePack ungated fields) and the " ++
      "returnGates/returnInterior count-and-boundary fields.",
    "HYGIENE: additive only - no existing module edited (the root import file gains one " ++
      "line); no sorry / admit / new axiom / native_decide; all #print axioms in " ++
      "[propext, Classical.choice, Quot.sound] or fewer." ]

theorem erdos260ChargeCapstoneStatus_nonempty : erdos260ChargeCapstoneStatus ≠ [] := by
  simp [erdos260ChargeCapstoneStatus]

/-! ## Part 8.  Axiom-cleanliness audit -/

#print axioms ReturnDirtyEnvelopeField
#print axioms returnDirtyEnvelopeField_of_keyFields
#print axioms dirtyEnvelopeQOddField_of_envelopeField
#print axioms Erdos260ReturnChargeResidual.towerEnum
#print axioms Erdos260ReturnChargeResidual.runNumeric
#print axioms Erdos260ReturnChargeResidual.class0Cycle
#print axioms Erdos260ReturnChargeResidual.class1Deep
#print axioms Erdos260ReturnChargeResidual.returnGatesCycle
#print axioms Erdos260ReturnChargeResidual.fibreSmall
#print axioms Erdos260ReturnChargeResidual.dirtyEnvelopeAt
#print axioms Erdos260ReturnChargeResidual.interiorAt
#print axioms Erdos260ReturnChargeResidual.chargeData
#print axioms Erdos260ReturnChargeResidual.returnCharge
#print axioms Erdos260ReturnChargeResidual.returnFloor
#print axioms Erdos260ReturnChargeResidual.perSliceCount
#print axioms Erdos260ReturnChargeResidual.towerCountV3
#print axioms Erdos260ReturnChargeResidual.runCore
#print axioms Erdos260ReturnChargeResidual.runChain
#print axioms Erdos260ReturnChargeResidual.budget
#print axioms Erdos260ReturnChargeResidual.class0Empty
#print axioms Erdos260ReturnChargeResidual.class1Empty
#print axioms Erdos260ReturnChargeResidual.densePackCorrected
#print axioms Erdos260ReturnChargeResidual.toLedger
#print axioms Erdos260ReturnChargeResidual.toStatement
#print axioms erdos260_of_returnChargeResidual
#print axioms returnChargeResidual_of_keyResidual
#print axioms returnChargeResidual_of_caseSplitResidual
#print axioms nonempty_returnChargeResidual_of_key
#print axioms nonempty_returnChargeResidual_of_caseSplit
#print axioms erdos260ChargeCapstoneStatus_nonempty

end

end Erdos260
