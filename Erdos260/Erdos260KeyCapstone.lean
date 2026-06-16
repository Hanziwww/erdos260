import Erdos260.ValuationSliceCap
import Erdos260.ParityResidueClosure
import Erdos260.MultiScaleRigidity

/-!
# The wave-12 key capstone - key injectivity, parity pins, multi-scale verdict

This module (NEW; it edits no existing file) assembles the three wave-12 deliverables
into one surface and one endpoint.

## The three inputs (all green, all additive)

* `ValuationSliceCap.lean` - THE HEADLINE: at Q odd, `ReturnZeroBody` collapses
  ENTIRELY to key injectivity (`returnZeroBody_iff_keyInjOn_of_Q_odd`) - the reset-law
  descent closes EVERY valuation level (`sameKey_zeroRun_refuted_of_Q_odd`), so ZERO
  digit content remains in the Q-odd `returnZero` lane.  The successor field
  `ReturnKeyInjectiveField` is INTERCHANGEABLE with the wave-11 split field
  (`returnZeroQOddSplitField_of_keyInjective` /
  `returnKeyInjectiveField_of_qOddSplitField`).  ADOPTED here as the canonical Q-odd
  `returnZero` shape, with the sharpened sub-counts recorded: at most 1 member at
  `v = 0`, at most 1 at `v = 1` (all val-1 members share the key `Nat.pair 1 0`),
  at most `2^v` at level `v`, and only levels `v <= vCap ctx =
  log2 log2 (Q*(2X+2))` carry content (vacuous above).
* `ParityResidueClosure.lean` - the PARITY PINS: ten parity-pinned pairs (six
  member-EVEN data where the val-0 clause is FREE and `returnMaxClean` is the pure
  carry-parity branch; four member-ODD data - including the `63@10` class-4 lane -
  where `returnMaxClean` is pure doubling), the `W <= 2c` singleton regime on
  odd-period unique-band-2 data, and the `63@10` dual-parity record (class-1 fibre
  EVEN, class-4 fibre ODD on the same cycle).  FOLDED here: the `returnMaxClean`
  parity reduction stands alone and becomes the surface field
  (`ReturnMaxCleanQOddParityReducedField`); the `returnZero` parity content - aimed
  at the superseded split shape - becomes PER-DATUM COUNT SUPPORT for the
  key-injectivity demand (on the six member-EVEN data the val-0 key class is empty,
  so injectivity reduces to val-positive singletons).
* `MultiScaleRigidity.lean` - the QUANTIFIER VERDICT: the bridge layer proves
  all-large-scales sparsity for the genuine counterexample word
  (`counterexample_shellsAtAllLargeScales`) but with UNCONTROLLED onset, while the
  rigidity firing window `[2^5, 2^493443]` is FIXED - the quantifiers do not
  cooperate and no unconditional voiding follows.  The named gap
  `SiblingShellInFiringWindow` / `MultiScaleSiblingSupply` voids ALL pinned-value
  families (endpoint `erdos260_of_multiScaleSiblingSupply`, re-exported PROMINENTLY
  below); the unconditional facts are the firing-window cleanliness
  (`firingWindow_clean_of_rep`: pinned words have failure-free windows) and the
  onset cap (`onset_above_cap_of_rep`: a pinned word with a sparsity tail has onset
  forced above 493443).  The manuscript's H.4/H.5 do NOT supply the gap; the named
  future target is a sparsity-onset bound `<= 493443` from the
  hlarge/startThreshold data.

## The new surface and endpoint

`Erdos260KeyResidual` := the wave-11 split surface with the Q-odd `returnZero` field
REPLACED by the counting field `ReturnKeyInjectiveField` (zero digit content) and the
Q-odd `returnMaxClean` field REPLACED by the parity-reduced per-datum form
`ReturnMaxCleanQOddParityReducedField` (only the live branch demanded per datum
class); 16 fields, 14 verbatim wave-11 shapes.  Endpoint `erdos260_of_keyResidual :
Erdos260KeyResidual -> Erdos260Statement` through PUBLIC bridges only.  Weakening
witnesses and Nonempty-equivalences in both directions (both replaced fields are
EQUIVALENT to their wave-11 forms - an honest presentation refinement).  The
conditional routes are re-exported PARALLEL: multi-scale sibling supply, cofinal
upper band (+ seed form + the no-shortcut equivalence), canonical per-scale,
per-depth, deep lever v2.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The wave-12 key surface -/

/-- **The wave-12 key surface**: the wave-11 split surface
(`Erdos260SplitResidual`) with the Q-odd `returnZero` field replaced by the PURE
COUNTING field `ReturnKeyInjectiveField` (`ValuationSliceCap`; zero digit content)
and the Q-odd `returnMaxClean` field replaced by the parity-reduced per-datum form
`ReturnMaxCleanQOddParityReducedField` (`ParityResidueClosure`; only the live branch
demanded per datum class).  The other 14 fields are verbatim wave-11 shapes. -/
structure Erdos260KeyResidual where
  /-- Tower / class 2 - enumerated part (`q < 107`), with the free aperiodicity guard
  (covers every `q = 9` context: `oddpart(Q) ≤ 3`). -/
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
  /-- Return / class 4 count gates - verbatim field. -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 digit Z, Q ODD - **the canonical counting shape**: key
  injectivity on the class-4 fibre (`ValuationSliceCap.ReturnKeyInjectiveField`);
  zero digit content (`returnZeroBody_iff_keyInjOn_of_Q_odd`). -/
  returnKeyInjective : ReturnKeyInjectiveField
  /-- Return / class 4 digit Z, Q EVEN - the verbatim dyadic-floor trajectory field
  restricted to even denominators (`QOddResetClosure.ReturnZeroQEvenFloorField`). -/
  returnZeroQEvenFloor : ReturnZeroQEvenFloorField
  /-- Return / class 4 clean step, Q ODD - **the parity-reduced per-datum form**
  (`ParityResidueClosure.ReturnMaxCleanQOddParityReducedField`): carry parity on the
  six member-EVEN data, pure doubling on the four member-ODD data (incl. `63@10`),
  the full split off the ten pinned pairs. -/
  returnMaxCleanQOddParityReduced : ReturnMaxCleanQOddParityReducedField
  /-- Return / class 4 clean step, Q EVEN - the verbatim trajectory field restricted
  to even denominators (`QOddResetClosure.ReturnMaxCleanQEvenField`). -/
  returnMaxCleanQEven : ReturnMaxCleanQEvenField
  /-- Return / class 4 K.1 interior - verbatim field. -/
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
  /-- CNL / class 1 - enumerated deep part (`q < 101`), with the free aperiodicity
  guard (covers the `63@10` pair: `oddpart(Q) = 3`). -/
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

/-! ## Part 2.  The endpoint - composition through public bridges only -/

namespace Erdos260KeyResidual

/-- **The bridge into the wave-11 split surface**: the counting field rebuilds the
Q-odd split field through the PUBLIC `ValuationSliceCap` bridge
(`returnZeroQOddSplitField_of_keyInjective`); the parity-reduced field rebuilds the
Q-odd `returnMaxClean` split field through the PUBLIC `ParityResidueClosure` bridge
(`returnMaxCleanQOddSplitField_of_parityReduced` - the dead branch is restored free
per datum class).  The other 14 fields transfer verbatim. -/
def toSplit (R : Erdos260KeyResidual) : Erdos260SplitResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnZeroQOddSplit := returnZeroQOddSplitField_of_keyInjective R.returnKeyInjective
  returnZeroQEvenFloor := R.returnZeroQEvenFloor
  returnMaxCleanQOddSplit :=
    returnMaxCleanQOddSplitField_of_parityReduced R.returnMaxCleanQOddParityReduced
  returnMaxCleanQEven := R.returnMaxCleanQEven
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- The wave-11 thirds-exclusion surface, through the split bridge. -/
def toThirdsExclusion (R : Erdos260KeyResidual) : Erdos260ThirdsExclusionResidual :=
  R.toSplit.toThirdsExclusion

/-- The wave-10 valuation surface, through the split bridge. -/
def toValuation (R : Erdos260KeyResidual) : Erdos260ValuationResidual :=
  R.toSplit.toValuation

/-- The final statement: counting + parity-reduced fields -> split surface -> thirds
surface -> valuation surface -> the public wave-10 chain.  Composition only; nothing
re-proved. -/
theorem toStatement (R : Erdos260KeyResidual) : Erdos260Statement :=
  erdos260_of_splitResidual R.toSplit

end Erdos260KeyResidual

/-- **THE WAVE-12 ENDPOINT**: `Erdos260Statement` from the key surface. -/
theorem erdos260_of_keyResidual (R : Erdos260KeyResidual) : Erdos260Statement :=
  R.toStatement

/-! ## Part 3.  Weakening witnesses and the equivalence chain -/

/-- **Weakening witness**: any wave-11 split provider yields the key surface.  The
counting field comes through the exact interchange
`returnKeyInjectiveField_of_qOddSplitField`; the parity-reduced field is the
recorded weakening `parityReducedFields_of_split`. -/
def keyResidual_of_split (R : Erdos260SplitResidual) : Erdos260KeyResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnKeyInjective := returnKeyInjectiveField_of_qOddSplitField R.returnZeroQOddSplit
  returnZeroQEvenFloor := R.returnZeroQEvenFloor
  returnMaxCleanQOddParityReduced := (parityReducedFields_of_split R).2
  returnMaxCleanQEven := R.returnMaxCleanQEven
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- Weakening witness from the wave-11 thirds-exclusion surface. -/
def keyResidual_of_thirdsExclusion (R : Erdos260ThirdsExclusionResidual) :
    Erdos260KeyResidual :=
  keyResidual_of_split (splitResidual_of_thirdsExclusion R)

/-- Weakening witness from the wave-10 valuation surface. -/
def keyResidual_of_valuation (R : Erdos260ValuationResidual) :
    Erdos260KeyResidual :=
  keyResidual_of_split (splitResidual_of_valuation R)

/-- The key surface is EQUIVALENT to the wave-11 split surface: both replaced fields
are interchangeable with their wave-11 forms (`returnZeroQOddSplitField_of_
keyInjective` / `returnKeyInjectiveField_of_qOddSplitField` and
`returnMaxCleanQOddSplitField_of_parityReduced` / `parityReducedFields_of_split`) -
a presentation refinement, honestly recorded: the Q-odd `returnZero` obligation is
now a PURE COUNTING statement and the Q-odd `returnMaxClean` obligation demands only
the live branch per datum class, but the logical content is equal. -/
theorem nonempty_keyResidual_iff_split :
    Nonempty Erdos260KeyResidual ↔ Nonempty Erdos260SplitResidual :=
  ⟨fun ⟨R⟩ => ⟨R.toSplit⟩, fun ⟨R⟩ => ⟨keyResidual_of_split R⟩⟩

/-- The key surface is equivalent to the wave-11 thirds-exclusion surface. -/
theorem nonempty_keyResidual_iff_thirdsExclusion :
    Nonempty Erdos260KeyResidual ↔ Nonempty Erdos260ThirdsExclusionResidual :=
  nonempty_keyResidual_iff_split.trans nonempty_splitResidual_iff_thirdsExclusion

/-- The key surface is equivalent to the wave-10 valuation surface. -/
theorem nonempty_keyResidual_iff_valuation :
    Nonempty Erdos260KeyResidual ↔ Nonempty Erdos260ValuationResidual :=
  nonempty_keyResidual_iff_split.trans nonempty_splitResidual_iff_valuation

/-! ## Part 4.  The adopted canonical shape and the sharpened sub-counts

The Q-odd `returnZero` lane is CLOSED as a digit problem: `ReturnZeroBody` at Q odd
IS injectivity of the self-referential key on the class-4 fibre.  What the demand
costs, level by level, is recorded here through the public count lemmas. -/

/-- Re-export of the master equivalence: at Q odd, `ReturnZeroBody` IS key
injectivity on the fibre - ZERO digit content. -/
theorem keyCapstone_returnZero_iff_keyInjOn (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) :
    ReturnZeroBody ctx ↔ ReturnKeyInjOn ctx :=
  returnZeroBody_iff_keyInjOn_of_Q_odd ctx hQodd

/-- Sub-count at `v = 0` (wave-11 form): under the injectivity demand there is at
most one val-0 fibre member (no parity input needed - the val-0 members share the
key `Nat.pair 0 0`). -/
theorem keyCapstone_val0_atMostOne_of_keyInjOn (ctx : ActualFailureContext)
    (hinj : ReturnKeyInjOn ctx) : QOddVal0AtMostOne ctx :=
  (qOddReturnZeroSplit_of_keyInjOn ctx hinj).1

/-- Sub-count at `v = 1`: under the injectivity demand there is at most ONE val-1
member in the whole fibre (all val-1 members are even and share the single key
`Nat.pair 1 0`). -/
theorem keyCapstone_val1_card_le_one (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (hinj : ReturnKeyInjOn ctx) :
    ((olcFibre ctx).filter (fun k => carryVal2 ctx k = 1)).card ≤ 1 :=
  qOddValPosZeroRun_val1_card_le_one ctx hQodd
    (qOddReturnZeroSplit_of_keyInjOn ctx hinj).2

/-- Sub-count at level `v ≥ 1`: under the injectivity demand there are at most
`2^v` members at valuation level `v` (residue classes mod `2^v`). -/
theorem keyCapstone_level_card_le_pow (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (hinj : ReturnKeyInjOn ctx) {v : ℕ} (hv : 1 ≤ v) :
    ((olcFibre ctx).filter (fun k => carryVal2 ctx k = v)).card ≤ 2 ^ v :=
  qOddValPosZeroRun_level_card_le_pow ctx hQodd
    (qOddReturnZeroSplit_of_keyInjOn ctx hinj).2 hv

/-- Above the cap `vCap ctx = log2 log2 (Q*(2X+2))` the demanded slices are
singletons - levels `v > vCap` are vacuous; only `1 ≤ v ≤ vCap` carry content. -/
theorem keyCapstone_singletons_above_vCap (ctx : ActualFailureContext)
    (hinj : ReturnKeyInjOn ctx) :
    ValPosSingletonsAbove ctx (vCap ctx) :=
  qOddValPosZeroRun_singletons_above_vCap ctx
    (qOddReturnZeroSplit_of_keyInjOn ctx hinj).2

/-! ## Part 5.  The parity fold - per-datum count support and the reduced surface

HONEST COMPOSABILITY: the `ParityResidueClosure` reductions target the wave-11
split fields.  The `returnMaxClean` reduction stands alone and IS the surface field
(Part 1).  The `returnZero` reduction (val-0 clause free on the six member-EVEN
data) is superseded as a FIELD by the key-injectivity shape, but its content
survives as per-datum count support: on the six pairs the val-0 key class is empty,
so the injectivity demand reduces to val-positive singletons. -/

/-- **Field-level fold**: the parity-reduced `returnZero` digit form supplies the
canonical counting field (through the wave-11 split rebuild). -/
theorem returnKeyInjectiveField_of_parityReducedZero
    (h : ReturnZeroQOddParityReducedField) : ReturnKeyInjectiveField :=
  returnKeyInjectiveField_of_qOddSplitField
    (returnZeroQOddSplitField_of_parityReduced h)

/-- **The parity-reduced combinator**: a key surface may be assembled from the
parity-reduced forms of BOTH Q-odd lanes (the weakest per-datum digit shapes on
record). -/
def keyResidual_withParityReduced (base : Erdos260KeyResidual)
    (hz : ReturnZeroQOddParityReducedField)
    (hm : ReturnMaxCleanQOddParityReducedField) : Erdos260KeyResidual :=
  { base with
    returnKeyInjective := returnKeyInjectiveField_of_parityReducedZero hz
    returnMaxCleanQOddParityReduced := hm }

/-- **Endpoint through the parity-reduced forms** (the `ParityResidueClosure`
endpoint shape, landed on the key surface). -/
theorem erdos260_key_of_parityReduced (base : Erdos260KeyResidual)
    (hz : ReturnZeroQOddParityReducedField)
    (hm : ReturnMaxCleanQOddParityReducedField) : Erdos260Statement :=
  erdos260_of_keyResidual (keyResidual_withParityReduced base hz hm)

/-- **Per-datum count support (member-EVEN data)**: on the six parity-even pairs the
key-injectivity demand IS the val-positive zero-run clause - the val-0 key class is
empty (a val-0 member would be an odd raw hit; members are even). -/
theorem keyCapstone_keyInjOn_iff_valPosRun_of_parityEvenDatum
    (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (hpe : ReturnB2ParityEvenDatum ctx) :
    ReturnKeyInjOn ctx ↔ QOddValPosZeroRun ctx :=
  (returnZeroBody_iff_keyInjOn_of_Q_odd ctx hQodd).symm.trans
    (returnZeroBody_iff_valPosZeroRun_of_memberEven ctx hQodd
      (olcFibre_even_of_parityEvenDatum ctx hpe))

/-- The fully-counting form of the member-EVEN support: on the six pairs the
injectivity demand IS "val-positive slices are singletons". -/
theorem keyCapstone_keyInjOn_iff_valPosSingletons_of_parityEvenDatum
    (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (hpe : ReturnB2ParityEvenDatum ctx) :
    ReturnKeyInjOn ctx ↔ ValPosSingletonsAbove ctx 0 :=
  (keyCapstone_keyInjOn_iff_valPosRun_of_parityEvenDatum ctx hQodd hpe).trans
    (qOddValPosZeroRun_iff_valPosSingletons ctx hQodd)

/-- Re-export of the generic `W ≤ 2` micro-lever: the val-0 component of the
injectivity demand is free on width-`≤ 2` shells at every Q-odd context. -/
theorem keyCapstone_val0_of_width_le_two (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1)
    (hW : (supportShell ctx.shell.d ctx.shell.X).card ≤ 2) :
    QOddVal0AtMostOne ctx :=
  qOddVal0AtMostOne_of_width_le_two ctx hQodd hW

/-- Re-export of the `63@10` dual-parity record: the class-1 fibre is pinned EVEN
while the class-4 fibre is pinned ODD on the SAME period-2 cycle - the two lanes
read opposite bands.  (The class-4 consequence is folded in the surface field: at
`63@10` `returnMaxClean` is pure doubling.) -/
theorem keyCapstone_datum_63_10_dual_parity (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    (∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1, k % 2 = 0)
      ∧ (∀ k ∈ olcFibre ctx, k % 2 = 1) :=
  datum_63_10_dual_parity ctx hq hK

/-! ## Part 6.  The multi-scale verdict - the named gap, re-exported prominently

The bridge layer proves all-large-scales sparsity for the genuine counterexample
word, but the onset is UNCONTROLLED while the rigidity firing window
`[2^5, 2^493443]` is FIXED: the quantifiers do not cooperate, and no unconditional
voiding follows (`MultiScaleRigidity`, the honest verdict).  The single named gap
under which ALL pinned-value families void is `SiblingShellInFiringWindow` /
`MultiScaleSiblingSupply`; H.4/H.5 of the manuscript do NOT supply it.  The named
future target: a sparsity-onset bound `≤ 493443` from the hlarge/startThreshold
data. -/

/-- **Re-export: THE MULTI-SCALE CONDITIONAL ENDPOINT** - `Erdos260Statement` from
the sibling supply (demanded only at deep contexts, `X > 2^493443`) plus the
lever-shrunk wave-5 surfaces. -/
theorem erdos260_key_multiScale_route (R : Erdos260MultiScaleResidual) :
    Erdos260Statement :=
  erdos260_of_multiScaleSiblingSupply R

/-- The unbundled form of the multi-scale route: supply + surfaces directly. -/
theorem erdos260_key_siblingSupply_route (h : MultiScaleSiblingSupply)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_of_multiScaleSiblingSupply ⟨h, surfaces⟩

/-- Re-export of the unconditional firing-window cleanliness: ANY pinned word
(`value = P/(u*2^t)`, `u ≤ 7`) keeps the ENTIRE firing window `[2^5, 2^493443]`
failure-free. -/
theorem keyCapstone_firingWindow_clean {u t : ℕ} {P : ℤ} {d : ℕ → ℕ}
    (hu7 : u ≤ 7) (hupos : 0 < u)
    (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ)) :
    ¬ ShellInFiringWindow d t :=
  firingWindow_clean_of_rep hu7 hupos hd hnonterm heta

/-- Re-export of the onset cap: a pinned word carrying an all-large-scales sparsity
tail has its onset FORCED above 493443 - the pin and the failure structure can only
coexist in the deep tail. -/
theorem keyCapstone_onset_above_cap {u t : ℕ} {P : ℤ} {d : ℕ → ℕ}
    (hu7 : u ≤ 7) (hupos : 0 < u)
    (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ))
    {L0 : ℕ} (h : ∀ L : ℕ, L0 ≤ L → ShellSparseAt d L)
    (ht : t ≤ 2 ^ max L0 5) : 493443 < L0 :=
  onset_above_cap_of_rep hu7 hupos hd hnonterm heta h ht

/-- Re-export of the shallow subsumption: every context at scale `X = 2^L` with
`L ≤ 493443` supplies its OWN sibling - the gap is open only in the deep tail. -/
theorem keyCapstone_sibling_self (ctx : ActualFailureContext) {L : ℕ}
    (hL : ctx.X = 2 ^ L) (hcap : L ≤ 493443) :
    SiblingShellInFiringWindow ctx :=
  siblingShellInFiringWindow_self ctx hL hcap

/-! ## Part 7.  Re-exported conditional routes (PARALLEL, not merged) -/

/-- **Re-export: the cofinal upper-band route** (wave 11; the REPAIRED satisfiable
per-scale supply). -/
theorem erdos260_key_cofinalUpperBand_route (h : CofinalUpperBandSupply)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_split_cofinalUpperBand_route h surfaces

/-- **Re-export: the seed form** - ONE banded base depth plus the tail expansion of
its complement per genuine start. -/
theorem erdos260_key_seedUpperBand_route (h : SeedUpperBandSupply)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_split_seedUpperBand_route h surfaces

/-- **Re-export: no free lunch at the band layer** - the cofinal upper-band supply
is logically EQUIVALENT to the dyadic-value lever it feeds. -/
theorem erdos260_key_cofinalUpperBand_iff_lever :
    CofinalUpperBandSupply ↔ DyadicValueLever :=
  erdos260_split_cofinalUpperBand_iff_lever

/-- **Re-export: the canonical per-scale route** (wave 10; live supply =
`canonicalPerScaleSupply_of_cofinalUpperBand` - the all-depths `ofResidueBand`
shape is unsatisfiable). -/
theorem erdos260_key_canonicalPerScale_route (h : CanonicalPerScaleSupply)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_split_canonicalPerScale_route h surfaces

/-- **Re-export: the conditional per-depth route** (wave 9). -/
theorem erdos260_key_perDepth_route (h : DeepDyadicPerDepthMatch)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_split_perDepth_route h surfaces

/-- **Re-export: the pushed deep-lever route v2** (`FloorPushV2`; demand only at
`X > 2^986893`). -/
theorem erdos260_key_deepLeverV2_route (h : DeepDyadicValueLeverPushV2)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_split_deepLeverV2_route h surfaces

/-! ## Part 8.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the wave-12 key capstone. -/
def erdos260KeyCapstoneStatus : List String :=
  [ "SURFACE: Erdos260KeyResidual = the wave-11 split surface with the Q-odd " ++
      "returnZero field REPLACED by the pure counting field ReturnKeyInjectiveField " ++
      "(ValuationSliceCap: key injectivity on the class-4 fibre under the verbatim " ++
      "wave-8 guards; ZERO digit content) and the Q-odd returnMaxClean field " ++
      "REPLACED by the parity-reduced per-datum form ReturnMaxCleanQOddParity" ++
      "ReducedField (ParityResidueClosure: carry parity on the six member-EVEN " ++
      "data, pure doubling on the four member-ODD data incl. 63@10, the full split " ++
      "off the ten pinned pairs).  16 fields total; 14 verbatim wave-11 shapes.",
    "ENDPOINT + COMPOSITION (honest): erdos260_of_keyResidual via toSplit - the " ++
      "counting field rebuilds the wave-11 Q-odd split field through the PUBLIC " ++
      "bridge returnZeroQOddSplitField_of_keyInjective, the parity-reduced field " ++
      "rebuilds the Q-odd maxClean split field through returnMaxCleanQOddSplit" ++
      "Field_of_parityReduced (the dead branch restored free per datum class), " ++
      "then erdos260_of_splitResidual runs the wave-11/10 chain (toThirds" ++
      "Exclusion -> toValuation -> erdos260_of_valuationResidual).  Nothing " ++
      "re-proved.",
    "ADOPTION (the wave-12 headline): key injectivity IS the canonical Q-odd " ++
      "returnZero shape - ReturnZeroBody at Q odd <-> returnSelfRefKey injective " ++
      "on the fibre (keyCapstone_returnZero_iff_keyInjOn = returnZeroBody_iff_" ++
      "keyInjOn_of_Q_odd; the reset-law descent closes EVERY valuation level: " ++
      "along a demanded run the valuation grows stepwise, so position z - v has " ++
      "valuation 0 and the reset law demands d(z-v) = 1 INSIDE the demanded zero " ++
      "interval - sameKey_zeroRun_refuted_of_Q_odd).  The positional val-1 " ++
      "dictionary carryVal2_eq_one_iff_of_Q_odd pins the v = 1 stratum.  " ++
      "SHARPENED SUB-COUNTS under the demand: <= 1 member at v = 0 (keyCapstone_" ++
      "val0_atMostOne_of_keyInjOn), <= 1 at v = 1 (keyCapstone_val1_card_le_one; " ++
      "all val-1 members share key Nat.pair 1 0), <= 2^v at level v (keyCapstone_" ++
      "level_card_le_pow), vacuous above vCap ctx = Nat.log 2 (Nat.log 2 " ++
      "(Q*(2X+2))) (keyCapstone_singletons_above_vCap).",
    "THE PARITY FOLD (honest composability): the ParityResidueClosure reductions " ++
      "target the wave-11 SPLIT fields.  For returnMaxClean the reduction stands " ++
      "alone and IS the surface field (only the live branch per datum class).  " ++
      "For returnZero the key-injective shape supersedes the split field, so the " ++
      "parity content becomes PER-DATUM COUNT SUPPORT: on the six member-EVEN " ++
      "pairs the val-0 key class is empty and the injectivity demand IS val-" ++
      "positive singletons (keyCapstone_keyInjOn_iff_valPosRun_of_parityEvenDatum " ++
      "/ keyCapstone_keyInjOn_iff_valPosSingletons_of_parityEvenDatum); the " ++
      "field-level fold returnKeyInjectiveField_of_parityReducedZero + combinator " ++
      "keyResidual_withParityReduced + endpoint erdos260_key_of_parityReduced " ++
      "land the ParityResidueClosure endpoint shape on the key surface.  Count " ++
      "support re-exports: the W <= 2 micro-lever (keyCapstone_val0_of_width_le_" ++
      "two; the W <= 2c odd-period regime and the (63,31) W <= 10 instance live " ++
      "in ParityResidueClosure as qOddVal0AtMostOne_of_band2_unique_oddc / _of_" ++
      "datum_63_31).  The 63@10 dual-parity record re-exported (keyCapstone_" ++
      "datum_63_10_dual_parity: class-1 fibre EVEN, class-4 fibre ODD, same " ++
      "cycle).",
    "WITNESSES + EQUIVALENCES: keyResidual_of_split / _of_thirdsExclusion / _of_" ++
      "valuation; nonempty_keyResidual_iff_split / _iff_thirdsExclusion / _iff_" ++
      "valuation.  HONEST: both replaced fields are INTERCHANGEABLE with their " ++
      "wave-11 forms (returnKeyInjectiveField_of_qOddSplitField back, parity" ++
      "ReducedFields_of_split back) - the key surface is an equivalent " ++
      "presentation refinement of the wave-8..11 chain; the obligations are " ++
      "sharper in SHAPE (counting, per-datum live branches), equal in content.",
    "THE MULTI-SCALE VERDICT (folded, honest): the bridge layer PROVES all-large-" ++
      "scales sparsity for the genuine counterexample word (counterexample_" ++
      "shellsAtAllLargeScales from theoremA_contradicts_nonirrational_erdos_sum) " ++
      "but the onset is UNCONTROLLED, while the rigidity firing window [2^5, " ++
      "2^493443] is FIXED (c0 = 17/2^24): the quantifiers DO NOT cooperate and " ++
      "no unconditional voiding follows - mathematically genuine, not an " ++
      "artifact (a pinned word can have density ~ 1/(L+4), sublinear).  THE " ++
      "SINGLE NAMED GAP: SiblingShellInFiringWindow / MultiScaleSiblingSupply " ++
      "(one failing shell of the same word in the fixed window, Q-compatibly) " ++
      "voids ALL pinned-value families - endpoint erdos260_of_multiScaleSibling" ++
      "Supply, re-exported PROMINENTLY (erdos260_key_multiScale_route / erdos260_" ++
      "key_siblingSupply_route).  UNCONDITIONAL facts re-exported: pinned words " ++
      "keep the entire firing window clean (keyCapstone_firingWindow_clean = " ++
      "firingWindow_clean_of_rep); onset forced above 493443 (keyCapstone_onset_" ++
      "above_cap = onset_above_cap_of_rep); the shallow regime supplies its own " ++
      "sibling (keyCapstone_sibling_self).  H.4/H.5 do NOT supply the gap (H.4 " ++
      "iterates thresholds inside ONE shell; H.5 derives pressure at the SAME " ++
      "X).  NAMED FUTURE TARGET: a sparsity-onset bound <= 493443 from the " ++
      "hlarge/startThreshold data.",
    "RE-EXPORTED CONDITIONAL ROUTES (all PARALLEL): erdos260_key_multiScale_route " ++
      "(+ unbundled erdos260_key_siblingSupply_route), erdos260_key_cofinal" ++
      "UpperBand_route (+ seed form erdos260_key_seedUpperBand_route, equivalence " ++
      "erdos260_key_cofinalUpperBand_iff_lever), erdos260_key_canonicalPerScale_" ++
      "route, erdos260_key_perDepth_route, erdos260_key_deepLeverV2_route.",
    "WHAT REMAINS OPEN (sharpest forms): (1) the key-injectivity counts - " ++
      "ReturnKeyInjectiveField, i.e. at most one class-4 fibre member per " ++
      "(valuation, residue) key at Q-odd contexts (per-level: <= 1 at v = 0, <= 1 " ++
      "at v = 1, <= 2^v at 2 <= v <= vCap; no in-tree count fact controls the " ++
      "fibre's key multiplicities); (2) the Q-even lanes (returnZeroQEvenFloor / " ++
      "returnMaxCleanQEven, verbatim trajectory forms) and the returnMaxClean " ++
      "live branches (carry parity on member-EVEN data, doubling on member-ODD " ++
      "data, the full split on the 35 parity-free pairs); (3) the descent atom = " ++
      "the lever equivalences (cofinalUpperBandSupply_iff_lever - supplying the " ++
      "band IS the voiding, no cheaper waypoint); (4) the per-pair aperiodic " ++
      "tails (every q <= 21 context is window-aperiodic, so the open content " ++
      "lives there); (5) the multi-scale onset quantification (the named target " ++
      "above).",
    "HYGIENE: additive only - no existing module edited (the root import file " ++
      "gained one line); no sorry / admit / new axiom / native_decide; all " ++
      "#print axioms in [propext, Classical.choice, Quot.sound] or fewer." ]

theorem erdos260KeyCapstoneStatus_nonempty : erdos260KeyCapstoneStatus ≠ [] := by
  simp [erdos260KeyCapstoneStatus]

/-! ## Part 9.  Axiom-cleanliness audit -/

#print axioms Erdos260KeyResidual.toSplit
#print axioms Erdos260KeyResidual.toThirdsExclusion
#print axioms Erdos260KeyResidual.toValuation
#print axioms Erdos260KeyResidual.toStatement
#print axioms erdos260_of_keyResidual
#print axioms keyResidual_of_split
#print axioms keyResidual_of_thirdsExclusion
#print axioms keyResidual_of_valuation
#print axioms nonempty_keyResidual_iff_split
#print axioms nonempty_keyResidual_iff_thirdsExclusion
#print axioms nonempty_keyResidual_iff_valuation
#print axioms keyCapstone_returnZero_iff_keyInjOn
#print axioms keyCapstone_val0_atMostOne_of_keyInjOn
#print axioms keyCapstone_val1_card_le_one
#print axioms keyCapstone_level_card_le_pow
#print axioms keyCapstone_singletons_above_vCap
#print axioms returnKeyInjectiveField_of_parityReducedZero
#print axioms keyResidual_withParityReduced
#print axioms erdos260_key_of_parityReduced
#print axioms keyCapstone_keyInjOn_iff_valPosRun_of_parityEvenDatum
#print axioms keyCapstone_keyInjOn_iff_valPosSingletons_of_parityEvenDatum
#print axioms keyCapstone_val0_of_width_le_two
#print axioms keyCapstone_datum_63_10_dual_parity
#print axioms erdos260_key_multiScale_route
#print axioms erdos260_key_siblingSupply_route
#print axioms keyCapstone_firingWindow_clean
#print axioms keyCapstone_onset_above_cap
#print axioms keyCapstone_sibling_self
#print axioms erdos260_key_cofinalUpperBand_route
#print axioms erdos260_key_seedUpperBand_route
#print axioms erdos260_key_cofinalUpperBand_iff_lever
#print axioms erdos260_key_canonicalPerScale_route
#print axioms erdos260_key_perDepth_route
#print axioms erdos260_key_deepLeverV2_route
#print axioms erdos260KeyCapstoneStatus_nonempty

end

end Erdos260
