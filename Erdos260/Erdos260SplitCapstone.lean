import Erdos260.QOddResetClosure
import Erdos260.ThirdsExclusionLever
import Erdos260.UpperBandPerScale

/-!
# The wave-11 split capstone - canonical digit splits on the thirds-exclusion surface

This module (NEW; it edits no existing file) assembles the three wave-11 deliverables
into one surface and one endpoint.

## The three inputs (all green, all additive)

* `QOddResetClosure.lean` - the CANONICAL digit splits: `ReturnZeroBody` is
  UNCONDITIONALLY the split form `QOddVal0AtMostOne AND QOddValPosZeroRun`
  (`returnZeroBody_iff_qOddSplit_uncond`), and `ReturnMaxCleanBody` at Q odd is the
  per-parity split `QOddMaxCleanSplit` (odd `k+1` = pure carry-parity fact, even `k+1` =
  unchanged doubling; `returnMaxCleanBody_iff_qOddSplit`).  The four per-parity successor
  fields (`ReturnZeroQOddSplitField`, `ReturnZeroQEvenFloorField`,
  `ReturnMaxCleanQOddSplitField`, `ReturnMaxCleanQEvenField`) rebuild the verbatim
  wave-10 digit fields through the PUBLIC bridges
  `returnZeroTrajectoryFloor_of_qOddSplit` / `returnMaxCleanTrajectory_of_qOddSplit`.
  ADOPTED here as the canonical digit fields of the new surface.
* `ThirdsExclusionLever.lean` - the APERIODICITY GUARDS: every `q <= 21` context is
  window-APERIODIC (`thirdsLever_smallq_not_windowPeriodic`; per-target forms
  `thirdsLever_q9_not_windowPeriodic` and `thirdsLever_q63K10_not_windowPeriodic`), and
  the surface `Erdos260ThirdsExclusionResidual` hands the free guard
  `oddpart(Q) <= 7 -> NOT WindowPeriodic ctx` to the two tower fields and
  `class1DeepLow` (endpoint `erdos260_of_thirdsExclusionLever`, equivalence
  `nonempty_thirdsExclusion_iff_valuation`).  FOLDED here verbatim.
* `UpperBandPerScale.lean` - the BAND TRANSITION LAW
  `rho_{n+1} = (2*rho_n + d(s+n)*q0) mod 2^{n+1}` (`bandResidue_succ`) and the
  equivalence chain: per-scale band at cofinally many depths IS TailMatch
  (`upperBandAt_cofinal_iff_tailMatch`) IS the lever (`cofinalUpperBandSupply_iff_lever`)
  - no shortcut.  THE REPAIR FINDING (recorded prominently below): the wave-10
  `PerScaleDescentWindowMatch.ofResidueBand` all-depths hypothesis is UNSATISFIABLE
  (`not_upperBandAt_zero` / `perScale_residueBand_all_depths_empty` - the band is FALSE
  at depth 0).  The live route is the repaired constructor
  `PerScaleDescentWindowMatch.ofUpperBandCofinal` and the successor atoms
  `CofinalUpperBandSupply` / `SeedUpperBandSupply` with endpoint
  `erdos260_of_cofinalUpperBand`.

## The new surface and endpoint

`Erdos260SplitResidual` := the thirds-exclusion surface with its two wave-10 digit
fields REPLACED by the four canonical per-parity split fields (16 fields total).
Endpoint `erdos260_of_splitResidual : Erdos260SplitResidual -> Erdos260Statement`,
composed ONLY from public bridges: the split fields rebuild the verbatim wave-10 digit
field shapes (QOddResetClosure bridges), which are exactly the thirds surface's digit
field shapes, then `Erdos260ThirdsExclusionResidual.toValuation` discharges the
aperiodicity guards and `erdos260_of_valuationResidual` runs the wave-10 chain.
Weakening witnesses and Nonempty-equivalences in both directions (the split shapes are
an equivalent presentation refinement - honestly recorded).  The conditional routes are
re-exported PARALLEL with the REPAIRED constructors only.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The wave-11 split surface -/

/-- **The wave-11 split surface**: the thirds-exclusion surface
(`Erdos260ThirdsExclusionResidual` - aperiodicity guards on the two tower fields and
`class1DeepLow`) with the two wave-10 digit-side Return fields REPLACED by the four
canonical per-parity split fields of `QOddResetClosure`.  The other 12 fields are
verbatim thirds-exclusion shapes. -/
structure Erdos260SplitResidual where
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
  /-- Return / class 4 digit Z, Q ODD - **the canonical split shape**: at most one
  val-0 fibre member plus the zero-run demand on val-POSITIVE slice pairs
  (`QOddResetClosure.ReturnZeroQOddSplitField`). -/
  returnZeroQOddSplit : ReturnZeroQOddSplitField
  /-- Return / class 4 digit Z, Q EVEN - the verbatim dyadic-floor trajectory field
  restricted to even denominators (`QOddResetClosure.ReturnZeroQEvenFloorField`). -/
  returnZeroQEvenFloor : ReturnZeroQEvenFloorField
  /-- Return / class 4 clean step, Q ODD - **the canonical per-parity split shape**:
  odd `k+1` demands the carry EVEN (pure parity), even `k+1` keeps the doubling form
  (`QOddResetClosure.ReturnMaxCleanQOddSplitField`). -/
  returnMaxCleanQOddSplit : ReturnMaxCleanQOddSplitField
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

namespace Erdos260SplitResidual

/-- **The bridge into the thirds-exclusion surface**: the four split fields rebuild the
two verbatim wave-10 digit field shapes through the PUBLIC `QOddResetClosure` bridges
(`returnZeroTrajectoryFloor_of_qOddSplit`, `returnMaxCleanTrajectory_of_qOddSplit`) -
the rebuilt shapes are exactly the thirds surface's digit field shapes (it holds them
verbatim from wave 10), so the composition order is: split fields -> wave-10 digit
fields -> thirds surface.  The other 12 fields pass verbatim. -/
def toThirdsExclusion (R : Erdos260SplitResidual) : Erdos260ThirdsExclusionResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnZeroTrajectoryFloor :=
    returnZeroTrajectoryFloor_of_qOddSplit R.returnZeroQOddSplit R.returnZeroQEvenFloor
  returnMaxCleanTrajectory :=
    returnMaxCleanTrajectory_of_qOddSplit R.returnMaxCleanQOddSplit R.returnMaxCleanQEven
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- The wave-10 valuation surface, through the thirds bridge (the aperiodicity guards
are discharged by `thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven` inside
`Erdos260ThirdsExclusionResidual.toValuation`). -/
def toValuation (R : Erdos260SplitResidual) : Erdos260ValuationResidual :=
  R.toThirdsExclusion.toValuation

/-- The final statement: split fields -> thirds surface -> valuation surface -> the
public wave-10 chain.  Composition only; nothing re-proved. -/
theorem toStatement (R : Erdos260SplitResidual) : Erdos260Statement :=
  erdos260_of_valuationResidual R.toValuation

end Erdos260SplitResidual

/-- **THE WAVE-11 ENDPOINT**: `Erdos260Statement` from the split surface. -/
theorem erdos260_of_splitResidual (R : Erdos260SplitResidual) : Erdos260Statement :=
  R.toStatement

/-- **The alternate endpoint through the `QOddResetClosure` combinator** - the split
fields fed to `erdos260_of_qOddSplit` (= `valuationResidual_withQOddSplit` + the
wave-10 chain) over the surface's own valuation image.  HONEST: the base's digit
fields are already the rebuilds of the same four split fields, so the combinator
overwrite is idempotent here; recorded to show the `QOddResetClosure` endpoint
genuinely fires.  Both endpoints land on the same statement. -/
theorem erdos260_of_splitResidual_viaQOddSplit (R : Erdos260SplitResidual) :
    Erdos260Statement :=
  erdos260_of_qOddSplit R.toThirdsExclusion.toValuation
    R.returnZeroQOddSplit R.returnZeroQEvenFloor
    R.returnMaxCleanQOddSplit R.returnMaxCleanQEven

/-! ## Part 3.  Weakening witnesses and the equivalence chain -/

/-- **Weakening witness**: any thirds-exclusion provider yields the split surface.
The Q-even split fields are verbatim restrictions; `returnMaxCleanQOddSplit` comes
through the exact equivalence `maxCleanCarryTrajectory_iff_qOddSplit`; and
`returnZeroQOddSplit` comes through `belowBandTrajectory_iff_qOddSplit` with the
dyadic-floor guard discharged FREE by `width_gt_of_returnZero_guard` (the count guard
itself forces `2^{v2(Q)} < W`). -/
def splitResidual_of_thirdsExclusion (R : Erdos260ThirdsExclusionResidual) :
    Erdos260SplitResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnZeroQOddSplit := fun ctx hA hB hC hD hQodd =>
    (belowBandTrajectory_iff_qOddSplit ctx hQodd).mp
      (R.returnZeroTrajectoryFloor ctx hA hB hC hD
        (width_gt_of_returnZero_guard ctx hC))
  returnZeroQEvenFloor := fun ctx hA hB hC hD hE _ =>
    R.returnZeroTrajectoryFloor ctx hA hB hC hD hE
  returnMaxCleanQOddSplit := fun ctx hA hD hQodd =>
    (maxCleanCarryTrajectory_iff_qOddSplit ctx hQodd).mp
      (R.returnMaxCleanTrajectory ctx hA hD)
  returnMaxCleanQEven := fun ctx hA hD _ =>
    R.returnMaxCleanTrajectory ctx hA hD
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- Weakening witness from the wave-10 valuation surface (drop the aperiodicity
guards, then split the digit fields). -/
def splitResidual_of_valuation (R : Erdos260ValuationResidual) :
    Erdos260SplitResidual :=
  splitResidual_of_thirdsExclusion (thirdsExclusionResidual_of_valuation R)

/-- The split surface is EQUIVALENT to the thirds-exclusion surface: the split shapes
are exact decompositions (`returnZeroBody_iff_qOddSplit_uncond`,
`returnMaxCleanBody_iff_qOddSplit`), so this is a presentation refinement - honestly
recorded, the digit obligations are SHARPER IN SHAPE but logically equal. -/
theorem nonempty_splitResidual_iff_thirdsExclusion :
    Nonempty Erdos260SplitResidual ↔ Nonempty Erdos260ThirdsExclusionResidual :=
  ⟨fun ⟨R⟩ => ⟨R.toThirdsExclusion⟩, fun ⟨R⟩ => ⟨splitResidual_of_thirdsExclusion R⟩⟩

/-- The split surface is equivalent to the wave-10 valuation surface (composing with
the thirds equivalence `nonempty_thirdsExclusion_iff_valuation`). -/
theorem nonempty_splitResidual_iff_valuation :
    Nonempty Erdos260SplitResidual ↔ Nonempty Erdos260ValuationResidual :=
  nonempty_splitResidual_iff_thirdsExclusion.trans nonempty_thirdsExclusion_iff_valuation

/-! ## Part 4.  The wave-10 repair and the retired strata, recorded prominently

**THE WAVE-10 `ofResidueBand` ROUTE IS DEAD.**  The wave-10
`PerScaleDescentWindowMatch.ofResidueBand` (`DescentAllDepths.lean`) takes the residue
band at ALL depths `n` - but the band is FALSE at depth `0` (`not_upperBandAt_zero`:
`rho_0 = 0` while `2^0 - q0 = 0` needs `0 < 0`), so that hypothesis is UNSATISFIABLE
at any genuine start (`perScale_residueBand_all_depths_empty`).  Any earlier status
text recommending the all-depths `ofResidueBand` route is now known dead; the
read-only wave-10 files are NOT edited - the record lives here.  The live route is the
repaired cofinal constructor `PerScaleDescentWindowMatch.ofUpperBandCofinal` and the
successor atoms `CofinalUpperBandSupply` / `SeedUpperBandSupply`. -/

/-- Re-export of the depth-0 falsity (the root of the wave-10 repair): the upper band
NEVER holds at depth `0`. -/
theorem splitCapstone_not_upperBandAt_zero (d : ℕ → ℕ) (s q0 : ℕ) :
    ¬ UpperBandAt d s q0 0 :=
  not_upperBandAt_zero

/-- Re-export of the unsatisfiability verdict: a residue band demanded at ALL depths
(`UpperBandAt` form) empties the genuine start set - the wave-10 all-depths
`ofResidueBand` hypothesis can never be supplied at a genuine start. -/
theorem splitCapstone_residueBand_all_depths_dead (ctx : ActualFailureContext)
    (hband : ∀ n : ℕ, ∀ k ∈ genuineDensePackStarts ctx,
      UpperBandAt ctx.shell.d (k + ctx.n24CarryData.r) (canonicalCenter ctx).q0 n) :
    ∀ k, k ∉ genuineDensePackStarts ctx :=
  fun k hk => not_upperBandAt_zero (hband 0 k hk)

/-- Re-export of the aperiodicity retirement: EVERY `q ≤ 21` context is
window-aperiodic - the periodic stratum of the `q = 9` branches and the `63@10`
crossover is formally retired; the open problems live on the aperiodic tail. -/
theorem splitCapstone_smallq_aperiodic (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 21) : ¬ WindowPeriodic ctx :=
  thirdsLever_smallq_not_windowPeriodic ctx hq

/-! ## Part 5.  Re-exported conditional routes (PARALLEL, not merged; repaired
constructors only) -/

/-- **Re-export: the cofinal upper-band route** (`UpperBandPerScale`, the REPAIRED
satisfiable form of the wave-10 per-scale supply): `Erdos260Statement` from upper-band
membership at cofinally many scales per genuine start (plus onset/order budgets) and
the lever-shrunk wave-5 surfaces. -/
theorem erdos260_split_cofinalUpperBand_route (h : CofinalUpperBandSupply)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_of_cofinalUpperBand h surfaces

/-- **Re-export: the seed form** - ONE banded base depth plus the tail expansion of its
complement per genuine start (the sharpest finitely-anchored shape), through
`cofinalUpperBandSupply_of_seed`. -/
theorem erdos260_split_seedUpperBand_route (h : SeedUpperBandSupply)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_of_cofinalUpperBand (cofinalUpperBandSupply_of_seed h) surfaces

/-- **Re-export: no free lunch at the band layer** - the cofinal upper-band supply is
logically EQUIVALENT to the dyadic-value lever it feeds; the per-scale band IS the
tail match IS the lever (`upperBandAt_cofinal_iff_tailMatch` +
`cofinalUpperBandSupply_iff_lever`). -/
theorem erdos260_split_cofinalUpperBand_iff_lever :
    CofinalUpperBandSupply ↔ DyadicValueLever :=
  cofinalUpperBandSupply_iff_lever

/-- **Re-export: the canonical per-scale route** (wave 10; its only LIVE supply is now
the repaired `PerScaleDescentWindowMatch.ofUpperBandCofinal` /
`canonicalPerScaleSupply_of_cofinalUpperBand` - the all-depths `ofResidueBand` shape
is unsatisfiable, see Part 4). -/
theorem erdos260_split_canonicalPerScale_route (h : CanonicalPerScaleSupply)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_valuation_canonicalPerScale_route h surfaces

/-- **Re-export: the conditional per-depth route** (wave 9). -/
theorem erdos260_split_perDepth_route (h : DeepDyadicPerDepthMatch)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_valuation_perDepth_route h surfaces

/-- **Re-export: the pushed deep-lever route v2** (`FloorPushV2`; demand only at
`X > 2^986893`). -/
theorem erdos260_split_deepLeverV2_route (h : DeepDyadicValueLeverPushV2)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_valuation_deepLeverV2_route h surfaces

/-- **Re-export: the `qOddSplit` endpoint** (`QOddResetClosure`): `Erdos260Statement`
from any wave-10 valuation base with the four digit fields supplied in split form. -/
theorem erdos260_split_qOddSplit_route (base : Erdos260ValuationResidual)
    (hz1 : ReturnZeroQOddSplitField) (hz0 : ReturnZeroQEvenFloorField)
    (hm1 : ReturnMaxCleanQOddSplitField) (hm0 : ReturnMaxCleanQEvenField) :
    Erdos260Statement :=
  erdos260_of_qOddSplit base hz1 hz0 hm1 hm0

/-! ## Part 6.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the wave-11 split capstone. -/
def erdos260SplitCapstoneStatus : List String :=
  [ "SURFACE: Erdos260SplitResidual = the wave-11 thirds-exclusion surface " ++
      "(free aperiodicity guards oddpart(Q) <= 7 -> NOT WindowPeriodic on " ++
      "towerEnumLow / towerEnumTail / class1DeepLow) with the two wave-10 digit " ++
      "fields REPLACED by the four canonical per-parity split fields of " ++
      "QOddResetClosure: returnZeroQOddSplit (= at most one val-0 fibre member + " ++
      "zero-runs on val-POSITIVE slice pairs; the dyadic-floor guard dropped as " ++
      "contentless at Q odd), returnZeroQEvenFloor (verbatim dyadic-floor " ++
      "trajectory at Q even), returnMaxCleanQOddSplit (odd k+1 = carry EVEN, a pure " ++
      "parity fact; even k+1 = unchanged doubling), returnMaxCleanQEven (verbatim " ++
      "doubling at Q even).  16 fields total; 12 verbatim thirds shapes.",
    "ENDPOINT + COMPOSITION (honest): erdos260_of_splitResidual via " ++
      "toThirdsExclusion - the split fields rebuild the verbatim wave-10 digit " ++
      "field shapes through the PUBLIC QOddResetClosure bridges " ++
      "returnZeroTrajectoryFloor_of_qOddSplit / returnMaxCleanTrajectory_of_" ++
      "qOddSplit (parity case split + the exact iffs), and those shapes are " ++
      "exactly the thirds surface's digit fields (held verbatim from wave 10); " ++
      "then Erdos260ThirdsExclusionResidual.toValuation discharges the " ++
      "aperiodicity guards (thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven) " ++
      "and erdos260_of_valuationResidual runs the wave-10 chain.  Nothing " ++
      "re-proved.  Alternate endpoint erdos260_of_splitResidual_viaQOddSplit " ++
      "through erdos260_of_qOddSplit / valuationResidual_withQOddSplit - HONEST: " ++
      "the combinator overwrite is idempotent on the already-rebuilt base; " ++
      "recorded to show the QOddResetClosure endpoint genuinely fires.",
    "WITNESSES + EQUIVALENCES: splitResidual_of_thirdsExclusion (Q-even fields = " ++
      "verbatim restrictions; returnMaxCleanQOddSplit via maxCleanCarryTrajectory_" ++
      "iff_qOddSplit; returnZeroQOddSplit via belowBandTrajectory_iff_qOddSplit " ++
      "with the dyadic-floor guard discharged FREE by width_gt_of_returnZero_" ++
      "guard), splitResidual_of_valuation; nonempty_splitResidual_iff_" ++
      "thirdsExclusion and nonempty_splitResidual_iff_valuation.  HONEST: the " ++
      "split surface is an EQUIVALENT presentation refinement of the wave-8..10 " ++
      "chain (returnZeroBody_iff_qOddSplit_uncond is unconditional; the digit " ++
      "obligations are sharper in SHAPE, equal in content).",
    "APERIODICITY RETIREMENT (folded): every q <= 21 context is window-APERIODIC " ++
      "(thirdsLever_smallq_not_windowPeriodic; re-export splitCapstone_smallq_" ++
      "aperiodic; per-target thirdsLever_q9_not_windowPeriodic and thirdsLever_" ++
      "q63K10_not_windowPeriodic) - the periodic stratum of the q=9 branches and " ++
      "the 63@10 crossover is formally retired; the open problems concentrate on " ++
      "the aperiodic tail.  The guards ride FREE on the three folded fields.",
    "THE WAVE-10 REPAIR (PROMINENT): the wave-10 PerScaleDescentWindowMatch." ++
      "ofResidueBand all-depths hypothesis is UNSATISFIABLE - the band is FALSE " ++
      "at depth 0 (not_upperBandAt_zero: rho_0 = 0; re-exports splitCapstone_not_" ++
      "upperBandAt_zero and splitCapstone_residueBand_all_depths_dead = " ++
      "perScale_residueBand_all_depths_empty).  ANY earlier status text " ++
      "recommending the all-depths ofResidueBand route is DEAD (the read-only " ++
      "wave-10 files are not edited; the record lives here).  The LIVE route is " ++
      "the repaired cofinal constructor PerScaleDescentWindowMatch." ++
      "ofUpperBandCofinal and the successor atoms CofinalUpperBandSupply / " ++
      "SeedUpperBandSupply.",
    "BAND TRANSITION LAW (folded findings): rho_{n+1} = (2*rho_n + d(s+n)*q0) " ++
      "mod 2^{n+1} (bandResidue_succ); band at cofinally many depths IS TailMatch " ++
      "(upperBandAt_cofinal_iff_tailMatch: the band-at-all-depths trajectory IS " ++
      "the binary expansion of c/q0) IS the lever (cofinalUpperBandSupply_iff_" ++
      "lever - NO shortcut, no cheaper waypoint).  The descent atom is now ONE " ++
      "digit per scale at the leftmost pinch k + r = X + 1, with first-deviation " ++
      "permanence (upperBandAt_persists_not: once the band fails it fails at " ++
      "every deeper scale).",
    "RE-EXPORTED CONDITIONAL ROUTES (all PARALLEL, repaired constructors only): " ++
      "erdos260_split_cofinalUpperBand_route (+ seed form erdos260_split_" ++
      "seedUpperBand_route, equivalence erdos260_split_cofinalUpperBand_iff_" ++
      "lever), erdos260_split_canonicalPerScale_route (live supply = " ++
      "canonicalPerScaleSupply_of_cofinalUpperBand), erdos260_split_perDepth_" ++
      "route, erdos260_split_deepLeverV2_route, erdos260_split_qOddSplit_route.",
    "HYGIENE: additive only - no existing module edited (the root import file " ++
      "gained one line); no sorry / admit / new axiom / native_decide; all " ++
      "#print axioms in [propext, Classical.choice, Quot.sound] or fewer." ]

theorem erdos260SplitCapstoneStatus_nonempty : erdos260SplitCapstoneStatus ≠ [] := by
  simp [erdos260SplitCapstoneStatus]

/-! ## Part 7.  Axiom-cleanliness audit -/

#print axioms Erdos260SplitResidual.toThirdsExclusion
#print axioms Erdos260SplitResidual.toValuation
#print axioms Erdos260SplitResidual.toStatement
#print axioms erdos260_of_splitResidual
#print axioms erdos260_of_splitResidual_viaQOddSplit
#print axioms splitResidual_of_thirdsExclusion
#print axioms splitResidual_of_valuation
#print axioms nonempty_splitResidual_iff_thirdsExclusion
#print axioms nonempty_splitResidual_iff_valuation
#print axioms splitCapstone_not_upperBandAt_zero
#print axioms splitCapstone_residueBand_all_depths_dead
#print axioms splitCapstone_smallq_aperiodic
#print axioms erdos260_split_cofinalUpperBand_route
#print axioms erdos260_split_seedUpperBand_route
#print axioms erdos260_split_cofinalUpperBand_iff_lever
#print axioms erdos260_split_canonicalPerScale_route
#print axioms erdos260_split_perDepth_route
#print axioms erdos260_split_deepLeverV2_route
#print axioms erdos260_split_qOddSplit_route
#print axioms erdos260SplitCapstoneStatus_nonempty

end

end Erdos260
