import Erdos260.FloorPushV2
import Erdos260.CarryValuationFloor
import Erdos260.DescentAllDepths

/-!
# Erdos 260 - the wave-10 valuation capstone (assembly)

Wave 10 lands three green modules; this one is their assembly verdict.

* `CarryValuationFloor` - `OlcFibreDeep` is a THEOREM (`olcFibreDeep_proved`: every
  class-4 fibre member sits at `k >= L = shellLadderDepth >= 28`, far beyond the demanded
  `>= 3`), so the wave-9 banded<->trajectory equivalence is UNCONDITIONAL
  (`nonempty_trajectoryResidual_iff_push`, `trajectoryResidualOfPush`); the `carryVal2`
  floor equals `v2(Q)` at every fibre member (`olcFibre_carryVal2_ge_dyadicPart`), with
  the exact Q-parity split (Q odd: the reset law `carryVal2 N = 0 iff N odd and d N = 1`);
  and the `returnZero` dyadic-floor successor field `ReturnZeroDyadicFloorField` with
  bridge `pushResidual_returnZero_field_of_dyadicFloor` and combinator
  `pushResidual_withDyadicFloorZero` - the field gains the FREE extra guard
  `2^{v2(Q)} < W` (`width_gt_of_returnZero_guard`).
* `FloorPushV2` - the successor surface `Erdos260FloorPushV2Residual` (the wave-9
  trajectory surface with the `q = 9` escape guard dropped via
  `TowerModulusEnumEscapeV2`; equivalence `nonempty_floorPushV2_iff_trajectory`) with
  endpoint `erdos260_of_floorPushV2`; the split floors (`q <= 2^20` gives
  `X > 2^986875`, `r >= 63`; per-pair value pins; the structural `r`-cap at 63); the new
  pinned family at 63@10 (`Q = 3*2^t`, value `10/(3*2^t)`); the pushed deep lever
  `DeepDyadicValueLeverPushV2` (demand only at `X > 2^986893`).
* `DescentAllDepths` - the conditional tower `PerScaleDescentWindowMatch ->
  CanonicalPerScaleSupply -> erdos260_of_canonicalPerScaleSupply`, the cofinal
  sufficiency `tailMatch_of_cofinal_fixedDenominator`, the leftmost-window pinch
  `onsetBudget_forces_shell_edge` (the deep tail match only at `k + r = X + 1`), and the
  no-cheaper-waypoint equivalence `canonicalPerScaleSupply_iff_lever`.  Conditional
  routes ONLY - re-exported here, never merged into the unconditional surface.

## The deliverable (honest)

`Erdos260ValuationResidual` - the wave-10 floor-push-v2 surface
`Erdos260FloorPushV2Residual` with its `returnZeroTrajectory` field further weakened by
the dyadic-floor guard `2^{ctxDyadicPart ctx} < W` of `CarryValuationFloor`.  The other
13 fields are verbatim.  Its endpoint composes only public bridges; nothing is re-proved.

### How the dyadic-floor guard composed (recorded honestly)

`CarryValuationFloor`'s bridge pair (`ReturnZeroDyadicFloorField` ->
`pushResidual_returnZero_field_of_dyadicFloor` -> `pushResidual_withDyadicFloorZero`)
lives on the BANDED wave-8 `returnZero` field (it concludes `ReturnZeroBodyBanded`),
while the FloorPushV2 surface holds the TRAJECTORY form
(`ReturnZeroBelowBandTrajectory`).  So on this surface the guard composes onto the
TRAJECTORY field: the discharge engine `width_gt_of_returnZero_guard` (the entire
content of the banded field bridge) eliminates the extra guard verbatim at the
trajectory shape (`toFloorPushV2`), and the chain continues through the public
`erdos260_of_floorPushV2`.  The banded combinator `pushResidual_withDyadicFloorZero` is
ALSO consumed, as the recorded alternate route: the valuation field plus the public
`returnZeroBodyBanded_of_belowBandTrajectory` yields a genuine
`ReturnZeroDyadicFloorField` (`toDyadicFloorField`), and the combinator applied to the
push image rebuilds an `Erdos260PushResidual` (`toPushResidualViaDyadicFloor`), with
endpoint `erdos260_of_valuationResidual_viaDyadicFloorZero`
(= `erdos260_of_dyadicFloorZero`).  Both routes land on `Erdos260Statement`.

### Equivalence accounting (recorded honestly)

The extra guard is FREE on demanded contexts (`width_gt_of_returnZero_guard`), so the
valuation surface is a presentation refinement EQUIVALENT to its predecessors, not a
strict shrink: `nonempty_valuationResidual_iff_floorPushV2`, `_iff_trajectory` (via
`nonempty_floorPushV2_iff_trajectory`), and `_iff_push` - the last through the wave-10
now-UNCONDITIONAL `nonempty_trajectoryResidual_iff_push` (the wave-9 deepness gate
`OlcFibreDeep` is discharged by `olcFibreDeep_proved`).
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The wave-10 valuation surface -/

/-- **The wave-10 valuation residual** - the wave-10 floor-push-v2 surface
(`Erdos260FloorPushV2Residual`) with its `returnZeroTrajectory` field further weakened
by the dyadic-floor guard `2^{v2(Q)} < W` (`CarryValuationFloor`; the guard is free on
demanded contexts by `width_gt_of_returnZero_guard`, so this surface is equal-or-weaker
to provide).  The other 13 fields are verbatim. -/
structure Erdos260ValuationResidual where
  /-- Tower / class 2 — enumerated part (`q < 107`); the `q = 9` `m₀`-guard is GONE. -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
    Class2CycleInequality ctx
  /-- Tower / class 2 — tail (`107 ≤ q`); the `q = 9` `m₀`-guard is GONE. -/
  towerEnumTail : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx →
    107 ≤ (class1SlopeDatum ctx).q →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx)
      ∨ Class2CycleInequality ctx
  /-- Run / class 5 — enumerated part (`q < 64`); verbatim wave-9 field. -/
  runNumericLow : ∀ ctx : ActualFailureContext,
    (class1SlopeDatum ctx).q < 64 →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 — tail (`64 ≤ q`); verbatim wave-9 field. -/
  runNumericTail : ∀ ctx : ActualFailureContext,
    64 ≤ (class1SlopeDatum ctx).q →
    ((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx
    ∨ Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Return / class 4 count gates — verbatim wave-9 field. -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 digit Z - trajectory form WITH the extra dyadic-floor guard (CarryValuationFloor; free on demanded contexts by width_gt_of_returnZero_guard). -/
  returnZeroTrajectoryFloor : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    2 ^ ctxDyadicPart ctx < (supportShell ctx.shell.d ctx.shell.X).card →
    ReturnZeroBelowBandTrajectory ctx
  /-- Return / class 4 clean step — trajectory form; verbatim wave-9 field. -/
  returnMaxCleanTrajectory : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnIndexWindowClean ctx →
    ReturnMaxCleanCarryTrajectory ctx
  /-- Return / class 4 K.1 interior — verbatim wave-9 field. -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- Chernoff / class 0 survivors — verbatim wave-9 field. -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    Class0SurvivorResidueMiss ctx
  /-- Chernoff / class 0 mid band — verbatim wave-9 field. -/
  class0Mid : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
    (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
    Class0WindowCycleCheck ctx
  /-- Chernoff / class 0 large moduli (`96 ≤ q`) — verbatim wave-9 field. -/
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
  /-- CNL / class 1 — enumerated deep part (`q < 101`); verbatim wave-9 field. -/
  class1DeepLow : ∀ ctx : ActualFailureContext,
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    ¬ Class1DatumClosed ctx →
    ¬ Class1GcdWindowMiss ctx →
    (class1SlopeDatum ctx).q < 101 →
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅
  /-- CNL / class 1 — tail (`101 ≤ q`); verbatim wave-9 field. -/
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
  /-- DensePack / class 3 — verbatim wave-9 field. -/
  densePackUngated : DensePackUngatedClosureResidual

/-! ## Part 2.  The endpoint - the guard discharged at the trajectory field -/

namespace Erdos260ValuationResidual

/-- **The bridge into the wave-10 floor-push-v2 surface**: the extra dyadic-floor guard
is discharged by `width_gt_of_returnZero_guard` (the `returnZero` guard itself forces
`2^{v2(Q)} < W` at every demanded context); the other 13 fields pass verbatim.  This is
the composition point of the `CarryValuationFloor` weakening with the FloorPushV2
surface shape - the guard composes onto the TRAJECTORY `returnZero` field, since that is
the form the v2 surface holds. -/
def toFloorPushV2 (R : Erdos260ValuationResidual) : Erdos260FloorPushV2Residual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnZeroTrajectory := fun ctx h1 h2 h3 h4 =>
    R.returnZeroTrajectoryFloor ctx h1 h2 h3 h4 (width_gt_of_returnZero_guard ctx h3)
  returnMaxCleanTrajectory := R.returnMaxCleanTrajectory
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- The final statement from the valuation residual: guard discharge, then the public
wave-10 chain `erdos260_of_floorPushV2` (-> `toTrajectoryResidual` via
`towerModulusEnumEscape_iff_v2` -> `erdos260_of_trajectoryResidual` -> the wave-9/8/6
chain).  Composition only. -/
theorem toStatement (R : Erdos260ValuationResidual) : Erdos260Statement :=
  erdos260_of_floorPushV2 R.toFloorPushV2

/-- **The banded composition, demonstrated** (the `CarryValuationFloor` bridge pair
consumed as named): the valuation field plus the public unconditional
`returnZeroBodyBanded_of_belowBandTrajectory` yields a genuine
`ReturnZeroDyadicFloorField` - the dyadic-floor-weakened BANDED field of
`CarryValuationFloor`. -/
def toDyadicFloorField (R : Erdos260ValuationResidual) : ReturnZeroDyadicFloorField :=
  fun ctx h1 h2 h3 h4 hguard =>
    returnZeroBodyBanded_of_belowBandTrajectory ctx
      (R.returnZeroTrajectoryFloor ctx h1 h2 h3 h4 hguard)

/-- **The alternate route through the banded combinator**: the push image of the
valuation surface with its `returnZero` field re-supplied through
`pushResidual_withDyadicFloorZero` - the literal `CarryValuationFloor` composition,
recorded for the audit trail (the main endpoint uses the direct trajectory-side
discharge instead). -/
def toPushResidualViaDyadicFloor (R : Erdos260ValuationResidual) : Erdos260PushResidual :=
  pushResidual_withDyadicFloorZero R.toFloorPushV2.toTrajectoryResidual.toPushResidual
    R.toDyadicFloorField

end Erdos260ValuationResidual

/-- **The wave-10 endpoint**: `Erdos260Statement` from the valuation surface. -/
theorem erdos260_of_valuationResidual (R : Erdos260ValuationResidual) :
    Erdos260Statement :=
  R.toStatement

/-- **The alternate endpoint through the banded combinator** - the
`CarryValuationFloor` endpoint `erdos260_of_dyadicFloorZero` fed by the valuation
surface's own push image and dyadic-floor field.  Both endpoints land on the same
statement; this one records that the named banded bridges genuinely fire. -/
theorem erdos260_of_valuationResidual_viaDyadicFloorZero (R : Erdos260ValuationResidual) :
    Erdos260Statement :=
  erdos260_of_dyadicFloorZero R.toFloorPushV2.toTrajectoryResidual.toPushResidual
    R.toDyadicFloorField

/-! ## Part 3.  Weakening witnesses and the equivalence chain -/

/-- **Weakening witness**: any floor-push-v2 provider yields the valuation surface (the
extra guard is simply dropped). -/
def valuationResidual_of_floorPushV2 (R : Erdos260FloorPushV2Residual) :
    Erdos260ValuationResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnZeroTrajectoryFloor := fun ctx h1 h2 h3 h4 _ =>
    R.returnZeroTrajectory ctx h1 h2 h3 h4
  returnMaxCleanTrajectory := R.returnMaxCleanTrajectory
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- Weakening witness from the wave-9 trajectory surface (through the v2 escape
equivalence). -/
def valuationResidual_of_trajectoryResidual (R : Erdos260TrajectoryResidual) :
    Erdos260ValuationResidual :=
  valuationResidual_of_floorPushV2 (floorPushV2Residual_of_trajectoryResidual R)

/-- Weakening witness from the wave-8 push surface - through the wave-10
NOW-UNCONDITIONAL converse `trajectoryResidualOfPush` (the wave-9 deepness gate
`OlcFibreDeep` is a theorem, `olcFibreDeep_proved`). -/
def valuationResidual_of_pushResidual (R : Erdos260PushResidual) :
    Erdos260ValuationResidual :=
  valuationResidual_of_trajectoryResidual (trajectoryResidualOfPush R)

/-- The valuation surface is EQUIVALENT to the floor-push-v2 surface (the extra guard is
free on demanded contexts - a presentation refinement, honestly recorded). -/
theorem nonempty_valuationResidual_iff_floorPushV2 :
    Nonempty Erdos260ValuationResidual ↔ Nonempty Erdos260FloorPushV2Residual :=
  ⟨fun ⟨R⟩ => ⟨R.toFloorPushV2⟩, fun ⟨R⟩ => ⟨valuationResidual_of_floorPushV2 R⟩⟩

/-- The valuation surface is equivalent to the wave-9 trajectory surface. -/
theorem nonempty_valuationResidual_iff_trajectory :
    Nonempty Erdos260ValuationResidual ↔ Nonempty Erdos260TrajectoryResidual :=
  nonempty_valuationResidual_iff_floorPushV2.trans nonempty_floorPushV2_iff_trajectory

/-- The valuation surface is equivalent to the wave-8 push surface - the chain closes
through the wave-10 UNCONDITIONAL `nonempty_trajectoryResidual_iff_push`
(`CarryValuationFloor`; the wave-9 version was gated on `OlcFibreDeep`). -/
theorem nonempty_valuationResidual_iff_push :
    Nonempty Erdos260ValuationResidual ↔ Nonempty Erdos260PushResidual :=
  nonempty_valuationResidual_iff_trajectory.trans nonempty_trajectoryResidual_iff_push

/-! ## Part 4.  Re-exported conditional routes (PARALLEL, not merged) -/

/-- **Re-export: the canonical per-scale supply route** (`DescentAllDepths`) -
`Erdos260Statement` from the per-scale canonical-centre match supply (at every deep
dyadic context: a `PerScaleDescentWindowMatch` plus one genuine start with the onset
budget `k + r <= X + 1` and the order budget `2*ord_{q0}(2) <= X`) plus the
lever-shrunk wave-5 surfaces.  Conditional: `DescentWindowMatch` is open data in-tree. -/
theorem erdos260_valuation_canonicalPerScale_route (h : CanonicalPerScaleSupply)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_of_canonicalPerScaleSupply h surfaces

/-- **Re-export: the no-cheaper-waypoint equivalence** (`DescentAllDepths`, NO FREE
LUNCH at the per-scale layer): `CanonicalPerScaleSupply` is logically EQUIVALENT to the
dyadic-value lever it feeds - supplying the per-scale match at dyadic contexts IS the
voiding; no intermediate waypoint exists. -/
theorem erdos260_valuation_canonicalPerScale_iff_lever :
    CanonicalPerScaleSupply ↔ DyadicValueLever :=
  canonicalPerScaleSupply_iff_lever

/-- **Re-export: the conditional per-depth route** (`TailMatchSupply`, wave 9) -
`Erdos260Statement` from per-depth bounded-denominator matches plus the lever-shrunk
wave-5 surfaces. -/
theorem erdos260_valuation_perDepth_route (h : DeepDyadicPerDepthMatch)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_of_dyadicPerDepthMatch h surfaces

/-- **Re-export: the pushed deep-lever route v2** (`FloorPushV2`) - the dyadic-value
exclusion demanded only at `X > 2^986893` (the regime below is closed unconditionally
by `shellValueDyadic_void_of_scale_pushV2`; strictly less demanded than the wave-8
`2^986891`). -/
theorem erdos260_valuation_deepLeverV2_route (h : DeepDyadicValueLeverPushV2)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_floorPushV2_deepLever_route h surfaces

/-! ## Part 5.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the wave-10 valuation capstone. -/
def erdos260ValuationCapstoneStatus : List String :=
  [ "MAIN ENDPOINT (wave 10): erdos260_of_valuationResidual (R : Erdos260ValuationResidual) " ++
      ": Erdos260Statement.  Erdos260ValuationResidual = the wave-10 floor-push-v2 surface " ++
      "Erdos260FloorPushV2Residual (the wave-9 trajectory surface with the q=9 escape guard " ++
      "dropped via TowerModulusEnumEscapeV2) with its returnZeroTrajectory field further " ++
      "weakened by the dyadic-floor guard 2^{v2(Q)} = 2^{ctxDyadicPart ctx} < W " ++
      "(CarryValuationFloor); the other 13 fields verbatim.  Route: toFloorPushV2 (guard " ++
      "discharged by width_gt_of_returnZero_guard) -> erdos260_of_floorPushV2 -> " ++
      "toTrajectoryResidual (towerModulusEnumEscape_iff_v2) -> erdos260_of_trajectoryResidual " ++
      "-> the wave-9/8/6 chain.  Composition only; nothing re-proved.",
    "HOW THE DYADIC-FLOOR GUARD COMPOSED (honest): CarryValuationFloor's bridge pair " ++
      "(ReturnZeroDyadicFloorField -> pushResidual_returnZero_field_of_dyadicFloor -> " ++
      "pushResidual_withDyadicFloorZero) lives on the BANDED wave-8 returnZero field (it " ++
      "concludes ReturnZeroBodyBanded), while the FloorPushV2 surface holds the TRAJECTORY " ++
      "form (ReturnZeroBelowBandTrajectory).  So the guard composes onto the TRAJECTORY " ++
      "returnZero field here: the discharge engine width_gt_of_returnZero_guard (the entire " ++
      "content of the banded bridge) eliminates the guard verbatim at the trajectory shape " ++
      "(toFloorPushV2).  The banded combinator is ALSO consumed, as the recorded alternate " ++
      "route: toDyadicFloorField (the valuation field + the public unconditional " ++
      "returnZeroBodyBanded_of_belowBandTrajectory gives a genuine ReturnZeroDyadicFloorField) " ++
      "+ pushResidual_withDyadicFloorZero on the push image = toPushResidualViaDyadicFloor, " ++
      "endpoint erdos260_of_valuationResidual_viaDyadicFloorZero (= " ++
      "erdos260_of_dyadicFloorZero).  Both routes land on Erdos260Statement.",
    "WAVE-10 INPUT (CarryValuationFloor): OlcFibreDeep is a THEOREM at every ctx " ++
      "(olcFibreDeep_proved; members >= L = shellLadderDepth >= 28, olcFibre_mem_ge_depth - " ++
      "far beyond the demanded >= 3), so the wave-9 banded<->trajectory equivalence is now " ++
      "UNCONDITIONAL: nonempty_trajectoryResidual_iff_push, trajectoryResidualOfPush, " ++
      "returnZeroBody_iff_belowBandTrajectory_uncond.  The carryVal2 floor: carryVal2 k >= " ++
      "v2(Q) at EVERY fibre member (olcFibre_carryVal2_ge_dyadicPart; carryVal2_ge_dyadicPart " ++
      "+ ctxDyadicPart_lt_depth), exact Q-parity split (Q even: carryVal2 >= 1 everywhere, " ++
      "carryVal2_pos_of_Q_even; Q odd: NO positive floor - the reset law carryVal2 N = 0 iff " ++
      "N odd and d N = 1, carryVal2_eq_zero_iff_of_Q_odd / carryVal2_pos_of_Q_odd_miss).  " ++
      "The returnZero field is CLOSED (vacuous) on width <= 2^{v2(Q)} shells " ++
      "(returnZero_guard_refuted_of_width_le); demanded contexts force 2^{v2(Q)} < W " ++
      "(width_gt_of_returnZero_guard) - exactly the FREE extra guard this surface adds.  " ++
      "Strong window facts: olcFibre_mem_ge_depth (members >= L), " ++
      "carryFloor_supportCount_ge_of_le_depth (supportCount >= m for every m <= L).",
    "WAVE-10 INPUT (FloorPushV2): successor surface Erdos260FloorPushV2Residual (the q=9 " ++
      "escape guard 3 <= m0 DROPPED - a theorem at the split floor; TowerModulusEnumEscapeV2; " ++
      "pointwise equivalence towerModulusEnumEscape_iff_v2; Nonempty equivalence " ++
      "nonempty_floorPushV2_iff_trajectory), endpoint erdos260_of_floorPushV2.  Split floors: " ++
      "q <= 2^20 -> X > 2^986875, r >= 63, m0 >= 3 (floorPushV2_*_of_q_le_2pow20); per-pair " ++
      "value pins (q=9: oddpart(Q) <= 3, X > 2^986892; q=11/13/(105,52): oddpart(Q) = 1 " ++
      "FORCED, X > 2^986893; q=63: u in {1,3,7,9,21}, X > 2^986889, r >= 63); the structural " ++
      "r-cap at 63 (sharp fire 17g <= 2^24 caps the void region at L <= 986893, so r >= 64 " ++
      "needs L >= 986896 - OUT of reach; the wave-9 thresholds r >= 85/106/149 for " ++
      "q=11/13/(105,52) are NOT reachable by ANY oddpart-route floor, the windows only " ++
      "narrow to [63,84]/[63,105]/[63,148]).  The q=9 count window [32,41] is EMPTY " ++
      "(floorPushV2_q9_count_window_empty) and every q=9 context is an escape context " ++
      "(floorPushV2_q9_demand_everywhere) - the q=9 demand sharpens to voiding the contexts " ++
      "themselves (value pins 4/2^t at u=1 and 1/(3*2^t) at u=3).  NEW pinned family at " ++
      "63@10: oddpart(Q) = 3 EXACTLY, Q = 3*2^t, value = 10/(3*2^t) " ++
      "(floorPushV2_q63K10_Q_shape / _value), X > 2^986892.  Pushed deep lever " ++
      "DeepDyadicValueLeverPushV2 (demand only at X > 2^986893; " ++
      "dyadicValueLever_of_deepScalePushV2; re-exported below).",
    "WAVE-10 INPUT (DescentAllDepths, conditional routes ONLY - re-exported, never merged): " ++
      "the conditional tower PerScaleDescentWindowMatch -> CanonicalPerScaleSupply -> " ++
      "erdos260_of_canonicalPerScaleSupply (re-export erdos260_valuation_canonicalPerScale_" ++
      "route); cofinal sufficiency tailMatch_of_cofinal_fixedDenominator (matches at " ++
      "cofinally many depths already promote to TailMatch - a shell-bounded depth range does " ++
      "NOT suffice); the leftmost-window pinch onsetBudget_forces_shell_edge (the sec-25.3 " ++
      "shell placement X < k+r plus the onset budget k+r <= X+1 force k+r = X+1: only the " ++
      "FIRST shell window can carry the deep tail match); the no-cheaper-waypoint " ++
      "equivalence canonicalPerScaleSupply_iff_lever (CanonicalPerScaleSupply <-> " ++
      "DyadicValueLever - supplying the per-scale match at dyadic contexts IS the voiding).  " ++
      "DescentWindowMatch is OPEN DATA in-tree; every route in that module is conditional.",
    "WEAKENING WITNESSES + EQUIVALENCES: toFloorPushV2 (guard discharge, forward); " ++
      "valuationResidual_of_floorPushV2 (drop the free guard, backward); " ++
      "valuationResidual_of_trajectoryResidual (via floorPushV2Residual_of_" ++
      "trajectoryResidual); valuationResidual_of_pushResidual (via the NOW-UNCONDITIONAL " ++
      "trajectoryResidualOfPush).  Nonempty chain: nonempty_valuationResidual_iff_" ++
      "floorPushV2 / _iff_trajectory (via nonempty_floorPushV2_iff_trajectory) / _iff_push " ++
      "(via the wave-10 unconditional nonempty_trajectoryResidual_iff_push).  HONEST: the " ++
      "valuation surface is a presentation refinement EQUIVALENT to the wave-8 push surface " ++
      "- the extra guard is free on demanded contexts, so nothing strictly shrinks; the " ++
      "wave-10 gains are the discharged deepness gate, the dropped q=9 escape guard, and " ++
      "the explicit closed regime W <= 2^{v2(Q)} inside returnZero.",
    "RE-EXPORTED CONDITIONAL ROUTES (all PARALLEL to the unconditional surface): (1) " ++
      "erdos260_valuation_canonicalPerScale_route (h : CanonicalPerScaleSupply) (surfaces : " ++
      "DyadicValueLever -> Erdos260DyadicLeverResidual) = erdos260_of_canonicalPerScale" ++
      "Supply, with erdos260_valuation_canonicalPerScale_iff_lever = canonicalPerScale" ++
      "Supply_iff_lever (no cheaper waypoint).  (2) erdos260_valuation_perDepth_route = " ++
      "erdos260_of_dyadicPerDepthMatch (per-depth bounded-denominator matches, wave 9).  " ++
      "(3) erdos260_valuation_deepLeverV2_route = erdos260_floorPushV2_deepLever_route " ++
      "(the dyadic exclusion demanded only at X > 2^986893).",
    "SHARPEST OPEN ATOM (sharpened in place by this wave): per-scale upper-band membership " ++
      "at cofinally many depths at the FIRST shell window (k + r = X + 1, " ++
      "onsetBudget_forces_shell_edge) - at dyadic-value contexts it is exactly as strong as " ++
      "the voiding it feeds (canonicalPerScaleSupply_iff_lever).  Cheapest named follow-up: " ++
      "a 1/(3*2^t)-exclusion lever - it voids the q=9 u=3 branch AND sharpens the new 63@10 " ++
      "pinned family (value 10/(3*2^t), the same oddpart-3 shape).",
    "HYGIENE: additive only; no upstream module touched; no sorry / admit / new axiom / " ++
      "native_decide; all #print axioms in [propext, Classical.choice, Quot.sound]." ]

theorem erdos260ValuationCapstoneStatus_nonempty :
    erdos260ValuationCapstoneStatus ≠ [] := by
  simp [erdos260ValuationCapstoneStatus]

/-! ## Part 6.  Axiom-cleanliness audit -/

#print axioms Erdos260ValuationResidual.toFloorPushV2
#print axioms Erdos260ValuationResidual.toStatement
#print axioms Erdos260ValuationResidual.toDyadicFloorField
#print axioms Erdos260ValuationResidual.toPushResidualViaDyadicFloor
#print axioms erdos260_of_valuationResidual
#print axioms erdos260_of_valuationResidual_viaDyadicFloorZero
#print axioms valuationResidual_of_floorPushV2
#print axioms valuationResidual_of_trajectoryResidual
#print axioms valuationResidual_of_pushResidual
#print axioms nonempty_valuationResidual_iff_floorPushV2
#print axioms nonempty_valuationResidual_iff_trajectory
#print axioms nonempty_valuationResidual_iff_push
#print axioms erdos260_valuation_canonicalPerScale_route
#print axioms erdos260_valuation_canonicalPerScale_iff_lever
#print axioms erdos260_valuation_perDepth_route
#print axioms erdos260_valuation_deepLeverV2_route
#print axioms erdos260ValuationCapstoneStatus_nonempty

end

end Erdos260
