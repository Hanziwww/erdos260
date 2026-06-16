import Erdos260.Erdos260PushCapstone
import Erdos260.BandedDigitClosure
import Erdos260.TailMatchSupply
import Erdos260.PairInstanceClosure

/-!
# Erdős 260 — the wave-9 trajectory capstone (assembly)

Wave 9 lands three green modules; this one is their assembly verdict.

* `BandedDigitClosure` — the two digit-valued Return fields of `Erdos260PushResidual`
  recast in PURE CARRY-TRAJECTORY form (`ReturnDigitTrajectorySurface`, matching the
  capstone field shapes exactly), with the drop-in bridges
  `pushResidual_returnZero_field_of_trajectory` /
  `pushResidual_returnMaxClean_field_of_trajectory`, the combinator
  `pushResidual_withTrajectoryDigits`, and the endpoint `erdos260_of_trajectoryDigits`.
* `TailMatchSupply` — the section-25.1 tail-match supply chain: the conditional per-depth
  route `erdos260_of_dyadicPerDepthMatch`, the bounded-vs-TailMatch equivalence
  (`tailMatch_iff_perDepth_bounded`), and the no-free-lunch refutation
  `deepDyadicTailMatch_iff_lever`.
* `PairInstanceClosure` — the per-pair `r`-window accounting: `r ≥ 32` closes no new
  counted pair / class-0 survivor / class-1 pair (the escape thresholds are wave-3–5
  upper edges the lower floor cannot move), the future floor targets `r ≥ 42/85/106/149`,
  and the surviving exceptional cofactors `{3,5,7,9,15,21,63}`.

## The deliverable (honest)

`Erdos260TrajectoryResidual` — the official wave-8 push surface `Erdos260PushResidual`
with its TWO digit-valued Return fields (`returnZero` / `returnMaxClean`, banded) REPLACED
by the trajectory forms `returnZeroTrajectory` / `returnMaxCleanTrajectory`.  The other 12
fields are verbatim.  Its endpoint composes the public BandedDigitClosure bridges; nothing
is re-proved.

### Equivalence-direction accounting (recorded honestly)

* **trajectory ⟹ banded is UNCONDITIONAL.**  A carry-trajectory provider rebuilds the
  banded digit fields outright (`returnZeroBodyBanded_of_belowBandTrajectory` /
  `returnMaxCleanBodyBanded_of_carryTrajectory`, packaged as the field bridges).  Hence
  `pushResidual_of_trajectoryResidual : Erdos260TrajectoryResidual → Erdos260PushResidual`
  holds with NO side condition: `Erdos260TrajectoryResidual` is the (equal-or-stronger)
  trajectory presentation of the push surface.
* **The converse (banded ⟹ trajectory) needs `OlcFibreDeep`.**  Recovering the
  below-band trajectory from a banded `returnZero` provider needs fibre deepness at every
  context (`trajectorySurface_of_pushResidual`; only positions `0,1,2` escape the deep
  escape bound).  So `trajectoryResidual_of_pushResidual` is gated on
  `∀ ctx, OlcFibreDeep ctx`; the `returnMaxClean` lane needs no deepness, but the bundled
  converse does.  No unconditional `Nonempty` equivalence is claimed.

This is the entire weakening account: the trajectory surface is reached unconditionally
from the wave-8 push surface only in one direction; the reverse is honestly conditional.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The wave-9 trajectory surface -/

/-- **The wave-9 trajectory residual** — the official wave-8 push surface
(`Erdos260PushResidual`) with its TWO digit-valued Return fields replaced by the pure
carry-trajectory forms from `BandedDigitClosure` (`ReturnDigitTrajectorySurface`).  The
other 12 fields are verbatim: their conclusions carry no digit values.  Inhabiting this
surface is equal-or-stronger than inhabiting `Erdos260PushResidual` (the trajectory forms
imply the banded digit fields unconditionally). -/
structure Erdos260TrajectoryResidual where
  /-- Tower / class 2 — enumerated part (`q < 107`); verbatim wave-8 field. -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscape ctx → (class1SlopeDatum ctx).q < 107 →
    Class2CycleInequality ctx
  /-- Tower / class 2 — tail (`107 ≤ q`); verbatim wave-8 field. -/
  towerEnumTail : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscape ctx →
    107 ≤ (class1SlopeDatum ctx).q →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx)
      ∨ Class2CycleInequality ctx
  /-- Run / class 5 — enumerated part (`q < 64`); verbatim wave-8 field. -/
  runNumericLow : ∀ ctx : ActualFailureContext,
    (class1SlopeDatum ctx).q < 64 →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 — tail (`64 ≤ q`); verbatim wave-8 field. -/
  runNumericTail : ∀ ctx : ActualFailureContext,
    64 ≤ (class1SlopeDatum ctx).q →
    ((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx
    ∨ Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Return / class 4 count gates — gate-free 3-way body; verbatim wave-8 field. -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 digit Z — TRAJECTORY form: the below-band carry trajectory plus
  the final doubling on every demanded slice interval (replaces the banded `returnZero`
  field; implies it unconditionally through `returnZeroBodyBanded_of_belowBandTrajectory`). -/
  returnZeroTrajectory : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    ReturnZeroBelowBandTrajectory ctx
  /-- Return / class 4 clean step — TRAJECTORY form: one carry-doubling equation per
  per-slice maximum (replaces the banded `returnMaxClean` field; implies it
  unconditionally through `returnMaxCleanBodyBanded_of_carryTrajectory`). -/
  returnMaxCleanTrajectory : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnIndexWindowClean ctx →
    ReturnMaxCleanCarryTrajectory ctx
  /-- Return / class 4 K.1 interior — verbatim wave-8 field (an index bound). -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- Chernoff / class 0 survivors — verbatim wave-8 field. -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    Class0SurvivorResidueMiss ctx
  /-- Chernoff / class 0 mid band — verbatim wave-8 field. -/
  class0Mid : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
    (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
    Class0WindowCycleCheck ctx
  /-- Chernoff / class 0 large moduli (`96 ≤ q`) — verbatim wave-8 field. -/
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
  /-- CNL / class 1 — enumerated deep part (`q < 101`); verbatim wave-8 field. -/
  class1DeepLow : ∀ ctx : ActualFailureContext,
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    ¬ Class1DatumClosed ctx →
    ¬ Class1GcdWindowMiss ctx →
    (class1SlopeDatum ctx).q < 101 →
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅
  /-- CNL / class 1 — tail (`101 ≤ q`); verbatim wave-8 field. -/
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
  /-- DensePack / class 3 — the collapsed ungated residual; verbatim wave-8 field. -/
  densePackUngated : DensePackUngatedClosureResidual

/-! ## Part 2.  The endpoint — composing the BandedDigitClosure bridges -/

namespace Erdos260TrajectoryResidual

/-- The two trajectory fields, packaged as the BandedDigitClosure successor surface. -/
def toTrajectorySurface (R : Erdos260TrajectoryResidual) : ReturnDigitTrajectorySurface where
  returnZeroTrajectory := R.returnZeroTrajectory
  returnMaxCleanTrajectory := R.returnMaxCleanTrajectory

/-- **The bridge into the wave-8 push surface** (UNCONDITIONAL): the 12 non-digit fields
pass verbatim and the two trajectory fields rebuild the banded digit fields outright via
the public field bridges `pushResidual_returnZero_field_of_trajectory` /
`pushResidual_returnMaxClean_field_of_trajectory`.  Nothing is re-proved. -/
def toPushResidual (R : Erdos260TrajectoryResidual) : Erdos260PushResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnZero := pushResidual_returnZero_field_of_trajectory R.returnZeroTrajectory
  returnMaxClean := pushResidual_returnMaxClean_field_of_trajectory R.returnMaxCleanTrajectory
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- The final statement from the trajectory residual, composing the BandedDigitClosure
combinator `pushResidual_withTrajectoryDigits` and endpoint `erdos260_of_trajectoryDigits`
(itself routing through `erdos260_of_pushResidual` and the entire wave-8/6 lineage).
Nothing is re-proved. -/
theorem toStatement (R : Erdos260TrajectoryResidual) : Erdos260Statement :=
  erdos260_of_trajectoryDigits R.toPushResidual R.toTrajectorySurface

end Erdos260TrajectoryResidual

/-- **The wave-9 final endpoint.**  `Erdos260Statement` from the trajectory residual —
the push surface with its two digit fields supplied in pure carry-trajectory form.  The
route is `erdos260_of_trajectoryDigits ∘ (toPushResidual, toTrajectorySurface)`; no field
is re-proved anywhere. -/
theorem erdos260_of_trajectoryResidual (R : Erdos260TrajectoryResidual) : Erdos260Statement :=
  R.toStatement

/-! ## Part 3.  Weakening witnesses and the (conditional) converse -/

/-- **Weakening witness, UNCONDITIONAL**: every trajectory provider yields the wave-8 push
surface (trajectory ⟹ banded needs no side condition).  This is the only direction that
holds for free. -/
def pushResidual_of_trajectoryResidual (R : Erdos260TrajectoryResidual) :
    Erdos260PushResidual :=
  R.toPushResidual

/-- **Weakening witness, UNCONDITIONAL** (per-pair instance lane): the trajectory provider
also yields the `PairInstanceClosure` successor surface (`r ≥ 32` closes no field). -/
def pairInstanceResidual_of_trajectoryResidual (R : Erdos260TrajectoryResidual) :
    Erdos260PairInstanceResidual :=
  pairInstanceResidual_of_pushResidual R.toPushResidual

/-- **The converse, CONDITIONAL on fibre deepness**: a wave-8 push provider yields the
trajectory residual ONLY given `OlcFibreDeep` at every context (the `returnZero` lane
needs deepness to recover the below-band trajectory; recorded via
`trajectorySurface_of_pushResidual`).  No unconditional converse exists. -/
def trajectoryResidual_of_pushResidual (R : Erdos260PushResidual)
    (hdeep : ∀ ctx : ActualFailureContext, OlcFibreDeep ctx) :
    Erdos260TrajectoryResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnZeroTrajectory := (trajectorySurface_of_pushResidual R hdeep).returnZeroTrajectory
  returnMaxCleanTrajectory :=
    (trajectorySurface_of_pushResidual R hdeep).returnMaxCleanTrajectory
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- The unconditional `Nonempty` weakening (trajectory ⟹ push).  The reverse direction is
conditional on `∀ ctx, OlcFibreDeep ctx` (`trajectoryResidual_of_pushResidual`), so no
unconditional `Nonempty` equivalence is asserted. -/
theorem nonempty_pushResidual_of_trajectoryResidual :
    Nonempty Erdos260TrajectoryResidual → Nonempty Erdos260PushResidual :=
  fun ⟨R⟩ => ⟨pushResidual_of_trajectoryResidual R⟩

/-- The `Nonempty` equivalence with the wave-8 push surface, GATED on global fibre
deepness — the honest converse boundary. -/
theorem nonempty_trajectoryResidual_iff_push_of_deep
    (hdeep : ∀ ctx : ActualFailureContext, OlcFibreDeep ctx) :
    Nonempty Erdos260TrajectoryResidual ↔ Nonempty Erdos260PushResidual :=
  ⟨nonempty_pushResidual_of_trajectoryResidual,
   fun ⟨R⟩ => ⟨trajectoryResidual_of_pushResidual R hdeep⟩⟩

/-! ## Part 4.  Re-exported conditional routes (PARALLEL, not merged) -/

/-- **Re-export: the conditional per-depth route** (`TailMatchSupply`) —
`Erdos260Statement` from per-depth bounded-denominator matches plus the lever-shrunk
wave-5 surfaces.  `DeepDyadicPerDepthMatch` is exactly as strong as `DeepDyadicTailMatch`
(`deepDyadicPerDepthMatch_iff`); supplying it from the in-tree fixed-centre residue-band
data at all depths is the sharpest open frontier. -/
theorem erdos260_trajectory_perDepth_route (h : DeepDyadicPerDepthMatch)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_of_dyadicPerDepthMatch h surfaces

/-- **Re-export: the tail-match / lever equivalence** (`TailMatchSupply`, NO FREE LUNCH) —
the frontier prop `DeepDyadicTailMatch` is logically EQUIVALENT to the full dyadic-value
lever it was meant to supply (backward: the lever empties the hypothesis class, so the
supply is vacuous).  Supplying the tail match at pinned contexts IS the voiding. -/
theorem erdos260_trajectory_tailMatch_iff_lever :
    DeepDyadicTailMatch ↔ DyadicValueLever :=
  deepDyadicTailMatch_iff_lever

/-- **Re-export: the deep-lever route** (`Erdos260PushCapstone`) — `Erdos260Statement`
from the pushed deep dyadic-value lever (demanded only at `X > 2^986891`; the regime below
is closed unconditionally by the pushed pinned-value floor). -/
theorem erdos260_trajectory_deepLever_route (R : Erdos260DeepLeverPushResidual) :
    Erdos260Statement :=
  erdos260_push_deepLever_route R

/-- **Re-export: the per-pair instance endpoint** (`PairInstanceClosure`) —
`Erdos260Statement` from the per-pair instance surface (equivalent to the push surface;
`r ≥ 32` closes no new field). -/
theorem erdos260_trajectory_pairInstance_route (H : Erdos260PairInstanceResidual) :
    Erdos260Statement :=
  erdos260_of_pairInstanceResidual H

/-! ## Part 5.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the wave-9 trajectory capstone. -/
def erdos260TrajectoryCapstoneStatus : List String :=
  [ "MAIN ENDPOINT (wave 9): erdos260_of_trajectoryResidual (R : Erdos260TrajectoryResidual) " ++
      ": Erdos260Statement.  Erdos260TrajectoryResidual = the wave-8 push surface " ++
      "Erdos260PushResidual with its TWO digit-valued Return fields (returnZero / " ++
      "returnMaxClean, banded) REPLACED by the pure carry-trajectory forms " ++
      "returnZeroTrajectory / returnMaxCleanTrajectory (BandedDigitClosure's " ++
      "ReturnDigitTrajectorySurface shapes); the other 12 fields verbatim.  Route: " ++
      "toPushResidual (field bridges pushResidual_returnZero/returnMaxClean_field_of_trajectory) " ++
      "+ toTrajectorySurface -> erdos260_of_trajectoryDigits (which routes through " ++
      "pushResidual_withTrajectoryDigits -> erdos260_of_pushResidual -> the wave-8/6 chain).  " ++
      "Nothing re-proved; only public bridges consumed.",
    "DIGIT-FIELD CONVERSION (the wave-9 content, BandedDigitClosure): returnMaxClean is the " ++
      "EXACT carry-doubling equivalence returnMaxCleanBody_iff_carryTrajectory (the clean " ++
      "step at a per-slice maximum <-> one carry-doubling equation, no digit content); " ++
      "returnZero is the pure-carry restatement of the below-band demand " ++
      "(returnZeroBody / ReturnZeroBelowBandTrajectory) - zero-runs are constant-capped " ++
      "(<= 3 in general, <= 1 deep) by the escape-time argument band_zeroRun_envelope, and " ++
      "the only isolated open inputs are a positive carryVal2 lower bound at fibre members " ++
      "together with OlcFibreDeep.",
    "EQUIVALENCE-DIRECTION ACCOUNTING (honest): trajectory ==> banded is UNCONDITIONAL " ++
      "(returnZeroBodyBanded_of_belowBandTrajectory / returnMaxCleanBodyBanded_of_carryTrajectory), " ++
      "so pushResidual_of_trajectoryResidual : Erdos260TrajectoryResidual -> " ++
      "Erdos260PushResidual holds with NO side condition (and " ++
      "nonempty_pushResidual_of_trajectoryResidual).  The CONVERSE banded ==> trajectory " ++
      "needs OlcFibreDeep at every ctx (only positions 0,1,2 escape the deep escape bound; " ++
      "returnZero lane only - returnMaxClean needs none), so " ++
      "trajectoryResidual_of_pushResidual and the Nonempty equivalence " ++
      "nonempty_trajectoryResidual_iff_push_of_deep are GATED on (forall ctx, OlcFibreDeep " ++
      "ctx).  No unconditional Nonempty equivalence is claimed.",
    "WEAKENING WITNESSES (where they hold): pushResidual_of_trajectoryResidual (= " ++
      "toPushResidual, unconditional), pairInstanceResidual_of_trajectoryResidual " ++
      "(unconditional, into the PairInstanceClosure surface), and the conditional converse " ++
      "trajectoryResidual_of_pushResidual (needs OlcFibreDeep).",
    "RE-EXPORTED CONDITIONAL ROUTES (all PARALLEL to the unconditional surface, not merged): " ++
      "(1) erdos260_trajectory_perDepth_route (h : DeepDyadicPerDepthMatch) (surfaces : " ++
      "DyadicValueLever -> Erdos260DyadicLeverResidual) = erdos260_of_dyadicPerDepthMatch - " ++
      "per-depth bounded-denominator matches; DeepDyadicPerDepthMatch <-> DeepDyadicTailMatch " ++
      "(deepDyadicPerDepthMatch_iff), per-depth existence is FREE at growing denominators " ++
      "(matchesCompletion_exists_perDepth) but a free self-match is REFUTED.  (2) " ++
      "erdos260_trajectory_tailMatch_iff_lever = deepDyadicTailMatch_iff_lever - NO FREE " ++
      "LUNCH: DeepDyadicTailMatch is logically EQUIVALENT to the dyadic-value lever it was " ++
      "meant to supply (the lever empties the hypothesis class), so the supply at pinned " ++
      "contexts IS the voiding - no intermediate waypoint.  (3) " ++
      "erdos260_trajectory_deepLever_route (R : Erdos260DeepLeverPushResidual) = " ++
      "erdos260_push_deepLever_route - the dyadic-value exclusion demanded only at " ++
      "X > 2^986891.  (4) erdos260_trajectory_pairInstance_route = " ++
      "erdos260_of_pairInstanceResidual.",
    "PAIR-WINDOW FINDINGS (PairInstanceClosure, equivalence note): r >= 32 everywhere " ++
      "(pic_r_ge_32) closes NO new counted pair, class-0 survivor, or class-1 pair - the " ++
      "tower escape thresholds are wave-3-5 UPPER edges (q=9 r>=42, q=11 r>=85, q=13 " ++
      "r>=106, (105,52) r>=149) that the lower floor cannot move, and the class-0/class-1 " ++
      "obstructions are r-independent residue/congruence pins.  So " ++
      "Erdos260PairInstanceResidual is EQUIVALENT to Erdos260PushResidual " ++
      "(nonempty_pairInstanceResidual_iff_push), not strictly smaller.  FUTURE floor " ++
      "targets r >= 42/85/106/149 would void the tower windows.  Cofactor cross: " ++
      "mersenneSmallOrderModuli INTERSECT class1ClosedModuli = {31} (pic_cofactor_31_closed); " ++
      "surviving cofactors {3,5,7,9,15,21,63} (picCofactorsSurviving_eq), of which 63 is the " ++
      "open class-1 pair 63@10.",
    "CHEAPEST IN-TREE MOVE: extend DescentWindowMatch's fixed-depth canonical-centre match " ++
      "to ALL depths (the section-25.1 iterated 25.1/25.3 descent gives a uniform " ++
      "denominator bound across depths for an irreducible input); that supplies " ++
      "DeepDyadicPerDepthMatch and hence DeepDyadicTailMatch (tailMatch_iff_perDepth_bounded).",
    "HYGIENE: additive only; no upstream module touched; no sorry / admit / new axiom / " ++
      "native_decide; all #print axioms in [propext, Classical.choice, Quot.sound]." ]

theorem erdos260TrajectoryCapstoneStatus_nonempty :
    erdos260TrajectoryCapstoneStatus ≠ [] := by
  simp [erdos260TrajectoryCapstoneStatus]

/-! ## Part 6.  Axiom-cleanliness audit -/

#print axioms Erdos260TrajectoryResidual.toTrajectorySurface
#print axioms Erdos260TrajectoryResidual.toPushResidual
#print axioms Erdos260TrajectoryResidual.toStatement
#print axioms erdos260_of_trajectoryResidual
#print axioms pushResidual_of_trajectoryResidual
#print axioms pairInstanceResidual_of_trajectoryResidual
#print axioms trajectoryResidual_of_pushResidual
#print axioms nonempty_pushResidual_of_trajectoryResidual
#print axioms nonempty_trajectoryResidual_iff_push_of_deep
#print axioms erdos260_trajectory_perDepth_route
#print axioms erdos260_trajectory_tailMatch_iff_lever
#print axioms erdos260_trajectory_deepLever_route
#print axioms erdos260_trajectory_pairInstance_route
#print axioms erdos260TrajectoryCapstoneStatus_nonempty

end

end Erdos260
