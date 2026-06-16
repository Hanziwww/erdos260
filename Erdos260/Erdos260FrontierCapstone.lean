import Erdos260.OnsetBoundClosure
import Erdos260.OrbitPinVoiding
import Erdos260.DeepShellTailClosure
import Erdos260.AbsorptionGateClosure

/-!
# The wave-18 frontier capstone: `Erdos260FrontierResidual`

The wave-17 endgame surface (`Erdos260EndgameResidual`) REBASED on the four
wave-18 lanes:

* **`OrbitPinVoiding`** — the three orbit-pin voiding fields (`returnBand2Void`,
  `densePackBand3Void`, `runBand4Void`) collapse to the SINGLE deep field
  `deepOrbitPin : DeepOrbitPinVoiding` (demanded only at `X > 2^986891`): every
  shallow regime is closed unconditionally by the proved scale floors
  (`orbitBandPinned2/4_void_of_scale`, `band3PinnedWide_void_of_scale` — the
  conditional kills at `X ≤ 2^986893` / `2^986891` are folded INTO the field),
  and by `deepOrbitPinVoiding_iff_deepFixedFamilyVoid` the field IS the wave-8
  deep fixed-family axis: no strength is gained or lost.  The three deep value
  levers supply the whole field (`deepOrbitPinVoiding_of_levers`).
* **`DeepShellTailClosure`** — `class1Deep` is the class-1 absorption demanded
  ONLY on the genuinely deep shells `L ≥ 1274740` (where `r ≥ 82` is proved):
  the parametric width gate `dstClass1Absorption_of_depth_le` closes EVERY datum
  (on-table, off-table, all `q ≥ 200`) at `L ≤ 1274739 = ⌊31·2^24/408⌋`, on top
  of the 110-pair `L ≤ T` regime relief already in the wave-17 capstone.  The
  tower / run lane fields become floor-guarded supplies
  (`dstTowerEnumLow/Tail_field_of_floors`, `dstRunNumericLow/Tail_field_of_floors`):
  the supplies may assume the proved context floors (`L ≥ 986888` on the pinned
  bands, `r ≥ 63`/`32`, sparsity-block floors).
* **`AbsorptionGateClosure`** — the class-0 field is carried in the de-razored
  MASS shape on all three lanes (`class0Mass`, the `Erdos260AbsorptionResidual`
  field verbatim), reaching the statement through
  `erdos260_of_absorptionResidual`; the interior fields and the pin-free return
  count gate get NAMED conditional consumption slots
  (`frontierReturnInterior_of_topBandDevLight`,
  `frontierDensePackInterior_of_topBandDevLight`,
  `frontierReturnGatesFree_of_cycleCount`).
* **`OnsetBoundClosure`** — the covering-family lane: as in wave 17 the lane is
  a PARALLEL endpoint, NOT a surface field (the v17 endgame surface never
  carried it, and the covering endpoint additionally consumes the wave-5 lever
  surfaces).  It is recorded here as `frontier_offCycleParallel`: the
  fixed-cycle stratum of the covering demand is PROVED pin-free
  (`certifiedCycleWindow_void`) and the consumer reduces LOSSLESSLY to
  `OffCycleCoveringSupply` (`coveringFamilies_iff_offCycle`).

## The surface (12 fields)

`deepOrbitPin` (replaces the three voidings; shallow free) + `towerEnumLow` /
`towerEnumTail` / `runNumericLow` / `runNumericTail` (floor-guarded supply
shapes) + `returnGatesFree` / `returnInterior` / `densePackCoverFree` /
`densePackDensity` / `densePackInterior` (verbatim wave-17 shapes) +
`class0Mass` (mass shape, all three lanes) + `class1Deep` (deep shells only).

## The endpoint

`erdos260_of_frontierResidual` routes through the wave-18 absorption surface:
the frontier fields rebuild a full `Erdos260AbsorptionResidual`
(`toAbsorptionResidual`) and `erdos260_of_absorptionResidual` finishes through
the FULLY-corrected six-phase ledger.

## Folds kept at the v17 shape (honest)

`returnGatesFree`, `returnInterior`, `densePackCoverFree`, `densePackDensity`,
`densePackInterior` stay verbatim: the wave-18 conditional closures
(top-band-dev-light, cycle-count) are SUPPLY slots, not weakenings — their
hypotheses are genuine new demands (`agcTopBandDev_le_cap` shows the in-tree
deviation ceiling exceeds the heaviness floor, so the dev-light form is not
implied; a `(q,K0,c,b2)` table would slot into the cycle-count gate).  The
class-0 mid/big lanes keep the certificate horn verbatim inside the mass shape
(the wave-18 de-razoring already replaced emptiness by mass there).
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The wave-18 frontier surface -/

/-- **The wave-18 frontier capstone surface.**  The wave-17 endgame surface rebased on
the four wave-18 lanes: the three orbit-pin voiding fields are replaced by the single
deep-scale field `deepOrbitPin` (shallow regimes proved free), the class-1 absorption
is demanded only on the genuinely deep shells `L ≥ 1274740` (the parametric width gate
closes everything below), the tower/run fields carry the proved context floors as free
hypotheses, and the class-0 field is in the de-razored mass shape.  12 fields. -/
structure Erdos260FrontierResidual where
  /-- **The single deep orbit-pin voiding** (replaces `returnBand2Void` +
  `densePackBand3Void` + `runBand4Void`): the three voidings demanded ONLY at
  `X > 2^986891` — the shallow regime is closed unconditionally by the proved scale
  floors (bands 2/3-wide at `X ≤ 2^986893`, band 4 at `X ≤ 2^986891`).  By
  `deepOrbitPinVoiding_iff_voidings` this field is EQUIVALENT to the three v17
  fields; by `deepOrbitPinVoiding_iff_deepFixedFamilyVoid` it IS the wave-8 deep
  fixed-family axis; by `deepOrbitPinVoiding_of_levers` the three deep value levers
  supply it outright. -/
  deepOrbitPin : DeepOrbitPinVoiding
  /-- Tower / class 2 - enumerated part (`q < 107`), floor-guarded: the supply may
  assume `L ≥ 986888` (q-side pin), `r ≥ 63` and a sparsity block `≥ 3`
  (`dstTowerEnumLow_field_of_floors` rebuilds the exact v17 field). -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
    ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
    986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
    3 ≤ towerSparsityBlock ctx →
    Class2CycleInequality ctx
  /-- Tower / class 2 - tail (`107 ≤ q`), floor-guarded: unconditional `L ≥ 493461`,
  `r ≥ 32`, block `≥ 2`, with the pin upgrade `L ≥ 986888` on `107 ≤ q < 384`
  (`dstTowerEnumTail_field_of_floors` rebuilds the exact v17 field). -/
  towerEnumTail : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx →
    107 ≤ (class1SlopeDatum ctx).q →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    493461 ≤ shellLadderDepth ctx → 32 ≤ ctx.n24CarryData.r →
    2 ≤ towerSparsityBlock ctx →
    ((class1SlopeDatum ctx).q < 384 → 986888 ≤ shellLadderDepth ctx) →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx)
      ∨ Class2CycleInequality ctx
  /-- Run / class 5 - enumerated part (`q < 64`) on band-4-free contexts,
  floor-guarded: the supply may assume `L ≥ 986888` and `r ≥ 63`
  (`dstRunNumericLow_field_of_floors`).  The band-4-free guard is discharged by
  `deepOrbitPin` through `runBand4Void_of_deepOrbitPinVoiding`. -/
  runNumericLow : ∀ ctx : ActualFailureContext,
    ¬ OrbitBandPinned ctx 4 →
    (class1SlopeDatum ctx).q < 64 →
    986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 - tail (`64 ≤ q`) on band-4-free contexts, floor-guarded:
  unconditional `L ≥ 493461`, `r ≥ 32`, with the pin upgrade on `64 ≤ q < 384`
  (`dstRunNumericTail_field_of_floors`); relieved of `(93,15)`. -/
  runNumericTail : ∀ ctx : ActualFailureContext,
    ¬ OrbitBandPinned ctx 4 →
    64 ≤ (class1SlopeDatum ctx).q →
    ¬ ((class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 15) →
    493461 ≤ shellLadderDepth ctx → 32 ≤ ctx.n24CarryData.r →
    ((class1SlopeDatum ctx).q < 384 → 986888 ≤ shellLadderDepth ctx) →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx)
    ∨ (Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx)
  /-- Return / class 4 count gates on band-2-free contexts (verbatim wave-17 field;
  the band-2-free guard is discharged by `deepOrbitPin`).  Conditional supply slot:
  `frontierReturnGatesFree_of_cycleCount` (a per-ctx certified period `c` with the
  window regime `(W/c + 1)·b₂ ≤ r + 1`). -/
  returnGatesFree : ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 2 →
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 K.1 interior (verbatim wave-17 field).  Conditional supply
  slot: `frontierReturnInterior_of_topBandDevLight` (top-band deviation `< Y`). -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- DensePack / class 3 corrected K.1.2 Nat-cover on the wide band-3-free
  complement (verbatim wave-17 field; the guard is discharged by `deepOrbitPin`). -/
  densePackCoverFree : ∀ ctx : ActualFailureContext, ¬ Band3PinnedWide ctx →
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card
  /-- DensePack / class 3 K.1.1 coarea hit-density (verbatim wave-17 field). -/
  densePackDensity : ∀ ctx : ActualFailureContext,
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    densePackEndpointDensity ctx
  /-- DensePack / class 3 K.1 active-window interior (verbatim wave-17 field).
  Conditional supply slot: `frontierDensePackInterior_of_topBandDevLight`. -/
  densePackInterior : ∀ ctx : ActualFailureContext,
    ¬ Class3TopBandCycleFree ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card
  /-- **The mass-shaped class-0 field** (the wave-18 de-razored shape, verbatim from
  `Erdos260AbsorptionResidual`): routed MASS caps `mass₀ ≤ (31/1536)·X` on the
  survivor lane and the mid-band lane, and on the big-order lane the certificate horn
  OR the mass cap.  Both sum routes to this field are formally refuted
  (`agcClass0DevGate_refuted` / `agcGenericDevGate_refuted`: the in-tree deviation
  budget is a FLOOR `(768/1536)·X`, factor `24.8` above the cap) — the count gate at
  the 19 survivor pairs is the genuinely open named conditional. -/
  class0Mass : ∀ ctx : ActualFailureContext,
    (Class0DatumSurvivor ctx →
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)) ∧
    (48 ≤ (class1SlopeDatum ctx).q → (class1SlopeDatum ctx).q < 96 →
      Class0CycleMeetsShallow ctx →
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)) ∧
    (96 ≤ (class1SlopeDatum ctx).q →
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
      ∨ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
          ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ))
  /-- **The deep-shell class-1 field** (the wave-18 relief): the class-1 count-cap
  absorption demanded ONLY at `L ≥ 1274740` (where `r ≥ 82` is proved) on off-regime
  data — the ENTIRE band `L ≤ 1274739` is relieved by the parametric width gate
  `dstClass1Absorption_of_depth_le` (sharp: `dstWidthGate_sharp`), on top of the
  110-pair `L ≤ T` regime relief.  Per-pair currency: `DstClass1DeepPairAtom`
  (consume through `frontierClass1Deep_of_pairAtoms`). -/
  class1Deep : ∀ ctx : ActualFailureContext,
    1274740 ≤ shellLadderDepth ctx → 82 ≤ ctx.n24CarryData.r →
    1 ≤ ctx.n24CarryData.r →
    (¬ ∃ cv bv Tv : ℕ,
      ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀, cv, bv, Tv)
          ∈ sreClass1ThresholdTable
        ∧ shellLadderDepth ctx ≤ Tv) →
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)

namespace Erdos260FrontierResidual

/-! ### The rebuild: frontier → wave-18 absorption surface -/

/-- **The frontier surface rebuilds the full wave-18 absorption surface**: the three
voiding fields from `deepOrbitPin` (shallow kills folded in), the tower/run fields
through the floor-guarded producers, the class-1 field through the parametric width
gate.  Composition only. -/
def toAbsorptionResidual (R : Erdos260FrontierResidual) : Erdos260AbsorptionResidual where
  towerEnumLow := dstTowerEnumLow_field_of_floors R.towerEnumLow
  towerEnumTail := dstTowerEnumTail_field_of_floors R.towerEnumTail
  runBand4Void := runBand4Void_of_deepOrbitPinVoiding R.deepOrbitPin
  runNumericLow := dstRunNumericLow_field_of_floors R.runNumericLow
  runNumericTail := dstRunNumericTail_field_of_floors R.runNumericTail
  returnBand2Void := returnBand2Void_of_deepOrbitPinVoiding R.deepOrbitPin
  returnGatesFree := R.returnGatesFree
  returnInterior := R.returnInterior
  densePackBand3Void := densePackBand3Void_of_deepOrbitPinVoiding R.deepOrbitPin
  densePackCoverFree := R.densePackCoverFree
  densePackDensity := R.densePackDensity
  densePackInterior := R.densePackInterior
  class0MassAbsorption := R.class0Mass
  class1CapAbsorption := dstClass1CapAbsorption_field_of_deep R.class1Deep

/-- The final statement from the wave-18 frontier surface, through the absorption
route and the fully-corrected six-phase ledger.  Composition only. -/
theorem toStatement (R : Erdos260FrontierResidual) : Erdos260Statement :=
  R.toAbsorptionResidual.toStatement

end Erdos260FrontierResidual

/-- **THE WAVE-18 ENDPOINT**: `Erdos260Statement` from the folded 12-field frontier
surface — the three orbit-pin voidings replaced by the single deep field (shallow
regimes proved free), the class-1 absorption demanded only beyond the parametric
width gate `L > 1274739`, the tower/run supplies floor-guarded, the class-0 lanes
in routed-mass shape.  Public bridges only. -/
theorem erdos260_of_frontierResidual (R : Erdos260FrontierResidual) :
    Erdos260Statement :=
  R.toStatement

/-! ## Part 2.  The weakening witnesses: wave 17 / wave 18a → frontier (never harder) -/

/-- **The weakening witness from the wave-18 absorption surface**: every absorption
inhabitant yields a frontier inhabitant — `deepOrbitPin` is the deep restriction of
the three voiding fields, the tower/run/class-1 fields DROP their new floor guards,
everything else transports verbatim.  One direction only; NO converse is claimed
(the converse direction is exactly the wave-18 relief). -/
def frontierResidual_of_absorptionResidual (R : Erdos260AbsorptionResidual) :
    Erdos260FrontierResidual where
  deepOrbitPin := fun ctx _ =>
    ⟨R.returnBand2Void ctx, R.densePackBand3Void ctx, R.runBand4Void ctx⟩
  towerEnumLow := fun ctx hesc hq haper h31 h213 _ _ _ =>
    R.towerEnumLow ctx hesc hq haper h31 h213
  towerEnumTail := fun ctx hesc hq haper _ _ _ _ =>
    R.towerEnumTail ctx hesc hq haper
  runNumericLow := fun ctx hpin hq _ _ => R.runNumericLow ctx hpin hq
  runNumericTail := fun ctx hpin hq h93 _ _ _ => R.runNumericTail ctx hpin hq h93
  returnGatesFree := R.returnGatesFree
  returnInterior := R.returnInterior
  densePackCoverFree := R.densePackCoverFree
  densePackDensity := R.densePackDensity
  densePackInterior := R.densePackInterior
  class0Mass := R.class0MassAbsorption
  class1Deep := fun ctx _ _ hr hreg => R.class1CapAbsorption ctx hr hreg

/-- **The weakening witness wave 17 → wave 18**: every wave-17 endgame inhabitant
yields a frontier inhabitant, through the absorption de-razoring
(`absorptionResidual_of_endgameResidual`) followed by the frontier relief. -/
def frontierResidual_of_endgameResidual (R : Erdos260EndgameResidual) :
    Erdos260FrontierResidual :=
  frontierResidual_of_absorptionResidual (absorptionResidual_of_endgameResidual R)

/-- Nonempty transport from the wave-17 endgame surface (one direction — honest). -/
theorem nonempty_frontierResidual_of_endgameResidual
    (h : Nonempty Erdos260EndgameResidual) :
    Nonempty Erdos260FrontierResidual :=
  h.elim fun R => ⟨frontierResidual_of_endgameResidual R⟩

/-- Sanity commutation: the wave-17 surface reaches the statement through the
wave-18 frontier route as well. -/
theorem erdos260_of_endgameResidual_via_frontier (R : Erdos260EndgameResidual) :
    Erdos260Statement :=
  (frontierResidual_of_endgameResidual R).toStatement

/-! ## Part 3.  The equivalence chain: one axis, three names -/

/-- **THE VOIDING EQUIVALENCE CHAIN, packaged**: the frontier's `deepOrbitPin` field
is EQUIVALENT to the wave-8 deep fixed-family axis AND to the three v17 capstone
voiding fields — one orbit-pin axis under three names; the wave-18 fold neither
gains nor loses strength at either interface. -/
theorem frontier_voidingEquivalenceChain :
    (DeepOrbitPinVoiding ↔ DeepFixedFamilyVoid)
      ∧ (DeepOrbitPinVoiding
          ↔ ((∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 2)
              ∧ (∀ ctx : ActualFailureContext, ¬ Band3PinnedWide ctx)
              ∧ (∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 4))) :=
  ⟨deepOrbitPinVoiding_iff_deepFixedFamilyVoid, deepOrbitPinVoiding_iff_voidings⟩

/-- The frontier surface carries the wave-8 deep fixed-family axis (through the
single `deepOrbitPin` field alone — no count field is consumed). -/
theorem frontierResidual_deepFixedFamilyVoid (R : Erdos260FrontierResidual) :
    DeepFixedFamilyVoid :=
  deepOrbitPinVoiding_iff_deepFixedFamilyVoid.mp R.deepOrbitPin

/-- The `FixedFamilyShellPersistence` axis stays ABSORBED on the frontier surface
(vacuously, from the deep voiding). -/
theorem frontierResidual_deepShellPersistence (R : Erdos260FrontierResidual) :
    DeepFixedFamilyShellPersistence := fun ctx hdeep hhit =>
  absurd hhit (frontierResidual_deepFixedFamilyVoid R ctx hdeep)

/-! ## Part 4.  The named conditional consumption slots -/

/-- **`deepOrbitPin` from the three named deep value levers** (the cleanest supply):
the dyadic lever kills bands 2 and 3, the fifth/thirds/dyadic levers kill the band-4
trio — no orbit content remains in the field. -/
theorem frontierDeepOrbitPin_of_levers (h1 : DeepDyadicValueLeverPushV2)
    (h5 : DeepTowerFifthValueLever) (h3 : DeepTowerThirdsValueLever) :
    DeepOrbitPinVoiding :=
  deepOrbitPinVoiding_of_levers h1 h5 h3

/-- **`class1Deep` from the per-pair deep atoms + the off-table deep supply**: at a
table datum the atom at its row fires (off-regime forces `T < L`); at an off-table
datum the off-table supply fires.  The per-pair atoms `DstClass1DeepPairAtom` are
the minimal currency of the deep class-1 residual. -/
theorem frontierClass1Deep_of_pairAtoms
    (hatoms : ∀ qv Kv cv bv Tv : ℕ,
      (qv, Kv, cv, bv, Tv) ∈ sreClass1ThresholdTable → DstClass1DeepPairAtom qv Kv Tv)
    (hoff : ∀ ctx : ActualFailureContext,
      (¬ ∃ cv bv Tv : ℕ,
        ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀, cv, bv, Tv)
            ∈ sreClass1ThresholdTable) →
      1274740 ≤ shellLadderDepth ctx → 82 ≤ ctx.n24CarryData.r →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)) :
    ∀ ctx : ActualFailureContext,
      1274740 ≤ shellLadderDepth ctx → 82 ≤ ctx.n24CarryData.r →
      1 ≤ ctx.n24CarryData.r →
      (¬ ∃ cv bv Tv : ℕ,
        ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀, cv, bv, Tv)
            ∈ sreClass1ThresholdTable
          ∧ shellLadderDepth ctx ≤ Tv) →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  intro ctx hL hr82 _ hreg
  by_cases htab : ∃ cv bv Tv : ℕ,
      ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀, cv, bv, Tv)
        ∈ sreClass1ThresholdTable
  · obtain ⟨cv, bv, Tv, hmem⟩ := htab
    rcases Nat.lt_or_ge Tv (shellLadderDepth ctx) with hT | hT
    · exact hatoms _ _ _ _ _ hmem ctx rfl rfl hT (by omega)
    · exact absurd ⟨cv, bv, Tv, hmem, hT⟩ hreg
  · exact hoff ctx htab hL hr82

/-- **`returnGatesFree` from a per-ctx cycle-count certificate** (lever (e) slot): a
certified period `c` with the window regime `(W/c + 1)·b₂ ≤ r + 1` closes the whole
pin-free count gate; a `(q, K₀, c, b₂)` table would slot in here. -/
theorem frontierReturnGatesFree_of_cycleCount
    (h : ∀ ctx : ActualFailureContext, ∃ c, 1 ≤ c ∧
      (∀ m, 1 ≤ m →
        slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
          = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) ∧
      ((supportShell ctx.shell.d ctx.shell.X).card / c + 1)
          * ((Finset.Icc 1 c).filter (fun j =>
              canonGap (class1SlopeDatum ctx).q
                (slopeOrbit (class1SlopeDatum ctx).q
                  (class1SlopeDatum ctx).K₀ j) = 2)).card
        ≤ ctx.n24CarryData.r + 1) :
    ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx :=
  agcReturnGatesFreeField_of_cycleCount h

/-- **`returnInterior` from top-band deviation light** (lever (d) slot): a top-band
deviation budget below the heaviness floor `Y = L/64` closes the field outright
(honest: `agcTopBandDev_le_cap` shows the in-tree ceiling exceeds `Y` — the
hypothesis is a genuine new demand). -/
theorem frontierReturnInterior_of_topBandDevLight
    (h : ∀ ctx : ActualFailureContext,
      fixedFamilyRecurrentBand ctx ≤ 4 ∧ (agcTopBandDev ctx : ℝ) < ctx.n24CarryData.Y) :
    ∀ ctx : ActualFailureContext, ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  agcReturnInteriorField_of_topBandDevLight h

/-- **`densePackInterior` from top-band deviation light** (lever (d) slot, densepack
sibling). -/
theorem frontierDensePackInterior_of_topBandDevLight
    (h : ∀ ctx : ActualFailureContext,
      fixedFamilyRecurrentBand ctx ≤ 4 ∧ (agcTopBandDev ctx : ℝ) < ctx.n24CarryData.Y) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  agcDensePackInteriorField_of_topBandDevLight h

/-! ## Part 5.  The covering lane: the parallel off-cycle endpoint -/

/-- **The covering-family lane, recorded at the capstone** (PARALLEL endpoint, as in
wave 17 — the lane is NOT a frontier surface field; it additionally consumes the
wave-5 lever surfaces): the fixed-cycle stratum of the covering demand is PROVED
pin-free (`certifiedCycleWindow_void` — eventual period `p ≤ 2^19` collides with the
context's own failing shell at every scale, no value pin, no odd-part guard), so the
consumer reduces LOSSLESSLY to the off-cycle stratum
(`coveringFamilies_iff_offCycle`) and only non-pinned aperiodic words can comply
(`offCycleResidual_pinned_flip`). -/
theorem frontier_offCycleParallel (h : OffCycleCoveringSupply)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) :
    Erdos260Statement :=
  erdos260_of_offCycleCovering h surfaces

/-! ## Part 6.  Honest machine-readable status -/

/-- Machine-readable, honest status of the wave-18 frontier capstone. -/
def erdos260FrontierCapstoneStatus : List String :=
  [ "SURFACE (12 fields): Erdos260FrontierResidual = the wave-17 endgame surface " ++
      "rebased on the four wave-18 lanes.  NEW vs wave 17: (a) the THREE orbit-pin " ++
      "voiding fields (returnBand2Void / densePackBand3Void / runBand4Void) are " ++
      "REPLACED by the single deep field deepOrbitPin : DeepOrbitPinVoiding " ++
      "(demanded only at X > 2^986891; the shallow kills at X <= 2^986893 (bands " ++
      "2/3-wide) and X <= 2^986891 (band 4) are PROVED and folded in); (b) " ++
      "class1Deep is demanded only at L >= 1274740 (where r >= 82 is proved) - the " ++
      "parametric width gate dstClass1Absorption_of_depth_le closes EVERY datum at " ++
      "L <= 1274739 = floor(31*2^24/408) (sharp), on top of the 110-pair L <= T " ++
      "relief; (c) towerEnumLow/Tail + runNumericLow/Tail are floor-guarded " ++
      "supplies (L >= 986888 on pinned bands, r >= 63/32, block floors free); (d) " ++
      "class0Mass is the de-razored MASS shape on all three lanes (verbatim " ++
      "wave-18a absorption field).",
    "ENDPOINT (PROVED): erdos260_of_frontierResidual : Erdos260FrontierResidual -> " ++
      "Erdos260Statement, through toAbsorptionResidual + " ++
      "erdos260_of_absorptionResidual + the fully-corrected six-phase ledger.  " ++
      "WEAKENING WITNESSES (PROVED): frontierResidual_of_absorptionResidual and " ++
      "frontierResidual_of_endgameResidual - the frontier surface is never harder " ++
      "than wave 17 or wave 18a; no converse is claimed (the converse IS the " ++
      "wave-18 relief).",
    "EQUIVALENCE CHAIN (PROVED, frontier_voidingEquivalenceChain): " ++
      "DeepOrbitPinVoiding <-> DeepFixedFamilyVoid (wave-8 axis) <-> the three v17 " ++
      "voiding fields - one orbit-pin axis under three names; " ++
      "frontierResidual_deepFixedFamilyVoid / frontierResidual_deepShellPersistence " ++
      "keep the FixedFamilyShellPersistence axis absorbed.",
    "CONSUMPTION SLOTS (PROVED, conditional): frontierDeepOrbitPin_of_levers " ++
      "(DeepDyadicValueLeverPushV2 + fifth + thirds levers supply deepOrbitPin - " ++
      "bands 2/3 from the dyadic lever ALONE); frontierClass1Deep_of_pairAtoms " ++
      "(per-pair DstClass1DeepPairAtom at the table rows + an off-table deep " ++
      "supply); frontierReturnGatesFree_of_cycleCount (a (q,K0,c,b2) certificate " ++
      "table would slot in); frontierReturnInterior_of_topBandDevLight / " ++
      "frontierDensePackInterior_of_topBandDevLight (top-band deviation < Y = " ++
      "L/64; honest: agcTopBandDev_le_cap shows the in-tree ceiling exceeds Y, so " ++
      "the hypothesis is a genuine new demand).",
    "COVERING LANE (PARALLEL, frontier_offCycleParallel): as in wave 17 the " ++
      "covering-family lane is NOT a surface field - it is the parallel endpoint " ++
      "erdos260_of_offCycleCovering, now with the fixed-cycle stratum PROVED " ++
      "pin-free (certifiedCycleWindow_void: eventual period p <= 2^19 collides " ++
      "with the failing shell at every scale) and the consumer reduced LOSSLESSLY " ++
      "to OffCycleCoveringSupply (coveringFamilies_iff_offCycle); pinned words are " ++
      "refuted by the flip (offCycleResidual_pinned_flip), so only non-pinned " ++
      "aperiodic words can comply.",
    "FOLDS SKIPPED (honest): returnGatesFree / returnInterior / " ++
      "densePackCoverFree / densePackDensity / densePackInterior keep the wave-17 " ++
      "shapes - the wave-18 conditional closures are SUPPLY slots, not " ++
      "weakenings: their hypotheses (top-band-dev-light, per-ctx cycle-count " ++
      "certificates) are genuine new demands not implied by the surface.  The " ++
      "class-0 big-order certificate horn stays verbatim inside the mass shape.  " ++
      "The class-0 narrow-support count gate stays open: BOTH sum routes are " ++
      "formally refuted (dstSumRouteBudget_above_cap for class 1; " ++
      "agcClass0DevGate_refuted / agcGenericDevGate_refuted for class 0/3 - the " ++
      "deviation budget is a FLOOR (768/1536)X, factor 24.8 above the (31/1536)X " ++
      "cap).",
    "WHAT REMAINS OPEN AFTER WAVE 18 (the honest core): (a) deepOrbitPin = " ++
      "DeepOrbitPinVoiding at the five fixed data (== the three deep value " ++
      "levers; structural frontier L > 986893 - the dyadic-tail kill is t-FREE so " ++
      "no Q-bound moves it; pressure-relocation misses the phase cap by ~1.3); " ++
      "(b) the per-pair class-1 deep atoms DstClass1DeepPairAtom at L > max(T, " ++
      "1274739), r >= 82 (no b4 = 0 threshold exists: dstBand4Residue_exists at " ++
      "every q >= 64); (c) the class-0 narrow-support count gate at the 19 " ++
      "survivor pairs (both sum routes refuted - genuinely open; survivor bands " ++
      "all in {1,2,3} by agcSurvivorBand_le_four) + the mid/big mass lanes; (d) " ++
      "densePackCoverFree / densePackDensity; (e) the top-band-dev and " ++
      "cycle-count conditional slots (or the verbatim v17 interior/gate fields); " ++
      "(f) the floor-guarded tower/run supplies; (g) OffCycleCoveringSupply over " ++
      "non-pinned aperiodic words (the parallel covering lane).",
    "HYGIENE: additive only - ONE new module; no sorry / admit / new axiom / " ++
      "native_decide; every key declaration passes #print axioms within [propext, " ++
      "Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem erdos260FrontierCapstoneStatus_nonempty :
    erdos260FrontierCapstoneStatus ≠ [] := by
  simp [erdos260FrontierCapstoneStatus]

/-! ## Part 7.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]` or
fewer. -/

#print axioms Erdos260FrontierResidual.toAbsorptionResidual
#print axioms Erdos260FrontierResidual.toStatement
#print axioms erdos260_of_frontierResidual
#print axioms frontierResidual_of_absorptionResidual
#print axioms frontierResidual_of_endgameResidual
#print axioms nonempty_frontierResidual_of_endgameResidual
#print axioms erdos260_of_endgameResidual_via_frontier
#print axioms frontier_voidingEquivalenceChain
#print axioms frontierResidual_deepFixedFamilyVoid
#print axioms frontierResidual_deepShellPersistence
#print axioms frontierDeepOrbitPin_of_levers
#print axioms frontierClass1Deep_of_pairAtoms
#print axioms frontierReturnGatesFree_of_cycleCount
#print axioms frontierReturnInterior_of_topBandDevLight
#print axioms frontierDensePackInterior_of_topBandDevLight
#print axioms frontier_offCycleParallel
#print axioms erdos260FrontierCapstoneStatus_nonempty

end

end Erdos260
