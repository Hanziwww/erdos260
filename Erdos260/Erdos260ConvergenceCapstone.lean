import Erdos260.Erdos260FrontierCapstone
import Erdos260.ExitMassControl
import Erdos260.NarrowSupportGate
import Erdos260.DensePackSlotClosure
import Erdos260.OffCycleCoveringClosure

/-!
# The wave-19 convergence capstone: `Erdos260ConvergenceResidual`

The wave-18 frontier surface (`Erdos260FrontierResidual`) REBASED on the four
wave-19 lanes:

* **`ExitMassControl`** — the 30% sharpening of the heavy-count floor is REFUTED
  with proofs: the count-shaped corrected class row HOLDS as a theorem on the whole
  band `L ≤ 1274739 = ⌊31·2²⁴/408⌋` (`emc_countTimesY_lt_cap`), a firing context is
  forced deep (`emc_fire_forces_deep`, sharp by `emc_threshold_sharp` — the SAME
  constant as the `class1Deep` threshold), and any uniform per-window cap `D0` is
  forced above `~0.5·L·(r+1)` (`emc_uniformCap_floor`).  The M.5/L.3 core is NAMED:
  `ExitMassControlCore` (per-class corrected mass caps `mass₃/₄/₅ ≤ (31/1536)·X` at
  `X > 2^986891`) kills all five pins AT EVERY SCALE through the relocation floors —
  `deepOrbitPinVoiding_of_exitMassControl` supplies the ENTIRE `deepOrbitPin` field.
  HONEST: the core is strictly STRONGER than the field
  (`exitMassControl_iff_split`: core ↔ `DeepOrbitPinVoiding` ∧
  `ExitMassControlOffPin`), so it stays the named SUPPLIER, not a surface field —
  folding it in would harden the surface and lose the v18 weakening.  The core does
  NOT cover `class1Deep` (it caps classes 3/4/5; class 1 is a different routed
  fibre), but its dead zone proves the class-1 count row outright at `L ≤ 1274739`
  (`convergenceClass1Row_shallow`) — both deep lanes start at the same `L ≥ 1274740`.
* **`NarrowSupportGate`** — the class-0 mass field is REPLACED by the three
  per-lane narrow-support gate suppliers (`NarrowSupportClass0Gates`):
  `nsgFrontierClass0Mass_of_gates` rebuilds the EXACT v18 `class0Mass` field.  The
  level-set bound is proved (`nsgLevelSet_count_cap`), the summation route is
  floor-refuted (`nsgLevelSum_route_refuted`), and the surviving per-member gate
  closes the survivor lane on the regime `s·L ≤ 1274739·c` (all 19 pairs at `s = 1`
  over `986876 ≤ L ≤ 2549478`, per pair up to `22945302` —
  `narrowSupportRegimeTable`); the mid lane is pinned to `s = 1`,
  `986876 ≤ L ≤ 1274739`.
* **`DensePackSlotClosure`** — the 128-pair `(q,K₀,c,b₂,b₃)` table `dscPairTable`:
  7 new `b₂ = 0` pairs close `ReturnGatesBodyUngated` outright at ALL X; 35 new
  `b₃ = 0` pairs make the three densepack fields vacuous at the datum.  The five
  return/densepack fields are demanded only OFF the table (`¬ DscReturnB2ZeroDatum`
  / `¬ DscBand3ZeroDatum` guards; the dispatchers `dsc*Field_of_offTable` rebuild
  the exact v18 shapes).  The per-gap top-band route is refuted
  (`dscY_le_perGapCeiling`); the surviving structural slot is `DscTopBandExitFree`
  (no L.3.1 exit in the top band), closing both interior fields
  (`dsc*InteriorField_of_topBandExitFree`).
* **`OffCycleCoveringClosure`** — the covering lane stays PARALLEL (as in waves
  17/18), now in the preferred pinned-split shape: `OffCycleCoveringSupply` ↔
  `DeepPinnedQVoid` ∧ `NonPinnedCoveringSupply`
  (`offCycleCoveringSupply_iff_pinnedSplit` — the demand's own Q-cap supplies the
  flip's t-bound).  The value classification is NOT exhaustive (escape stratum:
  aperiodic words with reduced odd-part denominator `≥ 9`); the endpoint is
  `erdos260_of_pinnedSplitCovering`, packaged here as
  `convergence_pinnedSplitParallel`.

## The surface (12 fields)

`deepOrbitPin` + `towerEnumLow` / `towerEnumTail` / `runNumericLow` /
`runNumericTail` (verbatim v18, floor-guarded) + `returnGatesOffTable` /
`returnInteriorOffTable` (v18 shapes guarded by `¬ DscReturnB2ZeroDatum`) +
`densePackCoverOffTable` / `densePackDensityOffTable` / `densePackInteriorOffTable`
(v18 shapes guarded by `¬ DscBand3ZeroDatum`) + `class0Gates` (the three
narrow-support gate lanes, REPLACING `class0Mass`) + `class1Deep` (verbatim v18).

## The endpoint

`erdos260_of_convergenceResidual` routes through the wave-18 frontier surface:
`toFrontierResidual` rebuilds a full `Erdos260FrontierResidual` (the table data
close the guarded strata; the gates rebuild the mass field) and
`erdos260_of_frontierResidual` finishes through the absorption route and the
fully-corrected six-phase ledger.

## Folds kept / witnesses (honest)

* `exitMassCore` is NOT a surface field: by `exitMassControl_iff_split` it is
  strictly stronger than `deepOrbitPin` (it adds the pin-free caps), so the pair
  `deepOrbitPin` + `class1Deep` stays — the core is the named unified supplier
  (`convergenceDeepOrbitPin_of_exitMassCore`), and the two deep lanes share the
  threshold `1274740 = ⌊31·2²⁴/408⌋ + 1` (`convergence_unifiedDeepCore`).
* The FULL weakening witness `convergenceResidual_of_frontierResidual` does NOT
  hold: the gates leg is a genuine strengthening of the mass cap (a mass bound does
  not bound per-member excess — the `NarrowSupportGate` no-converse note).  The
  honest witness is gates-assisted:
  `convergenceResidual_of_frontierResidual_and_gates` (every OTHER fold is a pure
  weakening — the guards are only dropped).
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The wave-19 convergence surface -/

/-- **The wave-19 convergence capstone surface.**  The wave-18 frontier surface
rebased on the four wave-19 lanes: the class-0 mass field is replaced by the three
narrow-support gate suppliers, the return/densepack fields are demanded only off the
`b₂ = 0` / `b₃ = 0` table strata, the deep pair `deepOrbitPin` + `class1Deep` is
kept with `ExitMassControlCore` as its named unified supplier.  12 fields. -/
structure Erdos260ConvergenceResidual where
  /-- **The single deep orbit-pin voiding** (verbatim v18 field).  NEW unified
  supplier: `ExitMassControlCore` discharges it outright at every deep context
  (`convergenceDeepOrbitPin_of_exitMassCore`); the core is strictly stronger
  (`convergence_exitMassCore_split`), so the FIELD stays the surface demand. -/
  deepOrbitPin : DeepOrbitPinVoiding
  /-- Tower / class 2 - enumerated part (`q < 107`), floor-guarded (verbatim v18). -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
    ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
    986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
    3 ≤ towerSparsityBlock ctx →
    Class2CycleInequality ctx
  /-- Tower / class 2 - tail (`107 ≤ q`), floor-guarded (verbatim v18). -/
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
  floor-guarded (verbatim v18). -/
  runNumericLow : ∀ ctx : ActualFailureContext,
    ¬ OrbitBandPinned ctx 4 →
    (class1SlopeDatum ctx).q < 64 →
    986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 - tail (`64 ≤ q`) on band-4-free contexts, floor-guarded
  (verbatim v18). -/
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
  /-- Return / class 4 count gates, demanded only OFF the `b₂ = 0` table stratum
  (the 7 new pairs `(105,7), (117,1), (117,4), (145,2), (145,72), (155,15),
  (195,19)` are closed outright at ALL X by their kernel cycle certificates —
  `dscReturnCycleCert_of_b2ZeroDatum`).  Off-table the v18 shape is verbatim; the
  named residual is the off-table `b₂ > 0` cycle-count content. -/
  returnGatesOffTable : ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
    ¬ OrbitBandPinned ctx 2 →
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 K.1 interior, demanded only OFF the `b₂ = 0` stratum (there
  the interior holds through fibre emptiness —
  `dscReturnCtxAllFour_of_b2ZeroDatum`).  Conditional supply slot:
  `convergenceReturnInterior_of_topBandExitFree`. -/
  returnInteriorOffTable : ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- DensePack / class 3 corrected K.1.2 Nat-cover, demanded only OFF the `b₃ = 0`
  stratum (at the 35 new pairs the `¬ Class3CycleBand3Free` guard is contradicted —
  `dscClass3CycleBand3Free_of_b3ZeroDatum`).  The open residual = the `b₃ > 0`
  data: the K.1 landing content. -/
  densePackCoverOffTable : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
    ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card
  /-- DensePack / class 3 K.1.1 coarea hit-density, demanded only OFF the `b₃ = 0`
  stratum. -/
  densePackDensityOffTable : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    densePackEndpointDensity ctx
  /-- DensePack / class 3 K.1 active-window interior, demanded only OFF the
  `b₃ = 0` stratum.  Conditional supply slot:
  `convergenceDensePackInterior_of_topBandExitFree`. -/
  densePackInteriorOffTable : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
    ¬ Class3TopBandCycleFree ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card
  /-- **The three narrow-support class-0 gate lanes** (REPLACES the v18 `class0Mass`
  field): per-lane gate levels with their closing regimes — survivor
  `s·L ≤ 1274739·c` (all 19 pairs close at `s = 1` on
  `986876 ≤ L ≤ 1274739·c`), mid `s·L ≤ 1274739` (pinned to `s = 1`,
  `986876 ≤ L ≤ 1274739`), big-order horn OR generic gate.
  `nsgFrontierClass0Mass_of_gates` rebuilds the EXACT v18 field; the open content is
  the gates at deep regimes.  Weakening witness from wave-16 emptiness:
  `nsgGates_of_fibreEmpty` (gates at `s = 0`). -/
  class0Gates : NarrowSupportClass0Gates
  /-- **The deep-shell class-1 field** (verbatim v18): demanded only at
  `L ≥ 1274740` — the SAME constant `⌊31·2²⁴/408⌋ + 1` as the exit-mass firing
  threshold (`emc_threshold_sharp`); below it the class-1 count row is now a
  THEOREM (`convergenceClass1Row_shallow`).  NOT covered by `ExitMassControlCore`
  (the core caps classes 3/4/5) — the two deep lanes should be attacked together at
  `L ≥ 1274740`. -/
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

namespace Erdos260ConvergenceResidual

/-! ### The rebuild: convergence → wave-18 frontier surface -/

/-- **The convergence surface rebuilds the full wave-18 frontier surface**: the
`b₂ = 0` stratum of the return gates closes through the kernel cycle certificates,
the `b₃ = 0` strata of the densepack fields through the band-3-freeness
contradictions, the class-0 mass field through the narrow-support gates.
Composition only (plus the table dispatchers). -/
def toFrontierResidual (R : Erdos260ConvergenceResidual) : Erdos260FrontierResidual where
  deepOrbitPin := R.deepOrbitPin
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGatesFree := fun ctx hpin hfree hone hnum => by
    by_cases hz : DscReturnB2ZeroDatum ctx
    · obtain ⟨c, hc, hper, hcount⟩ := dscReturnCycleCert_of_b2ZeroDatum ctx hz
      exact agcReturnGatesUngated_of_cycleCount_ceil ctx hc hper hcount
    · exact R.returnGatesOffTable ctx hz hpin hfree hone hnum
  returnInterior := dscReturnInteriorField_of_offTable R.returnInteriorOffTable
  densePackCoverFree := dscDensePackCoverFreeField_of_offTable R.densePackCoverOffTable
  densePackDensity := dscDensePackDensityField_of_offTable R.densePackDensityOffTable
  densePackInterior := dscDensePackInteriorField_of_offTable R.densePackInteriorOffTable
  class0Mass := nsgFrontierClass0Mass_of_gates R.class0Gates
  class1Deep := R.class1Deep

/-- The final statement from the wave-19 convergence surface, through the frontier
and absorption routes and the fully-corrected six-phase ledger. -/
theorem toStatement (R : Erdos260ConvergenceResidual) : Erdos260Statement :=
  R.toFrontierResidual.toStatement

end Erdos260ConvergenceResidual

/-- **THE WAVE-19 ENDPOINT**: `Erdos260Statement` from the folded 12-field
convergence surface — the class-0 mass lanes replaced by the narrow-support gates,
the return/densepack lanes relieved of the `b₂ = 0` / `b₃ = 0` table strata, the
deep pair kept with the exit-mass core as its named unified supplier.  Public
bridges only. -/
theorem erdos260_of_convergenceResidual (R : Erdos260ConvergenceResidual) :
    Erdos260Statement :=
  R.toStatement

/-! ## Part 2.  The weakening witness (honest: gates-assisted)

The FULL witness `Erdos260FrontierResidual → Erdos260ConvergenceResidual` does NOT
hold: the gates leg genuinely strengthens the class-0 lane (a routed-mass cap does
not bound any per-member excess — the `NarrowSupportGate` no-converse note), and no
trivial gate level lands in the closing regimes (`nsgTrivialGate_regime_disjoint`).
Every OTHER fold is a pure weakening: the new guards are simply dropped. -/

/-- **The gates-assisted weakening witness**: a wave-18 frontier inhabitant plus the
narrow-support gate data yields a convergence inhabitant — all non-class-0 fields
transport by dropping the new `¬ Dsc*ZeroDatum` guards.  One direction only; NO
converse is claimed. -/
def convergenceResidual_of_frontierResidual_and_gates
    (R : Erdos260FrontierResidual) (G : NarrowSupportClass0Gates) :
    Erdos260ConvergenceResidual where
  deepOrbitPin := R.deepOrbitPin
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGatesOffTable := fun ctx _ => R.returnGatesFree ctx
  returnInteriorOffTable := fun ctx _ => R.returnInterior ctx
  densePackCoverOffTable := fun ctx _ => R.densePackCoverFree ctx
  densePackDensityOffTable := fun ctx _ => R.densePackDensity ctx
  densePackInteriorOffTable := fun ctx _ => R.densePackInterior ctx
  class0Gates := G
  class1Deep := R.class1Deep

/-- Sanity commutation: a wave-18 inhabitant (with gates) reaches the statement
through the wave-19 convergence route as well. -/
theorem erdos260_of_frontierResidual_via_convergence
    (R : Erdos260FrontierResidual) (G : NarrowSupportClass0Gates) :
    Erdos260Statement :=
  (convergenceResidual_of_frontierResidual_and_gates R G).toStatement

/-! ## Part 3.  The unified deep core -/

/-- **`deepOrbitPin` from the M.5/L.3 exit-mass core** (the wave-19 unified
supplier): the per-class corrected mass caps kill all five pins at every deep
context through the relocation floors — no scale hypothesis, no r-floor, no Q-bound
consumed. -/
theorem convergenceDeepOrbitPin_of_exitMassCore (h : ExitMassControlCore) :
    DeepOrbitPinVoiding :=
  deepOrbitPinVoiding_of_exitMassControl h

/-- **The exact relation (no free lunch)**: the exit-mass core is EQUIVALENT to the
deep orbit-pin voiding PLUS the caps on pin-free deep contexts — supplying the core
is never cheaper than voiding the pins; its honest content beyond the axis is
exactly the pin-free conjunct.  This is why the core stays a SUPPLIER and not a
surface field. -/
theorem convergence_exitMassCore_split :
    ExitMassControlCore ↔ (DeepOrbitPinVoiding ∧ ExitMassControlOffPin) :=
  exitMassControl_iff_split

/-- **The class-1 shallow row is a THEOREM** (the exit-mass dead zone read at the
class-1 fibre): on the whole band `L ≤ 1274739` the class-1 count-cap row holds
outright — exactly the `class1Deep` relief band, with the SAME sharp constant
`⌊31·2²⁴/408⌋` (`emc_threshold_sharp`). -/
theorem convergenceClass1Row_shallow (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 1274739) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have h := emc_fibre_countTimesY_lt_cap ctx 1 hL
  rw [emcCap_eq_corrected ctx] at h
  exact h.le

/-- **THE UNIFIED-DEEP-CORE THEOREM**: the exit-mass core kills the orbit-pin lane
ENTIRELY (every scale, all five pins) and the class-1 lane's WHOLE shallow part
(`L ≤ 1274739`, where the row is in fact unconditional) — both deep lanes start at
the same `L ≥ 1274740 = ⌊31·2²⁴/408⌋ + 1`.  HONEST: the core does NOT supply the
deep class-1 cap itself (class 1 is not among the capped classes 3/4/5);
`class1Deep` stays a separate field, demanded exactly where the dead zone ends. -/
theorem convergence_unifiedDeepCore (h : ExitMassControlCore) :
    DeepOrbitPinVoiding ∧
      (∀ ctx : ActualFailureContext, shellLadderDepth ctx ≤ 1274739 →
        ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
            * ctx.n24CarryData.Y
          ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)) :=
  ⟨deepOrbitPinVoiding_of_exitMassControl h,
    fun ctx hL => convergenceClass1Row_shallow ctx hL⟩

/-! ## Part 4.  The named conditional consumption slots -/

/-- **`returnInteriorOffTable` from top-band exit-freeness** (the surviving lever-(d)
slot after the per-gap refutation `dscY_le_perGapCeiling`): exit-freeness of the
top band collapses the deviation mass to zero and closes the interior outright. -/
theorem convergenceReturnInterior_of_topBandExitFree
    (h : ∀ ctx : ActualFailureContext,
      fixedFamilyRecurrentBand ctx ≤ 4 ∧ DscTopBandExitFree ctx) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  fun ctx _ => dscReturnInteriorField_of_topBandExitFree h ctx

/-- **`densePackInteriorOffTable` from top-band exit-freeness** (densepack
sibling). -/
theorem convergenceDensePackInterior_of_topBandExitFree
    (h : ∀ ctx : ActualFailureContext,
      fixedFamilyRecurrentBand ctx ≤ 4 ∧ DscTopBandExitFree ctx) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  fun ctx _ => dscDensePackInteriorField_of_topBandExitFree h ctx

/-! ## Part 5.  The covering lane: the parallel pinned-split endpoint -/

/-- **The covering-family lane, recorded at the capstone** (PARALLEL endpoint, as in
waves 17/18 — the lane is NOT a surface field): the wave-19 preferred shape is the
LOSSLESS pinned split (`offCycleCoveringSupply_iff_pinnedSplit`) — the pinned-Q
voiding `DeepPinnedQVoid` (forced by the demand's own Q-cap,
`coveringDemand_pinned_void`) plus the construction `NonPinnedCoveringSupply` on
the escape stratum (aperiodic words with reduced odd-part denominator `≥ 9`, which
the in-tree value classification does NOT cover).  Difficulty floor: the supply
implies all three open deep value levers
(`offCycleCovering_forces_deepValueLevers`). -/
theorem convergence_pinnedSplitParallel (hvoid : DeepPinnedQVoid)
    (hsup : NonPinnedCoveringSupply)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) :
    Erdos260Statement :=
  erdos260_of_pinnedSplitCovering hvoid hsup surfaces

/-! ## Part 6.  Honest machine-readable status -/

/-- Machine-readable, honest status of the wave-19 convergence capstone. -/
def erdos260ConvergenceCapstoneStatus : List String :=
  [ "SURFACE (12 fields): Erdos260ConvergenceResidual = the wave-18 frontier " ++
      "surface rebased on the four wave-19 lanes.  NEW vs wave 18: (a) class0Mass " ++
      "is REPLACED by class0Gates : NarrowSupportClass0Gates - the three per-lane " ++
      "narrow-support gate suppliers (survivor regime s*L <= 1274739*c, all 19 " ++
      "pairs closed at s = 1 on [986876, 1274739*c], per pair up to 22945302; mid " ++
      "lane pinned to s = 1, 986876 <= L <= 1274739; big lane keeps the order " ++
      "horn) - nsgFrontierClass0Mass_of_gates rebuilds the exact v18 field; (b) " ++
      "returnGatesFree / returnInterior are demanded only OFF the 7-pair b2 = 0 " ++
      "stratum ((105,7),(117,1),(117,4),(145,2),(145,72),(155,15),(195,19) close " ++
      "ReturnGatesBodyUngated outright at ALL X via kernel cycle certificates); " ++
      "(c) the three densepack fields are demanded only OFF the 35-pair b3 = 0 " ++
      "stratum (band-3-freeness contradicts the guards - vacuous at the datum); " ++
      "(d) deepOrbitPin + class1Deep KEPT as the v18 pair (honest: " ++
      "ExitMassControlCore is strictly stronger than deepOrbitPin by " ++
      "exitMassControl_iff_split, so folding it in would harden the surface); " ++
      "(e) towerEnumLow/Tail + runNumericLow/Tail verbatim v18 floor-guarded " ++
      "supplies.",
    "ENDPOINT (PROVED): erdos260_of_convergenceResidual : " ++
      "Erdos260ConvergenceResidual -> Erdos260Statement, through " ++
      "toFrontierResidual + erdos260_of_frontierResidual + the absorption route " ++
      "and the fully-corrected six-phase ledger.  WEAKENING WITNESS (HONEST, " ++
      "gates-assisted): convergenceResidual_of_frontierResidual_and_gates - the " ++
      "FULL witness does NOT hold because the gates leg genuinely strengthens the " ++
      "class-0 lane (a routed-mass cap does not bound per-member excess; no " ++
      "trivial gate level lands in the closing regimes, " ++
      "nsgTrivialGate_regime_disjoint); every other fold is a pure weakening " ++
      "(guards dropped).",
    "THE UNIFIED DEEP CORE (PROVED): ExitMassControlCore (per-class corrected " ++
      "mass caps mass3/4/5 <= (31/1536)*X at X > 2^986891 - THE named M.5/L.3 " ++
      "content) supplies the ENTIRE deepOrbitPin field at every scale through the " ++
      "relocation floors (convergenceDeepOrbitPin_of_exitMassCore), and its dead " ++
      "zone makes the class-1 count row a THEOREM on the whole band L <= 1274739 " ++
      "(convergenceClass1Row_shallow) - both deep lanes start at the same L >= " ++
      "1274740 = floor(31*2^24/408) + 1 (emc_threshold_sharp).  HONEST " ++
      "(convergence_unifiedDeepCore): the core does NOT supply the deep class-1 " ++
      "cap itself - class 1 is not among the capped classes 3/4/5 - so class1Deep " ++
      "stays a separate field, demanded exactly where the dead zone ends; the two " ++
      "deep lanes should be attacked TOGETHER at L >= 1274740.",
    "THE 30% SHARPENING - REFUTED WITH PROOFS (ExitMassControl): the count-shaped " ++
      "lever needs the heavy count above (31/24)*X/L, but the support cap W < " ++
      "(17/2^24)*X bounds it for every L <= 1274739 (emc_countTimesY_lt_cap, all " ++
      "routed fibres); a firing context is deep (emc_fire_forces_deep, sharp); " ++
      "any uniform per-window cap D0 is forced above ~0.5*L*(r+1) " ++
      "(emc_uniformCap_floor) - the hoped 0.38*L*(r+1) cap is contradicted by the " ++
      "context itself.  The 1.3 factor is STRUCTURAL: 31*2^24/408 / 986894 = " ++
      "1.2917; no sharpening fires below 1274740.",
    "CONSUMPTION SLOTS (PROVED, conditional): " ++
      "convergenceReturnInterior_of_topBandExitFree / " ++
      "convergenceDensePackInterior_of_topBandExitFree (DscTopBandExitFree - no " ++
      "L.3.1 exit in the top band - collapses agcTopBandDev to 0 < Y; the per-gap " ++
      "route is REFUTED: dscY_le_perGapCeiling, one exit can swamp the floor); " ++
      "nsgGates_of_fibreEmpty (wave-16 per-lane emptiness supplies the gates at " ++
      "s = 0); frontierDeepOrbitPin_of_levers and frontierClass1Deep_of_pairAtoms " ++
      "remain live on the kept v18 pair.",
    "COVERING LANE (PARALLEL, convergence_pinnedSplitParallel): the wave-19 " ++
      "preferred endpoint shape is the LOSSLESS pinned split " ++
      "(offCycleCoveringSupply_iff_pinnedSplit): OffCycleCoveringSupply <-> " ++
      "DeepPinnedQVoid (forced by the demand's own Q-cap - " ++
      "coveringDemand_pinned_void) AND NonPinnedCoveringSupply (the construction " ++
      "demanded only on the escape stratum: aperiodic words with reduced odd-part " ++
      "denominator >= 9, NOT covered by the in-tree value classification - the " ++
      "manuscript's Appendix N descent is the intended route).  Difficulty floor: " ++
      "the supply implies all three open deep value levers " ++
      "(offCycleCovering_forces_deepValueLevers).",
    "FOLDS SKIPPED (honest): exitMassCore is NOT a surface field (it would " ++
      "strictly harden the surface - exitMassControl_iff_split); the class-0 " ++
      "gates fold breaks the unaided weakening witness (named above); the " ++
      "DscTopBandExitFree slot is NOT folded into the interior fields (genuine " ++
      "new content - the in-tree deviation ceiling exceeds Y, " ++
      "dscTopBandDevCeiling_ge_Y); the densepack cover/density fields keep the " ++
      "v18 inequality shapes off-table (the b3 > 0 cover/density content = the " ++
      "K.1 landing - the L-spacing hunt came back negative).",
    "WHAT REMAINS OPEN AFTER WAVE 19 (the honest core): (a) ExitMassControlCore " ++
      "- the single deep atom (= the unique L.3/M.5 route; kills deepOrbitPin " ++
      "entirely; its content beyond the axis is the pin-free caps); (b) the " ++
      "per-pair class-1 deep atoms at L > max(T, 1274739), r >= 82; (c) " ++
      "NarrowSupportClass0Gates at deep regimes (survivor s*L > 1274739*c, mid/ " ++
      "generic s*L > 1274739 - all 19 survivor pairs and the mid band are CLOSED " ++
      "below); (d) the K.1 landing: densepack cover/density at b3 > 0 data; (e) " ++
      "DscTopBandExitFree or the verbatim interior demands off-table; (f) the " ++
      "floor-guarded tower/run supplies; (g) the covering lane: " ++
      "NonPinnedCoveringSupply on the escape stratum (odd-part >= 9) + " ++
      "DeepPinnedQVoid (the forced voiding obligation).",
    "HYGIENE: additive only - ONE new module; no sorry / admit / new axiom / " ++
      "native_decide; every key declaration passes #print axioms within " ++
      "[propext, Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem erdos260ConvergenceCapstoneStatus_nonempty :
    erdos260ConvergenceCapstoneStatus ≠ [] := by
  simp [erdos260ConvergenceCapstoneStatus]

/-! ## Part 7.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]` or
fewer. -/

#print axioms Erdos260ConvergenceResidual.toFrontierResidual
#print axioms Erdos260ConvergenceResidual.toStatement
#print axioms erdos260_of_convergenceResidual
#print axioms convergenceResidual_of_frontierResidual_and_gates
#print axioms erdos260_of_frontierResidual_via_convergence
#print axioms convergenceDeepOrbitPin_of_exitMassCore
#print axioms convergence_exitMassCore_split
#print axioms convergenceClass1Row_shallow
#print axioms convergence_unifiedDeepCore
#print axioms convergenceReturnInterior_of_topBandExitFree
#print axioms convergenceDensePackInterior_of_topBandExitFree
#print axioms convergence_pinnedSplitParallel
#print axioms erdos260ConvergenceCapstoneStatus_nonempty

end

end Erdos260
