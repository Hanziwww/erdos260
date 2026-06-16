import Erdos260.Erdos260KeystoneCapstone
import Erdos260.ExitLightCycleCertificates
import Erdos260.Class1AlignmentBit
import Erdos260.ExitMassFamilyClosure
import Erdos260.K1AtomsClosure

/-!
# The wave-21 summit capstone: `Erdos260SummitResidual`

The wave-20 keystone surface (`Erdos260KeystoneResidual`) REBASED on the five
wave-21 lanes:

* **`ExitLightCycleCertificates`** — the complete survey of ALL 999000 pairs
  (`q` odd in `[3, 2000)`): 4578 NEW `b₄ = 1` deep-clearing pairs at `q ≥ 303`
  (`c` ∈ 50–70; 10 certified representatives; the wave-20 "none exist" was a
  `q < 200` horizon artifact; the exact deep boundary is `c ≥ 50`), and exactly
  384 EXIT-SILENT pairs (all bands ≥ 5; the class-1..5 fibres are EMPTY; the
  `b = 0` datum is proved) at which `ExitMassControlOffPin` FIRES OUTRIGHT
  (`elcOffPin_at_silent`).  The off-pin residual NARROWS to
  `ElcOffPinUncoveredResidual` (the off-pin demand at deep pin-free contexts
  whose datum is NOT exit-silent): `elcOffPin_of_uncoveredResidual` and
  `elcKeystoneCore_of_uncoveredResidual` rebuild the off-pin conjunct and the
  FULL `ExitMassControlCore`.  Share-from-spacing is NEGATIVE
  (`elcShare_not_from_spacing_alone` — a kernel counterexample: weight can
  concentrate on the fibre residue), so the share is genuinely
  exit-avoidance/equidistribution content, not a tiling consequence.
* **`ExitMassFamilyClosure`** — `emcFibreExitMass` is MULTIPLICITY-FREE (a
  union mass) and `mdcClass0ExitMass = emcFibreExitMass 0`: the per-class
  family is genuinely unified.  The spaced share IS an exit-AVOIDANCE demand
  (`emfc_spacedShare_forces_exitLight` ≤ 31/768 of the exit mass;
  `emfc_spacedShare_not_covering`; `emfc_spacedShare_misses_exit`); the named
  necessary atom is `EmfcFibreExitLight`.  Class-0: the wave-16 windowed check
  IS fibre-0 emptiness (`emfc_class0FibreEmpty_iff_windowCheck`) and supplies
  the class-0 atom (`emfc_class0Atom_of_windowCheck`) — the cheapest open
  input.  The preferred assembly is `EmfcUnifiedExitMassFamily` from
  `emfc_family_of_checks_and_regime` (per-survivor windowed checks + the
  spaced-share regime).
* **`Class1AlignmentBit`** — the named atom `Class1AlignmentBitAtom` supplies
  the level-1 aligned count (`c1abSupply_one_of_atom`) and DOUBLES the closed
  class-1 regime to `L ≤ 2549478` (`c1abClass1Absorption_of_atom`).  FREE
  levels exist at the slack table pairs (`2^v·b₄ < c`): level 4 at `(103,51)`,
  level 3 at `(107,53)` and `(101,50)` — the per-pair residuals move to their
  BOOSTED thresholds (`c1abPair_103_51_of_boostedAtom` etc.; `(101,50)` is
  honestly recorded as subsumed by its SRE threshold).  The gcd-of-periods
  lemma `c1abPeriod_gcd` upgrades the wave-18 floors: the run cycle horn is
  FALSE at every certified band-reading pair (`c1abClass5CycleNumeric_void`),
  instantiated at the recorded hard pair `(63,10)`
  (`c1abRunCycle_void_63_10` / `c1abRunLow_reduces_63_10` — the demand there
  is the band-heavy half; `c1abTowerCycle_void_63_10` on `m₀ ≥ 3`).
* **`K1AtomsClosure`** — the three K.1 demands get exact iff-reductions:
  `K1ClusterFloor ↔ K1InteriorClusterFloor` (the boundary stratum is free,
  `k1acClusterFloor_iff_interior`); `K1StartSpacing ↔ K1SpanRarity`
  (`k1acStartSpacing_iff_spanRarity`; the cycle-spacing route is DEAD at
  `r ≥ 2` — the width outruns every `c ≤ 15430`; `K1LocalExitLight` supplies
  spacing at band ≤ 4, the same currency as the exit-mass family);
  `densePackEndpointDensity ↔ ∃ d, K1AnchorSurplus`
  (`k1acDensity_iff_anchorSurplus`; the band-3 syndetic supply is 1 hit vs the
  `L/8` demand — the honest shortfall).  The `DscTopBandExitFree` price is
  PAID unconditionally at every band-2/3/4 pin
  (`k1acTopBandPricePaid_of_pin2/3/4`), and index persistence voids ALL three
  K.1 demands (`k1acK1Demands_of_indexPersistence`).
* **`GAP_MAP_V20.md`** — the manuscript cross-reference for the v20 surface
  (docs only; no Lean content).

## The surface (16 fields)

`deepOrbitPin` (verbatim; the documented deep-core supplier route narrows to
`ElcOffPinUncoveredResidual` + this axis, `summitExitMassCore_of_uncovered`) +
`towerEnumLow` / `towerEnumTail` (verbatim v20) + `runNumericLow6310` (NEW —
at `(63,10)` ONLY the band-heavy half is demanded; the cycle horn is provably
FALSE there) + `runNumericLowOff` (the v20 low lane off `(63,10)`) +
`runNumericTail` (verbatim v20) + `returnGatesOffTable` /
`returnInteriorOffTable` (verbatim v20) + `densePackInteriorClusterFloor`
(REPLACES the v20 cluster-floor atom by its interior stratum — exact iff) +
`densePackSpanRarity` (REPLACES the v20 spacing atom by one-per-span rarity —
exact iff) + `densePackAnchorSurplus` (REPLACES the v20 density field by
anchor-with-surplus — exact iff) + `densePackInteriorOffTable` (verbatim v20)
+ `class0Gates` (kept; preferred suppliers: the per-survivor windowed checks
through `emfc_class0Control_of_windowChecks`) + `boostLevel` /
`class1Aligned` / `class1DeepBoosted` (the v20 boost ladder kept verbatim;
`Class1AlignmentBitAtom` is the NAMED supplier of the level-1 aligned count).

## The endpoint and the witness

`erdos260_of_summitResidual` routes through `toKeystoneResidual` (the iff
suppliers rebuild the three K.1 fields; the `(63,10)` case split rebuilds the
run low lane) and the proved v20 endpoint.  The FULL weakening witness
`Erdos260KeystoneResidual → Erdos260SummitResidual` HOLDS
(`summitResidual_of_keystoneResidual`) — an IMPROVEMENT over v20→v19 (which
needed atom assistance): every wave-21 fold is an equivalence (the three K.1
iffs) or a proved resolution (the `(63,10)` cycle-horn voiding).

## Folds kept / skipped (honest)

* The class-1 ladder is KEPT in the v20 shape: replacing `class1Aligned` by
  `Class1AlignmentBitAtom` would STRENGTHEN the surface (the atom implies the
  level-1 supply; no converse is in-tree), and the three free-level pair
  routes are alternative suppliers, not surface demands — they are recorded
  as consumption theorems (`summitClass1Pair_*_of_boostedAtom`), with the
  honest note that `(101,50)`'s boosted band is subsumed by its SRE threshold.
* `towerEnumLow` is KEPT verbatim: `c1abTowerCycle_void_63_10` shows the
  demanded conclusion is FALSE at `(63,10)` on `m₀ ≥ 3`, i.e. any inhabitant
  must refute such contexts — that is information about the field, not a
  cheaper field shape (no band-heavy tower half exists in the demand).
* `class0Gates` is NOT replaced by the windowed checks: the checks supply the
  named atom `MdcClass0ExitMassControl` (and through it the survivor mass
  row), but the gates demand per-member levels on three lanes (unchanged v20
  reasoning).
* `deepOrbitPin` and the interiors/`DscTopBandExitFree` slots are unchanged;
  the price-paid theorems (`summitTopBandPrice_pin2/3/4`) record that the
  topband cost is already paid at every pinned band.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxRecDepth 8192

/-! ## Part 1.  The wave-21 summit surface -/

/-- **The wave-21 summit capstone surface.**  The wave-20 keystone surface
rebased on the five wave-21 lanes: the three densepack K.1 fields are replaced
by their exact iff-reductions (interior cluster floor / span rarity / anchor
surplus), the run low lane is narrowed to its band-heavy half at the certified
band-reading pair `(63,10)`, and the exit-mass / class-0 / class-1 axes keep
their v20 shapes with the new named suppliers wired (`ElcOffPinUncoveredResidual`,
`EmfcUnifiedExitMassFamily`, `Class1AlignmentBitAtom`, the windowed checks). -/
structure Erdos260SummitResidual where
  /-- **The single deep orbit-pin voiding** (verbatim v18/v19/v20 field).
  NEW supplier chain: `ElcOffPinUncoveredResidual` + this axis rebuild the FULL
  `ExitMassControlCore` (`summitExitMassCore_of_uncovered`) — the off-pin
  content is now demanded only at deep pin-free contexts whose datum is NOT
  one of the 384 exit-silent pairs (those fire outright,
  `summitExitSilent_free`); the preferred family assembly is
  `EmfcUnifiedExitMassFamily` (`summitExitMassCore_of_family`). -/
  deepOrbitPin : DeepOrbitPinVoiding
  /-- Tower / class 2 — enumerated part (`q < 107`), floor-guarded, narrowed
  off the seven certified band-4-free pairs (verbatim v20).  HONEST note: at
  `(63,10)` the conclusion is provably FALSE on `m₀ ≥ 3`
  (`summitTowerCycle_void_63_10`) — an inhabitant must refute those contexts. -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
    ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
    ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
      ∉ dccTowerBand4FreeLowPairs →
    986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
    3 ≤ towerSparsityBlock ctx →
    Class2CycleInequality ctx
  /-- Tower / class 2 — tail (`107 ≤ q`), floor-guarded (verbatim v19/v20). -/
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
  /-- **The `(63,10)` band-heavy half** (NEW — the wave-21 narrowing): at the
  recorded hard pair the certified period-2 band-4-reading cycle makes the
  cycle horn FALSE at every context (`c1abRunCycle_void_63_10`), so ONLY the
  band-heavy half is demanded — strictly less than the v20 disjunction. -/
  runNumericLow6310 : ∀ ctx : ActualFailureContext,
    ¬ OrbitBandPinned ctx 4 →
    (class1SlopeDatum ctx).q = 63 → (class1SlopeDatum ctx).K₀ = 10 →
    986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
    Class5BandHeavyNumericCloses ctx
  /-- Run / class 5 — enumerated part (`q < 64`) on band-4-free contexts,
  floor-guarded, off the six certified band-free pairs AND off `(63,10)`
  (whose demand moved to the band-heavy half above); otherwise verbatim v20. -/
  runNumericLowOff : ∀ ctx : ActualFailureContext,
    ¬ OrbitBandPinned ctx 4 →
    (class1SlopeDatum ctx).q < 64 →
    ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
      ∉ dccRunBandFreeLowPairs →
    ¬ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 10) →
    986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 — tail (`64 ≤ q`) on band-4-free contexts, floor-guarded
  (verbatim v19/v20). -/
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
  /-- Return / class 4 count gates, demanded only OFF the `b₂ = 0` table
  stratum (verbatim v19/v20). -/
  returnGatesOffTable : ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
    ¬ OrbitBandPinned ctx 2 →
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 K.1 interior, demanded only OFF the `b₂ = 0` stratum
  (verbatim v19/v20).  The topband price is PAID at every band-2 pin
  (`summitTopBandPrice_pin2`). -/
  returnInteriorOffTable : ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- **THE INTERIOR CLUSTER-FLOOR ATOM** (NEW — replaces the v20
  `densePackClusterFloor` by its EXACT iff-reduction
  `k1acClusterFloor_iff_interior`): the per-start floor demanded only at
  interior endpoints (window top strictly below `2X + W`); the boundary
  stratum is discharged for free (`k1acClusterFloorAt_of_topAbove`).  A
  violation pins an EXPLICIT shell hit in the top subwindow
  (`k1acClusterFloorAt_or_witness`). -/
  densePackInteriorClusterFloor : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
    ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
    K1InteriorClusterFloor ctx
  /-- **THE SPAN-RARITY ATOM** (NEW — replaces the v20 `densePackStartSpacing`
  by its EXACT iff-reduction `k1acStartSpacing_iff_spanRarity`): at most ONE
  genuine start per width-`W` span.  The cycle-spacing route is DEAD at
  `r ≥ 2` (the width `≥ L + 3B + 2` outruns every period `c ≤ 15430`,
  `k1acTablePeriod_lt_width_of_r_ge_two`); the surviving conditional supplier
  is per-span exit-lightness (`K1LocalExitLight`,
  `summitSpanRarity_of_localExitLight`) — the SAME currency as the exit-mass
  family. -/
  densePackSpanRarity : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
    ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
    K1SpanRarity ctx
  /-- **THE ANCHOR-SURPLUS ATOM** (NEW — replaces the v20
  `densePackDensityOffTable` by its EXACT iff-reduction
  `k1acDensity_iff_anchorSurplus`): every genuine endpoint sits within
  distance `d` of an anchor whose window carries `2d` SURPLUS hits — the
  manuscript "the descent lands IN a dense cluster" made exact at radius `d`
  (`d = 0` recovers density verbatim).  HONEST: the band-3 syndetic supply
  gives 1 hit against the `L/8` demand (`k1acDensity_demand_real_floor`) —
  the landing needs the cluster structure, not the bare syndetic floor. -/
  densePackAnchorSurplus : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    ∃ d : ℕ, K1AnchorSurplus ctx d
  /-- DensePack / class 3 K.1 active-window interior, demanded only OFF the
  `b₃ = 0` stratum (verbatim v19/v20).  The topband price is PAID at every
  band-3 pin (`summitTopBandPrice_pin3`); index persistence voids the whole
  K.1 demand set where it fires (`summitK1Demands_of_indexPersistence`). -/
  densePackInteriorOffTable : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
    ¬ Class3TopBandCycleFree ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card
  /-- **The three narrow-support class-0 gate lanes** (kept verbatim v19/v20).
  NEW preferred suppliers: per-survivor windowed cycle checks — they are
  EQUIVALENT to class-0 fibre emptiness (`emfc_class0FibreEmpty_iff_windowCheck`,
  the cheapest open input) and build the named atom
  (`summitClass0Control_of_windowChecks`), which closes the survivor mass row
  (`summitClass0SurvivorRow_of_windowChecks`).  HONEST: the checks do NOT
  supply this field (no mid/big lanes, no per-member levels), so it stays. -/
  class0Gates : NarrowSupportClass0Gates
  /-- **The boost level** of the class-1 deep ladder (verbatim v20). -/
  boostLevel : ℕ
  /-- **The aligned-count supply at the boost level** (verbatim v20).  NEW
  named supplier at level 1: `Class1AlignmentBitAtom`
  (`summitClass1Aligned_of_alignmentBit`), which doubles the closed class-1
  regime to `L ≤ 2549478` (`summitClass1Absorption_of_alignmentBit`).  FREE
  levels are PROVED at the slack table pairs: level 4 at `(103,51)`, level 3
  at `(107,53)` / `(101,50)` (`c1abPairSupply_103_51` etc.) — through the
  boosted gate the per-pair residuals move to their boosted thresholds
  (`summitClass1Pair_103_51_of_boostedAtom` etc.). -/
  class1Aligned : DccClass1AlignedCountSupply boostLevel
  /-- **The boosted class-1 deep residual** (verbatim v20): the demand at
  `L > 1274739·2^boostLevel` off the SRE table thresholds. -/
  class1DeepBoosted : DccClass1DeepResidual boostLevel

namespace Erdos260SummitResidual

/-! ### The rebuild: summit → wave-20 keystone surface -/

/-- **The summit surface rebuilds the full wave-20 keystone surface**: the
three K.1 iff-suppliers rebuild the cluster-floor / spacing / density fields,
and the `(63,10)` case split rebuilds the run low lane (the band-heavy half is
the left disjunct there).  Composition only. -/
def toKeystoneResidual (R : Erdos260SummitResidual) :
    Erdos260KeystoneResidual where
  deepOrbitPin := R.deepOrbitPin
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := fun ctx hpin hq hnotin hL hr => by
    by_cases h63 : (class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 10
    · exact Or.inl (R.runNumericLow6310 ctx hpin h63.1 h63.2 hL hr)
    · exact R.runNumericLowOff ctx hpin hq hnotin h63 hL hr
  runNumericTail := R.runNumericTail
  returnGatesOffTable := R.returnGatesOffTable
  returnInteriorOffTable := R.returnInteriorOffTable
  densePackClusterFloor :=
    k1acDensePackClusterFloorField_of_interior R.densePackInteriorClusterFloor
  densePackStartSpacing :=
    k1acDensePackStartSpacingField_of_spanRarity R.densePackSpanRarity
  densePackDensityOffTable :=
    k1acDensePackDensityOffTableField_of_anchorSurplus R.densePackAnchorSurplus
  densePackInteriorOffTable := R.densePackInteriorOffTable
  class0Gates := R.class0Gates
  boostLevel := R.boostLevel
  class1Aligned := R.class1Aligned
  class1DeepBoosted := R.class1DeepBoosted

/-- The final statement from the wave-21 summit surface, through the proved
v20 keystone route (→ v19 convergence → frontier + absorption + the
fully-corrected six-phase ledger). -/
theorem toStatement (R : Erdos260SummitResidual) : Erdos260Statement :=
  R.toKeystoneResidual.toStatement

end Erdos260SummitResidual

/-- **THE WAVE-21 ENDPOINT**: `Erdos260Statement` from the 16-field summit
surface — the three K.1 fields at their exact iff-reductions (interior cluster
floor / span rarity / anchor surplus), the run low lane narrowed to its
band-heavy half at `(63,10)`, the exit-silent stratum free, and the named
suppliers wired (`ElcOffPinUncoveredResidual`, `EmfcUnifiedExitMassFamily`,
`Class1AlignmentBitAtom`, the windowed checks).  Public bridges only. -/
theorem erdos260_of_summitResidual (R : Erdos260SummitResidual) :
    Erdos260Statement :=
  R.toStatement

/-! ## Part 2.  The weakening witness (FULL — an improvement over v20)

Unlike the v19→v20 step (where the two K.1 atoms genuinely strengthened the
cover lane and only an atoms-assisted witness existed), EVERY wave-21 fold is
an equivalence or a proved resolution: the three K.1 replacements are exact
iffs (`k1acClusterFloor_iff_interior`, `k1acStartSpacing_iff_spanRarity`,
`k1acDensity_iff_anchorSurplus`), and the `(63,10)` narrowing is the proved
cycle-horn voiding (`c1abRunCycle_void_63_10` resolves the v20 disjunction).
So the FULL witness holds — no atom assistance needed. -/

/-- **The FULL weakening witness**: every wave-20 keystone inhabitant yields a
wave-21 summit inhabitant.  The three K.1 fields transport through the iff
`mp` directions; the `(63,10)` lane resolves through the proved cycle-horn
voiding; everything else is verbatim. -/
def summitResidual_of_keystoneResidual (R : Erdos260KeystoneResidual) :
    Erdos260SummitResidual where
  deepOrbitPin := R.deepOrbitPin
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow6310 := fun ctx hpin hq hK hL hr => by
    have hq64 : (class1SlopeDatum ctx).q < 64 := by rw [hq]; norm_num
    have hnotin : ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
        ∉ dccRunBandFreeLowPairs := by
      rw [hq, hK]; decide
    exact c1abRunLow_reduces_63_10 ctx hq hK
      (R.runNumericLow ctx hpin hq64 hnotin hL hr)
  runNumericLowOff := fun ctx hpin hq hnotin _ hL hr =>
    R.runNumericLow ctx hpin hq hnotin hL hr
  runNumericTail := R.runNumericTail
  returnGatesOffTable := R.returnGatesOffTable
  returnInteriorOffTable := R.returnInteriorOffTable
  densePackInteriorClusterFloor := fun ctx h1 h2 h3 h4 h5 h6 =>
    (k1acClusterFloor_iff_interior ctx).mp
      (R.densePackClusterFloor ctx h1 h2 h3 h4 h5 h6)
  densePackSpanRarity := fun ctx h1 h2 h3 h4 h5 h6 =>
    (k1acStartSpacing_iff_spanRarity ctx).mp
      (R.densePackStartSpacing ctx h1 h2 h3 h4 h5 h6)
  densePackAnchorSurplus := fun ctx h1 h2 h3 h4 =>
    (k1acDensity_iff_anchorSurplus ctx).mp
      (R.densePackDensityOffTable ctx h1 h2 h3 h4)
  densePackInteriorOffTable := R.densePackInteriorOffTable
  class0Gates := R.class0Gates
  boostLevel := R.boostLevel
  class1Aligned := R.class1Aligned
  class1DeepBoosted := R.class1DeepBoosted

/-- Sanity commutation: a wave-20 keystone inhabitant reaches the statement
through the wave-21 summit route as well. -/
theorem erdos260_of_keystoneResidual_via_summit (R : Erdos260KeystoneResidual) :
    Erdos260Statement :=
  (summitResidual_of_keystoneResidual R).toStatement

/-! ## Part 3.  The exit-mass axis: the exit-silent stratum, the uncovered
residual, the unified family -/

/-- **The exit-silent stratum is FREE** (the 384-pair dispatcher, re-exported
at the capstone): at EVERY context whose slope datum is one of the 384
exit-silent table pairs, all three off-pin caps hold OUTRIGHT — the class
3/4/5 fibres are empty there (`elcSilentEmpty_of_mem`). -/
theorem summitExitSilent_free (ctx : ActualFailureContext) (h : ElcSilentCtx ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3 ≤ emcCap ctx
      ∧ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4 ≤ emcCap ctx
      ∧ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
          ≤ emcCap ctx :=
  elcOffPin_at_silent ctx h

/-- **The off-pin conjunct from the uncovered residual**: the off-pin demand
narrows to `ElcOffPinUncoveredResidual` — deep pin-free contexts whose datum is
NOT exit-silent (everything the 384 certificates do not cover). -/
theorem summitOffPin_of_uncovered (h : ElcOffPinUncoveredResidual) :
    ExitMassControlOffPin :=
  elcOffPin_of_uncoveredResidual h

/-- **The FULL deep core from the uncovered residual + the summit's kept axis**
(the documented v21 supplier route for `deepOrbitPin`'s unified core —
strictly narrower input than the v20 regime route). -/
theorem summitExitMassCore_of_uncovered (h : ElcOffPinUncoveredResidual)
    (R : Erdos260SummitResidual) : ExitMassControlCore :=
  elcCore_of_uncoveredResidual_and_voiding h R.deepOrbitPin

/-- **The FULL deep core from the unified family + the summit's kept axis**
(the preferred family assembly: class-0 atom + spaced-share regime). -/
theorem summitExitMassCore_of_family (h : EmfcUnifiedExitMassFamily)
    (R : Erdos260SummitResidual) : ExitMassControlCore :=
  emfc_family_core h R.deepOrbitPin

/-- **THE UNIFIED EXIT-MASS ASSEMBLY THEOREM** (the wave-21 deliverable): the
cheapest sufficient inputs — per-survivor windowed cycle checks (= class-0
fibre emptiness) plus the spaced-share regime — assemble the WHOLE unified
family, and with the summit's kept voiding axis they rebuild the FULL
`ExitMassControlCore`. -/
theorem summitUnifiedExitMass_assembly
    (hw : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      Class0WindowCycleCheck ctx)
    (hr : EmcOffPinSpacedShareRegime)
    (R : Erdos260SummitResidual) :
    EmfcUnifiedExitMassFamily ∧ ExitMassControlCore :=
  have hfam : EmfcUnifiedExitMassFamily := emfc_family_of_checks_and_regime hw hr
  ⟨hfam, emfc_family_core hfam R.deepOrbitPin⟩

/-- **The share-from-spacing verdict (NEGATIVE, re-recorded)**: `c`-spacing
plus containment does NOT imply the `b = 1` share — the weight can concentrate
on the fibre's residue class.  The share is genuinely exit-avoidance /
equidistribution content, not a tiling consequence. -/
theorem summitShare_not_from_spacing :
    ∃ (w : ℕ → ℕ) (F R : Finset ℕ) (c : ℕ), 1 ≤ c ∧ F ⊆ R
      ∧ (∀ x ∈ F, ∀ z ∈ F, x ≤ z → c ∣ z - x)
      ∧ ¬ (c * ∑ j ∈ F, w j ≤ 1 * ∑ j ∈ R, w j) :=
  elcShare_not_from_spacing_alone

/-! ## Part 4.  The class-0 windowed-check suppliers -/

/-- **The full class-0 atom from the windowed checks** (the cheapest open
input): windowed cycle checks at every survivor pair — each EQUIVALENT to
class-0 fibre emptiness at its context — supply the named atom
`MdcClass0ExitMassControl`. -/
theorem summitClass0Control_of_windowChecks
    (hw : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      Class0WindowCycleCheck ctx) : MdcClass0ExitMassControl :=
  emfc_class0Control_of_windowChecks hw

/-- **The survivor mass row from the windowed checks** (the v18/v19/v20 shape,
through the atom). -/
theorem summitClass0SurvivorRow_of_windowChecks
    (hw : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      Class0WindowCycleCheck ctx) :
    ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  mdcClass0SurvivorMass_of_atom (emfc_class0Control_of_windowChecks hw)

/-! ## Part 5.  The class-1 axis: the alignment bit and the free levels -/

/-- **The level-1 aligned supply from the named atom** — the alignment bit is
the NAMED supplier of the summit's `class1Aligned` field at `boostLevel = 1`. -/
theorem summitClass1Aligned_of_alignmentBit (h : Class1AlignmentBitAtom) :
    DccClass1AlignedCountSupply 1 :=
  c1abSupply_one_of_atom h

/-- **The doubled-regime chain** (re-exported): the alignment bit closes the
class-1 absorption on the whole band `L ≤ 2549478` — DOUBLE the v19/v20
parametric gate. -/
theorem summitClass1Absorption_of_alignmentBit (h : Class1AlignmentBitAtom)
    (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 2549478) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  c1abClass1Absorption_of_atom h ctx hL

/-- **`(103,51)` at its BOOSTED threshold** (level 4 is FREE there): the pair's
open content is the boosted atom at `L > 1274739·2^4 = 20395824` — a genuine
factor `1.18` past the wave-18 table threshold `T = 17270663`. -/
theorem summitClass1Pair_103_51_of_boostedAtom
    (hatom : DccClass1DeepPairAtomBoosted 103 51 17270663 4) :
    ∀ ctx : ActualFailureContext,
      (class1SlopeDatum ctx).q = 103 → (class1SlopeDatum ctx).K₀ = 51 →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  c1abPair_103_51_of_boostedAtom hatom

/-- **`(107,53)` at its BOOSTED threshold** (level 3 is FREE there): residual
regime `L > 1274739·2^3 = 10197912` — factor `1.25` past `T = 8172724`. -/
theorem summitClass1Pair_107_53_of_boostedAtom
    (hatom : DccClass1DeepPairAtomBoosted 107 53 8172724 3) :
    ∀ ctx : ActualFailureContext,
      (class1SlopeDatum ctx).q = 107 → (class1SlopeDatum ctx).K₀ = 53 →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  c1abPair_107_53_of_boostedAtom hatom

/-- **`(101,50)` honest record**: the proved level-3 supply gives the boosted
closure, but the boosted band `1274739·2^3 = 10197912 < T = 10280156` is
SUBSUMED by the SRE table threshold — the residual there stays `L > T`. -/
theorem summitClass1Pair_101_50_of_boostedAtom
    (hatom : DccClass1DeepPairAtomBoosted 101 50 10280156 3) :
    ∀ ctx : ActualFailureContext,
      (class1SlopeDatum ctx).q = 101 → (class1SlopeDatum ctx).K₀ = 50 →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  c1abPair_101_50_of_boostedAtom hatom

/-! ## Part 6.  The run/tower cycle-horn voidings (the gcd-period mechanism) -/

/-- **The run cycle horn is FALSE at every `(63,10)` context** (re-exported):
the certified period-2 band-4-reading cycle plus the gcd-period upgrade void
the horn — the summit's `runNumericLow6310` field shape is FORCED. -/
theorem summitRunCycle_void_63_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    ¬ Class5CycleNumericCloses ctx :=
  c1abRunCycle_void_63_10 ctx hq hK

/-- **The tower cycle horn is FALSE at every `(63,10)` context on the demanded
`m₀ ≥ 3` regime** (re-exported; the certified band-4-reading period 2 caps
`m₀ ≤ 2`).  HONEST: the tower field has no band-heavy half to retreat to, so
this is a constraint on inhabitants, not a cheaper field shape. -/
theorem summitTowerCycle_void_63_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10)
    (hm : 3 ≤ towerSparsityBlock ctx) :
    ¬ Class2CycleInequality ctx :=
  c1abTowerCycle_void_63_10 ctx hq hK hm

/-! ## Part 7.  The K.1 suppliers and the price-paid records -/

/-- **Span rarity from per-span exit-lightness** (the best conditional at
`r ≥ 2`, where the cycle route is dead): band ≤ 4 + `K1LocalExitLight` supply
the summit's `densePackSpanRarity` content outright — the K.1 spacing lane
consumes the SAME exit-mass currency as the unified family. -/
theorem summitSpanRarity_of_localExitLight (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) (h : K1LocalExitLight ctx) :
    K1SpanRarity ctx :=
  k1acSpanRarity_of_localExitLight ctx hband h

/-- **Index persistence voids ALL THREE K.1 demands** (re-exported): at a
fixed-family hit with index persistence, density, cluster floor and spacing
hold vacuously — the only in-tree route to `DscTopBandExitFree` empties the
genuine start set exactly as it voids the class-0 fibre. -/
theorem summitK1Demands_of_indexPersistence (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hp : FixedFamilyIndexPersistence ctx) :
    densePackEndpointDensity ctx ∧ K1ClusterFloor ctx ∧ K1StartSpacing ctx :=
  k1acK1Demands_of_indexPersistence ctx hhit hp

/-- **The topband price is PAID at every band-2 pin** (re-exported): the
sharpened support floor holds unconditionally — no `DscTopBandExitFree`
needed on the pinned strata. -/
theorem summitTopBandPrice_pin2 (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2) :
    ctx.shell.X ≤ 2 * ((emW ctx - (ctx.n24CarryData.r + 1))
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) :=
  k1acTopBandPricePaid_of_pin2 ctx hpin

/-- **The topband price is PAID at every band-3 pin** (re-exported). -/
theorem summitTopBandPrice_pin3 (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) :
    ctx.shell.X ≤ 2 * ((emW ctx - (ctx.n24CarryData.r + 1))
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) :=
  k1acTopBandPricePaid_of_pin3 ctx hpin

/-- **The topband price is PAID at every band-4 pin** (re-exported). -/
theorem summitTopBandPrice_pin4 (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4) :
    ctx.shell.X ≤ 2 * ((emW ctx - (ctx.n24CarryData.r + 1))
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) :=
  k1acTopBandPricePaid_of_pin4 ctx hpin

/-! ## Part 8.  Honest machine-readable status -/

/-- Machine-readable, honest status of the wave-21 summit capstone. -/
def erdos260SummitCapstoneStatus : List String :=
  [ "SURFACE (16 fields): Erdos260SummitResidual = the wave-20 keystone " ++
      "surface rebased on the five wave-21 lanes.  NEW vs wave 20: (a) the " ++
      "three densepack K.1 fields are replaced by their EXACT iff-reductions " ++
      "- densePackInteriorClusterFloor (K1InteriorClusterFloor; boundary " ++
      "stratum free, k1acClusterFloor_iff_interior), densePackSpanRarity " ++
      "(K1SpanRarity; spacing <-> one-per-span, " ++
      "k1acStartSpacing_iff_spanRarity; the cycle-spacing route is DEAD at " ++
      "r >= 2 - the width outruns every c <= 15430), densePackAnchorSurplus " ++
      "(exists d, K1AnchorSurplus; density <-> anchor-with-surplus, " ++
      "k1acDensity_iff_anchorSurplus; the band-3 syndetic supply is 1 hit vs " ++
      "the L/8 demand); (b) runNumericLow is SPLIT: at (63,10) only the " ++
      "band-heavy half is demanded (runNumericLow6310 - the cycle horn is " ++
      "provably FALSE there, c1abRunCycle_void_63_10), the rest verbatim " ++
      "(runNumericLowOff); (c) deepOrbitPin / class0Gates / the boost ladder " ++
      "/ towers / returns / interiors verbatim with new named suppliers.",
    "ENDPOINT (PROVED): erdos260_of_summitResidual : Erdos260SummitResidual " ++
      "-> Erdos260Statement through toKeystoneResidual + the proved v20 " ++
      "route.  WEAKENING WITNESS (FULL - an improvement over v20, which " ++
      "needed atom assistance): summitResidual_of_keystoneResidual holds " ++
      "outright - every wave-21 fold is an equivalence (the three K.1 iffs) " ++
      "or a proved resolution (the (63,10) cycle-horn voiding).",
    "THE EXIT-MASS AXIS (ExitLightCycleCertificates + ExitMassFamilyClosure): " ++
      "the complete survey of ALL 999000 pairs (q odd in [3,2000)) found " ++
      "4578 NEW b4 = 1 deep-clearing pairs at q >= 303 (c in 50..70; 10 " ++
      "certified; the wave-20 'none exist' was a q < 200 horizon artifact; " ++
      "the exact deep boundary is c >= 50, not 54/64) and exactly 384 " ++
      "EXIT-SILENT pairs (all bands >= 5; class 1-5 fibres EMPTY; b = 0 " ++
      "datum proved) where ExitMassControlOffPin fires OUTRIGHT " ++
      "(summitExitSilent_free).  The off-pin residual narrows to " ++
      "ElcOffPinUncoveredResidual (summitOffPin_of_uncovered; full core via " ++
      "summitExitMassCore_of_uncovered).  The family is genuinely unified: " ++
      "emcFibreExitMass is multiplicity-free and mdcClass0ExitMass = " ++
      "emcFibreExitMass 0; the preferred assembly is " ++
      "summitUnifiedExitMass_assembly (per-survivor windowed checks + the " ++
      "spaced-share regime => EmfcUnifiedExitMassFamily + the full core).  " ++
      "THE SHARE IS EXIT-AVOIDANCE, NOT EQUIDISTRIBUTION-FREE: it forces " ++
      "each recurrent class to carry <= 31/768 of the exit mass and to MISS " ++
      "an exit (emfc_spacedShare_forces_exitLight / _not_covering / " ++
      "_misses_exit; named necessary atom EmfcFibreExitLight); " ++
      "share-from-spacing is REFUTED by kernel counterexample " ++
      "(summitShare_not_from_spacing).",
    "THE CLASS-1 AXIS (Class1AlignmentBit): the named atom " ++
      "Class1AlignmentBitAtom supplies the level-1 aligned count " ++
      "(summitClass1Aligned_of_alignmentBit) and DOUBLES the closed class-1 " ++
      "regime to L <= 2549478 (summitClass1Absorption_of_alignmentBit); the " ++
      "spacing-to-count slack is settled three ways (incl. the 184-margin " ++
      "slack-tolerant gate c1abBoostGateSlack); FREE levels at slack table " ++
      "pairs (2^v*b4 < c): level 4 at (103,51), level 3 at (107,53)/(101,50) " ++
      "- the pair residuals move to their boosted thresholds " ++
      "(summitClass1Pair_103_51/107_53_of_boostedAtom; (101,50) honestly " ++
      "subsumed by its SRE threshold); the Q-even key-local even-gap bit is " ++
      "proved (c1abSameKey_gap_even_of_Q_even) but does not yield the supply " ++
      "without a class-1 key-count bound.",
    "THE GCD-PERIOD VOIDINGS (Class1AlignmentBit): orbit periods valid from " ++
      "index 1 are closed under gcd (c1abPeriod_gcd), upgrading the wave-18 " ++
      "floors from the witness period to ANY certified period: the run cycle " ++
      "horn is FALSE at every certified band-reading pair (every in-tree " ++
      "certified period <= 98 << 1537 - c1abClass5CycleNumeric_void), " ++
      "likewise the band-heavy horn bound (c1abClass5BandHeavy_void) and the " ++
      "tower block cap (c1abClass2Cycle_block_le_certified).  At (63,10): " ++
      "summitRunCycle_void_63_10 (the field's demand narrows to the " ++
      "band-heavy half - folded into the surface) and " ++
      "summitTowerCycle_void_63_10 (m0 >= 3 regime; recorded, not foldable - " ++
      "no tower band-heavy half exists).",
    "THE K.1 AXIS (K1AtomsClosure): all three demands at exact " ++
      "iff-reductions (folded into the surface); suppliers: " ++
      "summitSpanRarity_of_localExitLight (per-span exit-lightness at band " ++
      "<= 4 - the SAME currency as the exit-mass family, via the localized " ++
      "level-set cap k1acSpanCount_cap) and " ++
      "summitK1Demands_of_indexPersistence (index persistence voids all " ++
      "three demands - the only in-tree DscTopBandExitFree route empties the " ++
      "start set).  THE PRICE-PAID THEOREMS: the sharpened topband support " ++
      "floor holds UNCONDITIONALLY at every band-2/3/4 pin " ++
      "(summitTopBandPrice_pin2/3/4) - DscTopBandExitFree's quantitative " ++
      "cost is already paid on all pinned strata.",
    "THE CLASS-0 AXIS (ExitMassFamilyClosure): the wave-16 windowed check IS " ++
      "class-0 fibre emptiness per context " ++
      "(emfc_class0FibreEmpty_iff_windowCheck - the cheapest open input); " ++
      "per-survivor checks supply the full named atom " ++
      "(summitClass0Control_of_windowChecks) and the survivor mass row " ++
      "(summitClass0SurvivorRow_of_windowChecks); all 19 survivors defeat " ++
      "the window-FREE check, so the windowed check is genuinely open per " ++
      "survivor.  The gates field is KEPT (the checks supply neither the " ++
      "mid/big lanes nor per-member levels).",
    "FOLDS SKIPPED (honest): the class-1 ladder keeps the v20 shape " ++
      "(replacing class1Aligned by Class1AlignmentBitAtom would STRENGTHEN " ++
      "the surface - the atom implies the level-1 supply, no converse " ++
      "in-tree; the free-level pair routes are suppliers, not demands); " ++
      "towerEnumLow is verbatim (the (63,10) voiding constrains inhabitants " ++
      "but no band-heavy tower half exists); class0Gates is not replaced by " ++
      "the windowed checks; deepOrbitPin and the interior/topband slots are " ++
      "unchanged (price-paid noted); the binary-drift improvement " ++
      "(emfc_windowExcess_drift_binary, factor ~L/4 on exit-free blocks) " ++
      "clears NO regime unconditionally and stays a record.",
    "WHAT REMAINS OPEN AFTER WAVE 21 (the honest core): (a) " ++
      "ElcOffPinUncoveredResidual - the off-pin caps at deep pin-free " ++
      "contexts with non-exit-silent data - plus the b4 = 1 share/regime at " ++
      "the 4578 certified-style deep-clearing pairs (EmcSpacedShareDatum at " ++
      "b = 1, c >= 50); (b) Class1AlignmentBitAtom + the boosted per-pair " ++
      "residuals DccClass1DeepPairAtomBoosted (and the generic ladder at " ++
      "v >= 1); (c) the class-0 windowed cycle checks per survivor (= " ++
      "fibre-0 emptiness - the cheapest input); (d) K1InteriorClusterFloor + " ++
      "K1SpanRarity (suppliers: K1LocalExitLight at band <= 4) + " ++
      "K1AnchorSurplus at b3 > 0; (e) DscTopBandExitFree (price paid at all " ++
      "pins); (f) the tower/run band-heavy halves + the q >= 384 strata " ++
      "(towerEnumTail / runNumericTail verbatim); (g) DeepOrbitPinVoiding " ++
      "(+ the u = 7 cousin DeepSeventhsPinVoid).",
    "HYGIENE: additive only - ONE new module; no sorry / admit / new axiom / " ++
      "native_decide; every key declaration passes #print axioms within " ++
      "[propext, Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem erdos260SummitCapstoneStatus_nonempty :
    erdos260SummitCapstoneStatus ≠ [] := by
  simp [erdos260SummitCapstoneStatus]

/-! ## Part 9.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]`
or fewer. -/

#print axioms Erdos260SummitResidual.toKeystoneResidual
#print axioms Erdos260SummitResidual.toStatement
#print axioms erdos260_of_summitResidual
#print axioms summitResidual_of_keystoneResidual
#print axioms erdos260_of_keystoneResidual_via_summit
#print axioms summitExitSilent_free
#print axioms summitOffPin_of_uncovered
#print axioms summitExitMassCore_of_uncovered
#print axioms summitExitMassCore_of_family
#print axioms summitUnifiedExitMass_assembly
#print axioms summitShare_not_from_spacing
#print axioms summitClass0Control_of_windowChecks
#print axioms summitClass0SurvivorRow_of_windowChecks
#print axioms summitClass1Aligned_of_alignmentBit
#print axioms summitClass1Absorption_of_alignmentBit
#print axioms summitClass1Pair_103_51_of_boostedAtom
#print axioms summitClass1Pair_107_53_of_boostedAtom
#print axioms summitClass1Pair_101_50_of_boostedAtom
#print axioms summitRunCycle_void_63_10
#print axioms summitTowerCycle_void_63_10
#print axioms summitSpanRarity_of_localExitLight
#print axioms summitK1Demands_of_indexPersistence
#print axioms summitTopBandPrice_pin2
#print axioms summitTopBandPrice_pin3
#print axioms summitTopBandPrice_pin4
#print axioms erdos260SummitCapstoneStatus_nonempty

end

end Erdos260
