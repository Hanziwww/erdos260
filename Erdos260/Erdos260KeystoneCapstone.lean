import Erdos260.Erdos260ConvergenceCapstone
import Erdos260.ExitMassCoreTranscription
import Erdos260.K1LandingClosure
import Erdos260.DeepCountingClosure
import Erdos260.MissDistanceClosure
import Erdos260.AppendixNDescent

/-!
# The wave-20 keystone capstone: `Erdos260KeystoneResidual`

The wave-19 convergence surface (`Erdos260ConvergenceResidual`) REBASED on the
five wave-20 lanes:

* **`DeepCountingClosure`** — the class-1 deep field is re-cut as the BOOST
  LADDER: a `2^v`-sparse aligned-count supply (`DccClass1AlignedCountSupply v`)
  closes the class-1 absorption on the whole band `L ≤ 1274739·2^v`
  (`dccBoostGate`, sharp at every level `v` — `dccBoostGate_sharp`), so the
  surface pair is `boostLevel` + aligned supply + the boosted residual
  `DccClass1DeepResidual boostLevel` (demand only at `L > 1274739·2^v`).  Level
  `0` is FREE (`dccAlignedSupply_zero_free`) and exactly re-cuts the v19 field
  (`dccBoost_zero_recovers` / `dccResidual_zero_of_field`) — the v19 witness
  holds on this leg.  The tower/run low lanes are narrowed to their band-reading
  strata: 6 run pairs + 7 tower pairs are closed outright by new kernel cycle
  certificates (`dccRunBandFreeLowPairs` / `dccTowerBand4FreeLowPairs`); the
  dispatchers `dccRunNumericLow_field_of_bandReading` /
  `dccTowerEnumLow_field_of_bandReading` rebuild the exact v19 fields.
* **`K1LandingClosure`** — the v19 `densePackCoverOffTable` field is REPLACED by
  the two named K.1 atoms at `r ≥ 1`: `K1ClusterFloor` (per-window placement)
  and `K1StartSpacing` (W-spacing of genuine starts).  The `r = 0` stratum
  (ALL `L ≤ 15420`) closes unconditionally (`k1CoverBody_of_r_eq_zero` — the
  demanded width truncates to `0`; dichotomy `k1CoverWidth_eq_zero_iff`), and
  the K.1 landing `k1CoverBody_of_density_cluster_spacing` rebuilds the exact
  v19 cover body from density + the two atoms.  The spacing atom is discharged
  on single-band-3-residue cycles with `2·carryB Q + 1 ≤ c` at `r = 1`
  (`k1StartSpacing_of_singleResidue` / `k1CoverBody_of_r_one_singleResidue`).
  The density field stays verbatim (sharp anatomy:
  `densePackEndpointDensity_iff_endpoints_mem` — every genuine endpoint is an
  actual point).
* **`MissDistanceClosure`** — the gap-deviation classification is BINARY:
  non-exit gaps deviate exactly `0`, so every class-0 member's window contains
  an exit (`mdcFibre0_window_has_exit`) and the miss-distance count route is
  provably inverted (`mdc_missDistance_route_inverted`).  The class-0 lane
  JOINS the exit-mass family: the named atom `MdcClass0ExitMassControl` (the
  class-0 fibre exit-mass cap; the unrestricted form is REFUTED at factor
  `768/31` — `mdcUnrestrictedAtom_refuted`) closes the survivor mass row
  (`mdcClass0SurvivorMass_of_atom`), and per-lane class-0 exit-mass caps build
  the FULL gates field (`mdcGates_of_class0ExitMassCaps`).  The gates field is
  KEPT (the atom alone does not supply the mid/big lanes nor the per-member
  gate levels) — the atom is the named PREFERRED SUPPLIER.
  `DscTopBandExitFree` stays the structural slot (onset suppliers void the
  class-0 demand where they fire — `mdcIndexPersistence_voids_class0`; the
  refutation is impossible; the cost is the sharpened support floor
  `mdc_topBandExitFree_support_floor`).
* **`ExitMassCoreTranscription`** — the in-tree mass is start-indexed, so the
  manuscript's in-cycle-uncharged ledger transcribes as EVENT COUNTING: the
  fibre-restricted exit mass `emcFibreExitMass` with the spaced overlap bound
  gives the master conditional `emc2_cap_of_spacedShare`, and the regime
  self-limits to `768·((r+c)/c)·b ≤ 31·c` (`emc2_spacedShare_forces_threshold`).
  8 table pairs clear the absolute threshold, NONE the deep one
  (`emcDeepProportionalClearedPairs_eq_nil`) — the minimal residual is
  `EmcSpacedShareDatum` at UNCERTIFIED parameters (exit-light long cycles:
  `b = 1`, `c ≥ 64`).  `emc2_core_of_regime_and_voiding` rebuilds the FULL
  `ExitMassControlCore` from the regime + the kept `deepOrbitPin` axis — the
  documented supplier route for the deep core.
* **`AppendixNDescent`** — THE HEADLINE NEGATIVE: the covering demand is
  per-context UNSATISFIABLE (`coveringDemand_void` — the wave-10 sharp fire
  condition `17·g ≤ 2^24` at the trivial representation, fed by the demand's
  OWN Q-cap, kills it at ALL odd parts).  `OffCycleCoveringSupply`,
  `NonPinnedCoveringSupply`, `MultiScaleSiblingSupply` and the pinned split are
  ALL equivalent to context-emptiness (`offCycleCoveringSupply_iff_noContext`,
  `pinnedSplit_iff_noContext`, `multiScaleSiblingSupply_iff_noContext`) — the
  covering/sibling lane is a DEAD END, never cheaper than the per-class
  surface.  The v19 parallel endpoint is DROPPED from this surface's story;
  the collapse is recorded below (`keystone_coveringSupply_collapse`).  The
  `u = 7` stratum keeps its named atom `DeepSeventhsPinVoid` (genuinely
  uncovered by the three levers; inherits the `X > 2^986891` floor).

## The surface (15 fields)

`deepOrbitPin` (verbatim; suppliers: `ExitMassControlCore`, itself rebuildable
from `EmcOffPinSpacedShareRegime` + the axis) + `towerEnumLow` / `runNumericLow`
(narrowed OFF the 7/6 certified band-free pairs) + `towerEnumTail` /
`runNumericTail` (verbatim v19) + `returnGatesOffTable` /
`returnInteriorOffTable` (verbatim v19) + `densePackClusterFloor` /
`densePackStartSpacing` (the two named K.1 atoms at `r ≥ 1`, REPLACING the v19
cover field) + `densePackDensityOffTable` / `densePackInteriorOffTable`
(verbatim v19) + `class0Gates` (kept; preferred supplier
`MdcClass0ExitMassControl`) + `boostLevel` / `class1Aligned` /
`class1DeepBoosted` (the boost ladder, REPLACING the v19 `class1Deep`).

## The endpoint

`erdos260_of_keystoneResidual` routes through `toConvergenceResidual` (the K.1
landing rebuilds the cover field; the boost ladder rebuilds the class-1 field;
the band-reading dispatchers rebuild the tower/run low fields) and the proved
v19 endpoint `erdos260_of_convergenceResidual`.

## Folds kept / witnesses (honest)

* The FULL weakening witness `Erdos260ConvergenceResidual →
  Erdos260KeystoneResidual` does NOT hold: the two K.1 atoms genuinely
  strengthen the cover field (a cardinality inequality does not pin down hit
  placement or start spacing — the wave-19 L-spacing hunt's negative).  The
  honest witness is atoms-assisted:
  `keystoneResidual_of_convergenceResidual_and_atoms` (every OTHER fold is a
  pure weakening: guards dropped, ladder at level `0`).
* `class0Gates` is NOT replaced by `MdcClass0ExitMassControl`: the atom closes
  the survivor mass row only; the gates demand per-member levels on three
  lanes.  Kept + consumption lemmas (`keystoneClass0SurvivorRow_of_atom`;
  `mdcGates_of_class0ExitMassCaps` builds the full field from per-lane caps).
* `DscTopBandExitFree` is NOT folded into the interior fields (unchanged from
  v19); the onset suppliers are recorded
  (`keystoneReturnInterior_of_topBandOnsets`,
  `keystoneDensePackInterior_of_topBandOnsets`) with the honest void note.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The wave-20 keystone surface -/

/-- **The wave-20 keystone capstone surface.**  The wave-19 convergence surface
rebased on the five wave-20 lanes: the class-1 deep field becomes the boost
ladder (`2^v`-sparse aligned supply + boosted residual), the densepack cover
field becomes the two named K.1 atoms at `r ≥ 1` (the `r = 0` stratum is free),
the tower/run low lanes are narrowed off the certified band-free pairs, the
class-0 gates are kept with `MdcClass0ExitMassControl` as preferred supplier,
and the covering lane is GONE (provably dead — `coveringDemand_void`). -/
structure Erdos260KeystoneResidual where
  /-- **The single deep orbit-pin voiding** (verbatim v18/v19 field).  Supplier
  chain: `EmcOffPinSpacedShareRegime` + this axis rebuild the full
  `ExitMassControlCore` (`emc2_core_of_regime_and_voiding`), which in turn
  supplies this field at every scale — the spaced-share route's honest open
  content at deep scales is `EmcSpacedShareDatum` at UNCERTIFIED parameters
  (`b = 1`, `c ≥ 64` — `emc2_deep_spacedShare_not_certified`). -/
  deepOrbitPin : DeepOrbitPinVoiding
  /-- Tower / class 2 — enumerated part (`q < 107`), floor-guarded, NARROWED off
  the seven certified band-4-free pairs `dccTowerBand4FreeLowPairs`
  (`(5,1), (5,2), (7,3), (51,1), (51,8), (63,1), (63,4)` close
  `Class2CycleInequality` outright at every scale —
  `dccClass2Cycle_of_band4FreePair`). -/
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
  /-- Tower / class 2 — tail (`107 ≤ q`), floor-guarded (verbatim v19). -/
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
  /-- Run / class 5 — enumerated part (`q < 64`) on band-4-free contexts,
  floor-guarded, NARROWED off the six certified band-free pairs
  `dccRunBandFreeLowPairs` (`(3,1), (21,3), (51,1), (51,8), (63,1), (63,4)`
  close `Class5CycleNumericCloses` outright at every scale —
  `dccClass5CycleCloses_of_bandFreePair`). -/
  runNumericLow : ∀ ctx : ActualFailureContext,
    ¬ OrbitBandPinned ctx 4 →
    (class1SlopeDatum ctx).q < 64 →
    ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
      ∉ dccRunBandFreeLowPairs →
    986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 — tail (`64 ≤ q`) on band-4-free contexts, floor-guarded
  (verbatim v19). -/
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
  stratum (verbatim v19). -/
  returnGatesOffTable : ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
    ¬ OrbitBandPinned ctx 2 →
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 K.1 interior, demanded only OFF the `b₂ = 0` stratum
  (verbatim v19).  Conditional supply slots: `DscTopBandExitFree`
  (`convergenceReturnInterior_of_topBandExitFree`) and the onset route
  (`keystoneReturnInterior_of_topBandOnsets` — honest: the only in-tree
  band-following supplier voids the class-0 fibre where it fires). -/
  returnInteriorOffTable : ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- **THE K.1.1 CLUSTER-FLOOR ATOM** (NEW — replaces the v19 cover field
  jointly with the spacing atom): at every genuine start the endpoint window's
  hits keep top slack `W` — the per-window placement content the bare
  cardinality floor does not pin down.  Demanded only at `r ≥ 1` (the whole
  `r = 0` stratum, i.e. ALL `L ≤ 15420`, closes outright:
  `k1CoverBody_of_r_eq_zero`; the atom itself is free there —
  `k1ClusterFloor_of_r_eq_zero`). -/
  densePackClusterFloor : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
    ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
    K1ClusterFloor ctx
  /-- **THE K.1.3 START-SPACING ATOM** (NEW): distinct genuine starts are spaced
  at least `W` apart — the wave-19 spacing-hunt target, named exactly.
  Discharged on single-band-3-residue cycles with `2·carryB Q + 1 ≤ c`
  (`k1StartSpacing_of_singleResidue`); at `r = 1` the width is EXACTLY
  `2·carryB Q + 1` (`k1CoverWidth_eq_of_r_eq_one`), so the `b₃ = 1` regime is
  clean.  Demanded only at `r ≥ 1` (free at `r = 0`:
  `k1StartSpacing_of_r_eq_zero`). -/
  densePackStartSpacing : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
    ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
    K1StartSpacing ctx
  /-- DensePack / class 3 K.1.1 coarea hit-density, demanded only OFF the
  `b₃ = 0` stratum (verbatim v19).  Sharp anatomy: density ↔ every genuine
  endpoint `k + r` is an actual point
  (`densePackEndpointDensity_iff_endpoints_mem`); the open content at `b₃ > 0`
  is a position constraint, not a count
  (`k1DensityField_position_constraint`). -/
  densePackDensityOffTable : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    densePackEndpointDensity ctx
  /-- DensePack / class 3 K.1 active-window interior, demanded only OFF the
  `b₃ = 0` stratum (verbatim v19).  Conditional supply slots as in v19, plus
  the onset route (`keystoneDensePackInterior_of_topBandOnsets`). -/
  densePackInteriorOffTable : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
    ¬ Class3TopBandCycleFree ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card
  /-- **The three narrow-support class-0 gate lanes** (kept verbatim v19).
  NEW preferred supplier: the class-0 fibre exit-mass caps — per-lane caps
  build the FULL field (`mdcGates_of_class0ExitMassCaps`), and the named atom
  `MdcClass0ExitMassControl` closes the survivor mass row outright
  (`keystoneClass0SurvivorRow_of_atom`).  HONEST: the atom alone does NOT
  supply this field (no mid/big lanes, no per-member levels), so the field
  stays; the unrestricted (non-fibre) form of the atom is REFUTED at factor
  `768/31` (`mdcUnrestrictedAtom_refuted`) — class 0 genuinely JOINS the
  exit-mass family at the fibre-restricted cap. -/
  class0Gates : NarrowSupportClass0Gates
  /-- **The boost level** of the class-1 deep ladder.  Level `0` re-cuts the
  v19 surface exactly; each level `v ≥ 1` multiplies the closed class-1 band
  by `2^v` (`dccBoostGate`, sharp at every level — `dccBoostGate_sharp`). -/
  boostLevel : ℕ
  /-- **The aligned-count supply at the boost level** (NEW — the carry-alignment
  interface): on the genuinely deep contexts the class-1 fibre is
  `2^boostLevel`-sparse in the support window.  FREE at level `0`
  (`dccAlignedSupply_zero_free`).  HONEST: no in-tree carry-valuation exists
  for class 1 (all carry-valuation content is class-4-side), so levels `v ≥ 1`
  are a genuine residual. -/
  class1Aligned : DccClass1AlignedCountSupply boostLevel
  /-- **The boosted class-1 deep residual** (REPLACES the v19 `class1Deep`):
  the v19 demand pushed out to `L > 1274739·2^boostLevel` (off-table guard
  verbatim; `r ≥ 82` is free there).  At level `0` this IS the v19 field
  re-cut (`dccBoost_zero_recovers` / `dccResidual_zero_of_field`). -/
  class1DeepBoosted : DccClass1DeepResidual boostLevel

namespace Erdos260KeystoneResidual

/-! ### The rebuild: keystone → wave-19 convergence surface -/

/-- **The keystone surface rebuilds the full wave-19 convergence surface**:
the band-reading dispatchers close the certified tower/run strata, the K.1
landing (`r = 0` truncation + density + the two atoms) rebuilds the cover
body, and the boost ladder rebuilds the class-1 deep field.  Composition
only. -/
def toConvergenceResidual (R : Erdos260KeystoneResidual) :
    Erdos260ConvergenceResidual where
  deepOrbitPin := R.deepOrbitPin
  towerEnumLow := dccTowerEnumLow_field_of_bandReading R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := dccRunNumericLow_field_of_bandReading R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGatesOffTable := R.returnGatesOffTable
  returnInteriorOffTable := R.returnInteriorOffTable
  densePackCoverOffTable := fun ctx h1 h2 h3 h4 h5 => by
    rcases Nat.eq_zero_or_pos ctx.n24CarryData.r with hr | hr
    · exact k1CoverBody_of_r_eq_zero ctx hr
    · exact k1CoverBody_of_density_cluster_spacing ctx
        (R.densePackDensityOffTable ctx h1 h3 h4 h5)
        (R.densePackClusterFloor ctx h1 h2 h3 h4 h5 hr)
        (R.densePackStartSpacing ctx h1 h2 h3 h4 h5 hr)
  densePackDensityOffTable := R.densePackDensityOffTable
  densePackInteriorOffTable := R.densePackInteriorOffTable
  class0Gates := R.class0Gates
  class1Deep := dccClass1Deep_field_of_boost R.class1Aligned R.class1DeepBoosted

/-- The final statement from the wave-20 keystone surface, through the proved
v19 convergence route (frontier + absorption + the fully-corrected six-phase
ledger). -/
theorem toStatement (R : Erdos260KeystoneResidual) : Erdos260Statement :=
  R.toConvergenceResidual.toStatement

end Erdos260KeystoneResidual

/-- **THE WAVE-20 ENDPOINT**: `Erdos260Statement` from the 15-field keystone
surface — the class-1 deep lane as the boost ladder, the densepack cover lane
as the two named K.1 atoms at `r ≥ 1`, the tower/run low lanes off the
certified band-free pairs, the class-0 gates with the exit-mass atom as
preferred supplier, and NO covering lane (it is provably dead).  Public
bridges only. -/
theorem erdos260_of_keystoneResidual (R : Erdos260KeystoneResidual) :
    Erdos260Statement :=
  R.toStatement

/-! ## Part 2.  The weakening witness (honest: atoms-assisted)

The FULL witness `Erdos260ConvergenceResidual → Erdos260KeystoneResidual` does
NOT hold: the two K.1 atoms genuinely strengthen the cover lane — the v19
cover body is a cardinality inequality, and a cardinality bound pins down
neither the per-window hit placement (`K1ClusterFloor`) nor the start spacing
(`K1StartSpacing`); the wave-19 L-spacing hunt for an unconditional spacing
proof came back negative.  Every OTHER fold is a pure weakening: the
band-reading guards are dropped, and the boost ladder at level `0` is an
equivalent re-cut of the v19 class-1 field (`dccResidual_zero_of_field`). -/

/-- **The atoms-assisted weakening witness**: a wave-19 convergence inhabitant
plus the two K.1 atoms (under the cover-field guards, at `r ≥ 1`) yields a
keystone inhabitant — all other fields transport by dropping the new
band-reading guards and reading the boost ladder at level `0`.  One direction
only; NO converse is claimed. -/
def keystoneResidual_of_convergenceResidual_and_atoms
    (R : Erdos260ConvergenceResidual)
    (hcl : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1ClusterFloor ctx)
    (hsp : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1StartSpacing ctx) :
    Erdos260KeystoneResidual where
  deepOrbitPin := R.deepOrbitPin
  towerEnumLow := fun ctx hesc hq haper h31 h213 _ hL hr hm0 =>
    R.towerEnumLow ctx hesc hq haper h31 h213 hL hr hm0
  towerEnumTail := R.towerEnumTail
  runNumericLow := fun ctx hpin hq _ hL hr =>
    R.runNumericLow ctx hpin hq hL hr
  runNumericTail := R.runNumericTail
  returnGatesOffTable := R.returnGatesOffTable
  returnInteriorOffTable := R.returnInteriorOffTable
  densePackClusterFloor := hcl
  densePackStartSpacing := hsp
  densePackDensityOffTable := R.densePackDensityOffTable
  densePackInteriorOffTable := R.densePackInteriorOffTable
  class0Gates := R.class0Gates
  boostLevel := 0
  class1Aligned := dccAlignedSupply_zero_free
  class1DeepBoosted := dccResidual_zero_of_field R.class1Deep

/-- Sanity commutation: a wave-19 inhabitant (with the atoms) reaches the
statement through the wave-20 keystone route as well. -/
theorem erdos260_of_convergenceResidual_via_keystone
    (R : Erdos260ConvergenceResidual)
    (hcl : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1ClusterFloor ctx)
    (hsp : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1StartSpacing ctx) :
    Erdos260Statement :=
  (keystoneResidual_of_convergenceResidual_and_atoms R hcl hsp).toStatement

/-! ## Part 3.  The supplier graph -/

/-- **The class-1 field rebuilt** (the boost-ladder consumption, exposed at the
capstone): the keystone's aligned supply + boosted residual rebuild the exact
v19 `class1Deep` field shape. -/
theorem keystoneClass1Deep_rebuilt (R : Erdos260KeystoneResidual) :
    ∀ ctx : ActualFailureContext,
      1274740 ≤ shellLadderDepth ctx → 82 ≤ ctx.n24CarryData.r →
      1 ≤ ctx.n24CarryData.r →
      (¬ ∃ cv bv Tv : ℕ,
        ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀, cv, bv, Tv)
            ∈ sreClass1ThresholdTable
          ∧ shellLadderDepth ctx ≤ Tv) →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  dccClass1Deep_field_of_boost R.class1Aligned R.class1DeepBoosted

/-- **The deep core from the spaced-share regime + the kept axis** (the
documented supplier route for `deepOrbitPin`'s unified core): the event-counting
regime `EmcOffPinSpacedShareRegime` together with the keystone's own
`deepOrbitPin` field rebuild the FULL `ExitMassControlCore`.  HONEST: at deep
scales the regime is satisfiable only at UNCERTIFIED parameters — every
certified `(c, b₄)` row overshoots the self-limiting threshold
`768·((63+c)/c)·b ≤ 31·c` (`emc2_deep_spacedShare_not_certified`); the open
target is the exit-light long cycles `b = 1`, `c ≥ 64`. -/
theorem keystoneExitMassCore_of_regime (h : EmcOffPinSpacedShareRegime)
    (R : Erdos260KeystoneResidual) : ExitMassControlCore :=
  emc2_core_of_regime_and_voiding h R.deepOrbitPin

/-- **The class-0 survivor mass row from the named atom** (the preferred-supplier
consumption): `MdcClass0ExitMassControl` — the class-0 FIBRE exit-mass cap, the
class-0 member of the exit-mass family — closes the survivor mass row in the
exact v18/v19 shape.  The full gates field needs the per-lane caps
(`mdcGates_of_class0ExitMassCaps`). -/
theorem keystoneClass0SurvivorRow_of_atom (h : MdcClass0ExitMassControl) :
    ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  mdcClass0SurvivorMass_of_atom h

/-- **`returnInteriorOffTable` from band-following onsets** (the wave-20 supply
route for the kept interior slot): per-context onsets at or below the top
band's start yield `DscTopBandExitFree`, which closes the off-table return
interior.  HONEST: the only in-tree band-following supplier (index
persistence) voids the whole class-0 fibre where it fires
(`mdcIndexPersistence_voids_class0`) — the slot is a genuine structural
residual, and its quantitative cost is the sharpened support floor
`mdc_topBandExitFree_support_floor`. -/
theorem keystoneReturnInterior_of_topBandOnsets
    (h : ∀ ctx : ActualFailureContext,
      fixedFamilyRecurrentBand ctx ≤ 4 ∧
      ∃ k₀, k₀ + (ctx.n24CarryData.r + 1) ≤ emF ctx + emW ctx ∧
        ∀ k, k₀ ≤ k →
          hitGap ctx.n24CarryData.a k = fixedFamilyRecurrentBand ctx) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  mdcReturnInteriorOffTable_of_topBandOnsets h

/-- **`densePackInteriorOffTable` from band-following onsets** (densepack
sibling, composed through the v19 consumption slot). -/
theorem keystoneDensePackInterior_of_topBandOnsets
    (h : ∀ ctx : ActualFailureContext,
      fixedFamilyRecurrentBand ctx ≤ 4 ∧
      ∃ k₀, k₀ + (ctx.n24CarryData.r + 1) ≤ emF ctx + emW ctx ∧
        ∀ k, k₀ ≤ k →
          hitGap ctx.n24CarryData.a k = fixedFamilyRecurrentBand ctx) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  convergenceDensePackInterior_of_topBandExitFree (mdcTopBandSlot_of_onsets h)

/-! ## Part 4.  The covering-lane collapse (the headline negative, recorded)

The covering/sibling lane carried by waves 14–19 as a PARALLEL endpoint is
provably a DEAD END: the covering demand is per-context unsatisfiable
(`coveringDemand_void` — the wave-10 sharp fire condition `17·g ≤ 2^24` at the
trivial representation, fed by the demand's own Q-cap, kills it at ALL odd
parts), so every covering-lane supply is EQUIVALENT to the emptiness of the
failure structure — never cheaper than the per-class surface above.  Future
waves must NOT attempt covering families.  The lane is therefore DROPPED from
the keystone story; the v19 `convergence_pinnedSplitParallel` endpoint is
superseded by the surface-free `erdos260_of_pinnedSplit_direct`. -/

/-- **The covering-supply collapse** (re-recorded at the capstone):
`OffCycleCoveringSupply` is context-emptiness — the whole remaining problem. -/
theorem keystone_coveringSupply_collapse :
    OffCycleCoveringSupply ↔ (∀ ctx : ActualFailureContext, False) :=
  offCycleCoveringSupply_iff_noContext

/-- **The pinned-split collapse**: the v19 two-piece covering residual
(`DeepPinnedQVoid` + `NonPinnedCoveringSupply`) is context-emptiness. -/
theorem keystone_pinnedSplit_collapse :
    (DeepPinnedQVoid ∧ NonPinnedCoveringSupply) ↔
      (∀ ctx : ActualFailureContext, False) :=
  pinnedSplit_iff_noContext

/-- **The sibling collapse**: the wave-14..19 discharged intermediate
`MultiScaleSiblingSupply` is context-emptiness as well. -/
theorem keystone_siblingSupply_collapse :
    MultiScaleSiblingSupply ↔ (∀ ctx : ActualFailureContext, False) :=
  multiScaleSiblingSupply_iff_noContext

/-- **The `u = 7` named atom survives the collapse** (it lives on the value
axis, not the covering lane): the pinned-Q voiding yields the sevenths pin
voiding — the `u = 7` stratum genuinely uncovered by the three open deep value
levers, inheriting the `X > 2^986891` floor (`seventhsPin_scale_floor`). -/
theorem keystoneSeventhsPinVoid_of_pinnedQVoid (h : DeepPinnedQVoid) :
    DeepSeventhsPinVoid :=
  deepSeventhsPinVoid_of_pinnedQVoid h

/-! ## Part 5.  Honest machine-readable status -/

/-- Machine-readable, honest status of the wave-20 keystone capstone. -/
def erdos260KeystoneCapstoneStatus : List String :=
  [ "SURFACE (15 fields): Erdos260KeystoneResidual = the wave-19 convergence " ++
      "surface rebased on the five wave-20 lanes.  NEW vs wave 19: (a) " ++
      "class1Deep is REPLACED by the boost ladder boostLevel + class1Aligned : " ++
      "DccClass1AlignedCountSupply v + class1DeepBoosted : DccClass1DeepResidual " ++
      "v - any 2^v-sparse aligned count closes the class-1 absorption on the " ++
      "whole band L <= 1274739*2^v (dccBoostGate, sharp at EVERY level v); " ++
      "level 0 is free and re-cuts the v19 field exactly " ++
      "(dccResidual_zero_of_field); (b) densePackCoverOffTable is REPLACED by " ++
      "the two named K.1 atoms at r >= 1 - densePackClusterFloor (K1ClusterFloor)" ++
      " + densePackStartSpacing (K1StartSpacing); the r = 0 stratum (ALL L <= " ++
      "15420) closes unconditionally (k1CoverBody_of_r_eq_zero, width truncates " ++
      "to 0, dichotomy k1CoverWidth_eq_zero_iff) and the K.1 landing " ++
      "k1CoverBody_of_density_cluster_spacing rebuilds the exact v19 cover body " ++
      "from density + the atoms; (c) towerEnumLow / runNumericLow are NARROWED " ++
      "off the certified band-free pairs (7 tower: (5,1),(5,2),(7,3),(51,1)," ++
      "(51,8),(63,1),(63,4); 6 run: (3,1),(21,3),(51,1),(51,8),(63,1),(63,4) - " ++
      "new kernel cycle certificates close them outright at every scale); (d) " ++
      "class0Gates KEPT with MdcClass0ExitMassControl as the named preferred " ++
      "supplier; (e) deepOrbitPin verbatim; (f) the interior/return/density " ++
      "fields verbatim; (g) NO covering lane.",
    "ENDPOINT (PROVED): erdos260_of_keystoneResidual : Erdos260KeystoneResidual " ++
      "-> Erdos260Statement, through toConvergenceResidual + the proved v19 " ++
      "route (frontier + absorption + the fully-corrected six-phase ledger).  " ++
      "WEAKENING WITNESS (HONEST, atoms-assisted): " ++
      "keystoneResidual_of_convergenceResidual_and_atoms - the FULL witness " ++
      "does NOT hold because the two K.1 atoms genuinely strengthen the cover " ++
      "lane (a cardinality inequality pins down neither hit placement nor start " ++
      "spacing; the wave-19 L-spacing hunt was negative); every other fold is a " ++
      "pure weakening (band-reading guards dropped, ladder read at level 0).",
    "THE COVERING-LANE COLLAPSE (THE HEADLINE NEGATIVE, AppendixNDescent): the " ++
      "covering demand is per-context UNSATISFIABLE (coveringDemand_void - the " ++
      "wave-10 sharp fire condition 17*g <= 2^24 at the trivial representation, " ++
      "fed by the demand's own Q-cap 2^493443, kills it at ALL odd parts, no " ++
      "pin needed).  OffCycleCoveringSupply, the pinned split DeepPinnedQVoid + " ++
      "NonPinnedCoveringSupply, and MultiScaleSiblingSupply are ALL equivalent " ++
      "to context-emptiness (keystone_coveringSupply_collapse / " ++
      "keystone_pinnedSplit_collapse / keystone_siblingSupply_collapse) - the " ++
      "covering/sibling targets of waves 14-19 were NEVER satisfiable; the " ++
      "lane can never be cheaper than the per-class surface.  WARNING to " ++
      "future waves: do NOT attempt covering families; the per-class surface " ++
      "is the unique route.  Survivor of the collapse: DeepSeventhsPinVoid " ++
      "(the u = 7 value-axis atom; deepSeventhsPinVoid_of_pinnedQVoid; floor " ++
      "X > 2^986891 inherited - seventhsPin_scale_floor).",
    "THE EVENT-COUNTING TRANSCRIPTION (ExitMassCoreTranscription): the in-tree " ++
      "mass is start-indexed, so the manuscript's in-cycle-uncharged ledger " ++
      "transcribes as event counting - the fibre-restricted exit mass " ++
      "emcFibreExitMass with the spaced overlap bound gives the master " ++
      "conditional emc2_cap_of_spacedShare (band <= 4 + EmcSpacedShareDatum " ++
      "=> the corrected per-class cap mass_i <= (31/1536)*X).  The regime " ++
      "SELF-LIMITS: 768*((r+c)/c)*b <= 31*c is forced " ++
      "(emc2_spacedShare_forces_threshold); 8 table pairs clear the absolute " ++
      "threshold (none deep, all c <= 54 < 63); at deep scales NO certified " ++
      "(c,b4) row survives (emcDeepProportionalClearedPairs_eq_nil) - the " ++
      "minimal residual is EmcSpacedShareDatum at UNCERTIFIED parameters: " ++
      "exit-light long cycles b = 1, c >= 64.  CONCRETE mechanical target: " ++
      "generate kernel certificates for long-period b4 = 1 pairs.  " ++
      "emc2_core_of_regime_and_voiding rebuilds the FULL ExitMassControlCore " ++
      "(keystoneExitMassCore_of_regime).",
    "THE K.1 LANDING (K1LandingClosure): the cover field's r = 0 stratum (ALL " ++
      "L <= 15420) is closed unconditionally; W = 0 iff r = 0; the landing " ++
      "k1CoverBody_of_density_cluster_spacing proves the v19 cover body from " ++
      "the two named atoms + density (disjoint W-blocks of actual points); " ++
      "the spacing atom is DISCHARGED on single-band-3-residue cycles with " ++
      "2*carryB Q + 1 <= c (k1StartSpacing_of_singleResidue) - at r = 1 the " ++
      "width is EXACTLY 2B + 1 (k1CoverWidth_eq_of_r_eq_one), so the b3 = 1 / " ++
      "r = 1 regime is clean; density anatomy: density <-> every genuine " ++
      "endpoint is an actual point (densePackEndpointDensity_iff_endpoints_mem).",
    "THE BINARY GAP-DEVIATION CLASSIFICATION (MissDistanceClosure): non-exit " ++
      "gaps deviate EXACTLY 0, so every class-0 member's window contains an " ++
      "exit (mdcFibre0_window_has_exit) and the miss-distance count route is " ++
      "provably inverted (mdc_missDistance_route_inverted).  Class 0 JOINS the " ++
      "exit-mass family: MdcClass0ExitMassControl (the class-0 FIBRE exit-mass " ++
      "cap) closes the survivor mass row (keystoneClass0SurvivorRow_of_atom); " ++
      "per-lane caps build the FULL gates field (mdcGates_of_class0ExitMassCaps)" ++
      "; the unrestricted form is REFUTED at factor 768/31 " ++
      "(mdcUnrestrictedAtom_refuted) - the fibre restriction IS the content.  " ++
      "The unified exit-mass family is now MdcClass0ExitMassControl (class 0) " ++
      "+ ExitMassControlOffPin (classes 3/4/5).",
    "THE TOP-BAND SLOT (kept): DscTopBandExitFree remains the structural " ++
      "residual for both interior fields; onset suppliers exist " ++
      "(keystoneReturnInterior_of_topBandOnsets / " ++
      "keystoneDensePackInterior_of_topBandOnsets) but the only in-tree " ++
      "band-following supplier voids the class-0 fibre where it fires " ++
      "(mdcIndexPersistence_voids_class0); refutation is impossible - the " ++
      "honest cost is the sharpened support floor " ++
      "(mdc_topBandExitFree_support_floor).",
    "FOLDS SKIPPED (honest): class0Gates is NOT replaced by the mdc atom (the " ++
      "atom closes only the survivor mass row; the gates demand per-member " ++
      "levels on three lanes); ExitMassControlCore stays a SUPPLIER, not a " ++
      "field (unchanged v19 reasoning - exitMassControl_iff_split); " ++
      "DscTopBandExitFree is not folded into the interiors; the density field " ++
      "keeps its full guard set (no r = 0 closure exists for density - its " ++
      "honest content is a position constraint, " ++
      "k1DensityField_position_constraint).",
    "WHAT REMAINS OPEN AFTER WAVE 20 (the honest core): (a) EmcSpacedShareDatum " ++
      "at uncertified parameters (exit-light long cycles b = 1, c >= 64) - " ++
      "equivalently the exit-share equidistribution; (b) " ++
      "DccClass1AlignedCountSupply v at v >= 1 (no in-tree class-1 " ++
      "carry-valuation) + the boosted residual / per-pair atoms " ++
      "DccClass1DeepPairAtomBoosted; (c) the unified exit-mass family: " ++
      "MdcClass0ExitMassControl + ExitMassControlOffPin (classes 0/3/4/5); (d) " ++
      "K1ClusterFloor + K1StartSpacing at r >= 2 (r = 1 spacing is discharged " ++
      "on single-residue cycles) + densePackEndpointDensity at b3 > 0; (e) " ++
      "DscTopBandExitFree; (f) the tower/run band-reading tails (towerEnumTail " ++
      "/ runNumericTail + the narrowed low lanes off the certified pairs); (g) " ++
      "DeepOrbitPinVoiding (with the u = 7 cousin DeepSeventhsPinVoid noted).",
    "HYGIENE: additive only - ONE new module; no sorry / admit / new axiom / " ++
      "native_decide; every key declaration passes #print axioms within " ++
      "[propext, Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem erdos260KeystoneCapstoneStatus_nonempty :
    erdos260KeystoneCapstoneStatus ≠ [] := by
  simp [erdos260KeystoneCapstoneStatus]

/-! ## Part 6.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]`
or fewer. -/

#print axioms Erdos260KeystoneResidual.toConvergenceResidual
#print axioms Erdos260KeystoneResidual.toStatement
#print axioms erdos260_of_keystoneResidual
#print axioms keystoneResidual_of_convergenceResidual_and_atoms
#print axioms erdos260_of_convergenceResidual_via_keystone
#print axioms keystoneClass1Deep_rebuilt
#print axioms keystoneExitMassCore_of_regime
#print axioms keystoneClass0SurvivorRow_of_atom
#print axioms keystoneReturnInterior_of_topBandOnsets
#print axioms keystoneDensePackInterior_of_topBandOnsets
#print axioms keystone_coveringSupply_collapse
#print axioms keystone_pinnedSplit_collapse
#print axioms keystone_siblingSupply_collapse
#print axioms keystoneSeventhsPinVoid_of_pinnedQVoid
#print axioms erdos260KeystoneCapstoneStatus_nonempty

end

end Erdos260
