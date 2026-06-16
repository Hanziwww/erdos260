import Erdos260.Erdos260KeystoneCapstone
import Erdos260.AppendixUPinVoiding
import Erdos260.V30OffPinExitCap
import Erdos260.V30Class1Realization
import Erdos260.V30StructuralAtoms
import Erdos260.V30PinSeventhsClosure

/-!
# V30 FINAL ASSEMBLY — `Erdos260V30Endpoint` (Lane H)

This module (NEW; it edits no existing file) ASSEMBLES the v30 reroute of
`proof_v4_repaired_core_v30.tex` into a single endpoint
`erdos260_of_v30Residual : Erdos260V30Residual -> Erdos260Statement`, wiring every
field of the proved in-tree reduction `erdos260_of_keystoneResidual`
(`Erdos260KeystoneCapstone`, 15 fields) to a v30 lane (A-G + the discharges) or,
where no in-tree lane bridge exists, to a precisely-typed residual atom.

`Erdos260V30Residual` is the DISTILLED remaining residual set: EXACTLY the genuine
carried atoms that remain after Lanes A-G, the Lane-D bounded-period discharge, and
the two build-repairs.  Nothing a lane proved UNCONDITIONALLY is carried here.

## Supplier map (keystone field <- lane / lemma)

* `deepOrbitPin`  <-  the v30 (C1) M.5/L.3 exit-mass core `v30_exitMassCore`, built
  from `exitMassControl_iff_split.mpr` of
  - the off-pin half = `(v30_offPin_allClasses offPin).1 : ExitMassControlOffPin`
    (Lane C, Appendices AB+AC+AD on top of R; RISK b/c/e in `offPin`), and
  - the pin half = `deepOrbitPinVoiding_of_confinement confinement`
    (Appendix U confinement atom).
  `deepOrbitPinVoiding_of_exitMassControl` then reads the deep orbit-pin voiding off
  the relocation floors.  DISCOVERY (see notes below): the orbit pins are NOT
  voided unconditionally in tree; they require the Appendix-U confinement atom
  `FixedPinCleanContinuation` (provably EQUIVALENT to `DeepOrbitPinVoiding`).
* `towerEnumLow / towerEnumTail / runNumericLow / runNumericTail`  <-  Lane G's
  read-tail exit-count bridge `V30ReadTailExitCount` (R6, Appendix P); its four
  fields are VERBATIM the keystone tower/run field shapes.
* `returnInteriorOffTable / densePackInteriorOffTable`  <-  Lane G's top-band
  push-forward `V30TopBandPushforward` (R5, Appendix P), via
  `v30ReturnInteriorOffTable_of_pushforward` / `v30DensePackInteriorOffTable_of_pushforward`.
* `densePackStartSpacing`  <-  Lane E's `v30DensePackStartSpacingField_of_spanRarity`
  from the densepack disjointification `K1SpanRarity` (R4, Appendix Q; the formal
  residue of the maximal-disjoint-family selection, = the SAME exit-mass currency as
  (C1) via `v30SpanRarity_of_localExitLight`).
* `boostLevel / class1Aligned / class1DeepBoosted`  <-  Lane A (C2, Appendices
  X+Y+AA): `boostLevel := 0`, `class1Aligned := dccAlignedSupply_zero_free` (FREE),
  `class1DeepBoosted := v30Class1Deep_of_carryRealization class1C class1Clean class1Realize`
  (the finite bisection table/descent — PROVED — refutes the atom the AA realization
  bridge would expose; `parityZero` is now PROVED inside `class1SystemOfCarry`, Lane J,
  so it has LEFT the residual — only the carry DATA + the AA bridge remain).
* `returnGatesOffTable`, `densePackClusterFloor`, `densePackDensityOffTable`,
  `class0Gates`  <-  carried RAW (DISCOVERY): these v18/v19 surface demands are NOT
  re-cut by the in-tree v30 lanes — the manuscript closes them through (C1)/Q, but no
  in-tree bridge from the off-pin cap to these exact field shapes was built (the
  class-0 atom `MdcClass0ExitMassControl` supplies only the survivor mass row, not the
  full `NarrowSupportClass0Gates`; the K.1 `|actualPoints|` cover/density and the
  cluster-floor are the negative-result L-spacing hunt residue).

## The value axis is FREE (Lane F, recorded)

The keystone tower fields carry the value-classification guard
`ordCompl[2] ctx.Q <= 7 -> not WindowPeriodic ctx` as an internal hypothesis; Lane F's
`windowPeriodicGuard_unconditional` discharges it for EVERY context (odd part `>= 9`
vacuous; odd part `<= 7` by `pinnedValue_windowPeriodic_void`).  So the `u = 7` hole
and the odd-part `>= 9` stratum add NO residual field — see `v30_value_axis_free`.

## What is now UNCONDITIONAL (not carried here)

`deepOrbitPin`'s **off-pin** unsafe core (the exit-light long cycle `b=1`, `c>=64`)
is EMPTY by Lane D-discharge (`unsafeOffPinCoreSet_eq_empty`); the value-axis guard
(odd `>= 9` / the towerEnumLow/Tail value slot) is free (Lane F); the class-1
bisection core `A_{1,v}^deep = empty` is PROVED (Lane A `v30Class1BisectionDefectEmpty`);
the Lane-D bounded-period retirement (D1 routing + D2 affordability, margin `7/1536`)
is unconditional and `(C1)`-free; the densepack `r = 0` stratum and the 13 band-free
tower/run pairs close outright.  These are consumed INSIDE the lanes and leave no
field in `Erdos260V30Residual`.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only.
-/

namespace Erdos260

noncomputable section

open V30Class1Realization V30StructuralAtoms

set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

/-! ## Part 1.  The distilled residual: `Erdos260V30Residual`

EXACTLY the genuine carried atoms remaining after the v30 lanes.  Each field cites its
v30 appendix home. -/

/-- **THE v30 REMAINING RESIDUAL SET.**  The honest distance-to-unconditional of the
v30 reroute, as it lands on the proved in-tree keystone reduction.  Ten carried
obligations (plus the two pure-DATA class-1 fields `class1C`/`class1Clean`);
everything a lane proved unconditionally is absent.  `parityZero` is now PROVED
(Lane J), so the residual shrank from eleven to ten. -/
structure Erdos260V30Residual where
  /-- **(C1) the off-pin exit-mass cap** — Appendices AB+AC+AD on top of R
  (`cor:ac-offpin-cap-closed`, v30 line 11603).  Bundles the off-pin SAFE-CONE regime
  (classes `{3,4,5}`) and the class-0 leg.  Internally each safe-cone cell datum
  carries the three genuinely measure-theoretic v30 inputs: the discrete measure
  preservation `c*ExitMass <= b*M_tot` (**RISK c**, `lem:r-cycle-map-preserves-measure`
  9110), the disjoint-cell ambient bound `M_tot <= X` (**RISK b**,
  `lem:ad-summed-ambient-support` 11671), and the fibre `c`-spacing / band `<= 4` from
  the AB recurrent-pair certificate (**RISK e**, `lem:ab-safe-complement-exhaustion`
  11315).  Supplies `ExitMassControlOffPin` + `MdcClass0ExitMassControl`
  (`v30_offPin_allClasses`). -/
  offPin : V30OffPinFullRegime
  /-- **The Appendix-U orbit-pin confinement atom** `FixedPinCleanContinuation`
  (`prop:u-direct-fixed-pin-voiding`, v30 line 9826): every deep (`X > 2^986891`)
  band-2/3/4-pinned context has an eventually-banded clean continuation.  This is the
  PIN half of the M.5/L.3 core.  HONEST: it is provably EQUIVALENT to the conclusion
  `DeepOrbitPinVoiding` (`fixedPinCleanContinuation_iff_deepOrbitPinVoiding`) — the
  deep orbit pins are NOT voided unconditionally in tree. -/
  confinement : FixedPinCleanContinuation
  /-- **(C2) the class-1 boundary-carry DATA** over the representative finite class-1
  quotient `G_1 = ZMod 6` (Appendices X/Y, `def:y-formal-row`): the `π₁`-projected
  boundary-carry function.  Pure DATA, NOT an obligation — the formal system is built
  internally as `class1SystemOfCarry class1C class1Clean`, whose one-cell parity rule
  `parityZero` (`lem:x-depth-zero-void`) is now PROVED (Lane J,
  `parityZero_of_tagCatchesDepthZero`), not carried.  All of Y.1/Y.2/Y.3/Y.4 (cocycle
  additivity, the finite midpoint table, the well-founded depth descent, atom voiding)
  is PROVED in Lane A. -/
  class1C : ℕ → ZMod 6
  /-- The cut-wise cleanliness data of the corrected class-1 ledger (pure DATA). -/
  class1Clean : ℕ → Bool
  /-- **(C2) the Appendix-AA faithful realization bridge** for the concrete tag-faithful
  system `class1SystemOfCarry class1C class1Clean`
  (`prop:aa-c2-closed` 11034 / `cor:aa-r2-closed` 11056): a failed deep `(R2)` ledger row
  is realized as a retained formal class-1 atom.  The per-context normal-form
  identification needing the in-tree audited priority selector.  (Lane K
  `ledgerRealizes_iff_deepResidual` shows this field is EXACTLY the deep class-1 cap
  `DccClass1DeepResidual 0`, independent of the carry data.) -/
  class1Realize : V30Class1LedgerRealizesFormalRow
    (class1SystemOfCarry class1C class1Clean)
  /-- **(R5) the top-band push-forward exit cap** — Appendix P
  (`prop:p-top-band-routing-closed`, v30 line 8633): every top-band L.3.1 exit is
  routed to the (R3) fibre-restricted exit-mass ledger, so the top-band deviation mass
  sits below the heaviness floor `Y = L/64`.  The (C1)/(R3) deliverable in its
  top-band-localized shape (Lane C `v30_topBandPushforward_of_cap`). -/
  topBand : V30TopBandPushforward
  /-- **(R6) the read-tail exit-count bridge** — Appendix P
  (`prop:p-readtail-pushforward-closed`, v30 line 8689): the four band-reading
  tower/run closing inequalities in the I.3/L.3 first-entry/first-exit event-fibre
  count form.  Its four fields are VERBATIM the keystone tower/run field shapes. -/
  readTail : V30ReadTailExitCount
  /-- **(R4) the densepack disjointification regime** — Appendix Q
  (`prop:q-densepack-r4-removed`, v30 line 8907): one genuine start per width-`W` span
  (`K1SpanRarity`), the formal residue of the maximal pairwise-disjoint marker family.
  Its honest in-tree supplier is per-span exit-lightness `K1LocalExitLight` at band
  `<= 4` (`v30SpanRarity_of_localExitLight`) — the SAME exit-mass currency as (C1).
  Feeds the keystone `densePackStartSpacing` field via
  `v30DensePackStartSpacingField_of_spanRarity`. -/
  spanRarity : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
    ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
    K1SpanRarity ctx
  /-- **(R4) the K.1.1 cluster-floor atom** `K1ClusterFloor` (per-window hit placement),
  off the `b3 = 0` table at `r >= 1`.  DISCOVERY: NOT re-cut by the in-tree v30 lanes —
  the support-count route (Lane E) ELIMINATES it but does not rebuild the keystone
  cover field; on the keystone route it is the v18/v19 surface demand verbatim. -/
  clusterFloor : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
    ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
    K1ClusterFloor ctx
  /-- **(R4) the K.1.1 coarea hit-density field** `densePackEndpointDensity`, off the
  `b3 = 0` table.  DISCOVERY: carried raw — the support-count route consumes no
  density (`v30DensePackDensity_of_emptyStarts` only closes it where the starts
  vanish); the `b3 > 0` content is the K.1 landing the L-spacing hunt left open. -/
  density : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    densePackEndpointDensity ctx
  /-- **(R4-return) the class-4 return count gates**, off the `b2 = 0` table.
  DISCOVERY: carried raw — no in-tree v30 lane rebuilds `ReturnGatesBodyUngated` from
  the off-pin cap; it is the v18/v19 surface demand verbatim (the off-table `b2 > 0`
  cycle-count content). -/
  returnGates : ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
    ¬ OrbitBandPinned ctx 2 →
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- **The three narrow-support class-0 gate lanes** `NarrowSupportClass0Gates`.
  DISCOVERY: carried raw — Lane C's class-0 atom `MdcClass0ExitMassControl` closes only
  the survivor mass row (`keystoneClass0SurvivorRow_of_atom`); the full gates field
  demands per-member levels on three lanes (`mdcGates_of_class0ExitMassCaps` needs the
  per-lane caps `mdcClass0ExitMass <= s*Y`), which the atom does not supply. -/
  class0Gates : NarrowSupportClass0Gates

/-! ## Part 2.  The v30 (C1) M.5/L.3 exit-mass core and the off-pin deliverables -/

/-- **The v30 (C1) M.5/L.3 exit-mass core**, assembled from the residual: the off-pin
class caps (`offPin`, RISK b/c/e) plus the Appendix-U pin confinement
(`confinement`).  By `exitMassControl_iff_split` the full `ExitMassControlCore` is
exactly (deep orbit-pin voiding) AND (the pin-free off-pin caps) — this is the named
M.5/L.3 object the v30 manuscript closes as (C1)+(Appendix U). -/
theorem v30_exitMassCore (R : Erdos260V30Residual) : ExitMassControlCore :=
  exitMassControl_iff_split.mpr
    ⟨deepOrbitPinVoiding_of_confinement R.confinement, (v30_offPin_allClasses R.offPin).1⟩

/-- **The (C1) off-pin deliverables** carried in the residual: the per-class off-pin
caps `ExitMassControlOffPin` (classes `{3,4,5}`) and the class-0 leg
`MdcClass0ExitMassControl` (class `0`) — the AD-summed off-pin cap over `{0,3,4,5}`. -/
theorem v30_offPin_deliverables (R : Erdos260V30Residual) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  v30_offPin_allClasses R.offPin

/-- **The deep orbit-pin voiding** read off the (C1) core via the relocation floors
(`deepOrbitPinVoiding_of_exitMassControl`).  HONEST: the bare field is already supplied
by `confinement` alone (`deepOrbitPinVoiding_of_confinement`); routing through the core
records the v30-faithful M.5/L.3 supplier (the off-pin caps strengthen it to the full
core) without weakening the result. -/
theorem v30_deepOrbitPin (R : Erdos260V30Residual) : DeepOrbitPinVoiding :=
  deepOrbitPinVoiding_of_exitMassControl (v30_exitMassCore R)

/-! ## Part 3.  The 15-field keystone construction and the endpoint -/

/-- **The v30 residual builds the proved 15-field keystone surface.**  Each field is
sourced from its lane (see the supplier map in the module header); the four raw fields
(`returnGatesOffTable`, `densePackClusterFloor`, `densePackDensityOffTable`,
`class0Gates`) are the v18/v19 surface demands the in-tree v30 lanes do not re-cut. -/
def Erdos260V30Residual.toKeystone (R : Erdos260V30Residual) : Erdos260KeystoneResidual where
  deepOrbitPin := v30_deepOrbitPin R
  towerEnumLow := R.readTail.towerLow
  towerEnumTail := R.readTail.towerTail
  runNumericLow := R.readTail.runLow
  runNumericTail := R.readTail.runTail
  returnGatesOffTable := R.returnGates
  returnInteriorOffTable := v30ReturnInteriorOffTable_of_pushforward R.topBand
  densePackClusterFloor := R.clusterFloor
  densePackStartSpacing := v30DensePackStartSpacingField_of_spanRarity R.spanRarity
  densePackDensityOffTable := R.density
  densePackInteriorOffTable := v30DensePackInteriorOffTable_of_pushforward R.topBand
  class0Gates := R.class0Gates
  boostLevel := 0
  class1Aligned := dccAlignedSupply_zero_free
  class1DeepBoosted := v30Class1Deep_of_carryRealization R.class1C R.class1Clean R.class1Realize

/-- **THE v30 ENDPOINT**: `Erdos260Statement` from the distilled v30 residual, through
the keystone surface and the proved reduction `erdos260_of_keystoneResidual` (which
routes through the wave-19 convergence surface and the fully-corrected six-phase
ledger). -/
theorem erdos260_of_v30Residual (R : Erdos260V30Residual) : Erdos260Statement :=
  erdos260_of_keystoneResidual R.toKeystone

/-! ## Part 4.  The value axis is free (Lane F, recorded) -/

/-- **The value-classification guard slot is discharged FOR FREE** when the keystone
tower field of the v30 residual is consumed: Lane F's `windowPeriodicGuard_unconditional`
fills the `ordCompl[2] ctx.Q <= 7 -> not WindowPeriodic ctx` hypothesis at EVERY context
(odd part `>= 9` vacuous, odd part `<= 7` by `pinnedValue_windowPeriodic_void`).  So the
`u = 7` hole and the odd-part `>= 9` stratum are SUBSUMED and add no residual field. -/
theorem v30_value_axis_free (R : Erdos260V30Residual) (ctx : ActualFailureContext)
    (h1 : TowerModulusEnumEscapeV2 ctx)
    (h2 : (class1SlopeDatum ctx).q < 107)
    (h4 : ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1))
    (h5 : ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3))
    (h6 : ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
            ∉ dccTowerBand4FreeLowPairs)
    (h7 : 986888 ≤ shellLadderDepth ctx)
    (h8 : 63 ≤ ctx.n24CarryData.r)
    (h9 : 3 ≤ towerSparsityBlock ctx) :
    Class2CycleInequality ctx :=
  keystone_towerEnumLow_value_axis_free R.toKeystone ctx h1 h2 h4 h5 h6 h7 h8 h9

/-- **The `u = 7` lane reduces exactly to its exit-active residual** (Lane F): the full
`DeepSeventhsPinVoid` is EQUIVALENT to `SeventhsExitActiveResidual` (the periodic half
is already void), recorded so the `u = 7` content is not hidden.  It is NOT a field of
`Erdos260V30Residual`: the keystone surface consumes the value classification only via
the tower guard, which is free. -/
theorem v30_sevenths_reduces : DeepSeventhsPinVoid ↔ SeventhsExitActiveResidual :=
  deepSeventhsPinVoid_iff_exitActive

/-! ## Part 5.  Honest machine-readable status -/

/-- Honest, machine-readable status of the v30 final assembly (Lane H). -/
def erdos260V30EndpointStatus : List String :=
  [ "LANE H (Erdos260V30Endpoint) — final assembly of the v30 reroute " ++
      "(proof_v4_repaired_core_v30.tex) onto the proved in-tree reduction " ++
      "erdos260_of_keystoneResidual (15 fields).  ENDPOINT (PROVED): " ++
      "erdos260_of_v30Residual : Erdos260V30Residual -> Erdos260Statement, via " ++
      "Erdos260V30Residual.toKeystone + erdos260_of_keystoneResidual.  Additive: ONE " ++
      "new module, no existing .lean file edited.",
    "RESIDUAL (10 carried atoms, the EXACT distance-to-unconditional; parityZero " ++
      "DISCHARGED, shrink 11->10): offPin " ++
      "(V30OffPinFullRegime = (C1), RISK b/c/e); confinement (FixedPinCleanContinuation " ++
      "= Appendix U orbit-pin atom); class1Realize (Appendix AA bridge) = (C2), now over " ++
      "the carry DATA (class1C, class1Clean) built into class1SystemOfCarry whose " ++
      "parityZero is PROVED (Lane J) - so the Appendix X depth-0 parity rule has LEFT " ++
      "the residual; topBand (V30TopBandPushforward = R5); readTail " ++
      "(V30ReadTailExitCount = R6); " ++
      "spanRarity (K1SpanRarity regime = R4 disjointification, exit-mass currency); and " ++
      "the four raw v18/v19 surface demands clusterFloor (K1ClusterFloor), density " ++
      "(densePackEndpointDensity), returnGates (ReturnGatesBodyUngated), class0Gates " ++
      "(NarrowSupportClass0Gates).",
    "SUPPLIER MAP (keystone field <- source): deepOrbitPin <- v30_exitMassCore " ++
      "(exitMassControl_iff_split.mpr of (v30_offPin_allClasses offPin).1 = " ++
      "ExitMassControlOffPin AND deepOrbitPinVoiding_of_confinement confinement) then " ++
      "deepOrbitPinVoiding_of_exitMassControl; towerEnumLow/Tail + runNumericLow/Tail " ++
      "<- readTail (verbatim shapes); returnInteriorOffTable + densePackInteriorOffTable " ++
      "<- v30{Return,DensePack}InteriorOffTable_of_pushforward topBand; " ++
      "densePackStartSpacing <- v30DensePackStartSpacingField_of_spanRarity spanRarity; " ++
      "boostLevel:=0 + class1Aligned:=dccAlignedSupply_zero_free (FREE) + " ++
      "class1DeepBoosted:=v30Class1Deep_of_carryRealization class1C class1Clean class1Realize " ++
      "(parityZero PROVED inside class1SystemOfCarry); " ++
      "returnGatesOffTable/densePackClusterFloor/densePackDensityOffTable/class0Gates " ++
      "<- carried raw.",
    "DISCOVERY 1 — deepOrbitPin is NOT unconditional. deepOrbitPinVoiding_of_confinement " ++
      "consumes FixedPinCleanContinuation, which is PROVABLY EQUIVALENT to its conclusion " ++
      "DeepOrbitPinVoiding (fixedPinCleanContinuation_iff_deepOrbitPinVoiding).  The " ++
      "off-pin cap CANNOT supply the pins: ExitMassControlCore <-> DeepOrbitPinVoiding " ++
      "AND ExitMassControlOffPin (exitMassControl_iff_split), so the core CONTAINS the " ++
      "pin voiding as an input.  The pins need the Appendix-U confinement atom (or the " ++
      "three deep value levers).  It is a genuine carried residual.",
    "DISCOVERY 2 — four v18/v19 surface demands are not re-cut by the in-tree v30 " ++
      "lanes.  returnGatesOffTable, densePackClusterFloor, densePackDensityOffTable and " ++
      "class0Gates have no in-tree bridge from the (C1) off-pin cap: " ++
      "MdcClass0ExitMassControl closes only the class-0 survivor mass row, not the full " ++
      "NarrowSupportClass0Gates; the K.1 |actualPoints| cover/density and the " ++
      "cluster-floor are the negative L-spacing hunt residue.  The v30 manuscript closes " ++
      "them via (C1)/Q at the ledger level, below the in-tree surface granularity.",
    "DISCOVERY 3 — the per-span / top-band exit caps are SEPARATE hypotheses, not " ++
      "consequences of V30OffPinFullRegime.  The densepack disjointification uses a " ++
      "per-span exit cap (K1LocalExitLight, via spanRarity) and the interiors use a " ++
      "top-band exit cap (V30TopBandPushforward); both are in the (C1) exit-mass " ++
      "currency but are distinct localized caps, carried as topBand + spanRarity.",
    "UNCONDITIONAL (consumed inside lanes, NO residual field): (i) the off-pin unsafe " ++
      "exit-light long-cycle core b=1,c>=64 is EMPTY (Lane D-discharge " ++
      "unsafeOffPinCoreSet_eq_empty, (C1)-free, margin 7/1536); (ii) the value-axis " ++
      "guard (u=7 + odd part >= 9) is free (Lane F windowPeriodicGuard_unconditional, " ++
      "v30_value_axis_free); (iii) the class-1 bisection core A_{1,v}^deep = empty " ++
      "(Lane A v30Class1BisectionDefectEmpty); (iv) the Lane-D bounded-period " ++
      "retirement (D1 routing + D2 affordability); (v) the densepack r=0 stratum and " ++
      "the 13 band-free tower/run pairs.",
    "u=7 RECORD (v30_sevenths_reduces): DeepSeventhsPinVoid <-> SeventhsExitActiveResidual " ++
      "(Lane F) - the periodic half is unconditionally void; the exit-active half is the " ++
      "(C1)+(C2) content already carried by offPin + class1C/class1Clean/class1Realize.  Not a " ++
      "separate field.",
    "VERDICT (honest, non-triumphal): erdos260_of_v30Residual is PROVED and sorryAx-free, " ++
      "but it is a CONDITIONAL endpoint - it depends on 10 genuine residual atoms " ++
      "(parityZero discharged via Lane J; class1System replaced by the carry DATA " ++
      "class1C/class1Clean).  v30 " ++
      "is plausibly unconditional in the manuscript, and the soundest lanes (the class-1 " ++
      "bisection core, the off-pin unsafe-core emptiness, the bounded-period affordability, " ++
      "the value axis) ARE discharged in tree; what remains is real formalization work, " ++
      "chiefly the measure-theoretic (C1) inputs (RISK b/c/e in offPin), the Appendix-AA " ++
      "realization bridge (class1Realize) and the Appendix-U confinement (confinement), " ++
      "plus the four v18/v19 surface demands no v30 lane re-cuts.",
    "AXIOMS: erdos260_of_v30Residual and every key declaration report exactly " ++
      "[propext, Classical.choice, Quot.sound] or fewer; no sorry / admit / " ++
      "native_decide; no new axiom." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem erdos260V30EndpointStatus_nonempty : erdos260V30EndpointStatus ≠ [] := by
  unfold erdos260V30EndpointStatus
  simp

/-! ## Part 6.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]` or
fewer. -/

#print axioms Erdos260V30Residual
#print axioms erdos260_of_v30Residual
#print axioms Erdos260V30Residual.toKeystone
#print axioms v30_exitMassCore
#print axioms v30_offPin_deliverables
#print axioms v30_deepOrbitPin
#print axioms v30_value_axis_free
#print axioms v30_sevenths_reduces
#print axioms erdos260V30EndpointStatus_nonempty

end

end Erdos260
