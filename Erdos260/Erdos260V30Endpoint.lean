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

/-- V30 residual surface with the off-pin field refined to the concrete
coordinate-split zero-collar O2 provider.  This does not close the remaining
mathematics; it replaces the abstract `(C1)` atom by the lower-level provider
that has to be built from the TeX AK/AD/AB/R inputs. -/
structure Erdos260V30O2CollarCoordinateResidual {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int) where
  /-- Concrete zero-collar O2/AB/R provider for the four off-pin classes. -/
  offPinO2 : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs (β := β) (A := A) P₀ Q
  /-- Appendix-U orbit-pin confinement atom, unchanged from `Erdos260V30Residual`. -/
  confinement : FixedPinCleanContinuation
  /-- Class-1 boundary-carry data, unchanged. -/
  class1C : ℕ -> ZMod 6
  /-- Class-1 cleanliness data, unchanged. -/
  class1Clean : ℕ -> Bool
  /-- Appendix-AA realization bridge over the carried class-1 data. -/
  class1Realize : V30Class1LedgerRealizesFormalRow
    (class1SystemOfCarry class1C class1Clean)
  /-- Top-band push-forward exit cap, unchanged. -/
  topBand : V30TopBandPushforward
  /-- Read-tail exit-count bridge, unchanged. -/
  readTail : V30ReadTailExitCount
  /-- Densepack span-rarity regime, unchanged. -/
  spanRarity : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx ->
    ¬ Band3PinnedWide ctx -> ¬ Class3CycleBand3Free ctx ->
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) ->
    ¬ DensePackDatumClosed ctx -> 1 ≤ ctx.n24CarryData.r ->
    K1SpanRarity ctx
  /-- Raw K.1 cluster-floor residual, unchanged. -/
  clusterFloor : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx ->
    ¬ Band3PinnedWide ctx -> ¬ Class3CycleBand3Free ctx ->
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) ->
    ¬ DensePackDatumClosed ctx -> 1 ≤ ctx.n24CarryData.r ->
    K1ClusterFloor ctx
  /-- Raw densepack density residual, unchanged. -/
  density : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx ->
    ¬ Class3CycleBand3Free ctx ->
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) ->
    ¬ DensePackDatumClosed ctx ->
    densePackEndpointDensity ctx
  /-- Raw return-gates residual, unchanged. -/
  returnGates : ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx ->
    ¬ OrbitBandPinned ctx 2 ->
    ¬ ReturnB2FreeDatum ctx -> ¬ ReturnB2OneSpacedDatum ctx ->
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) ->
    ReturnGatesBodyUngated ctx
  /-- Raw narrow-support class-0 gate residual, unchanged. -/
  class0Gates : NarrowSupportClass0Gates

namespace Erdos260V30O2CollarCoordinateResidual

/-- Project the concrete zero-collar O2 off-pin provider surface back to the
existing v30 residual API. -/
def toV30Residual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    Erdos260V30Residual where
  offPin := v30OffPinFullRegime_of_o2_collar_supply_coordinate_full_provider
    P₀ Q R.offPinO2
  confinement := R.confinement
  class1C := R.class1C
  class1Clean := R.class1Clean
  class1Realize := R.class1Realize
  topBand := R.topBand
  readTail := R.readTail
  spanRarity := R.spanRarity
  clusterFloor := R.clusterFloor
  density := R.density
  returnGates := R.returnGates
  class0Gates := R.class0Gates

/-- The concrete zero-collar O2 off-pin provider supplies the same off-pin
deliverables consumed by the v30 endpoint. -/
theorem offPinDeliverables {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  v30_offPin_allClasses_of_o2_collar_supply_coordinate_full_provider P₀ Q R.offPinO2

/-- The coordinate O2 surface carries the same M.5/L.3 exit-mass core through
its projection to the v30 residual API. -/
theorem exitMassCore {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V30O2CollarCoordinateResidual beta A hdec P Q) :
    ExitMassControlCore :=
  exitMassControl_iff_split.mpr
    ⟨deepOrbitPinVoiding_of_confinement R.confinement, (offPinDeliverables R).1⟩

/-- The coordinate O2 surface carries the same deep orbit-pin voiding through
its projection to the v30 residual API. -/
theorem deepOrbitPinVoiding {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V30O2CollarCoordinateResidual beta A hdec P Q) :
    DeepOrbitPinVoiding :=
  deepOrbitPinVoiding_of_exitMassControl (exitMassCore R)

end Erdos260V30O2CollarCoordinateResidual

/-- V30 residual surface with the off-pin field refined to the coordinate-split
O2 collar provider retaining finite errors, plus explicit proofs that every
collar is actually zero.  This is the endpoint-facing form of the
`toZeroCollarProvider` bridge from Lane C. -/
structure Erdos260V30O2CollarCoordinateZeroErrorResidual {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int) where
  /-- Concrete coordinate O2/AB/R provider for the four off-pin classes, retaining
  collars before the zero-error proofs are applied. -/
  offPinO2 : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
    (β := β) (A := A) P₀ Q
  /-- The class-3 collar is genuinely zero on every pin-free deep context. -/
  class3Zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)),
      (offPinO2.class3 ctx hX hn2 hn3 hn4).collar.card = 0
  /-- The class-4 collar is genuinely zero on every pin-free deep context. -/
  class4Zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)),
      (offPinO2.class4 ctx hX hn2 hn3 hn4).collar.card = 0
  /-- The class-5 collar is genuinely zero on every pin-free deep context. -/
  class5Zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)),
      (offPinO2.class5 ctx hX hn2 hn3 hn4).collar.card = 0
  /-- The class-0 collar is genuinely zero on every class-0 survivor context. -/
  class0Zero : forall (ctx : ActualFailureContext) (hsurv : Class0DatumSurvivor ctx),
    (offPinO2.class0 ctx hsurv).collar.card = 0
  /-- Appendix-U orbit-pin confinement atom, unchanged from `Erdos260V30Residual`. -/
  confinement : FixedPinCleanContinuation
  /-- Class-1 boundary-carry data, unchanged. -/
  class1C : ℕ -> ZMod 6
  /-- Class-1 cleanliness data, unchanged. -/
  class1Clean : ℕ -> Bool
  /-- Appendix-AA realization bridge over the carried class-1 data. -/
  class1Realize : V30Class1LedgerRealizesFormalRow
    (class1SystemOfCarry class1C class1Clean)
  /-- Top-band push-forward exit cap, unchanged. -/
  topBand : V30TopBandPushforward
  /-- Read-tail exit-count bridge, unchanged. -/
  readTail : V30ReadTailExitCount
  /-- Densepack span-rarity regime, unchanged. -/
  spanRarity : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx ->
    ¬ Band3PinnedWide ctx -> ¬ Class3CycleBand3Free ctx ->
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) ->
    ¬ DensePackDatumClosed ctx -> 1 ≤ ctx.n24CarryData.r ->
    K1SpanRarity ctx
  /-- Raw K.1 cluster-floor residual, unchanged. -/
  clusterFloor : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx ->
    ¬ Band3PinnedWide ctx -> ¬ Class3CycleBand3Free ctx ->
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) ->
    ¬ DensePackDatumClosed ctx -> 1 ≤ ctx.n24CarryData.r ->
    K1ClusterFloor ctx
  /-- Raw densepack density residual, unchanged. -/
  density : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx ->
    ¬ Class3CycleBand3Free ctx ->
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) ->
    ¬ DensePackDatumClosed ctx ->
    densePackEndpointDensity ctx
  /-- Raw return-gates residual, unchanged. -/
  returnGates : ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx ->
    ¬ OrbitBandPinned ctx 2 ->
    ¬ ReturnB2FreeDatum ctx -> ¬ ReturnB2OneSpacedDatum ctx ->
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) ->
    ReturnGatesBodyUngated ctx
  /-- Raw narrow-support class-0 gate residual, unchanged. -/
  class0Gates : NarrowSupportClass0Gates

namespace Erdos260V30O2CollarCoordinateZeroErrorResidual

/-- Convert the finite-error/zero-collar endpoint surface to the existing
coordinate zero-collar endpoint surface. -/
def toO2CollarCoordinateResidual {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q where
  offPinO2 :=
    V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.toZeroCollarProvider
      R.offPinO2 R.class3Zero R.class4Zero R.class5Zero R.class0Zero
  confinement := R.confinement
  class1C := R.class1C
  class1Clean := R.class1Clean
  class1Realize := R.class1Realize
  topBand := R.topBand
  readTail := R.readTail
  spanRarity := R.spanRarity
  clusterFloor := R.clusterFloor
  density := R.density
  returnGates := R.returnGates
  class0Gates := R.class0Gates

/-- Project the finite-error/zero-collar endpoint surface back to the existing
v30 residual API. -/
def toV30Residual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V30Residual :=
  R.toO2CollarCoordinateResidual.toV30Residual

/-- The finite-error/zero-collar off-pin provider supplies the same off-pin
deliverables consumed by the v30 endpoint. -/
theorem offPinDeliverables {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.allClasses_of_zeroCollars
    R.offPinO2 R.class3Zero R.class4Zero R.class5Zero R.class0Zero

/-- The finite-error/zero-collar surface carries the same M.5/L.3 exit-mass core
through its projection to the v30 residual API. -/
theorem exitMassCore {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V30O2CollarCoordinateZeroErrorResidual beta A hdec P Q) :
    ExitMassControlCore :=
  exitMassControl_iff_split.mpr
    ⟨deepOrbitPinVoiding_of_confinement R.confinement, (offPinDeliverables R).1⟩

/-- The finite-error/zero-collar surface carries the same deep orbit-pin voiding
through its projection to the v30 residual API. -/
theorem deepOrbitPinVoiding {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V30O2CollarCoordinateZeroErrorResidual beta A hdec P Q) :
    DeepOrbitPinVoiding :=
  deepOrbitPinVoiding_of_exitMassControl (exitMassCore R)

end Erdos260V30O2CollarCoordinateZeroErrorResidual

/-- V30 residual surface with the off-pin field refined to the coordinate-split
O2 collar provider whose four collars are literally empty.  This is the endpoint
surface closest to the TeX wording that the endpoint/carry collars have been
deleted, rather than merely carrying their cardinalities as zero. -/
structure Erdos260V30O2CollarCoordinateEmptyCollarResidual {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int) where
  /-- Concrete coordinate O2/AB/R provider with literal empty-collar facts for
  the four off-pin classes. -/
  offPinO2 : V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs
    (β := β) (A := A) P₀ Q
  /-- Appendix-U orbit-pin confinement atom, unchanged from `Erdos260V30Residual`. -/
  confinement : FixedPinCleanContinuation
  /-- Class-1 boundary-carry data, unchanged. -/
  class1C : Nat -> ZMod 6
  /-- Class-1 cleanliness data, unchanged. -/
  class1Clean : Nat -> Bool
  /-- Appendix-AA realization bridge over the carried class-1 data. -/
  class1Realize : V30Class1LedgerRealizesFormalRow
    (class1SystemOfCarry class1C class1Clean)
  /-- Top-band push-forward exit cap, unchanged. -/
  topBand : V30TopBandPushforward
  /-- Read-tail exit-count bridge, unchanged. -/
  readTail : V30ReadTailExitCount
  /-- Densepack span-rarity regime, unchanged. -/
  spanRarity : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx ->
    ¬ Band3PinnedWide ctx -> ¬ Class3CycleBand3Free ctx ->
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) ->
    ¬ DensePackDatumClosed ctx -> 1 ≤ ctx.n24CarryData.r ->
    K1SpanRarity ctx
  /-- Raw K.1 cluster-floor residual, unchanged. -/
  clusterFloor : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx ->
    ¬ Band3PinnedWide ctx -> ¬ Class3CycleBand3Free ctx ->
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) ->
    ¬ DensePackDatumClosed ctx -> 1 ≤ ctx.n24CarryData.r ->
    K1ClusterFloor ctx
  /-- Raw densepack density residual, unchanged. -/
  density : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx ->
    ¬ Class3CycleBand3Free ctx ->
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) ->
    ¬ DensePackDatumClosed ctx ->
    densePackEndpointDensity ctx
  /-- Raw return-gates residual, unchanged. -/
  returnGates : ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx ->
    ¬ OrbitBandPinned ctx 2 ->
    ¬ ReturnB2FreeDatum ctx -> ¬ ReturnB2OneSpacedDatum ctx ->
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) ->
    ReturnGatesBodyUngated ctx
  /-- Raw narrow-support class-0 gate residual, unchanged. -/
  class0Gates : NarrowSupportClass0Gates

namespace Erdos260V30O2CollarCoordinateEmptyCollarResidual

/-- Convert the empty-collar endpoint surface to the existing coordinate
zero-collar endpoint surface. -/
def toO2CollarCoordinateResidual {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q where
  offPinO2 :=
    V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.toZeroCollarProvider
      R.offPinO2
  confinement := R.confinement
  class1C := R.class1C
  class1Clean := R.class1Clean
  class1Realize := R.class1Realize
  topBand := R.topBand
  readTail := R.readTail
  spanRarity := R.spanRarity
  clusterFloor := R.clusterFloor
  density := R.density
  returnGates := R.returnGates
  class0Gates := R.class0Gates

/-- Project the empty-collar endpoint surface back to the existing v30 residual
API. -/
def toV30Residual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V30Residual :=
  R.toO2CollarCoordinateResidual.toV30Residual

/-- The empty-collar O2 provider supplies the same off-pin deliverables consumed
by the v30 endpoint. -/
theorem offPinDeliverables {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.allClasses
    R.offPinO2

/-- The empty-collar O2 surface carries the same M.5/L.3 exit-mass core through
its projection to the v30 residual API. -/
theorem exitMassCore {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V30O2CollarCoordinateEmptyCollarResidual beta A hdec P Q) :
    ExitMassControlCore :=
  exitMassControl_iff_split.mpr
    ⟨deepOrbitPinVoiding_of_confinement R.confinement, (offPinDeliverables R).1⟩

/-- The empty-collar O2 surface carries the same deep orbit-pin voiding through
its projection to the v30 residual API. -/
theorem deepOrbitPinVoiding {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V30O2CollarCoordinateEmptyCollarResidual beta A hdec P Q) :
    DeepOrbitPinVoiding :=
  deepOrbitPinVoiding_of_exitMassControl (exitMassCore R)

end Erdos260V30O2CollarCoordinateEmptyCollarResidual

/-! ## Part 1a.  Localized exit-cap suppliers for R4/R5 -/

/-- Localized exit-count suppliers for the two residual fields that Lane C already
knows how to rebuild from cap-shaped hypotheses: densepack span-rarity (R4) and
top-band push-forward (R5).  This is a lower-level endpoint surface than carrying
`K1SpanRarity` and `V30TopBandPushforward` directly. -/
structure V30LocalizedExitCapSuppliers where
  /-- R5 top-band cap: band `<= 4` plus `64 * topBandDev < L`. -/
  topBandCap : forall ctx : ActualFailureContext,
    And (fixedFamilyRecurrentBand ctx <= 4)
      (64 * agcTopBandDev ctx < shellLadderDepth ctx)
  /-- R4 densepack per-span cap, stated on exactly the keystone span-rarity
  guard surface. -/
  spanCap : forall ctx : ActualFailureContext,
    Not (DscBand3ZeroDatum ctx) ->
    Not (Band3PinnedWide ctx) ->
    Not (Class3CycleBand3Free ctx) ->
    Or ((class1SlopeDatum ctx).q = 5) (13 <= (class1SlopeDatum ctx).q) ->
    Not (DensePackDatumClosed ctx) ->
    1 <= ctx.n24CarryData.r ->
    And (fixedFamilyRecurrentBand ctx <= 4)
      (forall m : Nat,
        32 * ((ctx.n24CarryData.r + 1) * k1acLocalExitMass ctx m)
          < shellLadderDepth ctx)

namespace V30LocalizedExitCapSuppliers

/-- Appendix-P top-band exit-freeness is an accepted R5 supplier source: it
rebuilds the numeric top-band cap via `v30_topBandCap_of_exitFree`, while R4 still
uses the per-span exit cap on the keystone span-rarity guard surface. -/
def ofTopBandExitFree
    (htop : forall ctx : ActualFailureContext,
      And (fixedFamilyRecurrentBand ctx <= 4) (DscTopBandExitFree ctx))
    (hspan : forall ctx : ActualFailureContext,
      Not (DscBand3ZeroDatum ctx) ->
      Not (Band3PinnedWide ctx) ->
      Not (Class3CycleBand3Free ctx) ->
      Or ((class1SlopeDatum ctx).q = 5) (13 <= (class1SlopeDatum ctx).q) ->
      Not (DensePackDatumClosed ctx) ->
      1 <= ctx.n24CarryData.r ->
      And (fixedFamilyRecurrentBand ctx <= 4)
        (forall m : Nat,
          32 * ((ctx.n24CarryData.r + 1) * k1acLocalExitMass ctx m)
            < shellLadderDepth ctx)) :
    V30LocalizedExitCapSuppliers where
  topBandCap := v30_topBandCap_of_exitFree htop
  spanCap := hspan

/-- Same supplier surface, but with R4 stated as the named local-exit-light atom
rather than the equivalent numeric per-span cap. -/
def ofTopBandExitFreeAndLocalExitLight
    (htop : forall ctx : ActualFailureContext,
      And (fixedFamilyRecurrentBand ctx <= 4) (DscTopBandExitFree ctx))
    (hspanLight : forall ctx : ActualFailureContext,
      Not (DscBand3ZeroDatum ctx) ->
      Not (Band3PinnedWide ctx) ->
      Not (Class3CycleBand3Free ctx) ->
      Or ((class1SlopeDatum ctx).q = 5) (13 <= (class1SlopeDatum ctx).q) ->
      Not (DensePackDatumClosed ctx) ->
      1 <= ctx.n24CarryData.r ->
      And (fixedFamilyRecurrentBand ctx <= 4) (K1LocalExitLight ctx)) :
    V30LocalizedExitCapSuppliers where
  topBandCap := v30_topBandCap_of_exitFree htop
  spanCap := fun ctx hz hwide hfree hq hd hr =>
    let hlight := hspanLight ctx hz hwide hfree hq hd hr
    ⟨hlight.1, (v30_localExitLight_iff_spanCap ctx).mp hlight.2⟩

/-- Band-following top-band onsets are accepted as a concrete R5 supplier source;
the numeric R5 cap is rebuilt by composing through `v30_topBandCap_of_onsets`. -/
def ofTopBandOnsets
    (htop : forall ctx : ActualFailureContext,
      And (fixedFamilyRecurrentBand ctx <= 4)
        (Exists (fun k1 : Nat =>
          And (k1 + (ctx.n24CarryData.r + 1) <= emF ctx + emW ctx)
            (forall k : Nat, k1 <= k ->
              hitGap ctx.n24CarryData.a k = fixedFamilyRecurrentBand ctx))))
    (hspan : forall ctx : ActualFailureContext,
      Not (DscBand3ZeroDatum ctx) ->
      Not (Band3PinnedWide ctx) ->
      Not (Class3CycleBand3Free ctx) ->
      Or ((class1SlopeDatum ctx).q = 5) (13 <= (class1SlopeDatum ctx).q) ->
      Not (DensePackDatumClosed ctx) ->
      1 <= ctx.n24CarryData.r ->
      And (fixedFamilyRecurrentBand ctx <= 4)
        (forall m : Nat,
          32 * ((ctx.n24CarryData.r + 1) * k1acLocalExitMass ctx m)
            < shellLadderDepth ctx)) :
    V30LocalizedExitCapSuppliers where
  topBandCap := v30_topBandCap_of_onsets htop
  spanCap := hspan

/-- Same onset-supplied R5 constructor, with R4 stated as the named
`K1LocalExitLight` atom rather than the numeric per-span cap. -/
def ofTopBandOnsetsAndLocalExitLight
    (htop : forall ctx : ActualFailureContext,
      And (fixedFamilyRecurrentBand ctx <= 4)
        (Exists (fun k1 : Nat =>
          And (k1 + (ctx.n24CarryData.r + 1) <= emF ctx + emW ctx)
            (forall k : Nat, k1 <= k ->
              hitGap ctx.n24CarryData.a k = fixedFamilyRecurrentBand ctx))))
    (hspanLight : forall ctx : ActualFailureContext,
      Not (DscBand3ZeroDatum ctx) ->
      Not (Band3PinnedWide ctx) ->
      Not (Class3CycleBand3Free ctx) ->
      Or ((class1SlopeDatum ctx).q = 5) (13 <= (class1SlopeDatum ctx).q) ->
      Not (DensePackDatumClosed ctx) ->
      1 <= ctx.n24CarryData.r ->
      And (fixedFamilyRecurrentBand ctx <= 4) (K1LocalExitLight ctx)) :
    V30LocalizedExitCapSuppliers where
  topBandCap := v30_topBandCap_of_onsets htop
  spanCap := fun ctx hz hwide hfree hq hd hr =>
    let hlight := hspanLight ctx hz hwide hfree hq hd hr
    ⟨hlight.1, (v30_localExitLight_iff_spanCap ctx).mp hlight.2⟩

/-- The R5 localized cap rebuilds the old `V30TopBandPushforward` residual field. -/
def topBand (S : V30LocalizedExitCapSuppliers) : V30TopBandPushforward :=
  v30_topBandPushforward_of_cap S.topBandCap

/-- The R4 localized per-span caps rebuild the old `K1SpanRarity` residual field. -/
def spanRarity (S : V30LocalizedExitCapSuppliers) :
    forall ctx : ActualFailureContext,
      Not (DscBand3ZeroDatum ctx) ->
      Not (Band3PinnedWide ctx) ->
      Not (Class3CycleBand3Free ctx) ->
      Or ((class1SlopeDatum ctx).q = 5) (13 <= (class1SlopeDatum ctx).q) ->
      Not (DensePackDatumClosed ctx) ->
      1 <= ctx.n24CarryData.r ->
      K1SpanRarity ctx :=
  fun ctx hz hwide hfree hq hd hr =>
    let hcap := S.spanCap ctx hz hwide hfree hq hd hr
    v30_spanRarity_of_cap ctx hcap.1 hcap.2

/-- The localized R4/R5 suppliers, together with the R6 read-tail bridge, form the
same Lane-G residual package used by `V30TopBandReadTail`. -/
def laneGResidual (S : V30LocalizedExitCapSuppliers)
    (hread : V30ReadTailExitCount) : V30TopBandReadTailResidual where
  topBand := S.topBand
  readTail := hread

/-- The Lane-G package built from localized caps has the expected R5 component. -/
theorem laneGResidual_topBand (S : V30LocalizedExitCapSuppliers)
    (hread : V30ReadTailExitCount) :
    (S.laneGResidual hread).topBand = S.topBand := rfl

/-- The Lane-G package built from localized caps has the expected R6 component. -/
theorem laneGResidual_readTail (S : V30LocalizedExitCapSuppliers)
    (hread : V30ReadTailExitCount) :
    (S.laneGResidual hread).readTail = hread := rfl

end V30LocalizedExitCapSuppliers

/-- V30 residual surface with R4/R5 lowered to localized cap suppliers instead of
carrying `K1SpanRarity` and `V30TopBandPushforward` directly.  All other residual
atoms are unchanged. -/
structure Erdos260V30LocalizedExitCapResidual where
  /-- The four-class off-pin cap, unchanged. -/
  offPin : V30OffPinFullRegime
  /-- Localized R4/R5 cap suppliers that rebuild `spanRarity` and `topBand`. -/
  localizedCaps : V30LocalizedExitCapSuppliers
  /-- Appendix-U orbit-pin confinement atom, unchanged. -/
  confinement : FixedPinCleanContinuation
  /-- Class-1 boundary-carry data, unchanged. -/
  class1C : ℕ -> ZMod 6
  /-- Class-1 cleanliness data, unchanged. -/
  class1Clean : ℕ -> Bool
  /-- Appendix-AA realization bridge over the carried class-1 data. -/
  class1Realize : V30Class1LedgerRealizesFormalRow
    (class1SystemOfCarry class1C class1Clean)
  /-- Read-tail exit-count bridge, unchanged. -/
  readTail : V30ReadTailExitCount
  /-- Raw K.1 cluster-floor residual, unchanged. -/
  clusterFloor : forall ctx : ActualFailureContext, Not (DscBand3ZeroDatum ctx) ->
    Not (Band3PinnedWide ctx) -> Not (Class3CycleBand3Free ctx) ->
    Or ((class1SlopeDatum ctx).q = 5) (13 <= (class1SlopeDatum ctx).q) ->
    Not (DensePackDatumClosed ctx) -> 1 <= ctx.n24CarryData.r ->
    K1ClusterFloor ctx
  /-- Raw densepack density residual, unchanged. -/
  density : forall ctx : ActualFailureContext, Not (DscBand3ZeroDatum ctx) ->
    Not (Class3CycleBand3Free ctx) ->
    Or ((class1SlopeDatum ctx).q = 5) (13 <= (class1SlopeDatum ctx).q) ->
    Not (DensePackDatumClosed ctx) ->
    densePackEndpointDensity ctx
  /-- Raw return-gates residual, unchanged. -/
  returnGates : forall ctx : ActualFailureContext, Not (DscReturnB2ZeroDatum ctx) ->
    Not (OrbitBandPinned ctx 2) ->
    Not (ReturnB2FreeDatum ctx) -> Not (ReturnB2OneSpacedDatum ctx) ->
    2 * (129 * shellLadderDepth ctx + 64)
      <= 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) ->
    ReturnGatesBodyUngated ctx
  /-- Raw narrow-support class-0 gate residual, unchanged. -/
  class0Gates : NarrowSupportClass0Gates

namespace Erdos260V30LocalizedExitCapResidual

/-- Project the localized-cap surface back to the existing v30 residual API. -/
def toV30Residual (R : Erdos260V30LocalizedExitCapResidual) :
    Erdos260V30Residual where
  offPin := R.offPin
  confinement := R.confinement
  class1C := R.class1C
  class1Clean := R.class1Clean
  class1Realize := R.class1Realize
  topBand := R.localizedCaps.topBand
  readTail := R.readTail
  spanRarity := R.localizedCaps.spanRarity
  clusterFloor := R.clusterFloor
  density := R.density
  returnGates := R.returnGates
  class0Gates := R.class0Gates

/-- The localized surface rebuilds the same R4 span-rarity field consumed by the
keystone densepack start-spacing slot. -/
theorem spanRarity (R : Erdos260V30LocalizedExitCapResidual) :
    forall ctx : ActualFailureContext,
      Not (DscBand3ZeroDatum ctx) ->
      Not (Band3PinnedWide ctx) ->
      Not (Class3CycleBand3Free ctx) ->
      Or ((class1SlopeDatum ctx).q = 5) (13 <= (class1SlopeDatum ctx).q) ->
      Not (DensePackDatumClosed ctx) ->
      1 <= ctx.n24CarryData.r ->
      K1SpanRarity ctx :=
  R.localizedCaps.spanRarity

/-- The localized surface rebuilds the same R5 top-band push-forward field consumed
by the keystone return/densepack interior slots. -/
theorem topBand (R : Erdos260V30LocalizedExitCapResidual) :
    V30TopBandPushforward :=
  R.localizedCaps.topBand

/-- The off-pin deliverables are unchanged by the R4/R5 localization. -/
theorem offPinDeliverables (R : Erdos260V30LocalizedExitCapResidual) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  v30_offPin_allClasses R.offPin

/-- The localized endpoint surface exposes the same combined Lane-G package
`R5 + R6` used by the convergence wiring. -/
def laneGResidual (R : Erdos260V30LocalizedExitCapResidual) :
    V30TopBandReadTailResidual :=
  R.localizedCaps.laneGResidual R.readTail

/-- Projection check for the top-band component of the localized Lane-G package. -/
theorem laneGResidual_topBand (R : Erdos260V30LocalizedExitCapResidual) :
    R.laneGResidual.topBand = R.localizedCaps.topBand := rfl

/-- Projection check for the read-tail component of the localized Lane-G package. -/
theorem laneGResidual_readTail (R : Erdos260V30LocalizedExitCapResidual) :
    R.laneGResidual.readTail = R.readTail := rfl

/-- The localized endpoint surface carries the same M.5/L.3 exit-mass core
through its projection to the v30 residual API. -/
theorem exitMassCore (R : Erdos260V30LocalizedExitCapResidual) :
    ExitMassControlCore :=
  exitMassControl_iff_split.mpr
    ⟨deepOrbitPinVoiding_of_confinement R.confinement, (offPinDeliverables R).1⟩

/-- The localized endpoint surface carries the same deep orbit-pin voiding
through its projection to the v30 residual API. -/
theorem deepOrbitPinVoiding (R : Erdos260V30LocalizedExitCapResidual) :
    DeepOrbitPinVoiding :=
  deepOrbitPinVoiding_of_exitMassControl (exitMassCore R)

end Erdos260V30LocalizedExitCapResidual

/-- V30 residual surface with both refinements active at once: the off-pin atom is
lowered to the finite-error coordinate O2 collar provider plus zero-collar proofs,
and R4/R5 are lowered to localized exit-cap suppliers. -/
structure Erdos260V30O2LocalizedExitCapZeroErrorResidual {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int) where
  /-- Concrete coordinate O2/AB/R provider for the four off-pin classes, retaining
  collars before the zero-error proofs are applied. -/
  offPinO2 : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
    (β := β) (A := A) P₀ Q
  /-- The class-3 collar is genuinely zero on every pin-free deep context. -/
  class3Zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)),
      (offPinO2.class3 ctx hX hn2 hn3 hn4).collar.card = 0
  /-- The class-4 collar is genuinely zero on every pin-free deep context. -/
  class4Zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)),
      (offPinO2.class4 ctx hX hn2 hn3 hn4).collar.card = 0
  /-- The class-5 collar is genuinely zero on every pin-free deep context. -/
  class5Zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)),
      (offPinO2.class5 ctx hX hn2 hn3 hn4).collar.card = 0
  /-- The class-0 collar is genuinely zero on every class-0 survivor context. -/
  class0Zero : forall (ctx : ActualFailureContext) (hsurv : Class0DatumSurvivor ctx),
    (offPinO2.class0 ctx hsurv).collar.card = 0
  /-- Localized R4/R5 cap suppliers that rebuild `spanRarity` and `topBand`. -/
  localizedCaps : V30LocalizedExitCapSuppliers
  /-- Appendix-U orbit-pin confinement atom, unchanged. -/
  confinement : FixedPinCleanContinuation
  /-- Class-1 boundary-carry data, unchanged. -/
  class1C : Nat -> ZMod 6
  /-- Class-1 cleanliness data, unchanged. -/
  class1Clean : Nat -> Bool
  /-- Appendix-AA realization bridge over the carried class-1 data. -/
  class1Realize : V30Class1LedgerRealizesFormalRow
    (class1SystemOfCarry class1C class1Clean)
  /-- Read-tail exit-count bridge, unchanged. -/
  readTail : V30ReadTailExitCount
  /-- Raw K.1 cluster-floor residual, unchanged. -/
  clusterFloor : forall ctx : ActualFailureContext, Not (DscBand3ZeroDatum ctx) ->
    Not (Band3PinnedWide ctx) -> Not (Class3CycleBand3Free ctx) ->
    Or ((class1SlopeDatum ctx).q = 5) (13 <= (class1SlopeDatum ctx).q) ->
    Not (DensePackDatumClosed ctx) -> 1 <= ctx.n24CarryData.r ->
    K1ClusterFloor ctx
  /-- Raw densepack density residual, unchanged. -/
  density : forall ctx : ActualFailureContext, Not (DscBand3ZeroDatum ctx) ->
    Not (Class3CycleBand3Free ctx) ->
    Or ((class1SlopeDatum ctx).q = 5) (13 <= (class1SlopeDatum ctx).q) ->
    Not (DensePackDatumClosed ctx) ->
    densePackEndpointDensity ctx
  /-- Raw return-gates residual, unchanged. -/
  returnGates : forall ctx : ActualFailureContext, Not (DscReturnB2ZeroDatum ctx) ->
    Not (OrbitBandPinned ctx 2) ->
    Not (ReturnB2FreeDatum ctx) -> Not (ReturnB2OneSpacedDatum ctx) ->
    2 * (129 * shellLadderDepth ctx + 64)
      <= 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) ->
    ReturnGatesBodyUngated ctx
  /-- Raw narrow-support class-0 gate residual, unchanged. -/
  class0Gates : NarrowSupportClass0Gates

namespace Erdos260V30O2LocalizedExitCapZeroErrorResidual

/-- Convert the combined lower-level surface to the localized-cap v30 endpoint
surface. -/
def toLocalizedExitCapResidual {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V30LocalizedExitCapResidual where
  offPin :=
    V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.fullRegime_of_zeroCollarProvider
      R.offPinO2 R.class3Zero R.class4Zero R.class5Zero R.class0Zero
  localizedCaps := R.localizedCaps
  confinement := R.confinement
  class1C := R.class1C
  class1Clean := R.class1Clean
  class1Realize := R.class1Realize
  readTail := R.readTail
  clusterFloor := R.clusterFloor
  density := R.density
  returnGates := R.returnGates
  class0Gates := R.class0Gates

/-- Project the combined lower-level surface back to the existing v30 residual API. -/
def toV30Residual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V30Residual :=
  R.toLocalizedExitCapResidual.toV30Residual

/-- The combined lower-level surface supplies the same four-class off-pin C1
deliverables once the finite-error collars are zero. -/
theorem offPinDeliverables {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.allClasses_of_zeroCollars
    R.offPinO2 R.class3Zero R.class4Zero R.class5Zero R.class0Zero

/-- The combined O2/localized endpoint surface still exposes the same Lane-G
`R5 + R6` package; the off-pin refinement is independent of this bookkeeping. -/
def laneGResidual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    V30TopBandReadTailResidual :=
  R.localizedCaps.laneGResidual R.readTail

/-- Projection check for the top-band component of the combined O2 Lane-G package. -/
theorem laneGResidual_topBand {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    R.laneGResidual.topBand = R.localizedCaps.topBand := rfl

/-- Projection check for the read-tail component of the combined O2 Lane-G package. -/
theorem laneGResidual_readTail {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    R.laneGResidual.readTail = R.readTail := rfl

/-- The combined O2/localized zero-error surface carries the same M.5/L.3
exit-mass core through its projection to the v30 residual API. -/
theorem exitMassCore {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V30O2LocalizedExitCapZeroErrorResidual beta A hdec P Q) :
    ExitMassControlCore :=
  exitMassControl_iff_split.mpr
    ⟨deepOrbitPinVoiding_of_confinement R.confinement, (offPinDeliverables R).1⟩

/-- The combined O2/localized zero-error surface carries the same deep orbit-pin
voiding through its projection to the v30 residual API. -/
theorem deepOrbitPinVoiding {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V30O2LocalizedExitCapZeroErrorResidual beta A hdec P Q) :
    DeepOrbitPinVoiding :=
  deepOrbitPinVoiding_of_exitMassControl (exitMassCore R)

end Erdos260V30O2LocalizedExitCapZeroErrorResidual

/-- V30 residual surface with both endpoint refinements active at once, but with
the TeX-style literal empty-collar package in place of four cardinality-zero
proofs.  The off-pin provider is still finite-error internally; the packaged
empty-collar bridge lowers it to the same zero-collar surface used above. -/
structure Erdos260V30O2LocalizedExitCapEmptyCollarResidual {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int) where
  /-- Concrete coordinate O2/AB/R provider with literal empty-collar facts for
  the four off-pin classes. -/
  offPinO2 : V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs
    (β := β) (A := A) P₀ Q
  /-- Localized R4/R5 cap suppliers that rebuild `spanRarity` and `topBand`. -/
  localizedCaps : V30LocalizedExitCapSuppliers
  /-- Appendix-U orbit-pin confinement atom, unchanged. -/
  confinement : FixedPinCleanContinuation
  /-- Class-1 boundary-carry data, unchanged. -/
  class1C : Nat -> ZMod 6
  /-- Class-1 cleanliness data, unchanged. -/
  class1Clean : Nat -> Bool
  /-- Appendix-AA realization bridge over the carried class-1 data. -/
  class1Realize : V30Class1LedgerRealizesFormalRow
    (class1SystemOfCarry class1C class1Clean)
  /-- Read-tail exit-count bridge, unchanged. -/
  readTail : V30ReadTailExitCount
  /-- Raw K.1 cluster-floor residual, unchanged. -/
  clusterFloor : forall ctx : ActualFailureContext, Not (DscBand3ZeroDatum ctx) ->
    Not (Band3PinnedWide ctx) -> Not (Class3CycleBand3Free ctx) ->
    Or ((class1SlopeDatum ctx).q = 5) (13 <= (class1SlopeDatum ctx).q) ->
    Not (DensePackDatumClosed ctx) -> 1 <= ctx.n24CarryData.r ->
    K1ClusterFloor ctx
  /-- Raw densepack density residual, unchanged. -/
  density : forall ctx : ActualFailureContext, Not (DscBand3ZeroDatum ctx) ->
    Not (Class3CycleBand3Free ctx) ->
    Or ((class1SlopeDatum ctx).q = 5) (13 <= (class1SlopeDatum ctx).q) ->
    Not (DensePackDatumClosed ctx) ->
    densePackEndpointDensity ctx
  /-- Raw return-gates residual, unchanged. -/
  returnGates : forall ctx : ActualFailureContext, Not (DscReturnB2ZeroDatum ctx) ->
    Not (OrbitBandPinned ctx 2) ->
    Not (ReturnB2FreeDatum ctx) -> Not (ReturnB2OneSpacedDatum ctx) ->
    2 * (129 * shellLadderDepth ctx + 64)
      <= 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) ->
    ReturnGatesBodyUngated ctx
  /-- Raw narrow-support class-0 gate residual, unchanged. -/
  class0Gates : NarrowSupportClass0Gates

namespace Erdos260V30O2LocalizedExitCapEmptyCollarResidual

/-- Convert the combined empty-collar surface to the existing finite-error plus
zero-cardinality combined surface. -/
def toZeroErrorResidual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V30O2LocalizedExitCapZeroErrorResidual (β := β) (A := A) P₀ Q where
  offPinO2 := R.offPinO2.provider
  class3Zero :=
    V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.class3Zero
      R.offPinO2
  class4Zero :=
    V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.class4Zero
      R.offPinO2
  class5Zero :=
    V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.class5Zero
      R.offPinO2
  class0Zero :=
    V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.class0Zero
      R.offPinO2
  localizedCaps := R.localizedCaps
  confinement := R.confinement
  class1C := R.class1C
  class1Clean := R.class1Clean
  class1Realize := R.class1Realize
  readTail := R.readTail
  clusterFloor := R.clusterFloor
  density := R.density
  returnGates := R.returnGates
  class0Gates := R.class0Gates

/-- Convert the combined empty-collar surface to the localized-cap v30 endpoint
surface. -/
def toLocalizedExitCapResidual {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V30LocalizedExitCapResidual :=
  R.toZeroErrorResidual.toLocalizedExitCapResidual

/-- Project the combined empty-collar surface back to the existing v30 residual
API. -/
def toV30Residual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V30Residual :=
  R.toLocalizedExitCapResidual.toV30Residual

/-- The combined empty-collar surface supplies the same four-class off-pin C1
deliverables consumed by the endpoint. -/
theorem offPinDeliverables {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.allClasses
    R.offPinO2

/-- The empty-collar endpoint surface exposes the same Lane-G `R5 + R6` package as
the zero-error and localized surfaces. -/
def laneGResidual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    V30TopBandReadTailResidual :=
  R.localizedCaps.laneGResidual R.readTail

/-- Projection check for the top-band component of the empty-collar Lane-G package. -/
theorem laneGResidual_topBand {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    R.laneGResidual.topBand = R.localizedCaps.topBand := rfl

/-- Projection check for the read-tail component of the empty-collar Lane-G package. -/
theorem laneGResidual_readTail {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    R.laneGResidual.readTail = R.readTail := rfl

/-- The combined O2/localized empty-collar surface carries the same M.5/L.3
exit-mass core through its projection to the v30 residual API. -/
theorem exitMassCore {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V30O2LocalizedExitCapEmptyCollarResidual beta A hdec P Q) :
    ExitMassControlCore :=
  exitMassControl_iff_split.mpr
    ⟨deepOrbitPinVoiding_of_confinement R.confinement, (offPinDeliverables R).1⟩

/-- The combined O2/localized empty-collar surface carries the same deep
orbit-pin voiding through its projection to the v30 residual API. -/
theorem deepOrbitPinVoiding {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V30O2LocalizedExitCapEmptyCollarResidual beta A hdec P Q) :
    DeepOrbitPinVoiding :=
  deepOrbitPinVoiding_of_exitMassControl (exitMassCore R)

end Erdos260V30O2LocalizedExitCapEmptyCollarResidual

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

/-- Namespaced form of the v30 (C1) M.5/L.3 exit-mass core supplier. -/
theorem Erdos260V30Residual.exitMassCore (R : Erdos260V30Residual) :
    ExitMassControlCore :=
  v30_exitMassCore R

/-- Namespaced form of the v30 off-pin deliverables carried by the residual. -/
theorem Erdos260V30Residual.offPinDeliverables (R : Erdos260V30Residual) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  v30_offPin_deliverables R

/-- Namespaced form of the deep orbit-pin voiding read from the v30 core. -/
theorem Erdos260V30Residual.deepOrbitPinVoiding (R : Erdos260V30Residual) :
    DeepOrbitPinVoiding :=
  v30_deepOrbitPin R

/-- The v30 residual rebuilds the full corrected Return-gates field.  The pinned
half comes from the Appendix-U confinement atom, while the `b₂ = 0` table is closed
by the existing cycle-count certificate and the off-table branch is exactly the
carried `returnGates` field. -/
theorem Erdos260V30Residual.returnGatesField (R : Erdos260V30Residual) :
    ReturnGatesField :=
  returnGatesField_iff_band2Void_split.mpr
    ⟨returnBand2Void_of_deepOrbitPinVoiding
        (deepOrbitPinVoiding_of_confinement R.confinement),
      fun ctx hpin hfree hone hnum => by
        by_cases hz : DscReturnB2ZeroDatum ctx
        · obtain ⟨c, hc, hper, hcount⟩ := dscReturnCycleCert_of_b2ZeroDatum ctx hz
          exact agcReturnGatesUngated_of_cycleCount_ceil ctx hc hper hcount
        · exact R.returnGates ctx hz hpin hfree hone hnum⟩

/-- The v30 residual rebuilds the full corrected Return-interior field.
The `b₂ = 0` table rows are closed by the dispatcher, and the off-table branch
is supplied by the top-band push-forward. -/
theorem Erdos260V30Residual.returnInteriorField (R : Erdos260V30Residual) :
    ∀ ctx : ActualFailureContext, ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  dscReturnInteriorField_of_offTable
    (v30ReturnInteriorOffTable_of_pushforward R.topBand)

/-- The v30 residual exposes the exact off-table Return-gates branch consumed by
the keystone surface before the `b₂ = 0` dispatcher is applied. -/
theorem Erdos260V30Residual.returnGatesOffTableField (R : Erdos260V30Residual) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx :=
  R.returnGates

/-- The v30 residual exposes the exact off-table Return-interior branch supplied
by the top-band push-forward. -/
theorem Erdos260V30Residual.returnInteriorOffTableField (R : Erdos260V30Residual) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  v30ReturnInteriorOffTable_of_pushforward R.topBand

/-- The v30 residual exposes the exact K.1 start-spacing field used by the
keystone DensePack cover branch; this is the Lane-E span-rarity atom repackaged
with the endpoint guards. -/
theorem Erdos260V30Residual.densePackStartSpacingField
    (R : Erdos260V30Residual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1StartSpacing ctx :=
  v30DensePackStartSpacingField_of_spanRarity R.spanRarity

/-- The v30 residual exposes the exact K.1 cluster-floor field used by the
keystone DensePack cover branch. -/
theorem Erdos260V30Residual.densePackClusterFloorField
    (R : Erdos260V30Residual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1ClusterFloor ctx :=
  R.clusterFloor

/-- The v30 residual rebuilds the densepack off-table cover field from the K.1
landing route.  At `r = 0` the cover body is closed by the K1 landing file;
at `r >= 1`, the carried density, cluster-floor atom, and span-rarity-induced
start-spacing atom give the exact cover inequality. -/
theorem Erdos260V30Residual.densePackCoverOffTableField
    (R : Erdos260V30Residual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  k1DensePackCoverOffTableField_of_deepStrata
    (fun ctx hzero hwide hcycle hq hclosed hr =>
      k1CoverBody_of_density_cluster_spacing ctx
        (R.density ctx hzero hcycle hq hclosed)
        (R.clusterFloor ctx hzero hwide hcycle hq hclosed hr)
        ((v30DensePackStartSpacingField_of_spanRarity R.spanRarity)
          ctx hzero hwide hcycle hq hclosed hr))

/-- The v30 residual rebuilds the full corrected densepack Nat-cover field.
The wide band-3 pinned half comes from Appendix-U confinement, while the
non-pinned half is the K.1 landing bridge above. -/
theorem Erdos260V30Residual.densePackCoverField (R : Erdos260V30Residual) :
    DensePackCoverField :=
  densePackCoverField_iff_band3Void_split.mpr
    ⟨densePackBand3Void_of_deepOrbitPinVoiding
        (deepOrbitPinVoiding_of_confinement R.confinement),
      dscDensePackCoverFreeField_of_offTable R.densePackCoverOffTableField⟩

/-- The v30 residual rebuilds the full corrected densepack density field.
The `b3 = 0` table rows are vacuous through `Class3CycleBand3Free`; off the
table the carried K.1 density field is used verbatim. -/
theorem Erdos260V30Residual.densePackDensityField (R : Erdos260V30Residual) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  dscDensePackDensityField_of_offTable R.density

/-- The v30 residual rebuilds the full corrected densepack active-window
interior field.  The `b3 = 0` table rows are vacuous through top-band cycle
freeness; off the table, the top-band push-forward supplies the interior bound. -/
theorem Erdos260V30Residual.densePackInteriorField (R : Erdos260V30Residual) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  dscDensePackInteriorField_of_offTable
    (v30DensePackInteriorOffTable_of_pushforward R.topBand)

/-- The v30 residual exposes the exact DensePack off-table density branch
consumed by the keystone surface. -/
theorem Erdos260V30Residual.densePackDensityOffTableField (R : Erdos260V30Residual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.density

/-- The v30 residual exposes the exact DensePack off-table active-window interior
branch supplied by the top-band push-forward. -/
theorem Erdos260V30Residual.densePackInteriorOffTableField (R : Erdos260V30Residual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  v30DensePackInteriorOffTable_of_pushforward R.topBand

/-- The v30 residual rebuilds the exact three-lane class-0 mass field consumed
by the wave-18 frontier/absorption surfaces, from its carried narrow-support
gate data. -/
theorem Erdos260V30Residual.class0MassField (R : Erdos260V30Residual) :
    Class0MassField :=
  nsgFrontierClass0Mass_of_gates R.class0Gates

/-- The localized endpoint surface inherits the full corrected Return-gates field
through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30LocalizedExitCapResidual.returnGatesField
    (R : Erdos260V30LocalizedExitCapResidual) :
    ReturnGatesField :=
  R.toV30Residual.returnGatesField

/-- The combined zero-error O2/localized endpoint surface inherits the full
corrected Return-gates field. -/
theorem Erdos260V30O2LocalizedExitCapZeroErrorResidual.returnGatesField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ReturnGatesField :=
  R.toV30Residual.returnGatesField

/-- The combined empty-collar O2/localized endpoint surface inherits the full
corrected Return-gates field. -/
theorem Erdos260V30O2LocalizedExitCapEmptyCollarResidual.returnGatesField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ReturnGatesField :=
  R.toV30Residual.returnGatesField

/-- The coordinate O2 endpoint surface inherits the full corrected Return-gates
field through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30O2CollarCoordinateResidual.returnGatesField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ReturnGatesField :=
  R.toV30Residual.returnGatesField

/-- The finite-error/zero-collar coordinate O2 endpoint surface inherits the full
corrected Return-gates field. -/
theorem Erdos260V30O2CollarCoordinateZeroErrorResidual.returnGatesField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ReturnGatesField :=
  R.toV30Residual.returnGatesField

/-- The empty-collar coordinate O2 endpoint surface inherits the full corrected
Return-gates field. -/
theorem Erdos260V30O2CollarCoordinateEmptyCollarResidual.returnGatesField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ReturnGatesField :=
  R.toV30Residual.returnGatesField

/-- The localized endpoint surface inherits the full corrected Return-interior
field through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30LocalizedExitCapResidual.returnInteriorField
    (R : Erdos260V30LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext, ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorField

/-- The combined zero-error O2/localized endpoint surface inherits the full
corrected Return-interior field. -/
theorem Erdos260V30O2LocalizedExitCapZeroErrorResidual.returnInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorField

/-- The combined empty-collar O2/localized endpoint surface inherits the full
corrected Return-interior field. -/
theorem Erdos260V30O2LocalizedExitCapEmptyCollarResidual.returnInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorField

/-- The coordinate O2 endpoint surface inherits the full corrected
Return-interior field through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30O2CollarCoordinateResidual.returnInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorField

/-- The finite-error/zero-collar coordinate O2 endpoint surface inherits the full
corrected Return-interior field. -/
theorem Erdos260V30O2CollarCoordinateZeroErrorResidual.returnInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorField

/-- The empty-collar coordinate O2 endpoint surface inherits the full corrected
Return-interior field. -/
theorem Erdos260V30O2CollarCoordinateEmptyCollarResidual.returnInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorField

/-- The localized endpoint surface inherits the off-table Return-gates branch
through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30LocalizedExitCapResidual.returnGatesOffTableField
    (R : Erdos260V30LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx :=
  R.toV30Residual.returnGatesOffTableField

/-- The combined zero-error O2/localized endpoint surface inherits the off-table
Return-gates branch. -/
theorem Erdos260V30O2LocalizedExitCapZeroErrorResidual.returnGatesOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx :=
  R.toV30Residual.returnGatesOffTableField

/-- The combined empty-collar O2/localized endpoint surface inherits the
off-table Return-gates branch. -/
theorem Erdos260V30O2LocalizedExitCapEmptyCollarResidual.returnGatesOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx :=
  R.toV30Residual.returnGatesOffTableField

/-- The coordinate O2 endpoint surface inherits the off-table Return-gates
branch through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30O2CollarCoordinateResidual.returnGatesOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx :=
  R.toV30Residual.returnGatesOffTableField

/-- The finite-error/zero-collar coordinate O2 endpoint surface inherits the
off-table Return-gates branch. -/
theorem Erdos260V30O2CollarCoordinateZeroErrorResidual.returnGatesOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx :=
  R.toV30Residual.returnGatesOffTableField

/-- The empty-collar coordinate O2 endpoint surface inherits the off-table
Return-gates branch. -/
theorem Erdos260V30O2CollarCoordinateEmptyCollarResidual.returnGatesOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx :=
  R.toV30Residual.returnGatesOffTableField

/-- The localized endpoint surface inherits the off-table Return-interior branch
through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30LocalizedExitCapResidual.returnInteriorOffTableField
    (R : Erdos260V30LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorOffTableField

/-- The combined zero-error O2/localized endpoint surface inherits the off-table
Return-interior branch. -/
theorem Erdos260V30O2LocalizedExitCapZeroErrorResidual.returnInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorOffTableField

/-- The combined empty-collar O2/localized endpoint surface inherits the
off-table Return-interior branch. -/
theorem Erdos260V30O2LocalizedExitCapEmptyCollarResidual.returnInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorOffTableField

/-- The coordinate O2 endpoint surface inherits the off-table Return-interior
branch through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30O2CollarCoordinateResidual.returnInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorOffTableField

/-- The finite-error/zero-collar coordinate O2 endpoint surface inherits the
off-table Return-interior branch. -/
theorem Erdos260V30O2CollarCoordinateZeroErrorResidual.returnInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorOffTableField

/-- The empty-collar coordinate O2 endpoint surface inherits the off-table
Return-interior branch. -/
theorem Erdos260V30O2CollarCoordinateEmptyCollarResidual.returnInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorOffTableField

/-- The localized endpoint surface inherits the exact K.1 start-spacing field
through its v30 projection. -/
theorem Erdos260V30LocalizedExitCapResidual.densePackStartSpacingField
    (R : Erdos260V30LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1StartSpacing ctx :=
  R.toV30Residual.densePackStartSpacingField

/-- The combined zero-error O2/localized endpoint surface inherits the exact K.1
start-spacing field. -/
theorem Erdos260V30O2LocalizedExitCapZeroErrorResidual.densePackStartSpacingField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1StartSpacing ctx :=
  R.toV30Residual.densePackStartSpacingField

/-- The combined empty-collar O2/localized endpoint surface inherits the exact
K.1 start-spacing field. -/
theorem Erdos260V30O2LocalizedExitCapEmptyCollarResidual.densePackStartSpacingField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1StartSpacing ctx :=
  R.toV30Residual.densePackStartSpacingField

/-- The coordinate O2 endpoint surface inherits the exact K.1 start-spacing
field through its v30 projection. -/
theorem Erdos260V30O2CollarCoordinateResidual.densePackStartSpacingField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1StartSpacing ctx :=
  R.toV30Residual.densePackStartSpacingField

/-- The finite-error/zero-collar coordinate O2 endpoint surface inherits the
exact K.1 start-spacing field. -/
theorem Erdos260V30O2CollarCoordinateZeroErrorResidual.densePackStartSpacingField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1StartSpacing ctx :=
  R.toV30Residual.densePackStartSpacingField

/-- The empty-collar coordinate O2 endpoint surface inherits the exact K.1
start-spacing field. -/
theorem Erdos260V30O2CollarCoordinateEmptyCollarResidual.densePackStartSpacingField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1StartSpacing ctx :=
  R.toV30Residual.densePackStartSpacingField

/-- The localized endpoint surface inherits the exact K.1 cluster-floor field
through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30LocalizedExitCapResidual.densePackClusterFloorField
    (R : Erdos260V30LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1ClusterFloor ctx :=
  R.toV30Residual.densePackClusterFloorField

/-- The combined zero-error O2/localized endpoint surface inherits the exact
K.1 cluster-floor field. -/
theorem Erdos260V30O2LocalizedExitCapZeroErrorResidual.densePackClusterFloorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1ClusterFloor ctx :=
  R.toV30Residual.densePackClusterFloorField

/-- The combined empty-collar O2/localized endpoint surface inherits the exact
K.1 cluster-floor field. -/
theorem Erdos260V30O2LocalizedExitCapEmptyCollarResidual.densePackClusterFloorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1ClusterFloor ctx :=
  R.toV30Residual.densePackClusterFloorField

/-- The coordinate O2 endpoint surface inherits the exact K.1 cluster-floor
field through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30O2CollarCoordinateResidual.densePackClusterFloorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1ClusterFloor ctx :=
  R.toV30Residual.densePackClusterFloorField

/-- The finite-error/zero-collar coordinate O2 endpoint surface inherits the
exact K.1 cluster-floor field. -/
theorem Erdos260V30O2CollarCoordinateZeroErrorResidual.densePackClusterFloorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1ClusterFloor ctx :=
  R.toV30Residual.densePackClusterFloorField

/-- The empty-collar coordinate O2 endpoint surface inherits the exact K.1
cluster-floor field. -/
theorem Erdos260V30O2CollarCoordinateEmptyCollarResidual.densePackClusterFloorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1ClusterFloor ctx :=
  R.toV30Residual.densePackClusterFloorField

/-- The localized endpoint surface inherits the K.1 densepack off-table cover
inequality through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30LocalizedExitCapResidual.densePackCoverOffTableField
    (R : Erdos260V30LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  R.toV30Residual.densePackCoverOffTableField

/-- The combined zero-error O2/localized endpoint surface inherits the K.1
densepack off-table cover inequality. -/
theorem Erdos260V30O2LocalizedExitCapZeroErrorResidual.densePackCoverOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  R.toV30Residual.densePackCoverOffTableField

/-- The combined empty-collar O2/localized endpoint surface inherits the K.1
densepack off-table cover inequality. -/
theorem Erdos260V30O2LocalizedExitCapEmptyCollarResidual.densePackCoverOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  R.toV30Residual.densePackCoverOffTableField

/-- The coordinate O2 endpoint surface inherits the K.1 densepack off-table
cover inequality through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30O2CollarCoordinateResidual.densePackCoverOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  R.toV30Residual.densePackCoverOffTableField

/-- The finite-error/zero-collar coordinate O2 endpoint surface inherits the
K.1 densepack off-table cover inequality. -/
theorem Erdos260V30O2CollarCoordinateZeroErrorResidual.densePackCoverOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  R.toV30Residual.densePackCoverOffTableField

/-- The empty-collar coordinate O2 endpoint surface inherits the K.1 densepack
off-table cover inequality. -/
theorem Erdos260V30O2CollarCoordinateEmptyCollarResidual.densePackCoverOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  R.toV30Residual.densePackCoverOffTableField

/-- The localized endpoint surface inherits the full corrected densepack
Nat-cover field through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30LocalizedExitCapResidual.densePackCoverField
    (R : Erdos260V30LocalizedExitCapResidual) :
    DensePackCoverField :=
  R.toV30Residual.densePackCoverField

/-- The combined zero-error O2/localized endpoint surface inherits the full
corrected densepack Nat-cover field. -/
theorem Erdos260V30O2LocalizedExitCapZeroErrorResidual.densePackCoverField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    DensePackCoverField :=
  R.toV30Residual.densePackCoverField

/-- The combined empty-collar O2/localized endpoint surface inherits the full
corrected densepack Nat-cover field. -/
theorem Erdos260V30O2LocalizedExitCapEmptyCollarResidual.densePackCoverField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    DensePackCoverField :=
  R.toV30Residual.densePackCoverField

/-- The coordinate O2 endpoint surface inherits the full corrected densepack
Nat-cover field through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30O2CollarCoordinateResidual.densePackCoverField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    DensePackCoverField :=
  R.toV30Residual.densePackCoverField

/-- The finite-error/zero-collar coordinate O2 endpoint surface inherits the
full corrected densepack Nat-cover field. -/
theorem Erdos260V30O2CollarCoordinateZeroErrorResidual.densePackCoverField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    DensePackCoverField :=
  R.toV30Residual.densePackCoverField

/-- The empty-collar coordinate O2 endpoint surface inherits the full corrected
densepack Nat-cover field. -/
theorem Erdos260V30O2CollarCoordinateEmptyCollarResidual.densePackCoverField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    DensePackCoverField :=
  R.toV30Residual.densePackCoverField

/-- The localized endpoint surface inherits the DensePack off-table density
branch through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30LocalizedExitCapResidual.densePackDensityOffTableField
    (R : Erdos260V30LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityOffTableField

/-- The combined zero-error O2/localized endpoint surface inherits the DensePack
off-table density branch. -/
theorem Erdos260V30O2LocalizedExitCapZeroErrorResidual.densePackDensityOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityOffTableField

/-- The combined empty-collar O2/localized endpoint surface inherits the
DensePack off-table density branch. -/
theorem Erdos260V30O2LocalizedExitCapEmptyCollarResidual.densePackDensityOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityOffTableField

/-- The coordinate O2 endpoint surface inherits the DensePack off-table density
branch through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30O2CollarCoordinateResidual.densePackDensityOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityOffTableField

/-- The finite-error/zero-collar coordinate O2 endpoint surface inherits the
DensePack off-table density branch. -/
theorem Erdos260V30O2CollarCoordinateZeroErrorResidual.densePackDensityOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityOffTableField

/-- The empty-collar coordinate O2 endpoint surface inherits the DensePack
off-table density branch. -/
theorem Erdos260V30O2CollarCoordinateEmptyCollarResidual.densePackDensityOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityOffTableField

/-- The localized endpoint surface inherits the DensePack off-table
active-window interior branch through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30LocalizedExitCapResidual.densePackInteriorOffTableField
    (R : Erdos260V30LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorOffTableField

/-- The combined zero-error O2/localized endpoint surface inherits the DensePack
off-table active-window interior branch. -/
theorem Erdos260V30O2LocalizedExitCapZeroErrorResidual.densePackInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorOffTableField

/-- The combined empty-collar O2/localized endpoint surface inherits the DensePack
off-table active-window interior branch. -/
theorem Erdos260V30O2LocalizedExitCapEmptyCollarResidual.densePackInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorOffTableField

/-- The coordinate O2 endpoint surface inherits the DensePack off-table
active-window interior branch through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30O2CollarCoordinateResidual.densePackInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorOffTableField

/-- The finite-error/zero-collar coordinate O2 endpoint surface inherits the
DensePack off-table active-window interior branch. -/
theorem Erdos260V30O2CollarCoordinateZeroErrorResidual.densePackInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorOffTableField

/-- The empty-collar coordinate O2 endpoint surface inherits the DensePack
off-table active-window interior branch. -/
theorem Erdos260V30O2CollarCoordinateEmptyCollarResidual.densePackInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorOffTableField

/-- The localized endpoint surface inherits the corrected densepack density field
through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30LocalizedExitCapResidual.densePackDensityField
    (R : Erdos260V30LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityField

/-- The combined zero-error O2/localized endpoint surface inherits the corrected
densepack density field. -/
theorem Erdos260V30O2LocalizedExitCapZeroErrorResidual.densePackDensityField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityField

/-- The combined empty-collar O2/localized endpoint surface inherits the corrected
densepack density field. -/
theorem Erdos260V30O2LocalizedExitCapEmptyCollarResidual.densePackDensityField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityField

/-- The coordinate O2 endpoint surface inherits the corrected densepack density
field through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30O2CollarCoordinateResidual.densePackDensityField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityField

/-- The finite-error/zero-collar coordinate O2 endpoint surface inherits the
corrected densepack density field. -/
theorem Erdos260V30O2CollarCoordinateZeroErrorResidual.densePackDensityField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityField

/-- The empty-collar coordinate O2 endpoint surface inherits the corrected
densepack density field. -/
theorem Erdos260V30O2CollarCoordinateEmptyCollarResidual.densePackDensityField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityField

/-- The localized endpoint surface inherits the corrected densepack
active-window interior field through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30LocalizedExitCapResidual.densePackInteriorField
    (R : Erdos260V30LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorField

/-- The combined zero-error O2/localized endpoint surface inherits the corrected
densepack active-window interior field. -/
theorem Erdos260V30O2LocalizedExitCapZeroErrorResidual.densePackInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorField

/-- The combined empty-collar O2/localized endpoint surface inherits the corrected
densepack active-window interior field. -/
theorem Erdos260V30O2LocalizedExitCapEmptyCollarResidual.densePackInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorField

/-- The coordinate O2 endpoint surface inherits the corrected densepack
active-window interior field through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30O2CollarCoordinateResidual.densePackInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorField

/-- The finite-error/zero-collar coordinate O2 endpoint surface inherits the
corrected densepack active-window interior field. -/
theorem Erdos260V30O2CollarCoordinateZeroErrorResidual.densePackInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorField

/-- The empty-collar coordinate O2 endpoint surface inherits the corrected
densepack active-window interior field. -/
theorem Erdos260V30O2CollarCoordinateEmptyCollarResidual.densePackInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorField

/-- The localized endpoint surface inherits the class-0 mass field rebuilt from
its carried narrow-support gate data. -/
theorem Erdos260V30LocalizedExitCapResidual.class0MassField
    (R : Erdos260V30LocalizedExitCapResidual) :
    Class0MassField :=
  R.toV30Residual.class0MassField

/-- The combined zero-error O2/localized endpoint surface inherits the class-0
mass field rebuilt from its carried narrow-support gate data. -/
theorem Erdos260V30O2LocalizedExitCapZeroErrorResidual.class0MassField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Class0MassField :=
  R.toV30Residual.class0MassField

/-- The combined empty-collar O2/localized endpoint surface inherits the class-0
mass field rebuilt from its carried narrow-support gate data. -/
theorem Erdos260V30O2LocalizedExitCapEmptyCollarResidual.class0MassField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Class0MassField :=
  R.toV30Residual.class0MassField

/-- The coordinate O2 endpoint surface inherits the class-0 mass field rebuilt
from its carried narrow-support gate data. -/
theorem Erdos260V30O2CollarCoordinateResidual.class0MassField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    Class0MassField :=
  R.toV30Residual.class0MassField

/-- The finite-error/zero-collar coordinate O2 endpoint surface inherits the
class-0 mass field rebuilt from its carried narrow-support gate data. -/
theorem Erdos260V30O2CollarCoordinateZeroErrorResidual.class0MassField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Class0MassField :=
  R.toV30Residual.class0MassField

/-- The empty-collar coordinate O2 endpoint surface inherits the class-0 mass
field rebuilt from its carried narrow-support gate data. -/
theorem Erdos260V30O2CollarCoordinateEmptyCollarResidual.class0MassField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Class0MassField :=
  R.toV30Residual.class0MassField

/-! ## Part 2a.  The class-1 carry realization package -/

/-- The class-1 carry data and Appendix-AA realization field of the v30 residual
are exactly the packaged Lane-J carry realization surface. -/
def Erdos260V30Residual.class1CarryInputs (R : Erdos260V30Residual) :
    V30Class1CarryRealizationInputs where
  C := R.class1C
  clean := R.class1Clean
  hreal := R.class1Realize

/-- The v30 residual supplies the boosted deep class-1 cap at level `0`. -/
theorem v30_class1DeepBoosted (R : Erdos260V30Residual) :
    DccClass1DeepResidual 0 :=
  V30Class1CarryRealizationInputs.deepResidual R.class1CarryInputs

/-- The localized endpoint surface keeps the same Appendix-AA/Lane-J
class-1 carry realization package as its projection to `Erdos260V30Residual`. -/
def Erdos260V30LocalizedExitCapResidual.class1CarryInputs
    (R : Erdos260V30LocalizedExitCapResidual) :
    V30Class1CarryRealizationInputs :=
  R.toV30Residual.class1CarryInputs

/-- The localized endpoint surface supplies the same level-`0` boosted
class-1 residual as its v30 projection. -/
theorem Erdos260V30LocalizedExitCapResidual.class1DeepBoosted
    (R : Erdos260V30LocalizedExitCapResidual) :
    DccClass1DeepResidual 0 :=
  V30Class1CarryRealizationInputs.deepResidual R.class1CarryInputs

/-- The combined zero-error O2/localized endpoint surface exposes the same
Appendix-AA/Lane-J class-1 carry realization package. -/
def Erdos260V30O2LocalizedExitCapZeroErrorResidual.class1CarryInputs
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    V30Class1CarryRealizationInputs :=
  R.toV30Residual.class1CarryInputs

/-- The combined zero-error O2/localized endpoint surface supplies the
level-`0` boosted class-1 residual. -/
theorem Erdos260V30O2LocalizedExitCapZeroErrorResidual.class1DeepBoosted
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    DccClass1DeepResidual 0 :=
  V30Class1CarryRealizationInputs.deepResidual R.class1CarryInputs

/-- The combined empty-collar O2/localized endpoint surface exposes the same
Appendix-AA/Lane-J class-1 carry realization package. -/
def Erdos260V30O2LocalizedExitCapEmptyCollarResidual.class1CarryInputs
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    V30Class1CarryRealizationInputs :=
  R.toV30Residual.class1CarryInputs

/-- The combined empty-collar O2/localized endpoint surface supplies the
level-`0` boosted class-1 residual. -/
theorem Erdos260V30O2LocalizedExitCapEmptyCollarResidual.class1DeepBoosted
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    DccClass1DeepResidual 0 :=
  V30Class1CarryRealizationInputs.deepResidual R.class1CarryInputs

/-- The coordinate O2 endpoint surface exposes the same Appendix-AA/Lane-J
class-1 carry realization package. -/
def Erdos260V30O2CollarCoordinateResidual.class1CarryInputs
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    V30Class1CarryRealizationInputs :=
  R.toV30Residual.class1CarryInputs

/-- The coordinate O2 endpoint surface supplies the level-`0` boosted class-1
residual. -/
theorem Erdos260V30O2CollarCoordinateResidual.class1DeepBoosted
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    DccClass1DeepResidual 0 :=
  V30Class1CarryRealizationInputs.deepResidual R.class1CarryInputs

/-- The finite-error/zero-collar coordinate O2 endpoint surface exposes the
same Appendix-AA/Lane-J class-1 carry realization package. -/
def Erdos260V30O2CollarCoordinateZeroErrorResidual.class1CarryInputs
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    V30Class1CarryRealizationInputs :=
  R.toV30Residual.class1CarryInputs

/-- The finite-error/zero-collar coordinate O2 endpoint surface supplies the
level-`0` boosted class-1 residual. -/
theorem Erdos260V30O2CollarCoordinateZeroErrorResidual.class1DeepBoosted
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    DccClass1DeepResidual 0 :=
  V30Class1CarryRealizationInputs.deepResidual R.class1CarryInputs

/-- The empty-collar coordinate O2 endpoint surface exposes the same
Appendix-AA/Lane-J class-1 carry realization package. -/
def Erdos260V30O2CollarCoordinateEmptyCollarResidual.class1CarryInputs
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    V30Class1CarryRealizationInputs :=
  R.toV30Residual.class1CarryInputs

/-- The empty-collar coordinate O2 endpoint surface supplies the level-`0`
boosted class-1 residual. -/
theorem Erdos260V30O2CollarCoordinateEmptyCollarResidual.class1DeepBoosted
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    DccClass1DeepResidual 0 :=
  V30Class1CarryRealizationInputs.deepResidual R.class1CarryInputs

/-- The v30 residual exposes the full v19 class-1 deep field rebuilt by the
Appendix-AA/Lane-J carry realization package. -/
theorem Erdos260V30Residual.class1DeepField (R : Erdos260V30Residual) :
    Class1DeepField :=
  V30Class1CarryRealizationInputs.class1DeepField R.class1CarryInputs

/-- The localized endpoint surface inherits the full class-1 deep field through
its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30LocalizedExitCapResidual.class1DeepField
    (R : Erdos260V30LocalizedExitCapResidual) :
    Class1DeepField :=
  R.toV30Residual.class1DeepField

/-- The combined zero-error O2/localized endpoint surface inherits the full
class-1 deep field. -/
theorem Erdos260V30O2LocalizedExitCapZeroErrorResidual.class1DeepField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Class1DeepField :=
  R.toV30Residual.class1DeepField

/-- The combined empty-collar O2/localized endpoint surface inherits the full
class-1 deep field. -/
theorem Erdos260V30O2LocalizedExitCapEmptyCollarResidual.class1DeepField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Class1DeepField :=
  R.toV30Residual.class1DeepField

/-- The coordinate O2 endpoint surface inherits the full class-1 deep field
through its projection to `Erdos260V30Residual`. -/
theorem Erdos260V30O2CollarCoordinateResidual.class1DeepField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    Class1DeepField :=
  R.toV30Residual.class1DeepField

/-- The finite-error/zero-collar coordinate O2 endpoint surface inherits the full
class-1 deep field. -/
theorem Erdos260V30O2CollarCoordinateZeroErrorResidual.class1DeepField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Class1DeepField :=
  R.toV30Residual.class1DeepField

/-- The empty-collar coordinate O2 endpoint surface inherits the full class-1
deep field. -/
theorem Erdos260V30O2CollarCoordinateEmptyCollarResidual.class1DeepField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Class1DeepField :=
  R.toV30Residual.class1DeepField

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
  class1DeepBoosted := v30_class1DeepBoosted R

/-- **THE v30 ENDPOINT**: `Erdos260Statement` from the distilled v30 residual, through
the keystone surface and the proved reduction `erdos260_of_keystoneResidual` (which
routes through the wave-19 convergence surface and the fully-corrected six-phase
ledger). -/
theorem erdos260_of_v30Residual (R : Erdos260V30Residual) : Erdos260Statement :=
  erdos260_of_keystoneResidual R.toKeystone

/-- Endpoint form where R4/R5 are supplied by localized exit caps rather than by
pre-packaged `K1SpanRarity` and `V30TopBandPushforward` fields. -/
theorem erdos260_of_v30LocalizedExitCapResidual
    (R : Erdos260V30LocalizedExitCapResidual) : Erdos260Statement :=
  erdos260_of_v30Residual R.toV30Residual

/-- Endpoint form with the off-pin field lowered to finite-error O2 collars plus
zero-collar proofs, and R4/R5 lowered to localized exit-cap suppliers. -/
theorem erdos260_of_v30O2LocalizedExitCapZeroErrorResidual
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260Statement :=
  erdos260_of_v30LocalizedExitCapResidual R.toLocalizedExitCapResidual

/-- Endpoint form with the off-pin field lowered to a finite-error O2 provider
with literal empty collars, and R4/R5 lowered to localized exit-cap suppliers. -/
theorem erdos260_of_v30O2LocalizedExitCapEmptyCollarResidual
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260Statement :=
  erdos260_of_v30O2LocalizedExitCapZeroErrorResidual R.toZeroErrorResidual

/-- Endpoint form where the off-pin residual is supplied by the concrete
coordinate-split zero-collar O2 provider surface.  The theorem is exactly as
conditional as `erdos260_of_v30Residual` on the remaining non-off-pin fields. -/
theorem erdos260_of_v30O2CollarCoordinateResidual
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    Erdos260Statement :=
  erdos260_of_v30Residual R.toV30Residual

/-- Endpoint form where the off-pin residual is supplied by the concrete
coordinate-split O2 collar surface with explicit finite-error collars, plus
proofs that those collars vanish. -/
theorem erdos260_of_v30O2CollarCoordinateZeroErrorResidual
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260Statement :=
  erdos260_of_v30O2CollarCoordinateResidual R.toO2CollarCoordinateResidual

/-- Endpoint form where the off-pin residual is supplied by the coordinate O2
collar surface with literal empty-collar facts. -/
theorem erdos260_of_v30O2CollarCoordinateEmptyCollarResidual
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260Statement :=
  erdos260_of_v30O2CollarCoordinateResidual R.toO2CollarCoordinateResidual

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

/-- Namespaced form of the v30 value-axis discharge. -/
theorem Erdos260V30Residual.value_axis_free (R : Erdos260V30Residual)
    (ctx : ActualFailureContext)
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
  v30_value_axis_free R ctx h1 h2 h4 h5 h6 h7 h8 h9

/-- Localized-cap v30 surfaces consume the value-classification guard through their
projection to the v30 residual. -/
theorem Erdos260V30LocalizedExitCapResidual.value_axis_free
    (R : Erdos260V30LocalizedExitCapResidual) (ctx : ActualFailureContext)
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
  R.toV30Residual.value_axis_free ctx h1 h2 h4 h5 h6 h7 h8 h9

/-- Combined zero-error O2/localized v30 surfaces inherit the same value-axis
discharge through their v30 projection. -/
theorem Erdos260V30O2LocalizedExitCapZeroErrorResidual.value_axis_free
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) (ctx : ActualFailureContext)
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
  R.toV30Residual.value_axis_free ctx h1 h2 h4 h5 h6 h7 h8 h9

/-- Combined empty-collar O2/localized v30 surfaces inherit the same value-axis
discharge through their v30 projection. -/
theorem Erdos260V30O2LocalizedExitCapEmptyCollarResidual.value_axis_free
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) (ctx : ActualFailureContext)
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
  R.toV30Residual.value_axis_free ctx h1 h2 h4 h5 h6 h7 h8 h9

/-- Coordinate O2 v30 surfaces inherit the same value-axis discharge through their
v30 projection. -/
theorem Erdos260V30O2CollarCoordinateResidual.value_axis_free
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateResidual (β := β) (A := A) P₀ Q)
    (ctx : ActualFailureContext)
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
  R.toV30Residual.value_axis_free ctx h1 h2 h4 h5 h6 h7 h8 h9

/-- Finite-error/zero-collar coordinate O2 v30 surfaces inherit the same
value-axis discharge through their v30 projection. -/
theorem Erdos260V30O2CollarCoordinateZeroErrorResidual.value_axis_free
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) (ctx : ActualFailureContext)
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
  R.toV30Residual.value_axis_free ctx h1 h2 h4 h5 h6 h7 h8 h9

/-- Empty-collar coordinate O2 v30 surfaces inherit the same value-axis discharge
through their v30 projection. -/
theorem Erdos260V30O2CollarCoordinateEmptyCollarResidual.value_axis_free
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V30O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) (ctx : ActualFailureContext)
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
  R.toV30Residual.value_axis_free ctx h1 h2 h4 h5 h6 h7 h8 h9

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
      "Erdos260V30Residual.toKeystone + erdos260_of_keystoneResidual.  The localized " ++
      "endpoint erdos260_of_v30LocalizedExitCapResidual replaces the carried R4/R5 " ++
      "fields spanRarity/topBand by localized exit-cap suppliers and rebuilds them " ++
      "through v30_spanRarity_of_cap and v30_topBandPushforward_of_cap.  The combined " ++
      "endpoint erdos260_of_v30O2LocalizedExitCapZeroErrorResidual uses both " ++
      "refinements at once: finite-error O2 collars plus four zero-collar proofs for " ++
      "offPin, and localized cap suppliers for R4/R5.  The parallel empty-collar " ++
      "combined endpoint erdos260_of_v30O2LocalizedExitCapEmptyCollarResidual uses " ++
      "the same localized suppliers but packages the four off-pin collars as literal " ++
      "empty-set facts.  The refined " ++
      "endpoint erdos260_of_v30O2CollarCoordinateResidual replaces the abstract offPin " ++
      "field by the coordinate-split zero-collar O2 provider surface and then projects " ++
      "back to Erdos260V30Residual.  The zero-error endpoint " ++
      "erdos260_of_v30O2CollarCoordinateZeroErrorResidual accepts the finite-error O2 " ++
      "collar provider plus four collar=0 proofs, converts it to the existing " ++
      "zero-collar surface, and then uses the same endpoint.",
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
    "OFF-PIN REFINEMENT: Erdos260V30O2CollarCoordinateResidual is the same residual " ++
      "surface except that offPin is replaced by " ++
      "V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs, i.e. the concrete " ++
      "coordinate-split zero-collar O2/AB/R provider for the four off-pin classes. " ++
      "This discharges none of the remaining provider mathematics, but it lowers the " ++
      "Lane-H offPin field to the AK/AD-facing interface already proved in Lane C. " ++
      "Erdos260V30O2CollarCoordinateZeroErrorResidual is the explicit finite-error " ++
      "variant: it uses the Lane-C toZeroCollarProvider bridge once the four collar " ++
      "cardinalities are proved zero. " ++
      "Erdos260V30O2CollarCoordinateEmptyCollarResidual packages the empty-collar " ++
      "version of the same finite-error surface and uses the proved Lane-C empty-collar " ++
      "bridge to reach the zero-collar endpoint without carrying four separate " ++
      "collar-cardinality fields.",
    "LOCALIZED R4/R5 REFINEMENT: Erdos260V30LocalizedExitCapResidual is the same " ++
      "residual surface except that topBand/spanRarity are replaced by " ++
      "V30LocalizedExitCapSuppliers: a top-band cap 64*agcTopBandDev < L plus " ++
      "band<=4, and per-span caps 32*(r+1)*localExitMass(m) < L on the exact " ++
      "densepack guard surface.  The projection reconstructs the old fields using " ++
      "the already-proved Lane-C bridges v30_topBandPushforward_of_cap and " ++
      "v30_spanRarity_of_cap.  V30LocalizedExitCapSuppliers.ofTopBandExitFree " ++
      "also accepts Appendix-P DscTopBandExitFree as the R5 source via " ++
      "v30_topBandCap_of_exitFree; ofTopBandExitFreeAndLocalExitLight additionally " ++
      "accepts K1LocalExitLight as the R4 source via v30_localExitLight_iff_spanCap. " ++
      "ofTopBandOnsets / ofTopBandOnsetsAndLocalExitLight additionally accept the " ++
      "MissDistanceClosure band-following onset supplier as the R5 source via " ++
      "v30_topBandCap_of_onsets.",
    "COMBINED LOWER-LEVEL ENDPOINT: Erdos260V30O2LocalizedExitCapZeroErrorResidual " ++
      "simultaneously lowers offPin to the finite-error coordinate O2 collar provider " ++
      "with zero-collar proofs and lowers R4/R5 to V30LocalizedExitCapSuppliers.  It " ++
      "projects through Erdos260V30LocalizedExitCapResidual, preserving the same " ++
      "remaining raw fields and adding no new theorem assumption beyond the two " ++
      "already recorded lower-level surfaces.  " ++
      "Erdos260V30O2LocalizedExitCapEmptyCollarResidual is the corresponding " ++
      "TeX-facing literal empty-collar version, using the packaged Lane-C " ++
      "empty-collar bridge instead of four separate collar-cardinality fields.",
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
#print axioms Erdos260V30Residual.returnGatesField
#print axioms Erdos260V30Residual.returnInteriorField
#print axioms Erdos260V30Residual.returnGatesOffTableField
#print axioms Erdos260V30Residual.returnInteriorOffTableField
#print axioms Erdos260V30Residual.densePackStartSpacingField
#print axioms Erdos260V30Residual.densePackClusterFloorField
#print axioms Erdos260V30Residual.densePackCoverOffTableField
#print axioms Erdos260V30Residual.densePackCoverField
#print axioms Erdos260V30Residual.densePackDensityOffTableField
#print axioms Erdos260V30Residual.densePackInteriorOffTableField
#print axioms Erdos260V30Residual.densePackDensityField
#print axioms Erdos260V30Residual.densePackInteriorField
#print axioms Erdos260V30Residual.class0MassField
#print axioms Erdos260V30Residual.class1CarryInputs
#print axioms v30_class1DeepBoosted
#print axioms Erdos260V30Residual.class1DeepField
#print axioms V30LocalizedExitCapSuppliers
#print axioms V30LocalizedExitCapSuppliers.ofTopBandExitFree
#print axioms V30LocalizedExitCapSuppliers.ofTopBandExitFreeAndLocalExitLight
#print axioms V30LocalizedExitCapSuppliers.ofTopBandOnsets
#print axioms V30LocalizedExitCapSuppliers.ofTopBandOnsetsAndLocalExitLight
#print axioms V30LocalizedExitCapSuppliers.topBand
#print axioms V30LocalizedExitCapSuppliers.spanRarity
#print axioms V30LocalizedExitCapSuppliers.laneGResidual
#print axioms V30LocalizedExitCapSuppliers.laneGResidual_topBand
#print axioms V30LocalizedExitCapSuppliers.laneGResidual_readTail
#print axioms Erdos260V30LocalizedExitCapResidual
#print axioms Erdos260V30LocalizedExitCapResidual.toV30Residual
#print axioms Erdos260V30LocalizedExitCapResidual.spanRarity
#print axioms Erdos260V30LocalizedExitCapResidual.topBand
#print axioms Erdos260V30LocalizedExitCapResidual.offPinDeliverables
#print axioms Erdos260V30LocalizedExitCapResidual.exitMassCore
#print axioms Erdos260V30LocalizedExitCapResidual.deepOrbitPinVoiding
#print axioms Erdos260V30LocalizedExitCapResidual.laneGResidual
#print axioms Erdos260V30LocalizedExitCapResidual.laneGResidual_topBand
#print axioms Erdos260V30LocalizedExitCapResidual.laneGResidual_readTail
#print axioms Erdos260V30LocalizedExitCapResidual.returnGatesField
#print axioms Erdos260V30LocalizedExitCapResidual.returnInteriorField
#print axioms Erdos260V30LocalizedExitCapResidual.returnGatesOffTableField
#print axioms Erdos260V30LocalizedExitCapResidual.returnInteriorOffTableField
#print axioms Erdos260V30LocalizedExitCapResidual.densePackStartSpacingField
#print axioms Erdos260V30LocalizedExitCapResidual.densePackClusterFloorField
#print axioms Erdos260V30LocalizedExitCapResidual.densePackCoverOffTableField
#print axioms Erdos260V30LocalizedExitCapResidual.densePackCoverField
#print axioms Erdos260V30LocalizedExitCapResidual.densePackDensityOffTableField
#print axioms Erdos260V30LocalizedExitCapResidual.densePackInteriorOffTableField
#print axioms Erdos260V30LocalizedExitCapResidual.densePackDensityField
#print axioms Erdos260V30LocalizedExitCapResidual.densePackInteriorField
#print axioms Erdos260V30LocalizedExitCapResidual.class0MassField
#print axioms Erdos260V30LocalizedExitCapResidual.class1CarryInputs
#print axioms Erdos260V30LocalizedExitCapResidual.class1DeepBoosted
#print axioms Erdos260V30LocalizedExitCapResidual.class1DeepField
#print axioms Erdos260V30LocalizedExitCapResidual.value_axis_free
#print axioms erdos260_of_v30LocalizedExitCapResidual
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.toLocalizedExitCapResidual
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.toV30Residual
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.offPinDeliverables
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.exitMassCore
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.deepOrbitPinVoiding
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.laneGResidual
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.laneGResidual_topBand
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.laneGResidual_readTail
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.returnGatesField
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.returnInteriorField
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.returnGatesOffTableField
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.returnInteriorOffTableField
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.densePackStartSpacingField
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.densePackClusterFloorField
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.densePackCoverOffTableField
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.densePackCoverField
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.densePackDensityOffTableField
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.densePackInteriorOffTableField
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.densePackDensityField
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.densePackInteriorField
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.class0MassField
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.class1CarryInputs
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.class1DeepBoosted
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.class1DeepField
#print axioms Erdos260V30O2LocalizedExitCapZeroErrorResidual.value_axis_free
#print axioms erdos260_of_v30O2LocalizedExitCapZeroErrorResidual
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.toZeroErrorResidual
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.toLocalizedExitCapResidual
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.toV30Residual
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.offPinDeliverables
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.exitMassCore
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.deepOrbitPinVoiding
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.laneGResidual
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.laneGResidual_topBand
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.laneGResidual_readTail
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.returnGatesField
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.returnInteriorField
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.returnGatesOffTableField
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.returnInteriorOffTableField
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.densePackStartSpacingField
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.densePackClusterFloorField
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.densePackCoverOffTableField
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.densePackCoverField
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.densePackDensityOffTableField
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.densePackInteriorOffTableField
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.densePackDensityField
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.densePackInteriorField
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.class0MassField
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.class1CarryInputs
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.class1DeepBoosted
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.class1DeepField
#print axioms Erdos260V30O2LocalizedExitCapEmptyCollarResidual.value_axis_free
#print axioms erdos260_of_v30O2LocalizedExitCapEmptyCollarResidual
#print axioms Erdos260V30O2CollarCoordinateResidual
#print axioms Erdos260V30O2CollarCoordinateResidual.toV30Residual
#print axioms Erdos260V30O2CollarCoordinateResidual.offPinDeliverables
#print axioms Erdos260V30O2CollarCoordinateResidual.exitMassCore
#print axioms Erdos260V30O2CollarCoordinateResidual.deepOrbitPinVoiding
#print axioms Erdos260V30O2CollarCoordinateResidual.returnGatesField
#print axioms Erdos260V30O2CollarCoordinateResidual.returnInteriorField
#print axioms Erdos260V30O2CollarCoordinateResidual.returnGatesOffTableField
#print axioms Erdos260V30O2CollarCoordinateResidual.returnInteriorOffTableField
#print axioms Erdos260V30O2CollarCoordinateResidual.densePackStartSpacingField
#print axioms Erdos260V30O2CollarCoordinateResidual.densePackClusterFloorField
#print axioms Erdos260V30O2CollarCoordinateResidual.densePackCoverOffTableField
#print axioms Erdos260V30O2CollarCoordinateResidual.densePackCoverField
#print axioms Erdos260V30O2CollarCoordinateResidual.densePackDensityOffTableField
#print axioms Erdos260V30O2CollarCoordinateResidual.densePackInteriorOffTableField
#print axioms Erdos260V30O2CollarCoordinateResidual.densePackDensityField
#print axioms Erdos260V30O2CollarCoordinateResidual.densePackInteriorField
#print axioms Erdos260V30O2CollarCoordinateResidual.class0MassField
#print axioms Erdos260V30O2CollarCoordinateResidual.class1CarryInputs
#print axioms Erdos260V30O2CollarCoordinateResidual.class1DeepBoosted
#print axioms Erdos260V30O2CollarCoordinateResidual.class1DeepField
#print axioms Erdos260V30O2CollarCoordinateResidual.value_axis_free
#print axioms erdos260_of_v30O2CollarCoordinateResidual
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.toO2CollarCoordinateResidual
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.toV30Residual
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.offPinDeliverables
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.exitMassCore
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.deepOrbitPinVoiding
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.returnGatesField
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.returnInteriorField
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.returnGatesOffTableField
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.returnInteriorOffTableField
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.densePackStartSpacingField
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.densePackClusterFloorField
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.densePackCoverOffTableField
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.densePackCoverField
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.densePackDensityOffTableField
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.densePackInteriorOffTableField
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.densePackDensityField
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.densePackInteriorField
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.class0MassField
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.class1CarryInputs
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.class1DeepBoosted
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.class1DeepField
#print axioms Erdos260V30O2CollarCoordinateZeroErrorResidual.value_axis_free
#print axioms erdos260_of_v30O2CollarCoordinateZeroErrorResidual
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.toO2CollarCoordinateResidual
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.toV30Residual
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.offPinDeliverables
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.exitMassCore
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.deepOrbitPinVoiding
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.returnGatesField
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.returnInteriorField
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.returnGatesOffTableField
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.returnInteriorOffTableField
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.densePackStartSpacingField
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.densePackClusterFloorField
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.densePackCoverOffTableField
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.densePackCoverField
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.densePackDensityOffTableField
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.densePackInteriorOffTableField
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.densePackDensityField
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.densePackInteriorField
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.class0MassField
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.class1CarryInputs
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.class1DeepBoosted
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.class1DeepField
#print axioms Erdos260V30O2CollarCoordinateEmptyCollarResidual.value_axis_free
#print axioms erdos260_of_v30O2CollarCoordinateEmptyCollarResidual
#print axioms v30_exitMassCore
#print axioms v30_offPin_deliverables
#print axioms v30_deepOrbitPin
#print axioms Erdos260V30Residual.exitMassCore
#print axioms Erdos260V30Residual.offPinDeliverables
#print axioms Erdos260V30Residual.deepOrbitPinVoiding
#print axioms Erdos260V30Residual.value_axis_free
#print axioms v30_value_axis_free
#print axioms v30_sevenths_reduces
#print axioms erdos260V30EndpointStatus_nonempty

end

end Erdos260
