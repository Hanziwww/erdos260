import Erdos260.CarryHighExcessUnconditionalProvider
import Erdos260.ChargeMultiplierClosure

/-!
# Erdős #260 — the P9 central charge bridge / J.1.1 seven-class routing residual

This module (NEW; it edits no existing file) attacks the **deepest** analytic atom of the
whole development: the `HighExcessRoutingResidualProvider`
(`CarryHighExcessUnconditionalProvider.lean`), the residual feeding the central charge
bridge `highExcessCharge` (roadmap **P9**, manuscript J.1.1 / L.2 / G.6 / I.4.1·K.1.3 /
N.24 / L.6.5).

## STEP 0 — the per-shell residual targets a PROVABLY EMPTY type (the heart, exactly located)

The provider must produce, for **every** failing shell with **arbitrary** six-phase data
`phases` (carrying only `trtNonneg`) and **arbitrary** carry data `carryData`, a
`ShellHighExcessRoutingResidual phases carryData`.  We first prove

```
shellHighExcessRoutingResidual_isEmpty :
  IsEmpty (ShellHighExcessRoutingResidual phases carryData)
```

for *every* `phases`/`carryData`: any inhabitant runs `toHighExcessChargeData` into the
(provably empty, `highExcessChargeData_isEmpty`) bridge type and yields `False`.  Hence a
provider is **logically a refutation of the failing shell**
(`highExcessRoutingProvider_refutes`): a `HighExcessRoutingResidualProvider` proves there
is *no* failing `cQ`-shell carrying both valid six-phase data and valid carry data.  This is
the entire mathematical content of the central charge bridge — it can **never** be inhabited
unconditionally without the genuine per-class analytic estimates, exactly as the manuscript
places the difficulty.  This is **not** a vacuous statement: the existing matched-charge track
(`Erdos260UnconditionalSeedClosureV3` / `Erdos260ChargeReduced` / `Erdos260SeedResidual`)
proves the analogous per-class bounds, but **only** for the *constructed* phases
`faithfulCapacityPhases budget ctx` and the context carry datum `ctx.n24CarryData`; those
field-level closers (`hChernoffField_ofMatching`, `Class1CNLChargeData.hCnl_ofShellCharge`,
`hDensePack_field_ofCardLe`, `seedHTRT`) are pinned to `ActualFailureContext` and do **not**
transfer to the provider's *arbitrary* `phases`/`carryData`.

## STEP 1 — the genuinely-generic skeleton, discharged here

What *is* generic (over arbitrary `phases`/`carryData`) and is wired in here:

* the seven-fibre mass-conservation identity and the augmented bridge
  `highExcessMass ≤ ClosurePhaseMass + oldResMass`
  (`RoutedHighExcessChargeDataOldRes.highExcess_le_phaseMass_add_oldRes`);
* the four-bound contradiction engine
  (`RoutedHighExcessChargeDataOldRes.refutes_failingShell`) with the **already-proved**
  constant condition `cStar·ξ + 1·c_* < cPr` (`manuscript_closure_pressure`);
* the per-class count×multiplier closer `routedClassMassOf_le_countMultiplier`
  (`ChargeMultiplierClosure`), generic in `carryData`/`route`/`phases`;
* the L.6.5 density-sensitive old-residual estimate `oldRes_le_of_density`
  (`ChargeBridgeReduction`), generic in the index set / per-index bound / endpoint count.

## STEP 2 — three conditional reductions to the SHARP residual

Each isolates exactly the genuinely-open per-class analytic estimates and discharges
everything else:

1. `highExcessRoutingFromRoutingZero` — from a seven-class routing with the **old-residual
   class carrying no routed mass** (`oldResMass = 0`, the genuine first-obstruction route's
   class-6 vacancy, `genuineChargeRoute_routed6_zero`).  Discharges the `oldResMass` choice and
   the Lemma-L.6.5 smallness `oldRes_le` outright.  Open: the four phase bounds (Chernoff /
   clean-CNL / DensePack / joint-TRT) against the arbitrary `phases`.
2. `highExcessRoutingFromCountCharge` — the manuscript J.1.7 / G.6 / K.1.1 **matched-charge**
   form: the Chernoff (0), clean-CNL (1), DensePack (3) bounds are reduced, via the generic
   `routedClassMassOf_le_countMultiplier`, to per-class `count × multiplier` charge data
   (a per-element window-excess cap + a fibre count + the `count·mult ≤ term` numeric)
   against the arbitrary `phases`.  The joint Tower+Return+Run (2+4+5) N.24 compression is
   kept joint (those classes are mutually recursive — never bounded individually).
3. `highExcessRoutingFromFull` — the **faithful trichotomy** form: the four phase bounds plus
   the genuine nonzero L.6.4 old-residual branch mass, whose L.6.5 smallness is closed via the
   generic `oldRes_le_of_density` from the L.20/L.21 per-index multiplier×support bound and the
   L.22 low-density endpoint count.

## Discipline

No `sorry`/`axiom`/`admit`/`native_decide`/new axiom.  No degenerate / empty / vacuous /
`PEmpty` / false-hypothesis witness: every reduction routes through the genuine bridge
skeleton and the genuine contradiction engine, with the open per-class estimates carried as
the *explicit* residual (never assumed `False`).  The `oldResMass = 0` choice in reduction (1)
is faithful — it is exactly the genuine route's proved class-6 vacancy
(`genuineChargeRoute_routed6_zero`), the slack old-residual accounting term being unpopulated —
and reduction (3) carries the genuine nonzero old-residual with its L.6.5 closure.  Every def
below is checked to depend only on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The per-shell routing residual targets a provably empty type -/

/-- **The per-shell routing residual is empty for any genuine phase/carry data.**

Any `ShellHighExcessRoutingResidual phases carryData` runs `toHighExcessChargeData` (the
contradiction engine with the proved pressure floor, phase budget, and constant condition)
into the bridge type `HighExcessChargeData phases carryData`, which is itself empty
(`highExcessChargeData_isEmpty`: `cPr·X ≤ highExcessMass` while
`ClosurePhaseMass ≤ cStar·ξ·X < cPr·X`).  Hence the per-shell residual is uninhabitable — it
encodes "this failing shell does not exist", the manuscript's "no low-density shell". -/
theorem shellHighExcessRoutingResidual_isEmpty
    {shell : FailingDyadicShell}
    (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr) :
    IsEmpty (ShellHighExcessRoutingResidual phases carryData) :=
  ⟨fun res =>
    (highExcessChargeData_isEmpty phases carryData).false res.toHighExcessChargeData⟩

/-- **A high-excess routing provider refutes every failing shell.**

Because each per-shell residual is empty, a `HighExcessRoutingResidualProvider` yields `False`
from *any* failing `cQ`-shell equipped with six-phase data (`trtNonneg`) and carry data.  So
the provider is logically equivalent to "no such failing shell exists" — the genuine analytic
heart, never inhabitable from a single shell's hypotheses without the per-class estimates. -/
theorem highExcessRoutingProvider_refutes
    (P : HighExcessRoutingResidualProvider)
    (shell : FailingDyadicShell) (hcQ : shell.cQ = erdos260Constants.cQ)
    (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
    (hph : phases.trtNonneg) :
    False :=
  (shellHighExcessRoutingResidual_isEmpty phases carryData).false
    (P.residual shell hcQ phases carryData hph)

/-! ## 2.  Reduction (1) — the old-residual class carries no routed mass (`oldResMass = 0`)

The genuine first-obstruction route routes every high-excess start into one of the **six**
phase classes; the seventh (old-residual) class carries no routed mass
(`genuineChargeRoute_routed6_zero`).  So a seven-class routing with `oldResMass = 0` already
discharges the Lemma-L.6.5 smallness `oldRes_le` (trivially `0 ≤ 1·c_*·X`), leaving only the
four genuine phase bounds. -/

/-- **`oldResMass = 0` closure.**  A seven-class routing whose old-residual class carries no
routed mass (`RoutedHighExcessChargeDataOldRes phases carryData 0`, whose `hOldRes` reads
`routedClassMassOf … 6 ≤ 0`) yields a full `ShellHighExcessRoutingResidual`, with the L.6.5
smallness `oldRes_le : 0 ≤ 1·manuscriptCstarSmall·X` discharged by nonnegativity. -/
def routingZeroToShell
    {shell : FailingDyadicShell}
    {phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell erdos260Constants.cPr}
    (data : RoutedHighExcessChargeDataOldRes phases carryData 0) :
    ShellHighExcessRoutingResidual phases carryData where
  oldResMass := 0
  routing := data
  oldRes_le := by
    have hX : (0 : ℝ) ≤ (shell.X : ℝ) := shell.X_nonneg_real
    have hc : (0 : ℝ) ≤ manuscriptCstarSmall := manuscriptCstarSmall_pos.le
    exact mul_nonneg (mul_nonneg (by norm_num) hc) hX

/-- **The sharp residual for reduction (1).**  For every failing `cQ`-shell with arbitrary
six-phase data (`trtNonneg`) and arbitrary carry data, a seven-class routing
`RoutedHighExcessChargeDataOldRes phases carryData 0` — i.e. the route + the four genuine
phase bounds (Chernoff 0, clean-CNL 1, DensePack 3, joint Tower+Return+Run 2+4+5) + the
class-6 vacancy `routedClassMassOf … 6 ≤ 0`.  Nothing about `oldResMass`/L.6.5 survives. -/
structure HighExcessRoutingZeroResidual where
  /-- The genuine seven-class first-obstruction routing with the old-residual class empty. -/
  routingZero :
    ∀ (shell : FailingDyadicShell), shell.cQ = erdos260Constants.cQ →
      ∀ (phases :
          SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
        (carryData : CarryDataFromFailure shell erdos260Constants.cPr),
        phases.trtNonneg →
          RoutedHighExcessChargeDataOldRes phases carryData 0

/-- **The provider from reduction (1).**  Drops the `oldResMass = 0` seven-class routing into
the `HighExcessRoutingResidualProvider` shape (the central-charge-bridge `highExcessCharge`
field, modulo the four per-class phase bounds). -/
def highExcessRoutingFromRoutingZero (h : HighExcessRoutingZeroResidual) :
    HighExcessRoutingResidualProvider where
  residual := fun shell hcQ phases carryData hph =>
    routingZeroToShell (h.routingZero shell hcQ phases carryData hph)

/-! ## 3.  Reduction (2) — the manuscript matched-charge (count × multiplier) form

Each separable phase class (Chernoff 0 / clean-CNL 1 / DensePack 3) reduces, through the
generic proved core `routedClassMassOf_le_countMultiplier`, to its manuscript charging data:
a per-element window-excess multiplier (the K.1.2/L.20 active-window gap cap, J.1.7 / G.6 /
K.1.1) and a fibre count (I.4.2 progress count / L.1.2 cluster count / K.1.1 endpoint count),
with the numeric `count·mult ≤ term` against the *arbitrary* given `phases`.  The
Tower+Return+Run classes (2+4+5) are kept **jointly** bounded (N.24 same-threshold
compression) — they are mutually recursive and are never bounded individually. -/

/-- **The per-shell matched-charge data (manuscript J.1.7 / G.6 / K.1.1 + N.24).**

Reduces the three separable per-class bounds to count×multiplier charge data against an
arbitrary `phases`, plus the joint N.24 Tower+Return+Run bound and the class-6 vacancy. -/
structure ShellRoutingCountCharge
    {shell : FailingDyadicShell}
    (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr) where
  /-- The seven-class first-obstruction routing. -/
  route : Nat → Fin 7
  /-- **Class 6 vacancy** — the genuine route charges no old-residual mass
  (`genuineChargeRoute_routed6_zero`). -/
  hRoute6 : routedClassMassOf carryData route 6 = 0
  /-- **Class 0 (Chernoff, J.1.7 / 22.1A)** — per-element window-excess multiplier. -/
  mult0 : ℝ
  /-- The class-0 multiplier is nonnegative. -/
  hmult0 : 0 ≤ mult0
  /-- Each class-0 start charges window excess at most `mult0` (K.1.2/L.20 active-window gap). -/
  hpoint0 : ∀ k ∈ routedFibre carryData route 0,
    windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ mult0
  /-- The class-0 fibre count (I.4.2 progress-endpoint count). -/
  count0 : ℝ
  /-- The class-0 fibre cardinality bound. -/
  hcard0 : ((routedFibre carryData route 0).card : ℝ) ≤ count0
  /-- The 22.1A area numeric — `count0·mult0` fits the Chernoff term of the given phases. -/
  hbud0 : count0 * mult0 ≤ termChernoff phases.toClosurePhaseData
  /-- **Class 1 (clean-CNL, G.6 / G.35)** — per-element window-excess multiplier. -/
  mult1 : ℝ
  /-- The class-1 multiplier is nonnegative. -/
  hmult1 : 0 ≤ mult1
  /-- Each class-1 start charges window excess at most `mult1` (per-codeword Kraft rate). -/
  hpoint1 : ∀ k ∈ routedFibre carryData route 1,
    windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ mult1
  /-- The class-1 fibre count (L.1.2 cluster count). -/
  count1 : ℝ
  /-- The class-1 fibre cardinality bound. -/
  hcard1 : ((routedFibre carryData route 1).card : ℝ) ≤ count1
  /-- The G.35 Kraft numeric — `count1·mult1` fits the clean-CNL term of the given phases. -/
  hbud1 : count1 * mult1 ≤ termCnl phases.toClosurePhaseData
  /-- **Class 3 (DensePack, K.1.1 / K.1.3)** — per-element window-excess multiplier. -/
  mult3 : ℝ
  /-- The class-3 multiplier is nonnegative. -/
  hmult3 : 0 ≤ mult3
  /-- Each class-3 start charges window excess at most `mult3` (J.D unit charge). -/
  hpoint3 : ∀ k ∈ routedFibre carryData route 3,
    windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ mult3
  /-- The class-3 fibre count (K.1.1 endpoint-disjoint count). -/
  count3 : ℝ
  /-- The class-3 fibre cardinality bound. -/
  hcard3 : ((routedFibre carryData route 3).card : ℝ) ≤ count3
  /-- The K.1.3 coarea numeric — `count3·mult3` fits the DensePack term of the given phases. -/
  hbud3 : count3 * mult3 ≤ termDensePack phases.toClosurePhaseData
  /-- **Classes 2 + 4 + 5 — Tower + Return + Run, jointly** (N.24 same-threshold compression). -/
  hTRT : routedClassMassOf carryData route 2 + routedClassMassOf carryData route 4
        + routedClassMassOf carryData route 5
      ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
        + termRun phases.toClosurePhaseData

/-- **The matched-charge data builds the `oldResMass = 0` seven-class routing.**  The three
separable bounds are discharged from the count×multiplier data through the generic proved
core `routedClassMassOf_le_countMultiplier`; the joint N.24 bound and the class-6 vacancy are
carried directly. -/
def ShellRoutingCountCharge.toRouting
    {shell : FailingDyadicShell}
    {phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell erdos260Constants.cPr}
    (C : ShellRoutingCountCharge phases carryData) :
    RoutedHighExcessChargeDataOldRes phases carryData 0 where
  route := C.route
  hChernoff :=
    le_trans (routedClassMassOf_le_countMultiplier carryData C.route 0
      C.hpoint0 C.hmult0 C.hcard0) C.hbud0
  hCnl :=
    le_trans (routedClassMassOf_le_countMultiplier carryData C.route 1
      C.hpoint1 C.hmult1 C.hcard1) C.hbud1
  hDensePack :=
    le_trans (routedClassMassOf_le_countMultiplier carryData C.route 3
      C.hpoint3 C.hmult3 C.hcard3) C.hbud3
  hTRT := C.hTRT
  hOldRes := le_of_eq C.hRoute6

/-- **The sharp residual for reduction (2)** — the matched-charge data per failing shell. -/
structure HighExcessRoutingCountResidual where
  /-- The manuscript matched-charge data for every failing `cQ`-shell / arbitrary phases / carry. -/
  charge :
    ∀ (shell : FailingDyadicShell), shell.cQ = erdos260Constants.cQ →
      ∀ (phases :
          SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
        (carryData : CarryDataFromFailure shell erdos260Constants.cPr),
        phases.trtNonneg →
          ShellRoutingCountCharge phases carryData

/-- The matched-charge residual yields the `oldResMass = 0` routing residual. -/
def HighExcessRoutingCountResidual.toZeroResidual (h : HighExcessRoutingCountResidual) :
    HighExcessRoutingZeroResidual where
  routingZero := fun shell hcQ phases carryData hph =>
    (h.charge shell hcQ phases carryData hph).toRouting

/-- **The provider from reduction (2)** — the manuscript matched-charge (count×multiplier)
form of the central charge bridge. -/
def highExcessRoutingFromCountCharge (h : HighExcessRoutingCountResidual) :
    HighExcessRoutingResidualProvider :=
  highExcessRoutingFromRoutingZero h.toZeroResidual

/-! ## 4.  Reduction (3) — the faithful trichotomy (genuine nonzero L.6.4 / L.6.5 old-residual)

The fully faithful form: the four phase bounds plus a genuine nonzero old-residual branch mass
`OldRes = ∑_{k∈K} oldResAt k` (Lemma L.6.4), whose smallness `OldRes ≤ 1·c_*·X` is closed
through the generic proved core `oldRes_le_of_density` (Lemma L.6.5) from the L.20/L.21
per-index multiplier×support bound and the L.22 low-density endpoint count. -/

/-- **The per-shell faithful trichotomy residual.**  The four phase bounds + the genuine L.6.4
old-residual branch mass with its L.6.5 inputs (against an arbitrary `phases`/`carryData`). -/
structure ShellRoutingWithOldRes
    {shell : FailingDyadicShell}
    (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr) where
  /-- The seven-class first-obstruction routing. -/
  route : Nat → Fin 7
  /-- **Class 0 — Chernoff (J.1.7 / 22.1A area).** -/
  hChernoff : routedClassMassOf carryData route 0 ≤ termChernoff phases.toClosurePhaseData
  /-- **Class 1 — clean-CNL (G.6 / G.35 Kraft).** -/
  hCnl : routedClassMassOf carryData route 1 ≤ termCnl phases.toClosurePhaseData
  /-- **Class 3 — DensePack (K.1.1 / K.1.3 coarea).** -/
  hDensePack : routedClassMassOf carryData route 3 ≤ termDensePack phases.toClosurePhaseData
  /-- **Classes 2 + 4 + 5 — Tower + Return + Run, jointly** (N.24 same-threshold compression). -/
  hTRT : routedClassMassOf carryData route 2 + routedClassMassOf carryData route 4
        + routedClassMassOf carryData route 5
      ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
        + termRun phases.toClosurePhaseData
  /-- **L.6.4 retained terminal hit-index set** `K`. -/
  oldResIdx : Finset ℕ
  /-- **L.6.4 per-index old-residual mass** `oldResAt k`. -/
  oldResAt : ℕ → ℝ
  /-- **Class 6 — the v5 old-residual leakage** routed bound (Lemma L.6.4). -/
  hOldRes : routedClassMassOf carryData route 6 ≤ ∑ k ∈ oldResIdx, oldResAt k
  /-- L.20 residual multiplier constant `C_res` (multiplier is `C_res·Y`). -/
  Cres : ℝ
  /-- The active floor `Y` (the L.20 multiplier is linear in `Y`). -/
  Y : ℝ
  /-- L.21 endpoint-support constant `C_supp`. -/
  Csupp : ℝ
  /-- The canonical block fraction `|I_j|`. -/
  Ij : ℝ
  /-- **L.20 / L.21 per-index bound** — `oldResAt k ≤ (C_res·Y)·(C_supp·|I_j|)`. -/
  hpoint : ∀ k ∈ oldResIdx, oldResAt k ≤ (Cres * Y) * (Csupp * Ij)
  /-- Nonnegativity of the per-index bound. -/
  hbound_nonneg : 0 ≤ (Cres * Y) * (Csupp * Ij)
  /-- **L.22 low-density endpoint count** — the endpoint count times the per-index bound fits the
  L.6.5 target `1·c_*·X`. -/
  hcard : ((oldResIdx.card : ℝ)) * ((Cres * Y) * (Csupp * Ij))
      ≤ 1 * manuscriptCstarSmall * (shell.X : ℝ)

/-- **The faithful trichotomy data builds the full per-shell residual.**  The old-residual mass
is the genuine L.6.4 branch mass; its L.6.5 smallness `oldRes_le` is closed by the generic
`oldRes_le_of_density` and the low-density endpoint count `hcard`. -/
def ShellRoutingWithOldRes.toShell
    {shell : FailingDyadicShell}
    {phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell erdos260Constants.cPr}
    (C : ShellRoutingWithOldRes phases carryData) :
    ShellHighExcessRoutingResidual phases carryData where
  oldResMass := ∑ k ∈ C.oldResIdx, C.oldResAt k
  routing :=
    { route := C.route
      hChernoff := C.hChernoff
      hCnl := C.hCnl
      hDensePack := C.hDensePack
      hTRT := C.hTRT
      hOldRes := C.hOldRes }
  oldRes_le :=
    le_trans (oldRes_le_of_density C.hpoint C.hbound_nonneg (le_refl _)) C.hcard

/-- **The sharp residual for reduction (3)** — the faithful trichotomy data per failing shell. -/
structure HighExcessRoutingFullResidual where
  /-- The faithful trichotomy data for every failing `cQ`-shell / arbitrary phases / carry. -/
  full :
    ∀ (shell : FailingDyadicShell), shell.cQ = erdos260Constants.cQ →
      ∀ (phases :
          SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
        (carryData : CarryDataFromFailure shell erdos260Constants.cPr),
        phases.trtNonneg →
          ShellRoutingWithOldRes phases carryData

/-- **The provider from reduction (3)** — the faithful trichotomy form, with the genuine
nonzero L.6.4 old-residual and its L.6.5 closure. -/
def highExcessRoutingFromFull (h : HighExcessRoutingFullResidual) :
    HighExcessRoutingResidualProvider where
  residual := fun shell hcQ phases carryData hph =>
    (h.full shell hcQ phases carryData hph).toShell

/-! ## 5.  Honest residual inventory — the per-class verdict -/

/-- The precise post-reduction status of the P9 central charge bridge / J.1.1 routing. -/
def highExcessRoutingResiduals : List String :=
  [ "CHARACTERIZATION — shellHighExcessRoutingResidual_isEmpty: for EVERY phases/carryData the " ++
      "per-shell residual ShellHighExcessRoutingResidual is IsEmpty (any inhabitant runs " ++
      "toHighExcessChargeData into the provably-empty bridge, highExcessChargeData_isEmpty). " ++
      "highExcessRoutingProvider_refutes: a provider therefore refutes every failing cQ-shell. " ++
      "The provider is the irreducible analytic heart; it is universal over ARBITRARY phases/" ++
      "carryData, so the matched-charge track's field closers (hChernoffField_ofMatching, " ++
      "Class1CNLChargeData.hCnl_ofShellCharge, hDensePack_field_ofCardLe, seedHTRT), pinned to " ++
      "faithfulCapacityPhases/ctx.n24CarryData, do NOT transfer.",
    "DISCHARGED (skeleton) — the seven-fibre mass conservation + augmented bridge " ++
      "(highExcess_le_phaseMass_add_oldRes) + the four-bound contradiction engine " ++
      "(refutes_failingShell) with the PROVED constant condition cStar*xi + 1*c_* < cPr " ++
      "(manuscript_closure_pressure). All generic over arbitrary phases/carryData.",
    "DISCHARGED (class 6 + L.6.5, reduction 1) — oldResMass = 0 with the class-6 vacancy " ++
      "routedClassMassOf … 6 ≤ 0 (the genuine first-obstruction route never populates the " ++
      "old-residual class, genuineChargeRoute_routed6_zero). oldRes_le : 0 ≤ 1*c_**X by " ++
      "nonnegativity (manuscriptCstarSmall_pos, X_nonneg_real). NO L.6.5 needed.",
    "CLOSED-TO-CORE (class 6 + L.6.5, reduction 3) — the genuine nonzero L.6.4 branch mass " ++
      "OldRes = ∑_{k∈K} oldResAt k; oldRes_le closed by the generic PROVED oldRes_le_of_density " ++
      "(L.6.5) from the L.20/L.21 per-index bound (Cres*Y)*(Csupp*Ij) and the L.22 low-density " ++
      "endpoint count. The genuine analytic input is the L.22 count (multiplier linear in Y).",
    "OPEN (class 0, Chernoff — J.1.7 / 22.1A) — routedClassMassOf … 0 ≤ termChernoff phases, for " ++
      "ARBITRARY phases. Reduced (reduction 2) via the PROVED generic core " ++
      "routedClassMassOf_le_countMultiplier to the matched J.1.7 charge: a per-element " ++
      "window-excess multiplier (K.1.2/L.20 active-window gap) + the I.4.2 progress-endpoint " ++
      "count + the 22.1A area numeric count0*mult0 ≤ termChernoff. The 22.1A area family-sum " ++
      "value against the GIVEN phases is the irreducible analytic content.",
    "OPEN (class 1, clean-CNL — G.6 / G.35) — routedClassMassOf … 1 ≤ termCnl phases, for " ++
      "ARBITRARY phases. Reduced (reduction 2) to the matched per-codeword Kraft charge: a " ++
      "per-element multiplier (2^{-BND}-rate) + the L.1.2 cluster count + the G.35 Kraft numeric " ++
      "count1*mult1 ≤ termCnl. The G.35 weighted-Kraft family-sum against the GIVEN phases is the " ++
      "irreducible analytic content.",
    "OPEN (class 3, DensePack — I.4.1 / K.1.1·K.1.3) — routedClassMassOf … 3 ≤ termDensePack " ++
      "phases, for ARBITRARY phases. Reduced (reduction 2) to the matched K.1.1 coarea charge: the " ++
      "J.D unit window-excess charge + the K.1.1 endpoint-disjoint count + the K.1.3 coarea numeric " ++
      "count3*mult3 ≤ termDensePack. The K.1.1/K.1.3 endpoint-disjoint cover against the GIVEN " ++
      "phases is the irreducible analytic content.",
    "OPEN (joint TRT, classes 2+4+5 — N.24) — routedClassMassOf … 2 + … 4 + … 5 ≤ termTower + " ++
      "termReturn + termRun phases, for ARBITRARY phases. Kept JOINT (Tower/Return/Run are " ++
      "mutually recursive; never bounded individually). The N.24 same-threshold (TRT) compression " ++
      "against the GIVEN phases is the irreducible analytic content (I.4.1 active-floor count + " ++
      "I.5.2 run-mass floor + M.2.1 per-slice Return count).",
    "ENDPOINTS — highExcessRoutingFromRoutingZero (oldResMass=0), highExcessRoutingFromCountCharge " ++
      "(matched count*multiplier form), highExcessRoutingFromFull (faithful L.6.4/L.6.5 " ++
      "trichotomy) : each SharpResidual → HighExcessRoutingResidualProvider. The provider drops " ++
      "into Erdos260CapstoneResidual.highExcessRouting (erdos260_capstone). Axioms: " ++
      "[propext, Classical.choice, Quot.sound]." ]

theorem highExcessRoutingResiduals_nonempty : highExcessRoutingResiduals ≠ [] := by
  simp [highExcessRoutingResiduals]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms shellHighExcessRoutingResidual_isEmpty
#print axioms highExcessRoutingProvider_refutes
#print axioms routingZeroToShell
#print axioms highExcessRoutingFromRoutingZero
#print axioms ShellRoutingCountCharge.toRouting
#print axioms highExcessRoutingFromCountCharge
#print axioms ShellRoutingWithOldRes.toShell
#print axioms highExcessRoutingFromFull

end

end Erdos260
