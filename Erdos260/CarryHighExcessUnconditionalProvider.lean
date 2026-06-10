import Mathlib
import Erdos260.PressureFloorConstruction
import Erdos260.PositiveDensityRichShell
import Erdos260.ChargeBridgeContradiction
import Erdos260.ResidualScalarBudgets

/-!
# Carry data (Lemma 21.1) and central charge bridge (P9): sharpest unconditional providers

This file pushes the two deepest provider fields of `GlobalAssemblyCoreInputs`
(`GlobalClosureAssembly.lean`) — `carryData` (the Lemma 21.1 positive-density
pressure floor) and `highExcessCharge` (the central charge bridge, roadmap P9) —
as far toward an *unconditional* inhabitant as the current development allows,
and isolates the **single sharpest honest residual** of each.

It edits no shared file; it only assembles already-proved lemmas.

## `carryData` — reduced to the SINGLE residual `1 ≤ supportCount d X`

The field asks, for every failing dyadic shell that is `aboveCarryThreshold`
(`carryThreshold (carryB Q + 19) ≤ X`, i.e. the manuscript carry-large scale
`X ≥ 2^(carryB Q + 25)`), for a `CarryDataFromFailure shell cPr`.

`carryDataFromGate` builds it **with everything proved except one hypothesis**:

* the dyadic structure `X = 2^L` — proved (`Classical.choose shell.hXdyadic`);
* the gap constant `Q·4 ≤ 2^(carryB Q)` — proved (`carryB_spec`);
* the carry scale `carryB Q + 25 ≤ L` — **proved from the gate**
  (`carryLarge_of_carryThreshold_le`);
* the shell richness `L + 1 ≤ |supportShell d X|` — **proved from the gate plus
  the residual** by the genuine rationality-driven carry-gap content
  (`richShell_of_failure_large`, manuscript Theorem A.1 / `positive-dyadic-density`);
* the K.4 numerical allocation `hAlloc` — proved (`hAlloc_manuscript_strict`,
  inside `carryDataPinned`).

The **only** input not derivable from `aboveCarryThreshold` is

```
hSupportBefore : 1 ≤ supportCount shell.d shell.X      -- a support hit at or below X
```

This is genuinely irreducible *at this gate*: a nonterminating shell whose first
hit sits beyond `X` has `supportCount d X = 0` and `firstIndexAbove X = 0`, so the
window construction (which needs a hit `a (i-1) ≤ X`) cannot start, and no
`CarryDataFromFailure` of this shape exists (`richShell_of_failure_large`'s
module doc records the same).  It is a *scale* condition depending on `d` (where
the first hit lies), not just on `Q`.  Under the manuscript's genuine
"sufficiently large dyadic `X`" threshold `appendixNChainCompressionStartThreshold`
(which the global pipeline already pins `startThreshold` to) the residual VANISHES
— `carryDataFromStartThreshold` builds the carry data with **no** residual at all,
since that threshold supplies the support hit (`richShell_of_startThreshold_le`).

## `highExcessCharge` — reduced to the J.1.1 routing + L.6.5 smallness (irreducible)

`HighExcessChargeData phases carryData` carries the single inequality
`highExcessMass (…) ≤ ClosurePhaseMass phases`.  **For any genuine `carryData`
this inequality is FALSE**: the carry pressure floor gives
`cPr·X ≤ highExcessMass`, while every six-phase budget gives
`ClosurePhaseMass ≤ cStar·ξ·X < cPr·X` (`erdos260Constants.constantsCompatible`).
We prove this outright (`highExcess_strictly_exceeds_phaseMass`,
`highExcessChargeData_isEmpty`): the bridge type is *uninhabitable* for a real
failing shell.  Hence the **only** way to inhabit it is to derive `False` from the
hypothesis that the failing shell exists — which is exactly the manuscript's
"no low-density shell exists", encoded by the v5 contradiction engine
`RoutedHighExcessChargeDataOldRes.refutes_failingShell`.

`ShellHighExcessRoutingResidual` bundles the precise remaining analytic content:

* `routing : RoutedHighExcessChargeDataOldRes phases carryData oldResMass` — the
  J.1.1 seven-class first-obstruction priority routing with its FIVE per-class mass
  bounds (Chernoff `0`, clean-CNL `1`, DensePack `3`, the joint
  Tower+Return+Run TRT bound `2+4+5` of N.24, and the old-residual class `6`).
  The routing skeleton (mass conservation `highExcessMass = ∑ routedClassMass`) is
  PROVED; the five per-class bounds are the genuinely deep L.2 / N.3.3 / N.24 /
  L.6.4 family/transcript dynamics — the analytic heart that does NOT close here.
* `oldRes_le : oldResMass ≤ 1·c_*·X` — the Lemma L.6.5 old-residual smallness.

Given those, `toHighExcessChargeData` runs `refutes_failingShell` (with the
**already-proved** constant condition `manuscript_closure_pressure`,
`cStar·ξ + 1·c_* < cPr`) to get `False`, and `.elim`s into the (empty) bridge type.
The constant condition is NOT a residual here.

## Discipline

No `sorry`/`axiom`/`admit`/`native_decide`/new axiom.  No degenerate, vacuous or
false-hypothesis witnesses: `carryDataFromGate` is a genuine construction, and the
`highExcessCharge` `False.elim` is fed by `refutes_failingShell`, whose own inputs
(`routing`, `oldRes_le`) are carried as the *explicit residual* — not faked.  Every
def below is checked to depend only on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## Part 1 — `carryData`: the Lemma 21.1 pressure-floor provider -/

/--
**Carry data from the `aboveCarryThreshold` gate, modulo `supportCount ≥ 1`.**

For a failing dyadic shell that is `aboveCarryThreshold`, plus the single residual
`1 ≤ supportCount shell.d shell.X` (a support hit at or below `X`), this builds a
genuine `CarryDataFromFailure shell erdos260Constants.cPr`.

All other inputs of `carryDataPinned` are discharged here:
* the dyadic exponent `L := Classical.choose shell.hXdyadic` and `X = 2^L`;
* the carry gap constant `B := carryB shell.Q`, `Q·4 ≤ 2^B` (`carryB_spec`);
* the carry scale `B + 25 ≤ L` (`carryLarge_of_carryThreshold_le`, from the gate);
* the shell richness `L + 1 ≤ |supportShell d X|`
  (`richShell_of_failure_large`, the genuine manuscript A.1 carry-gap content).
-/
def carryDataFromGate
    (shell : FailingDyadicShell)
    (hgate : shell.aboveCarryThreshold)
    (hSupportBefore : 1 ≤ supportCount shell.d shell.X) :
    CarryDataFromFailure shell erdos260Constants.cPr :=
  carryDataPinned shell (Classical.choose shell.hXdyadic) (carryB shell.Q)
    (Classical.choose_spec shell.hXdyadic)
    (carryB_spec shell.hQ)
    (by
      have hlarge' : carryThreshold (carryB shell.Q + 19) ≤ shell.X := hgate
      exact carryLarge_of_carryThreshold_le (Classical.choose_spec shell.hXdyadic) hlarge')
    (richShell_of_failure_large shell (Classical.choose_spec shell.hXdyadic)
      hSupportBefore hgate)
    hSupportBefore

/--
**The Lemma 21.1 unscaled pressure floor holds for the constructed carry data.**

`cPr · X ≤ highExcessMass (highExcessStarts …) …` — the headline pressure floor,
for the genuinely-constructed `carryDataFromGate`.  (Reuses
`carryData_pressureFloor`.)
-/
theorem carryDataFromGate_pressureFloor
    (shell : FailingDyadicShell)
    (hgate : shell.aboveCarryThreshold)
    (hSupportBefore : 1 ≤ supportCount shell.d shell.X) :
    erdos260Constants.cPr * (shell.X : ℝ) ≤
      highExcessMass
        (highExcessStarts (carryDataFromGate shell hgate hSupportBefore).starts
          (hitGap (carryDataFromGate shell hgate hSupportBefore).a)
          (carryDataFromGate shell hgate hSupportBefore).r
          (carryDataFromGate shell hgate hSupportBefore).T
          (carryDataFromGate shell hgate hSupportBefore).Y)
        (hitGap (carryDataFromGate shell hgate hSupportBefore).a)
        (carryDataFromGate shell hgate hSupportBefore).r
        (carryDataFromGate shell hgate hSupportBefore).T :=
  carryData_pressureFloor erdos260Constants.cPr_pos.le _

/--
**The single carry-side residual** (manuscript "sufficiently large dyadic `X`",
the `d`-dependent first-hit part not captured by the `Q`-only carry-scale gate).

This is the *only* hypothesis standing between the `aboveCarryThreshold` gate and a
fully unconditional `carryData` field.  See `carryDataFromStartThreshold` for the
fact that the manuscript's genuine start threshold discharges it.
-/
structure CarryDataSupportResidual where
  /-- For every `aboveCarryThreshold` failing `cQ`-shell, a support hit at or below
  `X` (equivalently `a 0 ≤ X`, i.e. `1 ≤ firstIndexAbove X`). -/
  supportBefore :
    ∀ (shell : FailingDyadicShell),
      shell.cQ = erdos260Constants.cQ → shell.aboveCarryThreshold →
        1 ≤ supportCount shell.d shell.X

/--
**The `carryData` provider field, modulo the single support residual.**

This has exactly the type of `GlobalAssemblyCoreInputs.carryData`; the only input
beyond the field's own `cQ`/`aboveCarryThreshold` hypotheses is the residual
`CarryDataSupportResidual`.
-/
def CarryDataSupportResidual.carryDataField (res : CarryDataSupportResidual) :
    ∀ (shell : FailingDyadicShell),
      shell.cQ = erdos260Constants.cQ → shell.aboveCarryThreshold →
        CarryDataFromFailure shell erdos260Constants.cPr :=
  fun shell hcQ hgate => carryDataFromGate shell hgate (res.supportBefore shell hcQ hgate)

/--
**Fully-closed carry data under the manuscript start threshold (NO residual).**

For a failing dyadic shell beyond the manuscript "sufficiently large dyadic `X`"
threshold `appendixNChainCompressionStartThreshold` — the very threshold the global
pipeline pins `startThreshold` to — the carry data is built with **no** extra
hypothesis: that threshold simultaneously supplies the carry scale and the support
hit (`supportCount_pos_of_appendixNChainCompressionStartThreshold_le`).

This pins down that the lone residual of `carryDataFromGate` is purely an artifact
of the *weaker* `aboveCarryThreshold` gate, not of the Lemma 21.1 mathematics:
once `X` is genuinely large (past the first hit), the carry data is unconditional.
-/
def carryDataFromStartThreshold
    (shell : FailingDyadicShell)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd shell.hnonterm
        ≤ shell.X) :
    CarryDataFromFailure shell erdos260Constants.cPr :=
  carryDataFromGate shell
    (by
      -- `aboveCarryThreshold = carryThreshold (carryB Q + 19) ≤ X`, dominated by the
      -- combined start threshold.
      show carryThreshold (carryB shell.Q + 19) ≤ shell.X
      exact le_trans carryThreshold_le_appendixNChainCompressionStartThreshold hXge)
    (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)

/-! ## Part 2 — `highExcessCharge`: the central charge bridge (P9) provider -/

/--
**The central charge bridge inequality is FALSE for any genuine carry data.**

`ClosurePhaseMass phases < highExcessMass (highExcessStarts …) …`.  The carry
pressure floor gives `cPr·X ≤ highExcessMass`; the summed six-phase manuscript
budget gives `ClosurePhaseMass ≤ cStar·ξ·X`; and `cStar·ξ < cPr`
(`erdos260Constants.constantsCompatible`).  Chaining for `X > 0` yields the strict
inequality — so the `HighExcessChargeData` field can never hold directly.
-/
theorem highExcess_strictly_exceeds_phaseMass
    {shell : FailingDyadicShell}
    (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr) :
    ClosurePhaseMass phases.toClosurePhaseData <
      highExcessMass
        (highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T := by
  have hX : 0 < (shell.X : ℝ) := shell.X_pos_real
  have hLower :
      erdos260Constants.cPr * (shell.X : ℝ) ≤
        highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T :=
    carryData_pressureFloor erdos260Constants.cPr_pos.le carryData
  have hPhase :
      ClosurePhaseMass phases.toClosurePhaseData ≤
        erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : ℝ) :=
    ClosurePhaseMass_le_budget phases.toClosurePhaseData hX.le
  have hcompat :
      erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : ℝ) <
        erdos260Constants.cPr * (shell.X : ℝ) :=
    mul_lt_mul_of_pos_right erdos260Constants.constantsCompatible hX
  linarith

/--
**The high-excess charge type is empty for any genuine carry data.**

Direct corollary of `highExcess_strictly_exceeds_phaseMass`: the only field of
`HighExcessChargeData phases carryData` is the (now strictly-violated) inequality
`highExcessMass ≤ ClosurePhaseMass`.  Hence the bridge can be inhabited ONLY via a
derivation of `False` — the manuscript's "no low-density shell exists".
-/
theorem highExcessChargeData_isEmpty
    {shell : FailingDyadicShell}
    (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr) :
    IsEmpty (HighExcessChargeData phases carryData) :=
  ⟨fun h =>
    absurd h.highExcess_le_phaseMass
      (not_le.mpr (highExcess_strictly_exceeds_phaseMass phases carryData))⟩

/--
**The precise remaining analytic content of the central charge bridge (P9).**

For a failing shell with its phase and carry data, this bundles exactly the two
genuinely-residual pieces of the v5 charge bridge:

* `routing` — the J.1.1 first-obstruction seven-class priority routing
  `RoutedHighExcessChargeDataOldRes` (the augmented bridge
  `highExcessMass ≤ ClosurePhaseMass + oldResMass`).  Its mass-conservation skeleton
  is PROVED; its five per-class mass bounds (Chernoff / clean-CNL / DensePack / the
  joint Tower+Return+Run N.24 TRT bound / the old-residual class) are the deep
  L.2 / N.3.3 / N.24 / L.6.4 family-dynamics estimates — the analytic heart.
* `oldRes_le` — the Lemma L.6.5 old-residual smallness `oldResMass ≤ 1·c_*·X`
  (conservative cluster constant `C_Q = 1`, failure density `c_* = manuscriptCstarSmall`).
-/
structure ShellHighExcessRoutingResidual
    {shell : FailingDyadicShell}
    (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr) where
  /-- The branch-level v5 old-residual mass `OldRes_{s,j}(Y)` (Lemma L.6.4). -/
  oldResMass : ℝ
  /-- The J.1.1 seven-class priority routing with its per-class mass bounds. -/
  routing : RoutedHighExcessChargeDataOldRes phases carryData oldResMass
  /-- Lemma L.6.5: `OldRes ≤ C_Q·c_*·X` at `C_Q = 1`, `c_* = manuscriptCstarSmall`. -/
  oldRes_le : oldResMass ≤ 1 * manuscriptCstarSmall * (shell.X : ℝ)

/--
**Central charge bridge from the routing residual (via the contradiction engine).**

Runs `RoutedHighExcessChargeDataOldRes.refutes_failingShell` with the
**already-proved** constant condition `manuscript_closure_pressure`
(`cStar·ξ + 1·c_* < cPr`) and the L.6.5 smallness to derive `False`, then `.elim`s
into the (provably empty, `highExcessChargeData_isEmpty`) bridge type.  This is the
faithful charge-bridge-layer encoding of "no low-density shell exists"; the only
non-discharged inputs are the residual's `routing`/`oldRes_le`.
-/
def ShellHighExcessRoutingResidual.toHighExcessChargeData
    {shell : FailingDyadicShell}
    {phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell erdos260Constants.cPr}
    (res : ShellHighExcessRoutingResidual phases carryData) :
    HighExcessChargeData phases carryData :=
  (res.routing.refutes_failingShell erdos260Constants.cPr_pos.le res.oldRes_le
    manuscript_closure_pressure).elim

/--
**The `highExcessCharge` provider field, modulo the routing residual.**

A provider of the per-shell routing residual for every failing shell with its phase
and carry data.  The `phases.trtNonneg` hypothesis of the field is available (and is
exactly what the manuscript routing — via `CarryPriorityRoutingCharge` — would need
to build the residual), but is not consumed by the contradiction.
-/
structure HighExcessRoutingResidualProvider where
  residual :
    ∀ (shell : FailingDyadicShell)
      (_hcQ : shell.cQ = erdos260Constants.cQ)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
      (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
      (_hphases : phases.trtNonneg),
        ShellHighExcessRoutingResidual phases carryData

/-- Produce the exact `GlobalAssemblyCoreInputs.highExcessCharge` field shape. -/
def HighExcessRoutingResidualProvider.highExcessChargeField
    (prov : HighExcessRoutingResidualProvider) :
    ∀ (shell : FailingDyadicShell)
      (_hcQ : shell.cQ = erdos260Constants.cQ)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
      (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
      (_hphases : phases.trtNonneg),
        HighExcessChargeData phases carryData :=
  fun shell hcQ phases carryData hphases =>
    (prov.residual shell hcQ phases carryData hphases).toHighExcessChargeData

/-! ## Part 3 — capstone: the two providers are drop-in for the two deepest slots

`CarryHighExcessReducedCoreInputs` packages MY two residual providers
(`CarryDataSupportResidual`, `HighExcessRoutingResidualProvider`) together with the
other six per-shell providers of `GlobalAssemblyCoreInputs` (the Chernoff / CNL /
DensePack / Tower / Return / Run factory data + the phase-mass nonnegativity — the
remaining workers' fields, copied verbatim, unchanged).  `toCoreInputs` assembles a
genuine `GlobalAssemblyCoreInputs`, so `erdos260_of_carryHighExcessReduced` derives
`Erdos260Statement` via the canonical `erdos260_final_core`.

This machine-checks that the **only** distance my two slots add to an unconditional
proof is exactly `carrySupport` (`1 ≤ supportCount d X`) and `highExcessRouting`
(the J.1.1 routing + L.6.5 smallness); nothing else from the carry/charge layers
remains.  Conditional, NOT unconditional — faithfully exposing the residuals. -/

structure CarryHighExcessReducedCoreInputs where
  /-- **My carry residual** — the single `1 ≤ supportCount d X` per `aboveCarryThreshold` shell. -/
  carrySupport : CarryDataSupportResidual
  chernoff :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  cnl :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  densePack :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  tower :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  returnPkg :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  run :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        RunFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  returnRunMassNonneg :
    ∀ (shell : FailingDyadicShell) (hcQ : shell.cQ = erdos260Constants.cQ),
      0 ≤ (returnPkg shell hcQ).massSum + (run shell hcQ).runMass
  /-- **My high-excess residual** — the J.1.1 routing + L.6.5 smallness per shell. -/
  highExcessRouting : HighExcessRoutingResidualProvider

/-- Assemble the eight-provider core from my two residual providers and the other six. -/
def CarryHighExcessReducedCoreInputs.toCoreInputs
    (d : CarryHighExcessReducedCoreInputs) :
    GlobalAssemblyCoreInputs where
  carryData := d.carrySupport.carryDataField
  chernoff := d.chernoff
  cnl := d.cnl
  densePack := d.densePack
  tower := d.tower
  returnPkg := d.returnPkg
  run := d.run
  returnRunMassNonneg := d.returnRunMassNonneg
  highExcessCharge := d.highExcessRouting.highExcessChargeField

/-- **Erdős #260 from the carry/charge-reduced core** (conditional on the two
isolated residuals + the other six providers). -/
theorem erdos260_of_carryHighExcessReduced
    (d : CarryHighExcessReducedCoreInputs) : Erdos260Statement :=
  erdos260_final_core d.toCoreInputs

/-! ## Part 4 — honest residual inventory (machine-checked nonempty) -/

/-- Per-provider honesty report: what is fully closed vs. the sharpest residual. -/
def carryHighExcessProviderStatus : List String :=
  [ "carryData (Lemma 21.1 pressure floor): UNCONDITIONAL modulo the SINGLE residual " ++
      "`1 ≤ supportCount d X` (carryDataFromGate). Proved from the aboveCarryThreshold " ++
      "gate: dyadic X=2^L, Q·4≤2^(carryB Q), carry scale carryB Q+25≤L " ++
      "(carryLarge_of_carryThreshold_le), shell richness L+1≤|supportShell| " ++
      "(richShell_of_failure_large = manuscript A.1 carry-gap), and the K.4 allocation " ++
      "hAlloc (hAlloc_manuscript_strict). The residual VANISHES under the manuscript " ++
      "start threshold (carryDataFromStartThreshold, no hypothesis).",
    "highExcessCharge (central charge bridge, P9): the bridge inequality is PROVED FALSE " ++
      "for any genuine carry data (highExcess_strictly_exceeds_phaseMass / " ++
      "highExcessChargeData_isEmpty), so it is inhabitable ONLY by deriving False. " ++
      "REDUCED to the residual ShellHighExcessRoutingResidual = the J.1.1 seven-class " ++
      "routing (RoutedHighExcessChargeDataOldRes: 5 per-class mass bounds — Chernoff, " ++
      "clean-CNL, DensePack, the joint N.24 Tower+Return+Run TRT bound, old-residual) " ++
      "PLUS the Lemma L.6.5 smallness oldResMass ≤ 1·c_*·X. The constant condition " ++
      "cStar·ξ + 1·c_* < cPr is PROVED (manuscript_closure_pressure), NOT a residual." ]

theorem carryHighExcessProviderStatus_nonempty : carryHighExcessProviderStatus ≠ [] := by
  simp [carryHighExcessProviderStatus]

end

end Erdos260
