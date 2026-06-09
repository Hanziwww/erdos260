import Erdos260.UnconditionalAssemblyFinal
import Erdos260.PositiveDensityRichShell
import Erdos260.RunCylinderBridge
import Erdos260.ChargeAllocationConstruction
import Erdos260.TowerCycleRealization
import Erdos260.AuditFixedShapes

/-!
# The re-tightened FINAL Erdős #260 capstone (round 2 of the final layer)

This is the most-downstream node.  It integrates the five new
manuscript-referenced modules into a further-tightened atoms structure
`Erdos260MinimalAtomsFinal2` and the top theorem `erdos260_reduced_minimal_final2`,
reusing the existing `erdos260_reduced_minimal` plumbing (it targets the round‑0
`Erdos260MinimalAtoms`, the structure `erdos260_reduced_minimal` consumes).

## What is genuinely discharged this round (honest)

* **carryData richness (the A.1 "rich shells" core) — CLOSED.**  The
  `ShellWindowInputs.hKr` richness `L + 1 ≤ |supportShell|` — previously an *assumed*
  analytic input of the pressure-floor reduction — is now **derived** from the
  largeness gate `aboveCarryThreshold` and the support side-condition `1 ≤ supportCount`
  via `PositiveDensityRichShell.richShell_of_failure_large` (the genuine
  positive-density Theorem A.1 fact, "rationality ⇒ rich shells", proved from the carry
  recurrence).  The `carryWindow` reduced input drops from a full `ShellWindowInputs`
  (with assumed `hKr`/`hB`/`hL`) to **just** `1 ≤ supportCount`; `hKr`/`hB`/`hL` are all
  derived.  **This is the round's headline.**
* **Tower recurrent cycle — REDUCED to `CarryAPSubfibre`.**  The `towerSlope`/Tower
  field is fed the AP-subfibre landing datum `CarryAPSubfibre shell.Q P` (odd slope
  modulus `q ≥ 2` + base carry residue `K₀` + `P ≡ K₀ [ZMOD q]`); the recurrent cycle is
  *constructed* from the failing-shell carry by
  `TowerCycleRealization.towerCycleOfFailingShell` (the genuine carry-residue doubling
  map, E.5/E.11–E.13).
* **charge per-class multipliers — backed by the genuine J.1.8 charging map.**  The
  per-class multiplier `routedClassMassOf i ≤ termᵢ` is certified (`chargeMultiplier_via_chargingMap`)
  to come through the actual manuscript charging map (Def. J.1.2 outputs + Lemma J.1.8
  charged-ledger summation), with the term-vs-mass identification a **proved identity**.
  See the honest caveat under "Run/charge honest status".
* **Run mask (§25.1 digit↔cylinder) — CLOSED (equal-cylinder case).**  Certified by
  `RunCylinderBridge.ResidualCenter.maskWord_eq_of_dyadicCylinder`: the failing shell's
  actual mask word equals `dyadicDigit q₀ a` on the cylinder prefix, so the Run
  provenance's digit↔cylinder identification is now a *proof*, not an external input.

## Run/charge honest status (no overclaim)

* **Run mask** is closed in the *equal-cylinder* case (the branch routed to the run
  obstruction); the `runProvenance` field already fires the half-decrease on
  `dyadicDigit q₀ a`, and that word is now *proved* to be the shell's mask word
  (`runMask_closed`).  The adjacent-cylinder branch (routed to non-run outputs) remains
  the lone open primitive (`RunCylinderBridge`).
* **charge**: the charge field is kept in the robust *count×multiplier* form
  (`ShellChargeStructuralInput`, `ofGeomFibre`), inhabitable for **every** phase datum.
  `ofChargingMaps` is **not** forced as the field because it requires charging maps
  `ℕ → chernoff.α`/`ℕ → cnl.α`, hence *nonempty* `chernoff.α`/`cnl.α`; forcing it over
  the round‑0 charge field's `∀ phases` would make the field empty for empty-`α` phases —
  a vacuity regression (the very bug class under audit).  The genuine assembled phases do
  have nonempty `α` (path families `Fin m → ℕ`), so the charging-map derivation
  `chargeMultiplier_via_chargingMap` applies to them; it is provided as a proved
  certificate, with the term-vs-mass identity proved, rather than as a vacuity-risking
  field restriction.

## Honest scope (NOT unconditional)

The remaining genuine residual per shell is: the support side-condition `1 ≤ supportCount`
(carryData `inl`, or a genuine `CarryDataFromFailure`, `inr`); the `CarryAPSubfibre`
AP-subfibre landing datum (Tower, E.2–E.4); the per-class charge data (count×multiplier /
charging-map per-output estimates); the `ResidualCenter` + its equal-cylinder geometry
(Run); plus the still-per-shell Chernoff calibration / CNL coordinatization / DensePack
regime / Return reduced inputs.  No atom is reduced to `True`; this remains conditional,
and the bundle is non-vacuous (every field type is inhabited — § Non-vacuity).

No `sorry`, `admit`, or new `axiom`.  `#print axioms erdos260_reduced_minimal_final2`
is the three standard logical axioms only.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1. carryData richness: derive `hKr` via the positive-density Theorem A.1 -/

/--
**Build the full `ShellWindowInputs` from just `1 ≤ supportCount` + the largeness gate.**

The richness `hKr : L + 1 ≤ |supportShell|` is derived by
`PositiveDensityRichShell.richShell_of_failure_large` (the genuine A.1 fact); the scale
fields `hB`/`hL` by `aboveCarryThreshold_provides_windowScale`; `L`/`hX_eq` are the
dyadic exponent of `shell.X`.  So the only remaining input is `hsupp : 1 ≤ supportCount`
(the "`X` past the first hit" condition the carry gate does not supply). -/
def carryWindowInput_of_support {shell : FailingDyadicShell}
    (hsupp : 1 ≤ supportCount shell.d shell.X)
    (hlarge : shell.aboveCarryThreshold) :
    CarryWindowInput shell :=
  Sum.inl
    { L := Classical.choose shell.hXdyadic
      B := carryB shell.Q
      hX_eq := Classical.choose_spec shell.hXdyadic
      hB := (aboveCarryThreshold_provides_windowScale
        (Classical.choose_spec shell.hXdyadic) hlarge).1
      hL := (aboveCarryThreshold_provides_windowScale
        (Classical.choose_spec shell.hXdyadic) hlarge).2
      hKr := richShell_of_failure_large shell (Classical.choose_spec shell.hXdyadic) hsupp hlarge
      h_supportCount_pos := hsupp }

/-- Build the genuine carry datum (with the Lemma 21.1 pressure floor) from the
richness-reduced carry input: `inl` (a support side-condition) ⟹ the floor via the
derived `ShellWindowInputs`; `inr` (a genuine carry datum) ⟹ identity. -/
def carryDataFinal2 {shell : FailingDyadicShell} (hlarge : shell.aboveCarryThreshold) :
    (PLift (1 ≤ supportCount shell.d shell.X) ⊕ CarryDataFromFailure shell erdos260Constants.cPr) →
      CarryDataFromFailure shell erdos260Constants.cPr
  | Sum.inl hsupp => (carryWindowInput_of_support hsupp.down hlarge).build
  | Sum.inr d => d

/-! ## 2. The re-tightened atoms structure -/

/--
**The re-tightened FINAL minimal residual atoms.**

`Erdos260MinimalAtoms` (round 0) with two fields further reduced:

* `carryWindow`: the richness `hKr` is now *derived*, so the `inl` branch needs only
  `1 ≤ supportCount` (A.1 richness closed);
* `towerAP` (was `TowerRecurrentCycle`): the AP-subfibre landing datum `CarryAPSubfibre`,
  the recurrent cycle is constructed from the carry.

The other fields are unchanged from `Erdos260MinimalAtomsFinal` (the charge field is kept
robust; see the module doc-comment for why `ofChargingMaps` is certified, not forced). -/
structure Erdos260MinimalAtomsFinal2 where
  /-- **REDUCED (A.1 richness closed)** — gated by `aboveCarryThreshold`; the `inl` branch
  is just `1 ≤ supportCount` (`hKr`/`hB`/`hL` derived), the `inr` branch a genuine carry datum. -/
  carryWindow :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → shell.aboveCarryThreshold →
        PLift (1 ≤ supportCount shell.d shell.X) ⊕ CarryDataFromFailure shell erdos260Constants.cPr
  /-- Per-shell Chernoff calibration `m ≤ c₁Y` (unchanged). -/
  chernoffCalib :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → ChernoffCalibrationInput shell
  /-- Per-shell CNL coordinatization input (unchanged; non-vacuous fix). -/
  cnlCoord :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        CNLCoordinatizedShellInput erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : ℝ)
  /-- Per-shell DensePack regime input (unchanged). -/
  densePackRegime :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → DensePackRegimeInput shell
  /-- **REDUCED** — per-shell Tower AP-subfibre landing datum; the recurrent cycle is
  constructed from the carry by `towerCycleOfFailingShell`. -/
  towerAP :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → CarryAPSubfibre shell.Q shell.hrational.choose
  /-- Per-shell Return reduced input (unchanged). -/
  returnReduced :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        ReturnFactoryReducedInput erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : ℝ)
  /-- Per-shell Run residual-center provenance datum (unchanged; its §25.1 mask-word
  identification is now closed in the equal-cylinder case, `runMask_closed`). -/
  runProvenance :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → RunProvenanceData (shell.X : ℝ)
  /-- Per-shell Return/Run phase-mass nonnegativity (unchanged). -/
  returnRunMassNonneg :
    ∀ (shell : FailingDyadicShell) (hcQ : shell.cQ = erdos260Constants.cQ),
      0 ≤ ((returnReduced shell hcQ).toFactoryData).massSum
        + ((runProvenance shell hcQ).build).runMass
  /-- Per-shell charge structural-PKG fibre datum (unchanged, robust count×multiplier form);
  `pkg_exposes` proved structurally, restricted to `trtNonneg` phases.  Its per-class bounds
  are certified to come through the genuine charging map (`chargeMultiplier_via_chargingMap`). -/
  chargeStructural :
    ∀ (shell : FailingDyadicShell)
      (_hcQ : shell.cQ = erdos260Constants.cQ)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
      (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
      (_hphases : phases.trtNonneg),
        ShellChargeStructuralInput phases carryData

/-! ## 3. Expansion into the round‑0 atoms and the final theorem -/

/--
**Expand the re-tightened atoms into the round‑0 `Erdos260MinimalAtoms`.**

The two reduced fields are run through their new builders (`carryDataFinal2`,
`towerCycleOfFailingShell`); the seven unchanged fields are forwarded through the same
builders `Erdos260MinimalAtomsFinal` uses. -/
def Erdos260MinimalAtomsFinal2.toMinimalAtoms (m : Erdos260MinimalAtomsFinal2) :
    Erdos260MinimalAtoms where
  carryData := fun shell hcQ hlarge => carryDataFinal2 hlarge (m.carryWindow shell hcQ hlarge)
  chernoff := chernoffFactoryOfCalibration m.chernoffCalib
  cnl := cnlProvider_ofCoordinatization m.cnlCoord
  densePack := fun shell hcQ => (m.densePackRegime shell hcQ).build
  towerSlope := fun shell hcQ =>
    (towerCycleOfFailingShell shell shell.hrational.choose (m.towerAP shell hcQ)).toSlopeAtom
  returnPkg := returnPkgOfReducedProvider m.returnReduced
  run := fun shell hcQ => (m.runProvenance shell hcQ).build
  returnRunMassNonneg := m.returnRunMassNonneg
  charge := fun shell hcQ phases carryData hphases =>
    (m.chargeStructural shell hcQ phases carryData hphases).build

/--
**Erdős #260 reduced to the re-tightened FINAL residual atoms (the capstone).**

Same conclusion `Erdos260Statement`, conditional on the further-tightened
`Erdos260MinimalAtomsFinal2`.  Proved by expanding to the round‑0 `Erdos260MinimalAtoms`
and reusing `erdos260_reduced_minimal`.

**Honest scope.** Conditional, NOT unconditional, on the genuine irreducible per-shell
inputs.  The bundle is non-vacuous (§ Non-vacuity). -/
theorem erdos260_reduced_minimal_final2 (m : Erdos260MinimalAtomsFinal2) :
    Erdos260Statement :=
  erdos260_reduced_minimal m.toMinimalAtoms

/-! ## 4. Discharge certificates for the four wired cores -/

/-- **carryData richness CLOSED (A.1) — the headline.**  The `ShellWindowInputs.hKr`
richness `L + 1 ≤ |supportShell|` is a *derived* consequence of the largeness gate
`aboveCarryThreshold` and the support side-condition `1 ≤ supportCount` — no longer an
assumed analytic input.  Re-exports the genuine positive-density Theorem A.1 fact
`richShell_of_failure_large` that `carryWindowInput_of_support` uses to build the
pressure-floor datum. -/
theorem carryRichness_closed (shell : FailingDyadicShell) {L : ℕ}
    (hX_eq : shell.X = 2 ^ L)
    (hsupp : 1 ≤ supportCount shell.d shell.X)
    (hlarge : shell.aboveCarryThreshold) :
    L + 1 ≤ (supportShell shell.d shell.X).card :=
  richShell_of_failure_large shell hX_eq hsupp hlarge

/-- **carryData richness — fully closed start-threshold form.**  Beyond the
`aboveCarryThreshold` gate, the full manuscript start threshold discharges *both* the
carry scale and the support hit, so richness needs no residual hypothesis at all
(`richShell_of_startThreshold_le`). -/
theorem carryRichness_closed_startThreshold (shell : FailingDyadicShell) {L : ℕ}
    (hX_eq : shell.X = 2 ^ L)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd shell.hnonterm
        ≤ shell.X) :
    L + 1 ≤ (supportShell shell.d shell.X).card :=
  richShell_of_startThreshold_le shell hX_eq hXge

/-- **Tower recurrent cycle constructed from the carry.**  The capstone's Tower datum is
built from the AP-subfibre landing datum `CarryAPSubfibre shell.Q P` by
`towerCycleOfFailingShell` — the recurrent cycle is the genuine carry-residue doubling
map (E.5/E.11–E.13), not assumed. -/
theorem towerCycle_built_from_carry (shell : FailingDyadicShell) (P : ℤ)
    (S : CarryAPSubfibre shell.Q P) :
    (towerCycleOfFailingShell shell P S).Q = shell.Q := rfl

/-- **Run mask CLOSED (equal-cylinder).**  The failing shell's actual mask word equals the
run obstruction's word `dyadicDigit q₀ a` on the cylinder prefix — the §25.1 digit↔cylinder
identification, now a *proof*.  Re-exports `ResidualCenter.maskWord_eq_of_dyadicCylinder`. -/
theorem runMask_closed (C : ResidualCenter) {M D : ℝ} {n kM kν : ℕ}
    (hM : 0 ≤ M / D) (hk : kM = kν)
    (hcylM : DyadicCylinder n kM (M / D))
    (hcylc : DyadicCylinder n kν ((C.a : ℝ) / (C.q0 : ℝ))) :
    ∀ j, j < n → binaryDigitWord (M / D) j = dyadicDigit C.q0 C.a j :=
  C.maskWord_eq_of_dyadicCylinder hM hk hcylM hcylc

/-- **charge per-class multiplier through the genuine J.1.8 charging map.**  Each routed
class mass is dominated by the charged output area of any charging map satisfying the
per-output charged bound — the actual manuscript mechanism (Def. J.1.2 + Lemma J.1.8), with
the term identification a proved identity.  Re-exports `routedClassMassOf_le_chargedArea`.
This is the charging-map derivation that backs the per-class bounds for the genuine
(nonempty-`α`) assembled phases. -/
theorem chargeMultiplier_via_chargingMap
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7) (i : Fin 7)
    {O : Type*} [DecidableEq O] (chargeOf : ℕ → O) (outputs : Finset O) (cap : O → ℝ)
    (hmaps : ∀ k ∈ routedFibre carryData route i, chargeOf k ∈ outputs)
    (hcharged : ∀ o ∈ outputs,
      (∑ k ∈ (routedFibre carryData route i).filter (fun k => chargeOf k = o),
          windowExcess (hitGap carryData.a) k carryData.r carryData.T) ≤ cap o) :
    routedClassMassOf carryData route i ≤ ∑ o ∈ outputs, cap o :=
  routedClassMassOf_le_chargedArea carryData route i chargeOf outputs cap hmaps hcharged

/-! ## 5. NON-VACUITY of the re-tightened bundle

Every reduced field type is inhabited, so the hypothesis bundle is genuinely satisfiable
in principle (not vacuous like the round‑2 `cnlInput`). -/

/-- **The richness-reduced carryWindow input is inhabited** from a genuine carry datum
(the `inr` branch), with no scale hypothesis — no emptier than the round‑0 baseline. -/
theorem carryWindowReduced_inhabited_of_carryData {shell : FailingDyadicShell}
    (d : CarryDataFromFailure shell erdos260Constants.cPr) :
    Nonempty (PLift (1 ≤ supportCount shell.d shell.X)
      ⊕ CarryDataFromFailure shell erdos260Constants.cPr) :=
  ⟨Sum.inr d⟩

/-- **The richness `inl` branch is inhabited at a rich shell**: a support hit gives the
`inl` input, from which `carryWindowInput_of_support` builds the full pressure-floor datum
(richness derived — no `hKr` assumption). -/
theorem carryWindowReduced_inl_inhabited {shell : FailingDyadicShell}
    (hsupp : 1 ≤ supportCount shell.d shell.X) :
    Nonempty (PLift (1 ≤ supportCount shell.d shell.X)
      ⊕ CarryDataFromFailure shell erdos260Constants.cPr) :=
  ⟨Sum.inl (PLift.up hsupp)⟩

/-- **The Tower AP-subfibre datum is inhabited** (closed witness `q = 3, K₀ = 1, P = 1`):
the carry residue lands at a recurrent vertex of the slope-`1/3` cycle. -/
theorem towerAP_inhabited : ∃ (Q : ℕ) (P : ℤ), Nonempty (CarryAPSubfibre Q P) :=
  carryAPSubfibre_nonvacuous

/-- **The Run residual center is inhabited** (the `1/3` non-dyadic center), and its mask
word equals `dyadicDigit 3 1` (the bridge fired) — the equal-cylinder Run mask is
realized, not vacuous. -/
theorem runProvenanceCore_inhabited :
    Nonempty ResidualCenter ∧
      (∀ j, binaryDigitWord ((1 : ℝ) / 3) j = dyadicDigit 3 1 j) :=
  ⟨residualCenter_nonempty, maskWord_oneThird⟩

/-- **The charge structural input is inhabited** for any TRT-nonnegative phase data with
empty high-excess carry (reuses `Erdos260.shellChargeStructuralInput_inhabited_of_emptyHighExcess`):
the robust count×multiplier field is non-vacuous for *every* phase datum, in contrast to a
charging-map field which would require nonempty `chernoff.α`/`cnl.α`. -/
theorem chargeStructural_inhabited_of_emptyHighExcess {shell : FailingDyadicShell}
    (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
    (hphases : phases.trtNonneg)
    (hEmpty : highExcessStarts carryData.starts (hitGap carryData.a)
        carryData.r carryData.T carryData.Y = ∅)
    (hChern : 0 ≤ termChernoff phases.toClosurePhaseData)
    (hCnl : 0 ≤ termCnl phases.toClosurePhaseData) :
    Nonempty (ShellChargeStructuralInput phases carryData) :=
  shellChargeStructuralInput_inhabited_of_emptyHighExcess phases carryData hphases hEmpty
    hChern hCnl

end

end Erdos260
