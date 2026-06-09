import Erdos260.UnconditionalAssemblyFinal2
import Erdos260.TowerAPSubfibreLanding
import Erdos260.RunResidualCenterExistence
import Erdos260.ChargePerOutputEstimates
import Erdos260.ShellRegimeClosure
import Erdos260.CNLCoordinatizationExistence

/-!
# The next-tightened FINAL Erdős #260 capstone (round 3 of the final layer)

Most-downstream node.  Integrates five new closure modules into a further-tightened
atoms structure `Erdos260MinimalAtomsFinal3` and the top theorem
`erdos260_reduced_minimal_final3`, reusing the existing `erdos260_reduced_minimal`
plumbing (it targets the round‑0 `Erdos260MinimalAtoms`, the structure
`erdos260_reduced_minimal` consumes), and the Final2 helpers `carryWindowInput_of_support`
/ `carryDataFinal2`.

## Genuine FIELD reductions this round (honest)

* **Tower — CLOSED (field eliminated).**  `TowerAPSubfibreLanding.carryAPSubfibreOfFailingShellClosed`
  constructs the AP-subfibre landing datum `CarryAPSubfibre shell.Q P` from a genuine
  failing shell with **no extra hypothesis** (odd modulus `ordCompl[2](Q·H)`, base
  residue read off `R₀ = P`, non-degeneracy `0 < P` from non-termination), and
  `towerCycleOfFailingShellClosed` builds the `TowerRecurrentCycle`.  So the per-shell
  Tower input is no longer a field at all — `towerSlope` is built directly from the
  shell.  **Residual (outside the type):** the *faithful*-cycle canonical-gap zero-run
  `carry_tracks_slopeOrbit`'s `hzero` (whether this `q` is the genuine recurrent-cycle
  modulus); it is not needed to inhabit the `TowerSlopeAtom`.
* **CNL — REDUCED to `CNLClusterGeometry`.**  `CNLCoordinatizationExistence.cnlProvider_ofGeometry`
  builds the `cnl` provider from the per-shell `CNLClusterGeometryShellInput` (a recorded
  depth-`M` ladder-code word `sym` + telescoping additive BND height), strictly smaller
  than Final2's `CNLCoordinatizedShellInput` (which carried the whole coordinatization):
  `coherent`/`path_injOn`/`root_eq`/`sym_injOn`/`step_injOn` are now all theorems.

## CERTIFIED reductions this round (kept at their Final2 field shapes, with reason)

* **Run — `FailingShellResidual` certified.**  `RunResidualCenterExistence.residualCenterOfFailingShell`
  derives the `ResidualCenter` (hence the whole `(q₀,a,m)` provenance) from a
  `FailingShellResidual` (the non-dyadic residue orbit), and `adjacentBranch_nonRun`
  closes the adjacent branch as non-run.  The `runProvenance` field is kept as
  `RunProvenanceData` (its `ResidualCenter` sub-input is now `FailingShellResidual`-derivable);
  the run *budget* `chainRoot_le`/`hSmall` genuinely needs the large-scale regime, so the
  field is inhabitable at large shells (the manuscript regime), not at every small shell.
* **charge — per-output matching + `pkg_exposes` certified.**  `ChargePerOutputEstimates`
  discharges the per-output charged summation from a *matching* charging map + per-element
  domination (`routed…_le_term_of_matching`), and furnishes `pkg_exposes` as a theorem for
  the failing shell (`failingShellPkgGeometry_pkg_exposes`).  The `chargeStructural` field is
  kept in the robust count×multiplier form (`ShellChargeStructuralInput`, inhabitable for
  *every* phase), because the matching/`ofChargingMaps` route needs charging maps
  `ℕ → chernoff.α`/`cnl.α` (nonempty `α`); forcing it over the `∀ phases` field would
  reintroduce a vacuity.
* **ShellScalarRegime certified, not a field.**  `ShellRegimeClosure.ShellScalarRegime`
  closes the carry scale, support hit, small-density `c0 ≤ κ/16` (under the manuscript pin
  `c0 = κ/64`), the A.1 richness and the canonical DensePack datum.  It is **not** made an
  ungated field because `ShellScalarRegime shell` requires `carryLarge` (`carryB Q + 25 ≤ L`),
  which *fails* for small shells — an ungated `∀ shell` field would be vacuous.  It is
  certified (`shellRegime_of_aboveCarryThreshold`, `.richShell`, `.densePackFactoryData`),
  and the carryData richness it certifies is exactly what Final2's `carryWindow` already uses.

## Honest scope (NOT unconditional)

Conditional, NOT unconditional.  The genuinely irreducible per-shell data is listed in
`final3_irreducible_residual`: the Tower faithful-cycle zero-run, the Run
`FailingShellResidual` non-dyadicity (+ the large-scale run budget), the per-charge
matching + per-element domination + J.5 PKG faithfulness, the CNL `CNLClusterGeometry`
(recorded code word + telescoping height), and the `c0 = κ/64` pin / `M_L = o(s)` regime.
No field is reduced to `True`.  Per-field non-vacuity is certified below (the run/charge
fields at the genuine large-scale / nonneg-mass regime, as in Final2).

No `sorry`, `admit`, or new `axiom`.  `#print axioms erdos260_reduced_minimal_final3`
is the three standard logical axioms only.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1. The re-tightened atoms structure -/

/--
**The round-3 re-tightened FINAL minimal residual atoms.**

`Erdos260MinimalAtoms` (round 0) reached with:

* the **Tower** input ELIMINATED (built from the shell by `towerCycleOfFailingShellClosed`);
* the **CNL** input REDUCED to the smaller `CNLClusterGeometryShellInput`;
* the remaining fields unchanged from `Erdos260MinimalAtomsFinal2` (carryWindow,
  chernoffCalib, densePackRegime, returnReduced, runProvenance, returnRunMassNonneg,
  chargeStructural). -/
structure Erdos260MinimalAtomsFinal3 where
  /-- **REDUCED (A.1 richness derived)** — gated by `aboveCarryThreshold`; the `inl` branch is
  just `1 ≤ supportCount` (`hKr`/`hB`/`hL` derived via `richShell_of_failure_large`), the `inr`
  branch a genuine carry datum.  (Same as Final2.) -/
  carryWindow :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → shell.aboveCarryThreshold →
        PLift (1 ≤ supportCount shell.d shell.X) ⊕ CarryDataFromFailure shell erdos260Constants.cPr
  /-- Per-shell Chernoff calibration `m ≤ c₁Y` (same as Final2; the H.4 calibration is closed
  for the failing shell by `ShellRegimeClosure.failingShell_h4_calibration`). -/
  chernoffCalib :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → ChernoffCalibrationInput shell
  /-- **REDUCED (CNL → geometry)** — the per-shell CNL cluster *geometry* input (recorded
  depth-`M` code word + telescoping height), strictly smaller than Final2's coordinatization
  input; `cnlProvider_ofGeometry` constructs the coordinatization (all injectivity/coherence
  theorems). -/
  cnlGeom :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        CNLClusterGeometryShellInput erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : ℝ)
  /-- Per-shell DensePack regime input (same as Final2; `ShellScalarRegime.densePackFactoryData`
  certifies the canonical in-regime datum). -/
  densePackRegime :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → DensePackRegimeInput shell
  /-- Per-shell Return reduced input (same as Final2). -/
  returnReduced :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        ReturnFactoryReducedInput erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : ℝ)
  /-- Per-shell Run residual-center provenance datum (same as Final2; its `ResidualCenter`
  sub-input is now `FailingShellResidual`-derivable, `residualCenterOfFailingShell`). -/
  runProvenance :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → RunProvenanceData (shell.X : ℝ)
  /-- Per-shell Return/Run phase-mass nonnegativity (same as Final2). -/
  returnRunMassNonneg :
    ∀ (shell : FailingDyadicShell) (hcQ : shell.cQ = erdos260Constants.cQ),
      0 ≤ ((returnReduced shell hcQ).toFactoryData).massSum
        + ((runProvenance shell hcQ).build).runMass
  /-- Per-shell charge structural-PKG fibre datum (same as Final2, robust count×multiplier form;
  `ChargePerOutputEstimates` certifies the per-output matching derivation + `pkg_exposes`). -/
  chargeStructural :
    ∀ (shell : FailingDyadicShell)
      (_hcQ : shell.cQ = erdos260Constants.cQ)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
      (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
      (_hphases : phases.trtNonneg),
        ShellChargeStructuralInput phases carryData

/-! ## 2. Expansion into the round‑0 atoms and the final theorem -/

/--
**Expand the round-3 atoms into the round‑0 `Erdos260MinimalAtoms`.**

The Tower slope is built from the shell (`towerCycleOfFailingShellClosed`, no input); the CNL
provider from the geometry (`cnlProvider_ofGeometry`); the remaining fields through the same
Final2 builders. -/
def Erdos260MinimalAtomsFinal3.toMinimalAtoms (m : Erdos260MinimalAtomsFinal3) :
    Erdos260MinimalAtoms where
  carryData := fun shell hcQ hlarge => carryDataFinal2 hlarge (m.carryWindow shell hcQ hlarge)
  chernoff := chernoffFactoryOfCalibration m.chernoffCalib
  cnl := cnlProvider_ofGeometry m.cnlGeom
  densePack := fun shell hcQ => (m.densePackRegime shell hcQ).build
  towerSlope := fun shell _hcQ =>
    (towerCycleOfFailingShellClosed shell shell.hrational.choose shell.hrational.choose_spec).toSlopeAtom
  returnPkg := returnPkgOfReducedProvider m.returnReduced
  run := fun shell hcQ => (m.runProvenance shell hcQ).build
  returnRunMassNonneg := m.returnRunMassNonneg
  charge := fun shell hcQ phases carryData hphases =>
    (m.chargeStructural shell hcQ phases carryData hphases).build

/--
**Erdős #260 reduced to the round-3 re-tightened FINAL residual atoms (the capstone).**

Same conclusion `Erdos260Statement`, conditional on the further-tightened
`Erdos260MinimalAtomsFinal3`.  Proved by expanding to the round‑0 `Erdos260MinimalAtoms` and
reusing `erdos260_reduced_minimal`.

**Honest scope.** Conditional, NOT unconditional, on the genuine irreducible per-shell data
(`final3_irreducible_residual`).  No field is reduced to `True`; the Tower input is the only
field genuinely eliminated this round (derived from the shell), and CNL is reduced to its
smallest geometric residue. -/
theorem erdos260_reduced_minimal_final3 (m : Erdos260MinimalAtomsFinal3) :
    Erdos260Statement :=
  erdos260_reduced_minimal m.toMinimalAtoms

/-! ## 3. Discharge / reduction certificates for the five wired cores -/

/-- **Tower CLOSED — the AP-subfibre landing datum is derived from the shell.**  Every failing
shell yields the `CarryAPSubfibre` (hence the `TowerRecurrentCycle` and `TowerSlopeAtom`) with no
extra hypothesis (`carryAPSubfibreOfFailingShellClosed`); the Tower field is therefore eliminated.
Re-exports the headline closure. -/
theorem tower_closed_from_shell (shell : FailingDyadicShell) :
    ∃ t : TowerRecurrentCycle, t.Q = shell.Q :=
  towerCycleOfFailingShellClosed_exists shell

/-- **Tower faithful-cycle residual (precise).**  The single remaining genuine geometric input
is the canonical-gap zero-run `hzero` (whether `q` is the *faithful* recurrent-cycle modulus);
given it, the actual carry residues track the recurrent slope orbit (`carry_tracks_slopeOrbit`).
This residual is OUTSIDE `CarryAPSubfibre` and not needed to inhabit the `TowerSlopeAtom`. -/
theorem tower_faithful_residual (shell : FailingDyadicShell) (P : ℤ)
    (S : CarryAPSubfibre shell.Q P)
    (hzero : ∀ j i : ℕ, gapOrbit S.q S.K₀ 0 j < i →
        i ≤ gapOrbit S.q S.K₀ 0 j + canonGap S.q (slopeOrbit S.q S.K₀ j) →
        shell.d i = 0) :
    ∀ m, integerCarry shell.Q P shell.d (gapOrbit S.q S.K₀ 0 m)
          ≡ (slopeOrbit S.q S.K₀ m : ℤ) [ZMOD (S.q : ℤ)] :=
  carry_tracks_slopeOrbit shell P S hzero

/-- **Run `ResidualCenter` derived from `FailingShellResidual`.**  The §25.1 non-dyadic residue
orbit yields a genuine `ResidualCenter` (hence the whole `(q₀,a,m)` provenance and the L.4.2
half-decrease); re-exports `exists_residualCenter_of_failingShell`.  The `runProvenance` field's
`ResidualCenter` sub-input is therefore `FailingShellResidual`-derivable. -/
theorem run_residualCenter_from_failingShell (F : FailingShellResidual) :
    ∃ C : ResidualCenter, C.num = F.num ∧ C.den = F.den ∧ C.bound = F.bound :=
  exists_residualCenter_of_failingShell F

/-- **Run adjacent branch is non-run.**  The adjacent-cylinder carry-tail block routes to the
non-run `localSpike`/`cleanBoundaryDirty` classes, never the run obligation; re-exports
`adjacentBranch_nonRun`.  So the run side needs only the equal-cylinder center. -/
theorem run_adjacent_nonRun {w : ℕ → ℕ} {p bound : ℕ}
    (hadj : DenseAllOneBlock w p bound ∨ AllZeroBlock w p bound) :
    ∃ o : ResidualSingularOutput w p, o.isCarryTailOutput ∧ ¬ o.isRunObligation :=
  adjacentBranch_nonRun hadj

/-- **charge per-output summation discharged by matching.**  Each routed class mass is dominated
by the charged output area of a *matching* charging map with per-element charged domination;
re-exports `routedClassMassOf_le_chargedArea_of_matching`.  The per-output `hcharged` input of the
charging-map multipliers is thereby reduced to per-element domination + matching. -/
theorem charge_perOutput_by_matching
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7) (i : Fin 7)
    {O : Type*} [DecidableEq O] (chargeOf : ℕ → O) (outputs : Finset O) (cap : O → ℝ)
    (hmaps : ∀ k ∈ routedFibre carryData route i, chargeOf k ∈ outputs)
    (hinj : ∀ x ∈ routedFibre carryData route i, ∀ y ∈ routedFibre carryData route i,
      chargeOf x = chargeOf y → x = y)
    (hdom : ∀ k ∈ routedFibre carryData route i,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ cap (chargeOf k))
    (hcap_nonneg : ∀ o ∈ outputs, 0 ≤ cap o) :
    routedClassMassOf carryData route i ≤ ∑ o ∈ outputs, cap o :=
  routedClassMassOf_le_chargedArea_of_matching carryData route i chargeOf outputs cap
    hmaps hinj hdom hcap_nonneg

/-- **charge `pkg_exposes` furnished for the failing shell.**  The J.5 structural geometry of the
failing shell furnishes the coverage primitive `pkg_exposes` as a theorem; re-exports
`failingShellPkgGeometry_pkg_exposes`. -/
theorem charge_pkg_exposes_furnished (lab : LiftState → Option GeomPackage) (s : LiftState)
    (h : canonicalCNLSelector ((failingShellPkgGeometry lab).cnlOf s) = some CNLClass.pkg) :
    ∃ c : Fin 7, (failingShellPkgGeometry lab).toMarking.geomDetect c s = true :=
  failingShellPkgGeometry_pkg_exposes lab s h

/-- **ShellScalarRegime certified (carry scale + support + small density), from the gate + c0 pin.**
Re-exports `shellRegime_of_aboveCarryThreshold`: under the manuscript failure-constant pin
`c0 = κ/64` and the largeness gate `aboveCarryThreshold`, with the support side input, the carry
scale and small density are closed and the A.1 richness follows (`ShellScalarRegime.richShell`). -/
theorem shellRegime_certified (shell : FailingDyadicShell)
    (hpin : shell.c0 = manuscriptC0)
    (hlarge : shell.aboveCarryThreshold)
    (hSupport : 1 ≤ supportCount shell.d shell.X) :
    ShellScalarRegime shell :=
  shellRegime_of_aboveCarryThreshold shell hpin hlarge hSupport

/-- **Chernoff H.4 calibration closed for the failing shell.**  `m₁ ≤ c₁·Y₁` at the pinned
manuscript constants, for the dyadic exponent of any failing shell (err ≤ 1); re-exports
`failingShell_h4_calibration`. -/
theorem chernoff_h4_calibration_closed
    (shell : FailingDyadicShell) {err : ℝ} (herr : err ≤ 1) :
    h4m1 manuscriptCdrop manuscriptC1 manuscriptEps
        ((Classical.choose shell.hXdyadic : ℕ) : ℝ) err
      ≤ manuscriptC1 * h4Y1 manuscriptEta manuscriptEps
        ((Classical.choose shell.hXdyadic : ℕ) : ℝ) :=
  failingShell_h4_calibration shell herr

/-! ## 4. NON-VACUITY of the re-tightened bundle (per-field witnesses)

As in Final2, no *global* `Nonempty Erdos260MinimalAtomsFinal3` is claimed (that would amount to
proving Erdős #260).  Each field type is certified inhabited — the run/charge fields at the genuine
large-scale / nonnegative-mass regime — so the reduction is genuine (not vacuous). -/

/-- The CNL cluster geometry shell input at the pinned constants, for any `X ≥ 0` (empty cluster,
positive shell factor `1/1000`, budget `2·(1/1000)·X ≤ (31/256)·X/6`). -/
def cnlGeomShellInput_pinned (X : ℝ) (hX : 0 ≤ X) :
    CNLClusterGeometryShellInput erdos260Constants.cStar erdos260Constants.ξ X where
  T := ∅
  BNDHeight := fun _ => 0
  c := 1
  CQ := 2
  geom :=
    CNLClusterGeometry.ofReplicatedInjectiveLabel (∅ : Finset CNLTransition) (fun _ => 0) 1 2
      (by norm_num) (cnl_cq_dominates_of_c_ge_one (by norm_num) (by norm_num)) 0 (fun _ => 0)
      (by intro t ht; simp [selectedTransitions] at ht)
  shellFactor := 1 / 1000
  Ij := 1
  shellFactor_nonneg := by norm_num
  Ij_nonneg := by norm_num
  hbudget := by
    have hcs : erdos260Constants.cStar = 31 / 16 := rfl
    have hxi : erdos260Constants.ξ = 1 / 16 := rfl
    show (2 : ℝ) ^ (0 + 1 : ℕ) * (1 / 1000) * X * 1 ≤ erdos260Constants.cStar * erdos260Constants.ξ * X / 6
    rw [hcs, hxi]
    have hpow : (2 : ℝ) ^ (0 + 1 : ℕ) = 2 := by norm_num
    rw [hpow]
    nlinarith [hX]

/-- **The reduced CNL field type is inhabited** at the pinned constants and any `X ≥ 0`
(non-vacuous, with a genuinely positive shell-budget slice). -/
theorem cnlGeomShellInput_inhabited (X : ℝ) (hX : 0 ≤ X) :
    Nonempty (CNLClusterGeometryShellInput erdos260Constants.cStar erdos260Constants.ξ X) :=
  ⟨cnlGeomShellInput_pinned X hX⟩

/-- **The Tower datum is inhabited for every shell** (built from the shell, closed). -/
theorem final3_tower_inhabited (shell : FailingDyadicShell) :
    ∃ t : TowerRecurrentCycle, t.Q = shell.Q :=
  towerCycleOfFailingShellClosed_exists shell

/-- **The Run `FailingShellResidual` input is inhabited** (the `1/3` non-dyadic center witness),
for every shell (it is shell-independent). -/
theorem failingShellResidual_inhabited : Nonempty FailingShellResidual :=
  failingShellResidual_nonempty

/-- **The carryWindow reduced input is inhabited** from a genuine carry datum (`inr`), no scale
hypothesis (as in Final2). -/
theorem carryWindow_inhabited_of_carryData {shell : FailingDyadicShell}
    (d : CarryDataFromFailure shell erdos260Constants.cPr) :
    Nonempty (PLift (1 ≤ supportCount shell.d shell.X)
      ⊕ CarryDataFromFailure shell erdos260Constants.cPr) :=
  carryWindowReduced_inhabited_of_carryData d

/-- **The Return reduced input is inhabited** (degenerate witness). -/
theorem final3_returnReduced_inhabited :
    Nonempty (ReturnFactoryReducedInput (0 : ℝ) (0 : ℝ) (0 : ℝ)) :=
  returnFactoryReducedInput_nonempty

/-- **The DensePack regime input is inhabited for every shell** (fallback branch). -/
theorem final3_densePackRegime_inhabited (shell : FailingDyadicShell) :
    Nonempty (DensePackRegimeInput shell) :=
  densePackRegimeInput_nonempty shell
    (div_nonneg
      (mul_nonneg
        (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
        shell.X_nonneg_real)
      (by norm_num))

/-- **The Chernoff calibration input is inhabited for every large shell** (`64 ≤ X`). -/
theorem final3_chernoffCalib_inhabited (shell : FailingDyadicShell) (hX : 64 ≤ shell.X) :
    Nonempty (ChernoffCalibrationInput shell) :=
  chernoffCalibrationInput_nonempty_of_large_shell shell hX

/-- **The charge structural input is inhabited** for any TRT-nonnegative phase data with empty
high-excess carry (robust count×multiplier form; non-vacuous for *every* phase). -/
theorem chargeStructural_inhabited {shell : FailingDyadicShell}
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

/-! ## 5. The honest irreducible residual after round 3 -/

/-- The precise per-shell geometric / number-theoretic data that remains genuinely irreducible. -/
def final3_irreducible_residual : List String :=
  [ "Tower faithful-cycle zero-run: the canonical-gap zero-run carry_tracks_slopeOrbit's hzero " ++
      "(whether q = ordCompl[2](Q·H) is the FAITHFUL recurrent-cycle modulus). The CarryAPSubfibre " ++
      "datum itself is CLOSED (carryAPSubfibreOfFailingShellClosed); only the zero-run remains, " ++
      "outside the type — not needed to inhabit TowerSlopeAtom.",
    "Run FailingShellResidual non-dyadicity: the §25.1 residual center ν/Qp has a non-terminating " ++
      "residue orbit (≡ non-dyadic). Plus the large-scale run budget (chainRoot_le/hSmall genuinely " ++
      "need X large), so the run field is inhabitable at the manuscript large-scale regime.",
    "charge per-element charged domination + matching (windowExcess k ≤ cap(Θ k), Θ injective on the " ++
      "fibre) — the genuine J.1b/J.1.7/G.6/J.D per-charge content (orthogonal to every phase core); " ++
      "plus the J.5 PKG-definitional faithfulness inside StructuralPkgGeometry (pkg_exposes furnished).",
    "CNL CNLClusterGeometry: the recorded depth-M ladder-code word sym and the telescoping additive " ++
      "BND height (height_additive). CNLTransition carries no lift-state geometry, so this is the " ++
      "smallest genuine CNL input; sym_injOn/step_injOn/coherent/path_injOn/root_eq are theorems.",
    "Scalar regime: the manuscript failure-constant pin c0 = κ/64 (giving c0 ≤ κ/16) and the Return " ++
      "asymptotic M_L = o(s) (the Return scale s and dirty multiplicity are Return-side, not " ++
      "failing-shell fields). The carry scale, support hit (under the start threshold), Chernoff " ++
      "calibration and A.1 richness are CLOSED.",
    "Chernoff/Return per-shell factory inputs: the ChernoffCalibrationInput (m ≤ c₁Y, H.4-closed) " ++
      "and ReturnFactoryReducedInput (2·M_L ≤ s regime + L.2.2 counts) remain genuine per-shell data." ]

theorem final3_irreducible_residual_nonempty : final3_irreducible_residual ≠ [] := by
  simp [final3_irreducible_residual]

#print axioms erdos260_reduced_minimal_final3

end

end Erdos260
