import Erdos260.UnconditionalAssemblyFinal
import Erdos260.AppendixI_PhaseMass
import Erdos260.ChargeBridgeReduction
import Erdos260.RunDescentConstruction

/-!
# ADVERSARIAL AUDIT of the four geometric per-shell inputs + the final assembly

Scratch / audit module.  **Edits no existing file and is not imported by the root.**

Targets (per the audit brief):
1. `towerCycle`        — `TowerRecurrentCycle`            (E.2–E.4 recurrent carry cycle)
2. `runProvenance`     — `RunProvenanceData` / `ResidualCenter` (§25.1 residual center)
3. `returnReduced`     — `ReturnFactoryReducedInput`      (M.2.1 nesting + I.5.1 routing, `2·M_L ≤ s`)
4. `chargeStructural`  — `ShellChargeStructuralInput` / `StructuralPkgGeometry` (J.5 PKG taxonomy)
PLUS the assembly `Erdos260MinimalAtomsFinal` / `toMinimalAtoms` / `erdos260_reduced_minimal_final`.

Every claim here is machine-checked.  No `sorry`/`admit`/`native_decide`/new `axiom`.

## Headline findings (see the per-section comments for the precise statements)

* **Tower — SOUND.**  `TowerRecurrentCycle` is genuinely inhabited, including by a
  NON-degenerate 2-vertex cycle (`towerTwoCycleWitness`, slopes `3/5,1/5`), not only the `1/3`
  toy.  The recurrence E.13 (`slope_trans`) is an *input law*; oddness `Odd H` is *derived*
  (`carryCycle_den_odd`), not assumed.  No `→ False`.

* **Run — SOUND but with a sharp caveat.**  `RunProvenanceData X` is inhabited for realistic
  large shells (`runProvenanceData_inhabited_large`).  HOWEVER the type is *empty at `X = 0`*
  (`runProvenanceData_zero_empty : RunProvenanceData 0 → False`), and the file's published
  non-vacuity certificate (`residualCenter_nonempty`) covers only the SUB-input `ResidualCenter`,
  **not** the actual field `RunProvenanceData`.  No circular digit↔cylinder assumption.

* **Return — SOUND** (witness degenerate).  `ReturnFactoryReducedInput cStar ξ X` is inhabited at
  the REAL constants for every `X ≥ 0` (`returnReduced_inhabited_real`), strictly stronger than
  the file's `(0,0,0)` certificate, but only via the degenerate `s = ij = 0` datum.

* **Charge — OVER-STRONG (vacuity consequence).**  The charge atom FORCES the joint phase term
  to be nonnegative (`charge_forces_termTRT_nonneg`: routed masses are positive parts, so
  `0 ≤ termTower+termReturn+termRun`), yet `ReturnFactoryData`/`RunFactoryData` masses are
  sign-unconstrained, so valid `SixPhaseFactoryData` exist with that term `< 0`
  (`exists_phases_neg_termTRT`).  Hence `ShellChargeStructuralInput phases carryData → False` for
  such (adversarial, manuscript-unfaithful) phases, so the `∀ phases` field is NOT a total
  function.  This is present in the **round-0 baseline** charge field too.

* **Assembly.**  Consequently `Erdos260MinimalAtomsFinal` is inconsistent with ANY qualifying
  failing shell (`assembly_inconsistent_with_shell : (m) (shell) (hcQ) → False`), reached WITHOUT
  the pressure floor / per-phase budgets / constant condition — purely from the charge field's
  over-quantification.  (This coincides with the *intended* `refutes_failingShell` mechanism, so it
  does not make the theorem more vacuous than the framework's inherent reliance on
  `FailingDyadicShell` being uninhabited; but it shows the charge hypothesis is over-strong.)
-/

namespace Erdos260

namespace AuditGeometric

open Finset

noncomputable section

/-! ## 0.  A reusable nonnegativity fact: the phase Tower term is `≥ 0`. -/

/-- `termTower` is a sum of nonnegative charged weights (`TowerPackageData.chargedWeight_nonneg`). -/
theorem termTower_nonneg {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) :
    0 ≤ termTower data := by
  unfold termTower
  exact Finset.sum_nonneg fun b hb => data.tower.chargedWeight_nonneg b hb

/-! ## 1.  TOWER — `TowerRecurrentCycle`

VERDICT: **SOUND**.  Inhabited, including by a genuine multi-vertex cycle (not just the `1/3`
toy).  E.13 (`slope_trans`) is an input law; `Odd H` is a *derived* theorem. -/

/-- Re-derived non-vacuity (closed witness, the `1/3` one-cycle). -/
theorem tower_inhabited : Nonempty TowerRecurrentCycle :=
  towerRecurrentCycle_inhabited

/-- **NON-degenerate witness**: a genuine 2-vertex recurrent cycle with DISTINCT slopes
`3/5 → 1/5`, satisfying the E.13 recurrence on both edges (`twoCycleExample`).  This rebuts the
"witness is only the `1/3` toy" concern: the input type is inhabited by realistic multi-vertex
cycle data. -/
def towerTwoCycleWitness : TowerRecurrentCycle where
  D := twoCycleExample
  μ := fun i => if i.val = 0 then (3 : ℚ) / 5 else (1 : ℚ) / 5
  hcast := by
    intro i
    show (((if i.val = 0 then (3 : ℚ) / 5 else (1 : ℚ) / 5) : ℚ) : ℝ)
      = (if i.val = 0 then (3 : ℝ) / 5 else (1 : ℝ) / 5)
    split_ifs <;> norm_num
  i := ⟨0, twoCycleExample.hn⟩
  Q := 1
  hQ := one_ne_zero

theorem tower_nondegenerate_inhabited : Nonempty TowerRecurrentCycle :=
  ⟨towerTwoCycleWitness⟩

/-- The non-degenerate witness carries the genuine 2-element recurrent vertex set. -/
theorem towerTwoCycleWitness_card : towerTwoCycleWitness.D.vertices.card = 2 :=
  twoCycleExample.card_vertices

/-- **Oddness of the AP modulus is DERIVED, not assumed.**  For the non-degenerate witness, the
slope atom's `H = (μ i).den` is odd — produced by `carryCycle_den_odd` (2-adic descent on the E.13
recurrence), i.e. the `hH` field of the produced `TowerSlopeAtom` is a theorem. -/
theorem towerTwoCycleWitness_H_odd : Odd towerTwoCycleWitness.toSlopeAtom.H :=
  towerTwoCycleWitness.toSlopeAtom.hH

/-! ## 2.  RUN — `RunProvenanceData` / `ResidualCenter`

VERDICT: **SOUND** for realistic (large) shells, with a sharp caveat. -/

/-- Re-derived: the §25.1 geometric SUB-input is inhabited (non-dyadic `1/3`). -/
theorem run_residualCenter_inhabited : Nonempty ResidualCenter :=
  residualCenter_nonempty

/--
**The actual field type `RunProvenanceData X` is EMPTY at `X = 0`.**

`chainRoot_le` demands `2·(scaleMult·ord) ≤ X·Ij·twoNegcY`, but at `X = 0` the right side is `0`
while `scaleMult·ord > 0`.  So the published certificate `residualCenter_nonempty` (which only
inhabits the SUB-input `ResidualCenter`) does NOT certify the field `RunProvenanceData` itself.
The genuine field is inhabited only for `X > 0` (and in fact only for `X` large — see below),
matching the manuscript's large-scale regime, never a degenerate `X = 0` instance.
-/
theorem runProvenanceData_zero_empty (r : RunProvenanceData (0 : ℝ)) : False := by
  have h := r.chainRoot_le
  rw [zero_mul, zero_mul] at h
  have hpos : 0 < r.C.scaleMult * orderOf (2 : ZMod r.C.q0) :=
    Nat.mul_pos r.C.scaleMult_pos r.C.order_pos
  have hposR : (0 : ℝ) < ((r.C.scaleMult * orderOf (2 : ZMod r.C.q0) : ℕ) : ℝ) := by
    exact_mod_cast hpos
  linarith

/-! A genuinely empty `RunRoutingData` (over the empty index type) — zero routing bounds, zero
chain mass.  Used to exhibit the realistic Run witness. -/

def emptyRunRouting : RunRoutingData Empty where
  branches := ∅
  state := Empty.elim
  towerSlot := Empty.elim
  returnSlot := Empty.elim
  densePackSlot := Empty.elim
  meanLow_route := fun b => nomatch b
  spike_route := fun b => nomatch b
  boundary_route := fun b => nomatch b

theorem emptyRunRouting_chainMass : emptyRunRouting.toTri.chainMass = 0 := by
  simp [RunRoutingData.toTri, RunBranchTrichotomy.chainMass, RunBranchTrichotomy.classMass,
    emptyRunRouting]

theorem emptyRunRouting_towerBound : emptyRunRouting.towerBound = 0 := by
  simp [RunRoutingData.towerBound, emptyRunRouting]

theorem emptyRunRouting_returnBound : emptyRunRouting.returnBound = 0 := by
  simp [RunRoutingData.returnBound, emptyRunRouting]

theorem emptyRunRouting_densePackBound : emptyRunRouting.densePackBound = 0 := by
  simp [RunRoutingData.densePackBound, emptyRunRouting]

/--
**`RunProvenanceData X` IS inhabited for realistic large shells.**

For any `X > 0` with `12·(scaleMult·ord) ≤ cStar·ξ·X` (the manuscript large-scale regime: `X`
large enough relative to the run period), the full per-shell Run provenance datum is constructible
on the concrete `1/3` residual center.  So the field is genuinely non-vacuous for real shells —
the only thing the file's certificate failed to record.  (Witness uses zero routing bounds; the
genuine shell would carry real ones, but inhabitability is what matters for non-vacuity.)
-/
theorem runProvenanceData_inhabited_large {X : ℝ} (hX : 0 < X)
    (hbig : 12 * ((residualCenterWitness.scaleMult
          * orderOf (2 : ZMod residualCenterWitness.q0) : ℕ) : ℝ)
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * X) :
    Nonempty (RunProvenanceData X) := by
  have hXne : X ≠ 0 := ne_of_gt hX
  have heq : X * 1 * (2 * ((residualCenterWitness.scaleMult
        * orderOf (2 : ZMod residualCenterWitness.q0) : ℕ) : ℝ) / X)
      = 2 * ((residualCenterWitness.scaleMult
        * orderOf (2 : ZMod residualCenterWitness.q0) : ℕ) : ℝ) := by
    field_simp
  exact ⟨{
    C := residualCenterWitness
    α := Empty
    u := 0
    weight := 0
    D := emptyRunRouting
    len := 1
    hlen := le_refl 1
    smallError := 0
    hsmall_nonneg := le_refl 0
    twoNegcY := 2 * ((residualCenterWitness.scaleMult
      * orderOf (2 : ZMod residualCenterWitness.q0) : ℕ) : ℝ) / X
    Ij := 1
    chain_capture := by rw [emptyRunRouting_chainMass]; exact Nat.cast_nonneg _
    chainRoot_le := le_of_eq heq.symm
    hSmall := by
      rw [emptyRunRouting_towerBound, emptyRunRouting_returnBound,
        emptyRunRouting_densePackBound, heq]
      linarith }⟩

/-! ## 3.  RETURN — `ReturnFactoryReducedInput`

VERDICT: **SOUND** (witness degenerate). -/

/--
**Inhabited at the REAL constants for every `X ≥ 0`.**

Strictly stronger than the file's `returnReduced_inhabited : Nonempty (ReturnFactoryReducedInput 0 0 0)`
— that one is at `cStar = ξ = X = 0`, which can never be a genuine shell.  Here the constants are the
genuine `erdos260Constants.cStar, .ξ` and `X` is arbitrary `≥ 0`.  The witness is still degenerate
(`s = ij = 0`, empty dirty family), so this certifies *inhabitability*, not realism.  `2·M_L ≤ s`
holds as `0 ≤ 0`; the `hSmall` (K.4) field is the genuine I.5.1 numerical budget input, not the
conclusion. -/
theorem returnReduced_inhabited_real (X : ℝ) (hX : 0 ≤ X) :
    Nonempty (ReturnFactoryReducedInput erdos260Constants.cStar erdos260Constants.ξ X) := by
  have hbudget : (0 : ℝ) ≤ erdos260Constants.cStar * erdos260Constants.ξ * X / 6 :=
    div_nonneg
      (mul_nonneg (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le) hX)
      (by norm_num)
  exact ⟨{
    dirtyFamily := ∅
    ML := 0
    envelope := by simp
    shellSize := 0
    anchor_lt_shell := by intro x hx; simp at hx
    ordinaryShort := 0
    semiperiodic := 0
    nonlocalLong := 0
    c1 := 0
    c2 := 0
    c3 := 0
    c4 := 0
    s := 0
    ij := 0
    smallError := 0
    shell_route := by simp
    hXij_area := by simp
    ml_regime := by norm_num
    olc_return_budget := by
      have h0 : (0 : ℝ) * X * 0 = 0 := by ring
      have h1 : (0 : ℝ) * erdos260Constants.ξ * 0 * X * 0 + 0 / 4 = 0 := by ring
      rw [h0, h1]
    ordinaryShort_bound := by
      have h1 : (0 : ℝ) * erdos260Constants.ξ * 0 * X * 0 + 0 / 4 = 0 := by ring
      rw [h1]
    semiperiodic_bound := by
      have h1 : (0 : ℝ) * erdos260Constants.ξ * 0 * X * 0 + 0 / 4 = 0 := by ring
      rw [h1]
    nonlocalLong_bound := by
      have h1 : (0 : ℝ) * erdos260Constants.ξ * 0 * X * 0 + 0 / 4 = 0 := by ring
      rw [h1]
    hSmall := by
      have h0 : (0 + 0 + 0 + 0 : ℝ) * erdos260Constants.ξ * 0 * X * 0 + 0 = 0 := by ring
      rw [h0]; exact hbudget }⟩

/-! ## 4.  CHARGE — `ShellChargeStructuralInput` / `StructuralPkgGeometry`

VERDICT: **OVER-STRONG** (with a vacuity consequence) on the count×multiplier / TRT side;
the `StructuralPkgGeometry` coverage primitive `pkg_exposes` is FAITHFUL (no coverage baked in).

### 4a.  The over-strength obstruction. -/

/--
**The charge routing atom FORCES the joint Tower+Return+Run phase term to be `≥ 0`.**

Routed class masses are sums of `positivePart`s (`routedClassMassOf_nonneg`), so the `hTRT` field
`routed(2)+routed(4)+routed(5) ≤ termTower+termReturn+termRun` forces the right side `≥ 0`. -/
theorem charge_forces_termTRT_nonneg
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell cPr} {oldResMass : ℝ}
    (rc : CarryPriorityRoutingCharge phases carryData oldResMass) :
    0 ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
        + termRun phases.toClosurePhaseData := by
  have h := rc.hTRT
  have h2 := routedClassMassOf_nonneg carryData rc.routing.classify (2 : Fin 7)
  have h4 := routedClassMassOf_nonneg carryData rc.routing.classify (4 : Fin 7)
  have h5 := routedClassMassOf_nonneg carryData rc.routing.classify (5 : Fin 7)
  linarith

/-- Same obstruction at the actual capstone field type `ShellChargeStructuralInput` (via `.build`). -/
theorem shellChargeStructuralInput_termTRT_nonneg
    {shell : FailingDyadicShell}
    {phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell erdos260Constants.cPr}
    (inp : ShellChargeStructuralInput phases carryData) :
    0 ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
        + termRun phases.toClosurePhaseData :=
  charge_forces_termTRT_nonneg inp.build.routingCharge

/-! ### 4b.  ... but valid phase data can make that term negative. -/

/-- A perfectly valid `ReturnFactoryData` whose four masses sum to `-t-1` (`t ≥ 0`).  The fields are
sign-unconstrained (only upper-bounded), so this is a genuine inhabitant. -/
def advReturn (cStar ξ X t : ℝ) (ht : 0 ≤ t) (hc : 0 ≤ cStar) (hξ : 0 ≤ ξ) (hX : 0 ≤ X) :
    ReturnFactoryData cStar ξ X where
  ordinaryShort := -t - 1
  semiperiodic := 0
  olc := 0
  nonlocalLong := 0
  c1 := 0
  c2 := 0
  c3 := 0
  c4 := 0
  s := 0
  ij := 0
  smallError := 0
  hOrdinaryShort := by
    have h0 : (0 : ℝ) * ξ * 0 * X * 0 + 0 / 4 = 0 := by ring
    linarith
  hSemiperiodic := by
    have h0 : (0 : ℝ) * ξ * 0 * X * 0 + 0 / 4 = 0 := by ring
    linarith
  hOLC := by
    have h0 : (0 : ℝ) * ξ * 0 * X * 0 + 0 / 4 = 0 := by ring
    linarith
  hNonlocalLong := by
    have h0 : (0 : ℝ) * ξ * 0 * X * 0 + 0 / 4 = 0 := by ring
    linarith
  hSmall := by
    have h0 : (0 + 0 + 0 + 0 : ℝ) * ξ * 0 * X * 0 + 0 = 0 := by ring
    have h1 : (0 : ℝ) ≤ cStar * ξ * X / 6 :=
      div_nonneg (mul_nonneg (mul_nonneg hc hξ) hX) (by norm_num)
    linarith

/-- A perfectly valid `RunFactoryData` with `runMass = 0`. -/
def advRun (cStar ξ X : ℝ) (hc : 0 ≤ cStar) (hξ : 0 ≤ ξ) (hX : 0 ≤ X) :
    RunFactoryData cStar ξ X where
  runMass := 0
  nextTower := 0
  nextReturn := 0
  nextDensePack := 0
  twoNegcY := 0
  Ij := 0
  smallError := 0
  trichotomy := by
    have h0 : (0 : ℝ) + 0 + 0 + X * 0 * 0 + 0 = 0 := by ring
    linarith
  hSmall := by
    have h0 : (0 : ℝ) + 0 + 0 + X * 0 * 0 + 0 = 0 := by ring
    have h1 : (0 : ℝ) ≤ cStar * ξ * X / 6 :=
      div_nonneg (mul_nonneg (mul_nonneg hc hξ) hX) (by norm_num)
    linarith

/--
**From ANY phase data, a valid perturbed phase datum with `termTower+termReturn+termRun < 0`.**

Keep `tower`/`chernoff`/`cnl`/`densePack`; replace `returnPkg` by `advReturn` (sum `= -t-1`,
`t = termTower`) and `run` by `advRun` (`= 0`).  Then the joint term is `t + (-t-1) + 0 = -1 < 0`.
Every field of the perturbed `SixPhaseFactoryData` is a legitimate inhabitant of its type, so this
is genuine, manuscript-unfaithful-but-type-valid data. -/
theorem exists_phases_neg_termTRT {cStar ξ X : ℝ}
    (hc : 0 ≤ cStar) (hξ : 0 ≤ ξ) (hX : 0 ≤ X)
    (p : SixPhaseFactoryData cStar ξ X) :
    ∃ p' : SixPhaseFactoryData cStar ξ X,
      termTower p'.toClosurePhaseData + termReturn p'.toClosurePhaseData
        + termRun p'.toClosurePhaseData < 0 := by
  refine ⟨{ p with
      returnPkg := advReturn cStar ξ X (termTower p.toClosurePhaseData)
        (termTower_nonneg p.toClosurePhaseData) hc hξ hX
      run := advRun cStar ξ X hc hξ hX }, ?_⟩
  have hT : termTower ({ p with
      returnPkg := advReturn cStar ξ X (termTower p.toClosurePhaseData)
        (termTower_nonneg p.toClosurePhaseData) hc hξ hX
      run := advRun cStar ξ X hc hξ hX } : SixPhaseFactoryData cStar ξ X).toClosurePhaseData
        = termTower p.toClosurePhaseData := rfl
  have hRun : termRun ({ p with
      returnPkg := advReturn cStar ξ X (termTower p.toClosurePhaseData)
        (termTower_nonneg p.toClosurePhaseData) hc hξ hX
      run := advRun cStar ξ X hc hξ hX } : SixPhaseFactoryData cStar ξ X).toClosurePhaseData
        = 0 := rfl
  have hR : termReturn ({ p with
      returnPkg := advReturn cStar ξ X (termTower p.toClosurePhaseData)
        (termTower_nonneg p.toClosurePhaseData) hc hξ hX
      run := advRun cStar ξ X hc hξ hX } : SixPhaseFactoryData cStar ξ X).toClosurePhaseData
        = -(termTower p.toClosurePhaseData) - 1 := by
    show (-(termTower p.toClosurePhaseData) - 1) + 0 + 0 + 0 = -(termTower p.toClosurePhaseData) - 1
    ring
  rw [hT, hR, hRun]; linarith

/--
**Consequence: `ShellChargeStructuralInput` is EMPTY for adversarial phases.**

Given any seed phase data `p` (e.g. the genuine data the manuscript would build), there is a valid
`SixPhaseFactoryData p'` for which `ShellChargeStructuralInput p' carryData → False`.  Hence the
charge field `∀ phases, ShellChargeStructuralInput phases carryData` is NOT a total function:
once genuine phase data exists for the shell, the field is uninhabitable. -/
theorem chargeStructural_field_not_total
    {shell : FailingDyadicShell}
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
    (p : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)) :
    ∃ p' : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ),
      (ShellChargeStructuralInput p' carryData → False) := by
  obtain ⟨p', hp'⟩ :=
    exists_phases_neg_termTRT erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le
      shell.X_nonneg_real p
  exact ⟨p', fun inp => by
    have hnn := shellChargeStructuralInput_termTRT_nonneg (carryData := carryData) inp
    linarith⟩

/-! ### 4c.  `StructuralPkgGeometry` / `pkg_exposes` — FAITHFUL (no coverage assumed). -/

theorem structuralPkgGeometry_inhabited : Nonempty StructuralPkgGeometry :=
  ⟨StructuralPkgGeometry.sample⟩

/-- **Coverage is NOT baked in.**  The all-clean geometry (`label ≡ none`, no package ever fires)
is a valid `StructuralPkgGeometry`, and on it the proved selector never returns `PKG` — so
`pkg_exposes` holds *vacuously*, confirming the structure assumes no coverage between the free
`label`/`cleanAvail` data; coverage is the *derived* `StructuralPkgGeometry.pkg_exposes`. -/
def noCoverageGeom : StructuralPkgGeometry :=
  StructuralPkgGeometry.ofLabel (fun _ => none)

theorem noCoverageGeom_never_pkg (s : LiftState) :
    canonicalCNLSelector (noCoverageGeom.cnlOf s) ≠ some CNLClass.pkg := by
  intro h
  rw [StructuralPkgGeometry.selector_eq_pkg_iff] at h
  simp [noCoverageGeom, StructuralPkgGeometry.ofLabel] at h

/-! ## 5.  ASSEMBLY — `Erdos260MinimalAtomsFinal` -/

/--
**`Erdos260MinimalAtomsFinal` is inconsistent with ANY qualifying failing shell.**

Given `m` and any `shell` with the pinned `cQ`, build the genuine per-shell phase data and carry
data from `m`'s own fields, perturb the phase data to make `termTower+termReturn+termRun < 0`, then
feed it to `m.chargeStructural`: the charge atom forces that term `≥ 0`.  Contradiction.

Note: this derives `False` WITHOUT the pressure floor, the six per-phase budgets, or the constant
condition — purely from the charge field's `∀ phases` over-quantification.  It therefore shows the
charge HYPOTHESIS is over-strong.  (It coincides in spirit with the intended `refutes_failingShell`
mechanism "atoms ⇒ no failing shell", so it does not make the conditional more vacuous than the
framework's standing assumption that `FailingDyadicShell` is uninhabited.) -/
theorem assembly_inconsistent_with_shell
    (m : Erdos260MinimalAtomsFinal) (shell : FailingDyadicShell)
    (hcQ : shell.cQ = erdos260Constants.cQ) : False := by
  let RA := m.toMinimalAtoms.toResidualAtoms
  let cd : CarryDataFromFailure shell erdos260Constants.cPr := RA.carryData shell hcQ
  let phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
    { chernoff := RA.chernoff shell hcQ
      cnl := RA.cnl shell hcQ
      tower := RA.tower shell hcQ
      densePack := RA.densePack shell hcQ
      returnPkg := RA.returnPkg shell hcQ
      run := RA.run shell hcQ }
  obtain ⟨p', hp'⟩ :=
    exists_phases_neg_termTRT erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le
      shell.X_nonneg_real phases
  have hnn := shellChargeStructuralInput_termTRT_nonneg
    (carryData := cd) (m.chargeStructural shell hcQ p' cd)
  linarith

/--
**Equivalently: inhabiting the final atoms forces "no qualifying failing shell".**

So the published per-field non-vacuity certificates do NOT lift to `Nonempty Erdos260MinimalAtomsFinal`:
the structure is inhabitable only in the regime where no failing shell with the pinned `cQ` exists. -/
theorem assembly_forces_no_shell
    (m : Erdos260MinimalAtomsFinal) :
    ∀ shell : FailingDyadicShell, shell.cQ ≠ erdos260Constants.cQ := by
  intro shell hcQ
  exact assembly_inconsistent_with_shell m shell hcQ

/-! ## 6.  Axiom audit -/

#print axioms tower_nondegenerate_inhabited
#print axioms towerTwoCycleWitness_H_odd
#print axioms runProvenanceData_zero_empty
#print axioms runProvenanceData_inhabited_large
#print axioms returnReduced_inhabited_real
#print axioms charge_forces_termTRT_nonneg
#print axioms shellChargeStructuralInput_termTRT_nonneg
#print axioms exists_phases_neg_termTRT
#print axioms chargeStructural_field_not_total
#print axioms noCoverageGeom_never_pkg
#print axioms assembly_inconsistent_with_shell
#print axioms assembly_forces_no_shell

end

end AuditGeometric

end Erdos260
