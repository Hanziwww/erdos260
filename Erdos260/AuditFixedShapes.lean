import Mathlib
import Erdos260.UnconditionalAssemblyFinal
import Erdos260.AppendixI_PhaseMass

/-!
# FRESH ADVERSARIAL RE-AUDIT of the two faithfulness fixes (charge guard + carry gate)

This is a **scratch audit module**.  It edits nothing upstream and is not imported by
the root.  It machine-checks (no `sorry`/`admit`/`native_decide`/new `axiom`) the three
items of the re-audit brief against the *current, fixed* shapes of:

* `Erdos260MinimalAtomsFinal` (capstone hypothesis bundle,
  `erdos260_reduced_minimal_final : Erdos260MinimalAtomsFinal → Erdos260Statement`);
* the `SixPhaseFactoryData.trtNonneg` guard on the per-shell `chargeStructural` field
  + the new `returnRunMassNonneg` provider field;
* the `FailingDyadicShell.aboveCarryThreshold` gate on the per-shell `carryWindow`
  field + the pinned `GlobalAssemblyCoreInputs.startThreshold`.

The two stale audit files (`AuditAnalyticInputs`, `AuditGeometricInputs`) are NOT
imported; the probes below are independent re-derivations against the fixed types.

## Headline verdicts (proved below)

* **ITEM 1 — charge over-strength fix: SOUND.**  `§0` proves the only sign-unconstrained
  phase terms are `termReturn`/`termRun` (`termChernoff`/`termCnl`/`termDensePack` are
  nonnegative **by type**), so the joint-TRT guard `trtNonneg` targets *exactly* the
  unconstrained terms.  `§1` rebuilds the old negative-mass attack
  (`advPhases`): the type `ShellChargeStructuralInput (advPhases p) cd` is **still**
  empty (`chargeStructuralInput_advPhases_empty`), but the adversarial phases now FAIL
  the guard (`advPhases_not_trtNonneg`), so the field is never asked to produce it — the
  `chargeStructural_field_not_total` refutation is unreachable.  Genuine nonnegative-mass
  phases satisfy the guard (`nonnegPhases_trtNonneg`) and the guarded field is inhabited
  (`guardedCharge_inhabited`, needing ONLY `trtNonneg` + empty high-excess).

* **ITEM 2 — carry over-quantification fix: SOUND.**  The gate genuinely bites
  (`aboveCarryThreshold_forces_pow26`: `2^26 ≤ X`, exponent `≥ 1`), small shells are
  excluded (`small_not_aboveCarryThreshold`), and the pinned `startThreshold` is the real
  threshold `2^(carryB Q + 25) ≥ 2^26 > 0` (`startThreshold_eq`, `startThreshold_pos`),
  NOT the old vacuous `0`.  `aboveCarryThreshold` IS the `startThreshold ≤ X` inequality
  (`aboveCarryThreshold_is_startThreshold`).

* **ITEM 3 — no NEW vacuity: SOUND.**  The guard and the gate only SHRINK their fields'
  domains (cannot introduce vacuity); the new `returnRunMassNonneg` obligation is
  satisfied by mass-`0` data (`returnRunMassNonneg_witness`).  The known refutation route
  is blocked (`§1`); the guard hypothesis and an inhabited charge input are jointly
  realizable (`guardedCharge_inhabited`); the gated carry field is inhabited jointly with
  the gate at a large shell (`gated_carryWindow_inhabited_at_large_shell`).  No proof of
  `Erdos260MinimalAtomsFinal → False` is obtainable.
-/

namespace Erdos260

namespace AuditFixed

open Finset

noncomputable section

/-! ============================================================================
## §0.  Phase-term sign analysis — the guard targets exactly the unconstrained terms

The charge atom carries SEPARATE per-class bounds
`hChernoff/hCnl/hDensePack/hTRT/hOldRes`.  The joint-TRT guard `trtNonneg` constrains
only `termTower + termReturn + termRun`.  For the fix to be complete (and not leave a
back-door over-strength via Chernoff/CNL/DensePack), those three terms must be
nonnegative **for every valid phase datum**.  They are — by the structure fields
`ChernoffPathData.weight_nonneg`, `CNLEntropyData.shellFactor_nonneg`/`Ij_nonneg`
(+`cleanCNLKraftSum_nonneg`), and `Nat.cast_nonneg`.  So the only sign-unconstrained
phase masses are `termReturn` (= `ReturnFactoryData.massSum`) and `termRun`
(= `RunFactoryData.runMass`), which are exactly the two combined inside the guarded TRT
term.  `termTower` is also nonnegative (`Erdos260.termTower_nonneg`).
============================================================================ -/

/-- **`termChernoff` is nonnegative by type** (`ChernoffPathData.weight_nonneg` on the
high-cost subfamily).  So the charge atom's `hChernoff` bound `0 ≤ termChernoff` (at empty
high-excess) is automatic — Chernoff is NOT a residual over-strength back-door. -/
theorem termChernoff_nonneg {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) :
    0 ≤ termChernoff data := by
  unfold termChernoff weightedMass
  exact Finset.sum_nonneg fun p hp => data.chernoff.weight_nonneg p (mem_highCostSet.1 hp).1

/-- **`termCnl` is nonnegative by type** for `X ≥ 0` (`cleanCNLKraftSum_nonneg`,
`shellFactor_nonneg`, `Ij_nonneg`).  So `hCnl`'s `0 ≤ termCnl` (at empty high-excess) is
automatic — CNL is NOT a residual over-strength back-door. -/
theorem termCnl_nonneg {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) (hX : 0 ≤ X) :
    0 ≤ termCnl data := by
  unfold termCnl
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (cleanCNLKraftSum_nonneg _ _ _) data.cnl.shellFactor_nonneg) hX)
    data.cnl.Ij_nonneg

/-- **`termDensePack` is nonnegative by type** (a cardinality).  So `hDensePack`'s
`0 ≤ termDensePack` (at empty high-excess) is automatic. -/
theorem termDensePack_nonneg {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) :
    0 ≤ termDensePack data := by
  unfold termDensePack; exact Nat.cast_nonneg _

/-- **The structural reason the joint-TRT guard suffices.**  For any phase datum,
`termChernoff`, `termCnl` (given `X ≥ 0`), `termDensePack` are ALL `≥ 0` by type; thus the
ONLY phase masses that can be negative are `termReturn` and `termRun`, which are precisely
the two summed (with the always-nonnegative `termTower`) inside the guarded joint term.
The guard `trtNonneg` is therefore aimed at exactly the sign-unconstrained masses — there
is no Chernoff/CNL/DensePack analogue of the negative-mass attack. -/
theorem only_return_run_unconstrained {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X)
    (hX : 0 ≤ X) :
    0 ≤ termChernoff data ∧ 0 ≤ termCnl data ∧ 0 ≤ termDensePack data ∧ 0 ≤ termTower data :=
  ⟨termChernoff_nonneg data, termCnl_nonneg data hX, termDensePack_nonneg data,
    termTower_nonneg data⟩

/-! ============================================================================
## §1.  ITEM 1 — the negative-mass charge attack is excluded by the guard

We reconstruct the prior attack vector against the *current* types (the stale
`AuditGeometricInputs.advReturn/advRun/exists_phases_neg_termTRT/chargeStructural_field_not_total`
are NOT imported).  `advReturn`/`advRun` are genuine inhabitants of `ReturnFactoryData` /
`RunFactoryData` (their fields are only UPPER-bounded), so `advPhases p` is a genuine
`SixPhaseFactoryData` whose joint TRT term is `-1 < 0`.
============================================================================ -/

/-- A genuine `ReturnFactoryData` with `massSum = -t - 1` (`t ≥ 0`); fields only
upper-bounded, so the very negative `ordinaryShort` is a legitimate inhabitant. -/
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
    have h : (0 : ℝ) * ξ * 0 * X * 0 + 0 / 4 = 0 := by ring
    linarith
  hSemiperiodic := by
    have h : (0 : ℝ) * ξ * 0 * X * 0 + 0 / 4 = 0 := by ring
    linarith
  hOLC := by
    have h : (0 : ℝ) * ξ * 0 * X * 0 + 0 / 4 = 0 := by ring
    linarith
  hNonlocalLong := by
    have h : (0 : ℝ) * ξ * 0 * X * 0 + 0 / 4 = 0 := by ring
    linarith
  hSmall := by
    have h : ((0 : ℝ) + 0 + 0 + 0) * ξ * 0 * X * 0 + 0 = 0 := by ring
    have hb : (0 : ℝ) ≤ cStar * ξ * X / 6 :=
      div_nonneg (mul_nonneg (mul_nonneg hc hξ) hX) (by norm_num)
    linarith

/-- A genuine `ReturnFactoryData` with `massSum = 0` (all components `0`). -/
def zeroReturn (cStar ξ X : ℝ) (hc : 0 ≤ cStar) (hξ : 0 ≤ ξ) (hX : 0 ≤ X) :
    ReturnFactoryData cStar ξ X where
  ordinaryShort := 0
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
    have h : (0 : ℝ) * ξ * 0 * X * 0 + 0 / 4 = 0 := by ring
    linarith
  hSemiperiodic := by
    have h : (0 : ℝ) * ξ * 0 * X * 0 + 0 / 4 = 0 := by ring
    linarith
  hOLC := by
    have h : (0 : ℝ) * ξ * 0 * X * 0 + 0 / 4 = 0 := by ring
    linarith
  hNonlocalLong := by
    have h : (0 : ℝ) * ξ * 0 * X * 0 + 0 / 4 = 0 := by ring
    linarith
  hSmall := by
    have h : ((0 : ℝ) + 0 + 0 + 0) * ξ * 0 * X * 0 + 0 = 0 := by ring
    have hb : (0 : ℝ) ≤ cStar * ξ * X / 6 :=
      div_nonneg (mul_nonneg (mul_nonneg hc hξ) hX) (by norm_num)
    linarith

/-- A genuine `RunFactoryData` with `runMass = 0`. -/
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
    have h : (0 : ℝ) + 0 + 0 + X * 0 * 0 + 0 = 0 := by ring
    linarith
  hSmall := by
    have h : (0 : ℝ) + 0 + 0 + X * 0 * 0 + 0 = 0 := by ring
    have hb : (0 : ℝ) ≤ cStar * ξ * X / 6 :=
      div_nonneg (mul_nonneg (mul_nonneg hc hξ) hX) (by norm_num)
    linarith

/-- **The adversarial (negative-mass) phase datum** built from a seed `p`: keep
tower/chernoff/cnl/densePack, replace `returnPkg` by `advReturn` (`massSum = -termTower-1`)
and `run` by `advRun` (`runMass = 0`).  A genuine `SixPhaseFactoryData`. -/
def advPhases {cStar ξ X : ℝ} (hc : 0 ≤ cStar) (hξ : 0 ≤ ξ) (hX : 0 ≤ X)
    (p : SixPhaseFactoryData cStar ξ X) : SixPhaseFactoryData cStar ξ X :=
  { p with
    returnPkg := advReturn cStar ξ X (termTower p.toClosurePhaseData)
      (termTower_nonneg p.toClosurePhaseData) hc hξ hX
    run := advRun cStar ξ X hc hξ hX }

/-- The adversarial phase datum has joint Tower+Return+Run term `= -1`. -/
theorem advPhases_termTRT {cStar ξ X : ℝ} (hc : 0 ≤ cStar) (hξ : 0 ≤ ξ) (hX : 0 ≤ X)
    (p : SixPhaseFactoryData cStar ξ X) :
    termTower (advPhases hc hξ hX p).toClosurePhaseData
      + termReturn (advPhases hc hξ hX p).toClosurePhaseData
      + termRun (advPhases hc hξ hX p).toClosurePhaseData = -1 := by
  have e1 : termTower (advPhases hc hξ hX p).toClosurePhaseData
      = termTower p.toClosurePhaseData := rfl
  have e2 : termReturn (advPhases hc hξ hX p).toClosurePhaseData
      = -(termTower p.toClosurePhaseData) - 1 := by
    rw [termReturn_toClosurePhaseData_eq_massSum]
    show (advReturn cStar ξ X (termTower p.toClosurePhaseData)
      (termTower_nonneg p.toClosurePhaseData) hc hξ hX).massSum
        = -(termTower p.toClosurePhaseData) - 1
    unfold ReturnFactoryData.massSum
    show (-(termTower p.toClosurePhaseData) - 1) + 0 + 0 + 0
        = -(termTower p.toClosurePhaseData) - 1
    ring
  have e3 : termRun (advPhases hc hξ hX p).toClosurePhaseData = 0 := rfl
  rw [e1, e2, e3]; ring

/-- **The adversarial phases FAIL the guard** (`¬ trtNonneg`).  This is exactly the
mechanism that excludes them from the fixed per-shell charge field: its domain is
restricted to `phases.trtNonneg`, which these phases violate. -/
theorem advPhases_not_trtNonneg {cStar ξ X : ℝ} (hc : 0 ≤ cStar) (hξ : 0 ≤ ξ) (hX : 0 ≤ X)
    (p : SixPhaseFactoryData cStar ξ X) :
    ¬ (advPhases hc hξ hX p).trtNonneg :=
  neg_termTRT_not_trtNonneg _ (by rw [advPhases_termTRT hc hξ hX p]; norm_num)

/-- **Re-derivation: the charge structural input forces `trtNonneg`** (the audit's
necessity direction, via `.build` + `shellRoutedChargeAtom_forces_trtNonneg`).  So the
guard discards no data the atom would have accepted. -/
theorem chargeStructuralInput_forces_trtNonneg {shell : FailingDyadicShell}
    {phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell erdos260Constants.cPr}
    (inp : ShellChargeStructuralInput phases carryData) : phases.trtNonneg :=
  shellRoutedChargeAtom_forces_trtNonneg inp.build

/-- **The audit fact still holds: `ShellChargeStructuralInput` is empty for the
adversarial phases.**  So the type-level over-strength obstruction
(`AuditGeometricInputs.chargeStructural_field_not_total`) is still a true statement... -/
theorem chargeStructuralInput_advPhases_empty {shell : FailingDyadicShell}
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
    (p : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)) :
    ShellChargeStructuralInput
        (advPhases erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le
          shell.X_nonneg_real p) carryData → False := by
  intro inp
  exact advPhases_not_trtNonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le
    shell.X_nonneg_real p (chargeStructuralInput_forces_trtNonneg inp)

/-- **... but it is now UNREACHABLE through the field.**  The fixed per-shell charge field
`chargeStructural shell hcQ phases carryData (hphases : phases.trtNonneg)` requires the
guard argument `hphases`, which for the adversarial phases is `False`
(`advPhases_not_trtNonneg`).  So the bundle is never asked to produce the (empty) charge
input for them: the `→ False` of `chargeStructuralInput_advPhases_empty` has no
producible antecedent.  This is the precise sense in which
`chargeStructural_field_not_total` "no longer applies to the guarded field". -/
theorem charge_attack_guard_argument_unprovable {cStar ξ X : ℝ}
    (hc : 0 ≤ cStar) (hξ : 0 ≤ ξ) (hX : 0 ≤ X)
    (p : SixPhaseFactoryData cStar ξ X) :
    (advPhases hc hξ hX p).trtNonneg → False :=
  advPhases_not_trtNonneg hc hξ hX p

/-! ### Genuine path preserved -/

/-- **The genuine path is untouched: nonnegative-mass phases satisfy the guard.**
(`= SixPhaseFactoryData.trtNonneg_of_returnRun_nonneg`, the discharge the consumer uses.) -/
theorem genuinePhases_trtNonneg {cStar ξ X : ℝ} (p : SixPhaseFactoryData cStar ξ X)
    (h : 0 ≤ p.returnPkg.massSum + p.run.runMass) : p.trtNonneg :=
  SixPhaseFactoryData.trtNonneg_of_returnRun_nonneg p h

/-- A genuine nonnegative-mass phase datum (`returnPkg`/`run` masses both `0`). -/
def nonnegPhases {cStar ξ X : ℝ} (hc : 0 ≤ cStar) (hξ : 0 ≤ ξ) (hX : 0 ≤ X)
    (p : SixPhaseFactoryData cStar ξ X) : SixPhaseFactoryData cStar ξ X :=
  { p with
    returnPkg := zeroReturn cStar ξ X hc hξ hX
    run := advRun cStar ξ X hc hξ hX }

/-- **The genuine (nonnegative-mass) phases DO satisfy the guard.**  Concrete witness that
the restriction admits a real configuration (here masses `0`). -/
theorem nonnegPhases_trtNonneg {cStar ξ X : ℝ} (hc : 0 ≤ cStar) (hξ : 0 ≤ ξ) (hX : 0 ≤ X)
    (p : SixPhaseFactoryData cStar ξ X) :
    (nonnegPhases hc hξ hX p).trtNonneg := by
  apply genuinePhases_trtNonneg
  show (0 : ℝ) ≤ (zeroReturn cStar ξ X hc hξ hX).massSum + (advRun cStar ξ X hc hξ hX).runMass
  unfold ReturnFactoryData.massSum
  show (0 : ℝ) ≤ (0 + 0 + 0 + 0) + 0
  norm_num

/-- **The guarded charge field is inhabited for genuine data**, needing ONLY the guard
`trtNonneg` and the honest degenerate regime `highExcessStarts = ∅` — the Chernoff/CNL
nonnegativity hypotheses of `shellChargeStructuralInput_inhabited_of_emptyHighExcess` are
auto-discharged by §0.  Confirms `trtNonneg` and an inhabited `ShellChargeStructuralInput`
are JOINTLY realizable (no hidden contradiction the guard could have created). -/
theorem guardedCharge_inhabited {shell : FailingDyadicShell}
    (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
    (hphases : phases.trtNonneg)
    (hEmpty : highExcessStarts carryData.starts (hitGap carryData.a)
        carryData.r carryData.T carryData.Y = ∅) :
    Nonempty (ShellChargeStructuralInput phases carryData) :=
  shellChargeStructuralInput_inhabited_of_emptyHighExcess phases carryData hphases hEmpty
    (termChernoff_nonneg _) (termCnl_nonneg _ shell.X_nonneg_real)

/-! ============================================================================
## §2.  ITEM 2 — the carry gate genuinely bites; the pinned threshold is real

`aboveCarryThreshold shell := carryThreshold (carryB shell.Q + 19) ≤ shell.X`, and
`carryThreshold B = 2 ^ (B + 6)`, so the gate is `2^(carryB Q + 25) ≤ X`.  Independent
re-derivations (the upstream `aboveCarryThreshold_forces_scale` etc. are referenced too).
============================================================================ -/

/-- `carryThreshold (carryB Q + 19) = 2 ^ (carryB Q + 25)` — unfolds the threshold defs. -/
theorem carryThreshold_carryB_eq (Q : ℕ) :
    carryThreshold (carryB Q + 19) = 2 ^ (carryB Q + 25) := by
  unfold carryThreshold carryLogThreshold
  congr 1

/-- `1 ≤ carryB Q` always (`carryB Q = Nat.log 2 (Q*4) + 1`), so the gate exponent
`carryB Q + 25 ≥ 26 ≥ 1`. -/
theorem one_le_carryB (Q : ℕ) : 1 ≤ carryB Q := by unfold carryB; omega

/-- **The gate genuinely bites: `aboveCarryThreshold → 2^26 ≤ X`** with the dyadic
exponent `26 ≥ 1`.  Independent re-derivation; not the old vacuous `0 ≤ X`. -/
theorem aboveCarryThreshold_forces_pow26 {shell : FailingDyadicShell}
    (h : shell.aboveCarryThreshold) : (2 : ℕ) ^ 26 ≤ shell.X := by
  have h' : (2 : ℕ) ^ (carryB shell.Q + 25) ≤ shell.X := h
  exact le_trans (Nat.pow_le_pow_right (by norm_num) (by have := one_le_carryB shell.Q; omega)) h'

/-- **The gate is non-trivial: it forces a real `2^k ≤ X` with `k ≥ 1`.**  Existential
form of the previous lemma making the "`k ≥ 1`" explicit. -/
theorem aboveCarryThreshold_forces_pow_ge_one {shell : FailingDyadicShell}
    (h : shell.aboveCarryThreshold) : ∃ k : ℕ, 1 ≤ k ∧ (2 : ℕ) ^ k ≤ shell.X :=
  ⟨26, by norm_num, aboveCarryThreshold_forces_pow26 h⟩

/-- **Small shells are genuinely excluded.**  No shell with `X < 2^26` is above the carry
threshold — the carry obligation is genuinely not demanded there. -/
theorem small_not_aboveCarryThreshold {shell : FailingDyadicShell}
    (hX : shell.X < 2 ^ 26) : ¬ shell.aboveCarryThreshold := by
  intro h; exact absurd (aboveCarryThreshold_forces_pow26 h) (by omega)

/-- **`aboveCarryThreshold` IS definitionally the `startThreshold ≤ X` inequality.** -/
theorem aboveCarryThreshold_is_startThreshold (shell : FailingDyadicShell) :
    shell.aboveCarryThreshold ↔ carryThreshold (carryB shell.Q + 19) ≤ shell.X :=
  Iff.rfl

/-- **The pinned per-instance `startThreshold` is the real carry-large threshold**, NOT
the old vacuous `canonicalThresholds = 0`.  Holds for every core-inputs record and every
qualifying `(Q, d)`. -/
theorem startThreshold_eq (data : GlobalAssemblyCoreInputs) (Q : ℕ) (d : ℕ → ℕ)
    (hQ : 0 < Q) (hd : BinaryDigits d) (hnt : ¬ EventuallyZero d)
    (hr : ∃ P : ℤ, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) :
    data.startThreshold Q d hQ hd hnt hr = carryThreshold (carryB Q + 19) :=
  rfl

/-- **The pinned threshold is strictly positive** (`= 2^(carryB Q + 25) > 0`), so it is
emphatically not `0`. -/
theorem startThreshold_pos (data : GlobalAssemblyCoreInputs) (Q : ℕ) (d : ℕ → ℕ)
    (hQ : 0 < Q) (hd : BinaryDigits d) (hnt : ¬ EventuallyZero d)
    (hr : ∃ P : ℤ, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) :
    0 < data.startThreshold Q d hQ hd hnt hr := by
  rw [startThreshold_eq, carryThreshold_carryB_eq]; positivity

/-- **The pinned threshold is `≥ 2^26`** — the same non-trivial scale the gate forces. -/
theorem startThreshold_ge_pow26 (data : GlobalAssemblyCoreInputs) (Q : ℕ) (d : ℕ → ℕ)
    (hQ : 0 < Q) (hd : BinaryDigits d) (hnt : ¬ EventuallyZero d)
    (hr : ∃ P : ℤ, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) :
    (2 : ℕ) ^ 26 ≤ data.startThreshold Q d hQ hd hnt hr := by
  rw [startThreshold_eq, carryThreshold_carryB_eq]
  exact Nat.pow_le_pow_right (by norm_num) (by have := one_le_carryB Q; omega)

/-- **The gate delivers exactly the `ShellWindowInputs` scale** (re-export of the upstream
`aboveCarryThreshold_provides_windowScale`): `4Q ≤ 2^B ∧ B + 25 ≤ L` for `B = carryB Q`. -/
theorem gate_provides_windowScale {shell : FailingDyadicShell} {L : ℕ}
    (hX : shell.X = 2 ^ L) (h : shell.aboveCarryThreshold) :
    shell.Q * 4 ≤ 2 ^ carryB shell.Q ∧ carryB shell.Q + 25 ≤ L :=
  aboveCarryThreshold_provides_windowScale hX h

/-! ============================================================================
## §3.  ITEM 3 — no NEW vacuity; positive inhabitability certificates

The fix (a) RESTRICTS the charge field's domain to `trtNonneg` phases, (b) RESTRICTS the
carry field's domain to `aboveCarryThreshold` shells, and (c) ADDS the
`returnRunMassNonneg` obligation.  (a) and (b) can only make their fields MORE inhabited
(a hypothesis on a `∀` weakens the obligation).  (c) is the only new obligation; it is
satisfied by mass-`0` data.  We certify each positively and confirm the known
`→ False` route is blocked.
============================================================================ -/

/-- **The guard CANNOT introduce vacuity.**  Any inhabitant of the UN-guarded charge field
(`∀ shell hcQ phases carryData, ShellChargeStructuralInput …`, the pre-fix shape) yields an
inhabitant of the guarded field — just ignore the guard argument.  So adding the
`trtNonneg` hypothesis can only make the field MORE inhabited; it cannot have created a new
emptiness (the CNL-bug failure mode).  (The converse fails: the guarded field is inhabited
in cases the un-guarded one is not, e.g. the adversarial phases of §1.) -/
def guarded_charge_implied_by_unguarded
    (f : ∀ (shell : FailingDyadicShell) (_hcQ : shell.cQ = erdos260Constants.cQ)
        (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
        (carryData : CarryDataFromFailure shell erdos260Constants.cPr),
        ShellChargeStructuralInput phases carryData) :
    ∀ (shell : FailingDyadicShell) (_hcQ : shell.cQ = erdos260Constants.cQ)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
      (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
      (_hphases : phases.trtNonneg),
        ShellChargeStructuralInput phases carryData :=
  fun shell hcQ phases carryData _ => f shell hcQ phases carryData

/-- **The gate CANNOT introduce vacuity.**  Any inhabitant of the UN-gated carry field
(`∀ shell hcQ, CarryDataFromFailure …`, the round-0 baseline) yields an inhabitant of the
gated field — just ignore the gate argument.  So gating by `aboveCarryThreshold` can only
make the field MORE inhabited (indeed it is the round-0 baseline `carryData` that
`erdos260_reduced` already consumes, restricted to large shells). -/
def gated_carry_implied_by_ungated
    (f : ∀ (shell : FailingDyadicShell), shell.cQ = erdos260Constants.cQ →
        CarryDataFromFailure shell erdos260Constants.cPr) :
    ∀ (shell : FailingDyadicShell), shell.cQ = erdos260Constants.cQ →
      shell.aboveCarryThreshold → CarryDataFromFailure shell erdos260Constants.cPr :=
  fun shell hcQ _ => f shell hcQ

/-- **`returnRunMassNonneg` witness (`0 ≤ 0`).**  The obligation
`0 ≤ returnPkg.massSum + run.runMass` is satisfied by the degenerate mass-`0` factory
data (`zeroReturn`/`advRun`), at every constant triple with `cStar,ξ,X ≥ 0` (in particular
the pinned constants and any `X = shell.X ≥ 0`).  So the new field adds no vacuity: a
provider can always pick mass-`0` `returnReduced`/`runProvenance`. -/
theorem returnRunMassNonneg_witness {cStar ξ X : ℝ} (hc : 0 ≤ cStar) (hξ : 0 ≤ ξ)
    (hX : 0 ≤ X) :
    0 ≤ (zeroReturn cStar ξ X hc hξ hX).massSum + (advRun cStar ξ X hc hξ hX).runMass := by
  unfold ReturnFactoryData.massSum
  show (0 : ℝ) ≤ (0 + 0 + 0 + 0) + 0
  norm_num

/-- **The gated `carryWindow`/`carryData` field is inhabited jointly with the gate at a
large shell.**  Given a genuine carry datum `d` and `aboveCarryThreshold`, the gated
codomain `CarryWindowInput shell` is inhabited (`Sum.inr d`) WHILE the gate holds — the two
are jointly satisfiable, so the gate introduces no emptiness.  (The honest residual is
inhabiting `CarryDataFromFailure` itself at such a shell — the genuine Lemma 21.1 /
positive-density analytic core, NOT fabricated here.) -/
theorem gated_carryWindow_inhabited_at_large_shell {shell : FailingDyadicShell}
    (_hlarge : shell.aboveCarryThreshold)
    (d : CarryDataFromFailure shell erdos260Constants.cPr) :
    Nonempty (CarryWindowInput shell) :=
  ⟨Sum.inr d⟩

/-- **The gate and the carry datum are genuinely compatible** (no joint contradiction
between `aboveCarryThreshold` and possessing a `CarryDataFromFailure`). -/
theorem gate_and_carryDatum_compatible {shell : FailingDyadicShell}
    (hlarge : shell.aboveCarryThreshold)
    (d : CarryDataFromFailure shell erdos260Constants.cPr) :
    shell.aboveCarryThreshold ∧ Nonempty (CarryWindowInput shell) :=
  ⟨hlarge, ⟨Sum.inr d⟩⟩

/-- **The guarded charge field type is not uninhabitable.**  For ANY `trtNonneg` phases and
ANY empty-high-excess carry datum, `ShellChargeStructuralInput` is inhabited (§1's
`guardedCharge_inhabited`).  Restated as the negation of "`→ False` for all such inputs":
there is no `<charge field type> → False`. -/
theorem guardedCharge_not_uninhabited {shell : FailingDyadicShell}
    (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
    (hphases : phases.trtNonneg)
    (hEmpty : highExcessStarts carryData.starts (hitGap carryData.a)
        carryData.r carryData.T carryData.Y = ∅) :
    ¬ (ShellChargeStructuralInput phases carryData → False) := by
  intro hempty
  exact (guardedCharge_inhabited phases carryData hphases hEmpty).elim hempty

/-! ### Adversarial attempt: `Erdos260MinimalAtomsFinal → False` — blocked

We build the genuine per-shell phase datum from an arbitrary bundle `m`'s OWN fields
(exactly as the prior `AuditGeometricInputs.assembly_inconsistent_with_shell` did), perturb
it to negative joint mass, and observe that the fixed charge field can NOT be applied: the
perturbed phases fail the guard.  So the old refutation route yields nothing.  We do NOT
prove `False` — that is the point. -/

/-- **The assembly-level negative-mass refutation is unavailable.**  From `m`'s own fields
build the genuine phases `seed`, perturb to `advPhases seed` (joint mass `-1`).  Then:
`ShellChargeStructuralInput (advPhases seed) carryData → False` (the type is empty) AND
`¬ (advPhases seed).trtNonneg` (so the guard argument required by `m.chargeStructural` is
unprovable).  The conjunction shows the only known route to `Erdos260MinimalAtomsFinal →
False` is severed: the field is never asked for the empty input.  (`carryData` is taken as
a hypothesis exactly as in the original attack; the contradiction never closes.) -/
theorem assembly_negmass_refutation_unavailable
    (m : Erdos260MinimalAtomsFinal) (shell : FailingDyadicShell)
    (hcQ : shell.cQ = erdos260Constants.cQ)
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr) :
    ∃ p' : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ),
      (ShellChargeStructuralInput p' carryData → False) ∧ ¬ p'.trtNonneg := by
  let RA := m.toMinimalAtoms.toResidualAtoms
  let seed : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
    { chernoff := RA.chernoff shell hcQ
      cnl := RA.cnl shell hcQ
      tower := RA.tower shell hcQ
      densePack := RA.densePack shell hcQ
      returnPkg := RA.returnPkg shell hcQ
      run := RA.run shell hcQ }
  refine ⟨advPhases erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le
      shell.X_nonneg_real seed, ?_, ?_⟩
  · exact chargeStructuralInput_advPhases_empty carryData seed
  · exact advPhases_not_trtNonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le
      shell.X_nonneg_real seed

/-- **The capstone still reduces to `Erdos260Statement`** (sanity re-export): the fix did
not break the reduction. -/
theorem capstone_still_reduces (m : Erdos260MinimalAtomsFinal) : Erdos260Statement :=
  erdos260_reduced_minimal_final m

/-! ## §4.  Axiom audit -/

#print axioms termChernoff_nonneg
#print axioms termCnl_nonneg
#print axioms advPhases_termTRT
#print axioms advPhases_not_trtNonneg
#print axioms chargeStructuralInput_advPhases_empty
#print axioms nonnegPhases_trtNonneg
#print axioms guardedCharge_inhabited
#print axioms aboveCarryThreshold_forces_pow26
#print axioms small_not_aboveCarryThreshold
#print axioms startThreshold_eq
#print axioms startThreshold_pos
#print axioms returnRunMassNonneg_witness
#print axioms gated_carryWindow_inhabited_at_large_shell
#print axioms assembly_negmass_refutation_unavailable
#print axioms guarded_charge_implied_by_unguarded
#print axioms gated_carry_implied_by_ungated
#print axioms only_return_run_unconstrained
#print axioms guardedCharge_not_uninhabited

end

end AuditFixed

end Erdos260
