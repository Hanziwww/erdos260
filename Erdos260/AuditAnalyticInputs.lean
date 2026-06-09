import Mathlib
import Erdos260.UnconditionalAssemblyFinal
import Erdos260.ChargeBridgeContradiction

/-!
# ADVERSARIAL AUDIT of four `Erdos260MinimalAtomsFinal` input fields

This is a **scratch audit file**.  It edits nothing upstream and is not imported by
the root.  It machine-checks probe lemmas about four of the eight per-shell input
fields of `Erdos260MinimalAtomsFinal` (the hypothesis bundle of the capstone
`erdos260_reduced_minimal_final : Erdos260MinimalAtomsFinal → Erdos260Statement`):

1. `carryWindow` : `ShellWindowInputs shell`            (pressure floor, Lemma 21.1)
2. `chernoffCalib` : `ChernoffCalibrationInput shell`   (H.4 calibration `m ≤ c₁Y`)
3. `cnlCoord` : `CNLCoordinatizedShellInput cStar ξ X`  (L.1.2 coordinatization)
4. `densePackRegime` : `DensePackRegimeInput shell`     (K.1.2–K.1.5 regime)

For each field we probe **vacuity** (is it inhabitable at *realistic* parameters?),
**over-strength/circularity** (does it bake in the bridge / the `cPr·X ≤ budget`
contradiction?), and **faithfulness**.

No `sorry`/`admit`/`native_decide`/new `axiom`.  All probes are kernel-checked.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ============================================================================
## CENTRAL OVER-STRENGTH LEMMA (applies to all three phase-budget inputs)

The pinned constants satisfy `cStar·ξ < cPr` (`Erdos260Constants.constantsCompatible`).
Hence the *entire* per-phase budget `cStar·ξ·X` (the sum of the six manuscript phase
slices, each `≤ cStar·ξ·X/6`) is **strictly below** the pressure floor `cPr·X`.

Consequence: NO phase-budget input (Chernoff / CNL / DensePack), each contributing
`≤ cStar·ξ·X/6`, can possibly entail the contradiction `cPr·X ≤ budget`.  None of
them is "the budget already dominates".  The contradiction can only close through the
genuine routing geometry (the charge bridge), as probed below.
============================================================================ -/

/-- The full phase budget is strictly below the pressure floor (for `X > 0`).  This
is the heart of the non-circularity: a single phase budget `≤ cStar·ξ·X/6` is far
from the conclusion `cPr·X ≤ …`. -/
theorem audit_phaseBudget_strictly_below_floor (X : ℝ) (hX : 0 < X) :
    erdos260Constants.cStar * erdos260Constants.ξ * X < erdos260Constants.cPr * X :=
  mul_lt_mul_of_pos_right erdos260Constants.constantsCompatible hX

/-- **Non-circularity, made explicit.**  The pressure floor (carryWindow), a phase
budget (chernoff/cnl/densePack) and the old-residual smallness are *jointly
satisfiable while the charge bridge `highExcess ≤ phaseMass + oldRes` FAILS* — so the
contradiction does NOT follow from these inputs without the genuine routing bridge.
Witness: `X=1`, `highExcess = cPr`, `phaseMass = oldRes = 0`. -/
theorem audit_inputs_do_not_imply_contradiction_without_bridge :
    ∃ X highExcess phaseMass oldRes : ℝ, 0 < X ∧
      erdos260Constants.cPr * X ≤ highExcess ∧
      phaseMass ≤ erdos260Constants.cStar * erdos260Constants.ξ * X ∧
      oldRes ≤ erdos260Constants.cQ * (1 : ℝ) * X ∧
      ¬ (highExcess ≤ phaseMass + oldRes) := by
  refine ⟨1, erdos260Constants.cPr, 0, 0, one_pos, le_of_eq (by ring), ?_, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
      (by norm_num)
  · exact mul_nonneg (mul_nonneg erdos260Constants.cQ_pos.le (by norm_num)) (by norm_num)
  · simpa using not_le.mpr erdos260Constants.cPr_pos

/-! ============================================================================
## TARGET 1 — `carryWindow` : `ShellWindowInputs shell`  (pressure floor, Lemma 21.1)

`ShellWindowInputs` (in `UnconditionalAssemblyTight2`) bundles `L B : ℕ`,
`hX_eq : X = 2^L`, `hB : Q·4 ≤ 2^B`, `hL : B + 25 ≤ L`,
`hKr : L+1 ≤ (supportShell d X).card`, `h_supportCount_pos`.

KEY FINDING: the `hL` field forces `L ≥ 25`, hence `X ≥ 2^25`.  The type is therefore
UNINHABITABLE for any shell with `X < 2^25`.  There is **no** `Nonempty`/witness for
`ShellWindowInputs` anywhere in the codebase (unlike the other seven fields).
============================================================================ -/

/-- **Scale floor.**  Any `ShellWindowInputs shell` forces `2^25 ≤ shell.X`.  (From
`hL : B + 25 ≤ L` and `hX_eq : X = 2^L`.) -/
theorem audit_carryWindow_forces_scale {shell : FailingDyadicShell}
    (w : ShellWindowInputs shell) : 2 ^ 25 ≤ shell.X := by
  have hL : 25 ≤ w.L := by have h := w.hL; omega
  calc (2 : ℕ) ^ 25 ≤ 2 ^ w.L := Nat.pow_le_pow_right (by norm_num) hL
    _ = shell.X := w.hX_eq.symm

/-- **Richness floor.**  Any `ShellWindowInputs shell` forces at least 26 hits in the
shell `(X,2X]` (`hKr` with `L ≥ 25`). -/
theorem audit_carryWindow_forces_richness {shell : FailingDyadicShell}
    (w : ShellWindowInputs shell) : 26 ≤ (supportShell shell.d shell.X).card := by
  have hL : 25 ≤ w.L := by have h := w.hL; omega
  have hKr := w.hKr
  omega

/-- **Partial vacuity.**  `ShellWindowInputs shell` is UNINHABITABLE for any shell
with `X < 2^25`.  (Direct corollary of the scale floor.) -/
theorem audit_carryWindow_uninhabited_below_scale {shell : FailingDyadicShell}
    (hX : shell.X < 2 ^ 25) (w : ShellWindowInputs shell) : False := by
  have h := audit_carryWindow_forces_scale w
  omega

/-- **Crisp instance.**  No small-scale shell (`X = 2`) admits the carryWindow input.
This is the SAME failure mode as the round-2 CNL bug (`cnlUnconditionalKraftInput
_uninhabited`), restricted to small shells: the field type is empty there. -/
theorem audit_carryWindow_X_eq_two_uninhabited {shell : FailingDyadicShell}
    (hX : shell.X = 2) (w : ShellWindowInputs shell) : False := by
  have h := audit_carryWindow_forces_scale w
  rw [hX] at h; norm_num at h

/-- **Not a *total* (CNL-style) vacuity.**  The scale constraints `hB ∧ hL` are jointly
satisfiable, so the type is empty for small shells only by scale-gating, not by an
internal contradiction.  (Concrete: `Q=1, B=2, L=27`.) -/
theorem audit_carryWindow_scale_constraints_satisfiable :
    ∃ L B : ℕ, (1 : ℕ) * 4 ≤ 2 ^ B ∧ B + 25 ≤ L :=
  ⟨27, 2, by norm_num, by norm_num⟩

/-- **Richness vs. failure are compatible at scale.**  The richness floor `L+1 ≤ K`
and the failing-shell bound `K < c0·2^L` (with `c0 ≤ 1/16`) can hold together — so
`ShellWindowInputs` does NOT contradict the failing-shell hypothesis (it is genuinely
inhabitable in principle for a rich large shell).  (Concrete: `L=25, K=26`.) -/
theorem audit_carryWindow_richness_failure_compatible :
    ∃ L K : ℕ, 25 ≤ L ∧ L + 1 ≤ K ∧ (K : ℝ) < (1 / 16 : ℝ) * 2 ^ L := by
  refine ⟨25, 26, le_refl _, le_refl _, ?_⟩
  norm_num

/-! ### Verdict aid for Target 1
There is NO closed/per-shell witness of `ShellWindowInputs` (a genuine large failing
shell is the irreducible geometry).  The capstone field
`carryWindow : ∀ shell, cQ = … → ShellWindowInputs shell` quantifies over EVERY
`cQ`-shell with no scale guard and no fallback — contrast `densePackRegime`, which is
total via an explicit fallback (Target 4).  If any `cQ`-shell with `X < 2^25` exists
(the `FailingDyadicShell` definition imposes no scale floor), the field — and hence the
whole hypothesis bundle — is uninhabitable. -/

/-! ============================================================================
## TARGET 2 — `chernoffCalib` : `ChernoffCalibrationInput shell`  (H.4 `m ≤ c₁Y`)

The single field of interest is
`calibration : (1)·(1·regularTiltSum Csh G z)^m ≤ (cStar·ξ·X/6)·z^Y`.
============================================================================ -/

/-- **TOTAL non-vacuity (every shell, removing the existing `64 ≤ X` restriction).**
With `m = 0` the calibration LHS is `1`, satisfied by any `X ≥ 1` via `z=2, Y=6`.  So
`ChernoffCalibrationInput shell` is inhabited for EVERY failing shell. -/
def audit_chernoffCalib_witness (shell : FailingDyadicShell) :
    ChernoffCalibrationInput shell where
  Q := 0
  Csh := 0
  G := 1
  m := 0
  Y := 6
  z := 2
  z_ge_one := by norm_num
  calibration := by
    have hX : (1 : ℝ) ≤ (shell.X : ℝ) := by exact_mod_cast shell.X_pos
    have hcs : erdos260Constants.cStar = 31 / 16 := rfl
    have hxi : erdos260Constants.ξ = 1 / 16 := rfl
    rw [pow_zero, mul_one, hcs, hxi]
    nlinarith [hX]

theorem audit_chernoffCalib_inhabited_all (shell : FailingDyadicShell) :
    Nonempty (ChernoffCalibrationInput shell) :=
  ⟨audit_chernoffCalib_witness shell⟩

/-- The existing large-shell witness uses a *genuine* nonzero block length `m = 2`
(non-degenerate Chernoff geometry) — confirming the non-vacuity at `64 ≤ X` is on
realistic, non-trivializing parameters. -/
theorem audit_chernoffCalib_large_witness_block_genuine
    (shell : FailingDyadicShell) (hX : 64 ≤ shell.X) :
    (chernoffCalibrationInputOfLargeShell shell hX).m = 2 := rfl

/-- **FAITHFULNESS note (machine-checked).**  My total witness uses `m = 0`, which
trivializes the Chernoff block (empty path).  So the Lean field is *weaker* than the
manuscript's genuine `m ≤ c₁Y` (it does not force a real Chernoff estimate).  This is
logically SAFE (a weaker hypothesis makes the conditional stronger), but it means the
non-vacuity for small shells rides on a degenerate block. -/
theorem audit_chernoffCalib_total_witness_block_degenerate (shell : FailingDyadicShell) :
    (audit_chernoffCalib_witness shell).m = 0 := rfl

/-- **Over-strength check.**  The Chernoff input is satisfiable *simultaneously* with
the genuine non-degenerate constant regime `cStar·ξ < cPr` in which the shell is
actually refuted — so the input is not "the budget already dominates". -/
theorem audit_chernoffCalib_consistent_with_genuine_regime (shell : FailingDyadicShell) :
    Nonempty (ChernoffCalibrationInput shell) ∧
      erdos260Constants.cStar * erdos260Constants.ξ < erdos260Constants.cPr :=
  ⟨⟨audit_chernoffCalib_witness shell⟩, erdos260Constants.constantsCompatible⟩

/-! ============================================================================
## TARGET 3 — `cnlCoord` : `CNLCoordinatizedShellInput cStar ξ X`  (L.1.2)

The capstone field is `cnlCoord : ∀ shell, cQ = … →
  CNLCoordinatizedShellInput erdos260Constants.cStar erdos260Constants.ξ shell.X`.

The EXISTING certificate `cnlCoordinatizedShellInput_inhabited` is at parameters
`(1,1,1)` with an EMPTY cluster — i.e. at parameters that do NOT match the capstone
usage (pinned `cStar = 31/16, ξ = 1/16`, `X = shell.X`).  We rebuild the witness at the
genuine pinned constants and real `X`, AND with a genuinely NON-EMPTY selected cluster.
============================================================================ -/

/-- A concrete selected CNL transition (normal form `positiveLift`, available class
`{pkg}`); its canonical selector fires, so it survives `selectedTransitions`. -/
def audit_cnlTransition : CNLTransition where
  normalForm := CNLNormalForm.positiveLift
  available := {CNLClass.pkg}

theorem audit_cnlTransition_isSome :
    (canonicalCNLSelector audit_cnlTransition).isSome = true := by
  simp [canonicalCNLSelector, audit_cnlTransition, selectCNLClass?]

/-- **Non-degenerate, pinned-constant CNL witness.**  At the genuine pinned constants
`(erdos260Constants.cStar, erdos260Constants.ξ)`, any `X ≥ 0`, a NON-EMPTY selected
cluster `{audit_cnlTransition}`, positive shell factor `1/1000`, positive `Ij = 1`.  The
budget `2·(1/1000)·X·1 ≤ cStar·ξ·X/6` holds for all `X ≥ 0` since `1/500 < 31/1536`. -/
def audit_cnlCoord_witness_pinned (X : ℝ) (hX : 0 ≤ X) :
    CNLCoordinatizedShellInput erdos260Constants.cStar erdos260Constants.ξ X :=
  CNLCoordinatizedShellInput.ofReplicatedInjectiveLabel
    {audit_cnlTransition} (fun _ => 0) 1 2
    (by norm_num)
    (cnl_cq_dominates_of_c_ge_one (by norm_num) (by norm_num))
    0 (fun _ => 0)
    (by
      intro t₁ ht₁ t₂ ht₂ _
      simp only [selectedTransitions, Finset.mem_filter, Finset.mem_singleton] at ht₁ ht₂
      rw [ht₁.1, ht₂.1])
    (by
      intro t ht
      simp only [selectedTransitions, Finset.mem_filter, Finset.mem_singleton] at ht
      simp)
    (1 / 1000) 1 (by norm_num) (by norm_num)
    (by
      have hcs : erdos260Constants.cStar = 31 / 16 := rfl
      have hxi : erdos260Constants.ξ = 1 / 16 := rfl
      have hpow : (2 : ℝ) ^ (0 + 1) = 2 := by norm_num
      rw [hcs, hxi, hpow]
      nlinarith [hX])

/-- **CNL non-vacuity at the EXACT capstone parameters** (pinned constants, `X =
shell.X`), unlike the existing `(1,1,1)` certificate. -/
theorem audit_cnlCoord_inhabited_pinned (shell : FailingDyadicShell) :
    Nonempty (CNLCoordinatizedShellInput erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : ℝ)) :=
  ⟨audit_cnlCoord_witness_pinned (shell.X : ℝ) shell.X_nonneg_real⟩

/-- The pinned witness has a genuinely NON-EMPTY selected cluster (a strict
improvement over the empty-cluster `(1,1,1)` certificate). -/
theorem audit_cnlCoord_witness_pinned_cluster_nonempty (X : ℝ) (hX : 0 ≤ X) :
    (selectedTransitions (audit_cnlCoord_witness_pinned X hX).T).Nonempty := by
  refine ⟨audit_cnlTransition, ?_⟩
  simp only [audit_cnlCoord_witness_pinned, CNLCoordinatizedShellInput.ofReplicatedInjectiveLabel,
    selectedTransitions, Finset.mem_filter, Finset.mem_singleton]
  refine ⟨?_, audit_cnlTransition_isSome⟩
  trivial

/-- The pinned witness has a genuinely POSITIVE shell factor (`1/1000`), not the
degenerate `0` — so its budget slice is non-trivial. -/
theorem audit_cnlCoord_witness_pinned_shellFactor_pos (X : ℝ) (hX : 0 ≤ X) :
    0 < (audit_cnlCoord_witness_pinned X hX).shellFactor := by
  show (0 : ℝ) < 1 / 1000
  norm_num

/-- **Documenting the existing certificate's degenerate parameters**: its cluster is
EMPTY (so its `selectedTransitions` is empty).  This is why the `(1,1,1)` non-vacuity is
*misleading* for the capstone usage. -/
theorem audit_cnlCoord_existing_witness_cluster_empty :
    cnlCoordinatizedShellInput_witness.T = (∅ : Finset CNLTransition) := rfl

/-! ============================================================================
## TARGET 4 — `densePackRegime` : `DensePackRegimeInput shell`  (K.1.2–K.1.5)

`DensePackRegimeInput shell := PLift (c0 ≤ κ/16 ∧ carryB Q + 25 ≤ L) ⊕
  DensePackFactoryData cStar ξ X`.  It is TOTAL: the right (fallback) summand is always
inhabited (empty datum).  The left (in-regime) summand is scale-gated like carryWindow,
but optional.
============================================================================ -/

/-- The always-available fallback datum (empty point set). -/
def audit_densePackRegime_fallback (shell : FailingDyadicShell) :
    DensePackRegimeInput shell :=
  Sum.inr (densePackFactoryData_trivial
    (div_nonneg
      (mul_nonneg (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
        shell.X_nonneg_real)
      (by norm_num)))

/-- **TOTAL non-vacuity.**  `DensePackRegimeInput shell` is inhabited for EVERY shell
(via the fallback) — the right design that carryWindow lacks. -/
theorem audit_densePackRegime_inhabited (shell : FailingDyadicShell) :
    Nonempty (DensePackRegimeInput shell) :=
  ⟨audit_densePackRegime_fallback shell⟩

/-- **FAITHFULNESS note.**  The fallback build is an EMPTY DensePack datum (0 mass).
So the totality of the type rides on a degenerate datum that under-claims the DensePack
phase.  Logically SAFE (under-claiming a phase shifts burden to the bridge, never bakes
the conclusion). -/
theorem audit_densePackRegime_fallback_build_empty (shell : FailingDyadicShell) :
    (audit_densePackRegime_fallback shell).build.densePackPoints = (∅ : Finset _) := rfl

/-- **Over-strength / scale-gating of the in-regime branch.**  The left summand's
conditions force `X ≥ 2^25` (large scale), exactly like carryWindow — but here it is
OPTIONAL (the fallback keeps the type inhabited).  This is the structural contrast that
makes DensePack sound where carryWindow is concerning. -/
theorem audit_densePack_inRegime_forces_scale {shell : FailingDyadicShell}
    (h : shell.c0 ≤ manuscriptKappa / 16 ∧
        carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic) :
    2 ^ 25 ≤ shell.X := by
  have hspec := Classical.choose_spec shell.hXdyadic
  have hL : 25 ≤ Classical.choose shell.hXdyadic := by have := h.2; omega
  calc (2 : ℕ) ^ 25 ≤ 2 ^ Classical.choose shell.hXdyadic :=
        Nat.pow_le_pow_right (by norm_num) hL
    _ = shell.X := hspec.symm

/-! ============================================================================
## EMBEDDED VERDICTS (machine-checked to be present)
============================================================================ -/

/-- Per-target audit verdicts (compiled record). -/
def auditAnalyticInputsVerdicts : List String :=
  [ "carryWindow (ShellWindowInputs): FAITHFULNESS-CONCERN / potential VACUITY. " ++
      "Forces X ≥ 2^25 (audit_carryWindow_forces_scale); uninhabitable for X < 2^25 " ++
      "(audit_carryWindow_uninhabited_below_scale); NO witness exists; the capstone " ++
      "field quantifies over all cQ-shells with no scale guard and no fallback.",
    "chernoffCalib (ChernoffCalibrationInput): SOUND. Inhabited for EVERY shell " ++
      "(audit_chernoffCalib_inhabited_all); large-shell witness uses genuine m=2; not " ++
      "over-strong (audit_phaseBudget_strictly_below_floor). Faithfulness aside: m=0 " ++
      "trivializes the block (audit_chernoffCalib_total_witness_block_degenerate).",
    "cnlCoord (CNLCoordinatizedShellInput): SOUND (existing certificate misleading). " ++
      "Inhabited at the EXACT pinned constants & real X with a NON-EMPTY cluster " ++
      "(audit_cnlCoord_inhabited_pinned, audit_cnlCoord_witness_pinned_cluster_nonempty); " ++
      "existing (1,1,1) witness uses an empty cluster.",
    "densePackRegime (DensePackRegimeInput): SOUND. TOTAL via fallback " ++
      "(audit_densePackRegime_inhabited); in-regime branch scale-gated but optional " ++
      "(audit_densePack_inRegime_forces_scale); fallback empty datum is honest." ]

theorem auditAnalyticInputsVerdicts_nonempty : auditAnalyticInputsVerdicts ≠ [] := by
  simp [auditAnalyticInputsVerdicts]

end

end Erdos260
