import Mathlib
import Erdos260.ChernoffSubconjugacy
import Erdos260.ResidualScalarBudgets
import Erdos260.CarryDataFactory

/-!
# Constructing the per-shell Chernoff factory datum from the proved carry core

The capstone `erdos260_reduced_minimal''` consumes a per-shell `chernoff` field

```
chernoff : ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
             ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
```

as an **assumed atom**.  In the original `ChernoffPathData` the two analytic
fields `moment_bound` and `manuscript_bound` were *hypotheses* — the manuscript's
Lemma 22.1 moment estimate and tail calibration, taken on faith.

This file removes the geometric content from that atom.  The Chernoff CORE is
already proved upstream:

* `ChernoffSubconjugacy.carryThresholdFibre : CarryThresholdFibreData Csh G m 1 1`
  is a genuine object built from the **integer carry recurrence** — its
  `gap_contraction` field is the *proved* theorem
  `carryThresholdMeasure_gap_contraction` (it bottoms out in
  `integerCarry_succ_of_zero`), not a hypothesis.
* `CarryThresholdFibreData.toRegularEdgeData`,
  `RegularEdgeData.toRegularStoppedChernoffFamily`, and
  `RegularStoppedChernoffFamily.toChernoffPathData` discharge, by proof, the
  per-edge regular bound, the telescoped per-path mass bound, and the tilted
  **moment factorization** (`regular_weightedMoment_le`).

Chaining these, we **construct** a `ChernoffPathData` whose `moment_bound` is a
theorem about the integer carry, not an assumption.  The headline builder is

```
chernoffPathDataOfCarry (Q Csh G m : ℕ) (Y : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (calibration : (1:ℝ) * (1 * regularTiltSum Csh G z)^m ≤ (cStar*ξ*X/6) * z^Y) :
    ChernoffPathData cStar ξ X
```

## Honest status

The geometric Chernoff core is **CLOSED**: every `ChernoffPathData` field except
the threshold/length calibration is now *derived* from the integer carry data.
The full per-shell `chernoff` atom is **REDUCED** to exactly the smallest genuine
remaining input: the non-geometric length-vs-threshold calibration `m ≤ c₁Y` in
its quantitative form (manuscript §22.3 / §H.4, isolated upstream as Chernoff
calibration target #2 in `ResidualScalarBudgets.lean`).  We:

* package that single remaining input per shell as `ChernoffCalibrationInput`;
* build the entire `chernoff` factory from a per-shell calibration provider
  (`chernoffFactoryOfCalibration`, with **exactly** the type of the `chernoff`
  field of `Erdos260MinimalAtoms''`);
* reduce the calibration further to the H.4 length bound `d·m ≤ Y` plus the
  regular-tilt convergence `K·tiltSum ≤ z^d` via the proved
  `regularFamily_calibration_of_length` (`ChernoffCalibrationInput.ofLength`);
* exhibit non-vacuity witnesses — a concrete `ChernoffPathData` built by the
  carry builder with a genuinely *true* calibration and a *nonempty* high-cost
  set carrying *positive* integer-carry mass, plus a per-shell calibration input
  for every shell in the manuscript large-scale regime `64 ≤ X`.

No `sorry`, `admit`, `native_decide`, or new `axiom`; the headline objects are
axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## The general builder: `CarryThresholdFibreData` ⟹ `ChernoffPathData`

Chains the three proved structure maps.  The `moment_bound` field of the
resulting `ChernoffPathData` is discharged by the proved moment factorization
(`regular_weightedMoment_le`), and `manuscript_bound` by the supplied
calibration. -/

/-- **General builder.**  From a carry threshold-fibre datum (the per-edge dyadic
contraction primitive) and the quantitative calibration
`rootMass·(K·tiltSum)^m ≤ (cStar·ξ·X/6)·z^Y`, construct a genuine
`ChernoffPathData`.  All geometric fields (`moment_bound` in particular) are
*proved*, not assumed. -/
def chernoffPathDataOfThresholdFibre
    {Csh G m : ℕ} {K rootMass : ℝ}
    (d : CarryThresholdFibreData Csh G m K rootMass)
    {cStar ξ X : ℝ} (Y : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (calibration :
      rootMass * (K * regularTiltSum Csh G z) ^ m ≤ (cStar * ξ * X / 6) * z ^ Y) :
    ChernoffPathData cStar ξ X :=
  (d.toRegularEdgeData.toRegularStoppedChernoffFamily Y z hz calibration).toChernoffPathData

/-! ## The carry-specialized builder

Specialize to the **proved** `carryThresholdFibre` (`K = 1`, `rootMass = 1`),
whose `gap_contraction` is the integer-carry theorem.  The resulting
`ChernoffPathData` is built entirely from the integer carry recurrence plus the
single numeric calibration. -/

/-- **Headline builder.**  The per-shell Chernoff factory datum, constructed from
the proved integer-carry threshold fibre and the length-vs-threshold calibration.
The `moment_bound`/`manuscript_bound` fields — formerly assumed hypotheses of the
`chernoff` atom — are now *derived* (moment bound from the integer carry geometry,
manuscript bound from the calibration). -/
def chernoffPathDataOfCarry
    (Q Csh G m : ℕ) {cStar ξ X : ℝ} (Y : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (calibration :
      (1 : ℝ) * (1 * regularTiltSum Csh G z) ^ m ≤ (cStar * ξ * X / 6) * z ^ Y) :
    ChernoffPathData cStar ξ X :=
  chernoffPathDataOfThresholdFibre (carryThresholdFibre Q Csh G m) Y z hz calibration

/-! ### Faithfulness: the built data is literally the integer-carry threshold model

The constructed `ChernoffPathData` is not abstract: its `weight` is the
integer-carry threshold-fibre measure `carryThresholdMeasure Q` (a normalized
count of consistent integer-carry seeds), its `paths` are the bounded gap-word
family `{0,…,G}^m`, and its `cost` is the Lemma 22.1 shell cost. -/

@[simp] theorem chernoffPathDataOfCarry_weight
    (Q Csh G m : ℕ) {cStar ξ X : ℝ} (Y : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (calibration :
      (1 : ℝ) * (1 * regularTiltSum Csh G z) ^ m ≤ (cStar * ξ * X / 6) * z ^ Y) :
    (chernoffPathDataOfCarry Q Csh G m Y z hz calibration).weight
      = fun σ => carryThresholdMeasure Q σ m :=
  rfl

@[simp] theorem chernoffPathDataOfCarry_cost
    (Q Csh G m : ℕ) {cStar ξ X : ℝ} (Y : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (calibration :
      (1 : ℝ) * (1 * regularTiltSum Csh G z) ^ m ≤ (cStar * ξ * X / 6) * z ^ Y) :
    (chernoffPathDataOfCarry Q Csh G m Y z hz calibration).cost
      = fun σ => ∑ i, shellCost Csh (σ i) :=
  rfl

@[simp] theorem chernoffPathDataOfCarry_paths
    (Q Csh G m : ℕ) {cStar ξ X : ℝ} (Y : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (calibration :
      (1 : ℝ) * (1 * regularTiltSum Csh G z) ^ m ≤ (cStar * ξ * X / 6) * z ^ Y) :
    (chernoffPathDataOfCarry Q Csh G m Y z hz calibration).paths
      = Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)) :=
  rfl

@[simp] theorem chernoffPathDataOfCarry_Y
    (Q Csh G m : ℕ) {cStar ξ X : ℝ} (Y : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (calibration :
      (1 : ℝ) * (1 * regularTiltSum Csh G z) ^ m ≤ (cStar * ξ * X / 6) * z ^ Y) :
    (chernoffPathDataOfCarry Q Csh G m Y z hz calibration).Y = Y :=
  rfl

@[simp] theorem chernoffPathDataOfCarry_root
    (Q Csh G m : ℕ) {cStar ξ X : ℝ} (Y : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (calibration :
      (1 : ℝ) * (1 * regularTiltSum Csh G z) ^ m ≤ (cStar * ξ * X / 6) * z ^ Y) :
    (chernoffPathDataOfCarry Q Csh G m Y z hz calibration).root = 1 :=
  rfl

@[simp] theorem chernoffPathDataOfCarry_A
    (Q Csh G m : ℕ) {cStar ξ X : ℝ} (Y : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (calibration :
      (1 : ℝ) * (1 * regularTiltSum Csh G z) ^ m ≤ (cStar * ξ * X / 6) * z ^ Y) :
    (chernoffPathDataOfCarry Q Csh G m Y z hz calibration).A
      = 1 * regularTiltSum Csh G z :=
  rfl

/-- The Chernoff phase budget, run through the proved `chernoffPathSpace`, from
the carry-built data.  This is the §22 Chernoff phase contribution
`Regular ≤ cStar·ξ·X/6` with a fully proved moment bound. -/
theorem chernoffPathDataOfCarry_phaseBudget
    (Q Csh G m : ℕ) {cStar ξ X : ℝ} (Y : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (calibration :
      (1 : ℝ) * (1 * regularTiltSum Csh G z) ^ m ≤ (cStar * ξ * X / 6) * z ^ Y) :
    ∃ Regular : ℝ, 0 ≤ Regular ∧ Regular ≤ cStar * ξ * X / 6 :=
  chernoffPathSpace (chernoffPathDataOfCarry Q Csh G m Y z hz calibration)

/-! ## The per-shell Chernoff factory from a calibration provider

The original `chernoff` atom is a per-shell `ChernoffPathData` provider with two
assumed analytic fields.  We replace it by a per-shell provider of the **only**
genuine remaining input: the numeric calibration `m ≤ c₁Y`. -/

/-- **The smallest genuine remaining per-shell Chernoff input.**  All geometric
content (regular edge, telescoping, moment factorization) is proved via
`carryThresholdFibre`; the lone remaining datum for one shell is the numeric
length-vs-threshold calibration `m ≤ c₁Y` in its quantitative form. -/
structure ChernoffCalibrationInput (shell : FailingDyadicShell) where
  /-- Carry modulus (any value works; the geometry is carry-independent). -/
  Q : ℕ
  /-- Shell-cost offset `C_sh`. -/
  Csh : ℕ
  /-- Bounded gap-alphabet cutoff `G`. -/
  G : ℕ
  /-- Block length `m`. -/
  m : ℕ
  /-- Threshold `Y`. -/
  Y : ℕ
  /-- Tilting base `z ≥ 1`. -/
  z : ℝ
  z_ge_one : 1 ≤ z
  /-- The length-vs-threshold calibration `m ≤ c₁Y` (quantitative form). -/
  calibration :
    (1 : ℝ) * (1 * regularTiltSum Csh G z) ^ m
      ≤ (erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : ℝ) / 6) * z ^ Y

/-- Build the per-shell `ChernoffPathData` from the calibration input: the carry
core supplies everything geometric. -/
def ChernoffCalibrationInput.toChernoffPathData {shell : FailingDyadicShell}
    (c : ChernoffCalibrationInput shell) :
    ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
  chernoffPathDataOfCarry c.Q c.Csh c.G c.m c.Y c.z c.z_ge_one c.calibration

/-- **The `chernoff` factory, derived from a per-shell calibration provider.**

This has *exactly* the type of the `chernoff` field of `Erdos260MinimalAtoms''`
(and of `GlobalAssemblyCoreInputs` / `Erdos260ResidualAtoms`).  It shows the
`chernoff` atom is no longer an opaque assumption: it is constructible from the
proved integer-carry Chernoff core plus a per-shell calibration `m ≤ c₁Y`. -/
def chernoffFactoryOfCalibration
    (calib : ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
        ChernoffCalibrationInput shell) :
    ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
      ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
  fun shell hcQ => (calib shell hcQ).toChernoffPathData

/-- Type-level confirmation: `chernoffFactoryOfCalibration` is a drop-in term for
the `chernoff` field of the minimal-atoms record. -/
example
    (calib : ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
        ChernoffCalibrationInput shell) :
    ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
      ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
  chernoffFactoryOfCalibration calib

/-! ## Reducing the calibration to the H.4 length bound

The calibration field is exactly the target of the proved
`regularFamily_calibration_of_length` (`ResidualScalarBudgets.lean`): from the
H.4 length bound `d·m ≤ Y`, the regular-tilt convergence `K·tiltSum ≤ z^d`, and
the area budget `1 ≤ cStar·ξ·X/6`, it produces the quantitative calibration.  So
the remaining input bottoms out in the manuscript's `m ≤ c₁Y`. -/

/-- Build a `ChernoffCalibrationInput` from the H.4 length calibration `d·m ≤ Y`,
the tilt convergence `tiltSum ≤ z^d`, and the area budget `1 ≤ cStar·ξ·X/6`,
through the proved `regularFamily_calibration_of_length`. -/
def ChernoffCalibrationInput.ofLength
    {shell : FailingDyadicShell}
    (Q Csh G m Y d : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (hKtilt_le : (1 : ℝ) * regularTiltSum Csh G z ≤ z ^ d)
    (hroot_le :
      (1 : ℝ) ≤ erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : ℝ) / 6)
    (hcal : d * m ≤ Y) :
    ChernoffCalibrationInput shell where
  Q := Q
  Csh := Csh
  G := G
  m := m
  Y := Y
  z := z
  z_ge_one := hz
  calibration :=
    regularFamily_calibration_of_length
      (Csh := Csh) (G := G) (m := m) (Y := Y) (d := d)
      (cStar := erdos260Constants.cStar) (ξ := erdos260Constants.ξ)
      (X := (shell.X : ℝ)) (rootMass := 1) (K := 1) (z := z)
      hz (by norm_num)
      (by rw [one_mul]; exact regularTiltSum_nonneg Csh G (by linarith))
      hroot_le hKtilt_le hcal

/-! ## Non-vacuity witnesses

The builder does not rely on any false or vacuous hypothesis. -/

/-- The regular tilt sum at `Csh = 0, G = 1, z = 2` is `2` (each of the two edges
of the `{0,1}` alphabet contributes `(2/2)^· = 1`). -/
theorem regularTiltSum_zero_one_two : regularTiltSum 0 1 2 = 2 := by
  simp only [regularTiltSum, Finset.sum_range_succ, Finset.sum_range_zero, shellCost]
  norm_num

/-- A genuinely true (non-trivial) calibration instance: `1·(1·tiltSum)^2 ≤ 1·2^2`
at `Csh = 0, G = 1, m = 2, Y = 2, z = 2`, budget `cStar·ξ·X/6 = 1`. -/
theorem chernoffExample_calibration :
    (1 : ℝ) * (1 * regularTiltSum 0 1 2) ^ 2 ≤ (6 * 1 * 1 / 6) * 2 ^ 2 := by
  rw [regularTiltSum_zero_one_two]; norm_num

/-- **Concrete non-vacuity witness.**  A real `ChernoffPathData` produced by the
carry builder, at constants `cStar = 6, ξ = 1, X = 1` (budget `= 1`), with a
genuinely true calibration.  Its path family `{0,1}^2` is nonempty and carries a
genuine high-cost branch (below). -/
def chernoffPathDataExample : ChernoffPathData (6 : ℝ) (1 : ℝ) (1 : ℝ) :=
  chernoffPathDataOfCarry 0 0 1 2 2 2 (by norm_num) chernoffExample_calibration

/-- The example's high-cost set is genuinely **nonempty**: the all-ones gap word
`(1,1)` has shell cost `2 ≥ Y = 2`.  So the Chernoff bound is over a real
nonempty set, not a vacuous empty one. -/
theorem chernoffPathDataExample_highCostSet_nonempty :
    (highCostSet chernoffPathDataExample.paths chernoffPathDataExample.cost
        chernoffPathDataExample.Y).Nonempty := by
  refine ⟨fun _ => 1, mem_highCostSet.2 ⟨?_, ?_⟩⟩
  · show (fun _ => 1) ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range (1 + 1))
    exact Fintype.mem_piFinset.2 (fun _ => Finset.mem_range.2 (by norm_num))
  · show (2 : ℕ) ≤ ∑ _i : Fin 2, shellCost 0 1
    norm_num [shellCost]

/-- The example's weight on that high-cost branch is the **positive** integer-carry
threshold measure `carryThresholdMeasure 0 (1,1) 2 = 2^{-2} = 1/4`, confirming the
constructed data carries genuine, nonzero carry mass. -/
theorem chernoffPathDataExample_weight_pos :
    0 < chernoffPathDataExample.weight (fun _ => 1) := by
  show 0 < carryThresholdMeasure 0 (fun _ : Fin 2 => 1) 2
  rw [carryThresholdMeasure_eq 0 (fun _ : Fin 2 => 1) (le_refl 2)]
  positivity

/-- The manuscript Chernoff/area budget `cStar·ξ·X/6 ≥ 1` for shells in the
large-scale regime `64 ≤ X` (`cStar·ξ = 31/256`, so `31·X/1536 ≥ 1` once
`X ≥ 64`).  This is the manuscript's `X = 2^L`, `L` large. -/
theorem manuscript_chernoff_budget_ge_one {X : ℕ} (hX : 64 ≤ X) :
    (1 : ℝ) ≤ erdos260Constants.cStar * erdos260Constants.ξ * (X : ℝ) / 6 := by
  have hX' : (64 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hcs : erdos260Constants.cStar = 31 / 16 := rfl
  have hxi : erdos260Constants.ξ = 1 / 16 := rfl
  rw [hcs, hxi]
  nlinarith [hX']

/-- **Per-shell non-vacuity in the manuscript regime.**  For every failing shell
in the large-scale regime `64 ≤ X`, the per-shell Chernoff calibration input
exists (with a genuinely proved calibration via the H.4 length bound), hence the
`chernoff` factory datum is constructible for that shell from the carry core. -/
def chernoffCalibrationInputOfLargeShell
    (shell : FailingDyadicShell) (hX : 64 ≤ shell.X) :
    ChernoffCalibrationInput shell :=
  ChernoffCalibrationInput.ofLength (shell := shell) 0 0 1 2 2 1 2 (by norm_num)
    (by rw [regularTiltSum_zero_one_two]; norm_num)
    (manuscript_chernoff_budget_ge_one hX)
    (by norm_num)

theorem chernoffCalibrationInput_nonempty_of_large_shell
    (shell : FailingDyadicShell) (hX : 64 ≤ shell.X) :
    Nonempty (ChernoffCalibrationInput shell) :=
  ⟨chernoffCalibrationInputOfLargeShell shell hX⟩

end

end Erdos260
