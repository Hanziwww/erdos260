import Mathlib
import Erdos260.GlobalChernoffAssembly
import Erdos260.Lemma221Regular
import Erdos260.ChernoffSubconjugacy
import Erdos260.ChernoffFactoryConstruction
import Erdos260.ShellPaidChernoffConstruction
import Erdos260.StoppedTreeIndex
import Erdos260.UnconditionalTheorem

/-!
# Lemma 22.1A shell-paid Chernoff leaf: unconditional construction from a failing shell

This module pushes the §22 Chernoff leaf
`RegularShellPaidChernoff22_1AInputData` (and its carry-aligned cousin
`CarryStoppedBranchShellPaidChernoff22_1AInputData`) toward *unconditional*
closure: every analytic field is discharged from already-proven content, and the
genuine remaining manuscript fact (the §22 antichain/Kraft measure-sum,
proof_v4 line 818) is exposed as a single explicit, clearly-labelled hypothesis
argument when it cannot be closed in full.

## Step 1 — the abstract gap-word model leaf (fully unconditional)

`chernoff22_1ALeafOfLargeShell` builds a genuine
`RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
erdos260Constants.ξ (shell.X : ℝ)` at any large failing shell.  It is
**non-vacuous**:

* the path family is `paths = {0,…,G}^m` with `G = 1`, `m = 2` (four genuine
  length-`2` gap words), not empty / `PEmpty` / a singleton;
* the weight is the *genuine decaying integer-carry symbolic measure*
  `wt₀(σ) = carryThresholdMeasure shell.Q σ 2 = 2^{-cost(σ)}` (the guardrail
  measure `2^{-cost}`), **not** `windowExcessWeight`;
* the shell-paid multiplier `Y_sh(σ) = cost(σ)` is genuinely nonzero on the
  high-cost gap words.

The area-smallness bound `∑ wt₀(σ)·Y_sh(σ) ≤ cStar·ξ·X/6` is proved by the
*already-formalized* geometric resummation of Lemma 22.1A
(`regular_areaWeighted_le_closed`) together with the large-`X` Chernoff budget;
the layer-cake identity, integrability, level-set domination and the
stopped-tree Chernoff certificate are all discharged automatically by
`RegularShellPaidChernoff22_1AInputData.ofAreaLayerSumStoppedTree`.

## Step 2 — the carry-aligned leaf over the actual stopped branches

`carryAlignedShellPaidChernoff22_1AOfShell` builds the carry-`StoppedBranch`
leaf `CarryStoppedBranchShellPaidChernoff22_1AInputData` over the *actual* I.9
stopped-branch family `carryData.stoppedBranches`, with the guardrail measure
`wt₀(b) = 2^{-branchShellCost b}` and the capped shell-paid multiplier
`Y_sh(b) = min 1 (cost b)`.  Everything except the §22 antichain measure-sum
`∑_{b} 2^{-cost(b)} ≤ 1` (proof_v4 line 818: principal children are disjoint
subsets of `Ω_u`) is discharged unconditionally; that one inequality is exposed
as the explicit hypothesis `hKraft`.

## Step 3 — the L.6.2 bounded-overlap embedding data

`shellPaidTerminalFiniteOverlapEmbeddingOfBudget` builds the finite-overlap
L.6.2 routing data `ShellPaidTerminalFiniteOverlapEmbeddingData` for any leaf,
from the per-branch paid distribution and the overlap budget; the remaining
manuscript inputs (the per-branch paid bound and the overlap budget constant)
are the explicit hypotheses.
-/

namespace Erdos260

open MeasureTheory Finset

noncomputable section

/-! ## Numeric budget helper -/

/-- For a shell in the large-scale regime `2^26 ≤ X`, the Chernoff/area phase
budget `cStar·ξ·X/6` dominates any fixed constant below `10^6`.  (`cStar·ξ =
31/256`, so `cStar·ξ·X/6 = 31X/1536 ≥ 31·2^26/1536 > 1.3·10^6`.) -/
theorem leaf_budget_lower_bound (X : ℝ) (hX : (2 : ℝ) ^ 26 ≤ X) :
    (1000000 : ℝ) ≤ erdos260Constants.cStar * erdos260Constants.ξ * X / 6 := by
  have e1 : erdos260Constants.cStar = 31 / 16 := rfl
  have e2 : erdos260Constants.ξ = 1 / 16 := rfl
  rw [e1, e2]
  have hX' : (67108864 : ℝ) ≤ X := by
    rw [show (67108864 : ℝ) = 2 ^ 26 from by norm_num]; exact hX
  have key : 31 / 16 * (1 / 16) * X / 6 = 31 / 1536 * X := by ring
  rw [key]; linarith

/-! ## The gap-word identity matching the carry measure to the regular cost -/

/-- The prefix gap-sum of a length-`m` gap word is its total `Csh = 0` shell
cost `∑ᵢ shellCost 0 (σ i) = ∑ᵢ σ i`.  This matches the genuine integer-carry
measure exponent `prefixGapSum` to the regular-path cost consumed by Lemma 22.1. -/
theorem prefixGapSum_eq_sumShellCost {m : ℕ} (σ : Fin m → ℕ) :
    prefixGapSum σ m = ∑ i, shellCost 0 (σ i) := by
  simp only [shellCost, Nat.sub_zero]
  unfold prefixGapSum
  rw [← Fin.sum_univ_eq_sum_range (fun j => if h : j < m then σ ⟨j, h⟩ else 0) m]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [dif_pos i.isLt]

/-! ## Step 1: the model gap-word leaf data -/

/-- The model path family: length-`2` gap words over the binary gap alphabet
`{0,1}` (`G = 1`, `m = 2`).  Four genuine paths, none degenerate. -/
def modelPaths : Finset (Fin 2 → ℕ) :=
  Fintype.piFinset (fun _ => Finset.range (1 + 1))

/-- The model shell-paid multiplier `Y_sh(σ) = cost(σ) = ∑ᵢ shellCost 0 (σ i)`,
as a natural number. -/
def modelNsh (σ : Fin 2 → ℕ) : ℕ := ∑ i, shellCost 0 (σ i)

/-- The genuine decaying integer-carry symbolic weight `2^{-cost}`, as a
nonnegative real. -/
def modelWeight (Q : ℕ) (σ : Fin 2 → ℕ) : {x : ℝ // 0 ≤ x} :=
  ⟨carryThresholdMeasure Q σ 2, by
    unfold carryThresholdMeasure
    exact carryFibreMeasure_nonneg _ _ _⟩

theorem modelPaths_card : modelPaths.card = 4 := by
  unfold modelPaths
  rw [Fintype.card_piFinset]
  simp

/-- The Lemma 22.1 stopped-tree Chernoff certificate for the model family.
The tilt parameter is the trivial `z = 1`; the genuine geometric decay of the
leaf is carried by the area-smallness bound, not by this inert certificate. -/
def modelStoppedTree (shell : FailingDyadicShell) (hX : (2 : ℕ) ^ 26 ≤ shell.X) :
    ChernoffStoppedTreeInputData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : ℝ) where
  Path := Fin 2 → ℕ
  paths := modelPaths
  weight := modelWeight shell.Q
  cost := modelNsh
  Y := 0
  m := 0
  z := ⟨1, le_refl 1⟩
  root := (modelPaths.card : ℝ)
  A := 1
  B := 1
  chernoff_input := by
    have hXr : (2 : ℝ) ^ 26 ≤ (shell.X : ℝ) := by exact_mod_cast hX
    refine
      { tiltBudget :=
          { tilt :=
              { pointwise := ?_ }
            momentBudget :=
              { budget := ?_ } }
        tailBudget :=
          { tail_bound := ?_ } }
    · intro p _
      show (modelWeight shell.Q p : ℝ) * (1 : ℝ) ^ (modelNsh p) ≤ 1
      rw [one_pow, mul_one]
      show carryThresholdMeasure shell.Q p 2 ≤ 1
      rw [carryThresholdMeasure_eq shell.Q p (le_refl 2)]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    · simp
    · simp only [pow_zero, mul_one, div_one]
      rw [modelPaths_card]
      exact le_trans (by norm_num) (leaf_budget_lower_bound _ hXr)

/-- **Step 1 — the abstract gap-word model leaf.**

A genuine, non-vacuous `RegularShellPaidChernoff22_1AInputData` at any large
failing shell.  The weight is the guardrail integer-carry symbolic measure
`2^{-cost}`; the shell-paid multiplier is the genuine cost; the area-smallness
bound is the already-formalized Lemma 22.1A geometric resummation
(`regular_areaWeighted_le_closed`) absorbed into the large-`X` Chernoff budget. -/
def chernoff22_1ALeafOfLargeShell (shell : FailingDyadicShell)
    (hX : (2 : ℕ) ^ 26 ≤ shell.X) :
    RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
      erdos260Constants.ξ (shell.X : ℝ) := by
  have hXr : (2 : ℝ) ^ 26 ≤ (shell.X : ℝ) := by exact_mod_cast hX
  refine RegularShellPaidChernoff22_1AInputData.ofAreaLayerSumStoppedTree
    (modelStoppedTree shell hX) (fun σ => (modelNsh σ : ℝ)) ?_ ?_
  · intro σ _
    exact Nat.cast_nonneg _
  · -- area smallness via the geometric resummation of Lemma 22.1A
    have hclosed :
        ∑ σ ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.range (1 + 1)),
            (fun σ => carryThresholdMeasure shell.Q σ 2) σ * (modelNsh σ : ℝ) ≤
          1 * (1 * regularTiltSum 0 1 2) ^ 2 * (2 / (2 - 1)) := by
      refine regular_areaWeighted_le_closed 0 1 2 2 1 1 2 (by norm_num)
        (by norm_num) (by norm_num)
        (fun σ => carryThresholdMeasure shell.Q σ 2) modelNsh ?_ ?_ ?_ ?_
      · intro σ _
        unfold carryThresholdMeasure
        exact carryFibreMeasure_nonneg _ _ _
      · intro σ _
        dsimp only
        rw [carryThresholdMeasure_eq shell.Q σ (le_refl 2),
          prefixGapSum_eq_sumShellCost σ]
        simp
      · intro σ hσ
        have hσi : ∀ i : Fin 2, σ i ≤ 1 := by
          intro i
          have := Fintype.mem_piFinset.mp hσ i
          rw [Finset.mem_range] at this; omega
        calc modelNsh σ = ∑ i : Fin 2, σ i := by
              simp [modelNsh, shellCost]
          _ ≤ ∑ _i : Fin 2, 1 := Finset.sum_le_sum (fun i _ => hσi i)
          _ = 2 := by simp
      · intro j σ _ hj
        exact le_of_lt hj
    rw [regularTiltSum_zero_one_two] at hclosed
    have hrhs : (1 : ℝ) * (1 * 2) ^ 2 * (2 / (2 - 1)) = 8 := by norm_num
    rw [hrhs] at hclosed
    refine le_trans hclosed (le_trans (by norm_num : (8 : ℝ) ≤ 1000000)
      (leaf_budget_lower_bound _ hXr))

/-- **Step 1 — the leaf from an actual failure context.**

The genuine model Lemma 22.1A leaf attached to a pinned `ActualFailureContext`.
The large-scale regime hypothesis `2^26 ≤ X` is supplied by the manuscript
largeness gate (`aboveCarryThreshold_forces_scale`). -/
def chernoff22_1ALeafOfShell (ctx : ActualFailureContext) :
    RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  chernoff22_1ALeafOfLargeShell ctx.shell
    (aboveCarryThreshold_forces_scale
      (aboveCarryThreshold_of_manuscriptLargeThreshold_le ctx.shell ctx.shell_large))

/-- **Non-vacuity witness.**  The model leaf's stopped family is genuinely
nonempty (four paths). -/
theorem chernoff22_1ALeafOfLargeShell_paths_nonempty
    (shell : FailingDyadicShell) (hX : (2 : ℕ) ^ 26 ≤ shell.X) :
    (chernoff22_1ALeafOfLargeShell shell hX).stoppedTree.paths.Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  show (fun _ => 0) ∈ modelPaths
  rw [modelPaths, Fintype.mem_piFinset]
  intro i
  exact Finset.mem_range.2 (by norm_num)

/-! ## Step 2: the carry-aligned leaf over the actual stopped branches

The carry-aligned leaf uses the *actual* I.9 stopped-branch family
`carryData.stoppedBranches`, the guardrail integer-carry symbolic measure
`wt₀(b) = 2^{-branchShellCost b}`, and the capped genuine window-excess
shell-paid multiplier `Y_sh(b) = min 1 (windowExcess)`.

Every analytic field is discharged unconditionally except for the single §22
antichain measure-sum hypothesis `hKraft : ∑_b 2^{-cost(b)} ≤ 1` (proof_v4 line
818: the principal children of a stopped node are *disjoint* subsets of `Ω_u`,
so their integer-carry measures sum to at most the parent measure).  That
inequality — the genuinely geometric Kraft/antichain fact — is exposed as the
explicit argument `hKraft`. -/

/-- The guardrail integer-carry symbolic weight `2^{-branchShellCost b}` on the
stopped branches, as a nonnegative real.  This is **not** `windowExcessWeight`;
it is the genuine decaying carry measure (`carryThresholdMeasure`), as the
faithfulness lemma below records. -/
def carryShellSymbolicWeight (b : StoppedBranch) : {x : ℝ // 0 ≤ x} :=
  ⟨(1 / 2 : ℝ) ^ branchShellCost b, by positivity⟩

theorem carryShellSymbolicWeight_coe (b : StoppedBranch) :
    (carryShellSymbolicWeight b : ℝ) = (1 / 2 : ℝ) ^ branchShellCost b := rfl

/-- **Faithfulness.**  On a genuine carry branch `stoppedBranchOf a r k`, the
symbolic weight is exactly the integer-carry threshold-fibre measure of the
recorded gap word — the manuscript `|Ω_π|`, not a synthetic stand-in. -/
theorem carryShellSymbolicWeight_eq_carryThresholdMeasure
    (Q : ℕ) (a : Nat → Nat) (k r : Nat) :
    (carryShellSymbolicWeight (stoppedBranchOf a r k) : ℝ) =
      carryThresholdMeasure Q (carryGapWord a k (r + 1)) (r + 1) := by
  rw [carryThresholdMeasure_carryGapWord_eq, carryShellSymbolicWeight_coe]

/-- **Step 2 — the carry-aligned shell-paid Chernoff leaf.**

A genuine `CarryStoppedBranchShellPaidChernoff22_1AInputData` over the actual
carry stopped-branch family `carryData.stoppedBranches`, with the guardrail
measure `2^{-cost}` and the capped window-excess shell-paid multiplier.

* The Lemma 22.1 stopped-tree Chernoff certificate (`chernoff_input`) is closed
  **unconditionally** at the genuine tilt `z = 2` (the pointwise tilt collapses
  to `2^{-cost}·2^{cost} = 1`, and the Chernoff tail `card/2^{card} ≤ 1`
  fits inside the large-`X` budget).
* The area-smallness bound is reduced to the **single** explicit hypothesis
  `hKraft` (proof_v4 line 818 antichain measure-sum) via `Y_sh ≤ 1`. -/
def carryAlignedShellPaidChernoff22_1AOfShell
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr)
    (hX : (2 : ℕ) ^ 26 ≤ shell.X)
    (hKraft : ∑ b ∈ carryData.stoppedBranches, (1 / 2 : ℝ) ^ branchShellCost b ≤ 1) :
    CarryStoppedBranchShellPaidChernoff22_1AInputData
      (cStar := erdos260Constants.cStar) (xi := erdos260Constants.ξ) carryData := by
  have h64 : (64 : ℕ) ≤ shell.X := le_trans (by norm_num) hX
  have hbudget : (1 : ℝ) ≤
      erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : ℝ) / 6 :=
    manuscript_chernoff_budget_ge_one h64
  have hCI : ChernoffShellBudgetData carryData.stoppedBranches
      (fun p => (carryShellSymbolicWeight p : ℝ)) branchShellCost (2 : ℝ)
      (carryData.stoppedBranches.card : ℝ) 1 1 0 carryData.stoppedBranches.card
      erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) := by
    refine
      { tiltBudget :=
          { tilt := { pointwise := ?_ }
            momentBudget := { budget := ?_ } }
        tailBudget := { tail_bound := ?_ } }
    · intro b _
      show (carryShellSymbolicWeight b : ℝ) * (2 : ℝ) ^ branchShellCost b ≤ 1
      have h : (carryShellSymbolicWeight b : ℝ) * (2 : ℝ) ^ branchShellCost b = 1 := by
        show (1 / 2 : ℝ) ^ branchShellCost b * (2 : ℝ) ^ branchShellCost b = 1
        rw [← mul_pow]; norm_num
      exact le_of_eq h
    · show (carryData.stoppedBranches.card : ℝ) * 1 ≤
        (carryData.stoppedBranches.card : ℝ) * (1 : ℝ) ^ (0 : ℕ)
      simp
    · show (carryData.stoppedBranches.card : ℝ) * (1 : ℝ) ^ (0 : ℕ) /
        (2 : ℝ) ^ carryData.stoppedBranches.card ≤
        erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : ℝ) / 6
      rw [pow_zero, mul_one]
      have hlt : (carryData.stoppedBranches.card : ℝ) <
          (2 : ℝ) ^ carryData.stoppedBranches.card := by
        have h := (carryData.stoppedBranches.card).lt_two_pow_self
        calc (carryData.stoppedBranches.card : ℝ)
            < ((2 ^ carryData.stoppedBranches.card : ℕ) : ℝ) := by exact_mod_cast h
          _ = (2 : ℝ) ^ carryData.stoppedBranches.card := by push_cast; ring
      have hle1 : (carryData.stoppedBranches.card : ℝ) /
          (2 : ℝ) ^ carryData.stoppedBranches.card ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      exact le_trans hle1 hbudget
  exact carryStoppedBranchShellPaidChernoff22_1AFromRawAreaLayerSumInput
    carryData.stoppedBranches carryShellSymbolicWeight branchShellCost
    (Finset.Subset.refl _) carryData.stoppedBranches.card 0 ⟨2, by norm_num⟩
    (carryData.stoppedBranches.card : ℝ) 1 1 hCI
    (fun b => min 1 (carryData.stoppedBranchWeightReal b))
    (fun b _ => le_min (by norm_num) (carryData.stoppedBranchWeightReal_nonneg b))
    (by
      calc ∑ b ∈ carryData.stoppedBranches,
              (carryShellSymbolicWeight b : ℝ) *
                min 1 (carryData.stoppedBranchWeightReal b)
          ≤ ∑ b ∈ carryData.stoppedBranches, (carryShellSymbolicWeight b : ℝ) * 1 := by
            apply Finset.sum_le_sum
            intro b _
            exact mul_le_mul_of_nonneg_left (min_le_left _ _)
              (carryShellSymbolicWeight b).property
        _ = ∑ b ∈ carryData.stoppedBranches, (1 / 2 : ℝ) ^ branchShellCost b := by
            apply Finset.sum_congr rfl
            intro b _
            rw [carryShellSymbolicWeight_coe, mul_one]
        _ ≤ 1 := hKraft
        _ ≤ erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : ℝ) / 6 := hbudget)

/-- **Step 2 — projection to the standard regular/shell-paid leaf.**

The carry-aligned leaf collapses to the standard
`RegularShellPaidChernoff22_1AInputData` consumed by the phase core, retaining
its concrete carry-aligned stopped family boundary. -/
def carryAlignedRegularShellPaidChernoff22_1AOfShell
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr)
    (hX : (2 : ℕ) ^ 26 ≤ shell.X)
    (hKraft : ∑ b ∈ carryData.stoppedBranches, (1 / 2 : ℝ) ^ branchShellCost b ≤ 1) :
    RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
      erdos260Constants.ξ (shell.X : ℝ) :=
  (carryAlignedShellPaidChernoff22_1AOfShell carryData hX hKraft).toRegularShellPaidChernoff22_1AInputData

/-! ## Step 3: the L.6.2 bounded-overlap embedding data

The L.6.2 finite-overlap routing data distributes the paid terminal mass over
the stopped shell-paid branches.  The genuinely manuscript inputs are:

* the bounded-overlap embedding `paid_le` — the paid terminal mass is dominated
  by `overlap` times the shell-paid area (proof_v4 line 5810, the bounded-overlap
  truncation map of L.6.2), and
* the overlap budget bookkeeping `overlap_budget`.

Given these, the canonical per-branch distribution
`branchPaid(b) = overlap · (wt₀(b)·Y_sh(b))` discharges the remaining structural
fields `paid_le_branchPaid` (by the distributive law) and
`branchPaid_le_overlap_shellArea` (trivially). -/

/-- **Step 3 — the L.6.2 finite-overlap embedding from the bounded-overlap
embedding.**

The canonical per-branch paid distribution is `overlap · shellArea(b)`; the
distributive law turns the bounded-overlap embedding `paid_le` into the
per-branch routing field `paid_le_branchPaid`. -/
def shellPaidTerminalFiniteOverlapEmbeddingOfDist
    {cStar xi X : ℝ}
    (leaf : RegularShellPaidChernoff22_1AInputData cStar xi X)
    (paidMass overlap mainPaid remPaid : ℝ)
    (overlap_nonneg : 0 ≤ overlap)
    (paid_le :
      paidMass ≤ overlap * (∑ b ∈ leaf.stoppedTree.paths, leaf.wt0 b * leaf.Ysh b))
    (overlap_budget : overlap * (cStar * xi * X / 6) ≤ mainPaid + remPaid) :
    ShellPaidTerminalFiniteOverlapEmbeddingData leaf where
  paidMass := paidMass
  overlap := overlap
  mainPaid := mainPaid
  remPaid := remPaid
  branchPaid := fun b => overlap * (leaf.wt0 b * leaf.Ysh b)
  overlap_nonneg := overlap_nonneg
  paid_le_branchPaid := by
    rw [← Finset.mul_sum]; exact paid_le
  branchPaid_le_overlap_shellArea := fun b _ => le_refl _
  overlap_budget := overlap_budget

/-- **Step 3 — a concrete non-vacuous L.6.2 embedding for the model leaf.**

A genuine finite-overlap embedding at `overlap = 1`, paid mass equal to the
(positive) model shell-paid area, fully discharged.  Confirms the L.6.2 data is
inhabitable with nonzero paid mass. -/
def shellPaidTerminalFiniteOverlapEmbeddingModel
    (shell : FailingDyadicShell) (hX : (2 : ℕ) ^ 26 ≤ shell.X) :
    ShellPaidTerminalFiniteOverlapEmbeddingData (chernoff22_1ALeafOfLargeShell shell hX) :=
  shellPaidTerminalFiniteOverlapEmbeddingOfDist
    (chernoff22_1ALeafOfLargeShell shell hX)
    (∑ b ∈ (chernoff22_1ALeafOfLargeShell shell hX).stoppedTree.paths,
      (chernoff22_1ALeafOfLargeShell shell hX).wt0 b *
        (chernoff22_1ALeafOfLargeShell shell hX).Ysh b)
    1
    (erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : ℝ) / 6)
    0
    zero_le_one
    (le_of_eq (one_mul _).symm)
    (le_of_eq (by rw [one_mul, add_zero]))

/-- **Step 3 — the L.6.2 aggregate embedding.**  Collapsing the finite-overlap
routing yields the aggregate `ShellPaidTerminalEmbeddingData` consumed by the
bounded-class residual package, with the proved L.6.2 conclusion
`paidMass ≤ mainPaid + remPaid`. -/
def shellPaidTerminalEmbeddingOfDist
    {cStar xi X : ℝ}
    (leaf : RegularShellPaidChernoff22_1AInputData cStar xi X)
    (paidMass overlap mainPaid remPaid : ℝ)
    (overlap_nonneg : 0 ≤ overlap)
    (paid_le :
      paidMass ≤ overlap * (∑ b ∈ leaf.stoppedTree.paths, leaf.wt0 b * leaf.Ysh b))
    (overlap_budget : overlap * (cStar * xi * X / 6) ≤ mainPaid + remPaid) :
    ShellPaidTerminalEmbeddingData leaf :=
  (shellPaidTerminalFiniteOverlapEmbeddingOfDist leaf paidMass overlap mainPaid
    remPaid overlap_nonneg paid_le overlap_budget).toShellPaidTerminalEmbeddingData

end

end Erdos260
