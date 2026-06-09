import Mathlib
import Erdos260.ShellPaidChernoff22_1ALeafConstruction
import Erdos260.AppendixN33LeafFromShell

/-!
# Chernoff 22.1A deep analytic cores: the §22 antichain Kraft sum and the L.6.2
bounded-overlap bounded-class split

This module attacks the two deep analytic residuals of the Chernoff 22.1A leaf
that are still carried as explicit hypotheses by the `Erdos260IrreducibleCores`
surface:

* **Core 1 — the §22 antichain / Kraft measure-sum** `hKraft`
  (`∑_{b ∈ carryData.stoppedBranches} 2^{-branchShellCost b} ≤ 1`, proof_v4 line
  818: "principal children are disjoint subsets of `Ω_u`").

* **Core 2 — the L.6.2 shell-paid bounded-class split** `bddLowPaid`
  (proof_v4 truncation map line 5810).

## What is proved here, honestly

### Core 1 (Kraft) — the genuine Kraft inequality, reduced to disjoint fibres

`hKraft` is **not** a theorem over an arbitrary `CarryDataFromFailure`: the
stopped branches `carryData.stoppedBranches` are the length-`(r+1)` high-excess
windows over a (typically consecutive) start set, and these windows overlap, so
the raw sum `∑_b 2^{-cost(b)}` can exceed `1` (e.g. many short windows with small
gaps).  The inequality is true precisely because of the manuscript's geometric
antichain fact: the principal children's integer-carry fibres are **disjoint
subsets of the root fibre** `Ω_u`, and `2^{-cost(b)} = |Ω_π(b)| / |Ω_u|` is the
*normalized* fibre count (exactly the integer-carry measure `carryFibreMeasure =
card / 2^n` of `ChernoffSubconjugacy`).

We therefore:

* prove the **genuine Kraft inequality** `KraftAntichainFibres.sum_le_one` as a
  fully unconditional, axiom-clean theorem: given disjoint fibres inside a root
  `Finset.range (2^N)` with `mass i = |fibre i| / 2^N`, the masses sum to `≤ 1`.
  (The proof is the standard `Finset.card_biUnion` / `card_le_card` argument: the
  disjoint union of the fibres still fits inside the `2^N`-element root.)
* expose the **smallest possible residual** for `hKraft` as the explicit datum
  `KraftAntichainFibres carryData.stoppedBranches (fun b => (1/2)^branchShellCost b)`
  — i.e. *the disjoint-fibre realization of the manuscript `Ω_π ⊆ Ω_u`*; once
  that datum is supplied, `hKraft` (and the whole carry-aligned leaf
  `carryAlignedShellPaidChernoff22_1AOfShell`) follows with no further input.
* give a non-vacuous witness `kraftWitness` (a genuine 2-branch antichain with
  4-element disjoint fibres, masses `1/2 + 1/2 = 1`), so the residual structure
  is demonstrably inhabitable — not an empty/singleton shortcut.

### Core 2 (L.6.2) — the bounded-overlap embedding fully chained to `bddLowPaid`

The `bddLowPaid` field demands a `ShellPaidBddClassBoundData.LowPaidSplitData`.
We build it from the proof_v4 Lemma L.6.2 finite-overlap routing
(`ShellPaidTerminalFiniteOverlapEmbeddingData`) via the already-proven L.6 chain
`FiniteOverlapLowPaidSplitData → LowPaidSplitData`.  Every structural field — the
per-branch routing `paid_le_branchPaid` (distributive law),
`branchPaid_le_overlap_shellArea` (reflexivity), the L.6.1 split, the L.6.3 low
bound, the `paid_eq`/`output_budget` bookkeeping — is discharged here.  The split
collapses to **exactly two genuine manuscript inequalities**:

* `paid_le` — the bounded-overlap truncation: the bounded terminal class mass is
  dominated by `overlap ·` the shell-paid area (proof_v4 line 5810);
* `budget_le` — the budget placement `overlap · (cStar·ξ·X/6) ≤ O_bdd`.

These are the two `paid_le`/`overlap_budget` inputs named in the manuscript;
everything else is closed.

No `sorry`/`axiom`/`admit`; the only remaining inputs are the explicit
hypotheses named above.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## Core 1 — the §22 antichain / Kraft measure-sum -/

/-- **The disjoint-fibre realization of a Kraft antichain.**

This is the smallest faithful residual behind the §22 antichain measure-sum
(proof_v4 line 818).  For a finite family `S` of branches with masses `mass`, it
records a common resolution `N`, a fibre `Finset ℕ` for each branch, and the
manuscript facts:

* each fibre is a subset of the root fibre `Ω_u = Finset.range (2^N)`
  (`fibre_subset`);
* the mass is the *normalized fibre count* `|Ω_π| / |Ω_u|`
  (`mass_eq` — exactly the integer-carry measure `carryFibreMeasure = card/2^n`);
* the fibres are **pairwise disjoint** (`fibre_disjoint`) — "principal children
  are disjoint subsets of `Ω_u`".

From this datum the Kraft sum `∑ mass ≤ 1` follows unconditionally below. -/
structure KraftAntichainFibres {ι : Type*} (S : Finset ι) (mass : ι → ℝ) where
  /-- Resolution of the common root fibre `Ω_u = Finset.range (2^N)`. -/
  N : ℕ
  /-- The integer-carry fibre `Ω_π(i)` of each branch. -/
  fibre : ι → Finset ℕ
  /-- Each fibre is a subset of the root fibre `Ω_u`. -/
  fibre_subset : ∀ i ∈ S, fibre i ⊆ Finset.range (2 ^ N)
  /-- The branch mass is the normalized fibre count `|Ω_π(i)| / |Ω_u|`. -/
  mass_eq : ∀ i ∈ S, mass i = ((fibre i).card : ℝ) / (2 ^ N : ℝ)
  /-- The principal-child fibres are pairwise disjoint subsets of `Ω_u`. -/
  fibre_disjoint : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (fibre i) (fibre j)

namespace KraftAntichainFibres

/-- **The genuine Kraft inequality.**  If the branch masses are the normalized
counts of pairwise-disjoint fibres inside the `2^N`-element root, then the masses
sum to at most `1`.  The disjoint union of the fibres still fits inside the
`2^N`-element root, so `∑ |Ω_π| ≤ |Ω_u| = 2^N`, hence `∑ |Ω_π|/2^N ≤ 1`.

This is fully unconditional and axiom-clean; it is the formal content of
proof_v4 line 818. -/
theorem sum_le_one {ι : Type*} {S : Finset ι} {mass : ι → ℝ}
    (h : KraftAntichainFibres S mass) :
    ∑ i ∈ S, mass i ≤ 1 := by
  classical
  have hbU : (S.biUnion h.fibre).card = ∑ i ∈ S, (h.fibre i).card :=
    Finset.card_biUnion h.fibre_disjoint
  have hsub : S.biUnion h.fibre ⊆ Finset.range (2 ^ h.N) :=
    Finset.biUnion_subset.mpr h.fibre_subset
  have hcard_le : (S.biUnion h.fibre).card ≤ 2 ^ h.N := by
    have hle := Finset.card_le_card hsub
    rwa [Finset.card_range] at hle
  have key : ∑ i ∈ S, mass i = ((S.biUnion h.fibre).card : ℝ) / (2 ^ h.N : ℝ) := by
    rw [hbU, Nat.cast_sum, Finset.sum_div]
    exact Finset.sum_congr rfl (fun i hi => h.mass_eq i hi)
  rw [key, div_le_one (by positivity)]
  exact_mod_cast hcard_le

end KraftAntichainFibres

/-- **`(1/2)^c = 2^{N-c} / 2^N` for `c ≤ N`.**  The dyadic identity matching a
cost-`c` fibre's normalized count `2^{N-c}/2^N` to the symbolic mass `2^{-c}`. -/
theorem half_pow_eq_pow_sub_div {N c : ℕ} (h : c ≤ N) :
    (1 / 2 : ℝ) ^ c = (2 : ℝ) ^ (N - c) / 2 ^ N := by
  rw [div_pow, one_pow,
    div_eq_div_iff (by positivity : (2:ℝ) ^ c ≠ 0) (by positivity : (2:ℝ) ^ N ≠ 0),
    one_mul, ← pow_add]
  congr 1
  omega

/-- **Kraft fibre data from explicit fibre cardinalities.**  The manuscript-shaped
constructor: given a per-branch cost, a resolution `N` dominating every cost, and
disjoint fibres of size exactly `|Ω_π(i)| = 2^{N - cost i}`, package the Kraft
datum for the symbolic masses `2^{-cost}`. -/
def KraftAntichainFibres.ofCardPow {ι : Type*} (S : Finset ι) (cost : ι → ℕ)
    (N : ℕ) (fibre : ι → Finset ℕ)
    (cost_le : ∀ i ∈ S, cost i ≤ N)
    (fibre_subset : ∀ i ∈ S, fibre i ⊆ Finset.range (2 ^ N))
    (fibre_card : ∀ i ∈ S, (fibre i).card = 2 ^ (N - cost i))
    (fibre_disjoint : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (fibre i) (fibre j)) :
    KraftAntichainFibres S (fun i => (1 / 2 : ℝ) ^ cost i) where
  N := N
  fibre := fibre
  fibre_subset := fibre_subset
  mass_eq := fun i hi => by
    show (1 / 2 : ℝ) ^ cost i = ((fibre i).card : ℝ) / (2 ^ N : ℝ)
    rw [fibre_card i hi]
    push_cast
    exact half_pow_eq_pow_sub_div (cost_le i hi)
  fibre_disjoint := fibre_disjoint

/-- **Core 1 reduction.**  The §22 antichain measure-sum `hKraft` follows from the
disjoint-fibre Kraft datum on the actual carry stopped branches.  This reduces the
`hKraft` hypothesis of `carryAlignedShellPaidChernoff22_1AOfShell` to the single
explicit residual `KraftAntichainFibres carryData.stoppedBranches …` — the
formal "`Ω_π` are disjoint subsets of `Ω_u`" of proof_v4 line 818. -/
theorem hKraft_of_kraftFibres
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr)
    (kraft : KraftAntichainFibres carryData.stoppedBranches
      (fun b => (1 / 2 : ℝ) ^ branchShellCost b)) :
    ∑ b ∈ carryData.stoppedBranches, (1 / 2 : ℝ) ^ branchShellCost b ≤ 1 :=
  kraft.sum_le_one

/-- **Core 1 — the carry-aligned Chernoff 22.1A leaf from the Kraft fibre datum.**

Fully assembles `carryAlignedShellPaidChernoff22_1AOfShell` once the disjoint
`Ω_π ⊆ Ω_u` fibres are supplied: the §22 antichain measure-sum is discharged by
the proved Kraft inequality, and every other field is already unconditional. -/
def carryAlignedChernoff22_1ALeaf_ofKraftFibres
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr)
    (hX : (2 : ℕ) ^ 26 ≤ shell.X)
    (kraft : KraftAntichainFibres carryData.stoppedBranches
      (fun b => (1 / 2 : ℝ) ^ branchShellCost b)) :
    CarryStoppedBranchShellPaidChernoff22_1AInputData
      (cStar := erdos260Constants.cStar) (xi := erdos260Constants.ξ) carryData :=
  carryAlignedShellPaidChernoff22_1AOfShell carryData hX
    (hKraft_of_kraftFibres carryData kraft)

/-! ### Non-vacuity witness for the Kraft datum

A genuine 2-branch antichain whose fibres are the disjoint 4-element dyadic
half-intervals `[0,4)` and `[4,8)` inside the 8-element root `[0,8)`.  The masses
are `2^{-1} = 1/2` each, summing to exactly `1` — the Kraft bound is tight, so
this is a non-degenerate witness (no empty/singleton shortcut). -/

/-- The two disjoint fibres of the witness antichain. -/
def kraftWitnessFibre : Bool → Finset ℕ
  | true => Finset.Ico 0 4
  | false => Finset.Ico 4 8

/-- A genuine inhabitant of `KraftAntichainFibres`: two cost-`1` branches with
disjoint 4-element fibres inside the 8-element root. -/
def kraftWitness :
    KraftAntichainFibres (Finset.univ : Finset Bool) (fun _ => (1 / 2 : ℝ) ^ (1 : ℕ)) :=
  KraftAntichainFibres.ofCardPow (Finset.univ : Finset Bool) (fun _ => 1) 3
    kraftWitnessFibre
    (fun _ _ => by norm_num)
    (fun b _ => by
      cases b <;>
        · simp only [kraftWitnessFibre, Finset.range_eq_Ico]
          exact Finset.Ico_subset_Ico (by norm_num) (by norm_num))
    (fun b _ => by cases b <;> simp [kraftWitnessFibre, Nat.card_Ico])
    (fun b _ b' _ hbb' => by
      cases b <;> cases b' <;> simp only [kraftWitnessFibre]
      · exact absurd rfl hbb'
      · exact (Finset.Ico_disjoint_Ico_consecutive 0 4 8).symm
      · exact Finset.Ico_disjoint_Ico_consecutive 0 4 8
      · exact absurd rfl hbb')

/-- The witness antichain's Kraft sum is `≤ 1` (and in fact tight: `1/2 + 1/2`),
confirming the residual structure is genuinely inhabitable. -/
theorem kraftWitness_sum_le_one :
    ∑ _b ∈ (Finset.univ : Finset Bool), (1 / 2 : ℝ) ^ (1 : ℕ) ≤ 1 :=
  kraftWitness.sum_le_one

/-! ## Core 2 — the L.6.2 bounded-overlap bounded-class split `bddLowPaid` -/

/-- **L.6.2 finite-overlap low/paid split from the bounded-overlap inputs.**

Builds the proof_v4 Lemma L.6.2 finite-overlap routing of the bounded terminal
class into the stopped shell-paid family, with the canonical choices:

* all bounded-class mass is paid (`wtLow = 0`, `remLow = 0`) — the L.6.1 split;
* the per-branch routing is `branchPaid b = overlap · (wt0 b · Ysh b)`;
* `mainPaid = overlap · (cStar·ξ·X/6)`, `remPaid = 0`.

The structural fields (`paid_le_branchPaid`, `branchPaid_le_overlap_shellArea`,
`paid_eq`, `split`, `low_le`, `overlap_budget`) are all discharged; the only
manuscript inputs are `paid_le` (the bounded-overlap truncation, line 5810) and
`budget_le` (the budget placement). -/
def finiteOverlapLowPaidOfBoundedOverlap
    {cStar xi X : ℝ}
    (leaf : RegularShellPaidChernoff22_1AInputData cStar xi X)
    (objects : Finset OutputObjectV4) (terminalWeight : OutputObjectV4 → ℝ)
    (O_bdd overlap : ℝ)
    (overlap_nonneg : 0 ≤ overlap)
    (paid_le :
      AppendixN.classMassV4 objects terminalWeight OutputClassV4.bdd ≤
        overlap * (∑ b ∈ leaf.stoppedTree.paths, leaf.wt0 b * leaf.Ysh b))
    (budget_le : overlap * (cStar * xi * X / 6) ≤ O_bdd) :
    ShellPaidBddClassBoundData.FiniteOverlapLowPaidSplitData leaf objects
      terminalWeight O_bdd where
  wtLow := fun _ => 0
  wtPaid := terminalWeight
  remLow := 0
  embedding :=
    shellPaidTerminalFiniteOverlapEmbeddingOfDist leaf
      (AppendixN.classMassV4 objects terminalWeight OutputClassV4.bdd)
      overlap (overlap * (cStar * xi * X / 6)) 0
      overlap_nonneg paid_le (le_of_eq (by ring))
  paid_eq := rfl
  split := fun o _ => (zero_add _).symm
  low_le := by simp
  output_budget := by
    show overlap * (cStar * xi * X / 6) + ((0 : ℝ) + 0) ≤ O_bdd
    simpa using budget_le

/-- **Core 2 (generic) — the L.6.2 bounded-class low/paid split.**

Collapses the finite-overlap routing above to the aggregate
`ShellPaidBddClassBoundData.LowPaidSplitData` consumed by the N.3.3 terminal
absorption package, via the already-proven L.6 chain `toLowPaidSplitData`. -/
def lowPaidSplitOfBoundedOverlap
    {cStar xi X : ℝ}
    (leaf : RegularShellPaidChernoff22_1AInputData cStar xi X)
    (objects : Finset OutputObjectV4) (terminalWeight : OutputObjectV4 → ℝ)
    (O_bdd overlap : ℝ)
    (overlap_nonneg : 0 ≤ overlap)
    (paid_le :
      AppendixN.classMassV4 objects terminalWeight OutputClassV4.bdd ≤
        overlap * (∑ b ∈ leaf.stoppedTree.paths, leaf.wt0 b * leaf.Ysh b))
    (budget_le : overlap * (cStar * xi * X / 6) ≤ O_bdd) :
    ShellPaidBddClassBoundData.LowPaidSplitData leaf objects terminalWeight O_bdd :=
  (finiteOverlapLowPaidOfBoundedOverlap leaf objects terminalWeight O_bdd overlap
    overlap_nonneg paid_le budget_le).toLowPaidSplitData

/-- **Core 2 — the `bddLowPaid` datum at an actual failure context.**

Exactly the shape of the `bddLowPaid` field of `Erdos260N33Cores`: the L.6.2
shell-paid low/paid split of the bounded (Tower-routed) terminal class against the
unconditional Chernoff model leaf `chernoff22_1ALeafOfShell ctx`, for any class
budget `O_bdd` (the re-integration pins `O_bdd := termTower …`).

The remaining inputs are the two genuine manuscript inequalities:

* `paid_le` — the bounded terminal class mass `classMassV4 … bdd` is dominated by
  `overlap ·` the model leaf's shell-paid area (proof_v4 line 5810);
* `budget_le` — `overlap · (cStar·ξ·X/6) ≤ O_bdd`. -/
def bddLowPaidOfShell
    (ctx : ActualFailureContext) (O_bdd overlap : ℝ)
    (overlap_nonneg : 0 ≤ overlap)
    (paid_le :
      AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
          OutputClassV4.bdd ≤
        overlap * (∑ b ∈ (chernoff22_1ALeafOfShell ctx).stoppedTree.paths,
          (chernoff22_1ALeafOfShell ctx).wt0 b * (chernoff22_1ALeafOfShell ctx).Ysh b))
    (budget_le :
      overlap *
          (erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) ≤
        O_bdd) :
    ShellPaidBddClassBoundData.LowPaidSplitData (chernoff22_1ALeafOfShell ctx)
      (appendixN33Outputs ctx) appendixN33Weight O_bdd :=
  lowPaidSplitOfBoundedOverlap (chernoff22_1ALeafOfShell ctx)
    (appendixN33Outputs ctx) appendixN33Weight O_bdd overlap overlap_nonneg
    paid_le budget_le

end

end Erdos260
