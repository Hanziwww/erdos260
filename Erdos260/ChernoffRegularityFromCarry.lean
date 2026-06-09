import Mathlib
import Erdos260.Lemma221Regular
import Erdos260.StoppedTreeIndex

/-!
# The Chernoff regularity primitive: carry stopped tree ↦ Lemma 22.1

This file isolates, *honestly*, the single geometric input that the proved
Lemma 22.1 suite (`Lemma221Regular.lean`) needs in order to apply to the carry
stopped tree (`StoppedTreeIndex.lean`).

## What Lemma 22.1 consumes

`RegularStoppedChernoffFamily` (the packaged analytic core of Lemma 22.1) needs
the *per-path* manuscript regularity (`proof_v4` §22, lines 732-734)

```
weight(π) ≤ |Ω_root| · K^m · 2^{-cost(π)},   cost(π) = ∑_{e∈π} s(e),
```

which `regular_path_mass_le_of_edge` obtains by telescoping the *per-edge*
manuscript "regular edge" definition (`proof_v4` §22, lines 730-731)

```
edge u → v is regular  :⟺  |Ω_v| ≤ K · |Ω_u| · 2^{-𝔰(e)},   𝔰(e) = s(e) + c_θ θ(e).
```

Here `|Ω_v|` is the **measure** of the node `v` in the manuscript's symbolic
dynamics: a quantity that *decays multiplicatively* as one descends the tree.

## The honest determination: regularity is NOT derivable from the carry data

The carry stopped tree supplies a genuine combinatorial skeleton (branches,
edges, shell costs, the bounded gap alphabet), but its *intrinsic* branch weight
is the **window excess**

```
stoppedBranchWeightReal carryData b = windowExcessWeight T b = (branchShellCost b − T)₊
```

(`StoppedTreeIndex.lean`).  This is the OPPOSITE of a decaying node measure: it
is *non-decreasing* in the accumulated shell cost (`windowExcessWeight_mono_branchShellCost`),
and it concretely *violates* the regular-edge inequality
(`windowExcessWeight_violates_regularEdge`).  Therefore the per-edge regularity
`|Ω_v| ≤ K|Ω_u|2^{-s(e)}` is **not** a theorem of the carry recurrence / gap
structure: it is an *irreducible measure-theoretic primitive* — the existence of
a node measure on the carry tree that decays along regular edges.

## What is therefore proved here

We define the **smallest faithful regular-edge primitive** `RegularEdgeData`: a
nonnegative node measure `Ω` on the length-`m` gap-word paths over the bounded
gap alphabet `{0, …, G}`, together with the manuscript regular-edge inequality on
every edge and the root bound `Ω_root ≤ rootMass`.  From it we prove, with **no**
further hypothesis:

* `RegularEdgeData.regular_path_bound` — the per-path mass bound, by telescoping
  through `regular_path_mass_le_of_edge` (lifted to `Fin m` indexing in
  `regular_path_mass_le_of_edge_fin`);
* `RegularEdgeData.toRegularStoppedChernoffFamily` — a genuine
  `RegularStoppedChernoffFamily` whose `regular` field is *proved* from the
  per-edge primitive (only the numeric length/threshold calibration `m ≤ c₁Y`
  remains an explicit input, exactly as in `RegularStoppedChernoffFamily`);
* `RegularEdgeData.chernoffPhase` — the Chernoff phase budget
  `Regular ≤ cStar·ξ·X/6`, via `chernoffPathSpace_of_regularFamily`.

Finally, the **carry connection** is made faithful: the bounded gap alphabet and
its gap words are genuinely realized by the carry hit-gaps
(`carryGapWord`, `carryGapWord_mem_piFinset`), and the Lemma 22.1 shell-cost of a
carry branch's gap word is dominated by the carry tree's recorded branch shell
cost (`carryGapWord_shellCost_le_branchShellCost`).

**Net depth.** The Chernoff regularity primitive is reduced to *exactly one*
honest geometric obligation: a node measure on the carry tree decaying along
regular edges (`RegularEdgeData.regular_edge`).  Everything connecting that
obligation to the Chernoff phase budget is proved here, `sorry`/`axiom`-free.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## Reusable core: `Fin m`-indexed telescoping of per-edge regularity

`regular_path_mass_le_of_edge` (in `Lemma221Regular.lean`) telescopes per-edge
regularity for a `ℕ`-indexed gap sequence.  The Lemma 22.1 path family is indexed
by `Fin m → ℕ`, so we lift the telescoping to that indexing once and for all.
This is the same `ℕ`-lift used inside `regular_weightedMoment_le_of_edge`,
extracted as a standalone, reusable lemma. -/

/-- **Per-path mass bound from per-edge regularity (`Fin m` indexing).**

If a mass sequence `mass : ℕ → ℝ` over a length-`m` gap word `σ : Fin m → ℕ`
starts at `mass 0 ≤ rootMass` and obeys the manuscript per-edge regular bound
`mass(k+1) ≤ K·mass k·2^{-s(e_k)}` on every edge `k < m`, then the final mass
obeys the per-path bound `mass m ≤ rootMass·K^m·2^{-∑ s(e)}`.  This is a pure,
unconditional telescoping (it is `regular_path_mass_le_of_edge` reindexed). -/
theorem regular_path_mass_le_of_edge_fin
    (Csh m : ℕ) (K rootMass : ℝ) (hK : 0 ≤ K)
    (σ : Fin m → ℕ) (mass : ℕ → ℝ)
    (hmass0 : mass 0 ≤ rootMass)
    (hedge : ∀ (k : ℕ) (hk : k < m),
        mass (k + 1) ≤ K * mass k * (1 / 2) ^ shellCost Csh (σ ⟨k, hk⟩)) :
    mass m ≤ rootMass * K ^ m * (1 / 2) ^ (∑ i, shellCost Csh (σ i)) := by
  -- Canonical `ℕ`-indexed gap sequence of the `Fin m` path.
  set g : ℕ → ℕ := fun k => if h : k < m then σ ⟨k, h⟩ else 0 with hg
  have hgk : ∀ (k : ℕ) (hk : k < m), g k = σ ⟨k, hk⟩ := fun k hk => dif_pos hk
  have hpath := regular_path_mass_le_of_edge Csh K rootMass hK g mass hmass0 m
    (by
      intro k hk
      rw [hgk k hk]
      exact hedge k hk)
  have hcost :
      (∑ k ∈ Finset.range m, shellCost Csh (g k)) = ∑ i, shellCost Csh (σ i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => shellCost Csh (g k)) m]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrArg (shellCost Csh) (hgk (i : ℕ) i.isLt)
  rw [← hcost]
  exact hpath

/-! ## Honest obstruction: the carry intrinsic weight is not a regular measure

The carry tree's intrinsic branch weight `windowExcessWeight T b = (branchShellCost b − T)₊`
is interpreted as a node measure by attaching to each node the window excess of
the branch ending there.  We show this interpretation cannot be a regular-edge
measure: it is non-decreasing in shell cost, and there is a concrete edge that
violates the regular-edge inequality for *every* constant `K`. -/

/-- The window-excess weight is **monotone non-decreasing** in the accumulated
branch shell cost.  A regular-edge node measure must *decrease* by a factor
`K·2^{-s(e)}` along each edge; the carry intrinsic weight does the opposite. -/
theorem windowExcessWeight_mono_branchShellCost (T : ℝ) {b₁ b₂ : StoppedBranch}
    (h : branchShellCost b₁ ≤ branchShellCost b₂) :
    windowExcessWeight T b₁ ≤ windowExcessWeight T b₂ := by
  unfold windowExcessWeight
  apply positivePart_mono
  have hcast : (branchShellCost b₁ : ℝ) ≤ (branchShellCost b₂ : ℝ) := by
    exact_mod_cast h
  linarith

/-- Extending a branch by a head edge never decreases its window-excess weight:
`Ω(parent) ≤ Ω(child)`.  This is the precise sense in which the carry intrinsic
weight is "anti-regular": a regular edge would force `Ω(child) ≤ K·Ω(parent)·2^{-s}`,
i.e. a *contraction*, whereas the carry weight only grows under extension. -/
theorem windowExcessWeight_le_extend (T : ℝ) (e : BranchEdge) (es : List BranchEdge) :
    windowExcessWeight T ⟨es⟩ ≤ windowExcessWeight T ⟨e :: es⟩ := by
  apply windowExcessWeight_mono_branchShellCost
  rw [branchShellCost_cons]
  omega

/-- **Concrete violation of the regular-edge inequality.**

Interpret the carry intrinsic weight as a node measure.  Take the root node
(empty branch `⟨[]⟩`, window excess `0` at threshold `0`) and its child obtained
by appending one edge of shell cost `1` (window excess `1`).  For *no* constant
`K` and *no* shell exponent `s` is this edge regular: regularity would force the
strictly positive child excess `1` below `K · 0 · 2^{-s} = 0`.  Hence the carry
intrinsic weight is provably **not** the manuscript's decaying node measure
`|Ω_v|`, and the per-edge regularity must be supplied as an external primitive. -/
theorem windowExcessWeight_violates_regularEdge (K : ℝ) (s : ℕ) :
    ¬ windowExcessWeight 0 ⟨[⟨0, 0, 1, 0⟩]⟩
        ≤ K * windowExcessWeight 0 (⟨[]⟩ : StoppedBranch) * (1 / 2) ^ s := by
  have hroot : windowExcessWeight 0 (⟨[]⟩ : StoppedBranch) = 0 := by
    unfold windowExcessWeight
    rw [branchShellCost_nil]
    simp [positivePart]
  have hchild : windowExcessWeight 0 (⟨[⟨0, 0, 1, 0⟩]⟩ : StoppedBranch) = 1 := by
    have hcost : branchShellCost (⟨[⟨0, 0, 1, 0⟩]⟩ : StoppedBranch) = 1 := by
      rw [branchShellCost_cons, branchShellCost_nil]
    unfold windowExcessWeight
    rw [hcost]
    norm_num [positivePart]
  rw [hroot, hchild, mul_zero, zero_mul]
  norm_num

/-! ## The faithful regular-edge primitive and the Chernoff family it builds -/

/-- **The smallest faithful regular-edge primitive (manuscript §22).**

A nonnegative node measure `Ω` on the length-`m` gap-word paths over the bounded
gap alphabet `{0, …, G}`, satisfying the manuscript regular-edge inequality on
every edge and bounded at the root.  Concretely:

* `Ω σ k` is `|Ω|` of the depth-`k` node on the path with gap word `σ`;
* `root_le` is `|Ω_root| ≤ rootMass`;
* `regular_edge` is the irreducible geometric primitive
  `|Ω_v| ≤ K·|Ω_u|·2^{-s(e)}` (`proof_v4` §22, lines 730-731), here in the
  shell-only `2^{-s(e)}` form used by Lemma 22.1; the manuscript's larger
  `𝔰(e) = s(e) + c_θ θ(e) ≥ s(e)` only sharpens the decay, so this form is
  faithful and weaker.

This is precisely the input that the carry recurrence does **not** provide (see
the obstruction theorems above): everything else in the Chernoff phase is then
proved from it. -/
structure RegularEdgeData (Csh G m : ℕ) (K rootMass : ℝ) where
  /-- The decay constant of the regular-edge bound is nonnegative. -/
  hK : 0 ≤ K
  /-- The node measure `Ω σ k = |Ω|` of the depth-`k` node on path `σ`. -/
  Ω : (Fin m → ℕ) → ℕ → ℝ
  /-- The path weight (final-node measure) is nonnegative. -/
  weight_nonneg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
      0 ≤ Ω σ m
  /-- Root bound `|Ω_root| ≤ rootMass` (`proof_v4` §22). -/
  root_le : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
      Ω σ 0 ≤ rootMass
  /-- **The regular-edge primitive** `|Ω_v| ≤ K·|Ω_u|·2^{-s(e)}` on every edge
  (`proof_v4` §22, lines 730-731).  This is the one irreducible geometric input. -/
  regular_edge : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
      ∀ (k : ℕ) (hk : k < m),
        Ω σ (k + 1) ≤ K * Ω σ k * (1 / 2) ^ shellCost Csh (σ ⟨k, hk⟩)

/-- **Per-path mass bound (telescoped, proved).**  The final-node measure of any
regular path obeys the manuscript per-path bound `|Ω_π| ≤ rootMass·K^m·2^{-cost(π)}`.
This is `regular_path_mass_le_of_edge_fin` applied to the per-edge primitive — the
exact `regular` hypothesis consumed by `RegularStoppedChernoffFamily`. -/
theorem RegularEdgeData.regular_path_bound {Csh G m : ℕ} {K rootMass : ℝ}
    (d : RegularEdgeData Csh G m K rootMass)
    {σ : Fin m → ℕ}
    (hσ : σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1))) :
    d.Ω σ m ≤ rootMass * K ^ m * (1 / 2) ^ (∑ i, shellCost Csh (σ i)) :=
  regular_path_mass_le_of_edge_fin Csh m K rootMass d.hK σ (d.Ω σ)
    (d.root_le σ hσ) (d.regular_edge σ hσ)

/-- **Build the Lemma 22.1 Chernoff family from the regular-edge primitive.**

Given the regular-edge primitive and the numeric length-vs-threshold calibration
`m ≤ c₁Y` (in its quantitative form `rootMass·(K·tiltSum)^m ≤ (cStar·ξ·X/6)·z^Y`,
which is the only remaining input of `RegularStoppedChernoffFamily`), this
produces a genuine `RegularStoppedChernoffFamily` whose `regular` field is
**proved** by telescoping (`regular_path_bound`).  No new manuscript hypothesis
is introduced beyond the single geometric primitive `regular_edge`. -/
def RegularEdgeData.toRegularStoppedChernoffFamily {Csh G m : ℕ} {K rootMass : ℝ}
    (d : RegularEdgeData Csh G m K rootMass)
    {cStar ξ X : ℝ} (Y : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (calibration :
      rootMass * (K * regularTiltSum Csh G z) ^ m ≤ (cStar * ξ * X / 6) * z ^ Y) :
    RegularStoppedChernoffFamily cStar ξ X where
  Csh := Csh
  G := G
  m := m
  Y := Y
  rootMass := rootMass
  K := K
  z := z
  z_ge_one := hz
  weight := fun σ => d.Ω σ m
  weight_nonneg := fun σ hσ => d.weight_nonneg σ hσ
  regular := fun σ hσ => d.regular_path_bound (σ := σ) hσ
  calibration := calibration

/-- **Chernoff phase budget from the regular-edge primitive (capstone).**

For a regular-edge primitive with the calibration, the Chernoff phase
contribution `Regular` exists and fits the phase budget `cStar·ξ·X/6`, with a
fully proved moment bound (it factors through
`chernoffPathSpace_of_regularFamily`, whose `moment_bound` is discharged by the
proved factorization `regular_weightedMoment_le`).  Thus the Chernoff phase mass
of Lemma 22.1 is constructed *modulo exactly one* geometric primitive: the carry
tree carries a node measure decaying along regular edges. -/
theorem RegularEdgeData.chernoffPhase {Csh G m : ℕ} {K rootMass : ℝ}
    (d : RegularEdgeData Csh G m K rootMass)
    {cStar ξ X : ℝ} (Y : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (calibration :
      rootMass * (K * regularTiltSum Csh G z) ^ m ≤ (cStar * ξ * X / 6) * z ^ Y) :
    ∃ Regular : ℝ, 0 ≤ Regular ∧ Regular ≤ cStar * ξ * X / 6 :=
  chernoffPathSpace_of_regularFamily
    (d.toRegularStoppedChernoffFamily Y z hz calibration)

/-! ## Faithful realization of the gap alphabet by the carry stopped tree

The path family of `RegularStoppedChernoffFamily` is the set of length-`m` gap
words over `{0, …, G}`.  We show this is genuinely the carry stopped-branch family:
the gap word of the carry branch `stoppedBranchOf a r k` is `i ↦ hitGap a (k+i)`,
it lands in the bounded alphabet under the manuscript gap bound `hitGap ≤ G`
(`hitGap_le_logTwo_add_const`, with `G = L+B+1`), and its Lemma 22.1 shell-cost is
dominated by the carry tree's recorded `branchShellCost`. -/

/-- The gap word of the carry branch of length `m` starting at hit index `k`:
`i ↦ hitGap a (k + i)`.  This is the gap profile of `stoppedBranchOf a (m-1) k`. -/
def carryGapWord (a : Nat → Nat) (k m : Nat) : Fin m → Nat :=
  fun i => hitGap a (k + (i : Nat))

/-- **Alphabet realization.**  Under the manuscript bounded-gap hypothesis
`hitGap a (k+i) ≤ G` (the carry gap bound `g ≤ L + B + 1`), the carry branch gap
word lands in the Lemma 22.1 path family `{0, …, G}^m`.  Thus the abstract gap
alphabet of `RegularStoppedChernoffFamily` is genuinely the carry stopped-tree
alphabet. -/
theorem carryGapWord_mem_piFinset {a : Nat → Nat} {k m G : Nat}
    (hgap : ∀ i : Fin m, hitGap a (k + (i : Nat)) ≤ G) :
    carryGapWord a k m ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)) := by
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_range]
  have hi := hgap i
  simp only [carryGapWord]
  omega

/-- The Lemma 22.1 shell-cost of the carry branch gap word, reindexed as a sum
over hit indices `k, …, k+m-1`. -/
theorem carryGapWord_cost (a : Nat → Nat) (k m Csh : Nat) :
    (∑ i, shellCost Csh (carryGapWord a k m i))
      = ∑ i ∈ Finset.range m, shellCost Csh (hitGap a (k + i)) := by
  simp only [carryGapWord]
  exact Fin.sum_univ_eq_sum_range (fun i => shellCost Csh (hitGap a (k + i))) m

/-- **Cost domination.**  The Lemma 22.1 shell-cost `∑ s(e)` of a carry branch's
gap word is at most the carry tree's recorded total branch shell cost
`branchShellCost (stoppedBranchOf a r k) = gapWindow (hitGap a) k r`
(`branchShellCost_stoppedBranchOf`), since `s(h) = max(h − C_sh, 0) ≤ h`.  This is
the faithful bridge between the manuscript shell cost and the carry tree's
recorded cost. -/
theorem carryGapWord_shellCost_le_branchShellCost (a : Nat → Nat) (Csh r k : Nat) :
    (∑ i, shellCost Csh (carryGapWord a k (r + 1) i))
      ≤ branchShellCost (stoppedBranchOf a r k) := by
  rw [carryGapWord_cost, branchShellCost_stoppedBranchOf]
  unfold gapWindow
  exact Finset.sum_le_sum (fun i _ => shellCost_le_height Csh (hitGap a (k + i)))

/-- **Carry-branch corollary.**  For a carry/failure bundle, every carry branch's
gap word (length `r+1`, started at any hit index) lands in the Lemma 22.1 path
family under the manuscript gap bound.  This records that the regular-edge
primitive `RegularEdgeData (·) (·) (carryData.r + 1) (·) (·)` is the carry
stopped-tree object: its paths are exactly the carry branch gap words. -/
theorem CarryDataFromFailure.carryGapWord_mem
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) {G k : Nat}
    (hgap : ∀ i : Fin (carryData.r + 1),
        hitGap carryData.a (k + (i : Nat)) ≤ G) :
    carryGapWord carryData.a k (carryData.r + 1)
      ∈ Fintype.piFinset (fun _ : Fin (carryData.r + 1) => Finset.range (G + 1)) :=
  carryGapWord_mem_piFinset hgap

end

end Erdos260
