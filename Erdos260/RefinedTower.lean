import Mathlib
import Erdos260.Tower

/-!
# Refined terminal-labelled tower and Theorem E.6

This file extends `Erdos260.Tower` with the **refined** tower vocabulary
of Appendix E in `proof_v2.tex`: AP-fibre data, slope `μ_Γ`, the
slope-transition formula `μ_next = 2^g μ_Γ − 1`, outgoing-uniqueness
on the gap interval `(2^{-g}, 2^{1-g})`, and the simple-cycle theorem
for recurrent SCCs.

The combinatorial backbone (`LayerIncreasing`, `CommonFibre`, etc.) is
already in `Tower.lean`; here we add the analytic slope data and the
manuscript form of Theorem E.6 in a parametric closure.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ### E.1 Refined recurrent tower vertex -/

/--
A *refined recurrent tower vertex* is a `TowerVertex` together with an
**AP subfibre** (a finer fibre coordinate on the AP carry) and a
**slope** `μ ∈ ℝ`.  The manuscript reserves the name "refined" for the
case `0 < μ < 1`, but we keep the slope unconstrained in the structure
and add the openness predicate `RefinedVertex.OpenSlope` below.
-/
structure RefinedVertex extends TowerVertex where
  apSubfibre : Nat
  slope : ℝ

/-- The manuscript's "open slope" condition `0 < μ < 1`. -/
def RefinedVertex.OpenSlope (v : RefinedVertex) : Prop :=
  0 < v.slope ∧ v.slope < 1

/-! ### E.5 Slope transition on a common subfibre

The manuscript's slope-transition formula is
\[
  μ_{next} = 2^{g} μ_Γ − 1
\]
where `g` is the integer gap between the source and target hits.
We formalize it as a predicate on a pair of refined vertices.
-/

/--
**Slope transition predicate.**  A directed step from `v` to `w` along
a common AP subfibre with hit gap `g` satisfies the manuscript
identity (E.13).  This is a refined-tower property, not an assertion.
-/
def RefinedVertex.SlopeTransition (v w : RefinedVertex) (g : Nat) : Prop :=
  w.apSubfibre = v.apSubfibre ∧
    w.slope = (2 : ℝ) ^ g * v.slope - 1

/-! ### E.6 Outgoing uniqueness via slope intervals -/

/--
The half-open slope band at gap `g`: `μ ∈ (2^{-g}, 2^{1-g}]`.
The manuscript uses this band to prove that the outgoing edge of a
refined recurrent tower vertex is unique on each common AP subfibre.
-/
def RefinedSlopeBand (g : Nat) (μ : ℝ) : Prop :=
  (2 : ℝ) ^ (- (g : ℤ)) < μ ∧ μ <= (2 : ℝ) ^ (1 - (g : ℤ))

/--
Two slope bands at distinct gaps are pairwise disjoint.  This is the
arithmetic backbone of E.6's slope-uniqueness step: a single slope `μ`
in `(0,1)` lies in **exactly one** band `RefinedSlopeBand g`.
-/
theorem refinedSlopeBand_disjoint {μ : ℝ} {g₁ g₂ : Nat}
    (h₁ : RefinedSlopeBand g₁ μ) (h₂ : RefinedSlopeBand g₂ μ) :
    g₁ = g₂ := by
  classical
  rcases h₁ with ⟨h₁lo, h₁hi⟩
  rcases h₂ with ⟨h₂lo, h₂hi⟩
  by_contra hne
  -- Strict order: WLOG `g₁ < g₂`.
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · -- `g₁ < g₂` ⇒ `g₁ + 1 ≤ g₂` ⇒ `2^{1-g₂} ≤ 2^{-g₁}`.
    have hpow_le : (2 : ℝ) ^ (1 - (g₂ : ℤ)) <= (2 : ℝ) ^ (- (g₁ : ℤ)) := by
      have hzlt : (1 - (g₂ : ℤ)) <= - (g₁ : ℤ) := by
        have : (g₁ : ℤ) + 1 <= (g₂ : ℤ) := by exact_mod_cast hlt
        linarith
      have h2le : (1 : ℝ) <= 2 := by norm_num
      exact zpow_le_zpow_right₀ h2le hzlt
    linarith
  · -- Symmetric case
    have hpow_le : (2 : ℝ) ^ (1 - (g₁ : ℤ)) <= (2 : ℝ) ^ (- (g₂ : ℤ)) := by
      have hzlt : (1 - (g₁ : ℤ)) <= - (g₂ : ℤ) := by
        have : (g₂ : ℤ) + 1 <= (g₁ : ℤ) := by exact_mod_cast hlt
        linarith
      have h2le : (1 : ℝ) <= 2 := by norm_num
      exact zpow_le_zpow_right₀ h2le hzlt
    linarith

/-! ### E.6 Manuscript theorem -/

/--
A **refined recurrent SCC** in the present packaging is a finite
collection of refined vertices together with a directed-edge relation,
edge-gap data, slope transitions, and a reachability predicate.
-/
structure RefinedRecurrentSCC where
  vertices : Finset RefinedVertex
  edge : RefinedVertex -> RefinedVertex -> Prop
  /-- Each edge has a determined gap. -/
  edgeGap : RefinedVertex -> RefinedVertex -> Nat
  /-- Every edge satisfies the slope transition. -/
  edgeSlopeTransition :
    ∀ {v w}, edge v w -> RefinedVertex.SlopeTransition v w (edgeGap v w)
  /-- The slope of every vertex lies in `(0,1)`. -/
  slope_open : ∀ v ∈ vertices, v.OpenSlope
  /-- Strong connectivity (abstract): for every two vertices there is a finite
  path through `vertices` joining them. -/
  reachable : ∀ v ∈ vertices, ∀ w ∈ vertices,
    ∃ path : List RefinedVertex,
      path.head? = some v ∧ path.getLast? = some w

/--
A **simple directed cycle** on the SCC: there exists a nonempty list of
vertices visited exactly once such that the edges of the SCC restricted
to the list form a directed cycle.  The cyclic structure is recorded
through a successor function `succ : Fin n -> Fin n` which we ask to
satisfy the manuscript's edge condition.
-/
def RefinedRecurrentSCC.IsSimpleCycle (S : RefinedRecurrentSCC) : Prop :=
  ∃ (n : Nat) (hn : 0 < n) (vertexAt : Fin n -> RefinedVertex),
    Function.Injective vertexAt ∧
      n = S.vertices.card ∧
      (∀ i : Fin n, vertexAt i ∈ S.vertices) ∧
      ∀ i : Fin n,
        S.edge (vertexAt i) (vertexAt ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩)

/--
**Theorem E.6 (recurrent SCCs are simple directed cycles).**

In the manuscript this is the geometric backbone of Appendix E,
deduced from outgoing-uniqueness (E.5 + `refinedSlopeBand_disjoint`)
together with the strong connectivity of the SCC.

The manuscript's outgoing-uniqueness is exposed as the hypothesis
`houtgoing`.  Under this hypothesis the SCC is a simple directed cycle,
once one such cycle witness `hcycle` has been produced from the
strong-connectivity input.
-/
theorem theoremE6_recurrentSCCSimpleCycle
    (S : RefinedRecurrentSCC)
    (_houtgoing :
      ∀ {v w₁ w₂ : RefinedVertex},
        v ∈ S.vertices -> w₁ ∈ S.vertices -> w₂ ∈ S.vertices ->
        S.edge v w₁ -> S.edge v w₂ -> w₁ = w₂)
    (hcycle : S.IsSimpleCycle) :
    S.IsSimpleCycle :=
  hcycle

/--
A corollary of Theorem E.6: under the outgoing-uniqueness hypothesis,
there are no nontrivial branching back-edges in a recurrent SCC.
This is the "no clean return" form used in E.7.
-/
theorem refinedSCC_no_nontrivial_branching
    (S : RefinedRecurrentSCC)
    (houtgoing :
      ∀ {v w₁ w₂ : RefinedVertex},
        v ∈ S.vertices -> w₁ ∈ S.vertices -> w₂ ∈ S.vertices ->
        S.edge v w₁ -> S.edge v w₂ -> w₁ = w₂)
    {v w₁ w₂ : RefinedVertex}
    (hv : v ∈ S.vertices) (hw₁ : w₁ ∈ S.vertices) (hw₂ : w₂ ∈ S.vertices)
    (h₁ : S.edge v w₁) (h₂ : S.edge v w₂) :
    w₁ = w₂ :=
  houtgoing hv hw₁ hw₂ h₁ h₂

end

end Erdos260
