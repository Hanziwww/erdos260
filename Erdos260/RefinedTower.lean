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

/--
**Manuscript E.13 two-step slope transfer.**  Composing two slope transitions
`u → v` (gap `g₁`) and `v → w` (gap `g₂`) preserves the AP subfibre and yields
the closed-form slope `w.slope = 2^{g₁+g₂} u.slope − 2^{g₂} − 1`.  This is the
exact integer iteration of the slope recurrence `μ_next = 2^{g} μ − 1`. -/
theorem RefinedVertex.SlopeTransition.comp {u v w : RefinedVertex} {g₁ g₂ : Nat}
    (h₁ : u.SlopeTransition v g₁) (h₂ : v.SlopeTransition w g₂) :
    w.apSubfibre = u.apSubfibre ∧
      w.slope = (2 : ℝ) ^ (g₁ + g₂) * u.slope - (2 : ℝ) ^ g₂ - 1 := by
  obtain ⟨hsf1, hsl1⟩ := h₁
  obtain ⟨hsf2, hsl2⟩ := h₂
  refine ⟨by rw [hsf2, hsf1], ?_⟩
  rw [hsl2, hsl1, pow_add]
  ring

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

/-! ### Strict slope band (for outgoing uniqueness in open slopes) -/

/--
The open slope band at gap `g`: `μ ∈ (2^{-g}, 2^{1-g})`.  Since the manuscript
uses `OpenSlope = (0, 1)` (strict on both sides), it is this *strict* band
that arises when one demands `0 < w.slope < 1` for the target of an edge.
-/
def RefinedSlopeBandStrict (g : Nat) (μ : ℝ) : Prop :=
  (2 : ℝ) ^ (- (g : ℤ)) < μ ∧ μ < (2 : ℝ) ^ (1 - (g : ℤ))

/--
Strict variant of slope-band disjointness: a single slope lies in at most one
strict band.  This is what we use for outgoing-uniqueness on open-slope
vertices.
-/
theorem refinedSlopeBandStrict_disjoint {μ : ℝ} {g₁ g₂ : Nat}
    (h₁ : RefinedSlopeBandStrict g₁ μ) (h₂ : RefinedSlopeBandStrict g₂ μ) :
    g₁ = g₂ := by
  classical
  rcases h₁ with ⟨h₁lo, h₁hi⟩
  rcases h₂ with ⟨h₂lo, h₂hi⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hpow_le : (2 : ℝ) ^ (1 - (g₂ : ℤ)) <= (2 : ℝ) ^ (- (g₁ : ℤ)) := by
      have hzlt : (1 - (g₂ : ℤ)) <= - (g₁ : ℤ) := by
        have : (g₁ : ℤ) + 1 <= (g₂ : ℤ) := by exact_mod_cast hlt
        linarith
      have h2le : (1 : ℝ) <= 2 := by norm_num
      exact zpow_le_zpow_right₀ h2le hzlt
    linarith
  · have hpow_le : (2 : ℝ) ^ (1 - (g₁ : ℤ)) <= (2 : ℝ) ^ (- (g₂ : ℤ)) := by
      have hzlt : (1 - (g₁ : ℤ)) <= - (g₂ : ℤ) := by
        have : (g₂ : ℤ) + 1 <= (g₁ : ℤ) := by exact_mod_cast hlt
        linarith
      have h2le : (1 : ℝ) <= 2 := by norm_num
      exact zpow_le_zpow_right₀ h2le hzlt
    linarith

/--
Slope-transition determines a strict band on the source slope.

If both `v` and `w` have open slopes in `(0, 1)` and `w.slope = 2^g · v.slope − 1`,
then `v.slope` lies in the strict band `(2^{-g}, 2^{1-g})`.  This is the
arithmetic backbone of outgoing-uniqueness (E.5).
-/
theorem slopeTransition_to_band {v w : RefinedVertex} {g : Nat}
    (_hv : v.OpenSlope) (hw : w.OpenSlope)
    (htrans : RefinedVertex.SlopeTransition v w g) :
    RefinedSlopeBandStrict g v.slope := by
  rcases htrans with ⟨_, hslope⟩
  rcases hw with ⟨hw_pos, hw_lt⟩
  have h2g_pos : (0 : ℝ) < (2 : ℝ) ^ g := by positivity
  have h_pow_eq_neg : (2 : ℝ) ^ (-(g : ℤ)) = (1 : ℝ) / (2 : ℝ) ^ g := by
    rw [zpow_neg, zpow_natCast, one_div]
  have h_pow_eq_one_sub : (2 : ℝ) ^ (1 - (g : ℤ)) = (2 : ℝ) / (2 : ℝ) ^ g := by
    have h_eq : (1 : ℤ) - (g : ℤ) = 1 + (-(g : ℤ)) := by ring
    rw [h_eq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, zpow_neg,
        zpow_natCast, div_eq_mul_inv]
  refine ⟨?_, ?_⟩
  · -- `2^{-g} < v.slope`, i.e. `1 < 2^g · v.slope`.
    rw [h_pow_eq_neg, div_lt_iff₀ h2g_pos]
    linarith
  · -- `v.slope < 2^{1-g}`, i.e. `2^g · v.slope < 2`.
    rw [h_pow_eq_one_sub, lt_div_iff₀ h2g_pos]
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

/-! ### E.6 supporting structure: coherent recurrent SCCs

In the manuscript a *refined recurrent* SCC has more structure than the bare
`RefinedRecurrentSCC` records: the vertices share the AP subfibre, threshold
layer, fibre, and terminal label; each vertex has a forward edge inside the
SCC; and from any vertex one can reach any other along a real edge-path.

`Coherent` captures exactly this structural content.  Theorem E.6 below proves
that every coherent SCC is a simple directed cycle, without any further
axiomatic hypothesis.
-/

/--
**Coherence of a refined recurrent SCC.**

The manuscript's hypothesis on a "refined recurrent SCC at layer J on a common
AP subfibre" is:

1. the vertex set is nonempty;
2. all vertices share `apSubfibre`, `layer`, `fibre`, and `terminal`;
3. every vertex has an outgoing edge inside the SCC;
4. the SCC is strongly connected by edge-paths.

These are *not* additional analytic assumptions on E.6 itself.  They are
properties of the underlying finite graph that the manuscript implicitly
maintains throughout Appendix E.
-/
structure RefinedRecurrentSCC.Coherent (S : RefinedRecurrentSCC) : Prop where
  /-- The SCC has at least one vertex. -/
  nonempty : S.vertices.Nonempty
  /-- All vertices share the AP subfibre. -/
  commonSubfibre : ∃ k : Nat, ∀ v ∈ S.vertices, v.apSubfibre = k
  /-- All vertices share the threshold layer. -/
  commonLayer : ∃ ℓ : Nat, ∀ v ∈ S.vertices, v.layer = ℓ
  /-- All vertices share the fibre coordinate. -/
  commonFibre : ∃ f : Nat, ∀ v ∈ S.vertices, v.fibre = f
  /-- All vertices share the optional terminal label. -/
  commonTerminal : ∃ t : Option TerminalLabel, ∀ v ∈ S.vertices, v.terminal = t
  /-- Every vertex has an outgoing edge inside the SCC. -/
  outEdge : ∀ v ∈ S.vertices, ∃ w ∈ S.vertices, S.edge v w
  /-- Strong connectivity via real edge-paths inside the SCC. -/
  succReachable :
    ∀ (v w : { v : RefinedVertex // v ∈ S.vertices }),
      ∃ n : Nat, ∃ p : Fin (n + 1) → { v : RefinedVertex // v ∈ S.vertices },
        p 0 = v ∧ p (Fin.last n) = w ∧
        ∀ i : Fin n, S.edge (p i.castSucc).1 (p i.succ).1

/--
**Theorem E.5 (outgoing uniqueness).**

Within a coherent refined recurrent SCC, the outgoing edge of any vertex is
uniquely determined.

The proof is the manuscript argument: open-slope source + slope-transition +
disjointness of strict slope bands forces both targets to have the same gap,
hence the same slope, the same AP subfibre, and (by the common-coordinate
fields of `Coherent`) the same layer, fibre, and terminal label.
-/
theorem theoremE5_outgoingUnique
    {S : RefinedRecurrentSCC} (hC : S.Coherent)
    {v w₁ w₂ : RefinedVertex}
    (hv : v ∈ S.vertices) (hw₁ : w₁ ∈ S.vertices) (hw₂ : w₂ ∈ S.vertices)
    (h₁ : S.edge v w₁) (h₂ : S.edge v w₂) :
    w₁ = w₂ := by
  -- Open slopes from `slope_open`.
  have hv_open := S.slope_open v hv
  have hw₁_open := S.slope_open w₁ hw₁
  have hw₂_open := S.slope_open w₂ hw₂
  -- Slope transitions for both edges.
  have htrans₁ := S.edgeSlopeTransition h₁
  have htrans₂ := S.edgeSlopeTransition h₂
  -- Apply strict band lemma; band uniqueness forces equal gaps.
  have hband₁ := slopeTransition_to_band hv_open hw₁_open htrans₁
  have hband₂ := slopeTransition_to_band hv_open hw₂_open htrans₂
  have hgap_eq : S.edgeGap v w₁ = S.edgeGap v w₂ :=
    refinedSlopeBandStrict_disjoint hband₁ hband₂
  -- Read off equalities of all five coordinates.
  rcases htrans₁ with ⟨h_sub₁, h_slope₁⟩
  rcases htrans₂ with ⟨h_sub₂, h_slope₂⟩
  rcases hC.commonLayer with ⟨ℓ, hLayer⟩
  rcases hC.commonFibre with ⟨f, hFibre⟩
  rcases hC.commonTerminal with ⟨t, hTerm⟩
  have h_slope_eq : w₁.slope = w₂.slope := by rw [h_slope₁, h_slope₂, hgap_eq]
  have h_sub_eq : w₁.apSubfibre = w₂.apSubfibre := by rw [h_sub₁, h_sub₂]
  have h_layer_eq : w₁.layer = w₂.layer := by rw [hLayer w₁ hw₁, hLayer w₂ hw₂]
  have h_fibre_eq : w₁.fibre = w₂.fibre := by rw [hFibre w₁ hw₁, hFibre w₂ hw₂]
  have h_term_eq : w₁.terminal = w₂.terminal := by rw [hTerm w₁ hw₁, hTerm w₂ hw₂]
  -- Destructure both vertices and substitute all five coordinate equalities.
  obtain ⟨⟨f₁, ℓ₁, t₁⟩, asf₁, sl₁⟩ := w₁
  obtain ⟨⟨f₂, ℓ₂, t₂⟩, asf₂, sl₂⟩ := w₂
  subst h_fibre_eq
  subst h_layer_eq
  subst h_term_eq
  subst h_sub_eq
  subst h_slope_eq
  rfl

/--
The successor function on the subtype of vertices inside a coherent SCC,
chosen via `Classical.choose` from the `outEdge` field.
-/
noncomputable def RefinedRecurrentSCC.succOn
    {S : RefinedRecurrentSCC} (hC : S.Coherent)
    (v : { v : RefinedVertex // v ∈ S.vertices }) :
    { v : RefinedVertex // v ∈ S.vertices } :=
  ⟨Classical.choose (hC.outEdge v.1 v.2),
    (Classical.choose_spec (hC.outEdge v.1 v.2)).1⟩

/-- The successor of a vertex is connected to it by an edge in the SCC. -/
theorem RefinedRecurrentSCC.edge_succOn
    {S : RefinedRecurrentSCC} (hC : S.Coherent)
    (v : { v : RefinedVertex // v ∈ S.vertices }) :
    S.edge v.1 (S.succOn hC v).1 :=
  (Classical.choose_spec (hC.outEdge v.1 v.2)).2

/--
Outgoing uniqueness (Theorem E.5) lifted to the subtype: any vertex connected
to `v` by an edge equals `succOn v`.
-/
theorem RefinedRecurrentSCC.succOn_unique
    {S : RefinedRecurrentSCC} (hC : S.Coherent)
    (v w : { v : RefinedVertex // v ∈ S.vertices })
    (h : S.edge v.1 w.1) :
    w = S.succOn hC v := by
  apply Subtype.ext
  exact theoremE5_outgoingUnique hC v.2 w.2 (S.succOn hC v).2 h
    (S.edge_succOn hC v)

/--
An edge path inside a coherent SCC is exactly the orbit of `succOn`.

If `p : Fin (n + 1) → vertices` traces a real edge-path with `p 0` as
starting vertex, then `p i = succOn^i (p 0)` for every index `i`.
-/
theorem RefinedRecurrentSCC.path_iterate
    {S : RefinedRecurrentSCC} (hC : S.Coherent)
    {n : Nat} (p : Fin (n + 1) → { v : RefinedVertex // v ∈ S.vertices })
    (hedges : ∀ i : Fin n, S.edge (p i.castSucc).1 (p i.succ).1)
    (i : Fin (n + 1)) :
    p i = (S.succOn hC)^[i.val] (p 0) := by
  induction i using Fin.induction with
  | zero => simp
  | succ j ih =>
    have h_edge := hedges j
    have h_succ : S.succOn hC (p j.castSucc) = p j.succ :=
      (S.succOn_unique hC (p j.castSucc) (p j.succ) h_edge).symm
    -- Goal: `p j.succ = (S.succOn hC)^[j.succ.val] (p 0)`.
    have h_val : j.succ.val = j.castSucc.val + 1 := by
      simp
    rw [h_val, Function.iterate_succ_apply', ← ih]
    exact h_succ.symm

/--
**Theorem E.6 (recurrent SCCs are simple directed cycles).**

Every coherent refined recurrent SCC is a simple directed cycle.  The
proof: iterate `succOn` from any base vertex `v₀`.  By edge-path reachability
together with outgoing uniqueness, the iteration returns to `v₀` after some
positive period `p`, and the orbit of size `p` exhausts the vertex set.
Minimality of `p` forces the iterates on `[0, p)` to be pairwise distinct, so
the orbit packages as a `Fin p → vertices` injection covering everything.
-/
theorem theoremE6_recurrentSCCSimpleCycle
    (S : RefinedRecurrentSCC) (hC : S.Coherent) :
    S.IsSimpleCycle := by
  classical
  -- Base vertex.
  rcases hC.nonempty with ⟨v₀_val, v₀_mem⟩
  set v₀ : { v : RefinedVertex // v ∈ S.vertices } := ⟨v₀_val, v₀_mem⟩
  -- Step 1: positive return time exists.
  have hReturn : ∃ n : Nat, 0 < n ∧ (S.succOn hC)^[n] v₀ = v₀ := by
    set w := S.succOn hC v₀
    rcases hC.succReachable w v₀ with ⟨n, p, hp0, hplast, hedges⟩
    have h_path := S.path_iterate hC p hedges (Fin.last n)
    -- `p (Fin.last n) = (S.succOn hC)^[n] (p 0)`; substitute endpoints.
    have h_iter_n : (S.succOn hC)^[n] w = v₀ := by
      have := h_path
      rw [hp0, hplast, Fin.val_last] at this
      exact this.symm
    refine ⟨n + 1, Nat.succ_pos n, ?_⟩
    rw [Function.iterate_succ_apply]
    -- `(S.succOn hC)^[n] (S.succOn hC v₀) = (S.succOn hC)^[n] w = v₀`.
    exact h_iter_n
  -- Step 2: define the period as the minimum positive return time.
  have hExists : ∃ n, 0 < n ∧ (S.succOn hC)^[n] v₀ = v₀ := hReturn
  letI : DecidablePred (fun n => 0 < n ∧ (S.succOn hC)^[n] v₀ = v₀) :=
    Classical.decPred _
  set pd := Nat.find hExists with hpd_def
  have hpd_spec : 0 < pd ∧ (S.succOn hC)^[pd] v₀ = v₀ := Nat.find_spec hExists
  obtain ⟨hpd_pos, hpd_iter⟩ := hpd_spec
  have hpd_min : ∀ m, m < pd →
      ¬ (0 < m ∧ (S.succOn hC)^[m] v₀ = v₀) := fun m hm =>
    Nat.find_min hExists hm
  -- Step 3: every multiple of `pd` is also a return time.
  have hpd_kiter : ∀ k : Nat, (S.succOn hC)^[pd * k] v₀ = v₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, hpd_iter]
      exact ih
  -- Step 4: orbit injectivity on `[0, pd)`.
  have h_inj_orbit :
      ∀ (i j : Fin pd),
        (S.succOn hC)^[i.val] v₀ = (S.succOn hC)^[j.val] v₀ → i = j := by
    -- Auxiliary statement with `i.val ≤ j.val`.
    suffices h_aux :
        ∀ (i j : Fin pd), i.val ≤ j.val →
          (S.succOn hC)^[i.val] v₀ = (S.succOn hC)^[j.val] v₀ → i = j by
      intro i j h_eq
      by_cases hle : i.val ≤ j.val
      · exact h_aux i j hle h_eq
      · have hle' : j.val ≤ i.val := Nat.le_of_lt (Nat.lt_of_not_le hle)
        exact (h_aux j i hle' h_eq.symm).symm
    intro i j hle h_eq
    by_contra h_ne
    have hlt : i.val < j.val := by
      rcases lt_or_eq_of_le hle with hlt' | heq
      · exact hlt'
      · exact absurd (Fin.ext heq) h_ne
    have h_jval_lt : j.val < pd := j.isLt
    -- Apply `succOn^[pd - j.val]` to both sides.
    have h_apply : (S.succOn hC)^[pd - j.val] ((S.succOn hC)^[i.val] v₀) =
                   (S.succOn hC)^[pd - j.val] ((S.succOn hC)^[j.val] v₀) := by
      rw [h_eq]
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at h_apply
    -- `(pd - j.val) + j.val = pd`, hence the right-hand iterate equals `v₀`.
    have h_pd_eq : pd - j.val + j.val = pd := by omega
    rw [h_pd_eq, hpd_iter] at h_apply
    -- The remaining iterate index is a positive return time strictly less than `pd`,
    -- contradicting the minimality of `pd`.
    have h_ki_pos : 0 < pd - j.val + i.val := by omega
    have h_ki_lt : pd - j.val + i.val < pd := by omega
    exact hpd_min _ h_ki_lt ⟨h_ki_pos, h_apply⟩
  -- Step 5: vertex enumeration along the orbit.
  set vertexAt : Fin pd → RefinedVertex :=
    fun i => ((S.succOn hC)^[i.val] v₀).1
  have h_mem : ∀ i : Fin pd, vertexAt i ∈ S.vertices :=
    fun i => ((S.succOn hC)^[i.val] v₀).2
  have h_inj : Function.Injective vertexAt := by
    intro i j h_eq
    apply h_inj_orbit i j
    exact Subtype.ext h_eq
  -- Step 6: the orbit covers the whole vertex set, hence `pd = vertices.card`.
  have h_card_pd : pd = S.vertices.card := by
    set image_subtype : Finset { v : RefinedVertex // v ∈ S.vertices } :=
      (Finset.univ : Finset (Fin pd)).image
        (fun i => (S.succOn hC)^[i.val] v₀) with himage_def
    -- Image cardinality is `pd` by orbit injectivity.
    have h_image_card : image_subtype.card = pd := by
      rw [himage_def, Finset.card_image_of_injective _ ?_, Finset.card_univ,
          Fintype.card_fin]
      intro i j h
      apply h_inj_orbit
      exact h
    -- Image covers `S.vertices.attach` by `succReachable`.
    have h_cover : S.vertices.attach ⊆ image_subtype := by
      intro w _
      rcases hC.succReachable v₀ w with ⟨n, p, hp0, hplast, hedges⟩
      have h_path := S.path_iterate hC p hedges (Fin.last n)
      rw [hp0, hplast, Fin.val_last] at h_path
      -- `(S.succOn hC)^[n] v₀ = w`.
      set m := n % pd with hm_def
      have hm_lt : m < pd := Nat.mod_lt n hpd_pos
      have h_iter_m : (S.succOn hC)^[m] v₀ = w := by
        have h_n_eq : n = m + pd * (n / pd) := by
          have := Nat.div_add_mod n pd
          omega
        have h_iter_n_eq : (S.succOn hC)^[n] v₀ = w := h_path.symm
        rw [h_n_eq, Function.iterate_add_apply, hpd_kiter (n / pd)] at h_iter_n_eq
        exact h_iter_n_eq
      rw [himage_def, Finset.mem_image]
      exact ⟨⟨m, hm_lt⟩, Finset.mem_univ _, h_iter_m⟩
    -- Image cardinality equals `S.vertices.card`.
    have h_attach_card : S.vertices.attach.card = S.vertices.card :=
      Finset.card_attach
    have h_image_le : image_subtype.card ≤ S.vertices.attach.card := by
      apply Finset.card_le_card
      intro x _
      exact Finset.mem_attach _ _
    have h_attach_le : S.vertices.attach.card ≤ image_subtype.card :=
      Finset.card_le_card h_cover
    have h_card_attach_eq : image_subtype.card = S.vertices.attach.card :=
      le_antisymm h_image_le h_attach_le
    rw [← h_image_card, h_card_attach_eq, h_attach_card]
  -- Step 7: the cyclic edge condition.
  have h_edge_succ :
      ∀ i : Fin pd,
        S.edge (vertexAt i)
          (vertexAt ⟨(i.val + 1) % pd, Nat.mod_lt _ hpd_pos⟩) := by
    intro i
    show S.edge ((S.succOn hC)^[i.val] v₀).1
                ((S.succOn hC)^[(i.val + 1) % pd] v₀).1
    by_cases h_eq : i.val + 1 = pd
    · -- Wrap-around step: the cycle returns to `v₀`.
      have h_mod : (i.val + 1) % pd = 0 := by rw [h_eq, Nat.mod_self]
      rw [h_mod]
      show S.edge ((S.succOn hC)^[i.val] v₀).1 ((S.succOn hC)^[0] v₀).1
      rw [Function.iterate_zero_apply]
      -- `succOn (succOn^[i.val] v₀) = succOn^[i.val + 1] v₀ = succOn^[pd] v₀ = v₀`.
      have h_succ_eq : S.succOn hC ((S.succOn hC)^[i.val] v₀) = v₀ := by
        have h_iter_succ : (S.succOn hC)^[i.val + 1] v₀ = v₀ := by
          rw [h_eq]; exact hpd_iter
        rw [Function.iterate_succ_apply'] at h_iter_succ
        exact h_iter_succ
      have h_edge := S.edge_succOn hC ⟨_, ((S.succOn hC)^[i.val] v₀).2⟩
      -- The edge from `succOn^[i.val] v₀` to its successor; that successor is `v₀`.
      simp only [h_succ_eq] at h_edge
      exact h_edge
    · -- Regular step: the successor is the next iterate.
      have h_lt : i.val + 1 < pd := by
        have hi : i.val < pd := i.isLt
        omega
      rw [Nat.mod_eq_of_lt h_lt]
      show S.edge ((S.succOn hC)^[i.val] v₀).1
                  ((S.succOn hC)^[i.val + 1] v₀).1
      rw [Function.iterate_succ_apply']
      exact S.edge_succOn hC _
  -- Package as `IsSimpleCycle`.
  refine ⟨pd, hpd_pos, vertexAt, h_inj, h_card_pd, h_mem, h_edge_succ⟩

/--
A corollary of Theorem E.6: under outgoing uniqueness, there are no
nontrivial branching back-edges in a recurrent SCC.  This is the
"no clean return" form used in E.7.

The hypothesis `houtgoing` can be supplied by `theoremE5_outgoingUnique`
applied to any `S.Coherent` witness; we keep it parametric here so the
corollary remains usable when only outgoing uniqueness is in hand.
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

/--
Appendix E.7 clean-return impossibility, recurrent-edge core.

Inside a coherent refined recurrent SCC, a clean excursion that leaves a cycle
vertex and returns through another recurrent outgoing edge cannot be distinct
from the cycle edge: outgoing uniqueness forces the two continuations to agree.
Long-overlap realignments are routed separately through the Fine-Wilf/run
package; this theorem closes the recurrent outgoing-edge contradiction used by
the E.7 tower case.
-/
theorem AppendixE_CleanReturn
    {S : RefinedRecurrentSCC} (hC : S.Coherent)
    {v cycleNext excursionNext : RefinedVertex}
    (hv : v ∈ S.vertices)
    (hcycleNext : cycleNext ∈ S.vertices)
    (hexcursionNext : excursionNext ∈ S.vertices)
    (hcycle : S.edge v cycleNext)
    (hexcursion : S.edge v excursionNext) :
    cycleNext = excursionNext :=
  theoremE5_outgoingUnique hC hv hcycleNext hexcursionNext hcycle hexcursion

end

end Erdos260
