import Mathlib
import Erdos260.AppendixG_Ladder
import Erdos260.CNL
import Erdos260.AppendixK3_CNL

/-!
# Appendix G.6 / L.1.2: the clean-CNL cluster → ladder identification

The abstract path-level Kraft collapse is already a *proved, unconditional*
theorem in `AppendixG_Ladder.lean`:

* `pathKraft S w M root` is the depth-`M` descent-path Kraft sum of a branching
  tree `S : ℕ → Finset ℕ` with per-node weight `w`;
* `liftPathKraft_le` shows that with the lift weight `w δ = 2^{-(c·H δ)}` and any
  height dominating the exponent (`δ ≤ H δ`), this is `≤ ((1-2^{-c})⁻¹)^M`.

What was previously *assumed* (the field `cluster_le_pathKraft` of
`CNLClusterKraftData` in `AppendixK3_CNL.lean`) is the identification of the
concrete clean-CNL cluster Kraft sum with such an abstract `pathKraft`.  This
file makes that identification **genuinely provable** from a faithful
combinatorial model and isolates the irreducible manuscript residue.

## What is proved here (no `sorry`, no `axiom`)

1. **Descent-path model.** `descentPaths S M root` is the finite set of length-`M`
   descent paths of the branching tree `S`, encoded as `List ℕ`.  Each path
   carries the additive height `pathHeight H p = ∑_{δ ∈ p} H δ` (the telescoping
   BND height of manuscript Appendix G).

2. **The cluster→ladder identity (the heart of G.6).**
   ```
   cleanCNLKraftSum (descentPaths S M root) (pathHeight H) c
       = pathKraft S (fun δ => 2^{-(c·H δ)}) M root.
   ```
   This is a real theorem: the clean-CNL Kraft sum over the cluster's depth-`M`
   paths, with BND height additive along paths, **equals** the abstract ladder
   `pathKraft`.

3. **The ladder collapse, transported to the cluster.** Combining 2 with the
   proved `liftPathKraft_le` gives
   `cleanCNLKraftSum (descentPaths …) (pathHeight H) c ≤ ((1-2^{-c})⁻¹)^M`,
   genuinely derived, not assumed.

4. **Reduction of the *selected* clean-CNL family.** A
   `SelectedClusterLadderEncoding` packages the *only* residual manuscript input:
   an injective, height-additive encoding of the surviving selected clean
   transitions as descent paths of a BND-height branching tree.  From it we
   **prove**
   `cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ C_Q^M`
   (`SelectedClusterLadderEncoding.kraftSum_le`) — a real derivation of the
   K.3/L.1.2 Kraft bound from `liftPathKraft_le`.

5. **Connection to the existing K.3 interface.** The encoding yields a
   `CNLClusterKraftData (selectedTransitions T) BNDHeight c C_Q M` whose
   `cluster_le_pathKraft` field — *assumed* in `AppendixK3_CNL.lean` — is now
   discharged by the proved `cluster_le_pathKraft` below.

6. **Non-vacuousness.** `ofInjectiveLiftExponents` constructs a genuine
   depth-1 encoding from any injective lift-exponent labelling with
   `BNDHeight = liftExp`, so the reduction is inhabited and fires.

## The irreducible residue (honest)

Constructing a `SelectedClusterLadderEncoding` for the *actual* selected clean
cluster — i.e. that the surviving family after L.1.2a–d removal injects, with
additive BND height, into the descent-path family of the Type-C/Type-P
branching tree — is the deep combinatorial dynamics and is **not** proved here.
It is exactly the manuscript content that `liftPathKraft_le` cannot supply.
Everything that connects such an encoding to the final Kraft bound *is* proved.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## The descent-path model of a branching tree -/

/-- The multiplicative Kraft weight of a descent path `p` (a list of lift
exponents): the product of the per-node weights `w`. -/
def pathWeight (w : ℕ → ℝ) (p : List ℕ) : ℝ := (p.map w).prod

@[simp] theorem pathWeight_nil (w : ℕ → ℝ) : pathWeight w [] = 1 := by
  simp [pathWeight]

@[simp] theorem pathWeight_cons (w : ℕ → ℝ) (a : ℕ) (q : List ℕ) :
    pathWeight w (a :: q) = w a * pathWeight w q := by
  simp [pathWeight]

/-- The additive BND height of a descent path: the sum of the per-node heights.
This is the telescoping `ℋ_BND` of manuscript Appendix G, additive along the
ladder. -/
def pathHeight (H : ℕ → ℝ) (p : List ℕ) : ℝ := (p.map H).sum

@[simp] theorem pathHeight_nil (H : ℕ → ℝ) : pathHeight H [] = 0 := by
  simp [pathHeight]

@[simp] theorem pathHeight_cons (H : ℕ → ℝ) (a : ℕ) (q : List ℕ) :
    pathHeight H (a :: q) = H a + pathHeight H q := by
  simp [pathHeight]

/-- The finite set of length-`M` descent paths of the branching tree `S` from a
root node, encoded as lists of lift exponents.  A length-`(M+1)` path is a child
`c ∈ S root` prepended to a length-`M` path from `c`. -/
def descentPaths (S : ℕ → Finset ℕ) : ℕ → ℕ → Finset (List ℕ)
  | 0, _ => {[]}
  | (M + 1), root => (S root).biUnion (fun c => (descentPaths S M c).image (fun l => c :: l))

@[simp] theorem descentPaths_zero (S : ℕ → Finset ℕ) (root : ℕ) :
    descentPaths S 0 root = {[]} := rfl

theorem descentPaths_succ (S : ℕ → Finset ℕ) (M root : ℕ) :
    descentPaths S (M + 1) root =
      (S root).biUnion (fun c => (descentPaths S M c).image (fun l => c :: l)) := rfl

/-- The depth-`(M+1)` child branches of a fixed node are pairwise disjoint: paths
through distinct children begin with distinct heads. -/
theorem descentPaths_image_pairwiseDisjoint (S : ℕ → Finset ℕ) (M root : ℕ) :
    Set.PairwiseDisjoint (↑(S root))
      (fun c => (descentPaths S M c).image (fun l => c :: l)) := by
  intro c₁ _ c₂ _ hne
  refine Finset.disjoint_left.mpr ?_
  intro l h₁ h₂
  rcases Finset.mem_image.mp h₁ with ⟨q₁, _, rfl⟩
  rcases Finset.mem_image.mp h₂ with ⟨q₂, _, hq₂⟩
  injection hq₂ with hc _
  exact hne hc.symm

/-- **Descent-path Kraft identity.** The Kraft sum over all depth-`M` descent
paths (product weights) equals the abstract `pathKraft` of the branching tree.
This is the combinatorial backbone of the cluster → ladder identification. -/
theorem sum_pathWeight_descentPaths (S : ℕ → Finset ℕ) (w : ℕ → ℝ) :
    ∀ (M root : ℕ), ∑ p ∈ descentPaths S M root, pathWeight w p = pathKraft S w M root := by
  intro M
  induction M with
  | zero =>
      intro root
      rw [descentPaths_zero, pathKraft_zero, Finset.sum_singleton, pathWeight_nil]
  | succ n ih =>
      intro root
      rw [descentPaths_succ, pathKraft_succ,
        Finset.sum_biUnion (descentPaths_image_pairwiseDisjoint S n root)]
      refine Finset.sum_congr rfl ?_
      intro c _
      rw [Finset.sum_image (by
        intro x _ y _ h
        rw [List.cons.injEq] at h
        exact h.2)]
      calc ∑ q ∈ descentPaths S n c, pathWeight w (c :: q)
          = ∑ q ∈ descentPaths S n c, w c * pathWeight w q := by
            refine Finset.sum_congr rfl ?_
            intro q _
            rw [pathWeight_cons]
        _ = w c * ∑ q ∈ descentPaths S n c, pathWeight w q := by rw [Finset.mul_sum]
        _ = w c * pathKraft S w n c := by rw [ih c]

/-- The lift Kraft weight `w δ = 2^{-(c·H δ)}` turns the multiplicative path
weight into `2^{-(c · (additive path height))}`. -/
theorem pathWeight_two_rpow (c : ℝ) (H : ℕ → ℝ) (p : List ℕ) :
    pathWeight (fun δ => (2 : ℝ) ^ (-(c * H δ))) p = (2 : ℝ) ^ (-(c * pathHeight H p)) := by
  induction p with
  | nil => rw [pathWeight_nil, pathHeight_nil, mul_zero, neg_zero, Real.rpow_zero]
  | cons x q ih =>
      rw [pathWeight_cons, ih, pathHeight_cons]
      show (2 : ℝ) ^ (-(c * H x)) * (2 : ℝ) ^ (-(c * pathHeight H q))
        = (2 : ℝ) ^ (-(c * (H x + pathHeight H q)))
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

/-- **Cluster → ladder identity (Theorem G.6 core).** The clean-CNL Kraft sum
over the depth-`M` cluster of descent paths, weighted by the additive BND
height, *equals* the abstract ladder `pathKraft`.  No hypothesis: this is the
faithful identification that previously had to be assumed. -/
theorem cleanCNLKraftSum_descentPaths_eq_pathKraft
    (S : ℕ → Finset ℕ) (H : ℕ → ℝ) (c : ℝ) (M root : ℕ) :
    cleanCNLKraftSum (descentPaths S M root) (pathHeight H) c
      = pathKraft S (fun δ => (2 : ℝ) ^ (-(c * H δ))) M root := by
  rw [← sum_pathWeight_descentPaths S (fun δ => (2 : ℝ) ^ (-(c * H δ))) M root]
  unfold cleanCNLKraftSum
  refine Finset.sum_congr rfl ?_
  intro p _
  exact (pathWeight_two_rpow c H p).symm

/-- **Ladder collapse, transported to the cluster.** With `c > 0` and the
manuscript height domination `δ ≤ H δ`, the clean-CNL Kraft sum over the
depth-`M` descent-path cluster is at most `((1-2^{-c})⁻¹)^M`.  This is a genuine
consequence of the proved `liftPathKraft_le`, not an assumption. -/
theorem cleanCNLKraftSum_descentPaths_le
    {c : ℝ} (hc : 0 < c) (S : ℕ → Finset ℕ) (H : ℕ → ℝ)
    (hH : ∀ δ : ℕ, (δ : ℝ) ≤ H δ) (M root : ℕ) :
    cleanCNLKraftSum (descentPaths S M root) (pathHeight H) c
      ≤ ((1 - (2 : ℝ) ^ (-c))⁻¹) ^ M := by
  rw [cleanCNLKraftSum_descentPaths_eq_pathKraft]
  exact liftPathKraft_le hc S H hH M root

/-! ## The residual primitive: selected clean-CNL cluster as a descent-path family -/

/--
**The irreducible family-construction primitive (faithful form).**

An encoding of the surviving *selected* clean-CNL transition family into the
descent-path family of a BND-height branching tree.  Concretely it supplies:

* a branching tree `S` on lift exponents and its BND-height function
  `ladderHeight` (manuscript `H ≥ δ`, field `height_dom`);
* a per-transition descent-path encoding `encode`, which is injective on the
  selected family (`encode_injOn`) and lands in the depth-`M` descent paths
  (`encode_mem`);
* the additive-height coherence `BNDHeight t = ∑ (heights along encode t)`
  (`height_additive`), i.e. the BND height of a selected transition is the
  telescoped ladder height of its path;
* the one-step constant domination `(1-2^{-c})⁻¹ ≤ C_Q` (`hCQ_dom`).

This structure is *exactly* the manuscript residue (which transitions survive
L.1.2a–d and how the Type-C/Type-P branching forms the tree).  Everything that
turns it into the final Kraft bound is proved below. -/
structure SelectedClusterLadderEncoding
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ) where
  /-- The lift-exponent branching tree of the cluster. -/
  S : ℕ → Finset ℕ
  /-- The BND-height weight attached to each ladder node. -/
  ladderHeight : ℕ → ℝ
  /-- The root node of the ladder. -/
  root : ℕ
  /-- The ladder depth (cluster length). -/
  M : ℕ
  /-- The descent-path encoding of each transition. -/
  encode : CNLTransition → List ℕ
  /-- The CNL entropy slope is positive (manuscript `c > 0`). -/
  hc_pos : 0 < c
  /-- The one-step Kraft constant is dominated by `C_Q` (manuscript G.6). -/
  hCQ_dom : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ
  /-- Each ladder height dominates its lift exponent (manuscript `H ≥ δ`). -/
  height_dom : ∀ δ : ℕ, (δ : ℝ) ≤ ladderHeight δ
  /-- The encoding is injective on the selected family.

  WAVE-12/13 CORRECTION NOTE (additive; field & signature unchanged): this injectivity is the
  *over-strong* "false collapse" (it demands a 1-to-1 encoding, which is false for deep shells).
  The corrected bounded-multiplicity (`O_Q(1)`-to-one) closure is
  `CNLG35KraftSumCore.boundedMult_kraft_le_descentPaths` / `CNLG35Reconstruction`.

  WAVE-14 (additive; field & signature unchanged): the genuine bounded-multiplicity inhabitant is
  `CNLReconstructionMapCore.CNLBoundedClusterReconstruction` (via `toReconstruction`), which carries a
  multiplicity bound `μ ≥ 1` (`mult_le`) and proves the Kraft sum directly; this `encode_injOn` is
  exactly its `μ = 1` special case. -/
  encode_injOn :
    ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
      encode t₁ = encode t₂ → t₁ = t₂
  /-- Each selected transition encodes to a depth-`M` descent path. -/
  encode_mem :
    ∀ t ∈ selectedTransitions T, encode t ∈ descentPaths S M root
  /-- The transition's BND height is the additive ladder height of its path. -/
  height_additive :
    ∀ t ∈ selectedTransitions T,
      BNDHeight t = pathHeight ladderHeight (encode t)

namespace SelectedClusterLadderEncoding

variable {T : Finset CNLTransition} {BNDHeight : CNLTransition → ℝ} {c CQ : ℝ}

/-- **The discharged identification (proved `cluster_le_pathKraft`).** The
clean-CNL Kraft sum over the *selected* family is at most the abstract ladder
`pathKraft`.  This is the inequality that `CNLClusterKraftData` assumes; here it
is a theorem, proved by reindexing the selected sum along the injective encoding
into the descent paths and applying the descent-path identity. -/
theorem cluster_le_pathKraft (enc : SelectedClusterLadderEncoding T BNDHeight c CQ) :
    cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤
      pathKraft enc.S (fun δ => (2 : ℝ) ^ (-(c * enc.ladderHeight δ))) enc.M enc.root := by
  have hkey :
      cleanCNLKraftSum (descentPaths enc.S enc.M enc.root) (pathHeight enc.ladderHeight) c
        = pathKraft enc.S (fun δ => (2 : ℝ) ^ (-(c * enc.ladderHeight δ))) enc.M enc.root :=
    cleanCNLKraftSum_descentPaths_eq_pathKraft enc.S enc.ladderHeight c enc.M enc.root
  rw [← hkey]
  have himg :
      ∑ p ∈ (selectedTransitions T).image enc.encode,
          (2 : ℝ) ^ (-(c * pathHeight enc.ladderHeight p))
        = ∑ t ∈ selectedTransitions T,
            (2 : ℝ) ^ (-(c * pathHeight enc.ladderHeight (enc.encode t))) :=
    Finset.sum_image (fun t₁ ht₁ t₂ ht₂ h => enc.encode_injOn t₁ ht₁ t₂ ht₂ h)
  unfold cleanCNLKraftSum
  calc ∑ t ∈ selectedTransitions T, (2 : ℝ) ^ (-(c * BNDHeight t))
      = ∑ t ∈ selectedTransitions T,
          (2 : ℝ) ^ (-(c * pathHeight enc.ladderHeight (enc.encode t))) := by
        refine Finset.sum_congr rfl ?_
        intro t ht
        rw [enc.height_additive t ht]
    _ = ∑ p ∈ (selectedTransitions T).image enc.encode,
          (2 : ℝ) ^ (-(c * pathHeight enc.ladderHeight p)) := himg.symm
    _ ≤ ∑ p ∈ descentPaths enc.S enc.M enc.root,
          (2 : ℝ) ^ (-(c * pathHeight enc.ladderHeight p)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro p hp
          rcases Finset.mem_image.mp hp with ⟨t, ht, rfl⟩
          exact enc.encode_mem t ht
        · intro p _ _
          exact Real.rpow_nonneg (by norm_num) _

/-- **The K.3/L.1.2 Kraft bound, genuinely derived.**
`cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ C_Q^M`, obtained by
chaining the discharged identification, the proved `liftPathKraft_le`, and the
one-step constant domination — *not* assumed. -/
theorem kraftSum_le (enc : SelectedClusterLadderEncoding T BNDHeight c CQ) :
    cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ CQ ^ enc.M := by
  have hladder :
      pathKraft enc.S (fun δ => (2 : ℝ) ^ (-(c * enc.ladderHeight δ))) enc.M enc.root
        ≤ ((1 - (2 : ℝ) ^ (-c))⁻¹) ^ enc.M :=
    liftPathKraft_le enc.hc_pos enc.S enc.ladderHeight enc.height_dom enc.M enc.root
  have hpos : (0 : ℝ) ≤ (1 - (2 : ℝ) ^ (-c))⁻¹ := by
    have hlt1 : (2 : ℝ) ^ (-c) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [enc.hc_pos])
    exact le_of_lt (inv_pos.mpr (by linarith))
  have hcq : ((1 - (2 : ℝ) ^ (-c))⁻¹) ^ enc.M ≤ CQ ^ enc.M :=
    pow_le_pow_left₀ hpos enc.hCQ_dom enc.M
  exact enc.cluster_le_pathKraft.trans (hladder.trans hcq)

/-- **Connection to the existing K.3 interface.** The encoding produces a
`CNLClusterKraftData` for the selected family whose `cluster_le_pathKraft`
field — assumed in `AppendixK3_CNL.lean` — is supplied by the proved
`cluster_le_pathKraft` above. -/
def toCNLClusterKraftData (enc : SelectedClusterLadderEncoding T BNDHeight c CQ) :
    CNLClusterKraftData (selectedTransitions T) BNDHeight c CQ enc.M where
  ladderChildren := enc.S
  ladderHeight := enc.ladderHeight
  ladderRoot := enc.root
  hc_pos := enc.hc_pos
  hCQ_dom := enc.hCQ_dom
  ladderHeight_dom := enc.height_dom
  cluster_le_pathKraft := enc.cluster_le_pathKraft

/--
**Non-vacuous concrete encoding (depth-1 cluster).**

From any lift-exponent labelling `liftExp` that is injective on the selected
family, with `BNDHeight t = liftExp t`, build a genuine depth-1
`SelectedClusterLadderEncoding`.  Here the ladder is a single level whose
children are the labels of the selected transitions and whose height function is
the identity (so `δ ≤ ladderHeight δ` holds with equality, matching the
manuscript `H ≥ δ`).

This realizes the L.1.2 one-step case: the surviving clean transitions of a
single cluster level, indexed by genuinely distinct lift exponents, form exactly
the depth-1 descent paths of their label set.  It shows the residual primitive is
inhabited and the Kraft bound `≤ C_Q` fires. -/
def ofInjectiveLiftExponents
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ)
    (hc : 0 < c) (hCQ : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ)
    (liftExp : CNLTransition → ℕ)
    (hinj :
      ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
        liftExp t₁ = liftExp t₂ → t₁ = t₂)
    (hheight : ∀ t ∈ selectedTransitions T, BNDHeight t = (liftExp t : ℝ)) :
    SelectedClusterLadderEncoding T BNDHeight c CQ where
  S := fun _ => (selectedTransitions T).image liftExp
  ladderHeight := fun n => (n : ℝ)
  root := 0
  M := 1
  encode := fun t => [liftExp t]
  hc_pos := hc
  hCQ_dom := hCQ
  height_dom := fun n => le_refl _
  encode_injOn := by
    intro t₁ ht₁ t₂ ht₂ h
    rw [List.cons.injEq] at h
    exact hinj t₁ ht₁ t₂ ht₂ h.1
  encode_mem := by
    intro t ht
    rw [descentPaths_succ, Finset.mem_biUnion]
    refine ⟨liftExp t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
    rw [descentPaths_zero, Finset.mem_image]
    exact ⟨[], Finset.mem_singleton_self _, rfl⟩
  height_additive := by
    intro t ht
    rw [hheight t ht]
    simp [pathHeight]

end SelectedClusterLadderEncoding

/-! ## Headline statements -/

/-- **Headline (manuscript goal form).** For the manuscript slope `c = 1`, any
selected clean-CNL cluster admitting a ladder encoding satisfies the
K.3/L.1.2 weighted Kraft bound
`cleanCNLKraftSum (selectedTransitions T) BNDHeight 1 ≤ C_Q^M`,
genuinely derived from the abstract ladder collapse `liftPathKraft_le`. -/
theorem cleanCNLKraftSum_selectedTransitions_le_CQ_pow
    {T : Finset CNLTransition} {BNDHeight : CNLTransition → ℝ} {CQ : ℝ}
    (enc : SelectedClusterLadderEncoding T BNDHeight 1 CQ) :
    cleanCNLKraftSum (selectedTransitions T) BNDHeight 1 ≤ CQ ^ enc.M :=
  enc.kraftSum_le

/-- **Headline (general slope).** Same bound for any positive slope `c`. -/
theorem cleanCNLKraftSum_selectedTransitions_le_CQ_pow'
    {T : Finset CNLTransition} {BNDHeight : CNLTransition → ℝ} {c CQ : ℝ}
    (enc : SelectedClusterLadderEncoding T BNDHeight c CQ) :
    cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ CQ ^ enc.M :=
  enc.kraftSum_le

end

end Erdos260
