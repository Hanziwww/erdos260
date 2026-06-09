import Mathlib
import Erdos260.CNLClusterLadder
import Erdos260.AppendixG_CNLClassifier

/-!
# Appendix G.6 / L.1.2: constructing the `SelectedClusterLadderEncoding`

`CNLClusterLadder.lean` proved the cluster→ladder identity and the K.3/L.1.2 Kraft
bound `cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ C_Q^M`
*given* a `SelectedClusterLadderEncoding` — an injective, BND-height-additive map
of the surviving selected clean family into the depth-`M` descent paths
`descentPaths S M root` of a BND-height branching tree.  The residual primitive it
isolated is the **existence** of that encoding for the actual cluster.

This file **builds** that encoding as far as it is genuinely derivable, by
manufacturing it from the *per-step ladder data* of the manuscript's
"reconstruction by induction along the cluster" (Lemma L.1.2): a node-assignment
`nodeOf t i` (the reconstructed lift-state node of transition `t` at cluster depth
`i`), a children tree `S`, a BND-height function `ladderHeight`, plus local
coherence, injectivity and additivity.  Everything that turns such per-step data
into a full `SelectedClusterLadderEncoding` — hence into the final Kraft bound — is
proved here with no `sorry`/`axiom`.

## What is genuinely proved here

1. **Threaded descent-path builder (`descentBranch`).**  From a node sequence
   `node : ℕ → ℕ` we build the length-`M` path `[node 1, …, node M]` and prove,
   from local coherence `node (i+1) ∈ S (node i)`, that it is a genuine member of
   `descentPaths S M (node 0)` (`descentBranch_mem`), with additive ladder height
   `pathHeight ladderHeight (descentBranch node M) = ∑_{i<M} ladderHeight (node (i+1))`
   (`pathHeight_descentBranch`).  This is the depth-`M` tree geometry of L.1.2 that
   `CNLClusterLadder.lean` did not contain.

2. **General-tree depth-`M` constructor (`ofCoherentLadderNodes`).**  Assembles a
   `SelectedClusterLadderEncoding` from a coherent injective height-additive node
   coordinatization of the selected family, over an **arbitrary** branching tree
   `S` (the Type-C/Type-P tree).  This is the genuine advance over the depth-1
   `ofInjectiveLiftExponents` already in `CNLClusterLadder.lean`.

3. **Constant-base depth-`M` constructor (`ofInjectiveLadderWord`).**  The
   "constant-base alphabet" case (ordinary/TC bounded code of L.1.2): any
   per-transition code word of fixed length `M`, injective on the selected family,
   with BND height equal to its additive ladder height, assembles into an encoding.
   Backed by the constant-children membership lemma `mem_descentPaths_const`.

4. **Bridge strict-descent injectivity engine (`bridgeExp_nat_injective`,
   `ofBridgeLadderWord`).**  The manuscript's injectivity at Type-P positions rests
   on the strict descent of bridge exponents (Lemma G.3 = `bridgeExp_strictAnti`):
   the colliding suffix index is unique because the exponents are distinct.  We turn
   that proved `StrictAnti` into `Function.Injective` of the exponent labelling and
   use it to **derive** (not assume) injectivity of a depth-`M` bridge-exponent code
   from injectivity of the raw label word.

5. **Isolated residual primitive (`ClusterLadderCoordinatization`).**  The smallest
   irreducible input — the per-step coherent injective height-additive
   coordinatization of the surviving selected cluster — is packaged as a structure,
   from which the encoding and the final Kraft bound `≤ C_Q^M` are proved
   (`toEncoding`, `kraftSum_le`, `toCNLClusterKraftData`).

6. **Non-vacuousness at all depths (`ofReplicatedLiftExponent`).**  A genuine
   depth-`(m+1)` encoding from any injective lift-exponent labelling, showing the
   construction fires beyond depth 1.

## The irreducible residue (honest)

What is **not** proved is that the *actual* selected clean cluster admits such a
coordinatization, i.e. that after L.1.2a–d removal the surviving family is the
descent tree of the Type-C/Type-P branching with additive BND height and a
genuinely injective reconstruction.  That is the deep combinatorial dynamics
(L.1.2a–d removal geometry, the (G.7)–(G.8) child congruence, the
`O_Q(1)`-to-one reconstruction collapsed to injective on the clean subfamily).
This file reduces the original residual ("∃ a `SelectedClusterLadderEncoding`") to
the strictly more explicit, faithful, and local residual
"∃ a `ClusterLadderCoordinatization`", and proves the entire reduction.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## The threaded descent-path builder -/

/-- The depth-`M` descent path threaded through a tree by a node sequence
`node : ℕ → ℕ`: the list `[node 1, node 2, …, node M]`.  `node 0` is the root,
`node (i+1)` is the chosen child at depth `i`. -/
def descentBranch : (ℕ → ℕ) → ℕ → List ℕ
  | _, 0 => []
  | node, (m + 1) => node 1 :: descentBranch (fun i => node (i + 1)) m

@[simp] theorem descentBranch_zero (node : ℕ → ℕ) : descentBranch node 0 = [] := rfl

theorem descentBranch_succ (node : ℕ → ℕ) (m : ℕ) :
    descentBranch node (m + 1) = node 1 :: descentBranch (fun i => node (i + 1)) m := rfl

/-- **Membership in the descent-path family from local coherence.**  If each chosen
child threads through the tree (`node (i+1) ∈ S (node i)` for `i < M`), then the
threaded path `descentBranch node M` is a genuine depth-`M` descent path from the
root `node 0`.  This is the tree-membership core of Lemma L.1.2's reconstruction. -/
theorem descentBranch_mem (S : ℕ → Finset ℕ) :
    ∀ (m : ℕ) (node : ℕ → ℕ),
      (∀ i, i < m → node (i + 1) ∈ S (node i)) →
        descentBranch node m ∈ descentPaths S m (node 0) := by
  intro m
  induction m with
  | zero =>
      intro node _
      rw [descentBranch_zero, descentPaths_zero]
      exact Finset.mem_singleton_self _
  | succ n ih =>
      intro node hchain
      rw [descentBranch_succ, descentPaths_succ]
      refine Finset.mem_biUnion.mpr ⟨node 1, hchain 0 (Nat.succ_pos n), ?_⟩
      refine Finset.mem_image.mpr ⟨descentBranch (fun i => node (i + 1)) n, ?_, rfl⟩
      exact ih (fun i => node (i + 1)) (fun i hi => hchain (i + 1) (Nat.succ_lt_succ hi))

/-- **Additive ladder height of a threaded descent path.**  The telescoping BND
height of `descentBranch node M` is the sum of the per-node ladder heights
recorded along it — the additive `ℋ_BND` of Appendix G. -/
theorem pathHeight_descentBranch (H : ℕ → ℝ) :
    ∀ (m : ℕ) (node : ℕ → ℕ),
      pathHeight H (descentBranch node m) = ∑ i ∈ Finset.range m, H (node (i + 1)) := by
  intro m
  induction m with
  | zero =>
      intro node
      rw [descentBranch_zero, pathHeight_nil, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
      intro node
      rw [descentBranch_succ, pathHeight_cons, ih (fun i => node (i + 1)),
        Finset.sum_range_succ']
      simp only [zero_add]
      exact add_comm _ _

/-! ## Constant-children membership (the constant-base alphabet of L.1.2) -/

/-- **Constant-children membership.**  When every node has the same children set
`C`, a list of length `M` with all entries in `C` is a depth-`M` descent path.
This is the "constant-base ordinary/TC alphabet" branch of Lemma L.1.2. -/
theorem mem_descentPaths_const (C : Finset ℕ) :
    ∀ (p : List ℕ) (root : ℕ), (∀ x ∈ p, x ∈ C) →
      p ∈ descentPaths (fun _ => C) p.length root := by
  intro p
  induction p with
  | nil =>
      intro root _
      simp only [List.length_nil, descentPaths_zero]
      exact Finset.mem_singleton_self _
  | cons a q ih =>
      intro root hmem
      simp only [List.length_cons]
      rw [descentPaths_succ]
      refine Finset.mem_biUnion.mpr ⟨a, hmem a (List.mem_cons_self), ?_⟩
      refine Finset.mem_image.mpr ⟨q, ?_, rfl⟩
      exact ih a (fun x hx => hmem x (List.mem_cons_of_mem a hx))

/-! ## Path-height bookkeeping helpers -/

theorem pathHeight_append (H : ℕ → ℝ) (p q : List ℕ) :
    pathHeight H (p ++ q) = pathHeight H p + pathHeight H q := by
  unfold pathHeight
  rw [List.map_append, List.sum_append]

/-- The additive ladder height of a `range`-indexed code word. -/
theorem pathHeight_map_range (H : ℕ → ℝ) (f : ℕ → ℕ) :
    ∀ M, pathHeight H ((List.range M).map f) = ∑ i ∈ Finset.range M, H (f i) := by
  intro M
  induction M with
  | zero => simp [pathHeight]
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, pathHeight_append,
        ih, Finset.sum_range_succ, pathHeight_cons, pathHeight_nil, add_zero]

/-- The additive ladder height of a constant (replicated) code word: `M · H x`. -/
theorem pathHeight_replicate (H : ℕ → ℝ) (M x : ℕ) :
    pathHeight H (List.replicate M x) = (M : ℝ) * H x := by
  unfold pathHeight
  rw [List.map_replicate, List.sum_replicate, nsmul_eq_mul]

/-! ## A list-map injectivity helper (for the bridge-descent engine) -/

/-- `List.map f` is left-cancellable when `f` is injective. -/
theorem list_map_left_injective {f : ℕ → ℕ} (hf : Function.Injective f) :
    ∀ {a b : List ℕ}, a.map f = b.map f → a = b
  | [], [], _ => rfl
  | [], (_ :: _), h => by simp at h
  | (_ :: _), [], h => by simp at h
  | (x :: xs), (y :: ys), h => by
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hf h.1, list_map_left_injective hf h.2]

/-! ## The general-tree depth-`M` constructor (the genuine advance) -/

/--
**General-tree depth-`M` encoding constructor.**

Assembles a `SelectedClusterLadderEncoding` from a *coherent ladder
coordinatization* of the selected family over an arbitrary branching tree `S`
(the Type-C/Type-P tree of the manuscript):

* `nodeOf t i` is the reconstructed lift-state node of transition `t` at cluster
  depth `i`, with common root `nodeOf t 0 = root` (`hroot`);
* `hcoh` is the local child-coherence `nodeOf t (i+1) ∈ S (nodeOf t i)` — the
  (G.7)–(G.8) child congruence along the cluster;
* `hinj` is injectivity of the threaded descent path on the selected family — the
  reconstruction collapsed to injective on the clean surviving subfamily;
* `hheight` is the additive-height coherence — the telescoping BND height.

From these the membership, injectivity and additive-height fields of
`SelectedClusterLadderEncoding` are all *proved* (via `descentBranch_mem` and
`pathHeight_descentBranch`).  This is the depth-`M`, general-tree generalization of
the depth-1 `ofInjectiveLiftExponents`. -/
def SelectedClusterLadderEncoding.ofCoherentLadderNodes
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ)
    (hc : 0 < c) (hCQ : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ)
    (S : ℕ → Finset ℕ) (ladderHeight : ℕ → ℝ) (root M : ℕ)
    (hdom : ∀ δ : ℕ, (δ : ℝ) ≤ ladderHeight δ)
    (nodeOf : CNLTransition → ℕ → ℕ)
    (hroot : ∀ t ∈ selectedTransitions T, nodeOf t 0 = root)
    (hcoh : ∀ t ∈ selectedTransitions T, ∀ i, i < M → nodeOf t (i + 1) ∈ S (nodeOf t i))
    (hinj :
      ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
        descentBranch (nodeOf t₁) M = descentBranch (nodeOf t₂) M → t₁ = t₂)
    (hheight :
      ∀ t ∈ selectedTransitions T,
        BNDHeight t = ∑ i ∈ Finset.range M, ladderHeight (nodeOf t (i + 1))) :
    SelectedClusterLadderEncoding T BNDHeight c CQ where
  S := S
  ladderHeight := ladderHeight
  root := root
  M := M
  encode := fun t => descentBranch (nodeOf t) M
  hc_pos := hc
  hCQ_dom := hCQ
  height_dom := hdom
  encode_injOn := hinj
  encode_mem := by
    intro t ht
    have hmem := descentBranch_mem S M (nodeOf t) (fun i hi => hcoh t ht i hi)
    rwa [hroot t ht] at hmem
  height_additive := by
    intro t ht
    rw [hheight t ht]
    exact (pathHeight_descentBranch ladderHeight M (nodeOf t)).symm

/-! ## The constant-base depth-`M` constructor -/

/--
**Constant-base depth-`M` encoding constructor.**

The "constant-base alphabet" case of Lemma L.1.2: any per-transition code word
`code t` of fixed length `M`, injective on the selected family, whose BND height is
its additive ladder height, assembles into a depth-`M` `SelectedClusterLadderEncoding`
on the constant tree whose children at every node are the recorded code symbols of
the selected family.  Membership is supplied by `mem_descentPaths_const`. -/
def SelectedClusterLadderEncoding.ofInjectiveLadderWord
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ)
    (hc : 0 < c) (hCQ : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ)
    (ladderHeight : ℕ → ℝ) (root M : ℕ)
    (hdom : ∀ δ : ℕ, (δ : ℝ) ≤ ladderHeight δ)
    (code : CNLTransition → List ℕ)
    (hlen : ∀ t ∈ selectedTransitions T, (code t).length = M)
    (hinj :
      ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
        code t₁ = code t₂ → t₁ = t₂)
    (hheight :
      ∀ t ∈ selectedTransitions T, BNDHeight t = pathHeight ladderHeight (code t)) :
    SelectedClusterLadderEncoding T BNDHeight c CQ where
  S := fun _ => (selectedTransitions T).biUnion (fun u => (code u).toFinset)
  ladderHeight := ladderHeight
  root := root
  M := M
  encode := code
  hc_pos := hc
  hCQ_dom := hCQ
  height_dom := hdom
  encode_injOn := hinj
  encode_mem := by
    intro t ht
    have hsub :
        ∀ x ∈ code t, x ∈ (selectedTransitions T).biUnion (fun u => (code u).toFinset) := by
      intro x hx
      exact Finset.mem_biUnion.mpr ⟨t, ht, List.mem_toFinset.mpr hx⟩
    have hmem :=
      mem_descentPaths_const
        ((selectedTransitions T).biUnion (fun u => (code u).toFinset)) (code t) root hsub
    rwa [hlen t ht] at hmem
  height_additive := hheight

/-! ## Bridge strict-descent injectivity engine (genuine use of `bridgeExp_strictAnti`) -/

/-- **Bridge exponents are an injective labelling (Lemma G.3).**  A natural-number
realization `E` of the integer bridge exponents `A_s - A_t + σ^-_t`, with the
recent-window slide identity and positive leaving gaps, is strictly decreasing by
`bridgeExp_strictAnti`, hence injective.  This is the proved engine behind "the
colliding suffix index `t = n` is unique because the exponents are distinct." -/
theorem bridgeExp_nat_injective {E : ℕ → ℕ} {g sm gOld : ℕ → ℤ} {s : ℕ}
    (hE : ∀ t, (E t : ℤ) = bridgeExp g sm s t)
    (hwin : ∀ t, sm (t + 1) - sm t = g t - gOld t)
    (hpos : ∀ t, 0 < gOld t) :
    Function.Injective E := by
  have hSAz : StrictAnti (fun t => bridgeExp g sm s t) :=
    bridgeExp_strictAnti g sm gOld s hwin hpos
  have hSA : StrictAnti E := by
    intro a b hab
    have hlt : (E b : ℤ) < (E a : ℤ) := by
      rw [hE b, hE a]; exact hSAz hab
    exact_mod_cast hlt
  exact hSA.injective

/-- **Bridge-code injectivity reduction.**  If the per-position labelling word
`fun i => lab t i` is injective on the selected family, then so is the
bridge-exponent code `fun i => E (lab t i)` for any injective `E` — in particular
the `E` produced by `bridgeExp_nat_injective`.  Thus injectivity of the
bridge-exponent descent code is *derived* from the strict bridge descent plus
injectivity of the raw label word. -/
theorem bridgeCode_injOn_of_injective {E : ℕ → ℕ} (hE : Function.Injective E)
    (T : Finset CNLTransition) (lab : CNLTransition → ℕ → ℕ) (M : ℕ)
    (hlab :
      ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
        (List.range M).map (lab t₁) = (List.range M).map (lab t₂) → t₁ = t₂) :
    ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
      (List.range M).map (fun i => E (lab t₁ i))
          = (List.range M).map (fun i => E (lab t₂ i)) → t₁ = t₂ := by
  intro t₁ ht₁ t₂ ht₂ h
  refine hlab t₁ ht₁ t₂ ht₂ ?_
  refine list_map_left_injective hE ?_
  rw [List.map_map, List.map_map]
  exact h

/--
**Bridge-exponent depth-`M` encoding constructor.**

Builds the depth-`M` encoding whose code at each position is the bridge exponent
`E (lab t i)`, with injectivity *derived* from the strict bridge descent
(`bridgeExp_nat_injective`) and injectivity of the raw label word.  The ladder
height is the exponent itself (so `δ ≤ ladderHeight δ` holds with equality), and
the BND height is the additive sum of recorded bridge exponents. -/
def SelectedClusterLadderEncoding.ofBridgeLadderWord
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ)
    (hc : 0 < c) (hCQ : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ)
    (M : ℕ) (E : ℕ → ℕ) {g sm gOld : ℕ → ℤ} {s : ℕ}
    (hE : ∀ t, (E t : ℤ) = bridgeExp g sm s t)
    (hwin : ∀ t, sm (t + 1) - sm t = g t - gOld t)
    (hpos : ∀ t, 0 < gOld t)
    (lab : CNLTransition → ℕ → ℕ)
    (hlab :
      ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
        (List.range M).map (lab t₁) = (List.range M).map (lab t₂) → t₁ = t₂)
    (hheight :
      ∀ t ∈ selectedTransitions T,
        BNDHeight t = ∑ i ∈ Finset.range M, (E (lab t i) : ℝ)) :
    SelectedClusterLadderEncoding T BNDHeight c CQ :=
  SelectedClusterLadderEncoding.ofInjectiveLadderWord T BNDHeight c CQ hc hCQ
    (fun n => (n : ℝ)) 0 M (fun _ => le_refl _)
    (fun t => (List.range M).map (fun i => E (lab t i)))
    (by
      intro t _ht
      rw [List.length_map, List.length_range])
    (bridgeCode_injOn_of_injective (bridgeExp_nat_injective hE hwin hpos) T lab M hlab)
    (by
      intro t ht
      rw [hheight t ht, pathHeight_map_range])

/-! ## The isolated residual primitive and the proved reduction -/

/--
**The smallest irreducible residual primitive (faithful, local form).**

A *coherent ladder coordinatization* of the surviving selected clean CNL cluster:
the per-step lift-state node assignment of Lemma L.1.2's reconstruction along the
cluster, over the Type-C/Type-P branching tree `S`, with BND height
`ladderHeight`.  Its fields are exactly the manuscript residue —

* `nodeOf t i`, the reconstructed lift-state node of `t` at cluster depth `i`,
  with common root (`root_eq`);
* `coherent`, the local (G.7)–(G.8) child congruence `nodeOf t (i+1) ∈ S (nodeOf t i)`;
* `path_injOn`, the reconstruction's injectivity on the clean surviving subfamily;
* `height_additive`, the telescoping BND height.

Everything that turns this local data into the K.3/L.1.2 Kraft bound is proved
(`toEncoding`, `kraftSum_le`).  This is strictly more explicit and more local than
the original residual "∃ a `SelectedClusterLadderEncoding`". -/
structure ClusterLadderCoordinatization
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ) where
  /-- The Type-C/Type-P lift-exponent branching tree of the cluster. -/
  S : ℕ → Finset ℕ
  /-- The BND-height weight attached to each ladder node. -/
  ladderHeight : ℕ → ℝ
  /-- The root node of the ladder. -/
  root : ℕ
  /-- The ladder depth (cluster length). -/
  M : ℕ
  /-- The reconstructed lift-state node of each transition at each cluster depth. -/
  nodeOf : CNLTransition → ℕ → ℕ
  /-- The CNL entropy slope is positive (manuscript `c > 0`). -/
  hc_pos : 0 < c
  /-- The one-step Kraft constant is dominated by `C_Q` (manuscript G.6). -/
  hCQ_dom : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ
  /-- Each ladder height dominates its lift exponent (manuscript `H ≥ δ`). -/
  height_dom : ∀ δ : ℕ, (δ : ℝ) ≤ ladderHeight δ
  /-- Every selected transition's ladder starts at the common root. -/
  root_eq : ∀ t ∈ selectedTransitions T, nodeOf t 0 = root
  /-- Local child coherence: the (G.7)–(G.8) child congruence along the cluster. -/
  coherent :
    ∀ t ∈ selectedTransitions T, ∀ i, i < M → nodeOf t (i + 1) ∈ S (nodeOf t i)
  /-- The reconstruction is injective on the clean surviving selected family. -/
  path_injOn :
    ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
      descentBranch (nodeOf t₁) M = descentBranch (nodeOf t₂) M → t₁ = t₂
  /-- The BND height of a transition is the additive ladder height of its path. -/
  height_additive :
    ∀ t ∈ selectedTransitions T,
      BNDHeight t = ∑ i ∈ Finset.range M, ladderHeight (nodeOf t (i + 1))

namespace ClusterLadderCoordinatization

variable {T : Finset CNLTransition} {BNDHeight : CNLTransition → ℝ} {c CQ : ℝ}

/-- **The reduction: a coordinatization yields a full encoding.**  This discharges
the original residual primitive of `CNLClusterLadder.lean` from the strictly more
local coordinatization data. -/
def toEncoding (coord : ClusterLadderCoordinatization T BNDHeight c CQ) :
    SelectedClusterLadderEncoding T BNDHeight c CQ :=
  SelectedClusterLadderEncoding.ofCoherentLadderNodes T BNDHeight c CQ
    coord.hc_pos coord.hCQ_dom coord.S coord.ladderHeight coord.root coord.M
    coord.height_dom coord.nodeOf coord.root_eq coord.coherent coord.path_injOn
    coord.height_additive

/-- **The K.3/L.1.2 Kraft bound, genuinely derived from the coordinatization.**
`cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ C_Q^M`, obtained by feeding
the assembled encoding into `CNLClusterLadder`'s proved `kraftSum_le`. -/
theorem kraftSum_le (coord : ClusterLadderCoordinatization T BNDHeight c CQ) :
    cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ CQ ^ coord.M :=
  coord.toEncoding.kraftSum_le

/-- **Connection to the K.3 interface.**  The coordinatization yields the
`CNLClusterKraftData` whose `cluster_le_pathKraft` field is now discharged. -/
def toCNLClusterKraftData (coord : ClusterLadderCoordinatization T BNDHeight c CQ) :
    CNLClusterKraftData (selectedTransitions T) BNDHeight c CQ coord.M :=
  coord.toEncoding.toCNLClusterKraftData

end ClusterLadderCoordinatization

/-! ## Non-vacuousness at all depths -/

/--
**Non-vacuous depth-`(m+1)` encoding.**

From any lift-exponent labelling `liftExp` injective on the selected family, with
`BNDHeight t = (m+1)·liftExp t`, build a genuine depth-`(m+1)`
`SelectedClusterLadderEncoding` whose code repeats the single recorded exponent
along the cluster.  This shows the construction fires at every depth `m+1`, not
just depth 1. -/
def SelectedClusterLadderEncoding.ofReplicatedLiftExponent
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ)
    (hc : 0 < c) (hCQ : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ) (m : ℕ)
    (liftExp : CNLTransition → ℕ)
    (hinj :
      ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
        liftExp t₁ = liftExp t₂ → t₁ = t₂)
    (hheight :
      ∀ t ∈ selectedTransitions T, BNDHeight t = ((m + 1 : ℕ) : ℝ) * (liftExp t : ℝ)) :
    SelectedClusterLadderEncoding T BNDHeight c CQ :=
  SelectedClusterLadderEncoding.ofInjectiveLadderWord T BNDHeight c CQ hc hCQ
    (fun n => (n : ℝ)) 0 (m + 1) (fun _ => le_refl _)
    (fun t => List.replicate (m + 1) (liftExp t))
    (fun _ _ => List.length_replicate)
    (by
      intro t₁ ht₁ t₂ ht₂ h
      simp only [List.replicate_succ, List.cons.injEq] at h
      exact hinj t₁ ht₁ t₂ ht₂ h.1)
    (by
      intro t ht
      rw [hheight t ht, pathHeight_replicate])

/-! ## Headline statements -/

/-- **Headline (general slope).**  A coherent ladder coordinatization of the
surviving selected clean cluster yields the K.3/L.1.2 weighted Kraft bound
`cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ C_Q^M`, genuinely derived
from `CNLClusterLadder`'s proved ladder collapse. -/
theorem cleanCNLKraftSum_selectedTransitions_le_CQ_pow_ofCoordinatization
    {T : Finset CNLTransition} {BNDHeight : CNLTransition → ℝ} {c CQ : ℝ}
    (coord : ClusterLadderCoordinatization T BNDHeight c CQ) :
    cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ CQ ^ coord.M :=
  coord.kraftSum_le

/-- **Headline (manuscript slope `c = 1`).**  Same bound at the manuscript slope. -/
theorem cleanCNLKraftSum_selectedTransitions_le_CQ_pow_one_ofCoordinatization
    {T : Finset CNLTransition} {BNDHeight : CNLTransition → ℝ} {CQ : ℝ}
    (coord : ClusterLadderCoordinatization T BNDHeight 1 CQ) :
    cleanCNLKraftSum (selectedTransitions T) BNDHeight 1 ≤ CQ ^ coord.M :=
  coord.kraftSum_le

end

end Erdos260
