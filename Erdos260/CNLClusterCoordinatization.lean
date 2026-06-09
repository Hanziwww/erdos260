import Mathlib
import Erdos260.CNLEncodingConstruction

/-!
# Appendix G.6 / L.1.2: constructing the `ClusterLadderCoordinatization`

`CNLEncodingConstruction.lean` reduced the K.3/L.1.2 Kraft bound
`cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ C_Q^M` to the existence of
a `ClusterLadderCoordinatization`: a per-step node coordinatization `nodeOf`/`S`/`H`
of the surviving selected clean family, with **four** opaque fields:

* `root_eq`  — every selected transition starts at the common root;
* `coherent` — local child coherence `nodeOf t (i+1) ∈ S (nodeOf t i)`;
* `path_injOn` — injective reconstruction (distinct threaded paths ⇒ distinct
  transitions);
* `height_additive` — the telescoping BND height.

`coherent`, `path_injOn` and `root_eq` were left as *assumed* structure fields.
This file **constructs** them — converting those existence fields into theorems —
by faithfully modelling Lemma L.1.2's reconstruction *by induction along the
cluster*: the lift-state node sequence is built by **iterating** a deterministic
(G.7)–(G.8) child-congruence step from a common root, reading the recorded clean
ladder-code word.

## What is genuinely proved here (no `sorry`, no `axiom`)

1. **Iterated reconstruction (`reconNode`).**  The node sequence
   `reconNode step root sym` with `reconNode … 0 = root` and
   `reconNode … (i+1) = step (reconNode … i) (sym i)`.  This *is* the manuscript's
   "reconstruct the lift state by induction along the cluster".

2. **A descent path determines its nodes (`descentBranch_eq_imp`).**  Equal
   threaded descent paths agree at every recorded position.  This is the
   faithfulness on which L.1.2's injectivity rests, proved as a real theorem.

3. **Injective reconstruction from local atoms (`reconNode_sym_eq`).**  If the
   deterministic step is injective in the recorded symbol on the alphabet and both
   code words live in it, then equal descent paths force equal code words.  Hence
   *injective reconstruction is derived* from (i) step-determinism and (ii)
   code-faithfulness — strictly smaller and more local than assuming `path_injOn`.

4. **The constructed coordinatization (`CleanClusterReconstruction`).**  The
   smallest residual: a deterministic-step clean-cluster reconstruction.  From it
   `root_eq`, `coherent` and `path_injOn` are all **proved** (`toCoordinatization`),
   yielding a genuine `ClusterLadderCoordinatization` and, via the proved ladder
   collapse, `cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ C_Q^M`
   (`kraftSum_le`, `toCNLClusterKraftData`) — with **no assumed encoding and no
   assumed coordinatization**.

5. **Step-determinism from the proved bridge engine (`ofBridgeStep`).**  When the
   step decodes through the bridge-exponent labelling, `step_injOn` is *derived*
   from the proved strict bridge descent (`bridgeExp_nat_injective`, ultimately
   `bridgeExp_strictAnti` = Lemma G.3).  This is a genuine, non-assumed source of
   the determinism atom.

6. **Non-vacuous firing (`ofReplicatedInjectiveLabel`).**  Any lift-exponent
   labelling injective on the selected family yields a full depth-`(m+1)`
   reconstruction, so the whole pipeline fires beyond depth 1.

## The irreducible residue (honest)

`CNLTransition` carries *no* lift-state geometry (only a normal form and an
available-class set), so the geometry must be supplied.  After this file the
residue is the smallest, most local atoms:

* `sym_injOn` — the recorded clean ladder code is **faithful** on the surviving
  selected family (the manuscript's `O_Q(1)`-to-one collapsed to injective on the
  clean subfamily).  This is the genuinely irreducible combinatorial input;
* `sym_mem` — the recorded code is **constant-base** (lands in a fixed alphabet);
* `step_injOn` — the reconstruction step is **deterministic** in the recorded
  symbol (derived from the bridge engine in `ofBridgeStep`);
* `height_additive` — the BND height **telescopes** along the path.

In particular `coherent`, `path_injOn` and `root_eq` are **no longer assumed**:
they are theorems.  The construction is therefore *not* primitive-CLOSED for a
fully abstract `T` (faithfulness `sym_injOn` cannot be conjured from no geometry),
but it is reduced to a strictly smaller, more faithful, and more local residual
than `ClusterLadderCoordinatization` itself.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## Part 1. The iterated reconstruction node sequence
(Lemma L.1.2: "reconstruct the lift state by induction along the cluster") -/

/-- The reconstructed node sequence built by **iterating** a deterministic step
function `step` from a common `root`, reading the recorded ladder-code word `sym`:
`reconNode step root sym 0 = root`, and
`reconNode step root sym (i+1) = step (reconNode step root sym i) (sym i)`, the
(G.7)–(G.8) child congruence applied to the current node and the recorded symbol. -/
def reconNode (step : ℕ → ℕ → ℕ) (root : ℕ) (sym : ℕ → ℕ) : ℕ → ℕ
  | 0 => root
  | (i + 1) => step (reconNode step root sym i) (sym i)

@[simp] theorem reconNode_zero (step : ℕ → ℕ → ℕ) (root : ℕ) (sym : ℕ → ℕ) :
    reconNode step root sym 0 = root := rfl

theorem reconNode_succ (step : ℕ → ℕ → ℕ) (root : ℕ) (sym : ℕ → ℕ) (i : ℕ) :
    reconNode step root sym (i + 1) = step (reconNode step root sym i) (sym i) := rfl

/-- With the projection step (the symbol *is* the next node), the reconstruction
returns the recorded symbol.  Used by the constant-base non-vacuousness witness. -/
theorem reconNode_proj_succ (root : ℕ) (sym : ℕ → ℕ) (i : ℕ) :
    reconNode (fun _ σ => σ) root sym (i + 1) = sym i := rfl

/-! ## Part 2. A threaded descent path determines its node entries -/

/-- **The threaded descent path determines its nodes.**  If two node sequences
produce the *same* depth-`m` descent path, they agree at every recorded position
`i + 1` (`i < m`).  This is the faithfulness of the descent-path encoding on which
the injective reconstruction of Lemma L.1.2 rests, here a real theorem. -/
theorem descentBranch_eq_imp :
    ∀ (m : ℕ) (node node' : ℕ → ℕ),
      descentBranch node m = descentBranch node' m →
        ∀ i, i < m → node (i + 1) = node' (i + 1) := by
  intro m
  induction m with
  | zero =>
      intro node node' _ i hi
      exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
      intro node node' heq i hi
      simp only [descentBranch_succ, List.cons.injEq] at heq
      obtain ⟨hhead, htail⟩ := heq
      cases i with
      | zero => exact hhead
      | succ j =>
          have hj : j < n := by omega
          have hrec := ih (fun a => node (a + 1)) (fun a => node' (a + 1)) htail j hj
          simpa using hrec

/-! ## Part 3. Injective reconstruction from step-determinism + code-faithfulness -/

/-- The reconstructed nodes agree up to depth `M` once the descent paths agree. -/
theorem reconNode_agree
    (step : ℕ → ℕ → ℕ) (root : ℕ) (sym₁ sym₂ : ℕ → ℕ) (M : ℕ)
    (hpath : descentBranch (reconNode step root sym₁) M
              = descentBranch (reconNode step root sym₂) M) :
    ∀ i, i ≤ M → reconNode step root sym₁ i = reconNode step root sym₂ i := by
  have hagree := descentBranch_eq_imp M _ _ hpath
  intro i hi
  cases i with
  | zero => rfl
  | succ j => exact hagree j (by omega)

/-- **The recorded code word is recovered from the descent path.**  If the
deterministic step is injective in the recorded symbol on the alphabet, and both
code words land in the alphabet, then equal descent paths force equal code words
on `[0, M)`.  This is the engine of Lemma L.1.2's injective reconstruction: the
path determines the lift-state sequence, and step-determinism peels off the
recorded symbols one position at a time. -/
theorem reconNode_sym_eq
    (step : ℕ → ℕ → ℕ) (root : ℕ) (sym₁ sym₂ : ℕ → ℕ) (M : ℕ)
    (alphabet : Finset ℕ)
    (hstep : ∀ n, Set.InjOn (step n) (↑alphabet : Set ℕ))
    (h1 : ∀ i, i < M → sym₁ i ∈ alphabet)
    (h2 : ∀ i, i < M → sym₂ i ∈ alphabet)
    (hpath : descentBranch (reconNode step root sym₁) M
              = descentBranch (reconNode step root sym₂) M) :
    ∀ i, i < M → sym₁ i = sym₂ i := by
  have hnode := reconNode_agree step root sym₁ sym₂ M hpath
  have hagree := descentBranch_eq_imp M _ _ hpath
  intro i hi
  have hni : reconNode step root sym₁ i = reconNode step root sym₂ i :=
    hnode i (le_of_lt hi)
  have hni1 : reconNode step root sym₁ (i + 1) = reconNode step root sym₂ (i + 1) :=
    hagree i hi
  rw [reconNode_succ, reconNode_succ, hni] at hni1
  exact hstep (reconNode step root sym₂ i)
    (Finset.mem_coe.mpr (h1 i hi)) (Finset.mem_coe.mpr (h2 i hi)) hni1

/-! ## Part 4. The smallest residual: a step-deterministic clean-cluster reconstruction -/

/--
**The constructed local residual primitive.**

A *deterministic-step clean-cluster reconstruction* of the surviving selected
clean-CNL cluster, faithfully modelling Lemma L.1.2's reconstruction by induction
along the cluster:

* `step` is the deterministic (G.7)–(G.8) child congruence: from the current node
  and the recorded symbol it returns the next lift-state node;
* `sym t i` is the recorded clean ladder-code symbol of transition `t` at cluster
  depth `i`;
* `alphabet` is the constant-base ladder alphabet (`sym_mem`);
* `step_injOn` is the step-determinism atom (derived from the bridge engine in
  `ofBridgeStep`);
* `sym_injOn` is the code-faithfulness atom — the genuinely irreducible input;
* `height_additive` is the telescoping BND height.

From this data the node assignment `nodeOf` is **iterated** (so `root_eq` and
`coherent` are theorems), and `path_injOn` is **derived** from `step_injOn` and
`sym_injOn` (`reconNode_sym_eq`).  Hence the full `ClusterLadderCoordinatization`
is assembled with no assumed coherence or injectivity. -/
structure CleanClusterReconstruction
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ) where
  /-- The constant-base ladder alphabet (the ordinary/TC/TP/BND code symbols). -/
  alphabet : Finset ℕ
  /-- The deterministic (G.7)–(G.8) child-congruence step. -/
  step : ℕ → ℕ → ℕ
  /-- The BND-height weight attached to each ladder node. -/
  ladderHeight : ℕ → ℝ
  /-- The common root lift-state node. -/
  root : ℕ
  /-- The ladder depth (cluster length). -/
  M : ℕ
  /-- The recorded clean ladder-code word of each transition. -/
  sym : CNLTransition → ℕ → ℕ
  /-- The CNL entropy slope is positive (manuscript `c > 0`). -/
  hc_pos : 0 < c
  /-- The one-step Kraft constant is dominated by `C_Q` (manuscript G.6). -/
  hCQ_dom : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ
  /-- Each ladder height dominates its lift exponent (manuscript `H ≥ δ`). -/
  height_dom : ∀ δ : ℕ, (δ : ℝ) ≤ ladderHeight δ
  /-- Constant-base alphabet: every recorded symbol lies in the alphabet. -/
  sym_mem : ∀ t ∈ selectedTransitions T, ∀ i, i < M → sym t i ∈ alphabet
  /-- Step-determinism: the child congruence is injective in the recorded symbol. -/
  step_injOn : ∀ n, Set.InjOn (step n) (↑alphabet : Set ℕ)
  /-- Code-faithfulness: the recorded code is injective on the selected family. -/
  sym_injOn :
    ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
      (∀ i, i < M → sym t₁ i = sym t₂ i) → t₁ = t₂
  /-- The BND height telescopes to the additive ladder height of the path. -/
  height_additive :
    ∀ t ∈ selectedTransitions T,
      BNDHeight t = ∑ i ∈ Finset.range M, ladderHeight (reconNode step root (sym t) (i + 1))

namespace CleanClusterReconstruction

variable {T : Finset CNLTransition} {BNDHeight : CNLTransition → ℝ} {c CQ : ℝ}

/-- The reconstructed lift-state node of a transition at each cluster depth,
built by iterating the deterministic step from the common root. -/
def nodeOf (R : CleanClusterReconstruction T BNDHeight c CQ) (t : CNLTransition) : ℕ → ℕ :=
  reconNode R.step R.root (R.sym t)

@[simp] theorem nodeOf_zero (R : CleanClusterReconstruction T BNDHeight c CQ)
    (t : CNLTransition) : R.nodeOf t 0 = R.root := rfl

theorem nodeOf_succ (R : CleanClusterReconstruction T BNDHeight c CQ)
    (t : CNLTransition) (i : ℕ) :
    R.nodeOf t (i + 1) = R.step (R.nodeOf t i) (R.sym t i) := rfl

/-- The Type-C/Type-P branching tree: the children of a node are the deterministic
decodings of the alphabet symbols at that node. -/
def childrenTree (R : CleanClusterReconstruction T BNDHeight c CQ) : ℕ → Finset ℕ :=
  fun n => R.alphabet.image (R.step n)

/-- **Local child coherence is a theorem.**  Each reconstructed step lands in the
branching tree, because the next node is the decoding of an alphabet symbol. -/
theorem coherent (R : CleanClusterReconstruction T BNDHeight c CQ) :
    ∀ t ∈ selectedTransitions T, ∀ i, i < R.M →
      R.nodeOf t (i + 1) ∈ R.childrenTree (R.nodeOf t i) := by
  intro t ht i hi
  simp only [childrenTree, nodeOf_succ]
  exact Finset.mem_image.mpr ⟨R.sym t i, R.sym_mem t ht i hi, rfl⟩

/-- **Injective reconstruction is a theorem.**  Equal threaded descent paths force
equal code words (step-determinism, `reconNode_sym_eq`), hence equal transitions
(code-faithfulness, `sym_injOn`). -/
theorem path_injOn (R : CleanClusterReconstruction T BNDHeight c CQ) :
    ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
      descentBranch (R.nodeOf t₁) R.M = descentBranch (R.nodeOf t₂) R.M → t₁ = t₂ := by
  intro t₁ ht₁ t₂ ht₂ hpath
  refine R.sym_injOn t₁ ht₁ t₂ ht₂ ?_
  exact reconNode_sym_eq R.step R.root (R.sym t₁) (R.sym t₂) R.M R.alphabet
    R.step_injOn (R.sym_mem t₁ ht₁) (R.sym_mem t₂ ht₂) hpath

/-- **The constructed coordinatization.**  Assembles a genuine
`ClusterLadderCoordinatization` whose `root_eq`, `coherent` and `path_injOn`
fields are the theorems above (not assumptions). -/
def toCoordinatization (R : CleanClusterReconstruction T BNDHeight c CQ) :
    ClusterLadderCoordinatization T BNDHeight c CQ where
  S := R.childrenTree
  ladderHeight := R.ladderHeight
  root := R.root
  M := R.M
  nodeOf := R.nodeOf
  hc_pos := R.hc_pos
  hCQ_dom := R.hCQ_dom
  height_dom := R.height_dom
  root_eq := fun _ _ => rfl
  coherent := R.coherent
  path_injOn := R.path_injOn
  height_additive := by
    intro t ht
    simpa only [nodeOf] using R.height_additive t ht

/-- **The K.3/L.1.2 Kraft bound, genuinely derived from the constructed
coordinatization.**  No assumed encoding, no assumed coherence/injectivity. -/
theorem kraftSum_le (R : CleanClusterReconstruction T BNDHeight c CQ) :
    cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ CQ ^ R.M :=
  R.toCoordinatization.kraftSum_le

/-- **Connection to the K.3 interface.**  The constructed coordinatization yields
the `CNLClusterKraftData` whose `cluster_le_pathKraft` field is discharged. -/
def toCNLClusterKraftData (R : CleanClusterReconstruction T BNDHeight c CQ) :
    CNLClusterKraftData (selectedTransitions T) BNDHeight c CQ R.M :=
  R.toCoordinatization.toCNLClusterKraftData

end CleanClusterReconstruction

/-! ## Part 5. Step-determinism from the proved bridge strict-descent engine -/

/--
**Bridge-step clean-cluster reconstruction.**

The deterministic step decodes through the bridge-exponent labelling
`step n σ = E σ`, with `E` the natural realization of the integer bridge exponents
`A_s - A_t + σ^-_t`.  Here `step_injOn` is **derived** from the proved strict
bridge descent (`bridgeExp_nat_injective`, ultimately `bridgeExp_strictAnti` =
Lemma G.3): a genuine, non-assumed source of the step-determinism atom.  The
ladder alphabet is the actually-used symbol set (so `sym_mem` is automatic), the
ladder height is the node itself (so `H ≥ δ` with equality), and the BND height is
the additive sum of recorded bridge exponents.  The only remaining input is
code-faithfulness `sym_injOn`. -/
def CleanClusterReconstruction.ofBridgeStep
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ)
    (hc : 0 < c) (hCQ : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ)
    (M : ℕ) (E : ℕ → ℕ) {g sm gOld : ℕ → ℤ} {s : ℕ}
    (hE : ∀ t, (E t : ℤ) = bridgeExp g sm s t)
    (hwin : ∀ t, sm (t + 1) - sm t = g t - gOld t)
    (hpos : ∀ t, 0 < gOld t)
    (sym : CNLTransition → ℕ → ℕ)
    (hsym_inj :
      ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
        (∀ i, i < M → sym t₁ i = sym t₂ i) → t₁ = t₂)
    (hheight :
      ∀ t ∈ selectedTransitions T,
        BNDHeight t = ∑ i ∈ Finset.range M, (E (sym t i) : ℝ)) :
    CleanClusterReconstruction T BNDHeight c CQ where
  alphabet := (selectedTransitions T).biUnion (fun t => (Finset.range M).image (sym t))
  step := fun _ σ => E σ
  ladderHeight := fun n => (n : ℝ)
  root := 0
  M := M
  sym := sym
  hc_pos := hc
  hCQ_dom := hCQ
  height_dom := fun _ => le_refl _
  sym_mem := by
    intro t ht i hi
    exact Finset.mem_biUnion.mpr
      ⟨t, ht, Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩⟩
  step_injOn := fun _ => (bridgeExp_nat_injective hE hwin hpos).injOn
  sym_injOn := hsym_inj
  height_additive := by
    intro t ht
    rw [hheight t ht]
    apply Finset.sum_congr rfl
    intro i _
    rfl

/-- **The K.3/L.1.2 Kraft bound via the bridge-step reconstruction.**  Step
determinism is supplied by the proved strict bridge descent; only the clean
code-faithfulness remains a hypothesis. -/
theorem cleanCNLKraftSum_selectedTransitions_le_ofBridgeStep
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ)
    (hc : 0 < c) (hCQ : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ)
    (M : ℕ) (E : ℕ → ℕ) {g sm gOld : ℕ → ℤ} {s : ℕ}
    (hE : ∀ t, (E t : ℤ) = bridgeExp g sm s t)
    (hwin : ∀ t, sm (t + 1) - sm t = g t - gOld t)
    (hpos : ∀ t, 0 < gOld t)
    (sym : CNLTransition → ℕ → ℕ)
    (hsym_inj :
      ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
        (∀ i, i < M → sym t₁ i = sym t₂ i) → t₁ = t₂)
    (hheight :
      ∀ t ∈ selectedTransitions T,
        BNDHeight t = ∑ i ∈ Finset.range M, (E (sym t i) : ℝ)) :
    cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ CQ ^ M :=
  (CleanClusterReconstruction.ofBridgeStep T BNDHeight c CQ hc hCQ M E hE hwin hpos
    sym hsym_inj hheight).kraftSum_le

/-! ## Part 6. Non-vacuousness: a fully constructed depth-`(m+1)` reconstruction -/

/--
**Non-vacuous constant-base reconstruction.**

From any lift-exponent labelling `liftExp` injective on the selected family, with
`BNDHeight t = (m+1)·liftExp t`, build a genuine depth-`(m+1)`
`CleanClusterReconstruction` whose recorded word replays the single recorded
exponent along the cluster (the projection step makes the symbol the next node).
All four atoms are discharged: `sym_mem` (the labels form the alphabet),
`step_injOn` (the projection is injective), `sym_injOn` (from `liftExp`
injectivity), and `height_additive` (the replicated sum).  This shows the whole
constructed pipeline fires at every depth `m+1`. -/
def CleanClusterReconstruction.ofReplicatedInjectiveLabel
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ)
    (hc : 0 < c) (hCQ : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ) (m : ℕ)
    (liftExp : CNLTransition → ℕ)
    (hinj :
      ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
        liftExp t₁ = liftExp t₂ → t₁ = t₂)
    (hheight :
      ∀ t ∈ selectedTransitions T, BNDHeight t = ((m + 1 : ℕ) : ℝ) * (liftExp t : ℝ)) :
    CleanClusterReconstruction T BNDHeight c CQ where
  alphabet := (selectedTransitions T).image liftExp
  step := fun _ σ => σ
  ladderHeight := fun n => (n : ℝ)
  root := 0
  M := m + 1
  sym := fun t _ => liftExp t
  hc_pos := hc
  hCQ_dom := hCQ
  height_dom := fun _ => le_refl _
  sym_mem := by
    intro t ht _ _
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  step_injOn := by
    intro _ a _ b _ h
    exact h
  sym_injOn := by
    intro t₁ ht₁ t₂ ht₂ h
    exact hinj t₁ ht₁ t₂ ht₂ (h 0 (Nat.succ_pos m))
  height_additive := by
    intro t ht
    rw [hheight t ht]
    simp only [reconNode_proj_succ, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The K.3/L.1.2 Kraft bound, fully constructed at depth `m+1`.**  Given an
injective lift-exponent labelling, the constructed reconstruction yields
`cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ C_Q^(m+1)` with no assumed
encoding or coordinatization — every coordinatization field is a theorem. -/
theorem cleanCNLKraftSum_selectedTransitions_le_ofReplicatedInjectiveLabel
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ)
    (hc : 0 < c) (hCQ : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ) (m : ℕ)
    (liftExp : CNLTransition → ℕ)
    (hinj :
      ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
        liftExp t₁ = liftExp t₂ → t₁ = t₂)
    (hheight :
      ∀ t ∈ selectedTransitions T, BNDHeight t = ((m + 1 : ℕ) : ℝ) * (liftExp t : ℝ)) :
    cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ CQ ^ (m + 1) :=
  (CleanClusterReconstruction.ofReplicatedInjectiveLabel T BNDHeight c CQ hc hCQ m
    liftExp hinj hheight).kraftSum_le

/-! ## Headline -/

/-- **Headline.**  A deterministic-step clean-cluster reconstruction of the
surviving selected clean cluster yields the K.3/L.1.2 weighted Kraft bound
`cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ C_Q^M`, with the
coordinatization's coherence and injective reconstruction proved rather than
assumed. -/
theorem cleanCNLKraftSum_selectedTransitions_le_ofReconstruction
    {T : Finset CNLTransition} {BNDHeight : CNLTransition → ℝ} {c CQ : ℝ}
    (R : CleanClusterReconstruction T BNDHeight c CQ) :
    cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ CQ ^ R.M :=
  R.kraftSum_le

end

end Erdos260
