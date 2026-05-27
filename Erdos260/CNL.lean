import Mathlib

/-!
# Clean CNL selector primitives

This file contains the finite normal-form and one-step CNL classifier vocabulary
used by Appendix J.5 and Appendix L.1 of `proof_v2.tex`.  The selector is a
deterministic priority scan over the seven CNL classes; it does not assert any
analytic estimate.
-/

namespace Erdos260

open Finset

noncomputable section

/-- The two exact normal forms used by the CNL selector. -/
inductive CNLNormalForm where
  | positiveLift
  | childResidue
deriving DecidableEq, Fintype, Repr

/-- CNL one-step classes in the priority order of Appendix L.1. -/
inductive CNLClass where
  | bnd
  | sep
  | tc
  | vs
  | ds
  | tp
  | pkg
deriving DecidableEq, Fintype, Repr

/-- The priority rank: smaller rank is checked earlier. -/
def CNLClass.priorityRank : CNLClass -> Nat
  | .pkg => 0
  | .sep => 1
  | .bnd => 2
  | .tc => 3
  | .vs => 4
  | .ds => 5
  | .tp => 6

/-- A visible one-step transition after shell-paid and bounded factors have been
recorded.  `available` is the finite set of classes whose hypotheses currently
hold. -/
structure CNLTransition where
  normalForm : CNLNormalForm
  available : Finset CNLClass
deriving DecidableEq

/-- Deterministic CNL priority scan, in the order
PKG, SEP, BND, TC, VS, DS, TP. -/
def selectCNLClass? (available : Finset CNLClass) : Option CNLClass :=
  if CNLClass.pkg ∈ available then
    some CNLClass.pkg
  else if CNLClass.sep ∈ available then
    some CNLClass.sep
  else if CNLClass.bnd ∈ available then
    some CNLClass.bnd
  else if CNLClass.tc ∈ available then
    some CNLClass.tc
  else if CNLClass.vs ∈ available then
    some CNLClass.vs
  else if CNLClass.ds ∈ available then
    some CNLClass.ds
  else if CNLClass.tp ∈ available then
    some CNLClass.tp
  else
    none

/-- The canonical classifier attached to a visible CNL transition. -/
def canonicalCNLSelector (t : CNLTransition) : Option CNLClass :=
  selectCNLClass? t.available

theorem selectCNLClass?_single_valued {available : Finset CNLClass}
    {a b : CNLClass}
    (ha : selectCNLClass? available = some a)
    (hb : selectCNLClass? available = some b) :
    a = b := by
  rw [ha] at hb
  exact Option.some.inj hb

theorem canonicalCNLSelector_single_valued {t : CNLTransition}
    {a b : CNLClass}
    (ha : canonicalCNLSelector t = some a)
    (hb : canonicalCNLSelector t = some b) :
    a = b :=
  selectCNLClass?_single_valued ha hb

theorem selectCNLClass?_eq_some_mem {available : Finset CNLClass}
    {c : CNLClass} (h : selectCNLClass? available = some c) :
    c ∈ available := by
  unfold selectCNLClass? at h
  split_ifs at h with hpkg hsep hbnd htc hvs hds htp
  · cases h
    exact hpkg
  · cases h
    exact hsep
  · cases h
    exact hbnd
  · cases h
    exact htc
  · cases h
    exact hvs
  · cases h
    exact hds
  · cases h
    exact htp

theorem canonicalCNLSelector_eq_some_mem {t : CNLTransition}
    {c : CNLClass} (h : canonicalCNLSelector t = some c) :
    c ∈ t.available :=
  selectCNLClass?_eq_some_mem h

theorem selectCNLClass?_isSome_of_nonempty {available : Finset CNLClass}
    (h : available.Nonempty) :
    (selectCNLClass? available).isSome := by
  unfold selectCNLClass?
  split_ifs with hpkg hsep hbnd htc hvs hds htp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · rcases h with ⟨c, hc⟩
    cases c <;> contradiction

theorem exists_selectCNLClass?_eq_some_of_nonempty
    {available : Finset CNLClass} (h : available.Nonempty) :
    ∃ c : CNLClass, selectCNLClass? available = some c := by
  have hs := selectCNLClass?_isSome_of_nonempty h
  cases hsel : selectCNLClass? available with
  | none =>
      simp [hsel] at hs
  | some c =>
      exact ⟨c, rfl⟩

theorem exists_canonicalCNLSelector_eq_some_of_nonempty
    {t : CNLTransition} (h : t.available.Nonempty) :
    ∃ c : CNLClass, canonicalCNLSelector t = some c :=
  exists_selectCNLClass?_eq_some_of_nonempty h

theorem selectCNLClass?_eq_pkg_of_mem {available : Finset CNLClass}
    (h : CNLClass.pkg ∈ available) :
    selectCNLClass? available = some CNLClass.pkg := by
  simp [selectCNLClass?, h]

theorem selectCNLClass?_eq_sep_of_mem {available : Finset CNLClass}
    (hsep : CNLClass.sep ∈ available)
    (hpkg : CNLClass.pkg ∉ available) :
    selectCNLClass? available = some CNLClass.sep := by
  simp [selectCNLClass?, hpkg, hsep]

theorem selectCNLClass?_eq_bnd_of_mem {available : Finset CNLClass}
    (hbnd : CNLClass.bnd ∈ available)
    (hpkg : CNLClass.pkg ∉ available) (hsep : CNLClass.sep ∉ available) :
    selectCNLClass? available = some CNLClass.bnd := by
  simp [selectCNLClass?, hpkg, hsep, hbnd]

theorem selectCNLClass?_eq_tc_of_mem {available : Finset CNLClass}
    (htc : CNLClass.tc ∈ available)
    (hpkg : CNLClass.pkg ∉ available) (hsep : CNLClass.sep ∉ available)
    (hbnd : CNLClass.bnd ∉ available) :
    selectCNLClass? available = some CNLClass.tc := by
  simp [selectCNLClass?, hpkg, hsep, hbnd, htc]

theorem selectCNLClass?_eq_vs_of_mem {available : Finset CNLClass}
    (hvs : CNLClass.vs ∈ available)
    (hpkg : CNLClass.pkg ∉ available) (hsep : CNLClass.sep ∉ available)
    (hbnd : CNLClass.bnd ∉ available) (htc : CNLClass.tc ∉ available) :
    selectCNLClass? available = some CNLClass.vs := by
  simp [selectCNLClass?, hpkg, hsep, hbnd, htc, hvs]

theorem selectCNLClass?_eq_ds_of_mem {available : Finset CNLClass}
    (hds : CNLClass.ds ∈ available)
    (hpkg : CNLClass.pkg ∉ available) (hsep : CNLClass.sep ∉ available)
    (hbnd : CNLClass.bnd ∉ available) (htc : CNLClass.tc ∉ available)
    (hvs : CNLClass.vs ∉ available) :
    selectCNLClass? available = some CNLClass.ds := by
  simp [selectCNLClass?, hpkg, hsep, hbnd, htc, hvs, hds]

theorem selectCNLClass?_eq_tp_of_mem {available : Finset CNLClass}
    (htp : CNLClass.tp ∈ available)
    (hpkg : CNLClass.pkg ∉ available) (hsep : CNLClass.sep ∉ available)
    (hbnd : CNLClass.bnd ∉ available) (htc : CNLClass.tc ∉ available)
    (hvs : CNLClass.vs ∉ available) (hds : CNLClass.ds ∉ available) :
    selectCNLClass? available = some CNLClass.tp := by
  simp [selectCNLClass?, hpkg, hsep, hbnd, htc, hvs, hds, htp]

theorem selectCNLClass?_priorityRank_le_of_mem {available : Finset CNLClass}
    {c d : CNLClass} (hc : selectCNLClass? available = some c)
    (hd : d ∈ available) :
    CNLClass.priorityRank c <= CNLClass.priorityRank d := by
  unfold selectCNLClass? at hc
  split_ifs at hc with hpkg hsep hbnd htc hvs hds htp
  all_goals cases hc
  all_goals cases d <;> simp [CNLClass.priorityRank] at * <;> contradiction

theorem canonicalCNLSelector_priorityRank_le_of_mem {t : CNLTransition}
    {c d : CNLClass} (hc : canonicalCNLSelector t = some c)
    (hd : d ∈ t.available) :
    CNLClass.priorityRank c <= CNLClass.priorityRank d :=
  selectCNLClass?_priorityRank_le_of_mem hc hd

/-- Transitions whose canonical selector returns a fixed class. -/
def transitionsSelectedAs (transitions : Finset CNLTransition)
    (cls : CNLClass) : Finset CNLTransition :=
  transitions.filter fun t => canonicalCNLSelector t = some cls

/-- Transitions with some canonical selected class. -/
def selectedTransitions (transitions : Finset CNLTransition) :
    Finset CNLTransition :=
  transitions.filter fun t => (canonicalCNLSelector t).isSome

/-- Transitions with a fixed exact normal form. -/
def transitionsOfNormalForm (transitions : Finset CNLTransition)
    (normalForm : CNLNormalForm) : Finset CNLTransition :=
  transitions.filter fun t => t.normalForm = normalForm

theorem mem_transitionsSelectedAs {transitions : Finset CNLTransition}
    {cls : CNLClass} {t : CNLTransition} :
    t ∈ transitionsSelectedAs transitions cls ↔
      t ∈ transitions ∧ canonicalCNLSelector t = some cls := by
  simp [transitionsSelectedAs]

theorem mem_selectedTransitions {transitions : Finset CNLTransition}
    {t : CNLTransition} :
    t ∈ selectedTransitions transitions ↔
      t ∈ transitions ∧ (canonicalCNLSelector t).isSome := by
  simp [selectedTransitions]

theorem mem_transitionsOfNormalForm {transitions : Finset CNLTransition}
    {normalForm : CNLNormalForm} {t : CNLTransition} :
    t ∈ transitionsOfNormalForm transitions normalForm ↔
      t ∈ transitions ∧ t.normalForm = normalForm := by
  simp [transitionsOfNormalForm]

theorem transitionsSelectedAs_subset (transitions : Finset CNLTransition)
    (cls : CNLClass) :
    transitionsSelectedAs transitions cls ⊆ transitions := by
  intro t ht
  exact (mem_transitionsSelectedAs.1 ht).1

theorem selectedTransitions_subset (transitions : Finset CNLTransition) :
    selectedTransitions transitions ⊆ transitions := by
  intro t ht
  exact (mem_selectedTransitions.1 ht).1

theorem transitionsOfNormalForm_subset (transitions : Finset CNLTransition)
    (normalForm : CNLNormalForm) :
    transitionsOfNormalForm transitions normalForm ⊆ transitions := by
  intro t ht
  exact (mem_transitionsOfNormalForm.1 ht).1

theorem transitionsSelectedAs_subset_selected
    (transitions : Finset CNLTransition) (cls : CNLClass) :
    transitionsSelectedAs transitions cls ⊆ selectedTransitions transitions := by
  intro t ht
  exact mem_selectedTransitions.2
    ⟨(mem_transitionsSelectedAs.1 ht).1, by
      simp [(mem_transitionsSelectedAs.1 ht).2]⟩

theorem transitionsSelectedAs_card_le (transitions : Finset CNLTransition)
    (cls : CNLClass) :
    (transitionsSelectedAs transitions cls).card <= transitions.card :=
  card_le_card (transitionsSelectedAs_subset transitions cls)

theorem selectedTransitions_card_le (transitions : Finset CNLTransition) :
    (selectedTransitions transitions).card <= transitions.card :=
  card_le_card (selectedTransitions_subset transitions)

theorem transitionsOfNormalForm_card_le (transitions : Finset CNLTransition)
    (normalForm : CNLNormalForm) :
    (transitionsOfNormalForm transitions normalForm).card <= transitions.card :=
  card_le_card (transitionsOfNormalForm_subset transitions normalForm)

theorem disjoint_transitionsSelectedAs_of_ne
    {transitions : Finset CNLTransition} {class₁ class₂ : CNLClass}
    (hne : class₁ ≠ class₂) :
    Disjoint (transitionsSelectedAs transitions class₁)
      (transitionsSelectedAs transitions class₂) := by
  rw [disjoint_left]
  intro t ht₁ ht₂
  have h₁ := (mem_transitionsSelectedAs.1 ht₁).2
  have h₂ := (mem_transitionsSelectedAs.1 ht₂).2
  exact hne (canonicalCNLSelector_single_valued h₁ h₂)

theorem disjoint_transitionsOfNormalForm_of_ne
    {transitions : Finset CNLTransition} {nf₁ nf₂ : CNLNormalForm}
    (hne : nf₁ ≠ nf₂) :
    Disjoint (transitionsOfNormalForm transitions nf₁)
      (transitionsOfNormalForm transitions nf₂) := by
  rw [disjoint_left]
  intro t ht₁ ht₂
  exact hne ((mem_transitionsOfNormalForm.1 ht₁).2.symm.trans
    (mem_transitionsOfNormalForm.1 ht₂).2)

theorem pairwiseDisjoint_transitionsSelectedAs
    (transitions : Finset CNLTransition) :
    ((Finset.univ : Finset CNLClass) : Set CNLClass).PairwiseDisjoint
      (transitionsSelectedAs transitions) := by
  intro cls₁ _ cls₂ _ hne
  exact disjoint_transitionsSelectedAs_of_ne hne

theorem pairwiseDisjoint_transitionsOfNormalForm
    (transitions : Finset CNLTransition) :
    ((Finset.univ : Finset CNLNormalForm) : Set CNLNormalForm).PairwiseDisjoint
      (transitionsOfNormalForm transitions) := by
  intro nf₁ _ nf₂ _ hne
  exact disjoint_transitionsOfNormalForm_of_ne hne

theorem selectedTransitions_eq_biUnion_selectedAs
    (transitions : Finset CNLTransition) :
    selectedTransitions transitions =
      (Finset.univ : Finset CNLClass).biUnion
        (transitionsSelectedAs transitions) := by
  ext t
  constructor
  · intro ht
    rcases mem_selectedTransitions.1 ht with ⟨hmem, hsome⟩
    cases hsel : canonicalCNLSelector t with
    | none =>
        simp [hsel] at hsome
    | some cls =>
        exact mem_biUnion.2
          ⟨cls, by simp, mem_transitionsSelectedAs.2 ⟨hmem, hsel⟩⟩
  · intro ht
    rcases mem_biUnion.1 ht with ⟨cls, _, hclass⟩
    exact transitionsSelectedAs_subset_selected transitions cls hclass

theorem selectedTransitions_card_le_sum_selectedAs
    (transitions : Finset CNLTransition) :
    (selectedTransitions transitions).card <=
      ∑ cls : CNLClass, (transitionsSelectedAs transitions cls).card := by
  rw [selectedTransitions_eq_biUnion_selectedAs]
  exact card_biUnion_le

theorem selectedTransitions_card_eq_sum_selectedAs
    (transitions : Finset CNLTransition) :
    (selectedTransitions transitions).card =
      ∑ cls : CNLClass, (transitionsSelectedAs transitions cls).card := by
  rw [selectedTransitions_eq_biUnion_selectedAs]
  exact card_biUnion (pairwiseDisjoint_transitionsSelectedAs transitions)

theorem selectedTransitions_card_le_sum_class_bounds
    (transitions : Finset CNLTransition) {B : CNLClass -> Nat}
    (hB : ∀ cls : CNLClass, (transitionsSelectedAs transitions cls).card <= B cls) :
    (selectedTransitions transitions).card <= ∑ cls : CNLClass, B cls := by
  exact (selectedTransitions_card_le_sum_selectedAs transitions).trans
    (sum_le_sum fun cls _ => hB cls)

theorem transitions_eq_biUnion_normalForm (transitions : Finset CNLTransition) :
    transitions =
      (Finset.univ : Finset CNLNormalForm).biUnion
        (transitionsOfNormalForm transitions) := by
  ext t
  constructor
  · intro ht
    exact mem_biUnion.2
      ⟨t.normalForm, by simp,
        mem_transitionsOfNormalForm.2 ⟨ht, rfl⟩⟩
  · intro ht
    rcases mem_biUnion.1 ht with ⟨normalForm, _, hnf⟩
    exact (mem_transitionsOfNormalForm.1 hnf).1

theorem transitions_card_le_sum_normalForm
    (transitions : Finset CNLTransition) :
    transitions.card <=
      ∑ normalForm : CNLNormalForm,
        (transitionsOfNormalForm transitions normalForm).card := by
  calc
    transitions.card =
        ((Finset.univ : Finset CNLNormalForm).biUnion
          (transitionsOfNormalForm transitions)).card := by
          exact congrArg Finset.card (transitions_eq_biUnion_normalForm transitions)
    _ <= ∑ normalForm : CNLNormalForm,
        (transitionsOfNormalForm transitions normalForm).card := by
          exact card_biUnion_le
            (s := (Finset.univ : Finset CNLNormalForm))
            (t := transitionsOfNormalForm transitions)

theorem transitions_card_eq_sum_normalForm
    (transitions : Finset CNLTransition) :
    transitions.card =
      ∑ normalForm : CNLNormalForm,
        (transitionsOfNormalForm transitions normalForm).card := by
  calc
    transitions.card =
        ((Finset.univ : Finset CNLNormalForm).biUnion
          (transitionsOfNormalForm transitions)).card := by
          exact congrArg Finset.card (transitions_eq_biUnion_normalForm transitions)
    _ = ∑ normalForm : CNLNormalForm,
        (transitionsOfNormalForm transitions normalForm).card := by
          exact card_biUnion (pairwiseDisjoint_transitionsOfNormalForm transitions)

/-- Generic bounded-to-one finite encoding estimate used by the CNL cluster
encoding: if every code fibre has at most `B` elements, then the source set has
size at most `B` times the number of used codes. -/
theorem card_le_card_image_mul_of_fiber_card_le
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (paths : Finset α) (code : α -> β) {B : Nat}
    (hfiber :
      ∀ y ∈ paths.image code, (paths.filter fun x => code x = y).card <= B) :
    paths.card <= (paths.image code).card * B := by
  calc
    paths.card = ∑ y ∈ paths.image code,
        (paths.filter fun x => code x = y).card := by
          exact Finset.card_eq_sum_card_image code paths
    _ <= ∑ _y ∈ paths.image code, B := by
          exact sum_le_sum hfiber
    _ = (paths.image code).card * B := by
          simp [Nat.mul_comm]

theorem card_le_code_bound_mul_fiber_bound
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (paths : Finset α) (code : α -> β) {codeBound fiberBound : Nat}
    (hcodes : (paths.image code).card <= codeBound)
    (hfiber :
      ∀ y ∈ paths.image code,
        (paths.filter fun x => code x = y).card <= fiberBound) :
    paths.card <= codeBound * fiberBound := by
  exact (card_le_card_image_mul_of_fiber_card_le paths code hfiber).trans
    (Nat.mul_le_mul_right fiberBound hcodes)

theorem real_card_le_code_bound_mul_fiber_bound
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (paths : Finset α) (code : α -> β) {codeBound fiberBound : Nat}
    (hcodes : (paths.image code).card <= codeBound)
    (hfiber :
      ∀ y ∈ paths.image code,
        (paths.filter fun x => code x = y).card <= fiberBound) :
    (paths.card : ℝ) <= (codeBound : ℝ) * (fiberBound : ℝ) := by
  exact_mod_cast
    (card_le_code_bound_mul_fiber_bound paths code hcodes hfiber)

theorem selectedTransitions_card_le_sum_code_bounds
    {β : Type*} [DecidableEq β] (transitions : Finset CNLTransition)
    (code : CNLClass -> CNLTransition -> β)
    {codeBound fiberBound : CNLClass -> Nat}
    (hcodes :
      ∀ cls : CNLClass,
        ((transitionsSelectedAs transitions cls).image (code cls)).card <=
          codeBound cls)
    (hfiber :
      ∀ (cls : CNLClass) (y : β),
        y ∈ (transitionsSelectedAs transitions cls).image (code cls) ->
          ((transitionsSelectedAs transitions cls).filter
            fun t => code cls t = y).card <= fiberBound cls) :
    (selectedTransitions transitions).card <=
      ∑ cls : CNLClass, codeBound cls * fiberBound cls := by
  refine selectedTransitions_card_le_sum_class_bounds transitions ?_
  intro cls
  exact card_le_code_bound_mul_fiber_bound
    (transitionsSelectedAs transitions cls) (code cls)
    (hcodes cls) (hfiber cls)

theorem real_selectedTransitions_card_le_sum_code_bounds
    {β : Type*} [DecidableEq β] (transitions : Finset CNLTransition)
    (code : CNLClass -> CNLTransition -> β)
    {codeBound fiberBound : CNLClass -> Nat}
    (hcodes :
      ∀ cls : CNLClass,
        ((transitionsSelectedAs transitions cls).image (code cls)).card <=
          codeBound cls)
    (hfiber :
      ∀ (cls : CNLClass) (y : β),
        y ∈ (transitionsSelectedAs transitions cls).image (code cls) ->
          ((transitionsSelectedAs transitions cls).filter
            fun t => code cls t = y).card <= fiberBound cls) :
    ((selectedTransitions transitions).card : ℝ) <=
      ∑ cls : CNLClass, (codeBound cls : ℝ) * (fiberBound cls : ℝ) := by
  exact_mod_cast
    (selectedTransitions_card_le_sum_code_bounds transitions code hcodes hfiber)

/-! ### Manuscript K.3.5 CNL transition classifier and J.5.1 partition -/

/--
**Proposition K.3.5 (CNL transition classifier, manuscript form).**

Every visible CNL transition with a nonempty `available` set is
deterministically assigned to **exactly one** class through the
canonical priority scan.  This is the classifier criterion that
appears in `proof_v2.tex` as Proposition K.3.5.

The classifier produces a unique class together with the priority
minimality property `priorityRank c ≤ priorityRank d` for any other
available `d`.
-/
theorem propositionK3_5_cnlTransitionClassifier
    (t : CNLTransition) (havail : t.available.Nonempty) :
    ∃! c : CNLClass,
      canonicalCNLSelector t = some c ∧
        c ∈ t.available ∧
        ∀ d ∈ t.available, CNLClass.priorityRank c <= CNLClass.priorityRank d := by
  rcases exists_canonicalCNLSelector_eq_some_of_nonempty havail with
    ⟨c, hc⟩
  have hmem := canonicalCNLSelector_eq_some_mem hc
  have hmin : ∀ d ∈ t.available,
      CNLClass.priorityRank c <= CNLClass.priorityRank d :=
    fun d hd => canonicalCNLSelector_priorityRank_le_of_mem hc hd
  refine ⟨c, ⟨hc, hmem, hmin⟩, ?_⟩
  rintro d ⟨hd, _, _⟩
  exact canonicalCNLSelector_single_valued hd hc

/--
**Lemma J.5.1 (CNL one-step partition and entropy encoding).**

The selected-transition Finset of any visible CNL family decomposes
uniquely into the seven priority classes; the seven class sets are
pairwise disjoint, and their union equals the selected-transition set.

We expose this as the equivalent identity
`selectedTransitions = ⋃ cls, transitionsSelectedAs cls`
already proved in this file, plus the disjointness and cardinality
sum.
-/
theorem lemmaJ5_1_cnlOneStepPartition (transitions : Finset CNLTransition) :
    selectedTransitions transitions =
      Finset.biUnion (Finset.univ : Finset CNLClass)
        (transitionsSelectedAs transitions) ∧
      (selectedTransitions transitions).card =
        ∑ cls : CNLClass, (transitionsSelectedAs transitions cls).card := by
  refine ⟨?_, selectedTransitions_card_eq_sum_selectedAs transitions⟩
  exact selectedTransitions_eq_biUnion_selectedAs transitions

end

end Erdos260
