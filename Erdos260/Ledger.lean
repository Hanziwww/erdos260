import Mathlib

/-!
# Charged ledger primitives for proof_v2

The definitions here are deliberately small finite objects.  They model the
single-valued priority scan and charged output vocabulary used by Appendices I,
J, K, and L of `proof_v2.tex`; package estimates are proved later against these
objects rather than assumed here.
-/

namespace Erdos260

noncomputable section

/-- Package kinds in the proof_v2 charged output ledger. -/
inductive PackageKind where
  | densePack
  | returnPkg
  | runPkg
  | tower
  | progress
  | endpoint
deriving DecidableEq, Fintype, Repr

/-- Priority classes for the clean CNL selector and package ledger. -/
inductive PriorityClass where
  | pkg
  | sep
  | bnd
  | tc
  | vs
  | ds
  | tp
deriving DecidableEq, Fintype, Repr

/-! ### v4 output classes (Appendix N rolling-window variation-drop closure)

`proof_v4.tex` replaces the v3 same-threshold compression by the Appendix N
event-fibre map `(b,T,ζ) ↦ Θ_T^0(b,ζ)` whose target is the six-class disjoint
union

```
𝔒_D ⊔ 𝔒_P ⊔ 𝔒_E ⊔ 𝔒_CNL ⊔ 𝔒_bdd ⊔ 𝔒_V,
```

with the new variation-drop output `𝔒_V` (Lemma N.2.2).  We encode this target
as `OutputClassV4`.  The existing `PackageKind` is retained for the current
reduction; the routing of terminal non-drop outputs into D/P/E/CNL/bdd
(Lemma N.1.0 / N.3.3) and the variation-drop bound `VarDrop ≤ o(sX|I_j|)`
(Lemma N.2.2) are formalized in roadmap Phases B–E. -/
inductive OutputClassV4 where
  | densePack
  | progress
  | endpoint
  | cnl
  | bdd
  | varDrop
deriving DecidableEq, Fintype, Repr

/-- The variation-drop output class `𝔒_V`. -/
def OutputClassV4.IsVariationDrop (c : OutputClassV4) : Prop :=
  c = OutputClassV4.varDrop

instance : DecidablePred OutputClassV4.IsVariationDrop := by
  intro c
  unfold OutputClassV4.IsVariationDrop
  infer_instance

theorem OutputClassV4.isVariationDrop_iff (c : OutputClassV4) :
    c.IsVariationDrop ↔ c = OutputClassV4.varDrop := Iff.rfl

theorem OutputClassV4.varDrop_isVariationDrop :
    OutputClassV4.varDrop.IsVariationDrop := rfl

theorem OutputClassV4.not_isVariationDrop_of_ne {c : OutputClassV4}
    (h : c ≠ OutputClassV4.varDrop) : ¬ c.IsVariationDrop := h

/-- There are exactly six v4 output classes (`𝔒_D, 𝔒_P, 𝔒_E, 𝔒_CNL, 𝔒_bdd, 𝔒_V`). -/
theorem OutputClassV4.card_eq_six : Fintype.card OutputClassV4 = 6 := by decide

/-- A v4 charged output object: a class tag with support/threshold coordinates. -/
structure OutputObjectV4 where
  cls : OutputClassV4
  supportId : Nat
  thresholdLayer : Nat
deriving DecidableEq, Repr

/-- Residual variation-drop mass `VarDrop` (Lemma N.2.2): total weight of the
variation-drop outputs in a finite collection.  Phase C bounds this by
`C_Q · Y · V_s = o(s X |I_j|)`. -/
def variationDropMass (objects : Finset OutputObjectV4)
    (weight : OutputObjectV4 → ℝ) : ℝ :=
  ∑ o ∈ objects.filter (fun o => o.cls = OutputClassV4.varDrop), weight o

theorem variationDropMass_nonneg {objects : Finset OutputObjectV4}
    {weight : OutputObjectV4 → ℝ} (hw : ∀ o ∈ objects, 0 ≤ weight o) :
    0 ≤ variationDropMass objects weight := by
  unfold variationDropMass
  refine Finset.sum_nonneg ?_
  intro o ho
  exact hw o (Finset.mem_filter.mp ho).1

theorem variationDropMass_le_total {objects : Finset OutputObjectV4}
    {weight : OutputObjectV4 → ℝ} (hw : ∀ o ∈ objects, 0 ≤ weight o) :
    variationDropMass objects weight ≤ ∑ o ∈ objects, weight o := by
  unfold variationDropMass
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro o ho _
  exact hw o ho

theorem variationDropMass_eq_zero_of_no_varDrop {objects : Finset OutputObjectV4}
    {weight : OutputObjectV4 → ℝ}
    (h : ∀ o ∈ objects, o.cls ≠ OutputClassV4.varDrop) :
    variationDropMass objects weight = 0 := by
  unfold variationDropMass
  rw [Finset.filter_false_of_mem h, Finset.sum_empty]

/-- A stopped branch edge with an explicit shell cost and threshold layer. -/
structure BranchEdge where
  source : Nat
  target : Nat
  shellCost : Nat
  thresholdLayer : Nat
deriving DecidableEq, Repr

/-- A stopped branch is a finite path of edges. -/
structure StoppedBranch where
  edges : List BranchEdge
deriving DecidableEq, Repr

/-- Abstract charged output object for a package. -/
structure OutputObject where
  package : PackageKind
  supportId : Nat
  thresholdLayer : Nat
deriving DecidableEq, Repr

/-- Charged weights are nonnegative real weights carried by output objects. -/
structure ChargedWeight where
  value : ℝ
  nonneg : 0 <= value

/-- Optional result of a priority scan at one branch. -/
structure PriorityAssignment where
  priorityClass : PriorityClass
  package? : Option PackageKind
  output? : Option OutputObject
deriving DecidableEq, Repr

open Finset

/-- Deterministic priority scan from a finite list of candidate classes. -/
def firstPriority? (xs : List PriorityClass) : Option PriorityClass :=
  xs.find? fun _ => True

@[simp]
theorem firstPriority?_nil :
    firstPriority? [] = none := rfl

@[simp]
theorem firstPriority?_cons (x : PriorityClass) (xs : List PriorityClass) :
    firstPriority? (x :: xs) = some x := rfl

theorem firstPriority?_eq_some_mem {xs : List PriorityClass} {c : PriorityClass}
    (h : firstPriority? xs = some c) :
    c ∈ xs := by
  cases xs with
  | nil => simp at h
  | cons x xs =>
      simp [firstPriority?] at h
      simp [h]

theorem firstPriority?_single_valued {xs : List PriorityClass} {a b : PriorityClass}
    (ha : firstPriority? xs = some a) (hb : firstPriority? xs = some b) :
    a = b := by
  rw [ha] at hb
  exact Option.some.inj hb

/-- A branch-level priority map is single-valued by being an ordinary function. -/
def PriorityMap := StoppedBranch -> Option PriorityAssignment

theorem priorityMap_single_valued (Φ : PriorityMap) (b : StoppedBranch)
    {a₁ a₂ : PriorityAssignment}
    (h₁ : Φ b = some a₁) (h₂ : Φ b = some a₂) :
    a₁ = a₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-- Coherence condition: when an assignment emits an output, its optional
package field names the output's package. -/
def PriorityAssignment.Coherent (a : PriorityAssignment) : Prop :=
  ∀ o : OutputObject, a.output? = some o -> a.package? = some o.package

/-- Coherence of a branch-level priority map. -/
def PriorityMapCoherent (Φ : PriorityMap) : Prop :=
  ∀ b a, Φ b = some a -> a.Coherent

/-- A priority map emits at most one output from a fixed branch. -/
theorem priorityMap_output_single_valued (Φ : PriorityMap) (b : StoppedBranch)
    {o₁ o₂ : OutputObject} {a₁ a₂ : PriorityAssignment}
    (h₁ : Φ b = some a₁) (ho₁ : a₁.output? = some o₁)
    (h₂ : Φ b = some a₂) (ho₂ : a₂.output? = some o₂) :
    o₁ = o₂ := by
  have ha : a₁ = a₂ := priorityMap_single_valued Φ b h₁ h₂
  subst ha
  rw [ho₁] at ho₂
  exact Option.some.inj ho₂

theorem priorityMap_output_package_of_coherent {Φ : PriorityMap}
    (hΦ : PriorityMapCoherent Φ) {b : StoppedBranch}
    {a : PriorityAssignment} {o : OutputObject}
    (ha : Φ b = some a) (ho : a.output? = some o) :
    a.package? = some o.package :=
  hΦ b a ha o ho

/-- The optional output emitted by the priority map at a branch. -/
def branchOutput? (Φ : PriorityMap) (b : StoppedBranch) : Option OutputObject :=
  (Φ b).bind fun a => a.output?

/-- The singleton output set emitted by one branch, or empty if there is no
output. -/
def branchOutputSet (Φ : PriorityMap) (b : StoppedBranch) : Finset OutputObject :=
  match branchOutput? Φ b with
  | some o => {o}
  | none => ∅

/-- All output objects emitted by a finite branch family. -/
def branchOutputs (branches : Finset StoppedBranch) (Φ : PriorityMap) :
    Finset OutputObject :=
  branches.biUnion fun b => branchOutputSet Φ b

theorem branchOutput?_eq_some_iff {Φ : PriorityMap} {b : StoppedBranch}
    {o : OutputObject} :
    branchOutput? Φ b = some o ↔
      ∃ a : PriorityAssignment, Φ b = some a ∧ a.output? = some o := by
  unfold branchOutput?
  cases Φ b <;> simp

theorem mem_branchOutputSet {Φ : PriorityMap} {b : StoppedBranch}
    {o : OutputObject} :
    o ∈ branchOutputSet Φ b ↔ branchOutput? Φ b = some o := by
  unfold branchOutputSet
  cases branchOutput? Φ b <;> simp [eq_comm]

theorem branchOutputSet_card_le_one (Φ : PriorityMap) (b : StoppedBranch) :
    (branchOutputSet Φ b).card <= 1 := by
  unfold branchOutputSet
  cases branchOutput? Φ b <;> simp

theorem mem_branchOutputs {branches : Finset StoppedBranch} {Φ : PriorityMap}
    {o : OutputObject} :
    o ∈ branchOutputs branches Φ ↔
      ∃ b ∈ branches, branchOutput? Φ b = some o := by
  unfold branchOutputs
  simp [mem_branchOutputSet]

theorem branchOutput?_package_of_coherent {Φ : PriorityMap}
    (hΦ : PriorityMapCoherent Φ) {b : StoppedBranch} {o : OutputObject}
    (ho : branchOutput? Φ b = some o) :
    ∃ a : PriorityAssignment, Φ b = some a ∧
      a.output? = some o ∧ a.package? = some o.package := by
  rcases branchOutput?_eq_some_iff.1 ho with ⟨a, ha, hao⟩
  exact ⟨a, ha, hao, priorityMap_output_package_of_coherent hΦ ha hao⟩

theorem branchOutputs_card_le (branches : Finset StoppedBranch) (Φ : PriorityMap) :
    (branchOutputs branches Φ).card <= branches.card := by
  unfold branchOutputs
  calc
    (branches.biUnion fun b => branchOutputSet Φ b).card
        <= ∑ b ∈ branches, (branchOutputSet Φ b).card := by
          exact card_biUnion_le
    _ <= ∑ _b ∈ branches, 1 := by
          exact sum_le_sum fun b _ => branchOutputSet_card_le_one Φ b
    _ = branches.card := by
          simp

theorem branchOutputs_mono_subset {branches₁ branches₂ : Finset StoppedBranch}
    {Φ : PriorityMap} (h : branches₁ ⊆ branches₂) :
    branchOutputs branches₁ Φ ⊆ branchOutputs branches₂ Φ := by
  intro o ho
  rcases mem_branchOutputs.1 ho with ⟨b, hb, hout⟩
  exact mem_branchOutputs.2 ⟨b, h hb, hout⟩

/-- Output objects belonging to one package kind. -/
def outputsOf (objects : Finset OutputObject) (kind : PackageKind) :
    Finset OutputObject :=
  objects.filter fun o => o.package = kind

/-- Outputs emitted by a branch family and belonging to one package kind. -/
def branchOutputsOf (branches : Finset StoppedBranch) (Φ : PriorityMap)
    (kind : PackageKind) : Finset OutputObject :=
  outputsOf (branchOutputs branches Φ) kind

theorem mem_outputsOf {objects : Finset OutputObject} {kind : PackageKind}
    {o : OutputObject} :
    o ∈ outputsOf objects kind ↔ o ∈ objects ∧ o.package = kind := by
  simp [outputsOf]

theorem outputsOf_subset (objects : Finset OutputObject) (kind : PackageKind) :
    outputsOf objects kind ⊆ objects := by
  intro o ho
  exact (mem_outputsOf.1 ho).1

theorem outputsOf_mono_subset {s t : Finset OutputObject} {kind : PackageKind}
    (hst : s ⊆ t) :
    outputsOf s kind ⊆ outputsOf t kind := by
  intro o ho
  exact mem_outputsOf.2 ⟨hst (mem_outputsOf.1 ho).1, (mem_outputsOf.1 ho).2⟩

theorem mem_branchOutputsOf {branches : Finset StoppedBranch}
    {Φ : PriorityMap} {kind : PackageKind} {o : OutputObject} :
    o ∈ branchOutputsOf branches Φ kind ↔
      (∃ b ∈ branches, branchOutput? Φ b = some o) ∧ o.package = kind := by
  simp [branchOutputsOf, mem_outputsOf, mem_branchOutputs]

theorem branchOutputsOf_subset (branches : Finset StoppedBranch)
    (Φ : PriorityMap) (kind : PackageKind) :
    branchOutputsOf branches Φ kind ⊆ branchOutputs branches Φ :=
  outputsOf_subset (branchOutputs branches Φ) kind

theorem branchOutputsOf_mono_subset {branches₁ branches₂ : Finset StoppedBranch}
    {Φ : PriorityMap} {kind : PackageKind} (h : branches₁ ⊆ branches₂) :
    branchOutputsOf branches₁ Φ kind ⊆ branchOutputsOf branches₂ Φ kind :=
  outputsOf_mono_subset (branchOutputs_mono_subset h)

theorem branchOutputsOf_card_le (branches : Finset StoppedBranch)
    (Φ : PriorityMap) (kind : PackageKind) :
    (branchOutputsOf branches Φ kind).card <= branches.card := by
  exact (card_le_card (branchOutputsOf_subset branches Φ kind)).trans
    (branchOutputs_card_le branches Φ)

theorem not_mem_outputsOf_both_of_ne {objects : Finset OutputObject}
    {kind₁ kind₂ : PackageKind} (hneq : kind₁ ≠ kind₂) {o : OutputObject}
    (h₁ : o ∈ outputsOf objects kind₁) (h₂ : o ∈ outputsOf objects kind₂) :
    False := by
  have hk₁ := (mem_outputsOf.1 h₁).2
  have hk₂ := (mem_outputsOf.1 h₂).2
  exact hneq (hk₁.symm.trans hk₂)

theorem outputsOf_inter_eq_empty_of_ne {objects : Finset OutputObject}
    {kind₁ kind₂ : PackageKind} (hneq : kind₁ ≠ kind₂) :
    outputsOf objects kind₁ ∩ outputsOf objects kind₂ = ∅ := by
  ext o
  constructor
  · intro ho
    rcases mem_inter.1 ho with ⟨h₁, h₂⟩
    exact False.elim (not_mem_outputsOf_both_of_ne hneq h₁ h₂)
  · intro ho
    simp at ho

theorem disjoint_outputsOf_of_ne {objects : Finset OutputObject}
    {kind₁ kind₂ : PackageKind} (hneq : kind₁ ≠ kind₂) :
    Disjoint (outputsOf objects kind₁) (outputsOf objects kind₂) := by
  rw [disjoint_left]
  intro o ho₁ ho₂
  exact not_mem_outputsOf_both_of_ne hneq ho₁ ho₂

/-- Outputs with a fixed support identifier. -/
def outputsWithSupport (objects : Finset OutputObject) (supportId : Nat) :
    Finset OutputObject :=
  objects.filter fun o => o.supportId = supportId

/-- Support identifiers appearing in a finite output set. -/
def supportIds (objects : Finset OutputObject) : Finset Nat :=
  objects.image OutputObject.supportId

/-- Outputs at a fixed threshold layer. -/
def outputsAtThreshold (objects : Finset OutputObject) (layer : Nat) :
    Finset OutputObject :=
  objects.filter fun o => o.thresholdLayer = layer

/-- Threshold layers appearing in a finite output set. -/
def thresholdLayers (objects : Finset OutputObject) : Finset Nat :=
  objects.image OutputObject.thresholdLayer

theorem mem_outputsWithSupport {objects : Finset OutputObject} {supportId : Nat}
    {o : OutputObject} :
    o ∈ outputsWithSupport objects supportId ↔
      o ∈ objects ∧ o.supportId = supportId := by
  simp [outputsWithSupport]

theorem mem_supportIds {objects : Finset OutputObject} {supportId : Nat} :
    supportId ∈ supportIds objects ↔
      ∃ o ∈ objects, o.supportId = supportId := by
  simp [supportIds]

theorem mem_outputsAtThreshold {objects : Finset OutputObject} {layer : Nat}
    {o : OutputObject} :
    o ∈ outputsAtThreshold objects layer ↔
      o ∈ objects ∧ o.thresholdLayer = layer := by
  simp [outputsAtThreshold]

theorem mem_thresholdLayers {objects : Finset OutputObject} {layer : Nat} :
    layer ∈ thresholdLayers objects ↔
      ∃ o ∈ objects, o.thresholdLayer = layer := by
  simp [thresholdLayers]

theorem outputsWithSupport_subset (objects : Finset OutputObject)
    (supportId : Nat) :
    outputsWithSupport objects supportId ⊆ objects := by
  intro o ho
  exact (mem_outputsWithSupport.1 ho).1

theorem outputsAtThreshold_subset (objects : Finset OutputObject)
    (layer : Nat) :
    outputsAtThreshold objects layer ⊆ objects := by
  intro o ho
  exact (mem_outputsAtThreshold.1 ho).1

theorem outputsWithSupport_card_le (objects : Finset OutputObject)
    (supportId : Nat) :
    (outputsWithSupport objects supportId).card <= objects.card :=
  card_le_card (outputsWithSupport_subset objects supportId)

theorem outputsAtThreshold_card_le (objects : Finset OutputObject)
    (layer : Nat) :
    (outputsAtThreshold objects layer).card <= objects.card :=
  card_le_card (outputsAtThreshold_subset objects layer)

theorem supportIds_card_le (objects : Finset OutputObject) :
    (supportIds objects).card <= objects.card := by
  simpa [supportIds] using
    (card_image_le (s := objects) (f := OutputObject.supportId))

theorem thresholdLayers_card_le (objects : Finset OutputObject) :
    (thresholdLayers objects).card <= objects.card := by
  simpa [thresholdLayers] using
    (card_image_le (s := objects) (f := OutputObject.thresholdLayer))

theorem supportIds_mono_subset {s t : Finset OutputObject} (hst : s ⊆ t) :
    supportIds s ⊆ supportIds t := by
  intro supportId hs
  rcases mem_supportIds.1 hs with ⟨o, ho, hid⟩
  exact mem_supportIds.2 ⟨o, hst ho, hid⟩

theorem thresholdLayers_mono_subset {s t : Finset OutputObject} (hst : s ⊆ t) :
    thresholdLayers s ⊆ thresholdLayers t := by
  intro layer hs
  rcases mem_thresholdLayers.1 hs with ⟨o, ho, hlayer⟩
  exact mem_thresholdLayers.2 ⟨o, hst ho, hlayer⟩

theorem outputsWithSupport_mono_subset {s t : Finset OutputObject}
    {supportId : Nat} (hst : s ⊆ t) :
    outputsWithSupport s supportId ⊆ outputsWithSupport t supportId := by
  intro o ho
  exact mem_outputsWithSupport.2
    ⟨hst (mem_outputsWithSupport.1 ho).1, (mem_outputsWithSupport.1 ho).2⟩

theorem outputsAtThreshold_mono_subset {s t : Finset OutputObject}
    {layer : Nat} (hst : s ⊆ t) :
    outputsAtThreshold s layer ⊆ outputsAtThreshold t layer := by
  intro o ho
  exact mem_outputsAtThreshold.2
    ⟨hst (mem_outputsAtThreshold.1 ho).1, (mem_outputsAtThreshold.1 ho).2⟩

theorem disjoint_outputsWithSupport_of_ne {objects : Finset OutputObject}
    {supportId₁ supportId₂ : Nat} (hne : supportId₁ ≠ supportId₂) :
    Disjoint (outputsWithSupport objects supportId₁)
      (outputsWithSupport objects supportId₂) := by
  rw [disjoint_left]
  intro o ho₁ ho₂
  exact hne ((mem_outputsWithSupport.1 ho₁).2.symm.trans
    (mem_outputsWithSupport.1 ho₂).2)

theorem disjoint_outputsAtThreshold_of_ne {objects : Finset OutputObject}
    {layer₁ layer₂ : Nat} (hne : layer₁ ≠ layer₂) :
    Disjoint (outputsAtThreshold objects layer₁)
      (outputsAtThreshold objects layer₂) := by
  rw [disjoint_left]
  intro o ho₁ ho₂
  exact hne ((mem_outputsAtThreshold.1 ho₁).2.symm.trans
    (mem_outputsAtThreshold.1 ho₂).2)

theorem pairwiseDisjoint_outputsOf (objects : Finset OutputObject) :
    ((Finset.univ : Finset PackageKind) : Set PackageKind).PairwiseDisjoint
      (outputsOf objects) := by
  intro kind₁ _ kind₂ _ hne
  exact disjoint_outputsOf_of_ne hne

theorem pairwiseDisjoint_outputsWithSupport (objects : Finset OutputObject) :
    ((supportIds objects : Finset Nat) : Set Nat).PairwiseDisjoint
      (outputsWithSupport objects) := by
  intro supportId₁ _ supportId₂ _ hne
  exact disjoint_outputsWithSupport_of_ne hne

theorem pairwiseDisjoint_outputsAtThreshold (objects : Finset OutputObject) :
    ((thresholdLayers objects : Finset Nat) : Set Nat).PairwiseDisjoint
      (outputsAtThreshold objects) := by
  intro layer₁ _ layer₂ _ hne
  exact disjoint_outputsAtThreshold_of_ne hne

theorem objects_eq_biUnion_outputsOf_univ (objects : Finset OutputObject) :
    objects = (Finset.univ : Finset PackageKind).biUnion (outputsOf objects) := by
  ext o
  constructor
  · intro ho
    exact mem_biUnion.2
      ⟨o.package, by simp, mem_outputsOf.2 ⟨ho, rfl⟩⟩
  · intro ho
    rcases mem_biUnion.1 ho with ⟨kind, _, hokind⟩
    exact (mem_outputsOf.1 hokind).1

theorem objects_card_eq_sum_outputsOf (objects : Finset OutputObject) :
    objects.card = ∑ kind : PackageKind, (outputsOf objects kind).card := by
  calc
    objects.card =
        ((Finset.univ : Finset PackageKind).biUnion (outputsOf objects)).card := by
          exact congrArg Finset.card (objects_eq_biUnion_outputsOf_univ objects)
    _ = ∑ kind : PackageKind, (outputsOf objects kind).card := by
          exact card_biUnion (pairwiseDisjoint_outputsOf objects)

theorem objects_eq_biUnion_outputsWithSupport (objects : Finset OutputObject) :
    objects = (supportIds objects).biUnion (outputsWithSupport objects) := by
  ext o
  constructor
  · intro ho
    exact mem_biUnion.2
      ⟨o.supportId, mem_supportIds.2 ⟨o, ho, rfl⟩,
        mem_outputsWithSupport.2 ⟨ho, rfl⟩⟩
  · intro ho
    rcases mem_biUnion.1 ho with ⟨supportId, _, hosupport⟩
    exact (mem_outputsWithSupport.1 hosupport).1

theorem objects_card_eq_sum_outputsWithSupport (objects : Finset OutputObject) :
    objects.card =
      ∑ supportId ∈ supportIds objects, (outputsWithSupport objects supportId).card := by
  calc
    objects.card =
        ((supportIds objects).biUnion (outputsWithSupport objects)).card := by
          exact congrArg Finset.card (objects_eq_biUnion_outputsWithSupport objects)
    _ = ∑ supportId ∈ supportIds objects,
        (outputsWithSupport objects supportId).card := by
          exact card_biUnion (pairwiseDisjoint_outputsWithSupport objects)

theorem objects_eq_biUnion_outputsAtThreshold (objects : Finset OutputObject) :
    objects = (thresholdLayers objects).biUnion (outputsAtThreshold objects) := by
  ext o
  constructor
  · intro ho
    exact mem_biUnion.2
      ⟨o.thresholdLayer, mem_thresholdLayers.2 ⟨o, ho, rfl⟩,
        mem_outputsAtThreshold.2 ⟨ho, rfl⟩⟩
  · intro ho
    rcases mem_biUnion.1 ho with ⟨layer, _, holayer⟩
    exact (mem_outputsAtThreshold.1 holayer).1

theorem objects_card_eq_sum_outputsAtThreshold (objects : Finset OutputObject) :
    objects.card =
      ∑ layer ∈ thresholdLayers objects, (outputsAtThreshold objects layer).card := by
  calc
    objects.card =
        ((thresholdLayers objects).biUnion (outputsAtThreshold objects)).card := by
          exact congrArg Finset.card (objects_eq_biUnion_outputsAtThreshold objects)
    _ = ∑ layer ∈ thresholdLayers objects,
        (outputsAtThreshold objects layer).card := by
          exact card_biUnion (pairwiseDisjoint_outputsAtThreshold objects)

theorem outputsWithSupport_nonempty_iff_mem_supportIds
    {objects : Finset OutputObject} {supportId : Nat} :
    (outputsWithSupport objects supportId).Nonempty ↔
      supportId ∈ supportIds objects := by
  constructor
  · intro hnonempty
    rcases hnonempty with ⟨o, ho⟩
    exact mem_supportIds.2
      ⟨o, (mem_outputsWithSupport.1 ho).1,
        (mem_outputsWithSupport.1 ho).2⟩
  · intro hmem
    rcases mem_supportIds.1 hmem with ⟨o, ho, hid⟩
    exact ⟨o, mem_outputsWithSupport.2 ⟨ho, hid⟩⟩

theorem outputsAtThreshold_nonempty_iff_mem_thresholdLayers
    {objects : Finset OutputObject} {layer : Nat} :
    (outputsAtThreshold objects layer).Nonempty ↔
      layer ∈ thresholdLayers objects := by
  constructor
  · intro hnonempty
    rcases hnonempty with ⟨o, ho⟩
    exact mem_thresholdLayers.2
      ⟨o, (mem_outputsAtThreshold.1 ho).1,
        (mem_outputsAtThreshold.1 ho).2⟩
  · intro hmem
    rcases mem_thresholdLayers.1 hmem with ⟨o, ho, hlayer⟩
    exact ⟨o, mem_outputsAtThreshold.2 ⟨ho, hlayer⟩⟩

theorem outputsWithSupport_eq_empty_of_not_mem_supportIds
    {objects : Finset OutputObject} {supportId : Nat}
    (hnot : supportId ∉ supportIds objects) :
    outputsWithSupport objects supportId = ∅ := by
  ext o
  constructor
  · intro ho
    exact False.elim
      (hnot (outputsWithSupport_nonempty_iff_mem_supportIds.1 ⟨o, ho⟩))
  · intro ho
    simp at ho

theorem outputsAtThreshold_eq_empty_of_not_mem_thresholdLayers
    {objects : Finset OutputObject} {layer : Nat}
    (hnot : layer ∉ thresholdLayers objects) :
    outputsAtThreshold objects layer = ∅ := by
  ext o
  constructor
  · intro ho
    exact False.elim
      (hnot (outputsAtThreshold_nonempty_iff_mem_thresholdLayers.1 ⟨o, ho⟩))
  · intro ho
    simp at ho

/-- Total charged mass over a finite output set. -/
def chargedMass (objects : Finset OutputObject) (weight : OutputObject -> ℝ) :
    ℝ :=
  ∑ o ∈ objects, weight o

theorem chargedMass_nonneg {objects : Finset OutputObject}
    {weight : OutputObject -> ℝ}
    (hweight : ∀ o ∈ objects, 0 <= weight o) :
    0 <= chargedMass objects weight := by
  unfold chargedMass
  exact sum_nonneg hweight

theorem chargedMass_mono_subset {s t : Finset OutputObject}
    {weight : OutputObject -> ℝ} (hst : s ⊆ t)
    (hweight : ∀ o ∈ t, 0 <= weight o) :
    chargedMass s weight <= chargedMass t weight := by
  unfold chargedMass
  exact sum_le_sum_of_subset_of_nonneg hst fun o ho _ => hweight o ho

theorem chargedMass_outputsOf_le {objects : Finset OutputObject}
    {kind : PackageKind} {weight : OutputObject -> ℝ}
    (hweight : ∀ o ∈ objects, 0 <= weight o) :
    chargedMass (outputsOf objects kind) weight <= chargedMass objects weight :=
  chargedMass_mono_subset (outputsOf_subset objects kind) hweight

theorem chargedMass_outputsWithSupport_le {objects : Finset OutputObject}
    {supportId : Nat} {weight : OutputObject -> ℝ}
    (hweight : ∀ o ∈ objects, 0 <= weight o) :
    chargedMass (outputsWithSupport objects supportId) weight <=
      chargedMass objects weight :=
  chargedMass_mono_subset (outputsWithSupport_subset objects supportId) hweight

theorem chargedMass_outputsAtThreshold_le {objects : Finset OutputObject}
    {layer : Nat} {weight : OutputObject -> ℝ}
    (hweight : ∀ o ∈ objects, 0 <= weight o) :
    chargedMass (outputsAtThreshold objects layer) weight <=
      chargedMass objects weight :=
  chargedMass_mono_subset (outputsAtThreshold_subset objects layer) hweight

theorem chargedMass_eq_sum_outputsOf_univ
    (objects : Finset OutputObject) (weight : OutputObject -> ℝ) :
    chargedMass objects weight =
      ∑ kind : PackageKind, chargedMass (outputsOf objects kind) weight := by
  unfold chargedMass outputsOf
  have hmap :
      ∀ o ∈ objects, o.package ∈ (Finset.univ : Finset PackageKind) := by
    intro o _
    simp
  symm
  simpa using
    (Finset.sum_fiberwise_of_maps_to
      (s := objects)
      (t := (Finset.univ : Finset PackageKind))
      hmap
      weight)

theorem chargedMass_eq_sum_outputsWithSupport
    (objects : Finset OutputObject) (weight : OutputObject -> ℝ) :
    chargedMass objects weight =
      ∑ supportId ∈ supportIds objects,
        chargedMass (outputsWithSupport objects supportId) weight := by
  unfold chargedMass outputsWithSupport supportIds
  have hmap :
      ∀ o ∈ objects, o.supportId ∈ objects.image OutputObject.supportId := by
    intro o ho
    exact mem_image.2 ⟨o, ho, rfl⟩
  symm
  simpa using
    (Finset.sum_fiberwise_of_maps_to
      (s := objects)
      (t := objects.image OutputObject.supportId)
      hmap
      weight)

theorem chargedMass_eq_sum_outputsAtThreshold
    (objects : Finset OutputObject) (weight : OutputObject -> ℝ) :
    chargedMass objects weight =
      ∑ layer ∈ thresholdLayers objects,
        chargedMass (outputsAtThreshold objects layer) weight := by
  unfold chargedMass outputsAtThreshold thresholdLayers
  have hmap :
      ∀ o ∈ objects, o.thresholdLayer ∈ objects.image OutputObject.thresholdLayer := by
    intro o ho
    exact mem_image.2 ⟨o, ho, rfl⟩
  symm
  simpa using
    (Finset.sum_fiberwise_of_maps_to
      (s := objects)
      (t := objects.image OutputObject.thresholdLayer)
      hmap
      weight)

/-- Total package cost over a finite output set. -/
def packageCost (objects : Finset OutputObject) (cost : OutputObject -> ℝ) :
    ℝ :=
  ∑ o ∈ objects, cost o

theorem packageCost_nonneg {objects : Finset OutputObject}
    {cost : OutputObject -> ℝ}
    (hcost : ∀ o ∈ objects, 0 <= cost o) :
    0 <= packageCost objects cost := by
  unfold packageCost
  exact sum_nonneg hcost

theorem packageCost_mono_subset {s t : Finset OutputObject}
    {cost : OutputObject -> ℝ} (hst : s ⊆ t)
    (hcost : ∀ o ∈ t, 0 <= cost o) :
    packageCost s cost <= packageCost t cost := by
  unfold packageCost
  exact sum_le_sum_of_subset_of_nonneg hst fun o ho _ => hcost o ho

theorem packageCost_eq_sum_outputsOf_univ
    (objects : Finset OutputObject) (cost : OutputObject -> ℝ) :
    packageCost objects cost =
      ∑ kind : PackageKind, packageCost (outputsOf objects kind) cost := by
  unfold packageCost outputsOf
  have hmap :
      ∀ o ∈ objects, o.package ∈ (Finset.univ : Finset PackageKind) := by
    intro o _
    simp
  symm
  simpa using
    (Finset.sum_fiberwise_of_maps_to
      (s := objects)
      (t := (Finset.univ : Finset PackageKind))
      hmap
      cost)

theorem packageCost_eq_sum_outputsWithSupport
    (objects : Finset OutputObject) (cost : OutputObject -> ℝ) :
    packageCost objects cost =
      ∑ supportId ∈ supportIds objects,
        packageCost (outputsWithSupport objects supportId) cost := by
  unfold packageCost outputsWithSupport supportIds
  have hmap :
      ∀ o ∈ objects, o.supportId ∈ objects.image OutputObject.supportId := by
    intro o ho
    exact mem_image.2 ⟨o, ho, rfl⟩
  symm
  simpa using
    (Finset.sum_fiberwise_of_maps_to
      (s := objects)
      (t := objects.image OutputObject.supportId)
      hmap
      cost)

theorem packageCost_eq_sum_outputsAtThreshold
    (objects : Finset OutputObject) (cost : OutputObject -> ℝ) :
    packageCost objects cost =
      ∑ layer ∈ thresholdLayers objects,
        packageCost (outputsAtThreshold objects layer) cost := by
  unfold packageCost outputsAtThreshold thresholdLayers
  have hmap :
      ∀ o ∈ objects, o.thresholdLayer ∈ objects.image OutputObject.thresholdLayer := by
    intro o ho
    exact mem_image.2 ⟨o, ho, rfl⟩
  symm
  simpa using
    (Finset.sum_fiberwise_of_maps_to
      (s := objects)
      (t := objects.image OutputObject.thresholdLayer)
      hmap
      cost)

/-- If each output in a package costs at most `C` times its charged weight, then
the whole package cost is controlled by the package charged mass. -/
theorem packageCost_outputsOf_le_const_mul_chargedMass
    {objects : Finset OutputObject} {kind : PackageKind}
    {cost weight : OutputObject -> ℝ} {C : ℝ}
    (hpoint : ∀ o ∈ outputsOf objects kind, cost o <= C * weight o) :
    packageCost (outputsOf objects kind) cost <=
      C * chargedMass (outputsOf objects kind) weight := by
  unfold packageCost chargedMass
  calc
    (∑ o ∈ outputsOf objects kind, cost o)
        <= ∑ o ∈ outputsOf objects kind, C * weight o := by
          exact sum_le_sum hpoint
    _ = C * (∑ o ∈ outputsOf objects kind, weight o) := by
          rw [mul_sum]

theorem packageCost_outputsWithSupport_le_const_mul_chargedMass
    {objects : Finset OutputObject} {supportId : Nat}
    {cost weight : OutputObject -> ℝ} {C : ℝ}
    (hpoint :
      ∀ o ∈ outputsWithSupport objects supportId, cost o <= C * weight o) :
    packageCost (outputsWithSupport objects supportId) cost <=
      C * chargedMass (outputsWithSupport objects supportId) weight := by
  unfold packageCost chargedMass
  calc
    (∑ o ∈ outputsWithSupport objects supportId, cost o)
        <= ∑ o ∈ outputsWithSupport objects supportId, C * weight o := by
          exact sum_le_sum hpoint
    _ = C * (∑ o ∈ outputsWithSupport objects supportId, weight o) := by
          rw [mul_sum]

theorem packageCost_outputsAtThreshold_le_const_mul_chargedMass
    {objects : Finset OutputObject} {layer : Nat}
    {cost weight : OutputObject -> ℝ} {C : ℝ}
    (hpoint :
      ∀ o ∈ outputsAtThreshold objects layer, cost o <= C * weight o) :
    packageCost (outputsAtThreshold objects layer) cost <=
      C * chargedMass (outputsAtThreshold objects layer) weight := by
  unfold packageCost chargedMass
  calc
    (∑ o ∈ outputsAtThreshold objects layer, cost o)
        <= ∑ o ∈ outputsAtThreshold objects layer, C * weight o := by
          exact sum_le_sum hpoint
    _ = C * (∑ o ∈ outputsAtThreshold objects layer, weight o) := by
          rw [mul_sum]

theorem packageCost_outputsOf_le_const_mul_total_chargedMass
    {objects : Finset OutputObject} {kind : PackageKind}
    {cost weight : OutputObject -> ℝ} {C : ℝ}
    (hC : 0 <= C) (hweight : ∀ o ∈ objects, 0 <= weight o)
    (hpoint : ∀ o ∈ outputsOf objects kind, cost o <= C * weight o) :
    packageCost (outputsOf objects kind) cost <= C * chargedMass objects weight := by
  exact (packageCost_outputsOf_le_const_mul_chargedMass hpoint).trans
    (mul_le_mul_of_nonneg_left
      (chargedMass_outputsOf_le (kind := kind) hweight) hC)

theorem packageCost_outputsWithSupport_le_const_mul_total_chargedMass
    {objects : Finset OutputObject} {supportId : Nat}
    {cost weight : OutputObject -> ℝ} {C : ℝ}
    (hC : 0 <= C) (hweight : ∀ o ∈ objects, 0 <= weight o)
    (hpoint :
      ∀ o ∈ outputsWithSupport objects supportId, cost o <= C * weight o) :
    packageCost (outputsWithSupport objects supportId) cost <=
      C * chargedMass objects weight := by
  exact (packageCost_outputsWithSupport_le_const_mul_chargedMass hpoint).trans
    (mul_le_mul_of_nonneg_left
      (chargedMass_outputsWithSupport_le (supportId := supportId) hweight) hC)

theorem packageCost_outputsAtThreshold_le_const_mul_total_chargedMass
    {objects : Finset OutputObject} {layer : Nat}
    {cost weight : OutputObject -> ℝ} {C : ℝ}
    (hC : 0 <= C) (hweight : ∀ o ∈ objects, 0 <= weight o)
    (hpoint :
      ∀ o ∈ outputsAtThreshold objects layer, cost o <= C * weight o) :
    packageCost (outputsAtThreshold objects layer) cost <=
      C * chargedMass objects weight := by
  exact (packageCost_outputsAtThreshold_le_const_mul_chargedMass hpoint).trans
    (mul_le_mul_of_nonneg_left
      (chargedMass_outputsAtThreshold_le (layer := layer) hweight) hC)

theorem packageCost_le_sum_package_const_mul_chargedMass
    {objects : Finset OutputObject} {cost weight : OutputObject -> ℝ}
    {C : PackageKind -> ℝ}
    (hpoint :
      ∀ kind o, o ∈ outputsOf objects kind -> cost o <= C kind * weight o) :
    packageCost objects cost <=
      ∑ kind : PackageKind, C kind * chargedMass (outputsOf objects kind) weight := by
  calc
    packageCost objects cost =
        ∑ kind : PackageKind, packageCost (outputsOf objects kind) cost := by
          exact packageCost_eq_sum_outputsOf_univ objects cost
    _ <= ∑ kind : PackageKind, C kind * chargedMass (outputsOf objects kind) weight := by
          exact sum_le_sum fun kind _ =>
            packageCost_outputsOf_le_const_mul_chargedMass
              (objects := objects) (kind := kind)
              (cost := cost) (weight := weight) (C := C kind)
              (hpoint kind)

theorem packageCost_le_uniform_const_mul_chargedMass
    {objects : Finset OutputObject} {cost weight : OutputObject -> ℝ}
    {Cmax : ℝ} {C : PackageKind -> ℝ}
    (hC : ∀ kind : PackageKind, C kind <= Cmax)
    (hweight : ∀ o ∈ objects, 0 <= weight o)
    (hpoint :
      ∀ kind o, o ∈ outputsOf objects kind -> cost o <= C kind * weight o) :
    packageCost objects cost <= Cmax * chargedMass objects weight := by
  have hmass_nonneg :
      ∀ kind : PackageKind, 0 <= chargedMass (outputsOf objects kind) weight := by
    intro kind
    exact chargedMass_nonneg fun o ho =>
      hweight o (mem_outputsOf.1 ho).1
  calc
    packageCost objects cost
        <= ∑ kind : PackageKind, C kind * chargedMass (outputsOf objects kind) weight := by
          exact packageCost_le_sum_package_const_mul_chargedMass hpoint
    _ <= ∑ kind : PackageKind, Cmax * chargedMass (outputsOf objects kind) weight := by
          exact sum_le_sum fun kind _ =>
            mul_le_mul_of_nonneg_right (hC kind) (hmass_nonneg kind)
    _ = Cmax * (∑ kind : PackageKind, chargedMass (outputsOf objects kind) weight) := by
          rw [mul_sum]
    _ = Cmax * chargedMass objects weight := by
          rw [← chargedMass_eq_sum_outputsOf_univ]

theorem chargedMass_branchOutputsOf_le {branches : Finset StoppedBranch}
    {Φ : PriorityMap} {kind : PackageKind} {weight : OutputObject -> ℝ}
    (hweight : ∀ o ∈ branchOutputs branches Φ, 0 <= weight o) :
    chargedMass (branchOutputsOf branches Φ kind) weight <=
      chargedMass (branchOutputs branches Φ) weight :=
  chargedMass_outputsOf_le (objects := branchOutputs branches Φ)
    (kind := kind) hweight

theorem chargedMass_branchOutputs_mono_subset
    {branches₁ branches₂ : Finset StoppedBranch} {Φ : PriorityMap}
    {weight : OutputObject -> ℝ}
    (hbranches : branches₁ ⊆ branches₂)
    (hweight : ∀ o ∈ branchOutputs branches₂ Φ, 0 <= weight o) :
    chargedMass (branchOutputs branches₁ Φ) weight <=
      chargedMass (branchOutputs branches₂ Φ) weight :=
  chargedMass_mono_subset (branchOutputs_mono_subset hbranches) hweight

theorem chargedMass_branchOutputsOf_mono_subset
    {branches₁ branches₂ : Finset StoppedBranch} {Φ : PriorityMap}
    {kind : PackageKind} {weight : OutputObject -> ℝ}
    (hbranches : branches₁ ⊆ branches₂)
    (hweight : ∀ o ∈ branchOutputsOf branches₂ Φ kind, 0 <= weight o) :
    chargedMass (branchOutputsOf branches₁ Φ kind) weight <=
      chargedMass (branchOutputsOf branches₂ Φ kind) weight :=
  chargedMass_mono_subset (branchOutputsOf_mono_subset hbranches) hweight

theorem packageCost_branchOutputsOf_le_const_mul_chargedMass
    {branches : Finset StoppedBranch} {Φ : PriorityMap}
    {kind : PackageKind} {cost weight : OutputObject -> ℝ} {C : ℝ}
    (hpoint :
      ∀ o ∈ branchOutputsOf branches Φ kind, cost o <= C * weight o) :
    packageCost (branchOutputsOf branches Φ kind) cost <=
      C * chargedMass (branchOutputsOf branches Φ kind) weight :=
  packageCost_outputsOf_le_const_mul_chargedMass
    (objects := branchOutputs branches Φ) (kind := kind) hpoint

theorem packageCost_branchOutputs_mono_subset
    {branches₁ branches₂ : Finset StoppedBranch} {Φ : PriorityMap}
    {cost : OutputObject -> ℝ}
    (hbranches : branches₁ ⊆ branches₂)
    (hcost : ∀ o ∈ branchOutputs branches₂ Φ, 0 <= cost o) :
    packageCost (branchOutputs branches₁ Φ) cost <=
      packageCost (branchOutputs branches₂ Φ) cost :=
  packageCost_mono_subset (branchOutputs_mono_subset hbranches) hcost

theorem packageCost_branchOutputsOf_mono_subset
    {branches₁ branches₂ : Finset StoppedBranch} {Φ : PriorityMap}
    {kind : PackageKind} {cost : OutputObject -> ℝ}
    (hbranches : branches₁ ⊆ branches₂)
    (hcost : ∀ o ∈ branchOutputsOf branches₂ Φ kind, 0 <= cost o) :
    packageCost (branchOutputsOf branches₁ Φ kind) cost <=
      packageCost (branchOutputsOf branches₂ Φ kind) cost :=
  packageCost_mono_subset (branchOutputsOf_mono_subset hbranches) hcost

theorem packageCost_branchOutputsOf_le_const_mul_total_chargedMass
    {branches : Finset StoppedBranch} {Φ : PriorityMap}
    {kind : PackageKind} {cost weight : OutputObject -> ℝ} {C : ℝ}
    (hC : 0 <= C)
    (hweight : ∀ o ∈ branchOutputs branches Φ, 0 <= weight o)
    (hpoint :
      ∀ o ∈ branchOutputsOf branches Φ kind, cost o <= C * weight o) :
    packageCost (branchOutputsOf branches Φ kind) cost <=
      C * chargedMass (branchOutputs branches Φ) weight :=
  packageCost_outputsOf_le_const_mul_total_chargedMass
    (objects := branchOutputs branches Φ) (kind := kind) hC hweight hpoint

theorem packageCost_branchOutputs_le_sum_package_const_mul_chargedMass
    {branches : Finset StoppedBranch} {Φ : PriorityMap}
    {cost weight : OutputObject -> ℝ} {C : PackageKind -> ℝ}
    (hpoint :
      ∀ kind o, o ∈ branchOutputsOf branches Φ kind ->
        cost o <= C kind * weight o) :
    packageCost (branchOutputs branches Φ) cost <=
      ∑ kind : PackageKind,
        C kind * chargedMass (branchOutputsOf branches Φ kind) weight :=
  packageCost_le_sum_package_const_mul_chargedMass
    (objects := branchOutputs branches Φ) (cost := cost) (weight := weight)
    (C := C) hpoint

theorem packageCost_branchOutputs_le_uniform_const_mul_chargedMass
    {branches : Finset StoppedBranch} {Φ : PriorityMap}
    {cost weight : OutputObject -> ℝ} {Cmax : ℝ} {C : PackageKind -> ℝ}
    (hC : ∀ kind : PackageKind, C kind <= Cmax)
    (hweight : ∀ o ∈ branchOutputs branches Φ, 0 <= weight o)
    (hpoint :
      ∀ kind o, o ∈ branchOutputsOf branches Φ kind ->
        cost o <= C kind * weight o) :
    packageCost (branchOutputs branches Φ) cost <=
      Cmax * chargedMass (branchOutputs branches Φ) weight :=
  packageCost_le_uniform_const_mul_chargedMass
    (objects := branchOutputs branches Φ) (cost := cost) (weight := weight)
    (Cmax := Cmax) (C := C) hC hweight hpoint

/-- Packages that can feed the Return/Run/Tower cycle if the threshold does not
increase. -/
def IsFeedbackPackage : PackageKind -> Prop
  | .returnPkg => True
  | .runPkg => True
  | .tower => True
  | _ => False

instance (kind : PackageKind) : Decidable (IsFeedbackPackage kind) := by
  cases kind <;> simp [IsFeedbackPackage] <;> infer_instance

/-- A finite output family has no same-threshold feedback at layer `j`. -/
def SameLevelFeedbackFree (objects : Finset OutputObject) (j : Nat) : Prop :=
  ∀ o ∈ objects, IsFeedbackPackage o.package -> j < o.thresholdLayer

/-- The outputs of a branch family have no Return/Run/Tower feedback at the same
threshold layer. -/
def BranchOutputsFeedbackFree (branches : Finset StoppedBranch)
    (Φ : PriorityMap) (j : Nat) : Prop :=
  SameLevelFeedbackFree (branchOutputs branches Φ) j

theorem sameLevelFeedbackFree_mono_subset {s t : Finset OutputObject} {j : Nat}
    (hst : s ⊆ t) (hfree : SameLevelFeedbackFree t j) :
    SameLevelFeedbackFree s j := by
  intro o ho hfeedback
  exact hfree o (hst ho) hfeedback

theorem sameLevelFeedbackFree_outputsOf {objects : Finset OutputObject}
    {kind : PackageKind} {j : Nat}
    (hfree : SameLevelFeedbackFree objects j) :
    SameLevelFeedbackFree (outputsOf objects kind) j :=
  sameLevelFeedbackFree_mono_subset (outputsOf_subset objects kind) hfree

theorem branchOutputsFeedbackFree_outputsOf {branches : Finset StoppedBranch}
    {Φ : PriorityMap} {kind : PackageKind} {j : Nat}
    (hfree : BranchOutputsFeedbackFree branches Φ j) :
    SameLevelFeedbackFree (branchOutputsOf branches Φ kind) j :=
  sameLevelFeedbackFree_outputsOf hfree

theorem feedback_output_thresholdLayer_gt {objects : Finset OutputObject}
    {j : Nat} (hfree : SameLevelFeedbackFree objects j)
    {o : OutputObject} (ho : o ∈ objects)
    (hfeedback : IsFeedbackPackage o.package) :
    j < o.thresholdLayer :=
  hfree o ho hfeedback

theorem no_same_level_feedback_output {objects : Finset OutputObject}
    {j : Nat} (hfree : SameLevelFeedbackFree objects j)
    {o : OutputObject} (ho : o ∈ objects)
    (hfeedback : IsFeedbackPackage o.package) :
    o.thresholdLayer ≠ j := by
  exact ne_of_gt (feedback_output_thresholdLayer_gt hfree ho hfeedback)

theorem feedback_outputsOf_thresholdLayer_gt {objects : Finset OutputObject}
    {kind : PackageKind} {j : Nat} (hfree : SameLevelFeedbackFree objects j)
    (hkind : IsFeedbackPackage kind) {o : OutputObject}
    (ho : o ∈ outputsOf objects kind) :
    j < o.thresholdLayer := by
  have hmem := (mem_outputsOf.1 ho).1
  have hpack := (mem_outputsOf.1 ho).2
  exact hfree o hmem (by simpa [hpack] using hkind)

theorem branchFeedback_output_thresholdLayer_gt
    {branches : Finset StoppedBranch} {Φ : PriorityMap} {j : Nat}
    (hfree : BranchOutputsFeedbackFree branches Φ j)
    {o : OutputObject} (ho : o ∈ branchOutputs branches Φ)
    (hfeedback : IsFeedbackPackage o.package) :
    j < o.thresholdLayer :=
  hfree o ho hfeedback

theorem branchFeedback_outputsOf_thresholdLayer_gt
    {branches : Finset StoppedBranch} {Φ : PriorityMap}
    {kind : PackageKind} {j : Nat}
    (hfree : BranchOutputsFeedbackFree branches Φ j)
    (hkind : IsFeedbackPackage kind) {o : OutputObject}
    (ho : o ∈ branchOutputsOf branches Φ kind) :
    j < o.thresholdLayer :=
  feedback_outputsOf_thresholdLayer_gt
    (objects := branchOutputs branches Φ) (kind := kind)
    hfree hkind ho

/--
Appendix J.6 finite ledger-closure skeleton: package costs are controlled by a
uniform charged-mass constant, and every feedback package output moves to a
higher threshold layer.
-/
theorem chargedLedgerClosure_skeleton
    {branches : Finset StoppedBranch} {Φ : PriorityMap}
    {cost weight : OutputObject -> ℝ} {Cmax : ℝ} {C : PackageKind -> ℝ}
    {j : Nat}
    (hC : ∀ kind : PackageKind, C kind <= Cmax)
    (hweight : ∀ o ∈ branchOutputs branches Φ, 0 <= weight o)
    (hpoint :
      ∀ kind o, o ∈ branchOutputsOf branches Φ kind ->
        cost o <= C kind * weight o)
    (hfree : BranchOutputsFeedbackFree branches Φ j) :
    packageCost (branchOutputs branches Φ) cost <=
        Cmax * chargedMass (branchOutputs branches Φ) weight ∧
      ∀ {kind : PackageKind} {o : OutputObject},
        IsFeedbackPackage kind ->
        o ∈ branchOutputsOf branches Φ kind ->
          j < o.thresholdLayer := by
  constructor
  · exact packageCost_branchOutputs_le_uniform_const_mul_chargedMass
      hC hweight hpoint
  · intro kind o hkind ho
    exact branchFeedback_outputsOf_thresholdLayer_gt hfree hkind ho

/-! ### Manuscript-named theorems for Appendix J.1.3–J.6.1 -/

/--
**Lemma J.1.3 (DensePack charged output estimate, manuscript form).**

DensePack branches contribute `∑ wt(b) ≤ C_Q · wt(O)` per output.  In
the ledger packaging this is the package-output cost bound for
`PackageKind.densePack` (the dense-marker kind) when the per-output
hypothesis `hpoint` holds.
-/
theorem lemmaJ1_3_densePackChargedOutput
    {objects : Finset OutputObject} {cost weight : OutputObject -> ℝ}
    {C : ℝ}
    (hpoint :
      ∀ o ∈ outputsOf objects PackageKind.densePack, cost o <= C * weight o) :
    packageCost (outputsOf objects PackageKind.densePack) cost <=
      C * chargedMass (outputsOf objects PackageKind.densePack) weight :=
  packageCost_outputsOf_le_const_mul_chargedMass hpoint

/-- **Lemma J.1.4 (Return charged output estimate, manuscript form).** -/
theorem lemmaJ1_4_returnChargedOutput
    {objects : Finset OutputObject} {cost weight : OutputObject -> ℝ}
    {C : ℝ}
    (hpoint :
      ∀ o ∈ outputsOf objects PackageKind.returnPkg, cost o <= C * weight o) :
    packageCost (outputsOf objects PackageKind.returnPkg) cost <=
      C * chargedMass (outputsOf objects PackageKind.returnPkg) weight :=
  packageCost_outputsOf_le_const_mul_chargedMass hpoint

/-- **Lemma J.1.5 (Run charged output estimate, manuscript form).** -/
theorem lemmaJ1_5_runChargedOutput
    {objects : Finset OutputObject} {cost weight : OutputObject -> ℝ}
    {C : ℝ}
    (hpoint :
      ∀ o ∈ outputsOf objects PackageKind.runPkg, cost o <= C * weight o) :
    packageCost (outputsOf objects PackageKind.runPkg) cost <=
      C * chargedMass (outputsOf objects PackageKind.runPkg) weight :=
  packageCost_outputsOf_le_const_mul_chargedMass hpoint

/-- **Lemma J.1.6 (Tower charged output estimate, manuscript form).** -/
theorem lemmaJ1_6_towerChargedOutput
    {objects : Finset OutputObject} {cost weight : OutputObject -> ℝ}
    {C : ℝ}
    (hpoint :
      ∀ o ∈ outputsOf objects PackageKind.tower, cost o <= C * weight o) :
    packageCost (outputsOf objects PackageKind.tower) cost <=
      C * chargedMass (outputsOf objects PackageKind.tower) weight :=
  packageCost_outputsOf_le_const_mul_chargedMass hpoint

/-- **Lemma J.1.7 (Progress and endpoint estimates, manuscript form).**

Combined progress and endpoint mass bound: both `progress` and
`endpoint` package kinds are summable under their per-output cost
hypothesis. -/
theorem lemmaJ1_7_progressEndpointEstimate
    {objects : Finset OutputObject} {cost weight : OutputObject -> ℝ}
    {C : ℝ}
    (hpoint_progress :
      ∀ o ∈ outputsOf objects PackageKind.progress, cost o <= C * weight o)
    (hpoint_endpoint :
      ∀ o ∈ outputsOf objects PackageKind.endpoint, cost o <= C * weight o) :
    packageCost (outputsOf objects PackageKind.progress) cost <=
        C * chargedMass (outputsOf objects PackageKind.progress) weight ∧
      packageCost (outputsOf objects PackageKind.endpoint) cost <=
        C * chargedMass (outputsOf objects PackageKind.endpoint) weight :=
  ⟨packageCost_outputsOf_le_const_mul_chargedMass hpoint_progress,
   packageCost_outputsOf_le_const_mul_chargedMass hpoint_endpoint⟩

/--
**Proposition J.6.1 (charged ledger closure, manuscript form).**

The branch-output ledger closes: package cost is bounded by `C_max ·
chargedMass`, and feedback packages always lift to a higher threshold
layer.

This is just `chargedLedgerClosure_skeleton` under its manuscript name.
-/
theorem propositionJ6_1_chargedLedgerClosure
    {branches : Finset StoppedBranch} {Φ : PriorityMap}
    {cost weight : OutputObject -> ℝ} {Cmax : ℝ} {C : PackageKind -> ℝ}
    {j : Nat}
    (hC : ∀ kind : PackageKind, C kind <= Cmax)
    (hweight : ∀ o ∈ branchOutputs branches Φ, 0 <= weight o)
    (hpoint :
      ∀ kind o, o ∈ branchOutputsOf branches Φ kind ->
        cost o <= C kind * weight o)
    (hfree : BranchOutputsFeedbackFree branches Φ j) :
    packageCost (branchOutputs branches Φ) cost <=
        Cmax * chargedMass (branchOutputs branches Φ) weight ∧
      ∀ {kind : PackageKind} {o : OutputObject},
        IsFeedbackPackage kind ->
        o ∈ branchOutputsOf branches Φ kind ->
          j < o.thresholdLayer :=
  chargedLedgerClosure_skeleton hC hweight hpoint hfree

/--
**J.6.1 corollary (feedback-free at the current layer).**

In a feedback-free charged ledger at layer `j`, no branch output that sits
*at* the current threshold layer `j` can be a feedback package: feedback
packages are forced strictly above `j`.  This is the closure invariant that
prevents same-layer feedback in the threshold descent (Appendix J.6 / I.6),
an unconditional consequence of `BranchOutputsFeedbackFree`. -/
theorem no_feedback_at_threshold_layer
    {branches : Finset StoppedBranch} {Φ : PriorityMap} {j : Nat}
    (hfree : BranchOutputsFeedbackFree branches Φ j)
    {o : OutputObject} (ho : o ∈ branchOutputs branches Φ)
    (hlayer : o.thresholdLayer = j) :
    ¬ IsFeedbackPackage o.package := by
  intro hfb
  have hgt : j < o.thresholdLayer :=
    branchFeedback_output_thresholdLayer_gt hfree ho hfb
  omega

end

end Erdos260
