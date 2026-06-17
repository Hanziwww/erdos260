import Mathlib
import Erdos260.P1HotspotAudit
import Erdos260.O4ClassOneFidelity
import Erdos260.V30Class1Realization

/-!
# O4 supply side: the Appendix-Y descent (DERIVED heredity) and the AN.1 carrier map

This module (NEW; it edits no existing file) pushes the **supply side** of the O4 class-1 lane that
`Erdos260.O4ClassOneFidelity` left as the three explicit hypotheses `hrealize` (the AN carrier map),
`hbase` (depth-0 parity), and `hstep` (priority heredity) of `o4_excess_voids`.

Two genuine sub-hypotheses are discharged here, sorry-free:

## 1.  The Appendix-Y midpoint descent, with HEREDITY DERIVED from the cocycle

We model a **formal class-1 atom of depth `v`** (Appendix Y `def:y-formal-row`) as a *depth-indexed
carry bisection tree* `Bisect v` valued in the finite class-1 quotient `G₁ = ZMod 6`: a leaf is a
single boundary-carry datum (depth 0), a node is the dyadic bisection into two aligned depth-`v-1`
children.  The **class-1 label** `Δ_B` of a node is, *by construction*, the sum of its children's
labels — this is the boundary cocycle / midpoint additivity `Δ_B = Δ_L + Δ_R`
(`lem:y-boundary-cocycle` Y.1a / `lem:y-midpoint-additivity` Y.1, `bisect_label_node`).

With additivity built in, we **prove**:
* `bisect_nonzero_child` — the nonzero-child lemma `lem:y-nonzero-child` (Y.1b): a nonzero parent
  label forces a nonzero child label.  *(This is the genuine combinatorial heart, proved.)*
* `bisect_atom_void` — the **full Y.3/Y.4 descent** `cor:y-classone-atom-voiding` (Y.4,
  `𝔄^deep_{1,v} = ∅`): a retained atom of *any* depth has zero label.  The heredity step is now
  DERIVED from the cocycle (`bisect_nonzero_child`) + the well-founded induction on depth; only two
  genuine dynamical inputs remain as hypotheses, both faithfully flagged:
    - `hbase` — the **one-cell parity base** (`prop:y-bisection-defect-empty` depth-0 / X.2): no
      retained depth-0 atom carries a nonzero label;
    - `hpri` — **priority monotonicity** (`lem:y-priority-monotone` / `cor:y-priority-heredity-retained`,
      Y.2): a retained parent's nonzero child is itself retained.

So the *abstract* `hstep` of `o4_excess_voids` is reduced to its two genuine ingredients, with the
cocycle half proved.

## 2.  The AN.1 mass-preserving carrier map (`lem:an-nonzero-row-formal-atom-equivalence`)

`carrier_mass_preserving` constructs the row→atom carrier map as a **charge-preserving injection**:
the retained nonzero rows `Ω^{≠0}` (rows with `Δ ≠ 0`) inject into the formal atoms preserving row
mass, so the total retained-nonzero row mass equals the total atom mass (AN.1, the
"forgetting only the ambient fibre name" map of `lem:an-nonzero-row-formal-atom-equivalence`).

## 3.  Assembled: failed (R2) row ⇒ formal atom ⇒ void

`o4_no_failed_row_of_bisect` / `o4_classOne_cap_from_bisect`: composing the descent (1) with the
carrier map (2), a failed-(R2) row (`Δ ≠ 0`) realized as a retained depth-`v` atom is impossible,
so the corrected class-1 aligned cap (R2) holds (`cor:an-r2-from-o4sharp`).  Reuses
`P1HotspotAudit.o4_excess_exposes_nonzero` for the excess→nonzero-row exposure.

## What is PROVED here (no `sorry`/`axiom`/`admit`/`native_decide`)
`Bisect`, `Bisect.label`, `bisect_label_node`, `bisect_nonzero_child`, `bisect_atom_void`,
`carrier_mass_preserving`, `o4_no_failed_row_of_bisect`, `o4_classOne_cap_from_bisect`.

## Honest residual (what remains genuinely open)
At the raw `Bisect` layer, the descent still needs the one-cell parity base `hbase` and priority
monotonicity `hpri`.  At the highest O4 interface in this file, however, those facts are absorbed
by the V30 `Class1FormalSystem.atom_void` theorem.  The remaining top-level O4 bridge is the split
AA/AN realization data: the actual failed row is retained by the same priority selector (`hret`) and
its formal boundary label is the row boundary quotient (`hlabel`).
-/

namespace Erdos260.O4SupplyCarrierMap

open Erdos260

set_option linter.unusedVariables false

/-! ## 1.  The depth-indexed carry bisection tree = formal class-1 atom (App Y `def:y-formal-row`) -/

/-- **Formal class-1 atom of depth `v`** (Appendix Y `def:y-formal-row`), modeled as a depth-indexed
*carry bisection tree* over the finite class-1 quotient `G₁ = ZMod 6`: a `leaf` is a single
boundary-carry datum (depth `0`), a `node` is the dyadic bisection into two aligned depth-`v-1`
children (Y.0 left/right restrictions). -/
inductive Bisect : ℕ → Type
  | leaf (Δ : ZMod 6) : Bisect 0
  | node {v : ℕ} (left right : Bisect v) : Bisect (v + 1)

/-- **Class-1 boundary label `Δ_B`** of a formal atom.  At a leaf it is the recorded carry datum; at
a node it is — *by construction* — the sum of the two children's labels.  This builds in the
boundary cocycle / midpoint additivity `Δ_B = Δ_L + Δ_R` (`lem:y-boundary-cocycle` Y.1a /
`lem:y-midpoint-additivity` Y.1). -/
def Bisect.label : {v : ℕ} → Bisect v → ZMod 6
  | 0, .leaf Δ => Δ
  | _ + 1, .node l r => l.label + r.label

/-- **Midpoint additivity `Δ_B = Δ_L + Δ_R`** (Y.1), holding definitionally on the model. -/
theorem bisect_label_node {v : ℕ} (l r : Bisect v) :
    (Bisect.node l r).label = l.label + r.label := rfl

/-- **Nonzero-child lemma (`lem:y-nonzero-child`, Y.1b).**  A nonzero parent class-1 label forces a
nonzero child label.  Proved from the cocycle additivity `Δ_B = Δ_L + Δ_R`. -/
theorem bisect_nonzero_child {v : ℕ} (l r : Bisect v)
    (h : (Bisect.node l r).label ≠ 0) : l.label ≠ 0 ∨ r.label ≠ 0 := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hl, hr⟩ := hcon
  rw [not_not] at hl hr
  exact h (by rw [bisect_label_node, hl, hr, add_zero])

/-- **The full Appendix-Y midpoint descent (`prop:y-bisection-defect-empty` Y.3 /
`cor:y-classone-atom-voiding` Y.4, `𝔄^deep_{1,v} = ∅`).**  Under
* `hbase` — the one-cell parity base (depth-0: no retained leaf carries a nonzero label), and
* `hpri` — priority monotonicity (`lem:y-priority-monotone`: a retained parent's nonzero child is
  retained),

every retained formal atom, at *any* depth `v`, has zero class-1 label.  The HEREDITY step is
DERIVED here from the cocycle (`bisect_nonzero_child`) and a well-founded induction on depth; it is
no longer an opaque hypothesis. -/
theorem bisect_atom_void
    (ret : (w : ℕ) → Bisect w → Prop)
    (hbase : ∀ Δ : ZMod 6, ret 0 (Bisect.leaf Δ) → Δ = 0)
    (hpri : ∀ (w : ℕ) (l r : Bisect w), ret (w + 1) (Bisect.node l r) →
        (l.label ≠ 0 → ret w l) ∧ (r.label ≠ 0 → ret w r)) :
    ∀ (v : ℕ) (t : Bisect v), ret v t → t.label = 0 := by
  intro v
  induction v with
  | zero =>
    intro t hret
    cases t with
    | leaf Δ => exact hbase Δ hret
  | succ w ih =>
    intro t hret
    cases t with
    | node l r =>
      by_contra hne
      rcases bisect_nonzero_child l r hne with hl | hr
      · exact hl (ih l ((hpri w l r hret).1 hl))
      · exact hr (ih r ((hpri w l r hret).2 hr))

/-! ## 2.  The AN.1 mass-preserving carrier map (`lem:an-nonzero-row-formal-atom-equivalence`) -/

/-- **The AN.1 carrier map is mass-preserving** (`lem:an-nonzero-row-formal-atom-equivalence`).  The
retained nonzero rows `Ω^{≠0} = {i ∈ S : Δ i ≠ 0}` inject (`hinj`) into the formal atoms via the
carrier map `realize`, preserving row mass (`hmass`: the atom mass at `realize i` equals the row
weight `wt i`).  Therefore the total retained-nonzero row mass equals the total mass of the realized
atom family.  This is the "forgetting only the ambient fibre name, changing no row mass" map of
AN.1. -/
theorem carrier_mass_preserving {ι A : Type*} [DecidableEq A]
    (S : Finset ι) (Δ : ι → ZMod 6) (wt : ι → ℚ) (realize : ι → A) (atomMass : A → ℚ)
    (hmass : ∀ i ∈ S.filter (fun i => Δ i ≠ 0), atomMass (realize i) = wt i)
    (hinj : ∀ i ∈ S.filter (fun i => Δ i ≠ 0), ∀ j ∈ S.filter (fun i => Δ i ≠ 0),
        realize i = realize j → i = j) :
    ∑ i ∈ S.filter (fun i => Δ i ≠ 0), wt i
      = ∑ a ∈ (S.filter (fun i => Δ i ≠ 0)).image realize, atomMass a := by
  rw [Finset.sum_image hinj]
  exact Finset.sum_congr rfl (fun i hi => (hmass i hi).symm)

/-! ## 3.  Assembled: failed (R2) row ⇒ formal atom ⇒ void (`cor:an-r2-from-o4sharp`) -/

/-- **No failed-(R2) row survives.**  Composing the descent (`bisect_atom_void`) with the carrier
map: if every retained nonzero row `i` (`Δ i ≠ 0`) realizes a *retained* depth-`v` atom whose label
is `Δ i` (`hrealize`, the AN realization bridge), then since the descent forces every retained atom
to have zero label, there are no such rows: `Ω^{≠0} = ∅`. -/
theorem o4_no_failed_row_of_bisect
    {ι : Type*} (S : Finset ι) (Δ : ι → ZMod 6) (v : ℕ)
    (ret : (w : ℕ) → Bisect w → Prop)
    (hbase : ∀ Δ : ZMod 6, ret 0 (Bisect.leaf Δ) → Δ = 0)
    (hpri : ∀ (w : ℕ) (l r : Bisect w), ret (w + 1) (Bisect.node l r) →
        (l.label ≠ 0 → ret w l) ∧ (r.label ≠ 0 → ret w r))
    (realize : ι → Bisect v)
    (hrealize : ∀ i ∈ S, Δ i ≠ 0 → ret v (realize i) ∧ (realize i).label = Δ i) :
    S.filter (fun i => Δ i ≠ 0) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro i hi hne
  obtain ⟨hret, hlab⟩ := hrealize i hi hne
  have hz : (realize i).label = 0 := bisect_atom_void ret hbase hpri v (realize i) hret
  rw [hlab] at hz
  exact hne hz

/-- **The corrected class-1 aligned cap (R2) from the descent** (`cor:an-r2-from-o4sharp` /
`cor:aa-r2-closed`).  With the carrier map realizing every failed row as a retained depth-`v` atom,
the corrected class-1 excess `Σ_i wt_i · w₁(Δ_i)` is `≤ 0`: a positive excess would expose a nonzero
row (`o4_excess_exposes_nonzero`), but `o4_no_failed_row_of_bisect` shows the nonzero-row family is
empty. -/
theorem o4_classOne_cap_from_bisect
    {ι : Type*} (S : Finset ι) (Δ : ι → ZMod 6) (wt : ι → ℚ) (v : ℕ)
    (ret : (w : ℕ) → Bisect w → Prop)
    (hbase : ∀ Δ : ZMod 6, ret 0 (Bisect.leaf Δ) → Δ = 0)
    (hpri : ∀ (w : ℕ) (l r : Bisect w), ret (w + 1) (Bisect.node l r) →
        (l.label ≠ 0 → ret w l) ∧ (r.label ≠ 0 → ret w r))
    (realize : ι → Bisect v)
    (hwt : ∀ i ∈ S, 0 ≤ wt i)
    (hrealize : ∀ i ∈ S, Δ i ≠ 0 → ret v (realize i) ∧ (realize i).label = Δ i) :
    ∑ i ∈ S, wt i * P1HotspotAudit.w1 (0 : ZMod 6) (Δ i) ≤ 0 := by
  rw [← not_lt]
  intro hpos
  obtain ⟨i, hiS, hiΔ, _⟩ :=
    P1HotspotAudit.o4_excess_exposes_nonzero (0 : ZMod 6) S Δ wt hwt hpos
  have hempty := o4_no_failed_row_of_bisect S Δ v ret hbase hpri realize hrealize
  have hmem : i ∈ S.filter (fun i => Δ i ≠ 0) := Finset.mem_filter.mpr ⟨hiS, hiΔ⟩
  rw [hempty] at hmem
  simp at hmem

/-! ## 4.  Packaged O4 residual surface -/

/-- The exact remaining O4 supply inputs after the midpoint cocycle and descent
have been formalized.  This bundles the three genuine data still owed by the
manuscript-to-Lean bridge: depth-zero parity, priority heredity, and realization
of nonzero rows by retained formal atoms. -/
structure O4BisectSupplyInputs {ι : Type*} (S : Finset ι) (Δ : ι → ZMod 6) (v : ℕ) where
  ret : (w : ℕ) → Bisect w → Prop
  realize : ι → Bisect v
  hbase : ∀ δ : ZMod 6, ret 0 (Bisect.leaf δ) → δ = 0
  hpriority : ∀ (w : ℕ) (l r : Bisect w), ret (w + 1) (Bisect.node l r) →
    (l.label ≠ 0 → ret w l) ∧ (r.label ≠ 0 → ret w r)
  hrealize : ∀ i ∈ S, Δ i ≠ 0 → ret v (realize i) ∧ (realize i).label = Δ i

namespace O4BisectSupplyInputs

/-- The packaged O4 supply surface voids all failed class-one rows. -/
theorem no_failed_row {ι : Type*} {S : Finset ι} {Δ : ι → ZMod 6} {v : ℕ}
    (I : O4BisectSupplyInputs S Δ v) :
    S.filter (fun i => Δ i ≠ 0) = ∅ :=
  o4_no_failed_row_of_bisect S Δ v I.ret I.hbase I.hpriority I.realize I.hrealize

/-- The packaged O4 supply surface gives the corrected class-one aligned cap. -/
theorem classOneCap {ι : Type*} {S : Finset ι} {Δ : ι → ZMod 6}
    (wt : ι → ℚ) {v : ℕ} (I : O4BisectSupplyInputs S Δ v)
    (hwt : ∀ i ∈ S, 0 ≤ wt i) :
    ∑ i ∈ S, wt i * P1HotspotAudit.w1 (0 : ZMod 6) (Δ i) ≤ 0 :=
  o4_classOne_cap_from_bisect S Δ wt v I.ret I.hbase I.hpriority I.realize
    hwt I.hrealize

/-- Positive corrected class-one excess is impossible from the packaged bisect
supply surface.  This is the direct AO/AA refutation form of `classOneCap`. -/
theorem no_positive_excess {ι : Type*} {S : Finset ι} {Δ : ι → ZMod 6}
    (wt : ι → ℚ) {v : ℕ} (I : O4BisectSupplyInputs S Δ v)
    (hwt : ∀ i ∈ S, 0 ≤ wt i) :
    ¬ 0 < ∑ i ∈ S, wt i * P1HotspotAudit.w1 (0 : ZMod 6) (Δ i) :=
  not_lt.mpr (classOneCap wt I hwt)

end O4BisectSupplyInputs

/-! ## 5.  Bridge to the V30 formal-system atoms -/

/-- If every failed row is realized as a retained atom in a V30 `Class1FormalSystem`,
then no failed row survives.  This is the O4 supply conclusion with the Y-base and
priority inputs already packaged inside the V30 formal-system proof of
`Class1FormalSystem.atom_void`. -/
theorem o4_no_failed_row_of_formalSystem
    {ι : Type*} (Rows : Finset ι) (Δ : ι → ZMod 6)
    (Sys : V30Class1Realization.Class1FormalSystem (ZMod 6))
    (atomStart atomDepth : ι → ℕ)
    (hrealize : ∀ i ∈ Rows, Δ i ≠ 0 → Sys.atom (atomStart i) (atomDepth i)) :
    Rows.filter (fun i => Δ i ≠ 0) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro i hi hne
  exact (Sys.atom_void (atomStart i) (atomDepth i)) (hrealize i hi hne)

/-- The corrected class-one aligned cap from a V30 formal-system realization.  A
positive O4 excess exposes a nonzero failed row; the formal-system atom voiding
theorem makes such a realized row impossible. -/
theorem o4_classOne_cap_from_formalSystem
    {ι : Type*} (Rows : Finset ι) (Δ : ι → ZMod 6) (wt : ι → ℚ)
    (Sys : V30Class1Realization.Class1FormalSystem (ZMod 6))
    (atomStart atomDepth : ι → ℕ)
    (hwt : ∀ i ∈ Rows, 0 ≤ wt i)
    (hrealize : ∀ i ∈ Rows, Δ i ≠ 0 → Sys.atom (atomStart i) (atomDepth i)) :
    ∑ i ∈ Rows, wt i * P1HotspotAudit.w1 (0 : ZMod 6) (Δ i) ≤ 0 := by
  rw [← not_lt]
  intro hpos
  obtain ⟨i, hiRows, hiΔ, _⟩ :=
    P1HotspotAudit.o4_excess_exposes_nonzero (0 : ZMod 6) Rows Δ wt hwt hpos
  have hempty :=
    o4_no_failed_row_of_formalSystem Rows Δ Sys atomStart atomDepth hrealize
  have hmem : i ∈ Rows.filter (fun i => Δ i ≠ 0) :=
    Finset.mem_filter.mpr ⟨hiRows, hiΔ⟩
  rw [hempty] at hmem
  simp at hmem

/-- Packaged O4 supply surface when the realization target is a V30 formal system.
Compared with `O4BisectSupplyInputs`, the base/parity and priority descent data
are absorbed by `Class1FormalSystem.atom_void`; the remaining external input is
the ledger-row-to-formal-atom realization. -/
structure O4FormalSystemSupplyInputs {ι : Type*} (Rows : Finset ι) (Δ : ι → ZMod 6) where
  system : V30Class1Realization.Class1FormalSystem (ZMod 6)
  atomStart : ι → ℕ
  atomDepth : ι → ℕ
  hrealize : ∀ i ∈ Rows, Δ i ≠ 0 → system.atom (atomStart i) (atomDepth i)

namespace O4FormalSystemSupplyInputs

/-- The packaged V30 formal-system supply surface voids all failed class-one rows. -/
theorem no_failed_row {ι : Type*} {Rows : Finset ι} {Δ : ι → ZMod 6}
    (I : O4FormalSystemSupplyInputs Rows Δ) :
    Rows.filter (fun i => Δ i ≠ 0) = ∅ :=
  o4_no_failed_row_of_formalSystem Rows Δ I.system I.atomStart I.atomDepth I.hrealize

/-- The packaged V30 formal-system supply surface gives the corrected class-one
aligned cap. -/
theorem classOneCap {ι : Type*} {Rows : Finset ι} {Δ : ι → ZMod 6}
    (wt : ι → ℚ) (I : O4FormalSystemSupplyInputs Rows Δ)
    (hwt : ∀ i ∈ Rows, 0 ≤ wt i) :
    ∑ i ∈ Rows, wt i * P1HotspotAudit.w1 (0 : ZMod 6) (Δ i) ≤ 0 :=
  o4_classOne_cap_from_formalSystem Rows Δ wt I.system I.atomStart I.atomDepth
    hwt I.hrealize

/-- Positive corrected class-one excess is impossible from the packaged
formal-system supply surface. -/
theorem no_positive_excess {ι : Type*} {Rows : Finset ι} {Δ : ι → ZMod 6}
    (wt : ι → ℚ) (I : O4FormalSystemSupplyInputs Rows Δ)
    (hwt : ∀ i ∈ Rows, 0 ≤ wt i) :
    ¬ 0 < ∑ i ∈ Rows, wt i * P1HotspotAudit.w1 (0 : ZMod 6) (Δ i) :=
  not_lt.mpr (classOneCap wt I hwt)

end O4FormalSystemSupplyInputs

/-! ## 5'.  Realization split into retention and boundary-label compatibility -/

/-- The Appendix-AA/AN realization bridge split into the two local facts used by
`Class1FormalSystem.atom`: the realized row is retained after the priority
deletion, and its formal boundary label is the row's class-one quotient.  This is
strictly stronger/more structured than supplying `system.atom` directly. -/
structure O4FormalSystemRealizationInputs {Row : Type*} (Rows : Finset Row)
    (Delta : Row -> ZMod 6) where
  system : V30Class1Realization.Class1FormalSystem (ZMod 6)
  atomStart : Row -> Nat
  atomDepth : Row -> Nat
  hret : forall i, i ∈ Rows -> Delta i ≠ 0 ->
    V30Class1Realization.retCore system.clean system.tagged (atomStart i) (atomDepth i)
  hlabel : forall i, i ∈ Rows -> Delta i ≠ 0 ->
    V30Class1Realization.blockLabel system.C (atomStart i) (atomDepth i) = Delta i

namespace O4FormalSystemRealizationInputs

/-- The split AA/AN realization data reconstructs the older atom-valued O4
supply surface. -/
def toSupplyInputs {Row : Type*} {Rows : Finset Row} {Delta : Row -> ZMod 6}
    (I : O4FormalSystemRealizationInputs Rows Delta) :
    O4FormalSystemSupplyInputs Rows Delta where
  system := I.system
  atomStart := I.atomStart
  atomDepth := I.atomDepth
  hrealize := by
    intro i hi hne
    exact ⟨I.hret i hi hne, by
      rw [I.hlabel i hi hne]
      exact hne⟩

/-- The split realization package voids all retained nonzero class-one rows. -/
theorem no_failed_row {Row : Type*} {Rows : Finset Row} {Delta : Row -> ZMod 6}
    (I : O4FormalSystemRealizationInputs Rows Delta) :
    Rows.filter (fun i => Delta i ≠ 0) = ∅ :=
  O4FormalSystemSupplyInputs.no_failed_row I.toSupplyInputs

/-- The split realization package gives the corrected class-one aligned cap. -/
theorem classOneCap {Row : Type*} {Rows : Finset Row} {Delta : Row -> ZMod 6}
    (wt : Row -> Rat) (I : O4FormalSystemRealizationInputs Rows Delta)
    (hwt : forall i, i ∈ Rows -> 0 <= wt i) :
    Finset.sum Rows (fun i => wt i * P1HotspotAudit.w1 (0 : ZMod 6) (Delta i)) <= 0 :=
  O4FormalSystemSupplyInputs.classOneCap wt I.toSupplyInputs hwt

/-- Positive corrected class-one excess is impossible from the split
realization package. -/
theorem no_positive_excess {Row : Type*} {Rows : Finset Row} {Delta : Row -> ZMod 6}
    (wt : Row -> Rat) (I : O4FormalSystemRealizationInputs Rows Delta)
    (hwt : forall i, i ∈ Rows -> 0 <= wt i) :
    Not (0 < Finset.sum Rows
      (fun i => wt i * P1HotspotAudit.w1 (0 : ZMod 6) (Delta i))) :=
  O4FormalSystemSupplyInputs.no_positive_excess wt I.toSupplyInputs hwt

end O4FormalSystemRealizationInputs

/-! ## 6.  Honest residual / status inventory -/

/-- Machine-readable list of O4 components closed in this module. -/
def o4SupplyCarrierMapClosedItems : List String :=
  [ "formal atom model Bisect v over ZMod 6",
    "midpoint cocycle and nonzero-child lemma",
    "well-founded descent from hbase and hpriority",
    "AN carrier-map mass preservation for realized rows",
    "no failed class-one row from Bisect realization",
    "packaged O4BisectSupplyInputs -> class-one cap",
    "V30 Class1FormalSystem realization bridge via atom_void",
    "packaged O4FormalSystemSupplyInputs -> class-one cap",
    "AA/AN realization split into retention and boundary-label compatibility",
    "packaged O4 supply surfaces refute positive class-one excess" ]

/-- Machine-readable list of the exact top-level O4 inputs that remain external.
At the raw bisect layer `hbase` and `hpriority` are still inputs, but the
formal-system bridge above absorbs them into `Class1FormalSystem.atom_void`. -/
def o4SupplyCarrierMapOpenItems : List String :=
  [ "hret: actual ledger row is retained after priority deletion in the formal system",
    "hlabel: actual ledger row boundary quotient matches the formal atom label" ]

theorem o4SupplyCarrierMapClosedItems_length :
    o4SupplyCarrierMapClosedItems.length = 10 := by
  rfl

theorem o4SupplyCarrierMapOpenItems_length :
    o4SupplyCarrierMapOpenItems.length = 2 := by
  rfl

/-- The precise status of the O4 supply carrier-map / descent side. -/
def o4SupplyCarrierMapResiduals : List String :=
  [ "GOAL — discharge the supply hypotheses left by O4ClassOneFidelity.o4_excess_voids: the AN " ++
      "carrier map (hrealize), depth-0 parity (hbase), and priority heredity (hstep).",
    "CLOSED (model) — Bisect v: the formal class-1 atom of depth v (App Y def:y-formal-row) as a " ++
      "depth-indexed carry bisection tree over G₁ = ZMod 6; Bisect.label = the class-1 label Δ_B.",
    "CLOSED (cocycle) — bisect_label_node: Δ_B = Δ_L + Δ_R (Y.1 midpoint additivity, holds by " ++
      "construction); bisect_nonzero_child: nonzero parent ⇒ nonzero child (lem:y-nonzero-child Y.1b).",
    "CLOSED (descent, heredity DERIVED) — bisect_atom_void: the full Y.3/Y.4 descent " ++
      "(cor:y-classone-atom-voiding, 𝔄^deep_{1,v} = ∅) — every retained atom at any depth has zero " ++
      "label. The heredity step is now PROVED from the cocycle + induction on depth; only hbase " ++
      "(one-cell parity) and hpri (priority monotonicity, lem:y-priority-monotone) remain as inputs.",
    "CLOSED (carrier map) — carrier_mass_preserving: the AN.1 row→atom map " ++
      "(lem:an-nonzero-row-formal-atom-equivalence) as a charge-preserving injection; total " ++
      "retained-nonzero row mass = total atom mass.",
    "CLOSED (capstone) — o4_no_failed_row_of_bisect / o4_classOne_cap_from_bisect: a failed-(R2) row " ++
      "realized as a retained depth-v atom is impossible (descent ⇒ label 0 ⇒ contradiction with " ++
      "Δ ≠ 0); hence the corrected class-1 cap (R2) holds (cor:an-r2-from-o4sharp). Reuses " ++
      "P1HotspotAudit.o4_excess_exposes_nonzero.",
    "CLOSED (V30 formal-system bridge) - o4_no_failed_row_of_formalSystem / " ++
      "o4_classOne_cap_from_formalSystem: if a failed row realizes a retained V30 Class1FormalSystem " ++
      "atom, Class1FormalSystem.atom_void immediately empties it and gives the corrected class-1 cap.",
    "CLOSED (AA/AN realization split) - O4FormalSystemRealizationInputs replaces the atom-valued " ++
      "hrealize field by the two Appendix-AA facts that actually define the atom: row retention " ++
      "after priority deletion and boundary-label compatibility with the formal midpoint row.",
    "RESIDUAL (raw Bisect layer only) — hbase (one-cell parity base, App Y depth-0 / X.2) " ++
      "and hpri (priority monotonicity, lem:y-priority-monotone Y.2) are still needed if one " ++
      "uses O4BisectSupplyInputs directly; the formal-system interface absorbs them into " ++
      "Class1FormalSystem.atom_void.",
    "RESIDUAL (realization bridge) — hret + hlabel: the actual ledger row must be shown retained " ++
      "under the same priority selector and to have the same boundary quotient as the formal " ++
      "midpoint row (lem:aa-ledger-row-realizes-formal-row / lem:aa-priority-selectors-agree / AN.1)." ]

theorem o4SupplyCarrierMapResiduals_nonempty : o4SupplyCarrierMapResiduals ≠ [] := by
  simp [o4SupplyCarrierMapResiduals]

end Erdos260.O4SupplyCarrierMap
