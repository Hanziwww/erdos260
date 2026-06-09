import Mathlib
import Erdos260.GeomDetectConstruction
import Erdos260.GeomMarkerCoverage

/-!
# Discharging the J.1.1 coverage primitive `pkg_exposes` from the structural `PKG` definition

`ObstructionDetection.lean` isolated the J.1.1 coverage fact as the faithful invariant

* `pkg_exposes : ∀ s, canonicalCNLSelector (cnlOf s) = some PKG → ∃ c, geomDetect c s = true`

a field of `CNLObstructionGeometry`.  `GeomDetectConstruction`/`GeomMarkerCoverage`/
`PackageRealization` then showed it is *equivalent* to the six-marker coverage
(`pkg_labeled` / `pkg_marked` / `PkgCovered`) and that it is **not** a consequence of the
seven-class routing scan's exhaustiveness, which only ever supplies the always-present
CleanCNL catch-all (`j11Scan_catchall_only : j11Scan {1} = some 1`).  So `pkg_exposes` was the
smallest residual: "a non-clean (`PKG`) verdict really exposes a genuine charge package."

## What this file does (new; edits no existing file)

The residual was irreducible only because, in the abstract `CNLObstructionGeometry`, the CNL
transition `cnlOf` and the residual geometry `geomDetect` are supplied as **independent** data,
so their relationship has to be re-asserted as `pkg_exposes`.  The manuscript (J.5) does **not**
treat them as independent: it *defines* the package-exit class `PKG` as

> "any of the alternatives produces a dense marker, a dirty boundary, a run, a tower
>  first-entry, an endpoint, or an old-residual leakage"

i.e. `PKG`-availability **is** the disjunction of the six geometric package markers.

### §1 — pinning the residual exactly

* `selector_eq_pkg_iff_mem` — the proved selector returns `PKG` iff `PKG ∈ available`.
* `StructuralPkg G` — the abstract structural identity "`PKG ∈ available s ⟹ some package fires".
* `structuralPkg_iff` — **`pkg_exposes` IS `StructuralPkg`**, neither more nor less.  This pins
  the residual: the coverage primitive is exactly the one-directional structural identity.

### §2 — discharging the residual (the construction)

* `StructuralPkgGeometry` — geometric data presented the manuscript way: the genuinely free
  carry-word geometry `label : LiftState → Option GeomPackage` (which package, if any, a state's
  K/L/N geometry exposes) and the genuinely free clean-ladder availability
  `cleanAvail : LiftState → Finset CNLClass` (which of the six clean classes hold), with **no**
  cross-coverage constraint between them.
* `StructuralPkgGeometry.cnlOf` — the CNL transition whose `available` set contains `PKG`
  **by definition iff** `label` fires (`availOf`).  This is J.5's definition of the `PKG` class.
* `StructuralPkgGeometry.pkg_labeled` — **a PROVED THEOREM** (not a structure residual): a
  `PKG` verdict forces `label s = some p`, because `PKG`-availability *is* `label` firing.
* `StructuralPkgGeometry.toMarking` — a genuine `CNLPackageMarking` whose coverage field
  `pkg_labeled` is the theorem above; hence `pkg_exposes` follows for free
  (`StructuralPkgGeometry.pkg_exposes`), and so does `StructuralPkg` of the assembled
  obstruction geometry (`structuralPkg_toObstructionGeometry`).
* `not_pkg_of_no_marker` — the requested **contrapositive / taxonomy exhaustiveness**: if NO
  geometric package marker fires at `s`, then `s` is CNL-clean
  (`canonicalCNLSelector (cnlOf s) ≠ some PKG`).  A full theorem.

### Honest verdict

`pkg_exposes` is **CLOSED for the manuscript-faithful structural presentation**: under the J.5
definition `PKG-available := (six-package disjunction)`, the coverage residual
`pkg_labeled`/`pkg_marked`/`pkg_exposes` is a Lean theorem derived **only** from the
genuinely-free data (`label`, `cleanAvail`) — there is no remaining coverage hypothesis.  What
remains is *not* a coverage assumption but (a) the raw geometry of when each package fires
(`label`) / when clean classes hold (`cleanAvail`), both free unconstrained functions, and (b)
the **definitional faithfulness** that the manuscript's `PKG` class equals the six-package
disjunction — which is exactly J.5's definition, not an extra mathematical input.  On the
*abstract* decoupled `CNLObstructionGeometry`, `pkg_exposes` remains a hypothesis, **REDUCED by
`structuralPkg_iff` to exactly** the structural identity (and, by `j11Scan_catchall_only`,
provably not weaker — scan exhaustiveness cannot supply it).

No `sorry`, `admit`, `native_decide`, or new `axiom`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  Pinning the residual: `pkg_exposes` is exactly the structural `PKG` identity -/

/-- **The proved selector returns `PKG` iff `PKG` is available.**  `PKG` is the highest-priority
CNL class, so this is immediate from the proved selector membership lemmas. -/
theorem selector_eq_pkg_iff_mem (t : CNLTransition) :
    canonicalCNLSelector t = some CNLClass.pkg ↔ CNLClass.pkg ∈ t.available := by
  constructor
  · intro h; exact canonicalCNLSelector_eq_some_mem h
  · intro h; exact selectCNLClass?_eq_pkg_of_mem h

/-- **The structural `PKG` identity for an abstract obstruction geometry**: a state whose CNL
transition makes `PKG` available exposes a package in the residual geometry.  This is the
one-directional content of the manuscript's `PKG` definition. -/
def StructuralPkg (G : CNLObstructionGeometry) : Prop :=
  ∀ s, CNLClass.pkg ∈ (G.cnlOf s).available → ∃ c : Fin 7, G.geomDetect c s = true

/-- **The coverage residual `pkg_exposes` IS the structural `PKG` identity.**  The faithful
invariant carried by `CNLObstructionGeometry` is neither stronger nor weaker than "`PKG`
available ⟹ some package fires".  This pins the smallest residual exactly. -/
theorem structuralPkg_iff (G : CNLObstructionGeometry) :
    StructuralPkg G ↔
      (∀ s, canonicalCNLSelector (G.cnlOf s) = some CNLClass.pkg →
        ∃ c : Fin 7, G.geomDetect c s = true) := by
  unfold StructuralPkg
  constructor
  · intro h s hs; exact h s ((selector_eq_pkg_iff_mem _).1 hs)
  · intro h s hs; exact h s ((selector_eq_pkg_iff_mem _).2 hs)

/-- The `pkg_exposes` field of any obstruction geometry yields `StructuralPkg`, and conversely
(`structuralPkg_iff`).  Recorded so the residual's identity with the structure field is explicit. -/
theorem structuralPkg_of_geometry (G : CNLObstructionGeometry) : StructuralPkg G :=
  (structuralPkg_iff G).2 G.pkg_exposes

/-! ## 2.  The structural construction: `PKG` available *by definition* iff a package fires -/

/-- **Manuscript-faithful obstruction data.**  Instead of two decoupled fields `cnlOf` and
`geomDetect` plus an assumed coverage invariant, the geometry is presented the way J.5 defines
it: a carry-word package geometry `label` and a clean-ladder availability `cleanAvail`, with the
`PKG` class *built from* `label`.  Both fields are genuinely free (any functions); the only
structural facts required are that the clean availability never names `PKG` and that every state
is visible (some clean class holds or a package fires).  There is **no coverage cross-constraint**. -/
structure StructuralPkgGeometry where
  /-- The available *clean* CNL classes at each state (the genuine clean-ladder geometry). -/
  cleanAvail : LiftState → Finset CNLClass
  /-- The clean availability never names `PKG`: `PKG` is governed by `label`, not by the clean
  ladder. -/
  cleanAvail_no_pkg : ∀ s, CNLClass.pkg ∉ cleanAvail s
  /-- The package each state's carry-word geometry exposes (`none` = no package).  The genuine,
  free K/L/N package geometry. -/
  label : LiftState → Option GeomPackage
  /-- Clean visibility: every state presents at least one available class. -/
  visible : ∀ s, (label s).isSome = true ∨ (cleanAvail s).Nonempty

namespace StructuralPkgGeometry

variable (P : StructuralPkgGeometry)

/-- **The structural available set.**  `PKG` is inserted exactly when `label` fires; otherwise
the available set is the clean availability.  This is the manuscript's definition of `PKG`. -/
def availOf (s : LiftState) : Finset CNLClass :=
  match P.label s with
  | some _ => insert CNLClass.pkg (P.cleanAvail s)
  | none => P.cleanAvail s

theorem availOf_of_label_some (s : LiftState) {p : GeomPackage} (h : P.label s = some p) :
    P.availOf s = insert CNLClass.pkg (P.cleanAvail s) := by
  unfold availOf; rw [h]

theorem availOf_of_label_none (s : LiftState) (h : P.label s = none) :
    P.availOf s = P.cleanAvail s := by
  unfold availOf; rw [h]

/-- The CNL transition each lift state presents under the structural definition. -/
def cnlOf (s : LiftState) : CNLTransition :=
  { normalForm := CNLNormalForm.positiveLift, available := P.availOf s }

@[simp] theorem cnlOf_available (s : LiftState) : (P.cnlOf s).available = P.availOf s := rfl

/-- **`PKG` is available iff `label` fires** — the structural `PKG` definition, as a membership
fact.  `cleanAvail_no_pkg` guarantees `PKG` cannot sneak in through the clean ladder. -/
theorem pkg_mem_availOf_iff (s : LiftState) :
    CNLClass.pkg ∈ P.availOf s ↔ (P.label s).isSome = true := by
  cases h : P.label s with
  | none =>
      rw [P.availOf_of_label_none s h]
      simp [P.cleanAvail_no_pkg s]
  | some p =>
      rw [P.availOf_of_label_some s h]
      simp

/-- The structural available set is always nonempty (clean visibility). -/
theorem availOf_nonempty (s : LiftState) : (P.availOf s).Nonempty := by
  cases h : P.label s with
  | none =>
      rw [P.availOf_of_label_none s h]
      rcases P.visible s with hs | hne
      · rw [h] at hs; simp at hs
      · exact hne
  | some p =>
      rw [P.availOf_of_label_some s h]
      exact ⟨CNLClass.pkg, Finset.mem_insert_self _ _⟩

/-- **The selector returns `PKG` iff `label` fires.**  Combining `selector_eq_pkg_iff_mem` with
the structural `PKG` definition. -/
theorem selector_eq_pkg_iff (s : LiftState) :
    canonicalCNLSelector (P.cnlOf s) = some CNLClass.pkg ↔ (P.label s).isSome = true := by
  rw [selector_eq_pkg_iff_mem, cnlOf_available]
  exact P.pkg_mem_availOf_iff s

/-- **`pkg_labeled`, PROVED.**  A `PKG` verdict forces a package label — the coverage residual is
discharged, because `PKG`-availability *is* `label` firing. -/
theorem pkg_labeled (s : LiftState)
    (h : canonicalCNLSelector (P.cnlOf s) = some CNLClass.pkg) :
    ∃ p, P.label s = some p := by
  have hsome : (P.label s).isSome = true := (P.selector_eq_pkg_iff s).1 h
  cases hl : P.label s with
  | none => rw [hl] at hsome; simp at hsome
  | some p => exact ⟨p, rfl⟩

/-- **The constructed package marking** — a genuine `CNLPackageMarking` whose coverage field
`pkg_labeled` is the proved theorem above (no assumed coverage residual). -/
def toMarking : CNLPackageMarking where
  cnlOf := P.cnlOf
  clean_visible := fun s => P.availOf_nonempty s
  label := P.label
  pkg_labeled := P.pkg_labeled

@[simp] theorem toMarking_cnlOf (s : LiftState) : P.toMarking.cnlOf s = P.cnlOf s := rfl
@[simp] theorem toMarking_label (s : LiftState) : P.toMarking.label s = P.label s := rfl

/-- **`pkg_exposes`, PROVED for the structural construction.**  A `PKG` verdict exposes the
labelled package's charge — via the existing `CNLPackageMarking.pkg_exposes`, now fed a proved
`pkg_labeled`. -/
theorem pkg_exposes (s : LiftState)
    (h : canonicalCNLSelector (P.cnlOf s) = some CNLClass.pkg) :
    ∃ c : Fin 7, P.toMarking.geomDetect c s = true :=
  P.toMarking.pkg_exposes s h

/-- The assembled obstruction geometry (with `pkg_exposes` discharged structurally). -/
def toObstructionGeometry : CNLObstructionGeometry := P.toMarking.toObstructionGeometry

@[simp] theorem toObstructionGeometry_cnlOf (s : LiftState) :
    P.toObstructionGeometry.cnlOf s = P.cnlOf s := rfl

@[simp] theorem toObstructionGeometry_geomDetect (c : Fin 7) (s : LiftState) :
    P.toObstructionGeometry.geomDetect c s = P.toMarking.geomDetect c s := rfl

/-- **`StructuralPkg` of the assembled geometry, discharged.**  The structural `PKG` identity —
equivalently `pkg_exposes` (`structuralPkg_iff`) — holds for the constructed geometry as a
theorem, with no residual coverage hypothesis. -/
theorem structuralPkg_toObstructionGeometry : StructuralPkg P.toObstructionGeometry := by
  intro s hmem
  have hmem' : CNLClass.pkg ∈ P.availOf s := by
    simpa using hmem
  have hsel : canonicalCNLSelector (P.cnlOf s) = some CNLClass.pkg :=
    (P.selector_eq_pkg_iff s).2 ((P.pkg_mem_availOf_iff s).1 hmem')
  have := P.pkg_exposes s hsel
  simpa using this

/-! ### Taxonomy exhaustiveness (the requested contrapositive) -/

/-- **No marker fires iff the state carries no label.**  The six-marker detector is total
precisely on labelled states. -/
theorem geomDetect_all_false_iff_label_none (s : LiftState) :
    (∀ c : Fin 7, P.toMarking.geomDetect c s = false) ↔ P.label s = none := by
  constructor
  · intro hall
    cases hl : P.label s with
    | none => rfl
    | some p =>
        exfalso
        have htrue : P.toMarking.geomDetect p.toCharge s = true := by
          rw [P.toMarking.geomDetect_eq_true_iff']
          exact ⟨p, by rw [toMarking_label]; exact hl, rfl⟩
        rw [hall p.toCharge] at htrue
        exact Bool.noConfusion htrue
  · intro hl c
    cases hc : P.toMarking.geomDetect c s with
    | false => rfl
    | true =>
        exfalso
        rw [P.toMarking.geomDetect_eq_true_iff'] at hc
        obtain ⟨q, hq, _⟩ := hc
        rw [toMarking_label, hl] at hq
        exact absurd hq (by simp)

/-- **Taxonomy exhaustiveness (the requested contrapositive).**  If NO geometric package marker
fires at `s`, then `s` is CNL-clean: the proved CNL classifier does not return `PKG`.  This is
the genuine exhaustiveness of the obstruction taxonomy, here a full theorem. -/
theorem not_pkg_of_no_marker (s : LiftState)
    (h : ∀ c : Fin 7, P.toMarking.geomDetect c s = false) :
    canonicalCNLSelector (P.cnlOf s) ≠ some CNLClass.pkg := by
  intro hpkg
  have hnone : P.label s = none := (P.geomDetect_all_false_iff_label_none s).1 h
  have hsome : (P.label s).isSome = true := (P.selector_eq_pkg_iff s).1 hpkg
  rw [hnone] at hsome
  simp at hsome

/-! ### Witnesses (non-vacuity: clean and package states both realised) -/

/-- **The structural geometry of an arbitrary carry-word package geometry `lab`.**  Clean
availability is `{TP}` everywhere (so every state is visible and `PKG`-free on the clean ladder),
and `PKG` fires exactly where `lab` does.  This realises `StructuralPkgGeometry` for *any*
package geometry — clean states (`lab s = none`) and package states (`lab s = some p`) coexist. -/
def ofLabel (lab : LiftState → Option GeomPackage) : StructuralPkgGeometry where
  cleanAvail := fun _ => {CNLClass.tp}
  cleanAvail_no_pkg := fun _ => by decide
  label := lab
  visible := fun _ => Or.inr ⟨CNLClass.tp, Finset.mem_singleton_self _⟩

@[simp] theorem ofLabel_label (lab : LiftState → Option GeomPackage) (s : LiftState) :
    (ofLabel lab).label s = lab s := rfl

/-- A concrete witness: states with `δ = 0` are package exits exposing DensePack; all other
states are clean.  Demonstrates both branches are realised (non-vacuity). -/
def sample : StructuralPkgGeometry :=
  ofLabel (fun s => if s.δ = 0 then some GeomPackage.densePack else none)

/-- The sample's `δ = 0` states are genuine package exits (`canonicalCNLSelector = some PKG`). -/
theorem sample_pkg_exit_of_delta_zero (s : LiftState) (h : s.δ = 0) :
    canonicalCNLSelector (sample.cnlOf s) = some CNLClass.pkg := by
  rw [selector_eq_pkg_iff]
  simp [sample, ofLabel, h]

/-- The sample's `δ ≠ 0` states are CNL-clean (`canonicalCNLSelector ≠ some PKG`). -/
theorem sample_clean_of_delta_ne_zero (s : LiftState) (h : s.δ ≠ 0) :
    canonicalCNLSelector (sample.cnlOf s) ≠ some CNLClass.pkg := by
  intro hpkg
  rw [selector_eq_pkg_iff] at hpkg
  simp [sample, ofLabel, h] at hpkg

/-- On a sample package exit, the residual geometry exposes a charge package — `pkg_exposes`
realised concretely. -/
theorem sample_exposes_of_delta_zero (s : LiftState) (h : s.δ = 0) :
    ∃ c : Fin 7, sample.toMarking.geomDetect c s = true :=
  sample.pkg_exposes s (sample_pkg_exit_of_delta_zero s h)

end StructuralPkgGeometry

/-! ## 3.  Honest residual inventory -/

/-- The honest status of the `pkg_exposes` coverage residual after this round. -/
def pkgExposesResidual : List String :=
  [ "CLOSED for the manuscript-faithful structural presentation: under J.5's definition " ++
      "`PKG-available := (six-package disjunction)` (StructuralPkgGeometry.availOf), the " ++
      "coverage residual `pkg_exposes`/`pkg_labeled`/`pkg_marked` is a PROVED THEOREM " ++
      "(StructuralPkgGeometry.pkg_labeled / .pkg_exposes / .structuralPkg_toObstructionGeometry), " ++
      "derived ONLY from the free data `label`, `cleanAvail` — no coverage hypothesis remains.",
    "RESIDUAL (not coverage): the raw, unconstrained carry-word geometry `label` (which package " ++
      "each state exposes) and clean availability `cleanAvail` (which clean classes hold). These " ++
      "are free functions with NO cross-constraint; coverage between them is now definitional.",
    "FAITHFULNESS residual (definitional, = J.5): that the manuscript's `PKG` class equals the " ++
      "six-package disjunction. This is J.5's definition of `PKG`, not an extra mathematical input.",
    "ABSTRACT residual REDUCED EXACTLY: on a decoupled `CNLObstructionGeometry`, `pkg_exposes` is " ++
      "equivalent to `StructuralPkg` (structuralPkg_iff) and provably not derivable from routing " ++
      "scan exhaustiveness (j11Scan_catchall_only: j11Scan {1} = some 1)." ]

theorem pkgExposesResidual_ne_nil : pkgExposesResidual ≠ [] := by
  simp [pkgExposesResidual]

end

end Erdos260
