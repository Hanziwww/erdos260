import Mathlib
import Erdos260.ObstructionDetection

/-!
# Constructing the obstruction residual `geomDetect` from a package-marker assignment

`ObstructionDetection.lean` derived the clean-vs-package split of the J.1.1 charge
partition from the **proved** CNL transition classifier
(`canonicalCNLSelector`, `propositionK3_5_cnlTransitionClassifier`) and reduced the
remaining geometry to a single per-state primitive bundled in `CNLObstructionGeometry`:

* `geomDetect : Fin 7 → LiftState → Bool` — *which* charge package a package-exit
  state exposes (progress `0`, Tower `2`, DensePack `3`, Return `4`, Run `5`,
  old-residual `6`), supplied there as **raw data** (a structure field) together with
  two **assumed** invariants
  * `geom_not_cnl` : CleanCNL (class `1`) is never a geometric package, and
  * `pkg_exposes`  : a `PKG` verdict really exposes some charge package.

This file **constructs** that residual.  The deep K/L/N geometry of *which* package a
package-exit state exposes cannot be read off the bare lift state `(δ, q)` — the
package families (`DensePackFactoryData`, the Tower/Return/Run factories) carry their
own geometric data.  The faithful interface to that geometry is a **package-marker
assignment**

* `label : LiftState → Option GeomPackage` — the package each lift state's geometry
  exposes (`none` = clean / no obstruction).

Because `label` is a *partial function*, "a state carries **at most one** marker"
(mutual exclusivity / single-valuedness) is **structural** — it is free, not assumed.
And because the codomain `GeomPackage` has no CleanCNL constructor, `geom_not_cnl`
becomes a theorem about `toCharge` rather than a hypothesis.  The **only** residual is
the coverage half,

* `pkg_labeled` : every state the proved CNL classifier flags as a package exit
  (`canonicalCNLSelector (cnlOf s) = some PKG`) carries some marker.

This is exactly "the package markers **partition** the PKG-exit states", the smallest
irreducible K/L/N fact (its mutual-exclusivity half is now free).

From `label` + `pkg_labeled` we **prove**, with no `sorry`/`axiom`:

* a concrete `geomDetect c s := decide ((label s).map toCharge = some c)`;
* `geom_not_cnl`  (class `1` is never a package: every marker's charge `≠ 1`);
* `pkg_exposes`   (a `PKG` verdict, via `pkg_labeled`, exposes the marked package);
* `geomDetect_single_valued` (mutual exclusivity, **derived**, not assumed);
* a genuine `CNLObstructionGeometry` (`toObstructionGeometry`) whose `geomDetect` is
  concrete and whose invariants are theorems, so the J.1.1 exhaustiveness primitive
  `toRouting_cleanCNL_mem` is **discharged** for a concretely-constructed geometry,
  and the routing of a labelled package-exit is pinned exactly
  (`classify_eq_charge_of_label`).

`CNLPackageMarkers` exhibits the same data in its most literal form — six separate
Boolean per-package markers plus the coverage residual `pkg_marked` — with `label`
realised as a priority scan of the markers (`labelOf`), and `geomDetect` proved to
read them (`toMarking_geomDetect_iff`).

What remains a faithful primitive is precisely the marker coverage `pkg_labeled`
(/`pkg_marked`) and the CNL transition presentation `cnlOf`; the seven per-class mass
bounds remain the other deep input, isolated already in `CarryPriorityRoutingCharge`.
-/

namespace Erdos260

open Finset

/-! ## 1.  The six geometric package labels

The CleanCNL catch-all (class `1`) is deliberately **not** a constructor: a marker can
only ever name a genuine package, so "a marker is never CleanCNL" is structural. -/

/-- The six v5 charge packages a package-exit lift state can expose (manuscript J.5:
"any of the alternatives produces a dense marker, a dirty boundary, a run, a tower
first-entry, an endpoint, or an old-residual leakage").  CleanCNL is excluded. -/
inductive GeomPackage where
  | progress
  | tower
  | densePack
  | returnPkg
  | run
  | oldRes
deriving DecidableEq, Fintype, Repr

/-- The charge class (`Fin 7`, as in `CarryRouting`/`ObstructionDetection`) named by a
package marker: progress `0`, Tower `2`, DensePack `3`, Return `4`, Run `5`,
old-residual `6`.  Class `1` (CleanCNL) is intentionally never in the range. -/
def GeomPackage.toCharge : GeomPackage → Fin 7
  | .progress  => 0
  | .tower     => 2
  | .densePack => 3
  | .returnPkg => 4
  | .run       => 5
  | .oldRes    => 6

/-- No package marker names CleanCNL (class `1`): the structural fact behind the
faithful invariant `geom_not_cnl`. -/
theorem GeomPackage.toCharge_ne_one (p : GeomPackage) : p.toCharge ≠ 1 := by
  cases p <;> decide

/-- Distinct package markers name distinct charge classes (the markers really are six
disjoint slots of the seven-class partition). -/
theorem GeomPackage.toCharge_injective : Function.Injective GeomPackage.toCharge := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))

noncomputable section

/-! ## 2.  The package-marker assignment and the concrete `geomDetect` -/

/-- **The faithful obstruction residual: a package-marker assignment.**

* `cnlOf` / `clean_visible` : the CNL transition each lift state presents (so the
  proved classifier returns a class on it), exactly as in `CNLObstructionGeometry`.
* `label` : *which* package each lift state's K/L/N geometry exposes (`none` = clean).
  As a partial function it is structurally single-valued — a state carries at most one
  marker — so mutual exclusivity is free.
* `pkg_labeled` : the **only** residual — every classifier-flagged package exit carries
  a marker.  This is "the markers partition the PKG-exit states" (coverage half). -/
structure CNLPackageMarking where
  /-- The CNL transition each lift state presents. -/
  cnlOf : LiftState → CNLTransition
  /-- The presented transition is clean-visible, so the proved classifier returns a
  class on every state (Lemma J.5 / K.3.5). -/
  clean_visible : ∀ s, (cnlOf s).available.Nonempty
  /-- RESIDUAL PRIMITIVE — the package each lift state's geometry exposes (`none` =
  clean).  Single-valuedness is structural (it is a partial *function*). -/
  label : LiftState → Option GeomPackage
  /-- THE single residual K/L/N fact — every classifier-flagged package exit carries a
  marker.  Equivalently: the markers partition the PKG-exit states (coverage). -/
  pkg_labeled : ∀ s, canonicalCNLSelector (cnlOf s) = some CNLClass.pkg →
    ∃ p, label s = some p

namespace CNLPackageMarking

variable (M : CNLPackageMarking)

/-- The charge class named by a state's marker, if any. -/
def labelCharge (s : LiftState) : Option (Fin 7) :=
  (M.label s).map GeomPackage.toCharge

/-- **The concrete residual detector.**  `geomDetect c s = true` exactly when the
state's recorded marker names charge class `c`.  This is a genuine *definition* — no
longer an assumed structure field. -/
def geomDetect (c : Fin 7) (s : LiftState) : Bool :=
  decide (M.labelCharge s = some c)

/-- Detection unfolded against the marker charge. -/
theorem geomDetect_eq_true_iff (c : Fin 7) (s : LiftState) :
    M.geomDetect c s = true ↔ M.labelCharge s = some c := by
  unfold geomDetect
  rw [decide_eq_true_eq]

/-- Detection unfolded against the marker itself. -/
theorem geomDetect_eq_true_iff' (c : Fin 7) (s : LiftState) :
    M.geomDetect c s = true ↔ ∃ p, M.label s = some p ∧ p.toCharge = c := by
  rw [M.geomDetect_eq_true_iff]
  unfold labelCharge
  cases M.label s with
  | none => simp
  | some p =>
      constructor
      · intro h
        exact ⟨p, rfl, by simpa using h⟩
      · rintro ⟨q, hq, hqc⟩
        obtain rfl : q = p := (Option.some.inj hq).symm
        simpa using hqc

/-- A marker charge is never CleanCNL (class `1`). -/
theorem labelCharge_ne_one (s : LiftState) : M.labelCharge s ≠ some 1 := by
  unfold labelCharge
  cases M.label s with
  | none => simp
  | some p => simp [GeomPackage.toCharge_ne_one p]

/-! ### The two faithful invariants, now theorems -/

/-- **`geom_not_cnl`, proved.**  CleanCNL (class `1`) is never a geometric package —
because no marker names class `1`. -/
theorem geom_not_cnl (s : LiftState) : M.geomDetect 1 s = false := by
  cases h : M.geomDetect 1 s with
  | false => rfl
  | true =>
      rw [M.geomDetect_eq_true_iff] at h
      exact absurd h (M.labelCharge_ne_one s)

/-- **`pkg_exposes`, proved.**  When the proved classifier flags a package exit, the
residual geometry exposes the marked package — via the single residual `pkg_labeled`. -/
theorem pkg_exposes (s : LiftState)
    (h : canonicalCNLSelector (M.cnlOf s) = some CNLClass.pkg) :
    ∃ c : Fin 7, M.geomDetect c s = true := by
  obtain ⟨p, hp⟩ := M.pkg_labeled s h
  refine ⟨p.toCharge, ?_⟩
  rw [M.geomDetect_eq_true_iff]
  simp [labelCharge, hp]

/-- **Single-valuedness, derived (not assumed).**  A state exposes at most one charge
package — a structural consequence of `label` being a function, which the original
arbitrary `geomDetect : Fin 7 → LiftState → Bool` could not guarantee. -/
theorem geomDetect_single_valued {c d : Fin 7} {s : LiftState}
    (hc : M.geomDetect c s = true) (hd : M.geomDetect d s = true) : c = d := by
  rw [M.geomDetect_eq_true_iff] at hc hd
  rw [hc] at hd
  exact Option.some.inj hd

/-! ## 3.  Assembly into a concrete `CNLObstructionGeometry` -/

/-- **The concretely-constructed obstruction geometry.**  Same `cnlOf` interface as a
`CNLObstructionGeometry`, but its `geomDetect` is the concrete marker detector and both
invariants are the theorems proved above. -/
def toObstructionGeometry : CNLObstructionGeometry where
  cnlOf := M.cnlOf
  clean_visible := M.clean_visible
  geomDetect := M.geomDetect
  geom_not_cnl := M.geom_not_cnl
  pkg_exposes := M.pkg_exposes

@[simp] theorem toObstructionGeometry_cnlOf (s : LiftState) :
    M.toObstructionGeometry.cnlOf s = M.cnlOf s := rfl

@[simp] theorem toObstructionGeometry_geomDetect (c : Fin 7) (s : LiftState) :
    M.toObstructionGeometry.geomDetect c s = M.geomDetect c s := rfl

/-- **The J.1.1 exhaustiveness primitive, discharged for the constructed geometry.**
CleanCNL (class `1`) is always present — with `geomDetect` concretely defined rather
than assumed. -/
theorem toRouting_cleanCNL_mem (config : ℕ → LiftState) (k : ℕ) :
    (1 : Fin 7) ∈ (M.toObstructionGeometry.toRouting config).obstruction k :=
  M.toObstructionGeometry.toRouting_cleanCNL_mem config k

/-- **The routing of a labelled package exit is pinned exactly.**  If the proved
classifier flags a package exit and the marker names package `p`, the J.1.1
first-obstruction scan routes the start to `p`'s charge class.  (Single-valuedness of
the markers supplies the singleton hypothesis of `classify_eq_of_geom_singleton`.) -/
theorem classify_eq_charge_of_label (config : ℕ → LiftState) {k : ℕ} {p : GeomPackage}
    (hpkg : canonicalCNLSelector (M.cnlOf (config k)) = some CNLClass.pkg)
    (hlabel : M.label (config k) = some p) :
    (M.toObstructionGeometry.toRouting config).classify k = p.toCharge := by
  refine M.toObstructionGeometry.classify_eq_of_geom_singleton config hpkg ?_
  intro d hd
  have hd' : M.geomDetect d (config k) = true := hd
  rw [M.geomDetect_eq_true_iff'] at hd'
  obtain ⟨q, hq, hqc⟩ := hd'
  rw [hlabel] at hq
  obtain rfl : q = p := (Option.some.inj hq).symm
  exact hqc.symm

end CNLPackageMarking

/-! ## 4.  The literal six-marker form

The same data, presented at its true granularity: six separate Boolean per-package
markers plus the coverage residual `pkg_marked`.  `label` is recovered as a priority
scan (`labelOf`); the markers need not be mutually exclusive, the scan picks the
canonical one, and `geomDetect` is proved to read the scan. -/

/-- **Six Boolean per-package markers + coverage.**  The most literal faithful form of
the residual geometry. -/
structure CNLPackageMarkers where
  /-- The CNL transition each lift state presents. -/
  cnlOf : LiftState → CNLTransition
  /-- Clean visibility of the presented transition. -/
  clean_visible : ∀ s, (cnlOf s).available.Nonempty
  /-- Progress (`Ω`-shell-paid) marker. -/
  markProgress : LiftState → Bool
  /-- Tower first-entry marker. -/
  markTower : LiftState → Bool
  /-- DensePack (dense-marker) marker. -/
  markDensePack : LiftState → Bool
  /-- Return / endpoint / OLC-leakage marker. -/
  markReturn : LiftState → Bool
  /-- Run / variation-drop marker. -/
  markRun : LiftState → Bool
  /-- Old-residual (`Ω^oldres`) marker. -/
  markOldRes : LiftState → Bool
  /-- THE residual K/L/N fact — every classifier-flagged package exit fires at least
  one marker (coverage of the PKG-exit states by the six markers). -/
  pkg_marked : ∀ s, canonicalCNLSelector (cnlOf s) = some CNLClass.pkg →
    markProgress s = true ∨ markTower s = true ∨ markDensePack s = true ∨
      markReturn s = true ∨ markRun s = true ∨ markOldRes s = true

namespace CNLPackageMarkers

variable (D : CNLPackageMarkers)

/-- The priority scan turning six (possibly overlapping) markers into a single
canonical marker — the partial-function `label` of `CNLPackageMarking`. -/
def labelOf (s : LiftState) : Option GeomPackage :=
  if D.markProgress s = true then some GeomPackage.progress
  else if D.markTower s = true then some GeomPackage.tower
  else if D.markDensePack s = true then some GeomPackage.densePack
  else if D.markReturn s = true then some GeomPackage.returnPkg
  else if D.markRun s = true then some GeomPackage.run
  else if D.markOldRes s = true then some GeomPackage.oldRes
  else none

/-- If any marker fires, the priority scan records some package. -/
theorem labelOf_isSome_of_any (s : LiftState)
    (h : D.markProgress s = true ∨ D.markTower s = true ∨ D.markDensePack s = true ∨
      D.markReturn s = true ∨ D.markRun s = true ∨ D.markOldRes s = true) :
    ∃ p, D.labelOf s = some p := by
  unfold labelOf
  split_ifs with h0 h1 h2 h3 h4 h5
  · exact ⟨GeomPackage.progress, rfl⟩
  · exact ⟨GeomPackage.tower, rfl⟩
  · exact ⟨GeomPackage.densePack, rfl⟩
  · exact ⟨GeomPackage.returnPkg, rfl⟩
  · exact ⟨GeomPackage.run, rfl⟩
  · exact ⟨GeomPackage.oldRes, rfl⟩
  · exfalso
    rcases h with h | h | h | h | h | h
    · exact h0 h
    · exact h1 h
    · exact h2 h
    · exact h3 h
    · exact h4 h
    · exact h5 h

/-- Realise the six-marker data as a partial-function marking: the coverage residual
`pkg_labeled` follows from `pkg_marked` through the priority scan. -/
def toMarking : CNLPackageMarking where
  cnlOf := D.cnlOf
  clean_visible := D.clean_visible
  label := D.labelOf
  pkg_labeled := fun s h => D.labelOf_isSome_of_any s (D.pkg_marked s h)

@[simp] theorem toMarking_label (s : LiftState) :
    D.toMarking.label s = D.labelOf s := rfl

/-- **`geomDetect` reads the markers.**  The constructed detector fires on package
`p`'s charge exactly when the priority scan of the six markers records `p`. -/
theorem toMarking_geomDetect_iff (p : GeomPackage) (s : LiftState) :
    D.toMarking.geomDetect p.toCharge s = true ↔ D.labelOf s = some p := by
  rw [D.toMarking.geomDetect_eq_true_iff']
  constructor
  · rintro ⟨q, hq, hqc⟩
    rw [toMarking_label] at hq
    rw [hq]; congr 1; exact GeomPackage.toCharge_injective hqc
  · intro h
    exact ⟨p, by rw [toMarking_label]; exact h, rfl⟩

/-- The highest-priority marker (progress) is read unconditionally: when `markProgress`
fires, the detector reports charge `0`. -/
theorem toMarking_geomDetect_progress (s : LiftState) (h : D.markProgress s = true) :
    D.toMarking.geomDetect 0 s = true := by
  have hlabel : D.labelOf s = some GeomPackage.progress := by
    unfold labelOf; rw [if_pos h]
  have := (D.toMarking_geomDetect_iff GeomPackage.progress s).2 hlabel
  simpa using this

end CNLPackageMarkers

/-! ## 5.  An end-to-end witness

A non-degenerate marking in which every state is a package exit, all labelled
`progress`: the coverage residual is discharged outright, every invariant is a
theorem, and the routing is pinned to the progress class `0`. -/

/-- Every state presents the package-exit transition `⟨_, {PKG}⟩` and is marked
`progress`; `pkg_labeled` holds outright. -/
def allProgressMarking : CNLPackageMarking where
  cnlOf := fun _ => ⟨CNLNormalForm.positiveLift, {CNLClass.pkg}⟩
  clean_visible := fun _ => ⟨CNLClass.pkg, Finset.mem_singleton_self _⟩
  label := fun _ => some GeomPackage.progress
  pkg_labeled := fun _ _ => ⟨GeomPackage.progress, rfl⟩

/-- The witness routes every start to the progress class `0`, with `geomDetect`
concretely defined and the exhaustiveness primitive discharged. -/
theorem allProgressMarking_classify_eq_zero (config : ℕ → LiftState) (k : ℕ) :
    (allProgressMarking.toObstructionGeometry.toRouting config).classify k = 0 := by
  have hpkg : canonicalCNLSelector (allProgressMarking.cnlOf (config k))
      = some CNLClass.pkg :=
    selectCNLClass?_eq_pkg_of_mem (Finset.mem_singleton_self _)
  have := allProgressMarking.classify_eq_charge_of_label config
    (p := GeomPackage.progress) hpkg rfl
  exact this

/-- And CleanCNL stays available everywhere — the J.1.1 catch-all, discharged on a
concretely-constructed geometry. -/
theorem allProgressMarking_cleanCNL_mem (config : ℕ → LiftState) (k : ℕ) :
    (1 : Fin 7) ∈ (allProgressMarking.toObstructionGeometry.toRouting config).obstruction k :=
  allProgressMarking.toRouting_cleanCNL_mem config k

end

end Erdos260
