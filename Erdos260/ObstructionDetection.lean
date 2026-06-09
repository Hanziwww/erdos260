import Mathlib
import Erdos260.ObstructionProfile
import Erdos260.AppendixG_CNLClassifier
import Erdos260.CNL
import Erdos260.LiftState

/-!
# Obstruction detection: the CNL classifier gate over the residual geometry

`ObstructionProfile.lean` reduced the J.1.1 exhaustiveness of the v5 charge
partition to a single residual primitive: the **per-state detection geometry**
`stateDetect` / `detects : Fin 7 → LiftState → Bool` — *which lift configurations
expose which package-class obstruction* — and proved everything above it
(`ofDetect`, `ofStateProfile`, the catch-all law, the exact CleanCNL
characterisation).  It supplied that detection geometry as raw data.

This file **advances** that residual primitive by splitting it into two honestly
different pieces and deriving the larger piece from already-proved structure:

* the **proved CNL transition classifier** `canonicalCNLSelector`
  (`CNL.lean`, `propositionK3_5_cnlTransitionClassifier`) decides, single-valuedly,
  whether a lift state's CNL transition is one of the six *clean* ladder classes
  `BND, SEP, TC, VS, DS, TP` (manuscript J.5) or the *package-exit* class `PKG`.
  Whether a state exposes **any** charge-package obstruction at all — equivalently
  whether the J.1.1 scan routes it to the deliberately-last **CleanCNL** class — is
  therefore **derived** from the proved classifier (the `PKG` gate);

* the **residual per-state geometry** `geomDetect : Fin 7 → LiftState → Bool`:
  *which* charge package (DensePack `3`, Tower `2`, Return `4`, Run `5`,
  progress `0`, old-residual `6`) a package-exit state exposes.  This is the
  genuinely dynamical K/L/N input that the CNL classifier does **not** decide; it
  is the smallest faithful primitive that remains.

## The charge classes (`Fin 7`, as in `CarryRouting.lean`)

```
0  Chernoff / shell-paid progress   3  DensePack          6  old-residual (Ω^oldres)
1  CleanCNL Kraft tail              4  Return / endpoint / OLC leakage
2  Tower                            5  Run / variation-drop
```

## What is genuinely derived from the proved classifier (no `sorry`/`axiom`)

* `detects c s` is **defined** as the proved-classifier `PKG` gate composed with
  the residual geometry, so the detector literally *reuses* the proved classifier.
* `detects_all_false_iff` / `classify_eq_one_iff`: a start is routed to CleanCNL
  **iff** the proved CNL classifier certifies its state clean
  (`canonicalCNLSelector ≠ some PKG`).  The deliberately-last CleanCNL class is
  thus decided entirely by the proved classifier.
* `classify_mem_detect`: a start routed to a *charge package* was certified `PKG`
  by the classifier **and** exposed that package in the residual geometry.
* `classify_eq_of_geom_singleton`: when the residual geometry exposes a single
  package the J.1.1 first-obstruction scan routes there (single-valuedness reused).
* `classify_eq_one_of_tc_available` / `..._tp_available` reuse the proved selector
  iff lemmas (`selected_eq_tc_iff`, `selected_eq_tp_iff`); `suffix_dichotomy_ne_pkg`
  reuses `suffix_dichotomy_class`: the VS/DS suffix classes are clean, hence route
  to CleanCNL.
* `cnlClass_existsUnique`: the proved `propositionK3_5_cnlTransitionClassifier`
  gives the single-valued CNL class of each lift state.
* The assembled `PackageDetector` feeds `ObstructionProfile`'s `toGeometry.toRouting`
  (built on `CarryPriorityRouting.ofDetect`) and is exhibited as the per-state
  reduction `CarryPriorityRouting.ofStateProfile`, discharging the J.1.1
  exhaustiveness primitive `cleanCNL_mem` as a theorem.

## What remains the irreducible faithful primitive

`geomDetect : Fin 7 → LiftState → Bool` (which charge package a package-exit state
exposes), the lift-state → CNL-transition presentation `cnlOf`, and the faithful
invariant `pkg_exposes` (a `PKG` verdict really exposes some package).  The CNL
classifier decides **clean vs package**; the residual geometry decides **which
package**.  (The seven per-class mass bounds remain the separate deep input,
already isolated in `CarryPriorityRoutingCharge`.)
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The obstruction-detection geometry built on the CNL classifier -/

/-- **Obstruction-detection geometry: proved CNL classifier gate + residual geometry.**

The detector of *which lift configuration exposes which charge-package obstruction*
is decomposed into a derived piece and a residual piece:

* `cnlOf` / `clean_visible`: each lift state presents a clean-visible CNL transition,
  on which the **proved** single-valued classifier `canonicalCNLSelector` returns a
  class.  Whether that class is the package-exit class `PKG` is the **derived**
  clean/package gate.
* `geomDetect` / `geom_not_cnl` / `pkg_exposes`: the **residual** per-state geometry
  fixing *which* charge package a package-exit state exposes (`geom_not_cnl`:
  CleanCNL, class `1`, is never a geometric package; `pkg_exposes`: a `PKG` verdict
  really does expose at least one charge package — manuscript J.5, "any of the above
  alternatives produces a [package]"). -/
structure CNLObstructionGeometry where
  /-- RESIDUAL PRIMITIVE — the CNL transition each lift state presents (the
  manuscript's transition exposed along the last-`m` path `π`). -/
  cnlOf : LiftState → CNLTransition
  /-- The presented transition is clean-visible (nonempty available set), so the
  proved classifier returns a class on every state (Lemma J.5 / K.3.5). -/
  clean_visible : ∀ s, (cnlOf s).available.Nonempty
  /-- RESIDUAL GEOMETRIC PRIMITIVE — which v5 charge package a state exposes once
  the classifier has flagged a package exit.  This is the genuinely dynamical
  K/L/N geometry the CNL classifier does not decide. -/
  geomDetect : Fin 7 → LiftState → Bool
  /-- FAITHFUL invariant — CleanCNL (class `1`) is never itself a geometric
  package: it is the catch-all of fibres on which no obstruction occurs. -/
  geom_not_cnl : ∀ s, geomDetect 1 s = false
  /-- FAITHFUL invariant (manuscript J.5 `PKG` = "any alternative produces a dense
  marker, dirty boundary, run, tower first-entry, or endpoint leakage"): when the
  proved classifier flags a package exit, the residual geometry exposes at least one
  concrete charge package. -/
  pkg_exposes : ∀ s, canonicalCNLSelector (cnlOf s) = some CNLClass.pkg →
    ∃ c : Fin 7, geomDetect c s = true

namespace CNLObstructionGeometry

variable (G : CNLObstructionGeometry)

/-! ### The derived clean/package gate (proved classifier) -/

/-- A lift state is **CNL-clean** when the proved CNL classifier assigns its
transition one of the six clean ladder classes `BND, SEP, TC, VS, DS, TP`, i.e.
*not* the package-exit class `PKG`. -/
def IsCNLClean (s : LiftState) : Prop :=
  canonicalCNLSelector (G.cnlOf s) ≠ some CNLClass.pkg

/-- A lift state is a **CNL package exit** when the proved classifier assigns its
transition the package-exit class `PKG`. -/
def IsCNLPackageExit (s : LiftState) : Prop :=
  canonicalCNLSelector (G.cnlOf s) = some CNLClass.pkg

instance (s : LiftState) : Decidable (G.IsCNLClean s) := by
  unfold IsCNLClean; infer_instance

instance (s : LiftState) : Decidable (G.IsCNLPackageExit s) := by
  unfold IsCNLPackageExit; infer_instance

/-- **Package-exit verdict ⇔ `PKG` available.**  Because `PKG` is the
highest-priority CNL class, the classifier returns `PKG` exactly when `PKG` is
available — a direct consequence of the proved selector lemmas. -/
theorem isCNLPackageExit_iff (s : LiftState) :
    G.IsCNLPackageExit s ↔ CNLClass.pkg ∈ (G.cnlOf s).available := by
  constructor
  · intro h; exact canonicalCNLSelector_eq_some_mem h
  · intro h; exact selectCNLClass?_eq_pkg_of_mem h

/-! ### Detection (derived gate ∘ residual geometry) -/

/-- **Per-class package detection.**  `detects c s = true` iff the proved CNL
classifier flags the state as a package exit (`canonicalCNLSelector = some PKG`)
**and** the residual geometry exposes charge class `c`.  This literally reuses the
proved classifier as the clean/package gate. -/
def detects (c : Fin 7) (s : LiftState) : Bool :=
  if canonicalCNLSelector (G.cnlOf s) = some CNLClass.pkg then G.geomDetect c s
  else false

/-- CleanCNL (class `1`) is never detected: the gate cannot promote class `1`
because the residual geometry never exposes it. -/
theorem detects_one (s : LiftState) : G.detects 1 s = false := by
  unfold detects
  by_cases h : canonicalCNLSelector (G.cnlOf s) = some CNLClass.pkg
  · rw [if_pos h]; exact G.geom_not_cnl s
  · rw [if_neg h]

/-- **Detection unfolded.**  A class is detected iff the state is a package exit
*and* the residual geometry exposes it. -/
theorem detects_eq_true_iff (c : Fin 7) (s : LiftState) :
    G.detects c s = true ↔ G.IsCNLPackageExit s ∧ G.geomDetect c s = true := by
  unfold detects IsCNLPackageExit
  by_cases h : canonicalCNLSelector (G.cnlOf s) = some CNLClass.pkg
  · simp [h]
  · simp [h]

/-- **The CleanCNL detection law is decided by the proved classifier.**  *No*
charge package is detected at a state iff the proved CNL classifier certifies it
clean.  The forward use of `pkg_exposes` turns "the classifier says `PKG`" into a
genuinely exposed package. -/
theorem detects_all_false_iff (s : LiftState) :
    (∀ c : Fin 7, G.detects c s = false) ↔ G.IsCNLClean s := by
  constructor
  · intro hall hpkg
    obtain ⟨c, hc⟩ := G.pkg_exposes s hpkg
    have hct : G.detects c s = true := (G.detects_eq_true_iff c s).2 ⟨hpkg, hc⟩
    rw [hall c] at hct
    exact Bool.noConfusion hct
  · intro hclean c
    unfold detects
    rw [if_neg hclean]

/-! ## 2.  Assembly into the `ObstructionProfile` machinery -/

/-- Package the CNL-gated detector as an `ObstructionProfile.PackageDetector`
(`detects : Fin 7 → LiftState → Bool` with the never-CleanCNL invariant). -/
def toPackageDetector : PackageDetector where
  detects := G.detects
  not_detects_cnl := fun s => G.detects_one s

@[simp] theorem toPackageDetector_detects (c : Fin 7) (s : LiftState) :
    G.toPackageDetector.detects c s = G.detects c s := rfl

/-- **The J.1.1 routing of a lift-configuration sequence.**  Built through
`ObstructionProfile`'s `LiftObstructionGeometry.toRouting`, which is the catch-all
`CarryPriorityRouting.ofDetect` construction — so the J.1.1 exhaustiveness
primitive `cleanCNL_mem` is discharged for free. -/
def toRouting (config : ℕ → LiftState) : CarryPriorityRouting :=
  G.toPackageDetector.toGeometry.toRouting config

theorem toRouting_eq_geomRouting (config : ℕ → LiftState) :
    G.toRouting config = G.toPackageDetector.toGeometry.toRouting config := rfl

/-- **The J.1.1 exhaustiveness primitive, discharged.**  CleanCNL (class `1`) is
always present in the constructed obstruction profile. -/
theorem toRouting_cleanCNL_mem (config : ℕ → LiftState) (k : ℕ) :
    (1 : Fin 7) ∈ (G.toRouting config).obstruction k :=
  (G.toRouting config).cleanCNL_mem k

/-- The routing is exactly `ObstructionProfile`'s per-state reduction
`ofStateProfile`: the per-state catch-all profile `insert 1 (stateDetect s)` with
the per-state exhaustiveness fact `Finset.mem_insert_self`.  This is the genuine
reduction of global exhaustiveness to per-state classification. -/
theorem toRouting_eq_ofStateProfile (config : ℕ → LiftState) :
    G.toRouting config =
      CarryPriorityRouting.ofStateProfile
        (fun s => insert 1 (G.toPackageDetector.toGeometry.stateDetect s)) config
        (fun s => Finset.mem_insert_self 1 (G.toPackageDetector.toGeometry.stateDetect s)) :=
  LiftObstructionGeometry.toRouting_eq_ofStateProfile _ config

/-! ## 3.  The headline derived facts -/

/-- **CleanCNL is decided by the proved CNL classifier.**  A start is routed to
the deliberately-last CleanCNL class **iff** the proved CNL transition classifier
certifies its lift state clean (returns one of `BND, SEP, TC, VS, DS, TP`, not
`PKG`).  This is the J.1.1 catch-all law with its hypothesis *derived* from the
proved classifier rather than supplied as data. -/
theorem classify_eq_one_iff (config : ℕ → LiftState) (k : ℕ) :
    (G.toRouting config).classify k = 1 ↔ G.IsCNLClean (config k) := by
  rw [toRouting_eq_geomRouting, PackageDetector.toGeometry_classify_eq_one_iff]
  exact G.detects_all_false_iff (config k)

/-- **Clean ⟹ CleanCNL.**  If the proved classifier returns any clean class
(`cls ≠ PKG`) the start is routed to CleanCNL. -/
theorem classify_eq_one_of_clean (config : ℕ → LiftState) {k : ℕ} {cls : CNLClass}
    (hcls : cls ≠ CNLClass.pkg)
    (hsel : canonicalCNLSelector (G.cnlOf (config k)) = some cls) :
    (G.toRouting config).classify k = 1 := by
  rw [classify_eq_one_iff]
  intro hcontra
  exact hcls (Option.some.inj (hsel.symm.trans hcontra))

/-- **Routed to a package ⟹ certified `PKG` and genuinely exposed.**  If a start is
routed to a non-CleanCNL charge class, the proved classifier certified its state a
package exit **and** the residual geometry exposes exactly that charge class.  The
classifier never invents geometry, and the geometry never fires without the
classifier's `PKG` verdict. -/
theorem classify_mem_detect (config : ℕ → LiftState) {k : ℕ}
    (h : (G.toRouting config).classify k ≠ 1) :
    G.IsCNLPackageExit (config k) ∧
      G.geomDetect ((G.toRouting config).classify k) (config k) = true := by
  rw [toRouting_eq_geomRouting] at h ⊢
  have hmem := LiftObstructionGeometry.toRouting_classify_mem_detect_of_ne_one
    G.toPackageDetector.toGeometry config h
  rw [PackageDetector.toGeometry_stateDetect, PackageDetector.mem_stateDetect] at hmem
  exact (G.detects_eq_true_iff _ (config k)).1 hmem

/-- **First-obstruction single-valuedness, residual-geometry singleton case.**  If
the classifier flags a package exit and the residual geometry exposes a *unique*
charge package `c`, the J.1.1 first-obstruction scan routes the start to `c`.  This
reuses the proved single-valuedness of the routing (the scan never returns a class
the geometry did not expose). -/
theorem classify_eq_of_geom_singleton (config : ℕ → LiftState) {k : ℕ} {c : Fin 7}
    (hpkg : G.IsCNLPackageExit (config k))
    (huniq : ∀ d : Fin 7, G.geomDetect d (config k) = true → d = c) :
    (G.toRouting config).classify k = c := by
  have hne1 : (G.toRouting config).classify k ≠ 1 := by
    intro h1
    exact (G.classify_eq_one_iff config k).1 h1 hpkg
  obtain ⟨_, hgeom⟩ := G.classify_mem_detect config hne1
  exact huniq _ hgeom

/-! ## 4.  Reusing the proved CNL classifier characterisations -/

/-- The proved `propositionK3_5_cnlTransitionClassifier` gives the **single-valued**
CNL class of each lift state (clean visibility supplies the nonempty available
set). -/
theorem cnlClass_existsUnique (s : LiftState) :
    ∃! cls : CNLClass,
      canonicalCNLSelector (G.cnlOf s) = some cls ∧
        cls ∈ (G.cnlOf s).available ∧
        ∀ d ∈ (G.cnlOf s).available,
          CNLClass.priorityRank cls ≤ CNLClass.priorityRank d :=
  propositionK3_5_cnlTransitionClassifier (G.cnlOf s) (G.clean_visible s)

/-- The single-valued CNL class itself (existence). -/
theorem exists_cnlClass (s : LiftState) :
    ∃ cls : CNLClass, canonicalCNLSelector (G.cnlOf s) = some cls :=
  exists_canonicalCNLSelector_eq_some_of_nonempty (G.clean_visible s)

/-- **Type-C selection routes to CleanCNL (via the proved `selected_eq_tc_iff`).**
If `TC` is available and the strictly-higher CNL classes `PKG, SEP, BND` are
absent, the proved selector returns `TC`, a clean class, so the start is routed to
CleanCNL. -/
theorem classify_eq_one_of_tc_available (config : ℕ → LiftState) {k : ℕ}
    (htc : CNLClass.tc ∈ (G.cnlOf (config k)).available)
    (hpkg : CNLClass.pkg ∉ (G.cnlOf (config k)).available)
    (hsep : CNLClass.sep ∉ (G.cnlOf (config k)).available)
    (hbnd : CNLClass.bnd ∉ (G.cnlOf (config k)).available) :
    (G.toRouting config).classify k = 1 :=
  G.classify_eq_one_of_clean config (by decide)
    ((selected_eq_tc_iff _).2 ⟨htc, hpkg, hsep, hbnd⟩)

/-- **Type-P (bridge) selection routes to CleanCNL (via the proved
`selected_eq_tp_iff`).**  If `TP` is available and all six higher-priority CNL
classes are absent, the proved selector returns `TP`, a clean class, so the start
is routed to CleanCNL. -/
theorem classify_eq_one_of_tp_available (config : ℕ → LiftState) {k : ℕ}
    (htp : CNLClass.tp ∈ (G.cnlOf (config k)).available)
    (hpkg : CNLClass.pkg ∉ (G.cnlOf (config k)).available)
    (hsep : CNLClass.sep ∉ (G.cnlOf (config k)).available)
    (hbnd : CNLClass.bnd ∉ (G.cnlOf (config k)).available)
    (htc : CNLClass.tc ∉ (G.cnlOf (config k)).available)
    (hvs : CNLClass.vs ∉ (G.cnlOf (config k)).available)
    (hds : CNLClass.ds ∉ (G.cnlOf (config k)).available) :
    (G.toRouting config).classify k = 1 :=
  G.classify_eq_one_of_clean config (by decide)
    ((selected_eq_tp_iff _).2 ⟨htp, hpkg, hsep, hbnd, htc, hvs, hds⟩)

/-- **The suffix dichotomy delivers a clean class (via the proved
`suffix_dichotomy_class`).**  The vanishing-suffix / determined-suffix class
produced by Lemma G.4 is one of `VS, DS`, both of which are clean CNL classes
(`≠ PKG`): the 2-adic dichotomy never produces a package exit. -/
theorem suffix_dichotomy_ne_pkg {E : ℕ → ℕ} {u : ℕ → ℤ} {n M : ℕ} {Z : ℤ}
    (hdec : ∀ t ∈ Finset.range n, E n < E t) (hodd : Odd (u n))
    (hcong : (2 : ℤ) ^ M ∣ (powerSum E u (n + 1) - Z)) :
    ∃ cls : CNLClass, (cls = CNLClass.vs ∨ cls = CNLClass.ds) ∧ cls ≠ CNLClass.pkg := by
  obtain ⟨cls, hmem, _, _⟩ := suffix_dichotomy_class hdec hodd hcong
  exact ⟨cls, hmem, by rcases hmem with rfl | rfl <;> decide⟩

/-- **A state selected as a suffix-dichotomy class routes to CleanCNL.**  Combining
`suffix_dichotomy_ne_pkg` with the derived CleanCNL law: if the proved classifier
assigns the lift state the `VS` or `DS` suffix class produced by Lemma G.4, the
start is CleanCNL. -/
theorem classify_eq_one_of_suffix_class (config : ℕ → LiftState) {k : ℕ}
    {cls : CNLClass} (hmem : cls = CNLClass.vs ∨ cls = CNLClass.ds)
    (hsel : canonicalCNLSelector (G.cnlOf (config k)) = some cls) :
    (G.toRouting config).classify k = 1 :=
  G.classify_eq_one_of_clean config (by rcases hmem with rfl | rfl <;> decide) hsel

end CNLObstructionGeometry

/-! ## 5.  Summary

`CNLObstructionGeometry.toPackageDetector` is a genuine `ObstructionProfile`
`PackageDetector` whose `detects` predicate is the **proved CNL classifier**
(`canonicalCNLSelector`, `propositionK3_5_cnlTransitionClassifier`) used as a
clean/package gate over the residual per-state geometry `geomDetect`.  Feeding it
through `PackageDetector.toGeometry.toRouting` (i.e. `CarryPriorityRouting.ofDetect`,
exhibited as `ofStateProfile`) discharges the J.1.1 exhaustiveness primitive
`cleanCNL_mem`, and:

* **CleanCNL is fully derived** from the proved classifier: a start is routed to
  the deliberately-last CleanCNL class iff its state is CNL-clean
  (`classify_eq_one_iff`), and every package routing is certified `PKG` and
  genuinely exposed (`classify_mem_detect`);

* **which charge package** a package-exit state exposes is the irreducible residual
  geometry `geomDetect` (with the faithful `pkg_exposes` invariant), exactly the
  genuinely dynamical input the CNL classifier does not decide.
-/

end

end Erdos260
