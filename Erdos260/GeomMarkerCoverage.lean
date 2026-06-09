import Mathlib
import Erdos260.PackageRealization

/-!
# Closing the `geomDetect` coverage residual `pkg_marked` against the J.1.1 seven-class scan

`GeomDetectConstruction.lean` reduced the obstruction geometry to a six-marker priority scan
`CNLPackageMarkers.labelOf` whose **only** residual is the coverage field

* `pkg_marked` : every classifier-flagged package exit (`canonicalCNLSelector (cnlOf s) =
  some PKG`) fires at least one of the six markers (progress `0`, Tower `2`, DensePack `3`,
  Return `4`, Run `5`, old-residual `6`).

This file (new; it edits no existing file) **discharges `pkg_marked` as a theorem** for a
concretely-constructed `CNLPackageMarkers`, by *restricting the proved seven-class J.1.1 scan
to non-CleanCNL states*.

## The mechanism (manuscript J.1.1, "the order of the scan selects the first applicable class")

The seven v5 charge classes are `Fin 7 = {0,1,2,3,4,5,6}`.  The six `GeomPackage` markers are
exactly the **non-CleanCNL** classes `Fin 7 \ {1} = {0,2,3,4,5,6}` (`GeomPackage.toCharge` is a
bijection onto them, with `1` — CleanCNL — deliberately absent).  We prove the scan-level fact

* `j11Scan_eq_some_package_iff` — the J.1.1 first-obstruction scan lands in a `GeomPackage`
  charge **iff** some package class is exposed in the profile;
* `GeomPackage.exists_toCharge_eq_of_ne_one` — every non-CleanCNL charge `c ≠ 1` is a genuine
  `GeomPackage` marker.

and then build, from any obstruction geometry `G : CNLObstructionGeometry`, the concrete

* `CNLObstructionGeometry.toMarkers : CNLPackageMarkers` — the six markers
  `geomDetect {0,2,3,4,5,6}`, whose `pkg_marked` field is a **proved theorem**:  a PKG-exit
  exposes some charge class `c` (`pkg_exposes`); `c ≠ 1` (`geom_not_cnl`); so `c ∈ {0,2,3,4,5,6}`
  is one of the six markers, which therefore fires.

Consequently (reusing the already-proved `PackageRealization` lemmas for the constructed
markers):

* `toMarkers_pkg_exit_classify_ne_one` — a PKG-exit is routed by the J.1.1 charge scan to a
  genuine package class (`≠ 1`);
* `toMarkers_pkg_exit_scanned_package` — in fact to the charge of its scanned `GeomPackage`
  marker (restricting the seven-class scan to non-clean states lands it in the six-marker set).

## Honest verdict

**`pkg_marked` is CLOSED *relative to the obstruction-geometry coverage* `pkg_exposes`** — it is
now a Lean theorem (`CNLObstructionGeometry.toMarkers.pkg_marked`), not an assumed structure
field, for the markers built from any `G`.  The two coverage residuals are in fact **equivalent**:
`pkg_exposes ⟹ pkg_marked` is this file's `toMarkers`; `pkg_marked ⟹ pkg_exposes` is the existing
`CNLPackageMarking.pkg_exposes` (proved from `pkg_labeled`, i.e. from `pkg_marked` through the
priority scan).

`pkg_marked` is **NOT** derivable from the seven-class scan's *exhaustiveness/single-valuedness*
alone.  Exhaustiveness (`j11Scan_isSome_of_one_mem`, `toRouting_cleanCNL_mem`) only supplies the
**always-present CleanCNL catch-all** (class `1`): a profile carrying *only* the catch-all is
scanned to `1`, not to a package (`j11Scan_catchall_only`).  The irreducible input is the
geometric fact that a PKG verdict exposes a *genuine* charge class — exactly `pkg_exposes`, here
shown identical to the six-marker coverage `pkg_marked`.  The CNL classifier decides
*clean vs package*; *which* package (equivalently *that* a package class lands in the profile) is
the deep K/L/N geometry, faithfully isolated as this single primitive.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  `GeomPackage` is exactly the six non-CleanCNL charge classes `Fin 7 \ {1}` -/

/-- **The inverse of `GeomPackage.toCharge` on the non-CleanCNL classes.**  Every charge class
`c ≠ 1` (CleanCNL) is the charge of a genuine `GeomPackage` marker — the six markers exhaust
`Fin 7 \ {1} = {0,2,3,4,5,6}`. -/
theorem GeomPackage.exists_toCharge_eq_of_ne_one {c : Fin 7} (hc : c ≠ 1) :
    ∃ p : GeomPackage, p.toCharge = c := by
  have hval : c.val = 0 ∨ c.val = 2 ∨ c.val = 3 ∨ c.val = 4 ∨ c.val = 5 ∨ c.val = 6 := by
    have h7 : c.val < 7 := c.isLt
    have h1 : c.val ≠ 1 := fun h => hc (Fin.ext h)
    omega
  rcases hval with h | h | h | h | h | h
  · exact ⟨GeomPackage.progress, Fin.ext h.symm⟩
  · exact ⟨GeomPackage.tower, Fin.ext h.symm⟩
  · exact ⟨GeomPackage.densePack, Fin.ext h.symm⟩
  · exact ⟨GeomPackage.returnPkg, Fin.ext h.symm⟩
  · exact ⟨GeomPackage.run, Fin.ext h.symm⟩
  · exact ⟨GeomPackage.oldRes, Fin.ext h.symm⟩

/-! ## 2.  Restricting the proved seven-class J.1.1 scan to non-CleanCNL states

These are facts about the *existing* `j11Scan` (`CarryRouting.lean`).  They make precise what
"restrict the seven-class scan to non-clean states" means: the scan lands in a `GeomPackage`
charge **iff** a package class is exposed — the CleanCNL catch-all `1` is selected only when no
package class is present. -/

/-- **A package class in the profile forces a package verdict.**  If any of the six package
classes `{6,3,0,5,4,2}` is exposed, the J.1.1 first-obstruction scan returns one of them — never
the deliberately-last CleanCNL class `1`. -/
theorem j11Scan_ne_one_of_package_mem {avail : Finset (Fin 7)}
    (hP : (6 : Fin 7) ∈ avail ∨ (3 : Fin 7) ∈ avail ∨ (0 : Fin 7) ∈ avail ∨
      (5 : Fin 7) ∈ avail ∨ (4 : Fin 7) ∈ avail ∨ (2 : Fin 7) ∈ avail) :
    ∃ c : Fin 7, j11Scan avail = some c ∧ c ≠ 1 := by
  unfold j11Scan
  split_ifs with h6 h3 h0 h5 h4 h2 h1
  · exact ⟨6, rfl, by decide⟩
  · exact ⟨3, rfl, by decide⟩
  · exact ⟨0, rfl, by decide⟩
  · exact ⟨5, rfl, by decide⟩
  · exact ⟨4, rfl, by decide⟩
  · exact ⟨2, rfl, by decide⟩
  · exfalso; rcases hP with h | h | h | h | h | h
    · exact h6 h
    · exact h3 h
    · exact h0 h
    · exact h5 h
    · exact h4 h
    · exact h2 h
  · exfalso; rcases hP with h | h | h | h | h | h
    · exact h6 h
    · exact h3 h
    · exact h0 h
    · exact h5 h
    · exact h4 h
    · exact h2 h

/-- **The seven-class scan lands in a `GeomPackage` marker iff a package class is exposed.**
This is the exact content of "restrict the proved J.1.1 first-obstruction scan to non-CleanCNL
states": the scan's value is a genuine `GeomPackage` charge precisely when the obstruction
profile carries one of the six package classes. -/
theorem j11Scan_eq_some_package_iff (avail : Finset (Fin 7)) :
    (∃ p : GeomPackage, j11Scan avail = some p.toCharge) ↔
      (∃ p : GeomPackage, p.toCharge ∈ avail) := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, j11Scan_eq_some_mem hp⟩
  · rintro ⟨p, hp⟩
    have hP : (6 : Fin 7) ∈ avail ∨ (3 : Fin 7) ∈ avail ∨ (0 : Fin 7) ∈ avail ∨
        (5 : Fin 7) ∈ avail ∨ (4 : Fin 7) ∈ avail ∨ (2 : Fin 7) ∈ avail := by
      cases p with
      | progress => exact Or.inr (Or.inr (Or.inl hp))
      | tower => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp))))
      | densePack => exact Or.inr (Or.inl hp)
      | returnPkg => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))
      | run => exact Or.inr (Or.inr (Or.inr (Or.inl hp)))
      | oldRes => exact Or.inl hp
    obtain ⟨c, hsc, hc1⟩ := j11Scan_ne_one_of_package_mem hP
    obtain ⟨q, hq⟩ := GeomPackage.exists_toCharge_eq_of_ne_one hc1
    exact ⟨q, by rw [hsc, hq]⟩

/-- **Why exhaustiveness is not coverage.**  A profile carrying *only* the always-present
CleanCNL catch-all (class `1`) is scanned to `1`, not to a package.  So the seven-class scan's
exhaustiveness (`j11Scan_isSome_of_one_mem`) cannot, by itself, certify that a PKG-exit is routed
to a genuine package; that is the irreducible coverage primitive. -/
theorem j11Scan_catchall_only : j11Scan ({1} : Finset (Fin 7)) = some 1 := by decide

/-! ## 3.  The package-marker assignment built from an obstruction geometry

From any `CNLObstructionGeometry G`, the six markers are read off `geomDetect` at the six
non-CleanCNL charges, and the coverage residual `pkg_marked` becomes a **proved theorem** via the
six-into-seven embedding `{0,2,3,4,5,6} = Fin 7 \ {1}`. -/

namespace CNLObstructionGeometry

variable (G : CNLObstructionGeometry)

/-- **Six markers cover, from one exposed non-CleanCNL class.**  If the geometry exposes any
charge class `c ≠ 1` at `s`, then one of the six `GeomPackage` markers
(`geomDetect {0,2,3,4,5,6}`) fires at `s`.  This is the combinatorial core: `c ∈ Fin 7 \ {1} =
{0,2,3,4,5,6}`. -/
theorem geomDetect_ne_one_disjunction {s : LiftState} {c : Fin 7}
    (hc : G.geomDetect c s = true) (hc1 : c ≠ 1) :
    G.geomDetect 0 s = true ∨ G.geomDetect 2 s = true ∨ G.geomDetect 3 s = true ∨
      G.geomDetect 4 s = true ∨ G.geomDetect 5 s = true ∨ G.geomDetect 6 s = true := by
  have hval : c.val = 0 ∨ c.val = 2 ∨ c.val = 3 ∨ c.val = 4 ∨ c.val = 5 ∨ c.val = 6 := by
    have h7 : c.val < 7 := c.isLt
    have h1 : c.val ≠ 1 := fun h => hc1 (Fin.ext h)
    omega
  rcases hval with h | h | h | h | h | h
  · exact Or.inl (by rw [show c = (0 : Fin 7) from Fin.ext h] at hc; exact hc)
  · exact Or.inr (Or.inl (by rw [show c = (2 : Fin 7) from Fin.ext h] at hc; exact hc))
  · exact Or.inr (Or.inr (Or.inl (by rw [show c = (3 : Fin 7) from Fin.ext h] at hc; exact hc)))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [show c = (4 : Fin 7) from Fin.ext h] at hc; exact hc
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    rw [show c = (5 : Fin 7) from Fin.ext h] at hc; exact hc
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    rw [show c = (6 : Fin 7) from Fin.ext h] at hc; exact hc

/-- **The coverage residual, proved.**  A PKG-exit fires one of the six markers — its exposed
charge (`pkg_exposes`) is non-CleanCNL (`geom_not_cnl`), hence one of `{0,2,3,4,5,6}`. -/
theorem geomDetect_package_of_pkg_exit {s : LiftState}
    (hs : canonicalCNLSelector (G.cnlOf s) = some CNLClass.pkg) :
    G.geomDetect 0 s = true ∨ G.geomDetect 2 s = true ∨ G.geomDetect 3 s = true ∨
      G.geomDetect 4 s = true ∨ G.geomDetect 5 s = true ∨ G.geomDetect 6 s = true := by
  obtain ⟨c, hc⟩ := G.pkg_exposes s hs
  refine G.geomDetect_ne_one_disjunction hc ?_
  rintro rfl
  rw [G.geom_not_cnl s] at hc
  exact Bool.noConfusion hc

/-- **The concrete `CNLPackageMarkers` with `pkg_marked` discharged.**  The six markers are
`geomDetect` at the six non-CleanCNL charges; the coverage field `pkg_marked` is the theorem
`geomDetect_package_of_pkg_exit`, derived from the obstruction-geometry invariants
`pkg_exposes` + `geom_not_cnl`. -/
def toMarkers : CNLPackageMarkers where
  cnlOf := G.cnlOf
  clean_visible := G.clean_visible
  markProgress := fun s => G.geomDetect 0 s
  markTower := fun s => G.geomDetect 2 s
  markDensePack := fun s => G.geomDetect 3 s
  markReturn := fun s => G.geomDetect 4 s
  markRun := fun s => G.geomDetect 5 s
  markOldRes := fun s => G.geomDetect 6 s
  pkg_marked := fun _s hs => G.geomDetect_package_of_pkg_exit hs

@[simp] theorem toMarkers_cnlOf (s : LiftState) : G.toMarkers.cnlOf s = G.cnlOf s := rfl
@[simp] theorem toMarkers_markProgress (s : LiftState) :
    G.toMarkers.markProgress s = G.geomDetect 0 s := rfl
@[simp] theorem toMarkers_markTower (s : LiftState) :
    G.toMarkers.markTower s = G.geomDetect 2 s := rfl
@[simp] theorem toMarkers_markDensePack (s : LiftState) :
    G.toMarkers.markDensePack s = G.geomDetect 3 s := rfl
@[simp] theorem toMarkers_markReturn (s : LiftState) :
    G.toMarkers.markReturn s = G.geomDetect 4 s := rfl
@[simp] theorem toMarkers_markRun (s : LiftState) :
    G.toMarkers.markRun s = G.geomDetect 5 s := rfl
@[simp] theorem toMarkers_markOldRes (s : LiftState) :
    G.toMarkers.markOldRes s = G.geomDetect 6 s := rfl

/-! ### Consequences for the constructed markers (reusing `PackageRealization`)

With `pkg_marked` now a theorem, the `PackageRealization` lemmas — proved for *any*
`CNLPackageMarkers` from its `pkg_marked` field — specialise to genuine theorems about the J.1.1
charge routing of `G.toMarkers`. -/

/-- **A PKG-exit is routed to a genuine package class.**  Restricting the seven-class J.1.1 scan
to a non-CleanCNL state never returns the CleanCNL catch-all `1`. -/
theorem toMarkers_pkg_exit_classify_ne_one (config : ℕ → LiftState) {k : ℕ}
    (h : canonicalCNLSelector (G.cnlOf (config k)) = some CNLClass.pkg) :
    (G.toMarkers.toMarking.toObstructionGeometry.toRouting config).classify k ≠ 1 :=
  G.toMarkers.pkg_exit_classify_ne_one config h

/-- **A PKG-exit's seven-class scan lands in its scanned `GeomPackage` marker's charge.**  The
J.1.1 first-obstruction scan of a non-CleanCNL state is pinned to a genuine six-class package
charge `p.toCharge ∈ {0,2,3,4,5,6}`. -/
theorem toMarkers_pkg_exit_scanned_package (config : ℕ → LiftState) {k : ℕ}
    (h : canonicalCNLSelector (G.cnlOf (config k)) = some CNLClass.pkg) :
    ∃ p : GeomPackage, G.toMarkers.labelOf (config k) = some p ∧
      (G.toMarkers.toMarking.toObstructionGeometry.toRouting config).classify k = p.toCharge :=
  G.toMarkers.pkg_exit_classify_eq_scanned_charge config h

/-- **The equivalence direction `pkg_exposes ⟹ pkg_marked`, packaged.**  The six-marker coverage
holds for the constructed markers exactly because the obstruction geometry covers PKG-exits.  The
reverse direction `pkg_marked ⟹ pkg_exposes` is the existing `CNLPackageMarking.pkg_exposes`. -/
theorem toMarkers_anyMarker_of_pkg_exit {s : LiftState}
    (h : canonicalCNLSelector (G.cnlOf s) = some CNLClass.pkg) :
    G.toMarkers.anyMarker s = true :=
  (G.toMarkers.anyMarker_iff s).2 (G.toMarkers.pkg_marked s h)

end CNLObstructionGeometry

/-! ## 4.  A concrete, non-degenerate end-to-end witness

Unlike the all-`progress` witness already in `GeomDetectConstruction`, this one exposes the
**DensePack** class `3`: every state presents the package-exit transition `⟨_, {PKG}⟩` and its
geometry exposes charge `3`.  Its `pkg_marked` is the proved theorem above, and its J.1.1 charge
routing is pinned to DensePack (`3`). -/

/-- A concrete obstruction geometry exposing DensePack (charge `3`) on every package exit. -/
def denseObstructionGeometry : CNLObstructionGeometry where
  cnlOf := fun _ => ⟨CNLNormalForm.positiveLift, {CNLClass.pkg}⟩
  clean_visible := fun _ => ⟨CNLClass.pkg, Finset.mem_singleton_self _⟩
  geomDetect := fun c _ => decide (c = 3)
  geom_not_cnl := fun _ => by decide
  pkg_exposes := fun _ _ => ⟨3, by decide⟩

/-- Its package markers — `pkg_marked` is the proved coverage theorem. -/
def denseMarkers : CNLPackageMarkers := denseObstructionGeometry.toMarkers

theorem denseMarkers_markProgress (s : LiftState) : denseMarkers.markProgress s = false := rfl
theorem denseMarkers_markTower (s : LiftState) : denseMarkers.markTower s = false := rfl
theorem denseMarkers_markDensePack (s : LiftState) : denseMarkers.markDensePack s = true := rfl

/-- The priority scan records DensePack at every state. -/
theorem denseMarkers_labelOf (s : LiftState) :
    denseMarkers.labelOf s = some GeomPackage.densePack := by
  unfold CNLPackageMarkers.labelOf
  rw [if_neg (by rw [denseMarkers_markProgress]; decide),
    if_neg (by rw [denseMarkers_markTower]; decide),
    if_pos (denseMarkers_markDensePack s)]

/-- Every state is a package exit (the canonical CNL selector returns `PKG`). -/
theorem denseMarkers_pkg_exit (s : LiftState) :
    canonicalCNLSelector (denseMarkers.cnlOf s) = some CNLClass.pkg :=
  selectCNLClass?_eq_pkg_of_mem (Finset.mem_singleton_self _)

/-- **The witness routes every start to the DensePack class `3`**, with `pkg_marked` discharged,
the seven-class scan restricted to the (everywhere) non-clean states, and the routing pinned to a
genuine `GeomPackage` charge. -/
theorem denseMarkers_classify_eq_three (config : ℕ → LiftState) (k : ℕ) :
    (denseMarkers.toMarking.toObstructionGeometry.toRouting config).classify k = 3 := by
  have hlabel : denseMarkers.toMarking.label (config k) = some GeomPackage.densePack := by
    rw [CNLPackageMarkers.toMarking_label]; exact denseMarkers_labelOf (config k)
  have h := denseMarkers.toMarking.classify_eq_charge_of_label config
    (denseMarkers_pkg_exit (config k)) hlabel
  simpa [GeomPackage.toCharge] using h

/-! ## 5.  Residual inventory (honest) -/

/-- The honest status of the coverage residual after this round. -/
def geomMarkerCoverageResidual : List String :=
  [ "CLOSED relative to `pkg_exposes`: `CNLObstructionGeometry.toMarkers` is a concrete " ++
      "`CNLPackageMarkers` whose `pkg_marked` coverage field is a PROVED THEOREM " ++
      "(`geomDetect_package_of_pkg_exit`), derived from the obstruction-geometry invariants " ++
      "`pkg_exposes` + `geom_not_cnl` via the six-into-seven embedding {0,2,3,4,5,6} = Fin 7\\{1}.",
    "EQUIVALENCE: `pkg_marked` ⟺ `pkg_exposes` (forward = `toMarkers`; reverse = the existing " ++
      "`CNLPackageMarking.pkg_exposes` from `pkg_labeled`). The six-marker coverage and the " ++
      "obstruction-geometry coverage are the same primitive.",
    "IRREDUCIBLE: coverage is NOT a consequence of the seven-class scan's exhaustiveness/" ++
      "single-valuedness, which only supply the always-present CleanCNL catch-all class 1 " ++
      "(`j11Scan_catchall_only`: j11Scan {1} = some 1). The geometric fact that a PKG verdict " ++
      "exposes a genuine charge class (`pkg_exposes`) is the smallest deep K/L/N input." ]

theorem geomMarkerCoverageResidual_nonempty : geomMarkerCoverageResidual ≠ [] := by
  simp [geomMarkerCoverageResidual]

end

end Erdos260
