import Mathlib
import Erdos260.CarryRouting
import Erdos260.LiftState

/-!
# The per-start obstruction profile and the J.1.1 exhaustiveness primitive

`CarryRouting.lean` builds the Lemma J.1.1 first-obstruction priority routing
`classify` out of a `CarryPriorityRouting`, which carries **two** faithful
primitives:

* the per-start **obstruction profile** `obstruction : ℕ → Finset (Fin 7)` (the
  set of charge-classes whose geometric obstruction is *exposed* at a start), and
* the J.1.1 **exhaustiveness** primitive `cleanCNL_mem : ∀ k, (1 : Fin 7) ∈
  obstruction k` (CleanCNL, class `1`, is always available as the catch-all last
  class).

This file **advances the construction** of the obstruction profile from the
carry/lift dynamics and **proves** the exhaustiveness primitive `cleanCNL_mem`,
turning it from an assumed structure field into a discharged theorem.

## The honest decomposition

J.1.1's exhaustiveness — *"every retained fibre belongs to some class, with
`CleanCNL` deliberately last (the catch-all of fibres on which no obstruction
occurs)"* — splits into two pieces of very different depth:

* **Detection of package obstructions** (classes `0,2,3,4,5,6`): *which* lift
  configurations expose *which* package-class obstruction.  This is the deep
  K/L/N manuscript geometry; it is the **irreducible faithful primitive** and is
  carried here as data (`stateDetect` / `detects`).  We do **not** fabricate it.

* **Availability of the CleanCNL catch-all** (class `1`): this is *not* deep.
  By the very definition of `CleanCNL` as the catch-all — the class of fibres on
  which no package obstruction occurs — it is always a valid fallback.  We model
  this honestly: the full profile is `obstruction k = insert 1 (detect k)`, the
  detected packages together with the unconditionally-present catch-all.  Then
  `cleanCNL_mem` is a **theorem** (`Finset.mem_insert_self`), not an assumption.

## What is genuinely proved here (no `sorry`/`axiom`)

* `CarryPriorityRouting.ofDetect` — builds a `CarryPriorityRouting` from *any*
  package-detection profile `detect : ℕ → Finset (Fin 7)`, with the J.1.1
  exhaustiveness primitive `cleanCNL_mem` **discharged** by the catch-all design.
* `CarryPriorityRouting.ofStateProfile` — the genuine **reduction of
  exhaustiveness to per-state classification**: the global `cleanCNL_mem` over all
  starts follows from the per-state fact that every lift-state profile exposes
  CleanCNL.
* Full classifier behaviour on the constructed profile: the catch-all law
  (no package detected ⟹ routed to CleanCNL), the converse (routed to a package
  ⟹ that package was genuinely detected), and the exact characterisation
  `classify k = 1 ↔` no package class is detected (⟺ `detect k = ∅` under the
  faithful "CleanCNL is never itself detected" invariant).
* `LiftObstructionGeometry` / `PackageDetector` — the carry/lift-dynamics model:
  detection on lift states (`LiftState`), optionally presented as six per-class
  Boolean detectors, converted into the constructed routing.

## What remains the irreducible faithful primitive

The **obstruction-detection geometry** `stateDetect : LiftState → Finset (Fin 7)`
(equivalently the per-class `detects : Fin 7 → LiftState → Bool`): which lift
configurations are which class.  This is the genuine deep input and is supplied
as data, exactly as `CarryRouting.lean`'s `obstruction` field was.  (The seven
per-class **mass** bounds remain the other deep input, isolated already in
`CarryPriorityRoutingCharge`; they are out of scope here.)
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The CleanCNL branch of the J.1.1 scan

Two small facts about the existing `j11Scan` (defined in `CarryRouting.lean`):
the scan returns `CleanCNL` (class `1`) only when no higher-priority package
class is exposed, and an elementary insertion lemma for the catch-all. -/

/-- **CleanCNL is the deliberately-last class.**  If the J.1.1 scan selects
CleanCNL (class `1`), then none of the six package classes `6,3,0,5,4,2` is
exposed — the precise content of "CleanCNL is chosen only when no package
obstruction occurs". -/
theorem j11Scan_eq_one_imp {avail : Finset (Fin 7)} (h : j11Scan avail = some 1) :
    (6 : Fin 7) ∉ avail ∧ (3 : Fin 7) ∉ avail ∧ (0 : Fin 7) ∉ avail ∧
      (5 : Fin 7) ∉ avail ∧ (4 : Fin 7) ∉ avail ∧ (2 : Fin 7) ∉ avail := by
  unfold j11Scan at h
  split_ifs at h with h6 h3 h0 h5 h4 h2 h1 <;>
    first
      | exact ⟨h6, h3, h0, h5, h4, h2⟩
      | exact absurd h (by decide)

/-- A non-CleanCNL class is absent from the catch-all profile `insert 1 s`
exactly when it is absent from the detected packages `s`. -/
theorem not_mem_insert_one {x : Fin 7} (hx : x ≠ 1) {s : Finset (Fin 7)}
    (hxs : x ∉ s) : x ∉ insert (1 : Fin 7) s := fun hmem =>
  (Finset.mem_insert.1 hmem).elim hx hxs

/-! ## 2.  The CleanCNL catch-all profile

The full per-start obstruction profile is the detected **package** obstructions
together with the unconditionally-present CleanCNL catch-all. -/

/-- Adjoin the always-available CleanCNL catch-all (class `1`) to a per-start
package-detection profile `detect`. -/
def withCleanCNL (detect : ℕ → Finset (Fin 7)) : ℕ → Finset (Fin 7) :=
  fun k => insert 1 (detect k)

theorem mem_withCleanCNL {detect : ℕ → Finset (Fin 7)} {k : ℕ} {j : Fin 7} :
    j ∈ withCleanCNL detect k ↔ j = 1 ∨ j ∈ detect k := Finset.mem_insert

/-- **The exhaustiveness primitive, discharged.**  CleanCNL (class `1`) is always
present in the catch-all profile — this is `CarryPriorityRouting.cleanCNL_mem`,
now a theorem rather than an assumed field. -/
theorem cleanCNL_mem_withCleanCNL (detect : ℕ → Finset (Fin 7)) (k : ℕ) :
    (1 : Fin 7) ∈ withCleanCNL detect k := Finset.mem_insert_self _ _

namespace CarryPriorityRouting

/-! ## 3.  Generic classifier behaviour via the obstruction equation

These lemmas hold for *any* `CarryPriorityRouting R` whose obstruction profile at
`k` is a catch-all profile `insert 1 (D k)`.  They are stated abstractly through
the hypothesis `hobs` and specialised below to the concrete constructors, so no
construction-specific `defeq` is relied on. -/

/-- If the classifier selects CleanCNL, the underlying scan really returns
`some 1` (using `cleanCNL_mem` to rule out the empty-scan fallback). -/
theorem classify_eq_one_imp (R : CarryPriorityRouting) {k : ℕ}
    (h : R.classify k = 1) : j11Scan (R.obstruction k) = some 1 := by
  have h1 : (1 : Fin 7) ∈ R.obstruction k := R.cleanCNL_mem k
  cases hi : j11Scan (R.obstruction k) with
  | none =>
      have hsome := j11Scan_isSome_of_one_mem h1
      rw [hi] at hsome
      simp at hsome
  | some i =>
      rw [classify_eq, hi] at h
      simp only [Option.getD_some] at h
      rw [h]

/-- **Converse of the catch-all law.**  If a start is routed to a non-CleanCNL
class, that class was genuinely *detected* (it lies in `D k`); the classifier
never invents a package obstruction. -/
theorem classify_mem_of_obstruction_insert (R : CarryPriorityRouting)
    {D : ℕ → Finset (Fin 7)} {k : ℕ} (hobs : R.obstruction k = insert 1 (D k))
    (h : R.classify k ≠ 1) : R.classify k ∈ D k := by
  have hmem := R.classify_mem_obstruction k
  rw [hobs] at hmem
  rcases Finset.mem_insert.1 hmem with h1 | hd
  · exact absurd h1 h
  · exact hd

/-- **The catch-all law.**  A start with no detected package obstruction is
routed to CleanCNL. -/
theorem classify_eq_one_of_obstruction_insert_of_empty (R : CarryPriorityRouting)
    {D : ℕ → Finset (Fin 7)} {k : ℕ} (hobs : R.obstruction k = insert 1 (D k))
    (h : D k = ∅) : R.classify k = 1 := by
  refine R.classify_eq_cnl ?_ ?_ ?_ ?_ ?_ ?_ <;> rw [hobs, h]
  all_goals exact not_mem_insert_one (by decide) (Finset.notMem_empty _)

/-- **Exact CleanCNL characterisation.**  A start is routed to CleanCNL iff none
of the six package classes is detected. -/
theorem classify_eq_one_iff_of_obstruction_insert (R : CarryPriorityRouting)
    {D : ℕ → Finset (Fin 7)} {k : ℕ} (hobs : R.obstruction k = insert 1 (D k)) :
    R.classify k = 1 ↔
      (6 : Fin 7) ∉ D k ∧ (3 : Fin 7) ∉ D k ∧ (0 : Fin 7) ∉ D k ∧
        (5 : Fin 7) ∉ D k ∧ (4 : Fin 7) ∉ D k ∧ (2 : Fin 7) ∉ D k := by
  constructor
  · intro h
    obtain ⟨h6, h3, h0, h5, h4, h2⟩ := j11Scan_eq_one_imp (R.classify_eq_one_imp h)
    rw [hobs] at h6 h3 h0 h5 h4 h2
    exact ⟨fun hc => h6 (Finset.mem_insert_of_mem hc),
           fun hc => h3 (Finset.mem_insert_of_mem hc),
           fun hc => h0 (Finset.mem_insert_of_mem hc),
           fun hc => h5 (Finset.mem_insert_of_mem hc),
           fun hc => h4 (Finset.mem_insert_of_mem hc),
           fun hc => h2 (Finset.mem_insert_of_mem hc)⟩
  · rintro ⟨h6, h3, h0, h5, h4, h2⟩
    refine R.classify_eq_cnl ?_ ?_ ?_ ?_ ?_ ?_ <;> rw [hobs]
    exacts [not_mem_insert_one (by decide) h6, not_mem_insert_one (by decide) h3,
            not_mem_insert_one (by decide) h0, not_mem_insert_one (by decide) h5,
            not_mem_insert_one (by decide) h4, not_mem_insert_one (by decide) h2]

/-! ## 4.  The per-start detection constructor `ofDetect`

The headline artifact: build a `CarryPriorityRouting` from *any* package-detection
profile, with the J.1.1 exhaustiveness primitive `cleanCNL_mem` **proved**. -/

/-- **Build the J.1.1 routing from a package-detection profile.**  The only input
is the faithful geometric primitive `detect` (the exposed *package* obstructions
per start).  The exhaustiveness primitive `cleanCNL_mem` is **discharged** by the
catch-all design `obstruction = insert 1 ∘ detect`. -/
def ofDetect (detect : ℕ → Finset (Fin 7)) : CarryPriorityRouting where
  obstruction := withCleanCNL detect
  cleanCNL_mem := cleanCNL_mem_withCleanCNL detect

@[simp] theorem ofDetect_obstruction (detect : ℕ → Finset (Fin 7)) (k : ℕ) :
    (ofDetect detect).obstruction k = insert 1 (detect k) := rfl

/-- The exhaustiveness primitive holds for the constructed routing — proved. -/
theorem ofDetect_cleanCNL_mem (detect : ℕ → Finset (Fin 7)) (k : ℕ) :
    (1 : Fin 7) ∈ (ofDetect detect).obstruction k :=
  (ofDetect detect).cleanCNL_mem k

theorem ofDetect_classify_mem_detect_of_ne_one (detect : ℕ → Finset (Fin 7))
    {k : ℕ} (h : (ofDetect detect).classify k ≠ 1) :
    (ofDetect detect).classify k ∈ detect k :=
  classify_mem_of_obstruction_insert _ (ofDetect_obstruction detect k) h

theorem ofDetect_classify_eq_one_of_empty (detect : ℕ → Finset (Fin 7))
    {k : ℕ} (h : detect k = ∅) : (ofDetect detect).classify k = 1 :=
  classify_eq_one_of_obstruction_insert_of_empty _ (ofDetect_obstruction detect k) h

theorem ofDetect_classify_eq_one_iff (detect : ℕ → Finset (Fin 7)) (k : ℕ) :
    (ofDetect detect).classify k = 1 ↔
      (6 : Fin 7) ∉ detect k ∧ (3 : Fin 7) ∉ detect k ∧ (0 : Fin 7) ∉ detect k ∧
        (5 : Fin 7) ∉ detect k ∧ (4 : Fin 7) ∉ detect k ∧ (2 : Fin 7) ∉ detect k :=
  classify_eq_one_iff_of_obstruction_insert _ (ofDetect_obstruction detect k)

/-! ## 5.  The per-state reduction `ofStateProfile`

The genuine reduction asked for by J.1.1: the *global* exhaustiveness
`cleanCNL_mem` (over all `ℕ` starts) follows from the *per-state* classification
fact that every lift-state profile exposes CleanCNL. -/

/-- **Reduce exhaustiveness to a per-state classification fact.**  Given a
per-state obstruction profile `stateObstruction` and a per-start configuration
`config`, the global `cleanCNL_mem` follows from the per-state fact `hstate`
(every state's profile exposes CleanCNL). -/
def ofStateProfile {S : Type*} (stateObstruction : S → Finset (Fin 7))
    (config : ℕ → S) (hstate : ∀ s, (1 : Fin 7) ∈ stateObstruction s) :
    CarryPriorityRouting where
  obstruction := fun k => stateObstruction (config k)
  cleanCNL_mem := fun k => hstate (config k)

@[simp] theorem ofStateProfile_obstruction {S : Type*}
    (stateObstruction : S → Finset (Fin 7)) (config : ℕ → S)
    (hstate : ∀ s, (1 : Fin 7) ∈ stateObstruction s) (k : ℕ) :
    (ofStateProfile stateObstruction config hstate).obstruction k
      = stateObstruction (config k) := rfl

end CarryPriorityRouting

/-! ## 6.  The carry/lift-dynamics model

The obstruction-detection geometry lives on the manuscript's lift states
`LiftState` (`(δ, q)`, Appendix G).  `stateDetect` is the irreducible faithful
primitive — which lift configurations expose which package obstruction. -/

/-- **The obstruction-detection geometry (faithful primitive).**

`stateDetect s` is the set of *package* charge-classes whose defining geometric
obstruction (dense marker, run explanation, complete return, tower atom,
old-residual leakage, …) is exposed by the lift state `s`.  CleanCNL (class `1`)
is *never* itself detected — it is the catch-all, adjoined unconditionally.
Computing `stateDetect` is the deep K/L/N manuscript geometry; here it is data. -/
structure LiftObstructionGeometry where
  /-- FAITHFUL PRIMITIVE — the exposed package obstructions of each lift state. -/
  stateDetect : LiftState → Finset (Fin 7)
  /-- FAITHFUL invariant — CleanCNL is the *absence* of a package obstruction, so
  the detector never reports it. -/
  cleanCNL_not_detected : ∀ s, (1 : Fin 7) ∉ stateDetect s

namespace LiftObstructionGeometry

/-- **The J.1.1 routing of a lift-configuration sequence.**  Built from the
detection geometry by the catch-all construction; `cleanCNL_mem` is proved. -/
def toRouting (G : LiftObstructionGeometry) (config : ℕ → LiftState) :
    CarryPriorityRouting :=
  CarryPriorityRouting.ofDetect (fun k => G.stateDetect (config k))

@[simp] theorem toRouting_obstruction (G : LiftObstructionGeometry)
    (config : ℕ → LiftState) (k : ℕ) :
    (G.toRouting config).obstruction k = insert 1 (G.stateDetect (config k)) := rfl

/-- The lift-state routing is exactly the per-state reduction `ofStateProfile`
applied to the catch-all per-state profiles — the per-state exhaustiveness fact
is `Finset.mem_insert_self`. -/
theorem toRouting_eq_ofStateProfile (G : LiftObstructionGeometry)
    (config : ℕ → LiftState) :
    G.toRouting config =
      CarryPriorityRouting.ofStateProfile (fun s => insert 1 (G.stateDetect s))
        config (fun s => Finset.mem_insert_self 1 (G.stateDetect s)) := rfl

/-- **The exhaustiveness primitive holds for the lift-state routing — proved.** -/
theorem toRouting_cleanCNL_mem (G : LiftObstructionGeometry)
    (config : ℕ → LiftState) (k : ℕ) :
    (1 : Fin 7) ∈ (G.toRouting config).obstruction k :=
  (G.toRouting config).cleanCNL_mem k

/-- Routed to a non-CleanCNL class ⟹ that class was genuinely detected at the
start's lift state. -/
theorem toRouting_classify_mem_detect_of_ne_one (G : LiftObstructionGeometry)
    (config : ℕ → LiftState) {k : ℕ} (h : (G.toRouting config).classify k ≠ 1) :
    (G.toRouting config).classify k ∈ G.stateDetect (config k) := by
  have hmem := (G.toRouting config).classify_mem_obstruction k
  rw [toRouting_obstruction] at hmem
  rcases Finset.mem_insert.1 hmem with h1 | hd
  · exact absurd h1 h
  · exact hd

/-- **Clean catch-all characterisation.**  A start is routed to CleanCNL **iff**
the deep geometry detects no package obstruction at its lift state.  (Forward uses
the faithful `cleanCNL_not_detected` invariant to convert "no package class" into
"empty detection".) -/
theorem toRouting_classify_eq_one_iff (G : LiftObstructionGeometry)
    (config : ℕ → LiftState) (k : ℕ) :
    (G.toRouting config).classify k = 1 ↔ G.stateDetect (config k) = ∅ := by
  have hobs : (G.toRouting config).obstruction k
      = insert 1 (G.stateDetect (config k)) := rfl
  constructor
  · intro hcl
    obtain ⟨h6, h3, h0, h5, h4, h2⟩ :=
      j11Scan_eq_one_imp ((G.toRouting config).classify_eq_one_imp hcl)
    rw [hobs] at h6 h3 h0 h5 h4 h2
    have h1 := G.cleanCNL_not_detected (config k)
    rw [Finset.eq_empty_iff_forall_notMem]
    intro j hj
    have hcases : ∀ y : Fin 7,
        y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 := by decide
    rcases hcases j with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0 (Finset.mem_insert_of_mem hj)
    · exact h1 hj
    · exact h2 (Finset.mem_insert_of_mem hj)
    · exact h3 (Finset.mem_insert_of_mem hj)
    · exact h4 (Finset.mem_insert_of_mem hj)
    · exact h5 (Finset.mem_insert_of_mem hj)
    · exact h6 (Finset.mem_insert_of_mem hj)
  · intro h
    refine (G.toRouting config).classify_eq_cnl ?_ ?_ ?_ ?_ ?_ ?_ <;>
      rw [toRouting_obstruction, h]
    all_goals exact not_mem_insert_one (by decide) (Finset.notMem_empty _)

end LiftObstructionGeometry

/-! ## 7.  Per-class Boolean detectors (finest isolation of the primitive)

The detection geometry can be presented at its true granularity: one Boolean
detector per package class.  The six detectors `detects 0, detects 2, detects 3,
detects 4, detects 5, detects 6` are the individual pieces of deep K/L/N geometry
(the seventh slot, `detects 1`, is pinned to `false`: CleanCNL is never a detected
obstruction). -/

/-- **Per-class detection geometry (faithful primitive, finest form).**
`detects c s = true` means the class-`c` package obstruction is exposed at lift
state `s`.  CleanCNL (class `1`) is never a detected obstruction. -/
structure PackageDetector where
  /-- FAITHFUL PRIMITIVE — the per-class obstruction detector. -/
  detects : Fin 7 → LiftState → Bool
  /-- FAITHFUL invariant — CleanCNL is never itself detected. -/
  not_detects_cnl : ∀ s, detects 1 s = false

namespace PackageDetector

/-- The detected package obstructions of a lift state. -/
def stateDetect (P : PackageDetector) (s : LiftState) : Finset (Fin 7) :=
  Finset.univ.filter (fun c => P.detects c s = true)

@[simp] theorem mem_stateDetect (P : PackageDetector) {c : Fin 7} {s : LiftState} :
    c ∈ P.stateDetect s ↔ P.detects c s = true := by
  simp [stateDetect, Finset.mem_filter]

theorem cleanCNL_not_detected (P : PackageDetector) (s : LiftState) :
    (1 : Fin 7) ∉ P.stateDetect s := by
  rw [mem_stateDetect, P.not_detects_cnl s]
  decide

/-- Assemble the per-class detectors into a `LiftObstructionGeometry`. -/
def toGeometry (P : PackageDetector) : LiftObstructionGeometry where
  stateDetect := P.stateDetect
  cleanCNL_not_detected := P.cleanCNL_not_detected

@[simp] theorem toGeometry_stateDetect (P : PackageDetector) (s : LiftState) :
    P.toGeometry.stateDetect s = P.stateDetect s := rfl

/-- **Catch-all characterisation in detector form.**  A start is routed to
CleanCNL iff *no* package detector fires at its lift state. -/
theorem toGeometry_classify_eq_one_iff (P : PackageDetector)
    (config : ℕ → LiftState) (k : ℕ) :
    (P.toGeometry.toRouting config).classify k = 1 ↔
      ∀ c : Fin 7, P.detects c (config k) = false := by
  rw [LiftObstructionGeometry.toRouting_classify_eq_one_iff, toGeometry_stateDetect,
    Finset.eq_empty_iff_forall_notMem]
  refine forall_congr' (fun c => ?_)
  rw [mem_stateDetect]
  cases hb : P.detects c (config k) <;> simp

end PackageDetector

/-! ## 8.  Summary

`CarryPriorityRouting.ofDetect detect` is precisely the `routing` field expected
by `CarryPriorityRoutingCharge` (`CarryRouting.lean`): the J.1.1 first-obstruction
routing whose single remaining structural obligation — the exhaustiveness
primitive `cleanCNL_mem` — has been **discharged** here from the catch-all design.
The irreducible faithful primitive that remains is the obstruction-detection
geometry `stateDetect` / `detects` (which lift configurations are which package
class), supplied as data; and, as in `CarryRouting.lean`, the seven per-class mass
bounds. -/

end

end Erdos260
