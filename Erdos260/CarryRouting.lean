import Mathlib
import Erdos260.ChargeBridgeReduction

/-!
# Carry priority routing — the J.1.1 first-obstruction scan into the v5 seven charge classes

`ChargeBridgeReduction.lean` proves the *summation skeleton* of the central charge
bridge: for an **arbitrary** routing `route : ℕ → Fin 7` of the high-excess starts
into the seven v5 charge classes, mass is conserved
(`highExcessMass_eq_sum_routedClassMassOf`), the class fibres are disjoint and
exhaustive, and the bound bundle `RoutedHighExcessChargeDataOldRes` discharges the
augmented bridge `highExcessMass ≤ ClosurePhaseMass + oldResMass`.

What is missing there — and supplied here — is the **construction of the routing**
from carry data via the manuscript's **Lemma J.1.1 first-obstruction priority
scan** (`proof_v4_unconditional_clean_v5.tex`, §J.1.1), plus the **I.0 fibrewise
old/new split** that precedes it (§I.0).

## The faithful decomposition

Lemma J.1.1 (eq. after J.1.1) states: *for each fixed threshold `T`, every retained
event fibre belongs to **exactly one** of the classes*
`Old, DensePack, Progress/Endpoint, Run, ShortReturn, LongReturn, Residual,
TowerFE/EX, CleanCNL`, where `CleanCNL` is **deliberately last** (the catch-all of
fibres on which no obstruction occurs), and the assignment is the *first applicable
class in the priority scan* — "the order of the scan selects the first applicable
class, so two later descriptions of the same spatial event cannot reassign the
fibre.  Hence `Φ_T` is single-valued and exhaustive."

We model this **honestly** by separating the *geometry* from the *combinatorics*:

* **Faithful geometric primitive.**  The per-start **obstruction profile**
  `obstruction : ℕ → Finset (Fin 7)`: `obstruction k` is the set of charge-classes
  whose defining geometric obstruction (dense marker, run explanation, complete
  return, tower atom, old-residual leakage, …) is *exposed* at the high-excess
  start `k`.  **Detecting these obstructions is the deep K/L/N manuscript geometry;
  here it is supplied as data** (we do not, and cannot, fabricate it).  The only
  structural demand is the J.1.1 **exhaustiveness** primitive `cleanCNL_mem`:
  CleanCNL (class `1`) is always available as the last-resort class.

* **Genuinely-proved combinatorics.**  The classifier `classify` is then *defined*
  as the deterministic **first-obstruction priority scan** `j11Scan` over the J.1.1
  order — so "classify is the J.1.1 first-obstruction assignment" is a Lean
  *definition*, with single-valuedness, membership, exhaustiveness, and the full
  per-class first-obstruction characterisations proved as theorems
  (`j11Scan_eq_old`, …, `j11Scan_eq_cnl`).  For *any* total classifier the routed
  class fibres are disjoint and exhaustive and mass is conserved
  (`filter_route_disjoint`, `filter_route_biUnion`, conservation) — this is the
  genuine, provable content, proved here in full.

## What remains a faithful primitive

The constructor `CarryPriorityRoutingCharge.toRoutedHighExcessChargeDataOldRes`
makes the remaining obligations **explicit and minimal**: the routing (built above)
plus the **seven per-class mass bounds** — Chernoff (0), clean-CNL (1), DensePack
(3), the joint Tower+Return+Run TRT bound (2+4+5, Lemma N.24), and the old-residual
bound (6, Lemma L.6.4/L.6.5).  These per-class estimates are exactly the deep
L.2 / N.3.3 family/transcript dynamics and are carried as clearly-labelled
hypotheses, **not** proved here.

The I.0 old/new split (`OldNewSplit`) carries the **I.0d pointwise bound**
`E_old ≤ (1-η)Y` on new fibres as a faithful primitive, and the exhaustive/disjoint
partition `B_b = B_b^old ⊔ B_b^new` plus its mass split are proved as genuine
bookkeeping.

No `sorry`/`axiom`.  Only the conservation/partition combinatorics and the scan's
single-valuedness are proved; the geometric obstruction profile and the per-class
mass bounds are the (faithfully isolated) deep inputs.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The summation skeleton holds for ANY total classifier

These two lemmas are the genuine, provable content underlying J.1.1's
"single-valued and exhaustive": a routing is a *total function*, so its class
fibres are automatically pairwise disjoint and cover all starts.  They generalise
`routedClass_disjoint` / `routedClass_biUnion` (proved in `ChargeBridgeReduction`
only for the six-class `Fin 6` routing) to an arbitrary finite class type, hence
to the v5 seven-class `Fin 7` routing. -/

/-- **Disjointness for an arbitrary routing (faithful J.1.1 single-valuedness).**
Distinct routing classes own disjoint starts: a routing is a total function, so
its class fibres are automatically disjoint. -/
theorem filter_route_disjoint {ι : Type*} [DecidableEq ι]
    (S : Finset ℕ) (route : ℕ → ι) {i j : ι} (hij : i ≠ j) :
    Disjoint (S.filter fun k => route k = i) (S.filter fun k => route k = j) := by
  rw [Finset.disjoint_left]
  intro k hki hkj
  rw [Finset.mem_filter] at hki hkj
  exact hij (hki.2.symm.trans hkj.2)

/-- **Exhaustiveness for an arbitrary routing (faithful J.1.1 exhaustiveness).**
Every start lies in some routing class: the class fibres cover all of `S`. -/
theorem filter_route_biUnion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ℕ) (route : ℕ → ι) :
    ((Finset.univ : Finset ι).biUnion fun i => S.filter fun k => route k = i) = S := by
  ext k
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, hk, _⟩; exact hk
  · intro hk; exact ⟨route k, hk, rfl⟩

/-! ## 2.  The J.1.1 first-obstruction priority scan over `Fin 7`

The seven v5 charge classes are encoded as `Fin 7` exactly as in
`RoutedHighExcessChargeDataOldRes`:

```
0  Chernoff / shell-paid progress      3  DensePack          6  old-residual (Ω^oldres)
1  clean-CNL Kraft tail                 4  Return / endpoint / OLC leakage
2  Tower                                5  Run / variation-drop
```

`j11Scan` is the deterministic **first-obstruction priority scan** of Lemma J.1.1.
The scan order is the manuscript order: old-residual `≺` DensePack `≺`
progress/Chernoff `≺` Run `≺` Return `≺` Tower `≺` **CleanCNL (last)**.  It returns
the first class whose obstruction is exposed, modelling the single-valued scan
"the order of the scan selects the first applicable class". -/

/-- The Lemma J.1.1 first-obstruction priority scan over the seven v5 charge
classes.  `avail` is the obstruction profile (the exposed classes); the scan
returns the highest-priority exposed class, or `none` if `avail` is empty. -/
def j11Scan (avail : Finset (Fin 7)) : Option (Fin 7) :=
  if (6 : Fin 7) ∈ avail then some 6
  else if (3 : Fin 7) ∈ avail then some 3
  else if (0 : Fin 7) ∈ avail then some 0
  else if (5 : Fin 7) ∈ avail then some 5
  else if (4 : Fin 7) ∈ avail then some 4
  else if (2 : Fin 7) ∈ avail then some 2
  else if (1 : Fin 7) ∈ avail then some 1
  else none

/-- The selected class is genuinely exposed (the scan never invents an
obstruction). -/
theorem j11Scan_eq_some_mem {avail : Finset (Fin 7)} {i : Fin 7}
    (h : j11Scan avail = some i) : i ∈ avail := by
  unfold j11Scan at h
  split_ifs at h with h6 h3 h0 h5 h4 h2 h1 <;>
    (obtain rfl := Option.some.inj h; assumption)

/-- **Single-valuedness (faithful J.1.1).**  The scan returns at most one class. -/
theorem j11Scan_single_valued {avail : Finset (Fin 7)} {a b : Fin 7}
    (ha : j11Scan avail = some a) (hb : j11Scan avail = some b) : a = b := by
  rw [ha] at hb; exact Option.some.inj hb

/-- **Exhaustiveness (faithful J.1.1).**  Whenever CleanCNL (class `1`) is
available — which J.1.1 guarantees for every retained fibre — the scan succeeds. -/
theorem j11Scan_isSome_of_one_mem {avail : Finset (Fin 7)}
    (h : (1 : Fin 7) ∈ avail) : (j11Scan avail).isSome := by
  unfold j11Scan
  split_ifs <;> simp_all

/-! ### Per-class first-obstruction characterisations (faithful J.1.1 priority)

Each class is selected exactly when its obstruction is exposed and **no
higher-priority class is exposed** — the precise content of "the order of the scan
selects the first applicable class". -/

/-- Old-residual is highest priority. -/
theorem j11Scan_eq_old {avail : Finset (Fin 7)} (h6 : (6 : Fin 7) ∈ avail) :
    j11Scan avail = some 6 := by simp [j11Scan, h6]

/-- DensePack is selected when exposed and no old-residual is. -/
theorem j11Scan_eq_densePack {avail : Finset (Fin 7)}
    (h3 : (3 : Fin 7) ∈ avail) (h6 : (6 : Fin 7) ∉ avail) :
    j11Scan avail = some 3 := by simp [j11Scan, h3, h6]

/-- Progress/Chernoff is selected when exposed and no higher class is. -/
theorem j11Scan_eq_progress {avail : Finset (Fin 7)}
    (h0 : (0 : Fin 7) ∈ avail) (h6 : (6 : Fin 7) ∉ avail) (h3 : (3 : Fin 7) ∉ avail) :
    j11Scan avail = some 0 := by simp [j11Scan, h0, h6, h3]

/-- Run is selected when exposed and no higher class is. -/
theorem j11Scan_eq_run {avail : Finset (Fin 7)}
    (h5 : (5 : Fin 7) ∈ avail) (h6 : (6 : Fin 7) ∉ avail) (h3 : (3 : Fin 7) ∉ avail)
    (h0 : (0 : Fin 7) ∉ avail) :
    j11Scan avail = some 5 := by simp [j11Scan, h5, h6, h3, h0]

/-- Return is selected when exposed and no higher class is. -/
theorem j11Scan_eq_return {avail : Finset (Fin 7)}
    (h4 : (4 : Fin 7) ∈ avail) (h6 : (6 : Fin 7) ∉ avail) (h3 : (3 : Fin 7) ∉ avail)
    (h0 : (0 : Fin 7) ∉ avail) (h5 : (5 : Fin 7) ∉ avail) :
    j11Scan avail = some 4 := by simp [j11Scan, h4, h6, h3, h0, h5]

/-- Tower is selected when exposed and no higher class is. -/
theorem j11Scan_eq_tower {avail : Finset (Fin 7)}
    (h2 : (2 : Fin 7) ∈ avail) (h6 : (6 : Fin 7) ∉ avail) (h3 : (3 : Fin 7) ∉ avail)
    (h0 : (0 : Fin 7) ∉ avail) (h5 : (5 : Fin 7) ∉ avail) (h4 : (4 : Fin 7) ∉ avail) :
    j11Scan avail = some 2 := by simp [j11Scan, h2, h6, h3, h0, h5, h4]

/-- CleanCNL is the deliberately-last class: selected only when no package
obstruction is exposed. -/
theorem j11Scan_eq_cnl {avail : Finset (Fin 7)}
    (h1 : (1 : Fin 7) ∈ avail) (h6 : (6 : Fin 7) ∉ avail) (h3 : (3 : Fin 7) ∉ avail)
    (h0 : (0 : Fin 7) ∉ avail) (h5 : (5 : Fin 7) ∉ avail) (h4 : (4 : Fin 7) ∉ avail)
    (h2 : (2 : Fin 7) ∉ avail) :
    j11Scan avail = some 1 := by simp [j11Scan, h1, h6, h3, h0, h5, h4, h2]

/-! ## 3.  The faithful carry priority routing structure -/

/-- **The J.1.1 carry priority routing (faithful).**

The only data are the **faithful geometric primitive** `obstruction` — the per-start
exposed-obstruction profile, which the deep K/L/N geometry computes — and the
**faithful J.1.1 exhaustiveness primitive** `cleanCNL_mem`: CleanCNL (class `1`) is
always available as the last-resort class.  Everything else (the classifier and all
of its properties) is *derived*. -/
structure CarryPriorityRouting where
  /-- FAITHFUL GEOMETRIC PRIMITIVE — the per-start obstruction profile.
  `obstruction k` is the set of charge-classes whose defining geometric obstruction
  (dense marker, run explanation, complete return, tower atom, old-residual
  leakage, …) is exposed at the high-excess start `k`.  Computing it is the deep
  manuscript geometry; here it is data. -/
  obstruction : ℕ → Finset (Fin 7)
  /-- FAITHFUL PRIMITIVE (Lemma J.1.1 exhaustiveness) — CleanCNL (class `1`) is
  always available as the deliberately-last catch-all class. -/
  cleanCNL_mem : ∀ k, (1 : Fin 7) ∈ obstruction k

namespace CarryPriorityRouting

/-- **The per-start classifier `classify : ℕ → Fin 7` (the J.1.1 first-obstruction
assignment).**  Defined as the deterministic first-obstruction priority scan over
the obstruction profile, so "classify is the J.1.1 first-obstruction assignment" is
a definition, not an unverified primitive.  When the scan returns nothing (an empty
profile, excluded by `cleanCNL_mem`) it falls back to CleanCNL. -/
def classify (R : CarryPriorityRouting) : ℕ → Fin 7 :=
  fun k => (j11Scan (R.obstruction k)).getD 1

theorem classify_eq (R : CarryPriorityRouting) (k : ℕ) :
    R.classify k = (j11Scan (R.obstruction k)).getD 1 := rfl

/-- The class assigned to each start genuinely has an exposed obstruction: the
classifier never invents geometry. -/
theorem classify_mem_obstruction (R : CarryPriorityRouting) (k : ℕ) :
    R.classify k ∈ R.obstruction k := by
  rw [classify_eq]
  cases hscan : j11Scan (R.obstruction k) with
  | none => simpa using R.cleanCNL_mem k
  | some i => simpa using j11Scan_eq_some_mem hscan

/-! ### First-obstruction priority of the classifier (faithful J.1.1) -/

theorem classify_eq_old (R : CarryPriorityRouting) {k : ℕ}
    (h6 : (6 : Fin 7) ∈ R.obstruction k) : R.classify k = 6 := by
  simp [classify_eq, j11Scan_eq_old h6]

theorem classify_eq_densePack (R : CarryPriorityRouting) {k : ℕ}
    (h3 : (3 : Fin 7) ∈ R.obstruction k) (h6 : (6 : Fin 7) ∉ R.obstruction k) :
    R.classify k = 3 := by simp [classify_eq, j11Scan_eq_densePack h3 h6]

theorem classify_eq_progress (R : CarryPriorityRouting) {k : ℕ}
    (h0 : (0 : Fin 7) ∈ R.obstruction k) (h6 : (6 : Fin 7) ∉ R.obstruction k)
    (h3 : (3 : Fin 7) ∉ R.obstruction k) :
    R.classify k = 0 := by simp [classify_eq, j11Scan_eq_progress h0 h6 h3]

theorem classify_eq_run (R : CarryPriorityRouting) {k : ℕ}
    (h5 : (5 : Fin 7) ∈ R.obstruction k) (h6 : (6 : Fin 7) ∉ R.obstruction k)
    (h3 : (3 : Fin 7) ∉ R.obstruction k) (h0 : (0 : Fin 7) ∉ R.obstruction k) :
    R.classify k = 5 := by simp [classify_eq, j11Scan_eq_run h5 h6 h3 h0]

theorem classify_eq_return (R : CarryPriorityRouting) {k : ℕ}
    (h4 : (4 : Fin 7) ∈ R.obstruction k) (h6 : (6 : Fin 7) ∉ R.obstruction k)
    (h3 : (3 : Fin 7) ∉ R.obstruction k) (h0 : (0 : Fin 7) ∉ R.obstruction k)
    (h5 : (5 : Fin 7) ∉ R.obstruction k) :
    R.classify k = 4 := by simp [classify_eq, j11Scan_eq_return h4 h6 h3 h0 h5]

theorem classify_eq_tower (R : CarryPriorityRouting) {k : ℕ}
    (h2 : (2 : Fin 7) ∈ R.obstruction k) (h6 : (6 : Fin 7) ∉ R.obstruction k)
    (h3 : (3 : Fin 7) ∉ R.obstruction k) (h0 : (0 : Fin 7) ∉ R.obstruction k)
    (h5 : (5 : Fin 7) ∉ R.obstruction k) (h4 : (4 : Fin 7) ∉ R.obstruction k) :
    R.classify k = 2 := by simp [classify_eq, j11Scan_eq_tower h2 h6 h3 h0 h5 h4]

theorem classify_eq_cnl (R : CarryPriorityRouting) {k : ℕ}
    (h6 : (6 : Fin 7) ∉ R.obstruction k) (h3 : (3 : Fin 7) ∉ R.obstruction k)
    (h0 : (0 : Fin 7) ∉ R.obstruction k) (h5 : (5 : Fin 7) ∉ R.obstruction k)
    (h4 : (4 : Fin 7) ∉ R.obstruction k) (h2 : (2 : Fin 7) ∉ R.obstruction k) :
    R.classify k = 1 := by
  simp [classify_eq, j11Scan_eq_cnl (R.cleanCNL_mem k) h6 h3 h0 h5 h4 h2]

/-! ### The routing satisfies the J.1.1 partition (disjoint / exhaustive / conserving)

These hold for the routing `classify` exactly because they hold for *any* total
classifier (§1).  They are the genuine, provable content of Lemma J.1.1's
"single-valued and exhaustive priority map" together with the conservation half of
Phase D1. -/

/-- **J.1.1 disjointness for the carry routing.** -/
theorem routedClass_disjoint {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (R : CarryPriorityRouting)
    {i j : Fin 7} (hij : i ≠ j) :
    Disjoint
      ((highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y).filter (fun k => R.classify k = i))
      ((highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y).filter (fun k => R.classify k = j)) :=
  filter_route_disjoint _ R.classify hij

/-- **J.1.1 exhaustiveness for the carry routing.** -/
theorem routedClass_biUnion {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (R : CarryPriorityRouting) :
    ((Finset.univ : Finset (Fin 7)).biUnion fun i =>
        (highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y).filter (fun k => R.classify k = i))
      = highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y :=
  filter_route_biUnion _ R.classify

/-- **Mass conservation for the carry routing (Phase D1 conservation half).** -/
theorem highExcessMass_eq_sum_routedClassMass {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (R : CarryPriorityRouting) :
    highExcessMass (highExcessStarts carryData.starts (hitGap carryData.a)
        carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T
      = ∑ i : Fin 7, routedClassMassOf carryData R.classify i :=
  highExcessMass_eq_sum_routedClassMassOf carryData R.classify

end CarryPriorityRouting

/-! ## 4.  Constructor toward `RoutedHighExcessChargeDataOldRes`

The routing is now built and its partition/conservation properties are proved.
The only remaining obligations are the **seven per-class mass bounds**, which are
the deep L.2 / N.3.3 family/transcript dynamics.  This bundle records them as
clearly-labelled hypotheses and assembles the v5 seven-class charge data. -/

/-- **The carry priority routing together with its seven per-class mass bounds.**

The `routing` field is the genuinely-constructed J.1.1 first-obstruction routing of
§3.  The bound fields are the **faithful primitives that remain**: the three
separable per-class bounds (Chernoff `0`, clean-CNL `1`, DensePack `3`), the joint
Tower+Return+Run TRT bound (`2+4+5`, Lemma N.24), and the old-residual bound (`6`,
Lemma L.6.4/L.6.5).  None of these analytic estimates is proved here. -/
structure CarryPriorityRoutingCharge
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (oldResMass : ℝ) where
  /-- The J.1.1 first-obstruction routing constructed in §3. -/
  routing : CarryPriorityRouting
  /-- FAITHFUL PRIMITIVE — Chernoff / shell-paid progress bound (separable). -/
  hChernoff :
    routedClassMassOf carryData routing.classify 0 ≤ termChernoff phases.toClosurePhaseData
  /-- FAITHFUL PRIMITIVE — clean-CNL Kraft-tail bound (separable). -/
  hCnl :
    routedClassMassOf carryData routing.classify 1 ≤ termCnl phases.toClosurePhaseData
  /-- FAITHFUL PRIMITIVE — DensePack marker-mass bound (separable). -/
  hDensePack :
    routedClassMassOf carryData routing.classify 3 ≤ termDensePack phases.toClosurePhaseData
  /-- FAITHFUL PRIMITIVE — joint Tower+Return+Run TRT bound (Lemma N.24). -/
  hTRT :
    routedClassMassOf carryData routing.classify 2
        + routedClassMassOf carryData routing.classify 4
        + routedClassMassOf carryData routing.classify 5
      ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
        + termRun phases.toClosurePhaseData
  /-- FAITHFUL PRIMITIVE — old-residual leakage bound (Lemma L.6.4/L.6.5). -/
  hOldRes :
    routedClassMassOf carryData routing.classify 6 ≤ oldResMass

/-- **Assemble the v5 seven-class charge data from the constructed routing and the
seven per-class bounds.**  Packaging only: the routing comes from the J.1.1 scan of
§3 and the bounds are the faithful primitives. -/
def CarryPriorityRoutingCharge.toRoutedHighExcessChargeDataOldRes
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell cPr} {oldResMass : ℝ}
    (D : CarryPriorityRoutingCharge phases carryData oldResMass) :
    RoutedHighExcessChargeDataOldRes phases carryData oldResMass where
  route := D.routing.classify
  hChernoff := D.hChernoff
  hCnl := D.hCnl
  hDensePack := D.hDensePack
  hTRT := D.hTRT
  hOldRes := D.hOldRes

/-- **Capstone — the constructed routing discharges the augmented charge bridge.**
Combining §3's routing with the seven per-class bounds yields the v5 augmented
bridge `highExcessMass ≤ ClosurePhaseMass + oldResMass` (the `+OldRes` term of
recurrence I.11'). -/
theorem CarryPriorityRoutingCharge.highExcess_le_phaseMass_add_oldRes
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell cPr} {oldResMass : ℝ}
    (D : CarryPriorityRoutingCharge phases carryData oldResMass) :
    highExcessMass (highExcessStarts carryData.starts (hitGap carryData.a)
        carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T
      ≤ ClosurePhaseMass phases.toClosurePhaseData + oldResMass :=
  D.toRoutedHighExcessChargeDataOldRes.highExcess_le_phaseMass_add_oldRes

/-! ## 5.  The I.0 fibrewise old/new split (eqs I.0a–I.0d)

The old/new decision precedes the J.1.1 scan: each coarea branch's threshold
support `B_b` is split fibrewise into `B_b^old ⊔ B_b^new` (eq. I.0b), and the
package masses are formed **only over new fibres**.  On the new fibres the I.0d
pointwise bound `E_old ≤ (1-η)Y` holds (the very definition of `B_b^new`).

We model this at the level of the carry high-excess starts: `isOld` is the
fibrewise old/new decision, the I.0d bound is the **faithful primitive**
`newFibre_Eold_le`, and the exhaustive/disjoint partition with its mass split is
proved as genuine bookkeeping. -/

/-- **The I.0 fibrewise old/new split (faithful).**

`isOld k` is the I.0b old/new decision on the high-excess start `k`; `Eold k` is the
old-window excess `E_old = W_{k-m}^{(s-m)} - T`.  The single faithful primitive is
the **I.0d pointwise bound** on new fibres: `E_old ≤ (1-η)Y` (eq. I.0d / J.1old),
which is the definitional property of `B_b^new`. -/
structure OldNewSplit {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (η Y : ℝ) where
  /-- The I.0b fibrewise old/new decision on each high-excess start. -/
  isOld : ℕ → Bool
  /-- The old-window excess `E_old(k) = W_{k-m}^{(s-m)} - T`. -/
  Eold : ℕ → ℝ
  /-- FAITHFUL PRIMITIVE (eq. I.0d) — on each new high-excess fibre the old-window
  excess obeys `E_old ≤ (1-η)Y`. -/
  newFibre_Eold_le :
    ∀ k ∈ highExcessStarts carryData.starts (hitGap carryData.a)
        carryData.r carryData.T carryData.Y,
      isOld k = false → Eold k ≤ (1 - η) * Y

namespace OldNewSplit

variable {shell : FailingDyadicShell} {cPr η Y : ℝ}
    {carryData : CarryDataFromFailure shell cPr}

/-- The old high-excess fibres `B_b^old`. -/
def oldStarts (sp : OldNewSplit carryData η Y) : Finset ℕ :=
  (highExcessStarts carryData.starts (hitGap carryData.a)
      carryData.r carryData.T carryData.Y).filter (fun k => sp.isOld k = true)

/-- The new high-excess fibres `B_b^new` (on which all package masses are formed). -/
def newStarts (sp : OldNewSplit carryData η Y) : Finset ℕ :=
  (highExcessStarts carryData.starts (hitGap carryData.a)
      carryData.r carryData.T carryData.Y).filter (fun k => sp.isOld k = false)

/-- **I.0b disjointness:** old and new fibres are disjoint. -/
theorem old_new_disjoint (sp : OldNewSplit carryData η Y) :
    Disjoint sp.oldStarts sp.newStarts := by
  rw [Finset.disjoint_left]
  intro k hk hk'
  simp only [oldStarts, newStarts, Finset.mem_filter] at hk hk'
  rw [hk.2] at hk'
  exact Bool.noConfusion hk'.2

/-- **I.0b exhaustiveness:** `B_b = B_b^old ⊔ B_b^new`. -/
theorem old_new_union (sp : OldNewSplit carryData η Y) :
    sp.oldStarts ∪ sp.newStarts
      = highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y := by
  ext k
  simp only [oldStarts, newStarts, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk
  · intro hk
    by_cases h : sp.isOld k = true
    · exact Or.inl ⟨hk, h⟩
    · exact Or.inr ⟨hk, by simpa using h⟩

/-- **I.0b cardinality split.** -/
theorem old_new_card (sp : OldNewSplit carryData η Y) :
    sp.oldStarts.card + sp.newStarts.card
      = (highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y).card := by
  have h := Finset.card_union_of_disjoint sp.old_new_disjoint
  rw [sp.old_new_union] at h
  exact h.symm

/-- **I.0 high-excess mass split.**  The high-excess mass decomposes as old-fibre
mass plus new-fibre mass; only the new-fibre mass feeds the package sums (the old
mass is charged separately by Lemma I.0.1). -/
theorem highExcessMass_eq_old_add_new (sp : OldNewSplit carryData η Y) :
    highExcessMass (highExcessStarts carryData.starts (hitGap carryData.a)
        carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T
      = (∑ k ∈ sp.oldStarts,
            windowExcess (hitGap carryData.a) k carryData.r carryData.T)
        + (∑ k ∈ sp.newStarts,
            windowExcess (hitGap carryData.a) k carryData.r carryData.T) := by
  unfold highExcessMass
  rw [← sp.old_new_union, Finset.sum_union sp.old_new_disjoint]

end OldNewSplit

end

end Erdos260
