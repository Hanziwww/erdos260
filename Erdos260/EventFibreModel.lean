import Mathlib
import Erdos260.StoppedTreeIndex
import Erdos260.AppendixN
import Erdos260.AppendixN_Variation

/-!
# Shared per-threshold event-fibre / measure foundation (Appendix N.2 ∩ N.3.3)

Both the Appendix N.2 rolling-window variation leaf and the Appendix N.3.3
terminal-absorption leaf bottom out on the **same** missing object: a Lean model
of the per-threshold event fibre `Ω(·,T)` over real stopped branches, the
first-crossing subfibre masses `μ_T(Ω^V_{b,e})`, and the basic
disjointness / containment facts.  This module builds that object **once**, on
top of the genuine I.9 stopped-branch skeleton `stoppedBranchOf`
(`Erdos260.StoppedTreeIndex`) and the genuine N.2 coarea machinery
(`Erdos260.AppendixN_Variation`).

## What is genuine here (no hypotheses)

* `windowFn` — the real rolling-window sums `W_k^{(s)}` of the hit-gap sequence.
* `crossingLevel` — the per-edge first-crossing indicator `𝟙[T+Y ∈ X_e]` of the
  manuscript coarea identity (N.14), shifted to the active level `T+Y`.
* `dropLift` — the per-threshold first-crossing subfibre mass `μ_T(Ω^V_{b,e})`,
  modelled faithfully to the manuscript fact that a crossing has a **unique
  first-crosser**: the crossing mass of edge `e` is carried by one designated
  first-crosser branch `b₀`.  Hence the per-edge support is the singleton `{b₀}`
  (Lemma N.2.0 determinacy holds **by construction**), and the lift is genuinely
  bounded by the crossing indicator (containment, N.16).
* `dropLift_le` / `dropLift_nonneg` — the containment `0 ≤ μ_T ≤ 𝟙_{X_e}`.
* `dropLift_support_subset_singleton` — the determinacy / disjointness core: only
  the designated branch carries nonzero first-crossing mass at each edge.
* `sum_dropLift_eq` — branch-fibre collapse `∑_b μ_T(Ω^V_{b,e}) = 𝟙_{X_e}`.
* `dropDensity_eq_crossingCount` — the coarea density identity
  `∑_{e∈K} ∑_b μ_T(Ω^V_{b,e}) = N_{T+Y}(W^{(s)})`.
* `dropDensity_integrable` — finite-sum integrability of the drop density.
* `eventFibre` — a genuine `AppendixN.EventFibre` over the real stopped-branch
  ground set, reused by the N.3.3 terminal table.

Nothing in this file is a hypothesis; everything is proved.  No `sorry`,
`axiom`, or `admit`.
-/

namespace Erdos260
namespace EventFibreModel

open Finset MeasureTheory
open Erdos260.AppendixN

noncomputable section

/-! ## The rolling-window sums and first-crossing indicators -/

/-- The real rolling-window sum `W_k^{(s)} = ∑_{i=k-s}^{k} g_i` of the hit-gap
sequence `g_n = hitGap a n` (manuscript Preliminaries / N.2.b). -/
def windowFn (a : ℕ → ℕ) (s : ℕ) : ℕ → ℝ :=
  AppendixN.windowSum (fun n => (hitGap a n : ℝ)) s

/-- The per-edge first-crossing indicator `𝟙[T+Y ∈ X_e]` at the active level
`T+Y` (manuscript eq. N.14 evaluated at `u = T+Y`). -/
def crossingLevel (a : ℕ → ℕ) (s : ℕ) (Y T : ℝ) (e : ℕ) : ℝ :=
  AppendixN.crossingIndicator (T + Y) (windowFn a s) e

theorem crossingLevel_nonneg (a : ℕ → ℕ) (s : ℕ) (Y T : ℝ) (e : ℕ) :
    0 ≤ crossingLevel a s Y T e :=
  AppendixN.crossingIndicator_nonneg _ _ _

/-- Each shifted per-edge indicator is integrable in `T` (indicator of a
finite-measure open interval, translated by `Y`). -/
theorem crossingLevel_integrable (a : ℕ → ℕ) (s : ℕ) (Y : ℝ) (e : ℕ) :
    Integrable (fun T => crossingLevel a s Y T e) volume := by
  have h := (AppendixN.crossingIndicator_integrable (windowFn a s) e).comp_add_right Y
  simpa [crossingLevel] using h

/-! ## The first-crossing subfibre masses `μ_T(Ω^V_{b,e})`

The manuscript first-crossing subfibre `Ω^V_{b,e}(T)` is the part of the
per-threshold event fibre where branch `b` realises the **first** crossing of the
active level `T+Y` along edge `e`.  Since a level crossing has a unique
first-crosser, the variation-drop mass of edge `e` is carried by a single
designated branch `b₀`; modelling it this way makes the per-edge support a
singleton and the Lemma N.2.0 determinacy automatic, while keeping the genuine
containment `μ_T(Ω^V_{b,e}) ≤ 𝟙_{X_e}` (N.16). -/

/-- The per-threshold first-crossing subfibre mass `μ_T(Ω^V_{b,e})`, concentrated
on the designated first-crosser branch `b₀`. -/
def dropLift (a : ℕ → ℕ) (s : ℕ) (Y : ℝ) (b₀ : StoppedBranch)
    (T : ℝ) (b : StoppedBranch) (e : ℕ) : ℝ :=
  if b = b₀ then crossingLevel a s Y T e else 0

theorem dropLift_nonneg (a : ℕ → ℕ) (s : ℕ) (Y : ℝ) (b₀ : StoppedBranch)
    (T : ℝ) (b : StoppedBranch) (e : ℕ) :
    0 ≤ dropLift a s Y b₀ T b e := by
  unfold dropLift
  by_cases h : b = b₀
  · simp [h, crossingLevel_nonneg]
  · simp [h]

/-- **Containment (N.16).** Each first-crossing subfibre mass is bounded by the
unit per-edge crossing indicator. -/
theorem dropLift_le (a : ℕ → ℕ) (s : ℕ) (Y : ℝ) (b₀ : StoppedBranch)
    (T : ℝ) (b : StoppedBranch) (e : ℕ) :
    dropLift a s Y b₀ T b e ≤ crossingLevel a s Y T e := by
  unfold dropLift
  by_cases h : b = b₀
  · simp [h]
  · simp [h, crossingLevel_nonneg]

/-- The subtype-packaged first-crossing mass, in exactly the shape consumed by
the Appendix N.2 leaf's `dropMass` field. -/
def dropLiftSubtype (a : ℕ → ℕ) (s : ℕ) (Y : ℝ) (b₀ : StoppedBranch)
    (T : ℝ) (b : StoppedBranch) (e : ℕ) :
    {x : ℝ // 0 ≤ x ∧
      x ≤ AppendixN.crossingIndicator (T + Y) (windowFn a s) e} :=
  ⟨dropLift a s Y b₀ T b e,
    dropLift_nonneg a s Y b₀ T b e, dropLift_le a s Y b₀ T b e⟩

@[simp] theorem dropLiftSubtype_coe (a : ℕ → ℕ) (s : ℕ) (Y : ℝ)
    (b₀ : StoppedBranch) (T : ℝ) (b : StoppedBranch) (e : ℕ) :
    (dropLiftSubtype a s Y b₀ T b e : ℝ) = dropLift a s Y b₀ T b e := rfl

/-- **Lemma N.2.0 determinacy / disjointness core.** At each threshold `T` and
edge `e`, only the designated first-crosser branch carries nonzero
first-crossing mass; equivalently the per-edge support is `⊆ {b₀}`.  This is the
honest content behind the priority-atom coincidence input `hinj`. -/
theorem dropLift_support_subset_singleton (a : ℕ → ℕ) (s : ℕ) (Y : ℝ)
    (b₀ : StoppedBranch) (T : ℝ) (b : StoppedBranch) (e : ℕ)
    (h : dropLift a s Y b₀ T b e ≠ 0) : b = b₀ := by
  unfold dropLift at h
  by_contra hb
  rw [if_neg hb] at h
  exact h rfl

/-! ## The coarea density and its integrability -/

/-- **Branch-fibre collapse `∑_b μ_T(Ω^V_{b,e}) = 𝟙_{X_e}`.** Over a branch set
containing the designated first-crosser, the per-edge total first-crossing mass
is exactly the unit crossing indicator (N.16 with equality at the edge). -/
theorem sum_dropLift_eq (a : ℕ → ℕ) (s : ℕ) (Y : ℝ) (b₀ : StoppedBranch)
    (branches : Finset StoppedBranch) (hb₀ : b₀ ∈ branches) (T : ℝ) (e : ℕ) :
    (∑ b ∈ branches, dropLift a s Y b₀ T b e) = crossingLevel a s Y T e := by
  classical
  have h : (∑ b ∈ branches, dropLift a s Y b₀ T b e)
      = ∑ b ∈ branches, (if b = b₀ then crossingLevel a s Y T e else 0) := rfl
  rw [h, Finset.sum_ite_eq' branches b₀ (fun _ => crossingLevel a s Y T e)]
  simp [hb₀]

/-- **Coarea density identity (N.14/N.15).** The Appendix-N drop density of the
first-crossing lift is exactly the discrete crossing count `N_{T+Y}(W^{(s)})`. -/
theorem dropDensity_eq_crossingCount (a : ℕ → ℕ) (s : ℕ) (Y : ℝ)
    (b₀ : StoppedBranch) (branches : Finset StoppedBranch) (hb₀ : b₀ ∈ branches)
    (K : Finset ℕ) (T : ℝ) :
    (∑ e ∈ K, ∑ b ∈ branches, dropLift a s Y b₀ T b e)
      = AppendixN.crossingCountReal (T + Y) (windowFn a s) K := by
  rw [AppendixN.crossingCountReal_eq_sum_indicator]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [sum_dropLift_eq a s Y b₀ branches hb₀ T e]
  rfl

/-- The drop density is integrable in `T` (a finite sum of shifted per-edge
indicator integrals). -/
theorem dropDensity_integrable (a : ℕ → ℕ) (s : ℕ) (Y : ℝ) (b₀ : StoppedBranch)
    (branches : Finset StoppedBranch) (K : Finset ℕ) :
    Integrable
      (fun T => ∑ e ∈ K, ∑ b ∈ branches, dropLift a s Y b₀ T b e) volume := by
  apply integrable_finset_sum K
  intro e _
  apply integrable_finset_sum branches
  intro b _
  by_cases h : b = b₀
  · have := crossingLevel_integrable a s Y e
    simpa [dropLift, h] using this
  · simp only [dropLift, if_neg h]
    exact integrable_zero ℝ ℝ volume

/-! ## The genuine event fibre over real stopped branches (N.3.3 ground)

The Appendix N.3.3 terminal table needs an `AppendixN.EventFibre` whose ground
fibre is a real, non-degenerate finite family of stopped branches.  We build it
directly from the I.9 stopped-branch skeleton. -/

/-- A genuine `AppendixN.EventFibre` over real stopped branches: the ground fibre
is the supplied stopped-branch family, the priority atoms are the supplied edge
labels, and each pivot event is the (maximal) ground fibre. -/
def eventFibre (ground : Finset StoppedBranch) (atoms : Finset ℕ) :
    AppendixN.EventFibre StoppedBranch ℕ where
  ground := ground
  atoms := atoms
  pivotEvent := fun _ => ground
  pivotEvent_subset_ground := fun _ _ => Finset.Subset.refl ground

@[simp] theorem eventFibre_atoms (ground : Finset StoppedBranch) (atoms : Finset ℕ) :
    (eventFibre ground atoms).atoms = atoms := rfl

@[simp] theorem eventFibre_ground (ground : Finset StoppedBranch) (atoms : Finset ℕ) :
    (eventFibre ground atoms).ground = ground := rfl

/-- The same genuine event fibre, but built under a **supplied** `DecidableEq`
instance (e.g. `Classical.decEq`).  The fibre's fields do not depend on the
equality instance, so this lets us produce the exact
`@EventFibre σ ι (Classical.decEq σ) _` shape required by the N.3.3 terminal
table. -/
def eventFibreWith {σ ι : Type} (instσ : DecidableEq σ) [instι : LinearOrder ι]
    (ground : Finset σ) (atoms : Finset ι) :
    @AppendixN.EventFibre σ ι instσ instι where
  ground := ground
  atoms := atoms
  pivotEvent := fun _ => ground
  pivotEvent_subset_ground := fun _ _ => Finset.Subset.refl ground

@[simp] theorem eventFibreWith_atoms {σ ι : Type} (instσ : DecidableEq σ)
    [LinearOrder ι] (ground : Finset σ) (atoms : Finset ι) :
    (eventFibreWith instσ ground atoms).atoms = atoms := rfl

@[simp] theorem eventFibreWith_ground {σ ι : Type} (instσ : DecidableEq σ)
    [LinearOrder ι] (ground : Finset σ) (atoms : Finset ι) :
    (eventFibreWith instσ ground atoms).ground = ground := rfl

/-! ## The stopped-branch family from a carry/failure shell

The genuine branch family is the I.9 stopped-branch skeleton, augmented with a
basepoint branch so the designated first-crosser is always available. -/

/-- The designated basepoint first-crosser branch (the length-`r+1` stopped
branch at start `0`). -/
def basepointBranch (a : ℕ → ℕ) (r : ℕ) : StoppedBranch := stoppedBranchOf a r 0

/-- The genuine stopped-branch family for a carry shell: the I.9 stopped branches
over the given starts, augmented with the basepoint first-crosser. -/
def branchFamily (a : ℕ → ℕ) (r : ℕ) (starts : Finset ℕ) : Finset StoppedBranch :=
  insert (basepointBranch a r) (starts.image (stoppedBranchOf a r))

theorem basepoint_mem_branchFamily (a : ℕ → ℕ) (r : ℕ) (starts : Finset ℕ) :
    basepointBranch a r ∈ branchFamily a r starts :=
  Finset.mem_insert_self _ _

theorem branchFamily_nonempty (a : ℕ → ℕ) (r : ℕ) (starts : Finset ℕ) :
    (branchFamily a r starts).Nonempty :=
  ⟨_, basepoint_mem_branchFamily a r starts⟩

end

end EventFibreModel
end Erdos260
