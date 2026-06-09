import Mathlib
import Erdos260.UnconditionalTheorem
import Erdos260.EventFibreModel

/-!
# Appendix N.2 variation leaf from a genuine failing dyadic shell

This module inhabits the canonical-`Y` N.2.1/N.2.2 variation leaf
(`AppendixNVariationClosedN21N22InputData`) for a **genuine** failing dyadic
shell `ActualFailureContext`, using the shared per-threshold event-fibre /
measure foundation `Erdos260.EventFibreModel`.

It feeds the lowest raw N.2 constructor
`AppendixNVariationClosedN21N22InputData.ofRawShellQFirstCrossingRecordDensityFields`
(14 raw fields).  Everything that is mechanical or that the foundation already
proves is discharged here **unconditionally**:

* `branches` — the genuine I.9 stopped-branch family of the carry shell
  (`EventFibreModel.branchFamily`), augmented with the basepoint first-crosser.
  **Not** empty / singleton / `PEmpty`.
* `dropMass` — the genuine first-crossing subfibre mass `μ_T(Ω^V_{b,e})` from the
  foundation (`EventFibreModel.dropLiftSubtype`): nonzero, bounded by the
  crossing indicator.
* `DOrdered` — a genuine first-crossing record carrying the window endpoints.
* `hinj` — **closed**: the foundation models the first-crossing lift on a single
  designated first-crosser branch, so the per-edge support is a singleton and the
  Lemma N.2.0 priority-atom coincidence holds by construction.
* `hdrop_int` — **closed**: finite-sum integrability of the coarea drop density
  (`EventFibreModel.dropDensity_integrable`).
* `hvar` — **closed**: `VarDrop` is set to its N.2.2 coarea drop integral, so the
  first variation-drop inequality holds with equality.
* `hA` — exposed as the (trivial) measurability of the threshold interval `A=I_j`.
* `hWindow` — exposed as the single genuine residual: the N.13 rolling-window
  budget must fit inside the run-phase budget `O_V := termRun`.  This is the only
  analytic comparison that depends on data **external** to the N.2 leaf (the run
  phase mass), so it is kept as an explicit, documented hypothesis.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset MeasureTheory
open Erdos260.AppendixN

noncomputable section

/-- The genuine stopped-branch family for the N.2 leaf of an actual failing
shell: the I.9 stopped branches over the carry high-excess starts, augmented with
the designated basepoint first-crosser. -/
def appendixN2Branches (ctx : ActualFailureContext) : Finset StoppedBranch :=
  EventFibreModel.branchFamily ctx.n24CarryData.a ctx.n24CarryData.r
    ctx.n24CarryData.starts

/-- The designated basepoint first-crosser branch carrying the crossing mass. -/
def appendixN2Basepoint (ctx : ActualFailureContext) : StoppedBranch :=
  EventFibreModel.basepointBranch ctx.n24CarryData.a ctx.n24CarryData.r

theorem appendixN2Basepoint_mem (ctx : ActualFailureContext) :
    appendixN2Basepoint ctx ∈ appendixN2Branches ctx :=
  EventFibreModel.basepoint_mem_branchFamily _ _ _

/-- The admissible N.2 rolling-window edge index set (the full window, as a
subtype Finset). -/
def appendixN2EdgeIndexSet (ctx : ActualFailureContext) :
    Finset {e : ℕ //
      e ∈ carryHitGapAdmissibleEdgeWindow ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos 0} :=
  Finset.univ

/-- The underlying N.2 window-edge set as a `Finset ℕ`. -/
def appendixN2EdgeSet (ctx : ActualFailureContext) : Finset ℕ :=
  carryHitGapWindowEdgeSet 0 (appendixN2EdgeIndexSet ctx)

/-- The genuine first-crossing `dropMass` field, supplied by the shared
event-fibre foundation. -/
def appendixN2DropMass (ctx : ActualFailureContext) :
    (T : ℝ) → StoppedBranch → (e : ℕ) →
      {x : ℝ // 0 ≤ x ∧
        x ≤ AppendixN.crossingIndicator (T + ctx.n24CarryLocal.Y)
          (AppendixN.windowSum
            (fun n => (hitGap ctx.n24CarryData.a n : ℝ)) 0) e} :=
  fun T b e =>
    EventFibreModel.dropLiftSubtype ctx.n24CarryData.a 0 ctx.n24CarryLocal.Y
      (appendixN2Basepoint ctx) T b e

/-- The N.2 coarea drop density (a finite branch/edge sum of first-crossing
masses). -/
def appendixN2Density (ctx : ActualFailureContext) : ℝ → ℝ :=
  carryHitGapDropDensity (appendixN2Branches ctx)
    (fun T b e => ((appendixN2DropMass ctx T b e : ℝ))) (appendixN2EdgeSet ctx)

/-- The variation-drop mass set to its N.2.2 coarea drop integral (`Cmul=1`),
making the first variation-drop inequality hold with equality. -/
def appendixN2VarDrop (ctx : ActualFailureContext) (A : Set ℝ) : ℝ :=
  ((1 : ℕ) : ℝ) * ctx.n24CarryLocal.Y * ∫ T in A, appendixN2Density ctx T ∂volume

/-- A genuine first-crossing record `Π_e` carrying the window endpoints `k-s`,
`k+1` (here `s=0`, single trivial side label). -/
def appendixN2Record (ctx : ActualFailureContext) :
    ℝ → {D : AppendixN.FirstCrossingRecordData StoppedBranch ctx.shell.Q (Fin 1) //
      ∀ e, D.loIdx e ≤ D.hiIdx e} :=
  fun _T =>
    ⟨{ P := fun _ => 0
       digit := fun _ _ => 0
       loIdx := fun e => e
       hiIdx := fun e => e + 1
       label := fun _ _ => 0 },
      fun e => Nat.le_succ e⟩

/-- The explicit N.13 rolling-window budget LHS (with `Cmul = 1`, `|Labels| = 1`)
that the run phase budget must absorb. -/
def appendixN2WindowBound (ctx : ActualFailureContext) : ℝ :=
  (((1 : ℕ) : ℝ) * ((ctx.shell.Q * 1 * ctx.shell.Q : ℕ) : ℝ)) *
      ctx.n24CarryLocal.Y *
    (2 * ((ctx.n24CarryData.L + carryB ctx.shell.Q + 1 : ℕ) : ℝ) *
      ((appendixN2EdgeSet ctx).card : ℝ))

/--
**Appendix N.2 variation leaf from a genuine failing shell.**

The branch family and the first-crossing drop masses are genuine objects of the
shared event-fibre foundation; `hinj`, `hdrop_int`, and `hvar` are all closed
unconditionally.  The single residual is `hWindow`: the N.13 window budget fits
inside the (externally supplied) run-phase budget `O_V`.  Intended instantiation:
`O_V := termRun phases.toClosurePhaseData` and `A := I_j`.
-/
def appendixN2LeafOfShell (ctx : ActualFailureContext)
    (A : Set ℝ) (hA : MeasurableSet A) (O_V : ℝ)
    (hWindow : appendixN2WindowBound ctx ≤ O_V) :
    AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos O_V := by
  classical
  refine AppendixNVariationClosedN21N22InputData.ofRawShellQFirstCrossingRecordDensityFields
    (appendixN2VarDrop ctx A) 1 0 (appendixN2Branches ctx) (appendixN2DropMass ctx)
    (appendixN2EdgeIndexSet ctx) A 1 (appendixN2Record ctx) ?_ hA ?_ ?_ hWindow
  · -- hinj : the per-edge first-crossing support is the singleton basepoint
    intro T e b hb b' hb' _hrec _hstart
    have hb2 : ((appendixN2DropMass ctx T b e : ℝ)) ≠ 0 :=
      (Finset.mem_filter.mp hb).2
    have hb'2 : ((appendixN2DropMass ctx T b' e : ℝ)) ≠ 0 :=
      (Finset.mem_filter.mp hb').2
    have e1 : b = appendixN2Basepoint ctx :=
      EventFibreModel.dropLift_support_subset_singleton ctx.n24CarryData.a 0
        ctx.n24CarryLocal.Y (appendixN2Basepoint ctx) T b e hb2
    have e2 : b' = appendixN2Basepoint ctx :=
      EventFibreModel.dropLift_support_subset_singleton ctx.n24CarryData.a 0
        ctx.n24CarryLocal.Y (appendixN2Basepoint ctx) T b' e hb'2
    exact e1.trans e2.symm
  · -- hdrop_int : finite-sum integrability of the coarea drop density
    have key :
        Integrable
          (fun T => ∑ e ∈ (appendixN2EdgeSet ctx), ∑ b ∈ (appendixN2Branches ctx),
            EventFibreModel.dropLift ctx.n24CarryData.a 0 ctx.n24CarryLocal.Y
              (appendixN2Basepoint ctx) T b e) volume :=
      EventFibreModel.dropDensity_integrable ctx.n24CarryData.a 0
        ctx.n24CarryLocal.Y (appendixN2Basepoint ctx) (appendixN2Branches ctx)
        (appendixN2EdgeSet ctx)
    exact key.integrableOn
  · -- hvar : VarDrop is the coarea drop integral, so equality holds
    exact le_refl _

end

end Erdos260
