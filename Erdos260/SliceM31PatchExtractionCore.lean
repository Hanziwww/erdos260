import Erdos260.SliceM31OverlapClosureCore

/-!
# Actual M.3.1 patch extraction

This file sharpens the Appendix M.3 complete-return placement residual without assuming
`CleanReturnPlacement` or `SliceCompleteReturns`.

The new primitive residual is an actual-word `AnchoredPatchFamily` together with the M.3.2 strict
orientation that every slice start lies before the common anchored core.  From this data, the
`CompleteReturnArm` fields of `AnchoredSurvivorFamily` are derived from the patch family's clean-arm
zero-run using `completeReturnArm_iff_zeroRun`.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-- The actual M.3.1/M.3.2 patch-extraction residual below `AnchoredSurvivorFamily`.

It packages a genuine `AnchoredPatchFamily` whose ambient word is the actual digit word `ctx.d`, plus
the strict M.3.2 orientation `x < datum.core.start`.  It does not assume the value-level placement. -/
structure AnchoredActualPatchExtraction (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ) where
  family : AnchoredPatchFamily ctx key y
  w_eq_actual : family.w = ctx.d
  start_lt_core : ∀ x ∈ olcSlice ctx key y, x < family.datum.core.start

namespace AnchoredActualPatchExtraction

/-- The extracted anchored core is nonempty. -/
theorem core_nonempty {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (A : AnchoredActualPatchExtraction ctx key y) :
    0 < A.family.datum.core.length :=
  lt_of_lt_of_le A.family.datum_pos A.family.datum.core_len_lower

/-- Every extracted arm reaches strictly past the anchored core start. -/
theorem core_lt_arm_stop {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (A : AnchoredActualPatchExtraction ctx key y) {x : ℕ} (hx : x ∈ olcSlice ctx key y) :
    A.family.datum.core.start < (A.family.armBlock x).stop := by
  have hcontains_patch := A.family.arm_contains_patch x hx
  have hcontains_core := (A.family.anchored_patch x hx).core_contains
  have hcore_in_arm : IntervalBlock.Contains (A.family.armBlock x) A.family.datum.core :=
    IntervalBlock.contains_trans hcontains_patch hcontains_core
  have hright :
      A.family.datum.core.start + A.family.datum.core.length ≤
        (A.family.armBlock x).stop := by
    simpa [IntervalBlock.stop] using hcore_in_arm.2
  have hpos := A.core_nonempty
  omega

/-- The open-interval clean arm gives a closed `CompleteReturnArm` up to `stop - 1`. -/
theorem arm_complete {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (A : AnchoredActualPatchExtraction ctx key y) {x : ℕ} (hx : x ∈ olcSlice ctx key y) :
    CompleteReturnArm ctx x ((A.family.armBlock x).stop - 1) := by
  have hlt_stop := A.core_lt_arm_stop hx
  have hstart := A.family.arm_start x hx
  have hlt_core := A.start_lt_core x hx
  have hxle : x ≤ (A.family.armBlock x).stop - 1 := by omega
  refine (completeReturnArm_iff_zeroRun ctx hxle).2 ?_
  intro j hj1 hj2
  exact A.family.clean_arm x hx j hj1 (by omega)

/-- Reinterpret patch validity over `family.w` as validity over the actual word `ctx.d`. -/
theorem anchored_patch_actual {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (A : AnchoredActualPatchExtraction ctx key y) {x : ℕ} (hx : x ∈ olcSlice ctx key y) :
    AnchoredSemiperiodicPatch A.family.datum ctx.d (A.family.patch x) := by
  rw [← A.w_eq_actual]
  exact A.family.anchored_patch x hx

end AnchoredActualPatchExtraction

/-- Construct the current survivor-family residual from actual patch extraction. -/
def AnchoredSurvivorFamily.ofActualPatchExtraction {ctx : ActualFailureContext} {key : ℕ → ℕ}
    {y : ℕ} (A : AnchoredActualPatchExtraction ctx key y) :
    AnchoredSurvivorFamily ctx key y where
  datum := A.family.datum
  patch := A.family.patch
  armBlock := A.family.armBlock
  datum_pos := A.family.datum_pos
  arm_start := A.family.arm_start
  arm_complete := fun x hx => A.arm_complete hx
  anchored_patch := fun x hx => A.anchored_patch_actual hx
  arm_contains_patch := A.family.arm_contains_patch
  start_lt_core := A.start_lt_core

/-- The primitive actual patch-extraction residual implies the survivor-family residual. -/
theorem nonempty_survivorFamily_of_actualPatchExtraction {ctx : ActualFailureContext} {key : ℕ → ℕ}
    {y : ℕ} (h : Nonempty (AnchoredActualPatchExtraction ctx key y)) :
    Nonempty (AnchoredSurvivorFamily ctx key y) :=
  h.elim (fun A => ⟨AnchoredSurvivorFamily.ofActualPatchExtraction A⟩)

/-- Actual patch extraction discharges the value placement through the survivor family. -/
theorem cleanReturnPlacement_of_actualPatchExtraction {ctx : ActualFailureContext} {key : ℕ → ℕ}
    {y : ℕ} (A : AnchoredActualPatchExtraction ctx key y) :
    CleanReturnPlacement ctx key y :=
  cleanReturnPlacement_of_survivorFamily (AnchoredSurvivorFamily.ofActualPatchExtraction A)

/-- Nonempty primitive actual patch extraction discharges `CleanReturnPlacement`. -/
theorem cleanReturnPlacement_of_nonempty_actualPatchExtraction {ctx : ActualFailureContext}
    {key : ℕ → ℕ} {y : ℕ} (h : Nonempty (AnchoredActualPatchExtraction ctx key y)) :
    CleanReturnPlacement ctx key y :=
  h.elim (fun A => cleanReturnPlacement_of_actualPatchExtraction A)

/-- Nonempty primitive actual patch extraction discharges `SliceCompleteReturns`. -/
theorem sliceCompleteReturns_of_nonempty_actualPatchExtraction {ctx : ActualFailureContext}
    {key : ℕ → ℕ} {y : ℕ} (h : Nonempty (AnchoredActualPatchExtraction ctx key y)) :
    SliceCompleteReturns ctx key y :=
  h.elim (fun A => sliceCompleteReturns_of_survivorFamily
    (AnchoredSurvivorFamily.ofActualPatchExtraction A))

/-- A survivor family forgets to the primitive actual patch-extraction residual. -/
def AnchoredActualPatchExtraction.ofSurvivorFamily {ctx : ActualFailureContext} {key : ℕ → ℕ}
    {y : ℕ} (S : AnchoredSurvivorFamily ctx key y) :
    AnchoredActualPatchExtraction ctx key y where
  family := AnchoredPatchFamily.ofSurvivorFamily S
  w_eq_actual := rfl
  start_lt_core := S.start_lt_core

/-- The primitive actual patch-extraction residual is equivalent to the current survivor-family
residual, but factors the inputs one layer lower: actual anchored patches plus M.3.2 strict
orientation, with complete-return arms derived from the clean-arm field. -/
theorem nonempty_actualPatchExtraction_iff_survivorFamily
    (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ) :
    Nonempty (AnchoredActualPatchExtraction ctx key y) ↔
      Nonempty (AnchoredSurvivorFamily ctx key y) :=
  ⟨nonempty_survivorFamily_of_actualPatchExtraction,
    fun h => h.elim (fun S => ⟨AnchoredActualPatchExtraction.ofSurvivorFamily S⟩)⟩

/-- The primitive residual fires the genuine M.3.1 overlap bound on actual-word patches. -/
theorem actualPatchExtraction_overlap_card {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (A : AnchoredActualPatchExtraction ctx key y) {x z : ℕ}
    (hx : x ∈ olcSlice ctx key y) (hz : z ∈ olcSlice ctx key y) :
    A.family.datum.lowerBound ≤
      ((A.family.patch x).block.points ∩ (A.family.patch z).block.points).card :=
  theoremM3_1_anchoredSemiperiodicOverlap
    (A.anchored_patch_actual hx) (A.anchored_patch_actual hz)

/-- The primitive residual validates each patch over the actual digit word. -/
theorem actualPatchExtraction_patch_anchored {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (A : AnchoredActualPatchExtraction ctx key y) {x : ℕ} (hx : x ∈ olcSlice ctx key y) :
    AnchoredSemiperiodicPatch A.family.datum ctx.d (A.family.patch x) :=
  A.anchored_patch_actual hx

/-- The primitive residual's ambient word is the actual digit word. -/
theorem actualPatchExtraction_w_eq_actual {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (A : AnchoredActualPatchExtraction ctx key y) :
    A.family.w = ctx.d :=
  A.w_eq_actual

/-- Status after this module. -/
def sliceM31PatchExtractionResiduals : List String :=
  [ "CLOSED (primitive residual introduced) - AnchoredActualPatchExtraction packages the actual-word " ++
      "M.3.1 AnchoredPatchFamily with w = ctx.d and the M.3.2 strict orientation x < datum.core.start. " ++
      "It does not assume CleanReturnPlacement or SliceCompleteReturns.",
    "CLOSED (survivor construction) - AnchoredSurvivorFamily.ofActualPatchExtraction derives the " ++
      "CompleteReturnArm field from the patch family's clean_arm via completeReturnArm_iff_zeroRun.",
    "CLOSED (residual relationship) - nonempty_actualPatchExtraction_iff_survivorFamily shows the " ++
      "current survivor-family residual is equivalent to actual anchored patch extraction with strict " ++
      "M.3.2 placement.",
    "OPEN (primitive remainder) - construct Nonempty (AnchoredActualPatchExtraction ctx key y) from " ++
      "upstream routed local geometry: actual surviving anchored patches on ctx.d plus M.3.2 strict " ++
      "core orientation." ]

theorem sliceM31PatchExtractionResiduals_nonempty :
    sliceM31PatchExtractionResiduals ≠ [] := by
  simp [sliceM31PatchExtractionResiduals]

#print axioms AnchoredActualPatchExtraction.core_nonempty
#print axioms AnchoredActualPatchExtraction.core_lt_arm_stop
#print axioms AnchoredActualPatchExtraction.arm_complete
#print axioms AnchoredActualPatchExtraction.anchored_patch_actual
#print axioms AnchoredSurvivorFamily.ofActualPatchExtraction
#print axioms nonempty_survivorFamily_of_actualPatchExtraction
#print axioms cleanReturnPlacement_of_actualPatchExtraction
#print axioms cleanReturnPlacement_of_nonempty_actualPatchExtraction
#print axioms sliceCompleteReturns_of_nonempty_actualPatchExtraction
#print axioms AnchoredActualPatchExtraction.ofSurvivorFamily
#print axioms nonempty_actualPatchExtraction_iff_survivorFamily
#print axioms actualPatchExtraction_overlap_card
#print axioms actualPatchExtraction_patch_anchored
#print axioms actualPatchExtraction_w_eq_actual

end

end Erdos260
