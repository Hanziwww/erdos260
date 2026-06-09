import Erdos260.SliceM31PatchExtractionCore

/-!
# Actual M.3.1 patch extraction from the factored arm/core overlap

This focused bridge keeps the Appendix M.3.1 residual below the survivor-family layer. It proves
direct conversions between the new `AnchoredActualPatchExtraction` residual and the older factored
`AnchoredArmCoreOverlap` witness, without routing through `CleanReturnPlacement`,
`SliceCompleteReturns`, or `AnchoredSurvivorFamily`.

The backward direction from an arm/core overlap uses the existing actual-word patch family
`AnchoredPatchFamily.ofArmCoreOverlap`: its ambient word is definitionally `ctx.d`, and the strict
orientation is exactly the `start_lt_core` field of the overlap datum. This is a formal residual
reduction, not a construction of genuine survivor patches from the M.2.1 counting layer.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-- The primitive patch-family witness underlying `AnchoredActualPatchExtraction`: one
`AnchoredPatchFamily` over the actual digit word, plus the strict M.3.2 orientation. -/
def AnchoredActualPatchFamilyWitness
    (ctx : ActualFailureContext) (key : Nat -> Nat) (y : Nat) : Prop :=
  Exists fun family : AnchoredPatchFamily ctx key y =>
    family.w = ctx.d /\ forall x, x ∈ olcSlice ctx key y -> x < family.datum.core.start

namespace AnchoredActualPatchExtraction

/-- Package an actual-word patch family with strict orientation as the primitive extraction residual. -/
def ofPatchFamily {ctx : ActualFailureContext} {key : Nat -> Nat} {y : Nat}
    (family : AnchoredPatchFamily ctx key y) (hw : family.w = ctx.d)
    (hstrict : forall x, x ∈ olcSlice ctx key y -> x < family.datum.core.start) :
    AnchoredActualPatchExtraction ctx key y where
  family := family
  w_eq_actual := hw
  start_lt_core := hstrict

/-- Build actual patch extraction directly from the factored M.1.1/M.3.1/M.3.2 arm/core overlap. -/
def ofArmCoreOverlap {ctx : ActualFailureContext} {key : Nat -> Nat} {y : Nat}
    (O : AnchoredArmCoreOverlap ctx key y) :
    AnchoredActualPatchExtraction ctx key y where
  family := AnchoredPatchFamily.ofArmCoreOverlap O
  w_eq_actual := rfl
  start_lt_core := O.start_lt_core

end AnchoredActualPatchExtraction

/-- Forget an actual extraction witness to its exact primitive patch-family existential. -/
theorem actualPatchExtraction_witness {ctx : ActualFailureContext} {key : Nat -> Nat} {y : Nat}
    (A : AnchoredActualPatchExtraction ctx key y) :
    AnchoredActualPatchFamilyWitness ctx key y :=
  ⟨A.family, A.w_eq_actual, A.start_lt_core⟩

/-- The new residual is definitionally the existence of one actual-word patch family plus strict
orientation. -/
theorem nonempty_actualPatchExtraction_iff_patchFamilyWitness
    (ctx : ActualFailureContext) (key : Nat -> Nat) (y : Nat) :
    Nonempty (AnchoredActualPatchExtraction ctx key y) <->
      AnchoredActualPatchFamilyWitness ctx key y :=
  ⟨fun h => h.elim actualPatchExtraction_witness,
    fun h => by
      rcases h with ⟨family, hw, hstrict⟩
      exact ⟨AnchoredActualPatchExtraction.ofPatchFamily family hw hstrict⟩⟩

/-- Extract the factored arm/core overlap directly from actual patch extraction. -/
def AnchoredArmCoreOverlap.ofActualPatchExtraction {ctx : ActualFailureContext} {key : Nat -> Nat}
    {y : Nat} (A : AnchoredActualPatchExtraction ctx key y) :
    AnchoredArmCoreOverlap ctx key y where
  armBlock := A.family.armBlock
  core := A.family.datum.core
  core_nonempty := A.core_nonempty
  arm_start := A.family.arm_start
  arm_complete := fun x hx => A.arm_complete hx
  start_lt_core := A.start_lt_core
  core_contained := fun x hx =>
    IntervalBlock.contains_trans (A.family.arm_contains_patch x hx)
      ((A.family.anchored_patch x hx).core_contains)

/-- The factored arm/core overlap residual implies the new actual patch-extraction residual, directly
and without passing through the survivor-family residual. -/
theorem nonempty_actualPatchExtraction_of_armCoreOverlap {ctx : ActualFailureContext}
    {key : Nat -> Nat} {y : Nat} (h : Nonempty (AnchoredArmCoreOverlap ctx key y)) :
    Nonempty (AnchoredActualPatchExtraction ctx key y) :=
  h.elim (fun O => ⟨AnchoredActualPatchExtraction.ofArmCoreOverlap O⟩)

/-- Actual patch extraction implies the factored arm/core overlap residual, directly and without using
`CleanReturnPlacement`, `SliceCompleteReturns`, or `AnchoredSurvivorFamily`. -/
theorem nonempty_armCoreOverlap_of_actualPatchExtraction {ctx : ActualFailureContext}
    {key : Nat -> Nat} {y : Nat} (h : Nonempty (AnchoredActualPatchExtraction ctx key y)) :
    Nonempty (AnchoredArmCoreOverlap ctx key y) :=
  h.elim (fun A => ⟨AnchoredArmCoreOverlap.ofActualPatchExtraction A⟩)

/-- Direct residual reduction: the new actual patch extraction is equivalent to the factored
M.1.1/M.3.1/M.3.2 arm/core overlap residual, with no survivor-family detour. -/
theorem nonempty_actualPatchExtraction_iff_armCoreOverlap
    (ctx : ActualFailureContext) (key : Nat -> Nat) (y : Nat) :
    Nonempty (AnchoredActualPatchExtraction ctx key y) <->
      Nonempty (AnchoredArmCoreOverlap ctx key y) :=
  ⟨nonempty_armCoreOverlap_of_actualPatchExtraction,
    nonempty_actualPatchExtraction_of_armCoreOverlap⟩

/-- Status after the direct arm/core bridge. -/
def sliceM31PatchExtractionFromArmCoreResiduals : List String :=
  [ "CLOSED (exact primitive witness) - nonempty_actualPatchExtraction_iff_patchFamilyWitness states " ++
      "the residual as exactly one actual-word AnchoredPatchFamily plus the strict M.3.2 orientation.",
    "CLOSED (direct arm/core bridge) - AnchoredActualPatchExtraction.ofArmCoreOverlap builds the new " ++
      "residual from AnchoredArmCoreOverlap without using CleanReturnPlacement, SliceCompleteReturns, " ++
      "or AnchoredSurvivorFamily.",
    "CLOSED (direct equivalence) - nonempty_actualPatchExtraction_iff_armCoreOverlap identifies the " ++
      "remaining M.3.1 extraction gap with the factored M.1.1/M.3.1/M.3.2 arm/core overlap residual.",
    "OPEN (primitive remainder) - construct Nonempty (AnchoredArmCoreOverlap ctx key y), or " ++
      "equivalently an actual AnchoredPatchFamily witness with strict orientation, from the routed " ++
      "OLC return-slice geometry. The existing M.2.1 counting/crossing-freeness layer supplies counts " ++
      "and zero-run consequences, but not a formal AnchoredFirstDirtyDatum/SemiperiodicBlock payload." ]

theorem sliceM31PatchExtractionFromArmCoreResiduals_nonempty :
    sliceM31PatchExtractionFromArmCoreResiduals ≠ [] := by
  simp [sliceM31PatchExtractionFromArmCoreResiduals]

#print axioms AnchoredActualPatchExtraction.ofPatchFamily
#print axioms AnchoredActualPatchExtraction.ofArmCoreOverlap
#print axioms actualPatchExtraction_witness
#print axioms nonempty_actualPatchExtraction_iff_patchFamilyWitness
#print axioms AnchoredArmCoreOverlap.ofActualPatchExtraction
#print axioms nonempty_actualPatchExtraction_of_armCoreOverlap
#print axioms nonempty_armCoreOverlap_of_actualPatchExtraction
#print axioms nonempty_actualPatchExtraction_iff_armCoreOverlap

end

end Erdos260
