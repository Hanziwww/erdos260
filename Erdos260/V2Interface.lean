import Erdos260.CNL
import Erdos260.Ledger
import Erdos260.Pressure
import Erdos260.StoppedInduction

/-!
# proof_v2 auxiliary interface

This file names the five auxiliary estimates from Section 2 of `proof_v2.tex`.
It is only an interface vocabulary: no theorem in the final chain may assume an
inhabitant of `AuxiliaryEstimatesV2` unless the Appendix L proof constructs one.
-/

namespace Erdos260

open Finset

/-- The five auxiliary estimate propositions A1--A5 in Section 2 of `proof_v2.tex`. -/
structure AuxiliaryEstimateStatementsV2 where
  cnlSelector : Prop
  packageOutputMaps : Prop
  towerExcursion : Prop
  runTrichotomy : Prop
  thresholdDescent : Prop

/-- A proof package for the five auxiliary estimates once Appendix L is closed. -/
structure AuxiliaryEstimatesV2 (S : AuxiliaryEstimateStatementsV2) : Prop where
  cnlSelector : S.cnlSelector
  packageOutputMaps : S.packageOutputMaps
  towerExcursion : S.towerExcursion
  runTrichotomy : S.runTrichotomy
  thresholdDescent : S.thresholdDescent

theorem AuxiliaryEstimatesV2.cases {S : AuxiliaryEstimateStatementsV2}
    (h : AuxiliaryEstimatesV2 S) :
    S.cnlSelector ∧ S.packageOutputMaps ∧ S.towerExcursion ∧
      S.runTrichotomy ∧ S.thresholdDescent :=
  ⟨h.cnlSelector, h.packageOutputMaps, h.towerExcursion, h.runTrichotomy,
    h.thresholdDescent⟩

/-!
The following statements are the currently formalized finite skeleton of A1--A5.
They are not the final Appendix L estimates: the final estimates will strengthen
these propositions with the valuation, tower, run, and local closure content of
`proof_v2.tex`.
-/

/-- A1 skeleton: the canonical CNL selector is single-valued, exhaustive on a
nonempty available set, selects a priority-minimal available class, and admits
the finite selected-class encoding bounds used by clean CNL entropy. -/
def CNLSelectorSkeletonV2 : Prop :=
  (∀ {t : CNLTransition} {a b : CNLClass},
      canonicalCNLSelector t = some a ->
      canonicalCNLSelector t = some b ->
      a = b) ∧
    (∀ {t : CNLTransition}, t.available.Nonempty ->
      ∃ c : CNLClass, canonicalCNLSelector t = some c) ∧
    (∀ {t : CNLTransition} {c d : CNLClass},
      canonicalCNLSelector t = some c ->
      d ∈ t.available ->
      CNLClass.priorityRank c <= CNLClass.priorityRank d) ∧
    (∀ transitions : Finset CNLTransition,
      (selectedTransitions transitions).card <=
        ∑ cls : CNLClass, (transitionsSelectedAs transitions cls).card) ∧
    (∀ {β : Type} [DecidableEq β] (transitions : Finset CNLTransition)
        (code : CNLClass -> CNLTransition -> β)
        (codeBound fiberBound : CNLClass -> Nat),
      (∀ cls : CNLClass,
        ((transitionsSelectedAs transitions cls).image (code cls)).card <=
          codeBound cls) ->
      (∀ (cls : CNLClass) (y : β),
        y ∈ (transitionsSelectedAs transitions cls).image (code cls) ->
          ((transitionsSelectedAs transitions cls).filter
            fun t => code cls t = y).card <= fiberBound cls) ->
      (selectedTransitions transitions).card <=
        ∑ cls : CNLClass, codeBound cls * fiberBound cls)

/-- A2 skeleton: branch outputs are single-valued finite package outputs and
package costs sum over package/support/layer fibres and bound through charged
mass. -/
def PackageOutputMapsSkeletonV2 : Prop :=
  (∀ (branches : Finset StoppedBranch) (Φ : PriorityMap),
      (branchOutputs branches Φ).card <= branches.card) ∧
    (∀ (objects : Finset OutputObject) (cost : OutputObject -> ℝ),
      packageCost objects cost =
        ∑ kind : PackageKind, packageCost (outputsOf objects kind) cost) ∧
    (∀ (objects : Finset OutputObject) (cost : OutputObject -> ℝ),
      packageCost objects cost =
        ∑ supportId ∈ supportIds objects,
          packageCost (outputsWithSupport objects supportId) cost) ∧
    (∀ (objects : Finset OutputObject) (cost : OutputObject -> ℝ),
      packageCost objects cost =
        ∑ layer ∈ thresholdLayers objects,
          packageCost (outputsAtThreshold objects layer) cost) ∧
    (∀ {objects : Finset OutputObject} {cost weight : OutputObject -> ℝ}
        {Cmax : ℝ} {C : PackageKind -> ℝ},
      (∀ kind : PackageKind, C kind <= Cmax) ->
      (∀ o ∈ objects, 0 <= weight o) ->
      (∀ kind o, o ∈ outputsOf objects kind -> cost o <= C kind * weight o) ->
      packageCost objects cost <= Cmax * chargedMass objects weight)

/-- A3 skeleton: feedback packages in a branch-output family must raise the
threshold layer whenever `BranchOutputsFeedbackFree` holds. -/
def TowerExcursionSkeletonV2 : Prop :=
  ∀ {branches : Finset StoppedBranch} {Φ : PriorityMap}
      {kind : PackageKind} {j : Nat},
    BranchOutputsFeedbackFree branches Φ j ->
    IsFeedbackPackage kind ->
    ∀ {o : OutputObject}, o ∈ branchOutputsOf branches Φ kind ->
      j < o.thresholdLayer

/-- A4 skeleton: the same no-same-level feedback condition controls run outputs
because run is one of the feedback packages. -/
def RunTrichotomySkeletonV2 : Prop :=
  ∀ {branches : Finset StoppedBranch} {Φ : PriorityMap}
      {j : Nat} {o : OutputObject},
    BranchOutputsFeedbackFree branches Φ j ->
    o ∈ branchOutputsOf branches Φ PackageKind.runPkg ->
      j < o.thresholdLayer

/-- A5 skeleton: same-level Return/Run/Tower feedback is impossible under the
explicit feedback-free ledger predicate. -/
def ThresholdDescentSkeletonV2 : Prop :=
  ∀ {branches : Finset StoppedBranch} {Φ : PriorityMap}
      {j : Nat} {o : OutputObject},
    BranchOutputsFeedbackFree branches Φ j ->
    o ∈ branchOutputs branches Φ ->
    IsFeedbackPackage o.package ->
      o.thresholdLayer ≠ j

/-- The currently proved finite skeleton statements for A1--A5. -/
def auxiliaryEstimateSkeletonStatementsV2 : AuxiliaryEstimateStatementsV2 where
  cnlSelector := CNLSelectorSkeletonV2
  packageOutputMaps := PackageOutputMapsSkeletonV2
  towerExcursion := TowerExcursionSkeletonV2
  runTrichotomy := RunTrichotomySkeletonV2
  thresholdDescent := ThresholdDescentSkeletonV2

theorem CNLSelectorSkeletonV2_proved : CNLSelectorSkeletonV2 := by
  constructor
  · intro t a b ha hb
    exact canonicalCNLSelector_single_valued ha hb
  constructor
  · intro t ht
    exact exists_canonicalCNLSelector_eq_some_of_nonempty ht
  constructor
  · intro t c d hc hd
    exact canonicalCNLSelector_priorityRank_le_of_mem hc hd
  constructor
  · intro transitions
    exact selectedTransitions_card_le_sum_selectedAs transitions
  · intro β _ transitions code codeBound fiberBound hcodes hfiber
    exact selectedTransitions_card_le_sum_code_bounds
      transitions code hcodes hfiber

theorem PackageOutputMapsSkeletonV2_proved : PackageOutputMapsSkeletonV2 := by
  constructor
  · intro branches Φ
    exact branchOutputs_card_le branches Φ
  constructor
  · intro objects cost
    exact packageCost_eq_sum_outputsOf_univ objects cost
  constructor
  · intro objects cost
    exact packageCost_eq_sum_outputsWithSupport objects cost
  constructor
  · intro objects cost
    exact packageCost_eq_sum_outputsAtThreshold objects cost
  · intro objects cost weight Cmax C hC hweight hpoint
    exact packageCost_le_uniform_const_mul_chargedMass hC hweight hpoint

theorem TowerExcursionSkeletonV2_proved : TowerExcursionSkeletonV2 := by
  intro branches Φ kind j hfree hkind o ho
  exact branchFeedback_outputsOf_thresholdLayer_gt hfree hkind ho

theorem RunTrichotomySkeletonV2_proved : RunTrichotomySkeletonV2 := by
  intro branches Φ j o hfree ho
  exact branchFeedback_outputsOf_thresholdLayer_gt
    hfree (by simp [IsFeedbackPackage]) ho

theorem ThresholdDescentSkeletonV2_proved : ThresholdDescentSkeletonV2 := by
  intro branches Φ j o hfree ho hfeedback
  exact no_same_level_feedback_output hfree ho hfeedback

theorem AuxiliaryEstimatesV2_skeleton_proved :
    AuxiliaryEstimatesV2 auxiliaryEstimateSkeletonStatementsV2 where
  cnlSelector := CNLSelectorSkeletonV2_proved
  packageOutputMaps := PackageOutputMapsSkeletonV2_proved
  towerExcursion := TowerExcursionSkeletonV2_proved
  runTrichotomy := RunTrichotomySkeletonV2_proved
  thresholdDescent := ThresholdDescentSkeletonV2_proved

end Erdos260
