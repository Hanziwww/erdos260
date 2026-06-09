import Mathlib
import Erdos260.GlobalCarryShellAssembly
import Erdos260.GlobalHighExcessAssembly
import Erdos260.StoppedTreeIndex
import Erdos260.AppendixI_PackageBounds
import Erdos260.AppendixI_PhaseMass
import Erdos260.AppendixNVariationLeafConstruction
import Erdos260.ShellPaidChernoffConstruction

/-!
# Certificate bounds for the global Appendix N closure

This module keeps the carry-side high-excess identity that is type-correct for
the concrete `StoppedBranch` family.  The previous attempted certificate lemma
compared `ClosurePhaseData.chernoff.paths`, whose path type is existentially
packaged by the phase, with the carry `Finset StoppedBranch`.  That is not a
valid boundary condition for the final proof: the Chernoff leaf itself must
expose a stopped-tree package whose concrete path type is `StoppedBranch`.
-/

namespace Erdos260

noncomputable section

theorem groundedHighExcessBranchMass_eq_highExcessMass
    {shell : FailingDyadicShell}
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr) :
    groundedHighExcessBranchMass carryData =
      highExcessMass
        (highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T := by
  calc
    groundedHighExcessBranchMass carryData
        = branchWeightedMass
            ((highExcessStarts carryData.starts (hitGap carryData.a)
                carryData.r carryData.T carryData.Y).image
              (stoppedBranchOf carryData.a carryData.r))
            (windowExcessWeight carryData.T) := rfl
    _ = highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T :=
        carryData.highExcessMass_eq_branchWeightedMass.symm

/-- A carry-aligned proof-v4 22.1A leaf has a concrete stopped-branch mass
bounded by the corresponding mass on the full carry stopped skeleton.

This is the type-correct boundary fact needed by the final Appendix N
certificate: it compares two `Finset StoppedBranch` families rather than an
existential path type from `ClosurePhaseData` with the carry family. -/
theorem carryStoppedBranchShellPaid22_1A_branchWeightedMass_le_carry
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      CarryStoppedBranchShellPaidChernoff22_1AInputData
        (cStar := cStar) (xi := xi) carryData) :
    branchWeightedMass data.paths (fun b => (data.weight b : Real)) <=
      branchWeightedMass carryData.stoppedBranches
        (fun b => (data.weight b : Real)) := by
  exact branchWeightedMass_mono_subset data.paths_subset_carry
    (by
      intro b _hb
      exact (data.weight b).property)

/-- The finite layer-cake 22.1A provider carries the same stopped-branch
monotonicity before projection to the carry-specific Chernoff leaf. -/
theorem carryStoppedBranchShellPaid22_1AAreaLayer_branchWeightedMass_le_carry
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      CarryStoppedBranchShellPaidChernoff22_1AAreaLayerSumInputData
        (cStar := cStar) (xi := xi) carryData) :
    branchWeightedMass data.paths (fun b => (data.weight b : Real)) <=
      branchWeightedMass carryData.stoppedBranches
        (fun b => (data.weight b : Real)) := by
  exact branchWeightedMass_mono_subset data.paths_subset_carry
    (by
      intro b _hb
      exact (data.weight b).property)

/-- Boundary obligations that must be supplied before a no-input global
certificate can relate Appendix N terminal mass to the Chernoff phase. -/
def appendixNCertificateBoundaryOpenItems : List String :=
  [ "Chernoff leaf must be a concrete StoppedBranch stopped-tree family; use CarryStoppedBranchShellPaidChernoff22_1AInputData / shellPaidChernoff22_1AFromCarryStoppedBranchAreaLayerSum once the proof-v4 22.1A data are built; carryStoppedBranchShellPaid22_1A_branchWeightedMass_le_carry supplies the stopped-family mass monotonicity on the concrete carry skeleton.",
    "Closure phase must be built from that leaf, not from the empty Chernoff package.",
    "Terminal N.3.3 must consume the proof-v4 routing table, five-class bounds, and L.6-backed bounded class." ]

theorem appendixNCertificateBoundaryOpenItems_nonempty :
    appendixNCertificateBoundaryOpenItems = [] -> False := by
  intro h
  simp [appendixNCertificateBoundaryOpenItems] at h

end

end Erdos260
