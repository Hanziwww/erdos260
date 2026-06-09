import Mathlib
import Erdos260.GlobalCNLAssembly
import Erdos260.GlobalCarryShellAssembly
import Erdos260.CNLEntropy
import Erdos260.CNL
import Erdos260.Constants

/-!
# L.1.2/G.35 weighted-Kraft CNL leaf construction
-/

namespace Erdos260

open Finset

noncomputable section

/-- Identity constructor for the direct proof-v4 L.1.2 weighted-Kraft shell
leaf.  Use this when the selected-transition family, BND heights, Kraft bound,
and scalar shell budget have already been constructed. -/
def cnlStandardWeightedKraftShellFromInput
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellInputData shell cStar xi) :
    CNLStandardWeightedKraftShellInputData shell cStar xi :=
  data

/-- Identity constructor for the stronger proof-object CNL leaf consumed by
the preferred strict Appendix N endpoint. -/
def cnlStandardWeightedKraftShellProofFromInput
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellProofInputData shell cStar xi) :
    CNLStandardWeightedKraftShellProofInputData shell cStar xi :=
  data

namespace CNLStandardWeightedKraftShellInputData

/-- Build the direct shell-tied L.1.2/G.35 CNL leaf from the boxed
weighted-Kraft conclusion and the X-free shell/interval budget. -/
def ofWeightedKraft
    {shell : FailingDyadicShell} {cStar xi : Real}
    (transitions : Finset CNLTransition)
    (BNDHeightNat : CNLTransition -> Nat)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (kraftSum_le :
      cleanCNLKraftSum
          (selectedTransitions transitions) (fun t => (BNDHeightNat t : Real))
          (1 : Real) <=
        (2 : Real) ^ M)
    (scalar_budget :
      (2 : Real) ^ M * (shellFactor : Real) * (Ij : Real) <=
        cStar * xi / 6) :
    CNLStandardWeightedKraftShellInputData shell cStar xi where
  transitions := transitions
  BNDHeightNat := BNDHeightNat
  M := M
  shellFactor := shellFactor
  Ij := Ij
  kraftSum_le := kraftSum_le
  scalar_budget := scalar_budget

/-- Build the direct shell-tied L.1.2/G.35 CNL leaf when the manuscript scalar
budget is first proved with the shell-size factor still attached. -/
def ofWeightedKraftManuscriptBudget
    {shell : FailingDyadicShell} {cStar xi : Real}
    (transitions : Finset CNLTransition)
    (BNDHeightNat : CNLTransition -> Nat)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (kraftSum_le :
      cleanCNLKraftSum
          (selectedTransitions transitions) (fun t => (BNDHeightNat t : Real))
          (1 : Real) <=
        (2 : Real) ^ M)
    (manuscript_budget :
      (2 : Real) ^ M * (shellFactor : Real) * (shell.X : Real) *
          (Ij : Real) <=
        cStar * xi * (shell.X : Real) / 6) :
    CNLStandardWeightedKraftShellInputData shell cStar xi :=
  let data : CNLStandardWeightedKraftShellManuscriptInputData shell cStar xi := {
    transitions := transitions
    BNDHeightNat := BNDHeightNat
    M := M
    shellFactor := shellFactor
    Ij := Ij
    kraftSum_le := kraftSum_le
    manuscript_budget := manuscript_budget }
  data.toCNLStandardWeightedKraftShellInputData

end CNLStandardWeightedKraftShellInputData

/-- Public direct route from raw proof-v4 L.1.2/G.35 weighted-Kraft data to the
direct CNL shell leaf. -/
def cnlStandardWeightedKraftShellFromRawWeightedKraft
    {shell : FailingDyadicShell} {cStar xi : Real}
    (transitions : Finset CNLTransition)
    (BNDHeightNat : CNLTransition -> Nat)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (kraftSum_le :
      cleanCNLKraftSum
          (selectedTransitions transitions) (fun t => (BNDHeightNat t : Real))
          (1 : Real) <=
        (2 : Real) ^ M)
    (scalar_budget :
      (2 : Real) ^ M * (shellFactor : Real) * (Ij : Real) <=
        cStar * xi / 6) :
    CNLStandardWeightedKraftShellInputData shell cStar xi :=
  CNLStandardWeightedKraftShellInputData.ofWeightedKraft
    transitions BNDHeightNat M shellFactor Ij kraftSum_le scalar_budget

/-- Public direct route from raw proof-v4 L.1.2/G.35 weighted-Kraft data whose
shell/interval budget is still in the manuscript shell-size form. -/
def cnlStandardWeightedKraftShellFromRawWeightedKraftManuscriptBudget
    {shell : FailingDyadicShell} {cStar xi : Real}
    (transitions : Finset CNLTransition)
    (BNDHeightNat : CNLTransition -> Nat)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (kraftSum_le :
      cleanCNLKraftSum
          (selectedTransitions transitions) (fun t => (BNDHeightNat t : Real))
          (1 : Real) <=
        (2 : Real) ^ M)
    (manuscript_budget :
      (2 : Real) ^ M * (shellFactor : Real) * (shell.X : Real) *
          (Ij : Real) <=
        cStar * xi * (shell.X : Real) / 6) :
    CNLStandardWeightedKraftShellInputData shell cStar xi :=
  CNLStandardWeightedKraftShellInputData.ofWeightedKraftManuscriptBudget
    transitions BNDHeightNat M shellFactor Ij kraftSum_le manuscript_budget

/--
Proof-v4 L.1.2/G.35 construction route for the CNL leaf.

The real CNL leaf should be produced from a shell-tied Nat-height code/fibre
certificate: selected clean transitions, BND heights, class code bounds, fibre
bounds, the global Nat budget, and the scalar shell budget.  This projection is
one endpoint shape consumed by the fully separated Appendix N interface.  When
proof_v4's boxed G.35 weighted-Kraft inequality has already been proved, use
`cnlStandardWeightedKraftShellFromRawWeightedKraft` instead.
-/
def cnlStandardWeightedKraftShellFromNatBudget
    {shell : FailingDyadicShell}
    (data :
      CNLStandardNatHeightCodeBoundsNatBudgetShellInputData shell
        erdos260Constants.cStar erdos260Constants.ξ) :
    CNLStandardWeightedKraftShellInputData shell
      erdos260Constants.cStar erdos260Constants.ξ :=
  data.toCNLStandardWeightedKraftShellInputData

/-- Route from the shell-tied L.1.2 code/fibre Nat-budget certificate to the
direct weighted-Kraft shell leaf.

This is the manuscript-facing selected-family route: the provider supplies the
surviving CNL transitions, Nat-valued BND heights, class-local code/fibre
bounds, the Nat product budget, and the scalar G.35 shell budget. -/
def cnlStandardWeightedKraftShellFromCodeFibreNatBudgetShell
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data :
      CNLStandardNatHeightCodeBoundsNatBudgetShellInputData shell cStar xi) :
    CNLStandardWeightedKraftShellInputData shell cStar xi :=
  data.toCNLStandardWeightedKraftShellInputData

namespace CNLStandardNatHeightCodeBoundsNatBudgetShellInputData

/-- Build the shell-tied direct L.1.2/G.35 CNL provider from the raw
selected-transition code/fibre Nat-budget data.

The caller supplies the surviving selected-transition family, Nat BND heights,
class-local code and fibre bounds, the global Nat product budget, and the
scalar shell budget.  Nonnegativity of the shell size is supplied internally by
the shell-tied projection. -/
def ofCodeFibreNatBudget
    {shell : FailingDyadicShell} {cStar xi : Real}
    {Code : Type} [DecidableEq Code]
    (transitions : Finset CNLTransition)
    (BNDHeightNat : CNLTransition -> Nat)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (code : CNLClass -> CNLTransition -> Code)
    (codeBound fiberBound : CNLClass -> Nat)
    (hcodes :
      forall cls : CNLClass,
        ((transitionsSelectedAs transitions cls).image (code cls)).card <=
          codeBound cls)
    (hfiber :
      forall (cls : CNLClass) (y : Code),
        y ∈ (transitionsSelectedAs transitions cls).image (code cls) ->
          ((transitionsSelectedAs transitions cls).filter
            fun t => code cls t = y).card <= fiberBound cls)
    (hcodeSumNat :
      (Finset.univ.sum fun cls : CNLClass => codeBound cls * fiberBound cls) <=
        2 ^ M)
    (scalar_budget :
      (2 : Real) ^ M * (shellFactor : Real) * (Ij : Real) <=
        cStar * xi / 6) :
    CNLStandardNatHeightCodeBoundsNatBudgetShellInputData shell cStar xi where
  Code := Code
  decCode := inferInstance
  transitions := transitions
  BNDHeightNat := BNDHeightNat
  M := M
  shellFactor := shellFactor
  Ij := Ij
  code := code
  codeBound := codeBound
  fiberBound := fiberBound
  hcodes := hcodes
  hfiber := hfiber
  hcodeSumNat := hcodeSumNat
  scalar_budget := scalar_budget

/-- Build the shell-tied direct L.1.2/G.35 CNL provider from raw code/fibre
Nat-budget data while choosing code-label equality internally.

This mirrors the manuscript situation: the code labels are part of the local
encoding certificate, so the final provider should not have to expose a
separate decidable-equality instance. -/
def ofClassicalCodeFibreNatBudget
    {shell : FailingDyadicShell} {cStar xi : Real}
    {Code : Type}
    (transitions : Finset CNLTransition)
    (BNDHeightNat : CNLTransition -> Nat)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (code : CNLClass -> CNLTransition -> Code)
    (codeBound fiberBound : CNLClass -> Nat)
    (hcodes :
      letI : DecidableEq Code := Classical.decEq Code
      forall cls : CNLClass,
        ((transitionsSelectedAs transitions cls).image (code cls)).card <=
          codeBound cls)
    (hfiber :
      letI : DecidableEq Code := Classical.decEq Code
      forall (cls : CNLClass) (y : Code),
        y ∈ (transitionsSelectedAs transitions cls).image (code cls) ->
          ((transitionsSelectedAs transitions cls).filter
            fun t => code cls t = y).card <= fiberBound cls)
    (hcodeSumNat :
      (Finset.univ.sum fun cls : CNLClass => codeBound cls * fiberBound cls) <=
        2 ^ M)
    (scalar_budget :
      (2 : Real) ^ M * (shellFactor : Real) * (Ij : Real) <=
        cStar * xi / 6) :
    CNLStandardNatHeightCodeBoundsNatBudgetShellInputData shell cStar xi :=
  letI : DecidableEq Code := Classical.decEq Code
  CNLStandardNatHeightCodeBoundsNatBudgetShellInputData.ofCodeFibreNatBudget
    transitions BNDHeightNat M shellFactor Ij code codeBound fiberBound
    hcodes hfiber hcodeSumNat scalar_budget

end CNLStandardNatHeightCodeBoundsNatBudgetShellInputData

/-- Public route from raw shell-tied L.1.2/G.35 code/fibre Nat-budget data to
the direct weighted-Kraft CNL provider field. -/
def cnlStandardWeightedKraftShellFromRawCodeFibreNatBudgetShell
    {shell : FailingDyadicShell} {cStar xi : Real}
    {Code : Type} [DecidableEq Code]
    (transitions : Finset CNLTransition)
    (BNDHeightNat : CNLTransition -> Nat)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (code : CNLClass -> CNLTransition -> Code)
    (codeBound fiberBound : CNLClass -> Nat)
    (hcodes :
      forall cls : CNLClass,
        ((transitionsSelectedAs transitions cls).image (code cls)).card <=
          codeBound cls)
    (hfiber :
      forall (cls : CNLClass) (y : Code),
        y ∈ (transitionsSelectedAs transitions cls).image (code cls) ->
          ((transitionsSelectedAs transitions cls).filter
            fun t => code cls t = y).card <= fiberBound cls)
    (hcodeSumNat :
      (Finset.univ.sum fun cls : CNLClass => codeBound cls * fiberBound cls) <=
        2 ^ M)
    (scalar_budget :
      (2 : Real) ^ M * (shellFactor : Real) * (Ij : Real) <=
        cStar * xi / 6) :
    CNLStandardWeightedKraftShellInputData shell cStar xi :=
  CNLStandardNatHeightCodeBoundsNatBudgetShellInputData.ofCodeFibreNatBudget
    transitions BNDHeightNat M shellFactor Ij code codeBound fiberBound
    hcodes hfiber hcodeSumNat scalar_budget
    |>.toCNLStandardWeightedKraftShellInputData

/-- Public route from raw shell-tied L.1.2/G.35 code/fibre Nat-budget data to
the direct weighted-Kraft CNL provider, with code-label equality chosen
internally. -/
def cnlStandardWeightedKraftShellFromClassicalCodeFibreNatBudgetShell
    {shell : FailingDyadicShell} {cStar xi : Real}
    {Code : Type}
    (transitions : Finset CNLTransition)
    (BNDHeightNat : CNLTransition -> Nat)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (code : CNLClass -> CNLTransition -> Code)
    (codeBound fiberBound : CNLClass -> Nat)
    (hcodes :
      letI : DecidableEq Code := Classical.decEq Code
      forall cls : CNLClass,
        ((transitionsSelectedAs transitions cls).image (code cls)).card <=
          codeBound cls)
    (hfiber :
      letI : DecidableEq Code := Classical.decEq Code
      forall (cls : CNLClass) (y : Code),
        y ∈ (transitionsSelectedAs transitions cls).image (code cls) ->
          ((transitionsSelectedAs transitions cls).filter
            fun t => code cls t = y).card <= fiberBound cls)
    (hcodeSumNat :
      (Finset.univ.sum fun cls : CNLClass => codeBound cls * fiberBound cls) <=
        2 ^ M)
    (scalar_budget :
      (2 : Real) ^ M * (shellFactor : Real) * (Ij : Real) <=
        cStar * xi / 6) :
    CNLStandardWeightedKraftShellInputData shell cStar xi :=
  CNLStandardNatHeightCodeBoundsNatBudgetShellInputData.ofClassicalCodeFibreNatBudget
    transitions BNDHeightNat M shellFactor Ij code codeBound fiberBound
    hcodes hfiber hcodeSumNat scalar_budget
    |>.toCNLStandardWeightedKraftShellInputData

/-- Route from the manuscript-budget weighted-Kraft shell package to the direct
L.1.2 leaf. -/
def cnlStandardWeightedKraftShellFromManuscriptBudget
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellManuscriptInputData shell cStar xi) :
    CNLStandardWeightedKraftShellInputData shell cStar xi :=
  data.toCNLStandardWeightedKraftShellInputData

namespace CNLStandardWeightedKraftShellClusterInputData

/-- Package the raw proof-v4 L.1.2/G.35 cluster-to-ladder Kraft data into the
preferred CNL provider record. -/
def ofLadderKraftBudget
    {shell : FailingDyadicShell} {cStar xi : Real}
    (transitions : Finset CNLTransition)
    (BNDHeightNat : CNLTransition -> Nat)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (ladderChildren : Nat -> Finset Nat)
    (ladderHeight : Nat -> Real)
    (ladderRoot : Nat)
    (ladderHeight_dom :
      forall n : Nat, (n : Real) <= ladderHeight n)
    (cluster_le_pathKraft :
      cleanCNLKraftSum
          (selectedTransitions transitions) (fun t => (BNDHeightNat t : Real))
          (1 : Real) <=
        pathKraft ladderChildren
          (fun n => (2 : Real) ^ (-((1 : Real) * ladderHeight n))) M
          ladderRoot)
    (manuscript_budget :
      (2 : Real) ^ M * (shellFactor : Real) * (shell.X : Real) *
          (Ij : Real) <=
        cStar * xi * (shell.X : Real) / 6) :
    CNLStandardWeightedKraftShellClusterInputData shell cStar xi where
  transitions := transitions
  BNDHeightNat := BNDHeightNat
  M := M
  shellFactor := shellFactor
  Ij := Ij
  ladderChildren := ladderChildren
  ladderHeight := ladderHeight
  ladderRoot := ladderRoot
  ladderHeight_dom := ladderHeight_dom
  cluster_le_pathKraft := cluster_le_pathKraft
  manuscript_budget := manuscript_budget

end CNLStandardWeightedKraftShellClusterInputData

/-- Route from the proof-v4 cluster/Kraft certificate to the direct L.1.2
weighted-Kraft shell leaf. -/
def cnlStandardWeightedKraftShellFromCluster
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellClusterInputData shell cStar xi) :
    CNLStandardWeightedKraftShellInputData shell cStar xi :=
  data.toCNLStandardWeightedKraftShellManuscriptInputData
    |>.toCNLStandardWeightedKraftShellInputData

/-- Route from the proof-v4 cluster/Kraft certificate to the stronger
proof-object CNL leaf required by the strict Appendix N endpoint. -/
def cnlStandardWeightedKraftShellProofFromCluster
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellClusterInputData shell cStar xi) :
    CNLStandardWeightedKraftShellProofInputData shell cStar xi :=
  data.toCNLStandardWeightedKraftShellProofInputData

/-- Proof-v4 named route from the L.1.2/G.35 cluster-to-ladder manuscript
package to the strict CNL proof-object leaf.

This is the preferred final-provider boundary when the selected clean CNL
family, Nat BND heights, ladder Kraft domination, and G.35 manuscript scalar
budget have been constructed directly. -/
def cnlStandardWeightedKraftShellProofFromClosedL112G35Cluster
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellClusterInputData shell cStar xi) :
    CNLStandardWeightedKraftShellProofInputData shell cStar xi :=
  cnlStandardWeightedKraftShellProofFromCluster data

/-- Public strict route from raw proof-v4 L.1.2/G.35 cluster-to-ladder Kraft
data to the preferred CNL proof-object provider. -/
def cnlStandardWeightedKraftShellProofFromRawClosedL112G35Cluster
    {shell : FailingDyadicShell} {cStar xi : Real}
    (transitions : Finset CNLTransition)
    (BNDHeightNat : CNLTransition -> Nat)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (ladderChildren : Nat -> Finset Nat)
    (ladderHeight : Nat -> Real)
    (ladderRoot : Nat)
    (ladderHeight_dom :
      forall n : Nat, (n : Real) <= ladderHeight n)
    (cluster_le_pathKraft :
      cleanCNLKraftSum
          (selectedTransitions transitions) (fun t => (BNDHeightNat t : Real))
          (1 : Real) <=
        pathKraft ladderChildren
          (fun n => (2 : Real) ^ (-((1 : Real) * ladderHeight n))) M
          ladderRoot)
    (manuscript_budget :
      (2 : Real) ^ M * (shellFactor : Real) * (shell.X : Real) *
          (Ij : Real) <=
        cStar * xi * (shell.X : Real) / 6) :
    CNLStandardWeightedKraftShellProofInputData shell cStar xi :=
  cnlStandardWeightedKraftShellProofFromClosedL112G35Cluster
    (CNLStandardWeightedKraftShellClusterInputData.ofLadderKraftBudget
      transitions BNDHeightNat M shellFactor Ij ladderChildren ladderHeight
      ladderRoot ladderHeight_dom cluster_le_pathKraft manuscript_budget)

/-- Public direct route from raw proof-v4 L.1.2/G.35 cluster-to-ladder Kraft
data to the direct weighted-Kraft shell provider. -/
def cnlStandardWeightedKraftShellFromRawClosedL112G35Cluster
    {shell : FailingDyadicShell} {cStar xi : Real}
    (transitions : Finset CNLTransition)
    (BNDHeightNat : CNLTransition -> Nat)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (ladderChildren : Nat -> Finset Nat)
    (ladderHeight : Nat -> Real)
    (ladderRoot : Nat)
    (ladderHeight_dom :
      forall n : Nat, (n : Real) <= ladderHeight n)
    (cluster_le_pathKraft :
      cleanCNLKraftSum
          (selectedTransitions transitions) (fun t => (BNDHeightNat t : Real))
          (1 : Real) <=
        pathKraft ladderChildren
          (fun n => (2 : Real) ^ (-((1 : Real) * ladderHeight n))) M
          ladderRoot)
    (manuscript_budget :
      (2 : Real) ^ M * (shellFactor : Real) * (shell.X : Real) *
          (Ij : Real) <=
        cStar * xi * (shell.X : Real) / 6) :
    CNLStandardWeightedKraftShellInputData shell cStar xi :=
  cnlStandardWeightedKraftShellFromCluster
    (CNLStandardWeightedKraftShellClusterInputData.ofLadderKraftBudget
      transitions BNDHeightNat M shellFactor Ij ladderChildren ladderHeight
      ladderRoot ladderHeight_dom cluster_le_pathKraft manuscript_budget)

/-- Proof-v4 named route for L.1.2/G.35 at the stronger proof-object boundary:
surviving selected transitions, Nat BND heights, the cluster-to-ladder Kraft
proof, and the scalar shell budget are already packaged in the strict CNL
proof object. -/
def cnlStandardWeightedKraftShellProofFromClosedL112G35
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellProofInputData shell cStar xi) :
    CNLStandardWeightedKraftShellProofInputData shell cStar xi :=
  cnlStandardWeightedKraftShellProofFromInput data

/-- Route from the full L.1.2/G.35 encoding proof object to the direct
weighted-Kraft shell leaf. -/
def cnlStandardWeightedKraftShellFromEncodingProof
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellProofInputData shell cStar xi) :
    CNLStandardWeightedKraftShellInputData shell cStar xi :=
  data.toCNLStandardWeightedKraftShellClusterInputData
    |>.toCNLStandardWeightedKraftShellManuscriptInputData
    |>.toCNLStandardWeightedKraftShellInputData

/-- Proof-v4 named route for L.1.2/G.35: deterministic selected transitions,
Nat BND heights, code/fibre bounds, weighted Kraft, and the scalar shell budget
assembled into the direct CNL leaf. -/
def cnlStandardWeightedKraftShellFromClosedL112G35
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellProofInputData shell cStar xi) :
    CNLStandardWeightedKraftShellInputData shell cStar xi :=
  cnlStandardWeightedKraftShellFromEncodingProof data

/-- Remaining concrete CNL data needed before a no-input L.1.2/G.35 provider
can be installed. -/
def cnlStandardWeightedKraftShellOpenItems : List String :=
  [ "L.1.1 deterministic selector and priority partition for clean nonseparated transitions",
    "L.1.2a-L.1.2d removal of SEP, VS, DS, and PKG exits from the surviving clean family",
    "Nat-valued BND heights and the L.1w/G.35 weighted Kraft bound for surviving clusters",
    "G.35 scalar shell/interval budget converting the Kraft estimate to the CNL phase term" ]

theorem cnlStandardWeightedKraftShellOpenItems_nonempty :
    cnlStandardWeightedKraftShellOpenItems = [] -> False := by
  intro h
  simp [cnlStandardWeightedKraftShellOpenItems] at h

end

end Erdos260

