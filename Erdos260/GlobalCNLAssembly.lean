import Mathlib
import Erdos260.CNLEntropy
import Erdos260.GlobalChernoffAssembly

/-!
# Global CNL assembly

This module grounds the CNL phase one layer further.  The path family consumed
by the CNL entropy package is now the selected-transition family produced by
the K.3/J.5 priority selector, and the Kraft estimate is routed through the
K.3/L.1 weighted Kraft conclusion rather than an arbitrary path set.
-/

namespace Erdos260

noncomputable section

/--
Grounded K.3/L.1 selected-transition CNL input.

Compared with the generic `CNLClusterEncodingProof`, this local input no
longer asks the provider to prove the scalar normalization facts `0 < c` and
`(1 - 2^{-c})^{-1} <= C_Q`: the grounded CNL data carries both as typed
fields, and the full encoding proof below reconstructs the generic Kraft
certificate from those typed facts.
-/
structure GroundedCNLClusterEncodingInput {α : Type} (paths : Finset α)
    (BNDHeight : α -> Real) (c CQ shellFactor X Ij cStar xi : Real)
    (M : Nat) where
  ladderChildren : Nat -> Finset Nat
  ladderHeight : Nat -> Real
  ladderRoot : Nat
  ladderHeight_dom :
    ∀ k : Nat, (k : Real) <= ladderHeight k
  cluster_le_pathKraft :
    cleanCNLKraftSum paths BNDHeight c <=
      pathKraft ladderChildren
        (fun k => (2 : Real) ^ (-(c * ladderHeight k))) M ladderRoot
  manuscript_bound :
    CQ ^ M * shellFactor * X * Ij <= cStar * xi * X / 6

/--
Grounded proof-v4 G.35/L.1.2 weighted CNL input.

This is the actual entropy-facing conclusion consumed by the phase core: the
selected clean transitions have total weighted Kraft mass at most `C_Q^M`, and
the manuscript shell/interval arithmetic pays their contribution. Ladder data
remains available through `GroundedCNLClusterEncodingInput` as a stronger
compatibility route, but the strongest endpoint no longer asks providers for
that proof witness.
-/
structure GroundedCNLWeightedEncodingInput {α : Type} (paths : Finset α)
    (BNDHeight : α -> Real) (c CQ shellFactor X Ij cStar xi : Real)
    (M : Nat) where
  kraftSum_le :
    cleanCNLKraftSum paths BNDHeight c <= CQ ^ M
  manuscript_bound :
    CQ ^ M * shellFactor * X * Ij <= cStar * xi * X / 6

namespace GroundedCNLWeightedEncodingInput

/-- The CNL shell/interval budget is usually proved as an `X`-free scalar
budget and then multiplied by the nonnegative shell size. -/
theorem shellIntervalBudget_of_scalarBudget
    {cStar xi X shellFactor Ij : Real} {M : Nat}
    (hX_nonneg : 0 <= X)
    (hscalar :
      (2 : Real) ^ M * shellFactor * Ij <= cStar * xi / 6) :
    (2 : Real) ^ M * shellFactor * X * Ij <= cStar * xi * X / 6 := by
  have hmul := mul_le_mul_of_nonneg_right hscalar hX_nonneg
  nlinarith

/-- Reinsert the typed positivity of `c` and recover the generic weighted
entropy certificate. -/
def toWeightedEntropyData
    {cStar xi X : Real}
    {α : Type} {paths : Finset α} {BNDHeight : α -> Real}
    {c CQ shellFactor Ij : Real} {M : Nat}
    (input :
      GroundedCNLWeightedEncodingInput paths BNDHeight c CQ shellFactor X Ij
        cStar xi M)
    (hc_pos : 0 < c) :
    CNLWeightedEntropyData paths BNDHeight c CQ shellFactor X Ij cStar xi M where
  c_pos := hc_pos
  kraftSum_le := input.kraftSum_le
  manuscript_bound := input.manuscript_bound

/-- Build the weighted CNL input from a finite counting bound when all selected
heights are nonnegative.  This isolates the elementary Kraft step; the
manuscript work that remains is the actual selected-transition count and the
shell/interval budget. -/
def ofNonnegativeHeightCardBound
    {cStar xi X : Real}
    {α : Type} {paths : Finset α} {BNDHeight : α -> Real}
    {c CQ shellFactor Ij : Real} {M : Nat}
    (hc_nonneg : 0 <= c)
    (hheight : ∀ p, p ∈ paths -> 0 <= BNDHeight p)
    (hcard : (paths.card : Real) <= CQ ^ M)
    (hmanuscript :
      CQ ^ M * shellFactor * X * Ij <= cStar * xi * X / 6) :
    GroundedCNLWeightedEncodingInput paths BNDHeight c CQ shellFactor X Ij
      cStar xi M where
  kraftSum_le :=
    cleanCNLKraftSum_le_of_card_bound
      (paths := paths) (BNDHeight := BNDHeight)
      (c := c) (CQ := CQ) (M := M)
      hc_nonneg hheight hcard
  manuscript_bound := hmanuscript

/-- Nat-valued BND heights close the nonnegativity side of the elementary
finite Kraft bridge. -/
def ofNatHeightCardBound
    {cStar xi X : Real}
    {α : Type} {paths : Finset α} {BNDHeightNat : α -> Nat}
    {c CQ shellFactor Ij : Real} {M : Nat}
    (hc_nonneg : 0 <= c)
    (hcard : (paths.card : Real) <= CQ ^ M)
    (hmanuscript :
      CQ ^ M * shellFactor * X * Ij <= cStar * xi * X / 6) :
    GroundedCNLWeightedEncodingInput paths (fun p => (BNDHeightNat p : Real))
      c CQ shellFactor X Ij cStar xi M :=
  ofNonnegativeHeightCardBound
    (paths := paths) (BNDHeight := fun p => (BNDHeightNat p : Real))
    (c := c) (CQ := CQ) (shellFactor := shellFactor) (X := X)
    (Ij := Ij) (cStar := cStar) (xi := xi) (M := M)
    hc_nonneg (fun p _hp => Nat.cast_nonneg (BNDHeightNat p))
    hcard hmanuscript

end GroundedCNLWeightedEncodingInput

namespace GroundedCNLClusterEncodingInput

/-- Reinsert the typed positivity of `c` to recover the generic Kraft data. -/
def toKraftData
    {cStar xi X : Real}
    {α : Type} {paths : Finset α} {BNDHeight : α -> Real}
    {c CQ shellFactor Ij : Real} {M : Nat}
    (input :
      GroundedCNLClusterEncodingInput paths BNDHeight c CQ shellFactor X Ij
        cStar xi M)
    (hc_pos : 0 < c)
    (hCQ_dom : (1 - (2 : Real) ^ (-c))⁻¹ <= CQ) :
    CNLClusterKraftData paths BNDHeight c CQ M where
  ladderChildren := input.ladderChildren
  ladderHeight := input.ladderHeight
  ladderRoot := input.ladderRoot
  hc_pos := hc_pos
  hCQ_dom := hCQ_dom
  ladderHeight_dom := input.ladderHeight_dom
  cluster_le_pathKraft := input.cluster_le_pathKraft

/-- Project the final shell/interval budget from the grounded input. -/
def toBudgetData
    {cStar xi X : Real}
    {α : Type} {paths : Finset α} {BNDHeight : α -> Real}
    {c CQ shellFactor Ij : Real} {M : Nat}
    (input :
      GroundedCNLClusterEncodingInput paths BNDHeight c CQ shellFactor X Ij
        cStar xi M) :
    CNLClusterBudgetData CQ shellFactor X Ij cStar xi M where
  manuscript_bound := input.manuscript_bound

/-- Assemble the generic CNL encoding proof from grounded input plus `c > 0`. -/
def toEncodingProof
    {cStar xi X : Real}
    {α : Type} {paths : Finset α} {BNDHeight : α -> Real}
    {c CQ shellFactor Ij : Real} {M : Nat}
    (input :
      GroundedCNLClusterEncodingInput paths BNDHeight c CQ shellFactor X Ij
        cStar xi M)
    (hc_pos : 0 < c)
    (hCQ_dom : (1 - (2 : Real) ^ (-c))⁻¹ <= CQ) :
    CNLClusterEncodingProof paths BNDHeight c CQ shellFactor X Ij cStar xi M where
  kraft := input.toKraftData hc_pos hCQ_dom
  budget := input.toBudgetData

/-- Project the stronger ladder/Kraft proof object to the entropy-facing
weighted CNL input used by the current strongest endpoint. -/
def toWeightedEncodingInput
    {cStar xi X : Real}
    {α : Type} {paths : Finset α} {BNDHeight : α -> Real}
    {c CQ shellFactor Ij : Real} {M : Nat}
    (input :
      GroundedCNLClusterEncodingInput paths BNDHeight c CQ shellFactor X Ij
        cStar xi M)
    (hc_pos : 0 < c)
    (hCQ_dom : (1 - (2 : Real) ^ (-c))⁻¹ <= CQ) :
    GroundedCNLWeightedEncodingInput paths BNDHeight c CQ shellFactor X Ij
      cStar xi M where
  kraftSum_le :=
    CNLClusterEncodingProof.kraftSum_le
      (input.toEncodingProof hc_pos hCQ_dom)
  manuscript_bound := input.manuscript_bound

end GroundedCNLClusterEncodingInput

/--
Proof-v4 aligned CNL local data.

The clean CNL path set is no longer arbitrary: it is
`selectedTransitions selector.transitions`, tying the entropy package to the
canonical priority scan and one-step normal-form obligations.
-/
structure GroundedCNLLocalData (cStar xi X : Real) where
  selector : CNLNormalFormSelectorData
  BNDHeight : CNLTransition -> Real
  c : {c : Real // 0 < c}
  CQ : {CQ : Real // (1 - (2 : Real) ^ (-(c : Real)))⁻¹ <= CQ}
  M : Nat
  shellFactor : {x : Real // 0 <= x}
  Ij : {x : Real // 0 <= x}
  encoding_input :
    GroundedCNLWeightedEncodingInput
      (selectedTransitions selector.transitions) BNDHeight c (CQ : Real) (shellFactor : Real)
      X (Ij : Real) cStar xi M

/-- Assemble grounded CNL data from the closed selector package and the
K.3/L.1 selected-transition encoding/budget input. -/
def GroundedCNLLocalData.ofClosedSelectorAndBudget
    {cStar xi X : Real}
    (selector : CNLNormalFormSelectorData)
    (BNDHeight : CNLTransition -> Real)
    (c : {c : Real // 0 < c})
    (CQ : {CQ : Real // (1 - (2 : Real) ^ (-(c : Real)))⁻¹ <= CQ})
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (encoding_input :
      GroundedCNLWeightedEncodingInput
        (selectedTransitions selector.transitions) BNDHeight (c : Real)
        (CQ : Real) (shellFactor : Real) X (Ij : Real) cStar xi M) :
    GroundedCNLLocalData cStar xi X where
  selector := selector
  BNDHeight := BNDHeight
  c := c
  CQ := CQ
  M := M
  shellFactor := shellFactor
  Ij := Ij
  encoding_input := encoding_input

/-- G.6/L.1 selected-transition selector and shell-budget data before it is
packed as grounded CNL local data. -/
structure CNLSelectorBudgetInputData (cStar xi X : Real) where
  selector : CNLNormalFormSelectorData
  BNDHeight : CNLTransition -> Real
  c : {c : Real // 0 < c}
  CQ : {CQ : Real // (1 - (2 : Real) ^ (-(c : Real)))⁻¹ <= CQ}
  M : Nat
  shellFactor : {x : Real // 0 <= x}
  Ij : {x : Real // 0 <= x}
  encoding_input :
    GroundedCNLWeightedEncodingInput
      (selectedTransitions selector.transitions) BNDHeight (c : Real)
      (CQ : Real) (shellFactor : Real) X (Ij : Real) cStar xi M

/-- L.1.1/L.1.2 CNL leaf with the selector package and weighted encoding kept
separate.  The K.3.0--K.3.5 selector/normal-form obligations are carried by
`CNLNormalFormSelectorData`; this leaf leaves the L.1.2 selected-transition
weighted encoding as the remaining CNL content. -/
structure CNLSelectorEncodingInputData (cStar xi X : Real) where
  selector : CNLNormalFormSelectorData
  BNDHeight : CNLTransition -> Real
  c : {c : Real // 0 < c}
  CQ : {CQ : Real // (1 - (2 : Real) ^ (-(c : Real)))⁻¹ <= CQ}
  M : Nat
  shellFactor : {x : Real // 0 <= x}
  Ij : {x : Real // 0 <= x}
  encoding_input :
    GroundedCNLWeightedEncodingInput
      (selectedTransitions selector.transitions) BNDHeight (c : Real)
      (CQ : Real) (shellFactor : Real) X (Ij : Real) cStar xi M

/--
L.1.1/L.1.2 CNL leaf in the standard G.6 normalization used by the final
small-large endpoint.  The entropy exponent and one-step denominator are fixed
to the conservative constants `c = 1` and `C_Q = 2`; the remaining content is
the selected-transition weighted Kraft comparison and the final shell/interval
budget for those fixed constants.
-/
structure CNLStandardSelectorEncodingInputData (cStar xi X : Real) where
  selector : CNLNormalFormSelectorData
  BNDHeight : CNLTransition -> Real
  M : Nat
  shellFactor : {x : Real // 0 <= x}
  Ij : {x : Real // 0 <= x}
  encoding_input :
    GroundedCNLWeightedEncodingInput
      (selectedTransitions selector.transitions) BNDHeight (1 : Real)
      (2 : Real) (shellFactor : Real) X (Ij : Real) cStar xi M

/--
Standard CNL leaf with the closed selector skeleton kept out of the provider
surface.  The provider now gives only the clean-visible transition family and
the L.1.2 selected-transition cluster encoding; `CNLNormalFormSelectorData` is
rebuilt by the already-closed deterministic selector constructor.
-/
structure CNLStandardCleanVisibleEncodingInputData (cStar xi X : Real) where
  transitions : Finset CNLTransition
  BNDHeight : CNLTransition -> Real
  M : Nat
  shellFactor : {x : Real // 0 <= x}
  Ij : {x : Real // 0 <= x}
  clean_visible :
    forall t, t ∈ transitions -> t.available.Nonempty
  encoding_input :
    GroundedCNLWeightedEncodingInput
      (selectedTransitions transitions) BNDHeight (1 : Real)
      (2 : Real) (shellFactor : Real) X (Ij : Real) cStar xi M

/--
Standard CNL leaf on the already-selected transition family.  Compared with
`CNLStandardCleanVisibleEncodingInputData`, this removes the provider-side
clean-visibility field: membership in `selectedTransitions transitions` already
exhibits a selected class, hence a nonempty available set.
-/
structure CNLStandardSelectedEncodingInputData (cStar xi X : Real) where
  transitions : Finset CNLTransition
  BNDHeight : CNLTransition -> Real
  M : Nat
  shellFactor : {x : Real // 0 <= x}
  Ij : {x : Real // 0 <= x}
  encoding_input :
    GroundedCNLWeightedEncodingInput
      (selectedTransitions transitions) BNDHeight (1 : Real)
      (2 : Real) (shellFactor : Real) X (Ij : Real) cStar xi M

/--
Standard selected-transition CNL leaf in the proof-v4 code-budget form.

The selected clean-visibility skeleton is closed by `selectedTransitions`; the
remaining L.1.2 content is Nat-valued BND height, class-local code/fibre
budgets, their class-budget sum, and the final X-free shell/interval scalar
budget.
-/
structure CNLStandardNatHeightCodeClassScalarInputData
    (cStar xi X : Real) where
  Code : Type
  decCode : DecidableEq Code
  transitions : Finset CNLTransition
  BNDHeightNat : CNLTransition -> Nat
  M : Nat
  shellFactor : {x : Real // 0 <= x}
  Ij : {x : Real // 0 <= x}
  code : CNLClass -> CNLTransition -> Code
  codeBound : CNLClass -> Nat
  fiberBound : CNLClass -> Nat
  classBudget : CNLClass -> Real
  hX_nonneg : 0 <= X
  hcodes :
    forall cls : CNLClass,
      ((transitionsSelectedAs transitions cls).image (code cls)).card <=
        codeBound cls
  hfiber :
    forall (cls : CNLClass) (y : Code),
      y ∈ (transitionsSelectedAs transitions cls).image (code cls) ->
        ((transitionsSelectedAs transitions cls).filter
          fun t => code cls t = y).card <= fiberBound cls
  hclassBudget :
    forall cls : CNLClass,
      (codeBound cls : Real) * (fiberBound cls : Real) <= classBudget cls
  hbudgetSum :
    (∑ cls : CNLClass, classBudget cls) <= (2 : Real) ^ M
  scalar_budget :
    (2 : Real) ^ M * (shellFactor : Real) * (Ij : Real) <=
      cStar * xi / 6

/--
Standard selected-transition CNL leaf in the direct proof-v4 code/fibre budget
form.  Compared with `CNLStandardNatHeightCodeClassScalarInputData`, this drops
the auxiliary real `classBudget` layer: the manuscript input is the direct
global sum of the class-local code/fibre products.
-/
structure CNLStandardNatHeightCodeBoundsScalarInputData
    (cStar xi X : Real) where
  Code : Type
  decCode : DecidableEq Code
  transitions : Finset CNLTransition
  BNDHeightNat : CNLTransition -> Nat
  M : Nat
  shellFactor : {x : Real // 0 <= x}
  Ij : {x : Real // 0 <= x}
  code : CNLClass -> CNLTransition -> Code
  codeBound : CNLClass -> Nat
  fiberBound : CNLClass -> Nat
  hX_nonneg : 0 <= X
  hcodes :
    forall cls : CNLClass,
      ((transitionsSelectedAs transitions cls).image (code cls)).card <=
        codeBound cls
  hfiber :
    forall (cls : CNLClass) (y : Code),
      y ∈ (transitionsSelectedAs transitions cls).image (code cls) ->
        ((transitionsSelectedAs transitions cls).filter
          fun t => code cls t = y).card <= fiberBound cls
  hcodeSum :
    (∑ cls : CNLClass, (codeBound cls : Real) * (fiberBound cls : Real)) <=
      (2 : Real) ^ M
  scalar_budget :
    (2 : Real) ^ M * (shellFactor : Real) * (Ij : Real) <=
      cStar * xi / 6

/--
Standard selected-transition CNL leaf with the global code/fibre product budget
kept as a Nat-valued counting inequality.  This is the same proof-v4 content as
`CNLStandardNatHeightCodeBoundsScalarInputData`, but removes the last Real cast
from the provider surface for the class-local product sum.
-/
structure CNLStandardNatHeightCodeBoundsNatBudgetScalarInputData
    (cStar xi X : Real) where
  Code : Type
  decCode : DecidableEq Code
  transitions : Finset CNLTransition
  BNDHeightNat : CNLTransition -> Nat
  M : Nat
  shellFactor : {x : Real // 0 <= x}
  Ij : {x : Real // 0 <= x}
  code : CNLClass -> CNLTransition -> Code
  codeBound : CNLClass -> Nat
  fiberBound : CNLClass -> Nat
  hX_nonneg : 0 <= X
  hcodes :
    forall cls : CNLClass,
      ((transitionsSelectedAs transitions cls).image (code cls)).card <=
        codeBound cls
  hfiber :
    forall (cls : CNLClass) (y : Code),
      y ∈ (transitionsSelectedAs transitions cls).image (code cls) ->
        ((transitionsSelectedAs transitions cls).filter
          fun t => code cls t = y).card <= fiberBound cls
  hcodeSumNat :
    (Finset.univ.sum fun cls : CNLClass => codeBound cls * fiberBound cls) <=
      2 ^ M
  scalar_budget :
    (2 : Real) ^ M * (shellFactor : Real) * (Ij : Real) <=
      cStar * xi / 6

/--
Shell-tied version of the direct Nat-budget CNL leaf.  In the strongest
Appendix-N endpoint the shell size is always `(shell.X : Real)`, so the
nonnegativity of `X` is closed internally by `Nat.cast_nonneg` instead of being
carried by the provider.
-/
structure CNLStandardNatHeightCodeBoundsNatBudgetShellInputData
    (shell : FailingDyadicShell) (cStar xi : Real) where
  Code : Type
  decCode : DecidableEq Code
  transitions : Finset CNLTransition
  BNDHeightNat : CNLTransition -> Nat
  M : Nat
  shellFactor : {x : Real // 0 <= x}
  Ij : {x : Real // 0 <= x}
  code : CNLClass -> CNLTransition -> Code
  codeBound : CNLClass -> Nat
  fiberBound : CNLClass -> Nat
  hcodes :
    forall cls : CNLClass,
      ((transitionsSelectedAs transitions cls).image (code cls)).card <=
        codeBound cls
  hfiber :
    forall (cls : CNLClass) (y : Code),
      y ∈ (transitionsSelectedAs transitions cls).image (code cls) ->
        ((transitionsSelectedAs transitions cls).filter
          fun t => code cls t = y).card <= fiberBound cls
  hcodeSumNat :
    (Finset.univ.sum fun cls : CNLClass => codeBound cls * fiberBound cls) <=
      2 ^ M
  scalar_budget :
    (2 : Real) ^ M * (shellFactor : Real) * (Ij : Real) <=
      cStar * xi / 6

/--
Shell-tied CNL leaf in the direct L.1.2 weighted-Kraft form.

This is the manuscript conclusion (L.1w/G.35) after fixing the standard
constants `c = 1`, `C_Q = 2`, and the shell size `(shell.X : Real)`.  The
provider supplies the selected-transition weighted entropy bound and the
X-free shell/interval scalar budget; nonnegativity of the shell size is closed
internally.
-/
structure CNLStandardWeightedKraftShellInputData
    (shell : FailingDyadicShell) (cStar xi : Real) where
  transitions : Finset CNLTransition
  BNDHeightNat : CNLTransition -> Nat
  M : Nat
  shellFactor : {x : Real // 0 <= x}
  Ij : {x : Real // 0 <= x}
  kraftSum_le :
    cleanCNLKraftSum
        (selectedTransitions transitions) (fun t => (BNDHeightNat t : Real))
        (1 : Real) <=
      (2 : Real) ^ M
  scalar_budget :
    (2 : Real) ^ M * (shellFactor : Real) * (Ij : Real) <=
      cStar * xi / 6

/--
Shell-tied CNL leaf in the manuscript scalar-budget form.

Lemma L.1.2/G.35 pays the selected CNL contribution with the shell factor
still present on both sides.  Since a failing dyadic shell has positive
`X`, the projection below cancels that factor and recovers the X-free budget
used by the existing grounded CNL package.
-/
structure CNLStandardWeightedKraftShellManuscriptInputData
    (shell : FailingDyadicShell) (cStar xi : Real) where
  transitions : Finset CNLTransition
  BNDHeightNat : CNLTransition -> Nat
  M : Nat
  shellFactor : {x : Real // 0 <= x}
  Ij : {x : Real // 0 <= x}
  kraftSum_le :
    cleanCNLKraftSum
        (selectedTransitions transitions) (fun t => (BNDHeightNat t : Real))
        (1 : Real) <=
      (2 : Real) ^ M
  manuscript_budget :
    (2 : Real) ^ M * (shellFactor : Real) * (shell.X : Real) *
        (Ij : Real) <=
      cStar * xi * (shell.X : Real) / 6

/--
Shell-tied CNL leaf in the L.1.2 cluster-to-ladder form.

The abstract G.2/G.6 ladder iteration is already closed in Lean by
`liftPathKraft_le`.  This structure leaves only the proof-v4 reconstruction
step: the concrete selected clean CNL transitions must be dominated by the
abstract ladder Kraft sum, plus the final manuscript shell/interval budget.
-/
structure CNLStandardWeightedKraftShellClusterInputData
    (shell : FailingDyadicShell) (cStar xi : Real) where
  transitions : Finset CNLTransition
  BNDHeightNat : CNLTransition -> Nat
  M : Nat
  shellFactor : {x : Real // 0 <= x}
  Ij : {x : Real // 0 <= x}
  ladderChildren : Nat -> Finset Nat
  ladderHeight : Nat -> Real
  ladderRoot : Nat
  ladderHeight_dom :
    forall δ : Nat, (δ : Real) <= ladderHeight δ
  cluster_le_pathKraft :
    cleanCNLKraftSum
        (selectedTransitions transitions) (fun t => (BNDHeightNat t : Real))
        (1 : Real) <=
      pathKraft ladderChildren
        (fun δ => (2 : Real) ^ (-((1 : Real) * ladderHeight δ))) M
        ladderRoot
  manuscript_budget :
    (2 : Real) ^ M * (shellFactor : Real) * (shell.X : Real) *
        (Ij : Real) <=
      cStar * xi * (shell.X : Real) / 6

/--
Shell-tied CNL leaf in proof-object form.

This is the same proof-v4 L.1.2/G.35 content as
`CNLStandardWeightedKraftShellClusterInputData`, but packaged as the generic
`CNLClusterEncodingProof` object with the standard constants `c = 1` and
`C_Q = 2`.  The current strongest endpoint can consume this proof object and
project the older cluster leaf from it.
-/
structure CNLStandardWeightedKraftShellProofInputData
    (shell : FailingDyadicShell) (cStar xi : Real) where
  transitions : Finset CNLTransition
  BNDHeightNat : CNLTransition -> Nat
  M : Nat
  shellFactor : {x : Real // 0 <= x}
  Ij : {x : Real // 0 <= x}
  encodingProof :
    CNLClusterEncodingProof
      (selectedTransitions transitions) (fun t => (BNDHeightNat t : Real))
      (1 : Real) (2 : Real) (shellFactor : Real) (shell.X : Real) (Ij : Real)
      cStar xi M

namespace CNLSelectorBudgetInputData

/-- Convert the selector/budget leaf to the grounded CNL package. -/
def toGroundedCNLLocalData
    {cStar xi X : Real}
    (data : CNLSelectorBudgetInputData cStar xi X) :
    GroundedCNLLocalData cStar xi X :=
  GroundedCNLLocalData.ofClosedSelectorAndBudget data.selector data.BNDHeight
    data.c data.CQ data.M data.shellFactor data.Ij data.encoding_input

end CNLSelectorBudgetInputData

namespace CNLSelectorEncodingInputData

/-- Assemble the separated G.6/L.1 CNL leaf from the clean-visible selector
evidence and the selected-transition cluster encoding input. -/
def ofClosedG6L1
    {cStar xi X : Real}
    (transitions : Finset CNLTransition)
    (BNDHeight : CNLTransition -> Real)
    (c : {c : Real // 0 < c})
    (CQ : {CQ : Real // (1 - (2 : Real) ^ (-(c : Real)))⁻¹ <= CQ})
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (clean_visible :
      ∀ t ∈ transitions, t.available.Nonempty)
    (encoding_input :
      GroundedCNLWeightedEncodingInput
        (selectedTransitions transitions) BNDHeight (c : Real)
        (CQ : Real) (shellFactor : Real) X (Ij : Real) cStar xi M) :
    CNLSelectorEncodingInputData cStar xi X where
  selector := CNLNormalFormSelectorData.ofCleanVisible transitions clean_visible
  BNDHeight := BNDHeight
  c := c
  CQ := CQ
  M := M
  shellFactor := shellFactor
  Ij := Ij
  encoding_input := by
    simpa [CNLNormalFormSelectorData.ofCleanVisible] using encoding_input

/-- Project the L.1.1 clean-visibility selector evidence carried by the CNL
selector/encoding leaf. -/
theorem clean_visible
    {cStar xi X : Real}
    (data : CNLSelectorEncodingInputData cStar xi X) :
    ∀ t ∈ data.selector.transitions, t.available.Nonempty :=
  data.selector.clean_visible

/-- Project the closed deterministic priority classifier carried by the CNL
selector/encoding leaf. -/
theorem transitionClassifier
    {cStar xi X : Real}
    (data : CNLSelectorEncodingInputData cStar xi X)
    {t : CNLTransition} (ht : t ∈ data.selector.transitions) :
    ∃! cls : CNLClass,
      canonicalCNLSelector t = some cls ∧
        cls ∈ t.available ∧
        ∀ other ∈ t.available,
          CNLClass.priorityRank cls <= CNLClass.priorityRank other :=
  data.selector.transitionClassifier ht

/-- Reconstruct the selector-budget leaf from clean visibility and the L.1.2
cluster encoding input. -/
def toSelectorBudgetInputData
    {cStar xi X : Real}
    (data : CNLSelectorEncodingInputData cStar xi X) :
    CNLSelectorBudgetInputData cStar xi X where
  selector := data.selector
  BNDHeight := data.BNDHeight
  c := data.c
  CQ := data.CQ
  M := data.M
  shellFactor := data.shellFactor
  Ij := data.Ij
  encoding_input := data.encoding_input

/-- Convert the separated selector/encoding leaf to grounded CNL local data. -/
def toGroundedCNLLocalData
    {cStar xi X : Real}
    (data : CNLSelectorEncodingInputData cStar xi X) :
    GroundedCNLLocalData cStar xi X :=
  data.toSelectorBudgetInputData.toGroundedCNLLocalData

end CNLSelectorEncodingInputData

namespace CNLStandardSelectorEncodingInputData

/-- The fixed CNL entropy exponent in the standard G.6 normalization. -/
def cStandard : {c : Real // 0 < c} :=
  ⟨1, by norm_num⟩

/-- The fixed CNL one-step denominator in the standard G.6 normalization. -/
def CQStandard : {CQ : Real // (1 - (2 : Real) ^ (-(cStandard : Real)))⁻¹ <= CQ} :=
  ⟨2, by
    exact cnl_cq_dominates_of_c_ge_one (c := (1 : Real)) (CQ := (2 : Real))
      (by norm_num) (by norm_num)⟩

/-- Assemble the standard-normalized CNL leaf from clean visibility and the
selected-transition cluster encoding input. -/
def ofClosedG6L1Standard
    {cStar xi X : Real}
    (transitions : Finset CNLTransition)
    (BNDHeight : CNLTransition -> Real)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (clean_visible :
      ∀ t ∈ transitions, t.available.Nonempty)
    (encoding_input :
      GroundedCNLWeightedEncodingInput
        (selectedTransitions transitions) BNDHeight (1 : Real)
        (2 : Real) (shellFactor : Real) X (Ij : Real) cStar xi M) :
    CNLStandardSelectorEncodingInputData cStar xi X where
  selector := CNLNormalFormSelectorData.ofCleanVisible transitions clean_visible
  BNDHeight := BNDHeight
  M := M
  shellFactor := shellFactor
  Ij := Ij
  encoding_input := by
    simpa [CNLNormalFormSelectorData.ofCleanVisible] using encoding_input

/-- Forget the standard normalization and recover the older selector/encoding
leaf. -/
def toCNLSelectorEncodingInputData
    {cStar xi X : Real}
    (data : CNLStandardSelectorEncodingInputData cStar xi X) :
    CNLSelectorEncodingInputData cStar xi X where
  selector := data.selector
  BNDHeight := data.BNDHeight
  c := cStandard
  CQ := CQStandard
  M := data.M
  shellFactor := data.shellFactor
  Ij := data.Ij
  encoding_input := data.encoding_input

/-- Convert the standard-normalized selector/encoding leaf to grounded CNL local
data. -/
def toGroundedCNLLocalData
    {cStar xi X : Real}
    (data : CNLStandardSelectorEncodingInputData cStar xi X) :
    GroundedCNLLocalData cStar xi X :=
  data.toCNLSelectorEncodingInputData.toGroundedCNLLocalData

/-- Project the L.1.1 clean-visibility selector evidence carried by the
standard CNL selector/encoding leaf. -/
theorem clean_visible
    {cStar xi X : Real}
    (data : CNLStandardSelectorEncodingInputData cStar xi X) :
    ∀ t ∈ data.selector.transitions, t.available.Nonempty :=
  data.selector.clean_visible

/-- Project the deterministic priority classifier carried by the standard CNL
selector/encoding leaf. -/
theorem transitionClassifier
    {cStar xi X : Real}
    (data : CNLStandardSelectorEncodingInputData cStar xi X)
    {t : CNLTransition} (ht : t ∈ data.selector.transitions) :
    ∃! cls : CNLClass,
      canonicalCNLSelector t = some cls ∧
        cls ∈ t.available ∧
        ∀ other ∈ t.available,
          CNLClass.priorityRank cls <= CNLClass.priorityRank other :=
  data.selector.transitionClassifier ht

end CNLStandardSelectorEncodingInputData

namespace CNLStandardCleanVisibleEncodingInputData

/-- Rebuild the closed deterministic selector package from clean-visible
transition evidence. -/
def toCNLStandardSelectorEncodingInputData
    {cStar xi X : Real}
    (data : CNLStandardCleanVisibleEncodingInputData cStar xi X) :
    CNLStandardSelectorEncodingInputData cStar xi X :=
  CNLStandardSelectorEncodingInputData.ofClosedG6L1Standard
    data.transitions data.BNDHeight data.M data.shellFactor data.Ij
    data.clean_visible data.encoding_input

/-- Forget the standard clean-visible surface and recover the generic separated
CNL selector/encoding leaf. -/
def toCNLSelectorEncodingInputData
    {cStar xi X : Real}
    (data : CNLStandardCleanVisibleEncodingInputData cStar xi X) :
    CNLSelectorEncodingInputData cStar xi X :=
  data.toCNLStandardSelectorEncodingInputData.toCNLSelectorEncodingInputData

/-- Convert the standard clean-visible CNL leaf to grounded CNL local data. -/
def toGroundedCNLLocalData
    {cStar xi X : Real}
    (data : CNLStandardCleanVisibleEncodingInputData cStar xi X) :
    GroundedCNLLocalData cStar xi X :=
  data.toCNLStandardSelectorEncodingInputData.toGroundedCNLLocalData

/-- The only selector-side manuscript input left in the clean-visible CNL leaf. -/
theorem clean_visible_projected
    {cStar xi X : Real}
    (data : CNLStandardCleanVisibleEncodingInputData cStar xi X) :
    forall t, t ∈ data.transitions -> t.available.Nonempty :=
  data.clean_visible

/-- The deterministic priority classifier is recovered from the closed selector
skeleton after rebuilding the selector package. -/
theorem transitionClassifier
    {cStar xi X : Real}
    (data : CNLStandardCleanVisibleEncodingInputData cStar xi X)
    {t : CNLTransition} (ht : t ∈ data.transitions) :
    ∃! cls : CNLClass,
      canonicalCNLSelector t = some cls ∧
        cls ∈ t.available ∧
        ∀ other ∈ t.available,
          CNLClass.priorityRank cls <= CNLClass.priorityRank other := by
  exact
    data.toCNLStandardSelectorEncodingInputData.transitionClassifier
      (by
        simpa [toCNLStandardSelectorEncodingInputData,
          CNLStandardSelectorEncodingInputData.ofClosedG6L1Standard,
          CNLNormalFormSelectorData.ofCleanVisible] using ht)

end CNLStandardCleanVisibleEncodingInputData

namespace CNLStandardSelectedEncodingInputData

/-- Rebuild the closed deterministic selector package from the selected
transition family; clean visibility is automatic on that family. -/
def toCNLStandardSelectorEncodingInputData
    {cStar xi X : Real}
    (data : CNLStandardSelectedEncodingInputData cStar xi X) :
    CNLStandardSelectorEncodingInputData cStar xi X where
  selector := CNLNormalFormSelectorData.ofSelectedTransitions data.transitions
  BNDHeight := data.BNDHeight
  M := data.M
  shellFactor := data.shellFactor
  Ij := data.Ij
  encoding_input := by
    simpa [CNLNormalFormSelectorData.ofSelectedTransitions,
      CNLNormalFormSelectorData.ofCleanVisible,
      selectedTransitions_idempotent] using data.encoding_input

/-- Forget the standard selected-transition surface and recover the generic
separated CNL selector/encoding leaf. -/
def toCNLSelectorEncodingInputData
    {cStar xi X : Real}
    (data : CNLStandardSelectedEncodingInputData cStar xi X) :
    CNLSelectorEncodingInputData cStar xi X :=
  data.toCNLStandardSelectorEncodingInputData.toCNLSelectorEncodingInputData

/-- Convert the standard selected-transition CNL leaf to grounded CNL local
data. -/
def toGroundedCNLLocalData
    {cStar xi X : Real}
    (data : CNLStandardSelectedEncodingInputData cStar xi X) :
    GroundedCNLLocalData cStar xi X :=
  data.toCNLStandardSelectorEncodingInputData.toGroundedCNLLocalData

/-- Build the standard selected-transition CNL leaf from the finite counting
form of the weighted Kraft estimate.  This keeps the remaining manuscript
obligations exposed as a selected-family cardinality bound and the final
shell/interval arithmetic budget. -/
def ofNonnegativeHeightCardBound
    {cStar xi X : Real}
    (transitions : Finset CNLTransition)
    (BNDHeight : CNLTransition -> Real)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (height_nonneg :
      ∀ t, t ∈ selectedTransitions transitions -> 0 <= BNDHeight t)
    (card_bound :
      ((selectedTransitions transitions).card : Real) <= (2 : Real) ^ M)
    (manuscript_bound :
      (2 : Real) ^ M * (shellFactor : Real) * X * (Ij : Real) <=
        cStar * xi * X / 6) :
    CNLStandardSelectedEncodingInputData cStar xi X where
  transitions := transitions
  BNDHeight := BNDHeight
  M := M
  shellFactor := shellFactor
  Ij := Ij
  encoding_input :=
    GroundedCNLWeightedEncodingInput.ofNonnegativeHeightCardBound
      (paths := selectedTransitions transitions)
      (BNDHeight := BNDHeight)
      (c := (1 : Real)) (CQ := (2 : Real))
      (shellFactor := (shellFactor : Real)) (X := X) (Ij := (Ij : Real))
      (cStar := cStar) (xi := xi) (M := M)
      (by norm_num) height_nonneg card_bound manuscript_bound

/-- Build the standard selected-transition CNL leaf from the proof-v4
class/code/fibre counting route.  The selector-side partition and finite fibre
counting are closed in `CNL`; the remaining inputs are the manuscript code
budgets, nonnegative heights, and the final shell/interval budget. -/
def ofCodeBounds
    {cStar xi X : Real} {β : Type*} [DecidableEq β]
    (transitions : Finset CNLTransition)
    (BNDHeight : CNLTransition -> Real)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (code : CNLClass -> CNLTransition -> β)
    (codeBound fiberBound : CNLClass -> Nat)
    (height_nonneg :
      ∀ t, t ∈ selectedTransitions transitions -> 0 <= BNDHeight t)
    (hcodes :
      ∀ cls : CNLClass,
        ((transitionsSelectedAs transitions cls).image (code cls)).card <=
          codeBound cls)
    (hfiber :
      ∀ (cls : CNLClass) (y : β),
        y ∈ (transitionsSelectedAs transitions cls).image (code cls) ->
          ((transitionsSelectedAs transitions cls).filter
            fun t => code cls t = y).card <= fiberBound cls)
    (hcodeSum :
      (∑ cls : CNLClass, (codeBound cls : Real) * (fiberBound cls : Real)) <=
        (2 : Real) ^ M)
    (manuscript_bound :
      (2 : Real) ^ M * (shellFactor : Real) * X * (Ij : Real) <=
        cStar * xi * X / 6) :
    CNLStandardSelectedEncodingInputData cStar xi X :=
  ofNonnegativeHeightCardBound transitions BNDHeight M shellFactor Ij
    height_nonneg
    ((real_selectedTransitions_card_le_sum_code_bounds
      (transitions := transitions) (code := code) hcodes hfiber).trans
        hcodeSum)
    manuscript_bound

/-- Build the standard selected-transition CNL leaf from class-local code/fibre
budgets.  This is the form closest to L.1.2's separated class analysis: each
class supplies its own code/fibre budget, and the only global arithmetic is the
sum of those budgets. -/
def ofCodeClassBudgets
    {cStar xi X : Real} {β : Type*} [DecidableEq β]
    (transitions : Finset CNLTransition)
    (BNDHeight : CNLTransition -> Real)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (code : CNLClass -> CNLTransition -> β)
    (codeBound fiberBound : CNLClass -> Nat)
    (classBudget : CNLClass -> Real)
    (height_nonneg :
      ∀ t, t ∈ selectedTransitions transitions -> 0 <= BNDHeight t)
    (hcodes :
      ∀ cls : CNLClass,
        ((transitionsSelectedAs transitions cls).image (code cls)).card <=
          codeBound cls)
    (hfiber :
      ∀ (cls : CNLClass) (y : β),
        y ∈ (transitionsSelectedAs transitions cls).image (code cls) ->
          ((transitionsSelectedAs transitions cls).filter
            fun t => code cls t = y).card <= fiberBound cls)
    (hclassBudget :
      ∀ cls : CNLClass,
        (codeBound cls : Real) * (fiberBound cls : Real) <= classBudget cls)
    (hbudgetSum :
      (∑ cls : CNLClass, classBudget cls) <= (2 : Real) ^ M)
    (manuscript_bound :
      (2 : Real) ^ M * (shellFactor : Real) * X * (Ij : Real) <=
        cStar * xi * X / 6) :
    CNLStandardSelectedEncodingInputData cStar xi X := by
  have hcodeSum :
      (∑ cls : CNLClass, (codeBound cls : Real) * (fiberBound cls : Real)) <=
        (2 : Real) ^ M := by
    exact
      (Finset.sum_le_sum (fun cls _hcls => hclassBudget cls)).trans
        hbudgetSum
  exact
    ofCodeBounds transitions BNDHeight M shellFactor Ij code codeBound
      fiberBound height_nonneg hcodes hfiber hcodeSum manuscript_bound

/-- Nat-valued BND heights close the height-nonnegativity side of the
class/code/fibre CNL constructor. -/
def ofNatHeightCodeBounds
    {cStar xi X : Real} {β : Type*} [DecidableEq β]
    (transitions : Finset CNLTransition)
    (BNDHeightNat : CNLTransition -> Nat)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (code : CNLClass -> CNLTransition -> β)
    (codeBound fiberBound : CNLClass -> Nat)
    (hcodes :
      ∀ cls : CNLClass,
        ((transitionsSelectedAs transitions cls).image (code cls)).card <=
          codeBound cls)
    (hfiber :
      ∀ (cls : CNLClass) (y : β),
        y ∈ (transitionsSelectedAs transitions cls).image (code cls) ->
          ((transitionsSelectedAs transitions cls).filter
            fun t => code cls t = y).card <= fiberBound cls)
    (hcodeSum :
      (∑ cls : CNLClass, (codeBound cls : Real) * (fiberBound cls : Real)) <=
        (2 : Real) ^ M)
    (manuscript_bound :
      (2 : Real) ^ M * (shellFactor : Real) * X * (Ij : Real) <=
        cStar * xi * X / 6) :
    CNLStandardSelectedEncodingInputData cStar xi X :=
  ofCodeBounds transitions (fun t => (BNDHeightNat t : Real)) M shellFactor Ij
    code codeBound fiberBound
    (fun t _ht => Nat.cast_nonneg (BNDHeightNat t))
    hcodes hfiber hcodeSum manuscript_bound

/-- Nat-valued BND heights and class-local budgets give the most separated
current L.1.2 constructor: only the class-local code/fibre estimates and the
global class-budget sum remain as manuscript inputs. -/
def ofNatHeightCodeClassBudgets
    {cStar xi X : Real} {β : Type*} [DecidableEq β]
    (transitions : Finset CNLTransition)
    (BNDHeightNat : CNLTransition -> Nat)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (code : CNLClass -> CNLTransition -> β)
    (codeBound fiberBound : CNLClass -> Nat)
    (classBudget : CNLClass -> Real)
    (hcodes :
      ∀ cls : CNLClass,
        ((transitionsSelectedAs transitions cls).image (code cls)).card <=
          codeBound cls)
    (hfiber :
      ∀ (cls : CNLClass) (y : β),
        y ∈ (transitionsSelectedAs transitions cls).image (code cls) ->
          ((transitionsSelectedAs transitions cls).filter
            fun t => code cls t = y).card <= fiberBound cls)
    (hclassBudget :
      ∀ cls : CNLClass,
        (codeBound cls : Real) * (fiberBound cls : Real) <= classBudget cls)
    (hbudgetSum :
      (∑ cls : CNLClass, classBudget cls) <= (2 : Real) ^ M)
    (manuscript_bound :
      (2 : Real) ^ M * (shellFactor : Real) * X * (Ij : Real) <=
        cStar * xi * X / 6) :
    CNLStandardSelectedEncodingInputData cStar xi X :=
  ofCodeClassBudgets transitions (fun t => (BNDHeightNat t : Real)) M
    shellFactor Ij code codeBound fiberBound classBudget
    (fun t _ht => Nat.cast_nonneg (BNDHeightNat t))
    hcodes hfiber hclassBudget hbudgetSum manuscript_bound

/-- Same as `ofNatHeightCodeClassBudgets`, but with the final CNL arithmetic
budget supplied in the `X`-free scalar form used in the manuscript. -/
def ofNatHeightCodeClassBudgetsScalar
    {cStar xi X : Real} {β : Type*} [DecidableEq β]
    (transitions : Finset CNLTransition)
    (BNDHeightNat : CNLTransition -> Nat)
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (code : CNLClass -> CNLTransition -> β)
    (codeBound fiberBound : CNLClass -> Nat)
    (classBudget : CNLClass -> Real)
    (hX_nonneg : 0 <= X)
    (hcodes :
      ∀ cls : CNLClass,
        ((transitionsSelectedAs transitions cls).image (code cls)).card <=
          codeBound cls)
    (hfiber :
      ∀ (cls : CNLClass) (y : β),
        y ∈ (transitionsSelectedAs transitions cls).image (code cls) ->
          ((transitionsSelectedAs transitions cls).filter
            fun t => code cls t = y).card <= fiberBound cls)
    (hclassBudget :
      ∀ cls : CNLClass,
        (codeBound cls : Real) * (fiberBound cls : Real) <= classBudget cls)
    (hbudgetSum :
      (∑ cls : CNLClass, classBudget cls) <= (2 : Real) ^ M)
    (scalar_budget :
      (2 : Real) ^ M * (shellFactor : Real) * (Ij : Real) <=
        cStar * xi / 6) :
    CNLStandardSelectedEncodingInputData cStar xi X :=
  ofNatHeightCodeClassBudgets transitions BNDHeightNat M shellFactor Ij code
    codeBound fiberBound classBudget hcodes hfiber hclassBudget hbudgetSum
    (GroundedCNLWeightedEncodingInput.shellIntervalBudget_of_scalarBudget
      (M := M) hX_nonneg scalar_budget)

/-- The selected-transition CNL leaf recovers clean visibility on the selected
family without an external provider field. -/
theorem clean_visible_selected
    {cStar xi X : Real}
    (data : CNLStandardSelectedEncodingInputData cStar xi X) :
    forall t, t ∈ selectedTransitions data.transitions -> t.available.Nonempty :=
  fun _t ht => available_nonempty_of_mem_selectedTransitions ht

/-- The deterministic priority classifier is recovered from the closed selector
skeleton after rebuilding it on the selected transition family. -/
theorem transitionClassifier
    {cStar xi X : Real}
    (data : CNLStandardSelectedEncodingInputData cStar xi X)
    {t : CNLTransition} (ht : t ∈ selectedTransitions data.transitions) :
    ∃! cls : CNLClass,
      canonicalCNLSelector t = some cls ∧
        cls ∈ t.available ∧
        ∀ other ∈ t.available,
          CNLClass.priorityRank cls <= CNLClass.priorityRank other := by
  exact
    data.toCNLStandardSelectorEncodingInputData.transitionClassifier
      (by
        simpa [toCNLStandardSelectorEncodingInputData,
          CNLNormalFormSelectorData.ofSelectedTransitions,
          CNLNormalFormSelectorData.ofCleanVisible] using ht)

end CNLStandardSelectedEncodingInputData

namespace CNLStandardNatHeightCodeClassScalarInputData

/-- Build the standard selected-transition encoding leaf from the proof-v4
Nat-height, class-local code/fibre budgets, and X-free scalar budget. -/
def toCNLStandardSelectedEncodingInputData
    {cStar xi X : Real}
    (data : CNLStandardNatHeightCodeClassScalarInputData cStar xi X) :
    CNLStandardSelectedEncodingInputData cStar xi X := by
  letI : DecidableEq data.Code := data.decCode
  exact
    CNLStandardSelectedEncodingInputData.ofNatHeightCodeClassBudgetsScalar
      data.transitions data.BNDHeightNat data.M data.shellFactor data.Ij
      data.code data.codeBound data.fiberBound data.classBudget
      data.hX_nonneg data.hcodes data.hfiber data.hclassBudget
      data.hbudgetSum data.scalar_budget

/-- Convert the proof-v4 code-budget CNL leaf to grounded CNL local data. -/
def toGroundedCNLLocalData
    {cStar xi X : Real}
    (data : CNLStandardNatHeightCodeClassScalarInputData cStar xi X) :
    GroundedCNLLocalData cStar xi X :=
  data.toCNLStandardSelectedEncodingInputData.toGroundedCNLLocalData

/-- Compatibility projection to the selector/encoding leaf. -/
def toCNLSelectorEncodingInputData
    {cStar xi X : Real}
    (data : CNLStandardNatHeightCodeClassScalarInputData cStar xi X) :
    CNLSelectorEncodingInputData cStar xi X :=
  data.toCNLStandardSelectedEncodingInputData.toCNLSelectorEncodingInputData

end CNLStandardNatHeightCodeClassScalarInputData

namespace CNLStandardNatHeightCodeBoundsScalarInputData

/-- Build the standard selected-transition encoding leaf from direct
class-local code/fibre bounds and the X-free scalar shell budget. -/
def toCNLStandardSelectedEncodingInputData
    {cStar xi X : Real}
    (data : CNLStandardNatHeightCodeBoundsScalarInputData cStar xi X) :
    CNLStandardSelectedEncodingInputData cStar xi X := by
  letI : DecidableEq data.Code := data.decCode
  exact
    CNLStandardSelectedEncodingInputData.ofNatHeightCodeBounds
      data.transitions data.BNDHeightNat data.M data.shellFactor data.Ij
      data.code data.codeBound data.fiberBound
      data.hcodes data.hfiber data.hcodeSum
      (GroundedCNLWeightedEncodingInput.shellIntervalBudget_of_scalarBudget
        (M := data.M) data.hX_nonneg data.scalar_budget)

/-- Convert the direct code/fibre budget CNL leaf to grounded CNL local data. -/
def toGroundedCNLLocalData
    {cStar xi X : Real}
    (data : CNLStandardNatHeightCodeBoundsScalarInputData cStar xi X) :
    GroundedCNLLocalData cStar xi X :=
  data.toCNLStandardSelectedEncodingInputData.toGroundedCNLLocalData

/-- Compatibility projection to the selector/encoding leaf. -/
def toCNLSelectorEncodingInputData
    {cStar xi X : Real}
    (data : CNLStandardNatHeightCodeBoundsScalarInputData cStar xi X) :
    CNLSelectorEncodingInputData cStar xi X :=
  data.toCNLStandardSelectedEncodingInputData.toCNLSelectorEncodingInputData

end CNLStandardNatHeightCodeBoundsScalarInputData

/-- Recover the G.6/L.1 selector-budget leaf carried by grounded CNL data. -/
def GroundedCNLLocalData.toSelectorBudgetInputData
    {cStar xi X : Real}
    (data : GroundedCNLLocalData cStar xi X) :
    CNLSelectorBudgetInputData cStar xi X where
  selector := data.selector
  BNDHeight := data.BNDHeight
  c := data.c
  CQ := data.CQ
  M := data.M
  shellFactor := data.shellFactor
  Ij := data.Ij
  encoding_input := data.encoding_input

/-- Build grounded CNL data from the only selector-side manuscript input:
every surviving clean transition is visible to at least one priority class.
The deterministic priority scan and exact normal-form coherence are closed by
`CNLNormalFormSelectorData.ofCleanVisible`. -/
def GroundedCNLLocalData.ofCleanVisible
    {cStar xi X : Real}
    (transitions : Finset CNLTransition)
    (BNDHeight : CNLTransition -> Real)
    (c : {c : Real // 0 < c})
    (CQ : {CQ : Real // (1 - (2 : Real) ^ (-(c : Real)))⁻¹ <= CQ})
    (M : Nat)
    (shellFactor : {x : Real // 0 <= x})
    (Ij : {x : Real // 0 <= x})
    (clean_visible : ∀ t ∈ transitions, t.available.Nonempty)
    (encoding_input :
      GroundedCNLWeightedEncodingInput
        (selectedTransitions transitions) BNDHeight (c : Real) (CQ : Real)
        (shellFactor : Real) X (Ij : Real) cStar xi M) :
    GroundedCNLLocalData cStar xi X where
  selector := CNLNormalFormSelectorData.ofCleanVisible transitions clean_visible
  BNDHeight := BNDHeight
  c := c
  CQ := CQ
  M := M
  shellFactor := shellFactor
  Ij := Ij
  encoding_input := encoding_input

/-- The remaining selector-side content in grounded CNL data: each clean
transition has at least one available priority class. -/
theorem GroundedCNLLocalData.clean_visible
    {cStar xi X : Real} (data : GroundedCNLLocalData cStar xi X) :
    ∀ t ∈ data.selector.transitions, t.available.Nonempty :=
  data.selector.clean_visible

/-- The selected CNL class exists for every clean visible transition in grounded
CNL data. -/
theorem GroundedCNLLocalData.exists_selected
    {cStar xi X : Real} (data : GroundedCNLLocalData cStar xi X)
    {t : CNLTransition} (ht : t ∈ data.selector.transitions) :
    ∃ cls : CNLClass, canonicalCNLSelector t = some cls :=
  data.selector.exists_selected ht

/-- The exact normal form of a selected transition is one of the two manuscript
normal forms. -/
theorem GroundedCNLLocalData.selected_normalFormCoherent
    {cStar xi X : Real} (data : GroundedCNLLocalData cStar xi X)
    {t : CNLTransition} (ht : t ∈ data.selector.transitions) {cls : CNLClass}
    (hsel : canonicalCNLSelector t = some cls) :
    t.normalForm = CNLNormalForm.positiveLift ∨
      t.normalForm = CNLNormalForm.childResidue :=
  data.selector.selected_normalFormCoherent ht hsel

/-- The closed deterministic priority classifier projected from grounded CNL
data. -/
theorem GroundedCNLLocalData.transitionClassifier
    {cStar xi X : Real} (data : GroundedCNLLocalData cStar xi X)
    {t : CNLTransition} (ht : t ∈ data.selector.transitions) :
    ∃! cls : CNLClass,
      canonicalCNLSelector t = some cls ∧
        cls ∈ t.available ∧
        ∀ other ∈ t.available,
          CNLClass.priorityRank cls <= CNLClass.priorityRank other :=
  data.selector.transitionClassifier ht

/-- The entropy exponent carried by grounded CNL data is positive by type. -/
theorem GroundedCNLLocalData.c_pos
    {cStar xi X : Real} (data : GroundedCNLLocalData cStar xi X) :
    0 < (data.c : Real) :=
  data.c.property

/-- The grounded CNL `C_Q` constant dominates the one-step entropy denominator by type. -/
theorem GroundedCNLLocalData.CQ_dom
    {cStar xi X : Real} (data : GroundedCNLLocalData cStar xi X) :
    (1 - (2 : Real) ^ (-(data.c : Real)))⁻¹ <= (data.CQ : Real) :=
  data.CQ.property

/-- The real-valued grounded CNL `C_Q` constant. -/
def GroundedCNLLocalData.CQReal
    {cStar xi X : Real} (data : GroundedCNLLocalData cStar xi X) : Real :=
  data.CQ

/-- The real-valued CNL shell factor carried by grounded CNL data. -/
def GroundedCNLLocalData.shellFactorReal
    {cStar xi X : Real} (data : GroundedCNLLocalData cStar xi X) : Real :=
  data.shellFactor

/-- The real-valued interval length factor carried by grounded CNL data. -/
def GroundedCNLLocalData.IjReal
    {cStar xi X : Real} (data : GroundedCNLLocalData cStar xi X) : Real :=
  data.Ij

/-- The CNL shell factor is nonnegative by type. -/
theorem GroundedCNLLocalData.shellFactor_nonneg
    {cStar xi X : Real} (data : GroundedCNLLocalData cStar xi X) :
    0 <= data.shellFactorReal :=
  data.shellFactor.property

/-- The CNL interval factor is nonnegative by type. -/
theorem GroundedCNLLocalData.Ij_nonneg
    {cStar xi X : Real} (data : GroundedCNLLocalData cStar xi X) :
    0 <= data.IjReal :=
  data.Ij.property

/-- Project the final shell/interval CNL budget carried by grounded CNL data. -/
def GroundedCNLLocalData.budgetData
    {cStar xi X : Real} (data : GroundedCNLLocalData cStar xi X) :
    CNLClusterBudgetData data.CQReal data.shellFactorReal X data.IjReal cStar xi
      data.M where
  manuscript_bound := by
    simpa [GroundedCNLLocalData.CQReal, GroundedCNLLocalData.shellFactorReal,
      GroundedCNLLocalData.IjReal] using data.encoding_input.manuscript_bound

/-- Proof-v4 G.35/L.1w weighted entropy certificate for the selected clean CNL
transition family. -/
def GroundedCNLLocalData.weightedEntropy
    {cStar xi X : Real} (data : GroundedCNLLocalData cStar xi X) :
    CNLWeightedEntropyData
      (selectedTransitions data.selector.transitions) data.BNDHeight data.c data.CQReal
      data.shellFactorReal X data.IjReal cStar xi data.M where
  c_pos := data.c_pos
  kraftSum_le := by
    simpa [GroundedCNLLocalData.CQReal] using data.encoding_input.kraftSum_le
  manuscript_bound := by
    simpa [GroundedCNLLocalData.CQReal, GroundedCNLLocalData.shellFactorReal,
      GroundedCNLLocalData.IjReal] using data.encoding_input.manuscript_bound

/--
The L.1.2 / G.35 Kraft estimate for the selected clean CNL transition family.

This names the fact that the final entropy package is fed by
`selectedTransitions selector.transitions`, not by an arbitrary path set.
-/
theorem GroundedCNLLocalData.kraftSum_le
    {cStar xi X : Real} (data : GroundedCNLLocalData cStar xi X) :
    cleanCNLKraftSum
        (selectedTransitions data.selector.transitions) data.BNDHeight data.c <=
      data.CQReal ^ data.M :=
  data.weightedEntropy.kraft_bound

/-- The weighted CNL cluster contribution after the Kraft estimate and shell factors. -/
theorem GroundedCNLLocalData.manuscript_bound
    {cStar xi X : Real} (data : GroundedCNLLocalData cStar xi X) :
    data.CQReal ^ data.M * data.shellFactorReal * X * data.IjReal <=
      cStar * xi * X / 6 :=
  data.weightedEntropy.weighted_bound

/-- Convert selector-based CNL data into the existing cluster-encoding package. -/
def GroundedCNLLocalData.toCNLClusterEncodingData
    {cStar xi X : Real}
    (data : GroundedCNLLocalData cStar xi X) :
    CNLClusterEncodingData cStar xi X :=
  CNLClusterEncodingData.ofWeightedEntropy
    (selectedTransitions data.selector.transitions) data.BNDHeight
    data.c data.CQReal data.M data.shellFactorReal data.IjReal
    data.shellFactor_nonneg data.Ij_nonneg data.weightedEntropy

/-- Final selected-transition CNL entropy bound for the grounded local data. -/
theorem GroundedCNLLocalData.cnl_bound
    {cStar xi X : Real}
    (data : GroundedCNLLocalData cStar xi X)
    (hX_nonneg : 0 <= X) :
    ∃ CleanTerm : Real,
      0 <= CleanTerm ∧ CleanTerm <= cStar * xi * X / 6 :=
  cnlEntropy_of_clusterEncoding data.toCNLClusterEncodingData hX_nonneg

namespace CNLSelectorBudgetInputData

/-- Final selected-transition CNL entropy bound projected directly from the selector leaf. -/
theorem cnl_bound
    {cStar xi X : Real}
    (data : CNLSelectorBudgetInputData cStar xi X)
    (hX_nonneg : 0 <= X) :
    ∃ CleanTerm : Real,
      0 <= CleanTerm ∧ CleanTerm <= cStar * xi * X / 6 :=
  data.toGroundedCNLLocalData.cnl_bound hX_nonneg

end CNLSelectorBudgetInputData

namespace CNLSelectorEncodingInputData

/-- Final selected-transition CNL entropy bound projected from the separated
selector/encoding leaf. -/
theorem cnl_bound
    {cStar xi X : Real}
    (data : CNLSelectorEncodingInputData cStar xi X)
    (hX_nonneg : 0 <= X) :
    ∃ CleanTerm : Real,
      0 <= CleanTerm ∧ CleanTerm <= cStar * xi * X / 6 :=
  data.toGroundedCNLLocalData.cnl_bound hX_nonneg

end CNLSelectorEncodingInputData

namespace CNLStandardNatHeightCodeClassScalarInputData

/-- Final selected-transition CNL entropy bound projected from the proof-v4
code-budget leaf. -/
theorem cnl_bound
    {cStar xi X : Real}
    (data : CNLStandardNatHeightCodeClassScalarInputData cStar xi X) :
    ∃ CleanTerm : Real,
      0 <= CleanTerm ∧ CleanTerm <= cStar * xi * X / 6 :=
  data.toGroundedCNLLocalData.cnl_bound data.hX_nonneg

end CNLStandardNatHeightCodeClassScalarInputData

namespace CNLStandardNatHeightCodeBoundsScalarInputData

/-- Final selected-transition CNL entropy bound projected from the direct
code/fibre budget leaf. -/
theorem cnl_bound
    {cStar xi X : Real}
    (data : CNLStandardNatHeightCodeBoundsScalarInputData cStar xi X) :
    ∃ CleanTerm : Real,
      0 <= CleanTerm ∧ CleanTerm <= cStar * xi * X / 6 :=
  data.toGroundedCNLLocalData.cnl_bound data.hX_nonneg

end CNLStandardNatHeightCodeBoundsScalarInputData

namespace CNLStandardNatHeightCodeBoundsNatBudgetScalarInputData

/-- Forget the Nat-valued product-sum budget to the previous Real-valued CNL
leaf.  The cast is pure bookkeeping: the underlying estimate is the same finite
class-local code/fibre count. -/
def toCNLStandardNatHeightCodeBoundsScalarInputData
    {cStar xi X : Real}
    (data : CNLStandardNatHeightCodeBoundsNatBudgetScalarInputData cStar xi X) :
    CNLStandardNatHeightCodeBoundsScalarInputData cStar xi X where
  Code := data.Code
  decCode := data.decCode
  transitions := data.transitions
  BNDHeightNat := data.BNDHeightNat
  M := data.M
  shellFactor := data.shellFactor
  Ij := data.Ij
  code := data.code
  codeBound := data.codeBound
  fiberBound := data.fiberBound
  hX_nonneg := data.hX_nonneg
  hcodes := data.hcodes
  hfiber := data.hfiber
  hcodeSum := by
    exact_mod_cast data.hcodeSumNat
  scalar_budget := data.scalar_budget

/-- Build the standard selected-transition encoding leaf from the Nat-budget
direct code/fibre CNL leaf. -/
def toCNLStandardSelectedEncodingInputData
    {cStar xi X : Real}
    (data : CNLStandardNatHeightCodeBoundsNatBudgetScalarInputData cStar xi X) :
    CNLStandardSelectedEncodingInputData cStar xi X :=
  data.toCNLStandardNatHeightCodeBoundsScalarInputData.toCNLStandardSelectedEncodingInputData

/-- Convert the Nat-budget direct code/fibre CNL leaf to grounded CNL data. -/
def toGroundedCNLLocalData
    {cStar xi X : Real}
    (data : CNLStandardNatHeightCodeBoundsNatBudgetScalarInputData cStar xi X) :
    GroundedCNLLocalData cStar xi X :=
  data.toCNLStandardNatHeightCodeBoundsScalarInputData.toGroundedCNLLocalData

/-- Compatibility projection to the selector/encoding leaf. -/
def toCNLSelectorEncodingInputData
    {cStar xi X : Real}
    (data : CNLStandardNatHeightCodeBoundsNatBudgetScalarInputData cStar xi X) :
    CNLSelectorEncodingInputData cStar xi X :=
  data.toCNLStandardNatHeightCodeBoundsScalarInputData.toCNLSelectorEncodingInputData

/-- Final selected-transition CNL entropy bound projected from the Nat-budget
direct code/fibre leaf. -/
theorem cnl_bound
    {cStar xi X : Real}
    (data : CNLStandardNatHeightCodeBoundsNatBudgetScalarInputData cStar xi X) :
    ∃ CleanTerm : Real,
      0 <= CleanTerm ∧ CleanTerm <= cStar * xi * X / 6 :=
  data.toGroundedCNLLocalData.cnl_bound data.hX_nonneg

end CNLStandardNatHeightCodeBoundsNatBudgetScalarInputData

namespace CNLStandardWeightedKraftShellInputData

/-- Build the standard selected-transition encoding leaf from the direct
L.1.2 weighted-Kraft shell leaf. -/
def toCNLStandardSelectedEncodingInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellInputData shell cStar xi) :
    CNLStandardSelectedEncodingInputData cStar xi (shell.X : Real) where
  transitions := data.transitions
  BNDHeight := fun t => (data.BNDHeightNat t : Real)
  M := data.M
  shellFactor := data.shellFactor
  Ij := data.Ij
  encoding_input := {
    kraftSum_le := data.kraftSum_le
    manuscript_bound :=
      GroundedCNLWeightedEncodingInput.shellIntervalBudget_of_scalarBudget
        (M := data.M) (Nat.cast_nonneg shell.X) data.scalar_budget }

/-- Convert the direct L.1.2 weighted-Kraft shell leaf to grounded CNL data. -/
def toGroundedCNLLocalData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellInputData shell cStar xi) :
    GroundedCNLLocalData cStar xi (shell.X : Real) :=
  data.toCNLStandardSelectedEncodingInputData.toGroundedCNLLocalData

/-- Compatibility projection to the selector/encoding leaf. -/
def toCNLSelectorEncodingInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellInputData shell cStar xi) :
    CNLSelectorEncodingInputData cStar xi (shell.X : Real) :=
  data.toCNLStandardSelectedEncodingInputData.toCNLSelectorEncodingInputData

/-- Final selected-transition CNL entropy bound projected from the direct
weighted-Kraft shell leaf. -/
theorem cnl_bound
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellInputData shell cStar xi) :
    ∃ CleanTerm : Real,
      0 <= CleanTerm ∧ CleanTerm <= cStar * xi * (shell.X : Real) / 6 :=
  data.toGroundedCNLLocalData.cnl_bound (Nat.cast_nonneg shell.X)

end CNLStandardWeightedKraftShellInputData

namespace CNLStandardWeightedKraftShellManuscriptInputData

/-- Cancel the positive shell size in the manuscript L.1.2/G.35 shell budget. -/
def toCNLStandardWeightedKraftShellInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellManuscriptInputData shell cStar xi) :
    CNLStandardWeightedKraftShellInputData shell cStar xi where
  transitions := data.transitions
  BNDHeightNat := data.BNDHeightNat
  M := data.M
  shellFactor := data.shellFactor
  Ij := data.Ij
  kraftSum_le := data.kraftSum_le
  scalar_budget := by
    have hX_pos : 0 < (shell.X : Real) := shell.X_pos_real
    have hbudget := data.manuscript_budget
    have hbudget' :
        ((2 : Real) ^ data.M * (data.shellFactor : Real) *
            (data.Ij : Real)) * (shell.X : Real) <=
          (cStar * xi / 6) * (shell.X : Real) := by
      calc
        ((2 : Real) ^ data.M * (data.shellFactor : Real) *
            (data.Ij : Real)) * (shell.X : Real)
            =
          (2 : Real) ^ data.M * (data.shellFactor : Real) *
              (shell.X : Real) * (data.Ij : Real) := by ring
        _ <= cStar * xi * (shell.X : Real) / 6 := hbudget
        _ = (cStar * xi / 6) * (shell.X : Real) := by ring
    exact le_of_mul_le_mul_right hbudget' hX_pos

/-- Convert the manuscript-budget weighted-Kraft shell leaf to grounded CNL data. -/
def toGroundedCNLLocalData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellManuscriptInputData shell cStar xi) :
    GroundedCNLLocalData cStar xi (shell.X : Real) :=
  data.toCNLStandardWeightedKraftShellInputData.toGroundedCNLLocalData

/-- Compatibility projection to the selector/encoding leaf. -/
def toCNLSelectorEncodingInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellManuscriptInputData shell cStar xi) :
    CNLSelectorEncodingInputData cStar xi (shell.X : Real) :=
  data.toCNLStandardWeightedKraftShellInputData.toCNLSelectorEncodingInputData

/-- Final selected-transition CNL entropy bound projected from the manuscript
weighted-Kraft shell leaf. -/
theorem cnl_bound
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellManuscriptInputData shell cStar xi) :
    ∃ CleanTerm : Real,
      0 <= CleanTerm ∧ CleanTerm <= cStar * xi * (shell.X : Real) / 6 :=
  data.toGroundedCNLLocalData.cnl_bound (Nat.cast_nonneg shell.X)

end CNLStandardWeightedKraftShellManuscriptInputData

namespace CNLStandardWeightedKraftShellClusterInputData

/-- Upgrade the L.1.2 cluster-to-ladder CNL leaf to the proof-object shell
leaf consumed by the strongest Appendix N certificate boundary. -/
def toCNLStandardWeightedKraftShellProofInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellClusterInputData shell cStar xi) :
    CNLStandardWeightedKraftShellProofInputData shell cStar xi where
  transitions := data.transitions
  BNDHeightNat := data.BNDHeightNat
  M := data.M
  shellFactor := data.shellFactor
  Ij := data.Ij
  encodingProof :=
    CNLClusterEncodingProof.ofStandardConstants
      data.ladderChildren data.ladderHeight data.ladderRoot
      (by norm_num : (1 : Real) <= 1)
      (by norm_num : (2 : Real) <= 2)
      data.ladderHeight_dom
      data.cluster_le_pathKraft
      data.manuscript_budget

/-- Convert the L.1.2 cluster-to-ladder CNL leaf to the direct manuscript
weighted-Kraft shell leaf, closing the abstract G.2/G.6 ladder iteration. -/
def toCNLStandardWeightedKraftShellManuscriptInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellClusterInputData shell cStar xi) :
    CNLStandardWeightedKraftShellManuscriptInputData shell cStar xi where
  transitions := data.transitions
  BNDHeightNat := data.BNDHeightNat
  M := data.M
  shellFactor := data.shellFactor
  Ij := data.Ij
  kraftSum_le := by
    simpa using
      CNLClusterEncodingProof.kraftSum_le
        data.toCNLStandardWeightedKraftShellProofInputData.encodingProof
  manuscript_budget := data.manuscript_budget

/-- Convert the L.1.2 cluster-to-ladder CNL leaf to grounded CNL data. -/
def toGroundedCNLLocalData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellClusterInputData shell cStar xi) :
    GroundedCNLLocalData cStar xi (shell.X : Real) :=
  data.toCNLStandardWeightedKraftShellManuscriptInputData.toGroundedCNLLocalData

/-- Compatibility projection to the selector/encoding leaf. -/
def toCNLSelectorEncodingInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellClusterInputData shell cStar xi) :
    CNLSelectorEncodingInputData cStar xi (shell.X : Real) :=
  data.toCNLStandardWeightedKraftShellManuscriptInputData.toCNLSelectorEncodingInputData

/-- Final selected-transition CNL entropy bound projected from the L.1.2
cluster-to-ladder shell leaf. -/
theorem cnl_bound
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellClusterInputData shell cStar xi) :
    ∃ CleanTerm : Real,
      0 <= CleanTerm ∧ CleanTerm <= cStar * xi * (shell.X : Real) / 6 :=
  data.toGroundedCNLLocalData.cnl_bound (Nat.cast_nonneg shell.X)

end CNLStandardWeightedKraftShellClusterInputData

namespace CNLStandardWeightedKraftShellProofInputData

/-- Forget the proof-object packaging to the previous cluster-to-ladder shell
leaf. -/
def toCNLStandardWeightedKraftShellClusterInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellProofInputData shell cStar xi) :
    CNLStandardWeightedKraftShellClusterInputData shell cStar xi where
  transitions := data.transitions
  BNDHeightNat := data.BNDHeightNat
  M := data.M
  shellFactor := data.shellFactor
  Ij := data.Ij
  ladderChildren := data.encodingProof.ladderChildren
  ladderHeight := data.encodingProof.ladderHeight
  ladderRoot := data.encodingProof.ladderRoot
  ladderHeight_dom := data.encodingProof.ladderHeight_dom
  cluster_le_pathKraft := by
    simpa using data.encodingProof.cluster_le_pathKraft
  manuscript_budget := by
    simpa using data.encodingProof.manuscript_bound

/-- Convert the proof-object CNL leaf to grounded CNL data. -/
def toGroundedCNLLocalData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellProofInputData shell cStar xi) :
    GroundedCNLLocalData cStar xi (shell.X : Real) :=
  data.toCNLStandardWeightedKraftShellClusterInputData.toGroundedCNLLocalData

/-- Compatibility projection to the selector/encoding leaf. -/
def toCNLSelectorEncodingInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellProofInputData shell cStar xi) :
    CNLSelectorEncodingInputData cStar xi (shell.X : Real) :=
  data.toCNLStandardWeightedKraftShellClusterInputData.toCNLSelectorEncodingInputData

/-- Final CNL entropy bound projected from the proof-object shell leaf. -/
theorem cnl_bound
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellProofInputData shell cStar xi) :
    ∃ CleanTerm : Real,
      0 <= CleanTerm ∧ CleanTerm <= cStar * xi * (shell.X : Real) / 6 :=
  data.toGroundedCNLLocalData.cnl_bound (Nat.cast_nonneg shell.X)

end CNLStandardWeightedKraftShellProofInputData

namespace CNLStandardWeightedKraftShellInputData

/-- Reinsert the positive shell factor and view the X-free shell leaf in the
manuscript scalar-budget form. -/
def toCNLStandardWeightedKraftShellManuscriptInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : CNLStandardWeightedKraftShellInputData shell cStar xi) :
    CNLStandardWeightedKraftShellManuscriptInputData shell cStar xi where
  transitions := data.transitions
  BNDHeightNat := data.BNDHeightNat
  M := data.M
  shellFactor := data.shellFactor
  Ij := data.Ij
  kraftSum_le := data.kraftSum_le
  manuscript_budget := by
    have hX_nonneg : 0 <= (shell.X : Real) := Nat.cast_nonneg shell.X
    have hmul := mul_le_mul_of_nonneg_right data.scalar_budget hX_nonneg
    calc
      (2 : Real) ^ data.M * (data.shellFactor : Real) *
          (shell.X : Real) * (data.Ij : Real)
          =
        ((2 : Real) ^ data.M * (data.shellFactor : Real) *
            (data.Ij : Real)) * (shell.X : Real) := by ring
      _ <= (cStar * xi / 6) * (shell.X : Real) := hmul
      _ = cStar * xi * (shell.X : Real) / 6 := by ring

end CNLStandardWeightedKraftShellInputData

namespace CNLStandardNatHeightCodeBoundsNatBudgetShellInputData

/-- Forget the shell-tied CNL leaf to the generic Nat-budget scalar leaf, closing
`0 <= X` from the natural shell size. -/
def toCNLStandardNatHeightCodeBoundsNatBudgetScalarInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data :
      CNLStandardNatHeightCodeBoundsNatBudgetShellInputData shell cStar xi) :
    CNLStandardNatHeightCodeBoundsNatBudgetScalarInputData cStar xi
      (shell.X : Real) where
  Code := data.Code
  decCode := data.decCode
  transitions := data.transitions
  BNDHeightNat := data.BNDHeightNat
  M := data.M
  shellFactor := data.shellFactor
  Ij := data.Ij
  code := data.code
  codeBound := data.codeBound
  fiberBound := data.fiberBound
  hX_nonneg := Nat.cast_nonneg shell.X
  hcodes := data.hcodes
  hfiber := data.hfiber
  hcodeSumNat := data.hcodeSumNat
  scalar_budget := data.scalar_budget

/-- Build the standard selected-transition encoding leaf from the shell-tied
Nat-budget CNL leaf. -/
def toCNLStandardSelectedEncodingInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data :
      CNLStandardNatHeightCodeBoundsNatBudgetShellInputData shell cStar xi) :
    CNLStandardSelectedEncodingInputData cStar xi (shell.X : Real) :=
  data.toCNLStandardNatHeightCodeBoundsNatBudgetScalarInputData
    |>.toCNLStandardSelectedEncodingInputData

/-- Forget the concrete code/fibre proof witness to the direct L.1.2
weighted-Kraft shell leaf. -/
def toCNLStandardWeightedKraftShellInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data :
      CNLStandardNatHeightCodeBoundsNatBudgetShellInputData shell cStar xi) :
    CNLStandardWeightedKraftShellInputData shell cStar xi where
  transitions := data.transitions
  BNDHeightNat := data.BNDHeightNat
  M := data.M
  shellFactor := data.shellFactor
  Ij := data.Ij
  kraftSum_le := data.toCNLStandardSelectedEncodingInputData.encoding_input.kraftSum_le
  scalar_budget := data.scalar_budget

/-- View the shell-tied Nat-budget CNL leaf in the manuscript X-budget form. -/
def toCNLStandardWeightedKraftShellManuscriptInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data :
      CNLStandardNatHeightCodeBoundsNatBudgetShellInputData shell cStar xi) :
    CNLStandardWeightedKraftShellManuscriptInputData shell cStar xi :=
  data.toCNLStandardWeightedKraftShellInputData
    |>.toCNLStandardWeightedKraftShellManuscriptInputData

/-- Convert the shell-tied Nat-budget CNL leaf to grounded CNL data. -/
def toGroundedCNLLocalData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data :
      CNLStandardNatHeightCodeBoundsNatBudgetShellInputData shell cStar xi) :
    GroundedCNLLocalData cStar xi (shell.X : Real) :=
  data.toCNLStandardNatHeightCodeBoundsNatBudgetScalarInputData
    |>.toGroundedCNLLocalData

/-- Compatibility projection to the selector/encoding leaf. -/
def toCNLSelectorEncodingInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data :
      CNLStandardNatHeightCodeBoundsNatBudgetShellInputData shell cStar xi) :
    CNLSelectorEncodingInputData cStar xi (shell.X : Real) :=
  data.toCNLStandardNatHeightCodeBoundsNatBudgetScalarInputData
    |>.toCNLSelectorEncodingInputData

/-- Final selected-transition CNL entropy bound projected from the shell-tied
Nat-budget direct code/fibre leaf. -/
theorem cnl_bound
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data :
      CNLStandardNatHeightCodeBoundsNatBudgetShellInputData shell cStar xi) :
    ∃ CleanTerm : Real,
      0 <= CleanTerm ∧ CleanTerm <= cStar * xi * (shell.X : Real) / 6 :=
  data.toGroundedCNLLocalData.cnl_bound (Nat.cast_nonneg shell.X)

end CNLStandardNatHeightCodeBoundsNatBudgetShellInputData

/--
Core global assembly where carry, Chernoff, CNL, DensePack, and high-excess use
their current proof-v4 grounded interfaces.
-/
structure GlobalAssemblyCoreGroundedCarryChernoffCNLDensePackHighExcessInputs where
  carry :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCarryLocalData shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        RunFactoryData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (hcQ : shell.cQ = erdos260Constants.cQ)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        GroundedHighExcessLocalData phases ((carry shell hcQ).toCarryData)

/-- Convert the grounded carry/Chernoff/CNL/DensePack/high-excess interface to per-failure assembly. -/
def GlobalAssemblyCoreGroundedCarryChernoffCNLDensePackHighExcessInputs.toGlobalPerFailureAssembly
    (data : GlobalAssemblyCoreGroundedCarryChernoffCNLDensePackHighExcessInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro Q d hQ hd hnonterm hrational
    exact (canonicalThresholds Q d hQ hd hnonterm hrational).startThreshold
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic _hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    have hcQ : shell.cQ = erdos260Constants.cQ := rfl
    let phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (X : Real) := {
      chernoff := (data.chernoff shell hcQ).toChernoffPathData
      cnl := (data.cnl shell hcQ).toCNLClusterEncodingData
      tower := data.tower shell hcQ
      densePack := (data.densePack shell hcQ).toDensePackFactoryData
      returnPkg := data.returnPkg shell hcQ
      run := data.run shell hcQ }
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases
        ((data.carry shell hcQ).toCarryData)
        ((data.highExcess shell hcQ phases).toHighExcessChargeData)

/--
Erdos 260 from the core interface whose carry, Chernoff, CNL, DensePack, and
high-excess packages are supplied through proof-v4 aligned constructors.
-/
theorem erdos260_final_core_grounded_carry_chernoff_cnl_densePack_highExcess
    (data : GlobalAssemblyCoreGroundedCarryChernoffCNLDensePackHighExcessInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

end

end Erdos260
