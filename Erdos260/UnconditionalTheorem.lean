import Erdos260.GlobalClosureAssembly
import Erdos260.AppendixNVariationLeafConstruction
import Erdos260.AppendixNTerminalLeafConstruction
import Erdos260.ReturnLocalLeafConstruction
import Erdos260.RunLocalLeafConstruction
import Erdos260.ShellPaidChernoffConstruction
import Erdos260.ShellRegimeClosure
import Erdos260.CNLSelectedTransitionConstruction
import Erdos260.UnconditionalAssemblyFinal3

/-!
# Actual-shell final assembly interface

This file installs the final *shape* needed for a no-input Erdős #260 theorem:
providers are required only on genuinely large manuscript shells, and the
high-excess charge bridge is required only for the phase data actually assembled
from those providers.

It deliberately does not manufacture the remaining manuscript leaf proofs.  The
no-argument theorem should be added only after a term of
`GlobalAssemblyActualInputs` is built from the real proof-v4/v5 constructions.
-/

namespace Erdos260

noncomputable section

/--
The final manuscript largeness gate for one failing shell.

It combines the existing carry-pressure scale gate with the stronger Appendix N
start threshold.  The second component is the one that supplies the support hit
and the carry-large facts used by the current manuscript closure modules.
-/
def manuscriptLargeThreshold (shell : FailingDyadicShell) : Nat :=
  max (carryThreshold (carryB shell.Q + 19))
    (appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd shell.hnonterm)

/-- Raw version of `manuscriptLargeThreshold`, used as a global start threshold. -/
def manuscriptLargeThresholdOf
    (Q : Nat) (d : Nat → Nat) (hd : BinaryDigits d)
    (hnonterm : ¬ EventuallyZero d) : Nat :=
  max (carryThreshold (carryB Q + 19))
    (appendixNChainCompressionStartThreshold Q d hd hnonterm)

theorem carryThreshold_le_manuscriptLargeThreshold (shell : FailingDyadicShell) :
    carryThreshold (carryB shell.Q + 19) ≤ manuscriptLargeThreshold shell :=
  Nat.le_max_left _ _

theorem appendixNChainCompressionStartThreshold_le_manuscriptLargeThreshold
    (shell : FailingDyadicShell) :
    appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd shell.hnonterm
      ≤ manuscriptLargeThreshold shell :=
  Nat.le_max_right _ _

theorem aboveCarryThreshold_of_manuscriptLargeThreshold_le
    (shell : FailingDyadicShell)
    (hlarge : manuscriptLargeThreshold shell ≤ shell.X) :
    shell.aboveCarryThreshold :=
  le_trans (carryThreshold_le_manuscriptLargeThreshold shell) hlarge

theorem startThreshold_le_of_manuscriptLargeThreshold_le
    (shell : FailingDyadicShell)
    (hlarge : manuscriptLargeThreshold shell ≤ shell.X) :
    appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd shell.hnonterm
      ≤ shell.X :=
  le_trans (appendixNChainCompressionStartThreshold_le_manuscriptLargeThreshold shell) hlarge

theorem supportCount_pos_of_manuscriptLargeThreshold_le
    (shell : FailingDyadicShell)
    (hlarge : manuscriptLargeThreshold shell ≤ shell.X) :
    1 ≤ supportCount shell.d shell.X :=
  supportCount_pos_of_appendixNChainCompressionStartThreshold_le
    (startThreshold_le_of_manuscriptLargeThreshold_le shell hlarge)

theorem carryLarge_of_manuscriptLargeThreshold_le
    (shell : FailingDyadicShell)
    (hlarge : manuscriptLargeThreshold shell ≤ shell.X) :
    carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic :=
  carryLarge_of_appendixNChainCompressionStartThreshold_le
    (startThreshold_le_of_manuscriptLargeThreshold_le shell hlarge)

/--
One actual failure shell as it appears in the global contradiction argument.

The context keeps the raw `(Q,d,X)` data and the large-shell/failure hypotheses
from `GlobalPerFailureAssembly`; its `shell` projection is pinned to the
manuscript constants, in particular `c0 = manuscriptC0`.
-/
structure ActualFailureContext where
  Q : Nat
  d : Nat → Nat
  X : Nat
  hQ : 0 < Q
  hd : BinaryDigits d
  hnonterm : ¬ EventuallyZero d
  hrational :
    ∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)
  hXdyadic : Dyadic X
  hlarge : manuscriptLargeThresholdOf Q d hd hnonterm ≤ X
  hfailure : ((supportShell d X).card : ℝ) < erdos260Constants.c0 * (X : ℝ)

namespace ActualFailureContext

/-- The pinned failing shell associated to an actual global failure context. -/
def shell (ctx : ActualFailureContext) : FailingDyadicShell :=
  FailingDyadicShell.ofGlobalConstants erdos260Constants ctx.Q ctx.d ctx.X
    ctx.hQ ctx.hd ctx.hnonterm ctx.hrational ctx.hXdyadic
    erdos260Constants.c0 erdos260Constants.c0_pos
    manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ ctx.hfailure

@[simp] theorem shell_cQ (ctx : ActualFailureContext) :
    ctx.shell.cQ = erdos260Constants.cQ := rfl

@[simp] theorem shell_c0 (ctx : ActualFailureContext) :
    ctx.shell.c0 = manuscriptC0 := rfl

@[simp] theorem shell_X (ctx : ActualFailureContext) :
    ctx.shell.X = ctx.X := rfl

@[simp] theorem shell_Q (ctx : ActualFailureContext) :
    ctx.shell.Q = ctx.Q := rfl

/-- The raw global large-shell hypothesis, transported to the shell projection. -/
theorem shell_large (ctx : ActualFailureContext) :
    manuscriptLargeThreshold ctx.shell ≤ ctx.shell.X :=
  ctx.hlarge

theorem shell_startThreshold_le (ctx : ActualFailureContext) :
    appendixNChainCompressionStartThreshold ctx.shell.Q ctx.shell.d
        ctx.shell.hd ctx.shell.hnonterm ≤ ctx.shell.X :=
  startThreshold_le_of_manuscriptLargeThreshold_le ctx.shell ctx.shell_large

theorem shell_supportCount_pos (ctx : ActualFailureContext) :
    1 ≤ supportCount ctx.shell.d ctx.shell.X :=
  supportCount_pos_of_manuscriptLargeThreshold_le ctx.shell ctx.shell_large

theorem shell_carryLarge (ctx : ActualFailureContext) :
    carryB ctx.shell.Q + 25 ≤ Classical.choose ctx.shell.hXdyadic :=
  carryLarge_of_manuscriptLargeThreshold_le ctx.shell ctx.shell_large

/-- Canonical DensePack phase datum for an actual pinned failure context. -/
def densePack (ctx : ActualFailureContext) :
    DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  densePackFactoryDataCanonical ctx.shell
    (by simpa [ActualFailureContext.shell_c0] using manuscriptC0_le_kappa_div_sixteen)
    ctx.shell_carryLarge

/-- Tower phase datum built from the closed failing-shell recurrent cycle. -/
def tower (ctx : ActualFailureContext) :
    TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  towerOfSlope
    (towerCycleOfFailingShellClosed ctx.shell
      ctx.shell.hrational.choose ctx.shell.hrational.choose_spec).toSlopeAtom
    ctx.shell.X_nonneg_real

/-- Chernoff phase datum from the closed large-shell calibration constructor. -/
def chernoff (ctx : ActualFailureContext) :
    ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  (chernoffCalibrationInputOfLargeShell ctx.shell
    (by
      have h26 : (2 : ℕ) ^ 26 ≤ ctx.shell.X :=
        aboveCarryThreshold_forces_scale
          (aboveCarryThreshold_of_manuscriptLargeThreshold_le ctx.shell ctx.shell_large)
      have h64 : (64 : ℕ) ≤ 2 ^ 26 := by norm_num
      exact le_trans h64 h26)).toChernoffPathData

/-- Canonical rational-gap carry datum for an actual large failure context. -/
def carryData (ctx : ActualFailureContext) :
    CarryDataFromFailure ctx.shell erdos260Constants.cPr :=
  appendixNGapCanonicalYCarryDataAt ctx.shell
    (by simpa [ActualFailureContext.shell_c0] using manuscriptC0_le_kappa_div_sixteen)
    ctx.shell_startThreshold_le

/-- The actual shell is pinned to the manuscript constants. -/
def pin (ctx : ActualFailureContext) :
    PinnedManuscriptShell ctx.shell := { hcQ := rfl, hc0 := rfl }

/-- The manuscript smallness bound used by Appendix N leaf packages. -/
theorem hc0Small (ctx : ActualFailureContext) :
    ctx.shell.c0 <= manuscriptKappa / 16 :=
  ctx.pin.hc0Small

/-- Support positivity in the proof-term shape consumed by N.24 leaves. -/
theorem n24SupportCount_pos (ctx : ActualFailureContext) :
    1 <= supportCount ctx.shell.d ctx.shell.X :=
  supportCount_pos_of_appendixNChainCompressionStartThreshold_le
    ctx.shell_startThreshold_le

/-- Canonical carry-local datum used by the actual N.24 charge bridge. -/
def n24CarryLocal (ctx : ActualFailureContext) :
    ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
      ctx.shell erdos260Constants.cPr :=
  appendixNGapCanonicalYCarryLocalAt ctx.shell ctx.shell_startThreshold_le

/-- Carry datum paired definitionally with `n24CarryLocal`. -/
def n24CarryData (ctx : ActualFailureContext) :
    CarryDataFromFailure ctx.shell erdos260Constants.cPr :=
  (ctx.n24CarryLocal).toCarryData erdos260Constants_cPr_le_half
    ctx.hc0Small ctx.n24SupportCount_pos

/-- Assemble the actual six phases from the remaining leaf-level phase data. -/
def leafPhases (ctx : ActualFailureContext)
    (cnl :
      CNLStandardWeightedKraftShellClusterInputData ctx.shell
        erdos260Constants.cStar erdos260Constants.ξ)
    (returnPkg :
      ReturnClosedI51M2J4L6PackageInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : ℝ))
    (run :
      RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ)) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) where
  chernoff := ctx.chernoff
  cnl := cnl.toGroundedCNLLocalData.toCNLClusterEncodingData
  tower := ctx.tower
  densePack := ctx.densePack
  returnPkg :=
    returnPkg.toReturnSeparatedLocalLeafInputData.toGroundedReturnLocalData
      |>.toReturnFactoryData
  run := run.toGroundedRunLocalData.toRunFactoryData

/-- Assemble actual six phases when the Run leaf is supplied as its closed
L.4.1/L.4.2/I.5.2 manuscript package. -/
def leafPhasesRunPackage (ctx : ActualFailureContext)
    (cnl :
      CNLStandardWeightedKraftShellClusterInputData ctx.shell
        erdos260Constants.cStar erdos260Constants.ξ)
    (returnPkg :
      ReturnClosedI51M2J4L6PackageInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : ℝ))
    (run :
      RunClosedL41L42I52PackageInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : ℝ)) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) :=
  ctx.leafPhases cnl returnPkg run.toRunSeparatedLocalLeafInputData

/-- Assemble actual six phases when the Chernoff phase is supplied by the
proof-v4 regular/shell-paid Lemma 22.1A leaf. -/
def leafPhasesWithChernoffLeaf (ctx : ActualFailureContext)
    (chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    (cnl :
      CNLStandardWeightedKraftShellClusterInputData ctx.shell
        erdos260Constants.cStar erdos260Constants.ξ)
    (returnPkg :
      ReturnClosedI51M2J4L6PackageInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    (run :
      RunClosedL41L42I52PackageInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) where
  chernoff := chernoffLeaf.toGroundedChernoffLocalData.toChernoffPathData
  cnl := cnl.toGroundedCNLLocalData.toCNLClusterEncodingData
  tower := ctx.tower
  densePack := ctx.densePack
  returnPkg :=
    returnPkg.toReturnSeparatedLocalLeafInputData.toGroundedReturnLocalData
      |>.toReturnFactoryData
  run :=
    run.toRunSeparatedLocalLeafInputData.toGroundedRunLocalData
      |>.toRunFactoryData

/-- Assemble actual six phases when CNL is supplied by the direct weighted-Kraft
shell leaf rather than the cluster-to-ladder leaf. -/
def leafPhasesWithWeightedCNL (ctx : ActualFailureContext)
    (chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    (cnl :
      CNLStandardWeightedKraftShellInputData ctx.shell
        erdos260Constants.cStar erdos260Constants.ξ)
    (returnPkg :
      ReturnClosedI51M2J4L6PackageInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    (run :
      RunClosedL41L42I52PackageInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) where
  chernoff := chernoffLeaf.toGroundedChernoffLocalData.toChernoffPathData
  cnl := cnl.toGroundedCNLLocalData.toCNLClusterEncodingData
  tower := ctx.tower
  densePack := ctx.densePack
  returnPkg :=
    returnPkg.toReturnSeparatedLocalLeafInputData.toGroundedReturnLocalData
      |>.toReturnFactoryData
  run :=
    run.toRunSeparatedLocalLeafInputData.toGroundedRunLocalData
      |>.toRunFactoryData

end ActualFailureContext

/--
Raw actual L.1.2/G.35 CNL cluster data for one failing shell.

This is the manuscript-facing content of the CNL provider: selected clean
transitions, Nat-valued BND heights, the cluster-to-ladder Kraft comparison,
and the scalar shell/interval budget.
-/
structure ActualCNLRawL112G35Data (ctx : ActualFailureContext) where
  transitions : Finset CNLTransition
  BNDHeightNat : CNLTransition -> Nat
  M : Nat
  shellFactor : {x : ℝ // 0 <= x}
  Ij : {x : ℝ // 0 <= x}
  ladderChildren : Nat -> Finset Nat
  ladderHeight : Nat -> ℝ
  ladderRoot : Nat
  ladderHeight_dom : ∀ n : Nat, (n : ℝ) <= ladderHeight n
  cluster_le_pathKraft :
    cleanCNLKraftSum
        (selectedTransitions transitions) (fun t => (BNDHeightNat t : ℝ))
        (1 : ℝ) <=
      pathKraft ladderChildren
        (fun n => (2 : ℝ) ^ (-((1 : ℝ) * ladderHeight n))) M
        ladderRoot
  manuscript_budget :
    (2 : ℝ) ^ M * (shellFactor : ℝ) * (ctx.shell.X : ℝ) *
        (Ij : ℝ) <=
      erdos260Constants.cStar * erdos260Constants.ξ *
        (ctx.shell.X : ℝ) / 6

namespace ActualCNLRawL112G35Data

/-- Package raw L.1.2/G.35 CNL data as the cluster leaf. -/
def toClusterInputData {ctx : ActualFailureContext}
    (data : ActualCNLRawL112G35Data ctx) :
    CNLStandardWeightedKraftShellClusterInputData ctx.shell
      erdos260Constants.cStar erdos260Constants.ξ where
  transitions := data.transitions
  BNDHeightNat := data.BNDHeightNat
  M := data.M
  shellFactor := data.shellFactor
  Ij := data.Ij
  ladderChildren := data.ladderChildren
  ladderHeight := data.ladderHeight
  ladderRoot := data.ladderRoot
  ladderHeight_dom := data.ladderHeight_dom
  cluster_le_pathKraft := data.cluster_le_pathKraft
  manuscript_budget := data.manuscript_budget

end ActualCNLRawL112G35Data

/--
Actual CNL data in the direct code/fibre Nat-budget form.

This exposes selected transitions, Nat BND heights, class-local code and fibre
bounds, the Nat-valued global class budget, and the scalar shell/interval
budget used by the proof-v4 L.1.2/G.35 route.
-/
structure ActualCNLCodeFibreNatBudgetData (ctx : ActualFailureContext) where
  Code : Type
  decCode : DecidableEq Code
  transitions : Finset CNLTransition
  BNDHeightNat : CNLTransition -> Nat
  M : Nat
  shellFactor : {x : ℝ // 0 <= x}
  Ij : {x : ℝ // 0 <= x}
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
    (2 : ℝ) ^ M * (shellFactor : ℝ) * (Ij : ℝ) <=
      erdos260Constants.cStar * erdos260Constants.ξ / 6

namespace ActualCNLCodeFibreNatBudgetData

/-- Package the direct code/fibre Nat-budget data as the shell-tied CNL leaf. -/
def toNatBudgetShellInputData {ctx : ActualFailureContext}
    (data : ActualCNLCodeFibreNatBudgetData ctx) :
    CNLStandardNatHeightCodeBoundsNatBudgetShellInputData ctx.shell
      erdos260Constants.cStar erdos260Constants.ξ where
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
  hcodes := data.hcodes
  hfiber := data.hfiber
  hcodeSumNat := data.hcodeSumNat
  scalar_budget := data.scalar_budget

/-- Forget the code/fibre witnesses to the direct weighted-Kraft shell leaf. -/
def toWeightedKraftShellInputData {ctx : ActualFailureContext}
    (data : ActualCNLCodeFibreNatBudgetData ctx) :
    CNLStandardWeightedKraftShellInputData ctx.shell
      erdos260Constants.cStar erdos260Constants.ξ :=
  data.toNatBudgetShellInputData.toCNLStandardWeightedKraftShellInputData

end ActualCNLCodeFibreNatBudgetData

/--
Actual CNL code/fibre Nat-budget data with code-label equality chosen
internally.

This is the same manuscript L.1.2/G.35 content as
`ActualCNLCodeFibreNatBudgetData`, but it does not expose a separate
`DecidableEq Code` field.  The projection below uses `Classical.decEq`, matching
the proof-v4 route where equality on local code labels is an ambient classical
choice rather than mathematical data.
-/
structure ActualCNLClassicalCodeFibreNatBudgetData
    (ctx : ActualFailureContext) where
  Code : Type
  transitions : Finset CNLTransition
  BNDHeightNat : CNLTransition -> Nat
  M : Nat
  shellFactor : {x : Real // 0 <= x}
  Ij : {x : Real // 0 <= x}
  code : CNLClass -> CNLTransition -> Code
  codeBound : CNLClass -> Nat
  fiberBound : CNLClass -> Nat
  hcodes :
    letI : DecidableEq Code := Classical.decEq Code
    forall cls : CNLClass,
      ((transitionsSelectedAs transitions cls).image (code cls)).card <=
        codeBound cls
  hfiber :
    letI : DecidableEq Code := Classical.decEq Code
    forall (cls : CNLClass) (y : Code),
      y ∈ (transitionsSelectedAs transitions cls).image (code cls) ->
        ((transitionsSelectedAs transitions cls).filter
          fun t => code cls t = y).card <= fiberBound cls
  hcodeSumNat :
    (Finset.univ.sum fun cls : CNLClass => codeBound cls * fiberBound cls) <=
      2 ^ M
  scalar_budget :
    (2 : Real) ^ M * (shellFactor : Real) * (Ij : Real) <=
      erdos260Constants.cStar * erdos260Constants.ξ / 6

namespace ActualCNLClassicalCodeFibreNatBudgetData

/-- Re-expose the classical code/fibre CNL data at the explicit
`DecidableEq` code/fibre boundary. -/
def toCodeFibreNatBudgetData {ctx : ActualFailureContext}
    (data : ActualCNLClassicalCodeFibreNatBudgetData ctx) :
    ActualCNLCodeFibreNatBudgetData ctx where
  Code := data.Code
  decCode := Classical.decEq data.Code
  transitions := data.transitions
  BNDHeightNat := data.BNDHeightNat
  M := data.M
  shellFactor := data.shellFactor
  Ij := data.Ij
  code := data.code
  codeBound := data.codeBound
  fiberBound := data.fiberBound
  hcodes := by
    letI : DecidableEq data.Code := Classical.decEq data.Code
    exact data.hcodes
  hfiber := by
    letI : DecidableEq data.Code := Classical.decEq data.Code
    exact data.hfiber
  hcodeSumNat := data.hcodeSumNat
  scalar_budget := data.scalar_budget

/-- Package the classical code/fibre CNL data directly as the shell-tied
Nat-budget CNL leaf. -/
def toNatBudgetShellInputData {ctx : ActualFailureContext}
    (data : ActualCNLClassicalCodeFibreNatBudgetData ctx) :
    CNLStandardNatHeightCodeBoundsNatBudgetShellInputData ctx.shell
      erdos260Constants.cStar erdos260Constants.ξ :=
  data.toCodeFibreNatBudgetData.toNatBudgetShellInputData

/-- Forget the classical code/fibre witnesses directly to the weighted-Kraft
shell leaf consumed by older CNL bridges. -/
def toWeightedKraftShellInputData {ctx : ActualFailureContext}
    (data : ActualCNLClassicalCodeFibreNatBudgetData ctx) :
    CNLStandardWeightedKraftShellInputData ctx.shell
      erdos260Constants.cStar erdos260Constants.ξ :=
  data.toNatBudgetShellInputData.toCNLStandardWeightedKraftShellInputData

end ActualCNLClassicalCodeFibreNatBudgetData

/--
Actual CNL data in the direct weighted-Kraft G.35 form.

This is the manuscript-facing endpoint after the selected-transition heights
and weighted Kraft inequality have already been proved; no auxiliary
code/fibre witnesses are required by this surface.
-/
structure ActualCNLWeightedKraftData (ctx : ActualFailureContext) where
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
    (2 : Real) ^ M * (shellFactor : Real) * (ctx.shell.X : Real) *
        (Ij : Real) <=
      erdos260Constants.cStar * erdos260Constants.ξ *
        (ctx.shell.X : Real) / 6

namespace ActualCNLWeightedKraftData

/-- Package direct weighted-Kraft G.35 data as the CNL shell leaf consumed by
the actual phase package. -/
def toWeightedKraftShellInputData {ctx : ActualFailureContext}
    (data : ActualCNLWeightedKraftData ctx) :
    CNLStandardWeightedKraftShellInputData ctx.shell
      erdos260Constants.cStar erdos260Constants.ξ :=
  CNLStandardWeightedKraftShellInputData.ofWeightedKraftManuscriptBudget
    data.transitions data.BNDHeightNat data.M data.shellFactor data.Ij
    data.kraftSum_le data.manuscript_budget

end ActualCNLWeightedKraftData

/-- Raw actual Prop. I.5.1/M.2/J.4/L.6 return data for one failing shell. -/
structure ActualReturnRawI51M2J4L6Data (ctx : ActualFailureContext) where
  ordinaryShort : ℝ
  semiperiodic : ℝ
  olc : ℝ
  nonlocalLong : ℝ
  c1 : ℝ
  c2 : ℝ
  c3 : ℝ
  c4 : ℝ
  s : ℝ
  ij : ℝ
  smallError : ℝ
  ML : ℝ
  epsilonTerm : ℝ
  ordinaryShort_bound :
    ordinaryShort <= c1 * erdos260Constants.ξ * s * (ctx.shell.X : ℝ) *
      ij + smallError / 4
  semiperiodic_bound :
    semiperiodic <= c2 * erdos260Constants.ξ * s *
      (ctx.shell.X : ℝ) * ij + smallError / 4
  olc_multiplicity :
    olc <= ML * (ctx.shell.X : ℝ) * ij + epsilonTerm
  olc_epsilon :
    epsilonTerm <= s * (ctx.shell.X : ℝ) * ij / 2
  olc_ML_budget :
    ML * (ctx.shell.X : ℝ) * ij <= s * (ctx.shell.X : ℝ) * ij / 2
  olc_return_budget :
    s * (ctx.shell.X : ℝ) * ij <=
      c3 * erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * ij +
        smallError / 4
  nonlocalLong_bound :
    nonlocalLong <= c4 * erdos260Constants.ξ * s *
      (ctx.shell.X : ℝ) * ij + smallError / 4
  smallness :
    ReturnSmallnessInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) c1 c2 c3 c4 s ij smallError

namespace ActualReturnRawI51M2J4L6Data

/-- Package raw return estimates as the closed manuscript return package. -/
def toPackageInputData {ctx : ActualFailureContext}
    (data : ActualReturnRawI51M2J4L6Data ctx) :
    ReturnClosedI51M2J4L6PackageInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  ReturnClosedI51M2J4L6PackageInputData.ofOLCMultiplicity
    data.ordinaryShort_bound data.semiperiodic_bound
    data.olc_multiplicity data.olc_epsilon data.olc_ML_budget
    data.olc_return_budget data.nonlocalLong_bound data.smallness

/-- Re-expose a proof-v4 separated Return leaf as the compact actual Return
surface. -/
def ofSeparatedLeaf {ctx : ActualFailureContext}
    (data :
      ReturnSeparatedLocalLeafInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)) :
    ActualReturnRawI51M2J4L6Data ctx where
  ordinaryShort := data.ordinaryShort
  semiperiodic := data.semiperiodic
  olc := data.olc
  nonlocalLong := data.nonlocalLong
  c1 := data.c1
  c2 := data.c2
  c3 := data.c3
  c4 := data.c4
  s := data.s
  ij := data.ij
  smallError := data.smallError
  ML := data.ML
  epsilonTerm := data.epsilonTerm
  ordinaryShort_bound :=
    data.shortPieces.ordinary.ordinaryShort_bound
  semiperiodic_bound :=
    data.shortPieces.semiperiodicData.semiperiodic_bound
  olc_multiplicity :=
    data.olcData.multiplicityData.multiplicity
  olc_epsilon :=
    data.olcData.epsilonData.epsilon
  olc_ML_budget :=
    data.olcData.MLBudgetData.ML_budget
  olc_return_budget :=
    data.olcData.returnBudgetData.return_budget
  nonlocalLong_bound :=
    data.nonlocalLongData.nonlocalLong_bound
  smallness := data.smallness

end ActualReturnRawI51M2J4L6Data

/-- Raw actual return data with the final scalar smallness comparison exposed
as an inequality rather than a bundled `ReturnSmallnessInputData`. -/
structure ActualReturnRawI51M2J4L6ScalarData (ctx : ActualFailureContext) where
  ordinaryShort : Real
  semiperiodic : Real
  olc : Real
  nonlocalLong : Real
  c1 : Real
  c2 : Real
  c3 : Real
  c4 : Real
  s : Real
  ij : Real
  smallError : Real
  ML : Real
  epsilonTerm : Real
  ordinaryShort_bound :
    ordinaryShort <= c1 * erdos260Constants.ξ * s * (ctx.shell.X : Real) *
      ij + smallError / 4
  semiperiodic_bound :
    semiperiodic <= c2 * erdos260Constants.ξ * s *
      (ctx.shell.X : Real) * ij + smallError / 4
  olc_multiplicity :
    olc <= ML * (ctx.shell.X : Real) * ij + epsilonTerm
  olc_epsilon :
    epsilonTerm <= s * (ctx.shell.X : Real) * ij / 2
  olc_ML_budget :
    ML * (ctx.shell.X : Real) * ij <= s * (ctx.shell.X : Real) * ij / 2
  olc_return_budget :
    s * (ctx.shell.X : Real) * ij <=
      c3 * erdos260Constants.ξ * s * (ctx.shell.X : Real) * ij +
        smallError / 4
  nonlocalLong_bound :
    nonlocalLong <= c4 * erdos260Constants.ξ * s *
      (ctx.shell.X : Real) * ij + smallError / 4
  hSmall :
    (c1 + c2 + c3 + c4) * erdos260Constants.ξ * s *
        (ctx.shell.X : Real) * ij + smallError <=
      erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6

namespace ActualReturnRawI51M2J4L6ScalarData

/-- Bundle the exposed Return scalar smallness inequality for the existing raw
Return package. -/
def toRawData {ctx : ActualFailureContext}
    (data : ActualReturnRawI51M2J4L6ScalarData ctx) :
    ActualReturnRawI51M2J4L6Data ctx where
  ordinaryShort := data.ordinaryShort
  semiperiodic := data.semiperiodic
  olc := data.olc
  nonlocalLong := data.nonlocalLong
  c1 := data.c1
  c2 := data.c2
  c3 := data.c3
  c4 := data.c4
  s := data.s
  ij := data.ij
  smallError := data.smallError
  ML := data.ML
  epsilonTerm := data.epsilonTerm
  ordinaryShort_bound := data.ordinaryShort_bound
  semiperiodic_bound := data.semiperiodic_bound
  olc_multiplicity := data.olc_multiplicity
  olc_epsilon := data.olc_epsilon
  olc_ML_budget := data.olc_ML_budget
  olc_return_budget := data.olc_return_budget
  nonlocalLong_bound := data.nonlocalLong_bound
  smallness := { hSmall := data.hSmall }

end ActualReturnRawI51M2J4L6ScalarData

/--
Raw actual return data with the I.5.1/M.2/J.4/L.6 pieces kept as separate
manuscript certificates.
-/
structure ActualReturnRawI51M2J4L6SplitScalarData
    (ctx : ActualFailureContext) where
  ordinaryShort : Real
  semiperiodic : Real
  olc : Real
  nonlocalLong : Real
  c1 : Real
  c2 : Real
  c3 : Real
  c4 : Real
  s : Real
  ij : Real
  smallError : Real
  ML : Real
  epsilonTerm : Real
  shortPieces :
    ReturnShortPiecesData ordinaryShort semiperiodic c1 c2
      erdos260Constants.ξ s (ctx.shell.X : Real) ij smallError
  olcData :
    ReturnOLCData olc ML (ctx.shell.X : Real) ij epsilonTerm s c3
      erdos260Constants.ξ smallError
  nonlocalLongData :
    ReturnNonlocalLongData nonlocalLong c4 erdos260Constants.ξ s
      (ctx.shell.X : Real) ij smallError
  hSmall :
    (c1 + c2 + c3 + c4) * erdos260Constants.ξ * s *
        (ctx.shell.X : Real) * ij + smallError <=
      erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6

namespace ActualReturnRawI51M2J4L6SplitScalarData

/-- Project separated return certificates to the scalar actual return surface. -/
def toScalarData {ctx : ActualFailureContext}
    (data : ActualReturnRawI51M2J4L6SplitScalarData ctx) :
    ActualReturnRawI51M2J4L6ScalarData ctx where
  ordinaryShort := data.ordinaryShort
  semiperiodic := data.semiperiodic
  olc := data.olc
  nonlocalLong := data.nonlocalLong
  c1 := data.c1
  c2 := data.c2
  c3 := data.c3
  c4 := data.c4
  s := data.s
  ij := data.ij
  smallError := data.smallError
  ML := data.ML
  epsilonTerm := data.epsilonTerm
  ordinaryShort_bound :=
    data.shortPieces.ordinary.ordinaryShort_bound
  semiperiodic_bound :=
    data.shortPieces.semiperiodicData.semiperiodic_bound
  olc_multiplicity :=
    data.olcData.multiplicityData.multiplicity
  olc_epsilon :=
    data.olcData.epsilonData.epsilon
  olc_ML_budget :=
    data.olcData.MLBudgetData.ML_budget
  olc_return_budget :=
    data.olcData.returnBudgetData.return_budget
  nonlocalLong_bound :=
    data.nonlocalLongData.nonlocalLong_bound
  hSmall := data.hSmall

/-- Re-expose a proof-v4 separated Return leaf as the current actual split
Return surface. -/
def ofSeparatedLeaf {ctx : ActualFailureContext}
    (data :
      ReturnSeparatedLocalLeafInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)) :
    ActualReturnRawI51M2J4L6SplitScalarData ctx where
  ordinaryShort := data.ordinaryShort
  semiperiodic := data.semiperiodic
  olc := data.olc
  nonlocalLong := data.nonlocalLong
  c1 := data.c1
  c2 := data.c2
  c3 := data.c3
  c4 := data.c4
  s := data.s
  ij := data.ij
  smallError := data.smallError
  ML := data.ML
  epsilonTerm := data.epsilonTerm
  shortPieces := data.shortPieces
  olcData := data.olcData
  nonlocalLongData := data.nonlocalLongData
  hSmall := data.smallness.hSmall

end ActualReturnRawI51M2J4L6SplitScalarData

/-- Raw actual L.4.1/L.4.2/I.5.2 run data for one failing shell. -/
structure ActualRunRawL41L42I52Data (ctx : ActualFailureContext) where
  runMass : ℝ
  nextTower : ℝ
  nextReturn : ℝ
  nextDensePack : ℝ
  twoNegcY : ℝ
  Ij : ℝ
  smallError : ℝ
  meanLow : ℝ
  localSpike : ℝ
  boundary : ℝ
  chainWeight : Nat -> {x : ℝ // 0 <= x}
  chainLength : Nat
  trichotomy :
    RunTrichotomyAbsorptionData runMass nextTower nextReturn nextDensePack
      twoNegcY (ctx.shell.X : ℝ) Ij smallError meanLow localSpike boundary
      (fun n : Nat => (chainWeight n : ℝ)) chainLength
  chain_half :
    ∀ n : Nat,
      (chainWeight (n + 1) : ℝ) <= (chainWeight n : ℝ) / 2
  smallness :
    RunSmallnessInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) nextTower nextReturn nextDensePack twoNegcY Ij
      smallError

namespace ActualRunRawL41L42I52Data

/-- Package raw run estimates as the closed manuscript run package. -/
def toPackageInputData {ctx : ActualFailureContext}
    (data : ActualRunRawL41L42I52Data ctx) :
    RunClosedL41L42I52PackageInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : ℝ) :=
    RunClosedL41L42I52PackageInputData.ofTrichotomyHalfDecrease
    data.trichotomy data.chain_half data.smallness

/-- Re-expose a proof-v4 separated Run leaf as the compact actual Run surface. -/
def ofSeparatedLeaf {ctx : ActualFailureContext}
    (data :
      RunSeparatedLocalLeafInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)) :
    ActualRunRawL41L42I52Data ctx where
  runMass := data.runMass
  nextTower := data.nextTower
  nextReturn := data.nextReturn
  nextDensePack := data.nextDensePack
  twoNegcY := data.twoNegcY
  Ij := data.Ij
  smallError := data.smallError
  meanLow := data.meanLow
  localSpike := data.localSpike
  boundary := data.boundary
  chainWeight := data.chainWeight
  chainLength := data.chainLength
  trichotomy := data.trichotomy
  chain_half := data.periodHalf.chain_half
  smallness := data.smallness

end ActualRunRawL41L42I52Data

/-- Raw actual run data with the final scalar smallness comparison exposed as
an inequality rather than a bundled `RunSmallnessInputData`. -/
structure ActualRunRawL41L42I52ScalarData (ctx : ActualFailureContext) where
  runMass : Real
  nextTower : Real
  nextReturn : Real
  nextDensePack : Real
  twoNegcY : Real
  Ij : Real
  smallError : Real
  meanLow : Real
  localSpike : Real
  boundary : Real
  chainWeight : Nat -> {x : Real // 0 <= x}
  chainLength : Nat
  trichotomy :
    RunTrichotomyAbsorptionData runMass nextTower nextReturn nextDensePack
      twoNegcY (ctx.shell.X : Real) Ij smallError meanLow localSpike boundary
      (fun n : Nat => (chainWeight n : Real)) chainLength
  chain_half :
    forall n : Nat,
      (chainWeight (n + 1) : Real) <= (chainWeight n : Real) / 2
  hSmall :
    nextTower + nextReturn + nextDensePack +
        (ctx.shell.X : Real) * Ij * twoNegcY + smallError <=
      erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6

namespace ActualRunRawL41L42I52ScalarData

/-- Bundle the exposed Run scalar smallness inequality for the existing raw Run
package. -/
def toRawData {ctx : ActualFailureContext}
    (data : ActualRunRawL41L42I52ScalarData ctx) :
    ActualRunRawL41L42I52Data ctx where
  runMass := data.runMass
  nextTower := data.nextTower
  nextReturn := data.nextReturn
  nextDensePack := data.nextDensePack
  twoNegcY := data.twoNegcY
  Ij := data.Ij
  smallError := data.smallError
  meanLow := data.meanLow
  localSpike := data.localSpike
  boundary := data.boundary
  chainWeight := data.chainWeight
  chainLength := data.chainLength
  trichotomy := data.trichotomy
  chain_half := data.chain_half
  smallness := { hSmall := data.hSmall }

end ActualRunRawL41L42I52ScalarData

/-- Raw actual run data with the L.4.1 deterministic split and the output
absorption supplied as separate manuscript inputs. -/
structure ActualRunRawL41L42I52SplitAbsorptionScalarData
    (ctx : ActualFailureContext) where
  runMass : Real
  nextTower : Real
  nextReturn : Real
  nextDensePack : Real
  twoNegcY : Real
  Ij : Real
  smallError : Real
  meanLow : Real
  localSpike : Real
  boundary : Real
  chainWeight : Nat -> {x : Real // 0 <= x}
  chainLength : Nat
  localSplit :
    RunLocalSplitData runMass smallError meanLow localSpike boundary
      (fun n : Nat => Subtype.val (chainWeight n)) chainLength
  absorption :
    RunOutputAbsorptionData meanLow localSpike boundary
      (Subtype.val (chainWeight 0)) nextTower nextReturn nextDensePack
      ((ctx.shell.X : Real) * Ij * twoNegcY)
  chain_half :
    forall n : Nat,
      Subtype.val (chainWeight (n + 1)) <= Subtype.val (chainWeight n) / 2
  hSmall :
    nextTower + nextReturn + nextDensePack +
        (ctx.shell.X : Real) * Ij * twoNegcY + smallError <=
      erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6

namespace ActualRunRawL41L42I52SplitAbsorptionScalarData

/-- Recombine the separated L.4.1 split and absorption data into the compact
Run trichotomy package. -/
def toScalarData {ctx : ActualFailureContext}
    (data : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx) :
    ActualRunRawL41L42I52ScalarData ctx :=
  let tri :
      RunTrichotomyAbsorptionData data.runMass data.nextTower
        data.nextReturn data.nextDensePack data.twoNegcY (ctx.shell.X : Real)
        data.Ij data.smallError data.meanLow data.localSpike data.boundary
        (fun n : Nat => Subtype.val (data.chainWeight n)) data.chainLength :=
    { localData := data.localSplit
      absorption := data.absorption }
  { runMass := data.runMass
    nextTower := data.nextTower
    nextReturn := data.nextReturn
    nextDensePack := data.nextDensePack
    twoNegcY := data.twoNegcY
    Ij := data.Ij
    smallError := data.smallError
    meanLow := data.meanLow
    localSpike := data.localSpike
    boundary := data.boundary
    chainWeight := data.chainWeight
    chainLength := data.chainLength
    trichotomy := tri
    chain_half := data.chain_half
    hSmall := data.hSmall }

/-- Re-expose a proof-v4 separated Run leaf as the current actual split and
absorption Run surface. -/
def ofSeparatedLeaf {ctx : ActualFailureContext}
    (data :
      RunSeparatedLocalLeafInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)) :
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx where
  runMass := data.runMass
  nextTower := data.nextTower
  nextReturn := data.nextReturn
  nextDensePack := data.nextDensePack
  twoNegcY := data.twoNegcY
  Ij := data.Ij
  smallError := data.smallError
  meanLow := data.meanLow
  localSpike := data.localSpike
  boundary := data.boundary
  chainWeight := data.chainWeight
  chainLength := data.chainLength
  localSplit := data.trichotomy.localData
  absorption := data.trichotomy.absorption
  chain_half := data.periodHalf.chain_half
  hSmall := data.smallness.hSmall

end ActualRunRawL41L42I52SplitAbsorptionScalarData

/--
Final actual-consumption provider interface.

Compared with `GlobalAssemblyCoreInputs`, providers are indexed by
`ActualFailureContext`: only pinned manuscript shells that arise from the global
failure argument are in scope.  The charge bridge is requested only for the
single phase package assembled from these providers.
-/
structure GlobalAssemblyActualInputs where
  carryData : ∀ ctx : ActualFailureContext,
    CarryDataFromFailure ctx.shell erdos260Constants.cPr
  chernoff : ∀ ctx : ActualFailureContext,
    ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ)
  cnl : ∀ ctx : ActualFailureContext,
    CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ)
  densePack : ∀ ctx : ActualFailureContext,
    DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ)
  tower : ∀ ctx : ActualFailureContext,
    TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ)
  returnPkg : ∀ ctx : ActualFailureContext,
    ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ)
  run : ∀ ctx : ActualFailureContext,
    RunFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ)
  highExcessCharge :
    ∀ ctx : ActualFailureContext,
        HighExcessChargeData
          { chernoff := chernoff ctx
            cnl := cnl ctx
            tower := tower ctx
            densePack := densePack ctx
            returnPkg := returnPkg ctx
            run := run ctx }
          (carryData ctx)

namespace GlobalAssemblyActualInputs

/-- The actual global start threshold used by the final interface. -/
def startThreshold
    (_data : GlobalAssemblyActualInputs)
    (Q : Nat) (d : Nat → Nat)
    (_hQ : 0 < Q) (hd : BinaryDigits d)
    (hnonterm : ¬ EventuallyZero d)
    (_hrational :
      ∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) :
    Nat :=
  manuscriptLargeThresholdOf Q d hd hnonterm

/-- Build the actual phase package for one large failing shell. -/
def phases (data : GlobalAssemblyActualInputs)
    (ctx : ActualFailureContext) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) where
  chernoff := data.chernoff ctx
  cnl := data.cnl ctx
  tower := data.tower ctx
  densePack := data.densePack ctx
  returnPkg := data.returnPkg ctx
  run := data.run ctx

/--
Convert the actual-consumption interface to the existing global per-failure
assembly provider.
-/
def toGlobalPerFailureAssembly
    (data : GlobalAssemblyActualInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := data.startThreshold
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let ctx : ActualFailureContext :=
      { Q := Q
        d := d
        X := X
        hQ := hQ
        hd := hd
        hnonterm := hnonterm
        hrational := hrational
        hXdyadic := hXdyadic
        hlarge := hXge
        hfailure := hfailure }
    let phases := data.phases ctx
    let carry := data.carryData ctx
    let charge : HighExcessChargeData phases carry := data.highExcessCharge ctx
    exact PerFailureAssemblyData.ofHighExcessCharge phases carry charge

end GlobalAssemblyActualInputs

/--
Final bridge from the actual-consumption interface to Erdős #260.

This is the implementation of the planned interface/assembly step.  The
remaining task is to construct a term of `GlobalAssemblyActualInputs` from the
real manuscript leaves.
-/
theorem erdos260_final_actual (data : GlobalAssemblyActualInputs) : Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

/-- Alias emphasizing the only remaining input to a no-argument theorem. -/
theorem erdos260_unconditional_from_actual_inputs
    (data : GlobalAssemblyActualInputs) : Erdos260Statement :=
  erdos260_final_actual data

/-- Any inhabited provider surface that projects to the final actual-consumption
interface gives an actual assembly input object.  This is the generic bridge for
the many manuscript-shaped provider records exposing a `toActualInputs`
projection. -/
theorem globalAssemblyActualInputs_nonempty_of_projection
    {α : Type} (toActual : α -> GlobalAssemblyActualInputs)
    (hprovider : Nonempty α) :
    Nonempty GlobalAssemblyActualInputs := by
  exact hprovider.elim fun data => Nonempty.intro (toActual data)

/-- Generic final endpoint for any inhabited provider surface that projects to
the final actual-consumption interface. -/
theorem erdos260_unconditional_from_projected_actual_provider
    {α : Type} (toActual : α -> GlobalAssemblyActualInputs)
    (hprovider : Nonempty α) :
    Erdos260Statement :=
  hprovider.elim fun data => erdos260_final_actual (toActual data)

/--
Reduced actual-consumption interface after closing carry, DensePack, Tower, and
Chernoff from the pinned large shell context.

The remaining fields are the still-genuine manuscript leaves.  Carry is
`ActualFailureContext.carryData`; DensePack is `ActualFailureContext.densePack`;
Tower is `ActualFailureContext.tower`; Chernoff is `ActualFailureContext.chernoff`.
-/
structure GlobalAssemblyActualReducedInputs where
  cnl : ∀ ctx : ActualFailureContext,
    CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ)
  returnPkg : ∀ ctx : ActualFailureContext,
    ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ)
  run : ∀ ctx : ActualFailureContext,
    RunFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ)
  highExcessCharge :
    ∀ ctx : ActualFailureContext,
      HighExcessChargeData
        { chernoff := ctx.chernoff
          cnl := cnl ctx
          tower := ctx.tower
          densePack := ctx.densePack
          returnPkg := returnPkg ctx
          run := run ctx }
        ctx.carryData

namespace GlobalAssemblyActualReducedInputs

/-- Expand the reduced actual interface to the full actual interface. -/
def toActualInputs (data : GlobalAssemblyActualReducedInputs) :
    GlobalAssemblyActualInputs where
  carryData := ActualFailureContext.carryData
  chernoff := ActualFailureContext.chernoff
  cnl := data.cnl
  densePack := ActualFailureContext.densePack
  tower := ActualFailureContext.tower
  returnPkg := data.returnPkg
  run := data.run
  highExcessCharge := data.highExcessCharge

end GlobalAssemblyActualReducedInputs

/-- Final bridge after DensePack and Tower are closed from actual shell geometry. -/
theorem erdos260_final_actual_reduced
    (data : GlobalAssemblyActualReducedInputs) : Erdos260Statement :=
  erdos260_final_actual data.toActualInputs

/--
Grounded actual-consumption interface after projecting CNL, Return, and Run
from their local manuscript-shaped data.

This keeps the final charge bridge on the actual assembled phase package, while
moving the three remaining phase providers one layer below the capstone
`FactoryData` surface.
-/
structure GlobalAssemblyActualGroundedInputs where
  cnl : ∀ ctx : ActualFailureContext,
    GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ)
  returnPkg : ∀ ctx : ActualFailureContext,
    GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ)
  run : ∀ ctx : ActualFailureContext,
    GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ)
  highExcessCharge :
    ∀ ctx : ActualFailureContext,
      HighExcessChargeData
        { chernoff := ctx.chernoff
          cnl := (cnl ctx).toCNLClusterEncodingData
          tower := ctx.tower
          densePack := ctx.densePack
          returnPkg := (returnPkg ctx).toReturnFactoryData
          run := (run ctx).toRunFactoryData }
        ctx.carryData

namespace GlobalAssemblyActualGroundedInputs

/-- Project grounded local data to the reduced actual-consumption interface. -/
def toReducedInputs (data : GlobalAssemblyActualGroundedInputs) :
    GlobalAssemblyActualReducedInputs where
  cnl := fun ctx => (data.cnl ctx).toCNLClusterEncodingData
  returnPkg := fun ctx => (data.returnPkg ctx).toReturnFactoryData
  run := fun ctx => (data.run ctx).toRunFactoryData
  highExcessCharge := data.highExcessCharge

end GlobalAssemblyActualGroundedInputs

/-- Final bridge after CNL, Return, and Run are expressed as grounded local data. -/
theorem erdos260_final_actual_grounded
    (data : GlobalAssemblyActualGroundedInputs) : Erdos260Statement :=
  erdos260_final_actual_reduced data.toReducedInputs

/--
Actual interface with the CNL phase exposed as the proof-v4 L.1.2/G.35
cluster-to-ladder weighted-Kraft shell leaf.

Return and Run remain grounded local data here; this isolates the next honest
CNL obligation without changing the actual-phase charge surface.
-/
structure GlobalAssemblyActualCNLClusterInputs where
  cnl : ∀ ctx : ActualFailureContext,
    CNLStandardWeightedKraftShellClusterInputData ctx.shell
      erdos260Constants.cStar erdos260Constants.ξ
  returnPkg : ∀ ctx : ActualFailureContext,
    GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ)
  run : ∀ ctx : ActualFailureContext,
    GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ)
  highExcessCharge :
    ∀ ctx : ActualFailureContext,
      HighExcessChargeData
        { chernoff := ctx.chernoff
          cnl := (cnl ctx).toGroundedCNLLocalData.toCNLClusterEncodingData
          tower := ctx.tower
          densePack := ctx.densePack
          returnPkg := (returnPkg ctx).toReturnFactoryData
          run := (run ctx).toRunFactoryData }
        ctx.carryData

namespace GlobalAssemblyActualCNLClusterInputs

/-- Project the CNL cluster leaf to the grounded actual interface. -/
def toGroundedInputs (data : GlobalAssemblyActualCNLClusterInputs) :
    GlobalAssemblyActualGroundedInputs where
  cnl := fun ctx => (data.cnl ctx).toGroundedCNLLocalData
  returnPkg := data.returnPkg
  run := data.run
  highExcessCharge := data.highExcessCharge

end GlobalAssemblyActualCNLClusterInputs

/-- Final bridge with CNL supplied by the L.1.2/G.35 cluster leaf. -/
theorem erdos260_final_actual_cnlCluster
    (data : GlobalAssemblyActualCNLClusterInputs) : Erdos260Statement :=
  erdos260_final_actual_grounded data.toGroundedInputs

/--
Leaf-level actual interface for the still-open phase inputs.

Carry, Chernoff, DensePack, and Tower are closed from the actual shell.  CNL is
the L.1.2/G.35 cluster-to-ladder weighted-Kraft leaf; Return is the
I.5.1/M.2/J.4/L.6 closed package leaf; Run is the separated L.4.1/L.4.2 leaf.
The charge bridge remains scoped to the single actual phase package assembled
from these leaves.
-/
structure GlobalAssemblyActualLeafInputs where
  cnl : ∀ ctx : ActualFailureContext,
    CNLStandardWeightedKraftShellClusterInputData ctx.shell
      erdos260Constants.cStar erdos260Constants.ξ
  returnPkg : ∀ ctx : ActualFailureContext,
    ReturnClosedI51M2J4L6PackageInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : ℝ)
  run : ∀ ctx : ActualFailureContext,
    RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ)
  highExcessCharge :
    ∀ ctx : ActualFailureContext,
      HighExcessChargeData
        { chernoff := ctx.chernoff
          cnl := (cnl ctx).toGroundedCNLLocalData.toCNLClusterEncodingData
          tower := ctx.tower
          densePack := ctx.densePack
          returnPkg :=
            (returnPkg ctx).toReturnSeparatedLocalLeafInputData
              |>.toGroundedReturnLocalData
              |>.toReturnFactoryData
          run := (run ctx).toGroundedRunLocalData.toRunFactoryData }
        ctx.carryData

namespace GlobalAssemblyActualLeafInputs

/-- Project the leaf-level phase inputs to the CNL-cluster actual interface. -/
def toCNLClusterInputs (data : GlobalAssemblyActualLeafInputs) :
    GlobalAssemblyActualCNLClusterInputs where
  cnl := data.cnl
  returnPkg := fun ctx =>
    (data.returnPkg ctx).toReturnSeparatedLocalLeafInputData.toGroundedReturnLocalData
  run := fun ctx => (data.run ctx).toGroundedRunLocalData
  highExcessCharge := data.highExcessCharge

end GlobalAssemblyActualLeafInputs

/-- Final bridge at the current leaf-level actual interface. -/
theorem erdos260_final_actual_leaf
    (data : GlobalAssemblyActualLeafInputs) : Erdos260Statement :=
  erdos260_final_actual_cnlCluster data.toCNLClusterInputs

/-- Definitional six-class accounting against the actual phase masses. -/
def actualPhaseClassAccounting
    {cStar ξ X : ℝ} (phases : SixPhaseFactoryData cStar ξ X) :
    PhaseClassAccountingData phases where
  O_D := termDensePack phases.toClosurePhaseData
  O_P := termChernoff phases.toClosurePhaseData
  O_E := termReturn phases.toClosurePhaseData
  O_CNL := termCnl phases.toClosurePhaseData
  O_bdd := termTower phases.toClosurePhaseData
  O_V := termRun phases.toClosurePhaseData
  hD := le_rfl
  hP := le_rfl
  hE := le_rfl
  hCNL := le_rfl
  hbdd := le_rfl
  hV := le_rfl

/--
Actual leaf interface with the N.24 charge bridge opened to the manuscript
N.2 and N.3.3 leaves.

The phase providers are the same leaf-level CNL/Return/Run inputs as in
`GlobalAssemblyActualLeafInputs`.  Instead of asking for a finished
`HighExcessChargeData`, this surface asks for the canonical-Y variation leaf
and the separated terminal absorption leaf for the actual phase masses.
-/
structure GlobalAssemblyActualN24LeafInputs where
  cnl : ∀ ctx : ActualFailureContext,
    CNLStandardWeightedKraftShellClusterInputData ctx.shell
      erdos260Constants.cStar erdos260Constants.ξ
  returnPkg : ∀ ctx : ActualFailureContext,
    ReturnClosedI51M2J4L6PackageInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : ℝ)
  run : ∀ ctx : ActualFailureContext,
    RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ)
  variation : ∀ ctx : ActualFailureContext,
    CarryHitGapCanonicalYVariationLeafData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos
      (termRun
        (ctx.leafPhases (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
  terminalAbsorption : ∀ ctx : ActualFailureContext,
    ClassicalTerminalN33SeparatedLeafData
      (GroundedC1VDSplitData.ofVariation
        (variation ctx).toVariationClassData.toVariationClassData).termMass
      (termDensePack
        (ctx.leafPhases (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhases (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhases (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhases (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termTower
        (ctx.leafPhases (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)

namespace GlobalAssemblyActualN24LeafInputs

/-- The actual six-phase package assembled from the N.24 leaf interface. -/
def phases (data : GlobalAssemblyActualN24LeafInputs)
    (ctx : ActualFailureContext) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) :=
  ctx.leafPhases (data.cnl ctx) (data.returnPkg ctx) (data.run ctx)

/-- The canonical class-to-phase accounting for the actual phase package. -/
def accounting (data : GlobalAssemblyActualN24LeafInputs)
    (ctx : ActualFailureContext) :
    PhaseClassAccountingData (data.phases ctx) :=
  actualPhaseClassAccounting (data.phases ctx)

/-- Assemble the N.24 terminal-variation input from N.2 and N.3.3 leaves. -/
def n24Input (data : GlobalAssemblyActualN24LeafInputs)
    (ctx : ActualFailureContext) :
    CarryHitGapN24TerminalVariationInputData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos (data.accounting ctx).O_D
      (data.accounting ctx).O_P (data.accounting ctx).O_E
      (data.accounting ctx).O_CNL (data.accounting ctx).O_bdd
      (data.accounting ctx).O_V :=
  (CarryHitGapN24CanonicalYInputData.ofClosedN2N3Leaves
    (data.variation ctx) (data.terminalAbsorption ctx))
      |>.toCanonicalSplitInputData
      |>.toTerminalVariationInputData

/-- The table-routed high-excess local data for the actual phase package. -/
def toTableRoutedHighExcessData
    (data : GlobalAssemblyActualN24LeafInputs)
    (ctx : ActualFailureContext) :
    TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData
      (data.phases ctx) ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos where
  accounting := data.accounting ctx
  n24_input := data.n24Input ctx

/-- The actual high-excess charge bridge derived from N.24 leaves. -/
def highExcessCharge (data : GlobalAssemblyActualN24LeafInputs)
    (ctx : ActualFailureContext) :
    HighExcessChargeData (data.phases ctx) ctx.n24CarryData :=
  tableRoutedSplitPhaseAccountedToHighExcessData
    (data.toTableRoutedHighExcessData ctx)

/-- Project the opened N.24 leaf interface to the actual-consumption interface. -/
def toActualInputs (data : GlobalAssemblyActualN24LeafInputs) :
    GlobalAssemblyActualInputs where
  carryData := ActualFailureContext.n24CarryData
  chernoff := fun ctx => (data.phases ctx).chernoff
  cnl := fun ctx => (data.phases ctx).cnl
  densePack := fun ctx => (data.phases ctx).densePack
  tower := fun ctx => (data.phases ctx).tower
  returnPkg := fun ctx => (data.phases ctx).returnPkg
  run := fun ctx => (data.phases ctx).run
  highExcessCharge := fun ctx => data.highExcessCharge ctx

end GlobalAssemblyActualN24LeafInputs

/-- Final bridge with the charge bridge reduced to N.2/N.3.3 actual leaves. -/
theorem erdos260_final_actual_n24Leaf
    (data : GlobalAssemblyActualN24LeafInputs) : Erdos260Statement :=
  erdos260_final_actual data.toActualInputs

/--
Actual N.24 interface with the Run phase opened to the closed
L.4.1/L.4.2/I.5.2 manuscript package.

This removes the remaining `RunSeparatedLocalLeafInputData` consumption from
the actual final surface; the run leaf is now produced by
`RunClosedL41L42I52PackageInputData.toRunSeparatedLocalLeafInputData`.
-/
structure GlobalAssemblyActualRunPackageN24Inputs where
  cnl : ∀ ctx : ActualFailureContext,
    CNLStandardWeightedKraftShellClusterInputData ctx.shell
      erdos260Constants.cStar erdos260Constants.ξ
  returnPkg : ∀ ctx : ActualFailureContext,
    ReturnClosedI51M2J4L6PackageInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : ℝ)
  run : ∀ ctx : ActualFailureContext,
    RunClosedL41L42I52PackageInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : ℝ)
  variation : ∀ ctx : ActualFailureContext,
    CarryHitGapCanonicalYVariationLeafData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos
      (termRun
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
  terminalAbsorption : ∀ ctx : ActualFailureContext,
    ClassicalTerminalN33SeparatedLeafData
      (GroundedC1VDSplitData.ofVariation
        (variation ctx).toVariationClassData.toVariationClassData).termMass
      (termDensePack
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)

namespace GlobalAssemblyActualRunPackageN24Inputs

/-- Project the closed-run-package interface to the N.24 leaf interface. -/
def toN24LeafInputs (data : GlobalAssemblyActualRunPackageN24Inputs) :
    GlobalAssemblyActualN24LeafInputs where
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := fun ctx => (data.run ctx).toRunSeparatedLocalLeafInputData
  variation := data.variation
  terminalAbsorption := data.terminalAbsorption

end GlobalAssemblyActualRunPackageN24Inputs

/-- Final bridge with Run supplied by the L.4.1/L.4.2/I.5.2 package. -/
theorem erdos260_final_actual_runPackageN24
    (data : GlobalAssemblyActualRunPackageN24Inputs) : Erdos260Statement :=
  erdos260_final_actual_n24Leaf data.toN24LeafInputs

/--
Actual N.24 interface with N.2 opened to the closed N.2.1/N.2.2
first-crossing/drop-density package, and Run opened to its closed manuscript
package.
-/
structure GlobalAssemblyActualClosedN2RunPackageInputs where
  cnl : ∀ ctx : ActualFailureContext,
    CNLStandardWeightedKraftShellClusterInputData ctx.shell
      erdos260Constants.cStar erdos260Constants.ξ
  returnPkg : ∀ ctx : ActualFailureContext,
    ReturnClosedI51M2J4L6PackageInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : ℝ)
  run : ∀ ctx : ActualFailureContext,
    RunClosedL41L42I52PackageInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : ℝ)
  variation : ∀ ctx : ActualFailureContext,
    AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos
      (termRun
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
  terminalAbsorption : ∀ ctx : ActualFailureContext,
    ClassicalTerminalN33SeparatedLeafData
      (GroundedC1VDSplitData.ofVariation
        (variation ctx).toVariationClassData.toVariationClassData).termMass
      (termDensePack
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)

namespace GlobalAssemblyActualClosedN2RunPackageInputs

/-- Project the closed-N.2/run-package interface to the run-package N.24 one. -/
def toRunPackageN24Inputs
    (data : GlobalAssemblyActualClosedN2RunPackageInputs) :
    GlobalAssemblyActualRunPackageN24Inputs where
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  variation := fun ctx => (data.variation ctx).toLeaf
  terminalAbsorption := data.terminalAbsorption

end GlobalAssemblyActualClosedN2RunPackageInputs

/-- Final bridge with N.2 supplied by closed N.2.1/N.2.2 data. -/
theorem erdos260_final_actual_closedN2RunPackage
    (data : GlobalAssemblyActualClosedN2RunPackageInputs) :
    Erdos260Statement :=
  erdos260_final_actual_runPackageN24 data.toRunPackageN24Inputs

/--
Actual interface whose charge input is the closed proof-v4 N.2/N.3 package.

Compared with `GlobalAssemblyActualClosedN2RunPackageInputs`, this surface no
longer asks for a separated terminal leaf.  The terminal side is the
N.24-facing table-routed N.3.3 absorption already bundled in
`AppendixNClosedN2N3InputData`, paired with the closed N.2.1/N.2.2 variation
data for the actual phase masses.
-/
structure GlobalAssemblyActualClosedN2N3RunPackageInputs where
  cnl : ∀ ctx : ActualFailureContext,
    CNLStandardWeightedKraftShellClusterInputData ctx.shell
      erdos260Constants.cStar erdos260Constants.ξ
  returnPkg : ∀ ctx : ActualFailureContext,
    ReturnClosedI51M2J4L6PackageInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : ℝ)
  run : ∀ ctx : ActualFailureContext,
    RunClosedL41L42I52PackageInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : ℝ)
  n2n3 : ∀ ctx : ActualFailureContext,
    AppendixNClosedN2N3InputData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos
      (termDensePack
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termRun
        (ctx.leafPhasesRunPackage
          (cnl ctx) (returnPkg ctx) (run ctx)).toClosurePhaseData)

namespace GlobalAssemblyActualClosedN2N3RunPackageInputs

/-- The actual six-phase package assembled from the closed N.2/N.3 interface. -/
def phases (data : GlobalAssemblyActualClosedN2N3RunPackageInputs)
    (ctx : ActualFailureContext) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) :=
  ctx.leafPhasesRunPackage (data.cnl ctx) (data.returnPkg ctx) (data.run ctx)

/-- Definitional accounting for the actual closed N.2/N.3 phase package. -/
def accounting (data : GlobalAssemblyActualClosedN2N3RunPackageInputs)
    (ctx : ActualFailureContext) :
    PhaseClassAccountingData (data.phases ctx) :=
  actualPhaseClassAccounting (data.phases ctx)

/-- Project the closed N.2/N.3 package to the N.24 terminal-variation input. -/
def n24Input (data : GlobalAssemblyActualClosedN2N3RunPackageInputs)
    (ctx : ActualFailureContext) :
    CarryHitGapN24TerminalVariationInputData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos (data.accounting ctx).O_D
      (data.accounting ctx).O_P (data.accounting ctx).O_E
      (data.accounting ctx).O_CNL (data.accounting ctx).O_bdd
      (data.accounting ctx).O_V :=
  ((data.n2n3 ctx).toN24CanonicalYInputData)
    |>.toCanonicalSplitInputData
    |>.toTerminalVariationInputData

/-- Table-routed high-excess data from the closed N.2/N.3 package. -/
def toTableRoutedHighExcessData
    (data : GlobalAssemblyActualClosedN2N3RunPackageInputs)
    (ctx : ActualFailureContext) :
    TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData
      (data.phases ctx) ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos where
  accounting := data.accounting ctx
  n24_input := data.n24Input ctx

/-- High-excess charge derived directly from closed N.2/N.3 data. -/
def highExcessCharge
    (data : GlobalAssemblyActualClosedN2N3RunPackageInputs)
    (ctx : ActualFailureContext) :
    HighExcessChargeData (data.phases ctx) ctx.n24CarryData :=
  tableRoutedSplitPhaseAccountedToHighExcessData
    (data.toTableRoutedHighExcessData ctx)

/-- Project the closed N.2/N.3 package interface to actual-consumption input. -/
def toActualInputs (data : GlobalAssemblyActualClosedN2N3RunPackageInputs) :
    GlobalAssemblyActualInputs where
  carryData := ActualFailureContext.n24CarryData
  chernoff := fun ctx => (data.phases ctx).chernoff
  cnl := fun ctx => (data.phases ctx).cnl
  densePack := fun ctx => (data.phases ctx).densePack
  tower := fun ctx => (data.phases ctx).tower
  returnPkg := fun ctx => (data.phases ctx).returnPkg
  run := fun ctx => (data.phases ctx).run
  highExcessCharge := fun ctx => data.highExcessCharge ctx

end GlobalAssemblyActualClosedN2N3RunPackageInputs

/-- Final bridge from the actual closed N.2/N.3 package surface. -/
theorem erdos260_final_actual_closedN2N3RunPackage
    (data : GlobalAssemblyActualClosedN2N3RunPackageInputs) :
    Erdos260Statement :=
  erdos260_final_actual data.toActualInputs

/--
Actual final surface with the CNL provider opened to raw L.1.2/G.35 cluster
data.

This keeps Return, Run, and N.2/N.3 at their current closed manuscript-package
boundaries, while replacing the CNL cluster leaf by the explicit selected
transition / ladder Kraft / manuscript budget fields.
-/
structure GlobalAssemblyActualRawCNLClosedN2N3RunPackageInputs where
  cnl : ∀ ctx : ActualFailureContext,
    ActualCNLRawL112G35Data ctx
  returnPkg : ∀ ctx : ActualFailureContext,
    ReturnClosedI51M2J4L6PackageInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : ℝ)
  run : ∀ ctx : ActualFailureContext,
    RunClosedL41L42I52PackageInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : ℝ)
  n2n3 : ∀ ctx : ActualFailureContext,
    AppendixNClosedN2N3InputData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos
      (termDensePack
        (ctx.leafPhasesRunPackage
          ((cnl ctx).toClusterInputData)
          (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesRunPackage
          ((cnl ctx).toClusterInputData)
          (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesRunPackage
          ((cnl ctx).toClusterInputData)
          (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesRunPackage
          ((cnl ctx).toClusterInputData)
          (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesRunPackage
          ((cnl ctx).toClusterInputData)
          (returnPkg ctx) (run ctx)).toClosurePhaseData)
      (termRun
        (ctx.leafPhasesRunPackage
          ((cnl ctx).toClusterInputData)
          (returnPkg ctx) (run ctx)).toClosurePhaseData)

namespace GlobalAssemblyActualRawCNLClosedN2N3RunPackageInputs

/-- Project raw CNL data to the closed N.2/N.3 actual interface. -/
def toClosedN2N3RunPackageInputs
    (data : GlobalAssemblyActualRawCNLClosedN2N3RunPackageInputs) :
    GlobalAssemblyActualClosedN2N3RunPackageInputs where
  cnl := fun ctx => (data.cnl ctx).toClusterInputData
  returnPkg := data.returnPkg
  run := data.run
  n2n3 := data.n2n3

end GlobalAssemblyActualRawCNLClosedN2N3RunPackageInputs

/-- Final bridge from raw L.1.2/G.35 CNL data plus closed N.2/N.3 packages. -/
theorem erdos260_final_actual_rawCNLClosedN2N3RunPackage
    (data : GlobalAssemblyActualRawCNLClosedN2N3RunPackageInputs) :
    Erdos260Statement :=
  erdos260_final_actual_closedN2N3RunPackage
    data.toClosedN2N3RunPackageInputs

/--
Actual final surface with CNL, Return, and Run all opened to their raw
manuscript-facing data.

CNL is raw L.1.2/G.35 cluster data; Return is the seven Prop.
I.5.1/M.2/J.4/L.6 estimates plus scalar smallness; Run is the L.4.1
trichotomy, L.4.2 period-halving estimate, and scalar smallness.  The charge
input remains the closed N.2/N.3 package for the phase masses produced from
these raw providers.
-/
structure GlobalAssemblyActualRawCNLRRClosedN2N3Inputs where
  cnl : ∀ ctx : ActualFailureContext,
    ActualCNLRawL112G35Data ctx
  returnPkg : ∀ ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6Data ctx
  run : ∀ ctx : ActualFailureContext,
    ActualRunRawL41L42I52Data ctx
  n2n3 : ∀ ctx : ActualFailureContext,
    AppendixNClosedN2N3InputData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos
      (termDensePack
        (ctx.leafPhasesRunPackage
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesRunPackage
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesRunPackage
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesRunPackage
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesRunPackage
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termRun
        (ctx.leafPhasesRunPackage
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualRawCNLRRClosedN2N3Inputs

/-- Project raw CNL/Return/Run data to the previous actual interface. -/
def toRawCNLClosedN2N3RunPackageInputs
    (data : GlobalAssemblyActualRawCNLRRClosedN2N3Inputs) :
    GlobalAssemblyActualRawCNLClosedN2N3RunPackageInputs where
  cnl := data.cnl
  returnPkg := fun ctx => (data.returnPkg ctx).toPackageInputData
  run := fun ctx => (data.run ctx).toPackageInputData
  n2n3 := data.n2n3

end GlobalAssemblyActualRawCNLRRClosedN2N3Inputs

/-- Final bridge from raw CNL/Return/Run data plus the closed N.2/N.3 package. -/
theorem erdos260_final_actual_rawCNLRRClosedN2N3
    (data : GlobalAssemblyActualRawCNLRRClosedN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_actual_rawCNLClosedN2N3RunPackage
    data.toRawCNLClosedN2N3RunPackageInputs

/--
Actual N.2/N.3 package whose bounded-dirty-return terminal class is backed by
the proof-v4 L.6 shell-paid Chernoff leaf.

This is deliberately local to the actual final theorem: it mirrors the useful
Bdd/L6 projection without importing the larger proof-v4 certificate module.
-/
structure ActualClosedN2N3BddL6Data
    (ctx : ActualFailureContext)
    (chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    (O_D O_P O_E O_CNL O_bdd O_V : Real) where
  variation :
    AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos O_V
  terminalAbsorption :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
      chernoffLeaf
      (GroundedC1VDSplitData.ofVariation
        variation.toVariationClassData.toVariationClassData).termMass
      O_D O_P O_E O_CNL O_bdd

namespace ActualClosedN2N3BddL6Data

/-- Forget only the L.6 explanation, recovering the ordinary closed N.2/N.3
package consumed by N.24. -/
def toClosedN2N3InputData
    {ctx : ActualFailureContext}
    {chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    (data :
      ActualClosedN2N3BddL6Data ctx chernoffLeaf
        O_D O_P O_E O_CNL O_bdd O_V) :
    AppendixNClosedN2N3InputData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos O_D O_P O_E O_CNL O_bdd O_V where
  variation := data.variation
  terminalAbsorption :=
    data.terminalAbsorption.toClassicalTableRoutedDirectFiveClassTerminalAbsorptionData

end ActualClosedN2N3BddL6Data

/--
Actual final surface with raw CNL/Return/Run providers and an L.6-backed
N.3.3 bounded class.

The Chernoff slot of the actual six-phase package is assembled from the same
regular/shell-paid leaf that backs the bounded terminal class, so this surface
records the manuscript coupling instead of merely adding an unrelated L.6
certificate.
-/
structure GlobalAssemblyActualRawCNLRRClosedN2N3BddL6Inputs where
  chernoff : forall ctx : ActualFailureContext,
    RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real)
  cnl : forall ctx : ActualFailureContext,
    ActualCNLRawL112G35Data ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6Data ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52Data ctx
  n2n3 : forall ctx : ActualFailureContext,
    ActualClosedN2N3BddL6Data ctx (chernoff ctx)
      (termDensePack
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termRun
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualRawCNLRRClosedN2N3BddL6Inputs

/-- The actual phase package assembled from the coupled shell-paid Chernoff and
raw CNL/Return/Run providers. -/
def phases (data : GlobalAssemblyActualRawCNLRRClosedN2N3BddL6Inputs)
    (ctx : ActualFailureContext) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  ctx.leafPhasesWithChernoffLeaf
    (data.chernoff ctx)
    ((data.cnl ctx).toClusterInputData)
    ((data.returnPkg ctx).toPackageInputData)
    ((data.run ctx).toPackageInputData)

/-- Definitional accounting for the coupled Bdd/L6 actual phase package. -/
def accounting (data : GlobalAssemblyActualRawCNLRRClosedN2N3BddL6Inputs)
    (ctx : ActualFailureContext) :
    PhaseClassAccountingData (data.phases ctx) :=
  actualPhaseClassAccounting (data.phases ctx)

/-- Project the L.6-backed closed N.2/N.3 package to the N.24 terminal-variation
input for the coupled actual phases. -/
def n24Input (data : GlobalAssemblyActualRawCNLRRClosedN2N3BddL6Inputs)
    (ctx : ActualFailureContext) :
    CarryHitGapN24TerminalVariationInputData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos (data.accounting ctx).O_D
      (data.accounting ctx).O_P (data.accounting ctx).O_E
      (data.accounting ctx).O_CNL (data.accounting ctx).O_bdd
      (data.accounting ctx).O_V :=
  ((data.n2n3 ctx).toClosedN2N3InputData.toN24CanonicalYInputData)
    |>.toCanonicalSplitInputData
    |>.toTerminalVariationInputData

/-- Table-routed high-excess data from the coupled Bdd/L6 package. -/
def toTableRoutedHighExcessData
    (data : GlobalAssemblyActualRawCNLRRClosedN2N3BddL6Inputs)
    (ctx : ActualFailureContext) :
    TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData
      (data.phases ctx) ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos where
  accounting := data.accounting ctx
  n24_input := data.n24Input ctx

/-- High-excess charge derived from the coupled Bdd/L6 N.2/N.3 data. -/
def highExcessCharge
    (data : GlobalAssemblyActualRawCNLRRClosedN2N3BddL6Inputs)
    (ctx : ActualFailureContext) :
    HighExcessChargeData (data.phases ctx) ctx.n24CarryData :=
  tableRoutedSplitPhaseAccountedToHighExcessData
    (data.toTableRoutedHighExcessData ctx)

/-- Project the coupled Bdd/L6 actual interface to the final actual-consumption
input. -/
def toActualInputs
    (data : GlobalAssemblyActualRawCNLRRClosedN2N3BddL6Inputs) :
    GlobalAssemblyActualInputs where
  carryData := ActualFailureContext.n24CarryData
  chernoff := fun ctx => (data.phases ctx).chernoff
  cnl := fun ctx => (data.phases ctx).cnl
  densePack := fun ctx => (data.phases ctx).densePack
  tower := fun ctx => (data.phases ctx).tower
  returnPkg := fun ctx => (data.phases ctx).returnPkg
  run := fun ctx => (data.phases ctx).run
  highExcessCharge := fun ctx => data.highExcessCharge ctx

end GlobalAssemblyActualRawCNLRRClosedN2N3BddL6Inputs

/-- Final bridge from raw CNL/Return/Run data plus coupled Bdd/L6 N.2/N.3. -/
theorem erdos260_final_actual_rawCNLRRClosedN2N3BddL6
    (data : GlobalAssemblyActualRawCNLRRClosedN2N3BddL6Inputs) :
    Erdos260Statement :=
  erdos260_final_actual data.toActualInputs

/--
Actual closed-package final surface with CNL supplied by the direct
weighted-Kraft shell leaf.  This matches manuscript providers that already
bundle Return and Run as closed local packages, while retaining the L.6-backed
N.2/N.3 actual charge bridge.
-/
structure GlobalAssemblyActualWeightedKraftCNLClosedN2N3BddL6RunPackageInputs where
  chernoff : ∀ ctx : ActualFailureContext,
    RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real)
  cnl : ∀ ctx : ActualFailureContext,
    CNLStandardWeightedKraftShellInputData ctx.shell erdos260Constants.cStar
      erdos260Constants.ξ
  returnPkg : ∀ ctx : ActualFailureContext,
    ReturnClosedI51M2J4L6PackageInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real)
  run : ∀ ctx : ActualFailureContext,
    RunClosedL41L42I52PackageInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real)
  n2n3 : ∀ ctx : ActualFailureContext,
    ActualClosedN2N3BddL6Data ctx (chernoff ctx)
      (termDensePack
        (ctx.leafPhasesWithWeightedCNL
          (chernoff ctx) (cnl ctx) (returnPkg ctx)
          (run ctx)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithWeightedCNL
          (chernoff ctx) (cnl ctx) (returnPkg ctx)
          (run ctx)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithWeightedCNL
          (chernoff ctx) (cnl ctx) (returnPkg ctx)
          (run ctx)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithWeightedCNL
          (chernoff ctx) (cnl ctx) (returnPkg ctx)
          (run ctx)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithWeightedCNL
          (chernoff ctx) (cnl ctx) (returnPkg ctx)
          (run ctx)).toClosurePhaseData)
      (termRun
        (ctx.leafPhasesWithWeightedCNL
          (chernoff ctx) (cnl ctx) (returnPkg ctx)
          (run ctx)).toClosurePhaseData)

namespace GlobalAssemblyActualWeightedKraftCNLClosedN2N3BddL6RunPackageInputs

/-- The actual six-phase package assembled from direct weighted-Kraft CNL and
closed Return/Run packages. -/
def phases
    (data : GlobalAssemblyActualWeightedKraftCNLClosedN2N3BddL6RunPackageInputs)
    (ctx : ActualFailureContext) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  ctx.leafPhasesWithWeightedCNL
    (data.chernoff ctx) (data.cnl ctx) (data.returnPkg ctx) (data.run ctx)

/-- Definitional phase accounting for the direct weighted-Kraft closed package. -/
def accounting
    (data : GlobalAssemblyActualWeightedKraftCNLClosedN2N3BddL6RunPackageInputs)
    (ctx : ActualFailureContext) :
    PhaseClassAccountingData (data.phases ctx) :=
  actualPhaseClassAccounting (data.phases ctx)

/-- Project the closed N.2/N.3 package to the N.24 terminal-variation input. -/
def n24Input
    (data : GlobalAssemblyActualWeightedKraftCNLClosedN2N3BddL6RunPackageInputs)
    (ctx : ActualFailureContext) :
    CarryHitGapN24TerminalVariationInputData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos (data.accounting ctx).O_D
      (data.accounting ctx).O_P (data.accounting ctx).O_E
      (data.accounting ctx).O_CNL (data.accounting ctx).O_bdd
      (data.accounting ctx).O_V :=
  ((data.n2n3 ctx).toClosedN2N3InputData.toN24CanonicalYInputData)
    |>.toCanonicalSplitInputData
    |>.toTerminalVariationInputData

/-- Table-routed high-excess data for the direct weighted-Kraft closed package. -/
def toTableRoutedHighExcessData
    (data : GlobalAssemblyActualWeightedKraftCNLClosedN2N3BddL6RunPackageInputs)
    (ctx : ActualFailureContext) :
    TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData
      (data.phases ctx) ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos where
  accounting := data.accounting ctx
  n24_input := data.n24Input ctx

/-- High-excess charge on the actual direct weighted-Kraft phases. -/
def highExcessCharge
    (data : GlobalAssemblyActualWeightedKraftCNLClosedN2N3BddL6RunPackageInputs)
    (ctx : ActualFailureContext) :
    HighExcessChargeData (data.phases ctx) ctx.n24CarryData :=
  tableRoutedSplitPhaseAccountedToHighExcessData
    (data.toTableRoutedHighExcessData ctx)

/-- Project the direct weighted-Kraft closed-package surface to the final
actual-consumption interface. -/
def toActualInputs
    (data : GlobalAssemblyActualWeightedKraftCNLClosedN2N3BddL6RunPackageInputs) :
    GlobalAssemblyActualInputs where
  carryData := ActualFailureContext.n24CarryData
  chernoff := fun ctx => (data.phases ctx).chernoff
  cnl := fun ctx => (data.phases ctx).cnl
  densePack := fun ctx => (data.phases ctx).densePack
  tower := fun ctx => (data.phases ctx).tower
  returnPkg := fun ctx => (data.phases ctx).returnPkg
  run := fun ctx => (data.phases ctx).run
  highExcessCharge := fun ctx => data.highExcessCharge ctx

end GlobalAssemblyActualWeightedKraftCNLClosedN2N3BddL6RunPackageInputs

/-- Final bridge from direct weighted-Kraft CNL, closed Return/Run packages, and
L.6-backed closed N.2/N.3 data. -/
theorem erdos260_final_actual_weightedKraftCNLClosedN2N3BddL6RunPackage
    (data : GlobalAssemblyActualWeightedKraftCNLClosedN2N3BddL6RunPackageInputs) :
    Erdos260Statement :=
  erdos260_final_actual data.toActualInputs

/-- A nonempty provider for the direct weighted-Kraft closed-package surface
proves the final statement. -/
theorem erdos260_unconditional_from_weightedKraftCNLClosedN2N3BddL6RunPackage_provider
    (hprovider :
      Nonempty
        GlobalAssemblyActualWeightedKraftCNLClosedN2N3BddL6RunPackageInputs) :
    Erdos260Statement :=
  hprovider.elim
    erdos260_final_actual_weightedKraftCNLClosedN2N3BddL6RunPackage

/--
Actual final surface with the six-phase package supplied explicitly.

This is the narrow bridge used by certificate modules whose phase package has
already been assembled from the proof-v4 objects.  The high-excess route is
then required only for that explicit package, and the L.6-backed N.2/N.3 data
is indexed by its six terminal budgets.
-/
structure GlobalAssemblyActualExplicitPhaseClosedN2N3BddL6Inputs where
  phases : forall ctx : ActualFailureContext,
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real)
  chernoff : forall ctx : ActualFailureContext,
    RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real)
  n2n3 : forall ctx : ActualFailureContext,
    ActualClosedN2N3BddL6Data ctx (chernoff ctx)
      (termDensePack (phases ctx).toClosurePhaseData)
      (termChernoff (phases ctx).toClosurePhaseData)
      (termReturn (phases ctx).toClosurePhaseData)
      (termCnl (phases ctx).toClosurePhaseData)
      (termTower (phases ctx).toClosurePhaseData)
      (termRun (phases ctx).toClosurePhaseData)

namespace GlobalAssemblyActualExplicitPhaseClosedN2N3BddL6Inputs

/-- Phase accounting for the explicitly supplied actual phase package. -/
def accounting
    (data : GlobalAssemblyActualExplicitPhaseClosedN2N3BddL6Inputs)
    (ctx : ActualFailureContext) :
    PhaseClassAccountingData (data.phases ctx) :=
  actualPhaseClassAccounting (data.phases ctx)

/-- Project the closed N.2/N.3 package to the N.24 terminal-variation input. -/
def n24Input
    (data : GlobalAssemblyActualExplicitPhaseClosedN2N3BddL6Inputs)
    (ctx : ActualFailureContext) :
    CarryHitGapN24TerminalVariationInputData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos (data.accounting ctx).O_D
      (data.accounting ctx).O_P (data.accounting ctx).O_E
      (data.accounting ctx).O_CNL (data.accounting ctx).O_bdd
      (data.accounting ctx).O_V :=
  ((data.n2n3 ctx).toClosedN2N3InputData.toN24CanonicalYInputData)
    |>.toCanonicalSplitInputData
    |>.toTerminalVariationInputData

/-- Table-routed high-excess data for the explicitly supplied phase package. -/
def toTableRoutedHighExcessData
    (data : GlobalAssemblyActualExplicitPhaseClosedN2N3BddL6Inputs)
    (ctx : ActualFailureContext) :
    TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData
      (data.phases ctx) ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos where
  accounting := data.accounting ctx
  n24_input := data.n24Input ctx

/-- High-excess charge derived only for the explicit actual phases. -/
def highExcessCharge
    (data : GlobalAssemblyActualExplicitPhaseClosedN2N3BddL6Inputs)
    (ctx : ActualFailureContext) :
    HighExcessChargeData (data.phases ctx) ctx.n24CarryData :=
  tableRoutedSplitPhaseAccountedToHighExcessData
    (data.toTableRoutedHighExcessData ctx)

/-- Project the explicit-phase surface to the final actual-consumption
interface. -/
def toActualInputs
    (data : GlobalAssemblyActualExplicitPhaseClosedN2N3BddL6Inputs) :
    GlobalAssemblyActualInputs where
  carryData := ActualFailureContext.n24CarryData
  chernoff := fun ctx => (data.phases ctx).chernoff
  cnl := fun ctx => (data.phases ctx).cnl
  densePack := fun ctx => (data.phases ctx).densePack
  tower := fun ctx => (data.phases ctx).tower
  returnPkg := fun ctx => (data.phases ctx).returnPkg
  run := fun ctx => (data.phases ctx).run
  highExcessCharge := fun ctx => data.highExcessCharge ctx

end GlobalAssemblyActualExplicitPhaseClosedN2N3BddL6Inputs

/-- Final bridge from explicit actual phases and L.6-backed closed N.2/N.3
data. -/
theorem erdos260_final_actual_explicitPhaseClosedN2N3BddL6
    (data : GlobalAssemblyActualExplicitPhaseClosedN2N3BddL6Inputs) :
    Erdos260Statement :=
  erdos260_final_actual data.toActualInputs

/-- A nonempty explicit-phase provider proves the final statement. -/
theorem erdos260_unconditional_from_explicitPhaseClosedN2N3BddL6_provider
    (hprovider :
      Nonempty GlobalAssemblyActualExplicitPhaseClosedN2N3BddL6Inputs) :
    Erdos260Statement :=
  hprovider.elim erdos260_final_actual_explicitPhaseClosedN2N3BddL6

/--
Raw actual proof-v4 Lemma 22.1A shell-paid Chernoff data.

The stopped tree is the selected regular/shell-paid family; `Ysh` is the
nonnegative shell-paid multiplier, and `area_small` is the final layer-cake
smallness comparison used to fit the family inside the Chernoff phase budget.
-/
structure ActualShellPaidChernoffRawData (ctx : ActualFailureContext) where
  stoppedTree :
    ChernoffStoppedTreeInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real)
  Ysh : stoppedTree.Path -> Real
  hYsh : forall b, b ∈ stoppedTree.paths -> 0 <= Ysh b
  area_small :
    (∑ b ∈ stoppedTree.paths, (stoppedTree.weight b : Real) * Ysh b) <=
      erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6

namespace ActualShellPaidChernoffRawData

/-- Package the raw stopped-tree layer-cake data as the regular/shell-paid
Chernoff leaf consumed by the actual final interface. -/
def toChernoffLeaf {ctx : ActualFailureContext}
    (data : ActualShellPaidChernoffRawData ctx) :
    RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real) :=
  RegularShellPaidChernoff22_1AInputData.ofAreaLayerSumStoppedTree
    data.stoppedTree data.Ysh data.hYsh data.area_small

end ActualShellPaidChernoffRawData

/--
Field-level actual stopped-tree Chernoff data for the selected shell-paid
family.

This exposes the stopped family itself instead of accepting an already-bundled
`ChernoffStoppedTreeInputData`: paths, nonnegative weights, costs, the
tilt/tail scalars, the Lemma 22.1 shell-budget certificate, and the shell-paid
layer-cake multiplier are all visible at the actual final boundary.
-/
structure ActualShellPaidChernoffStoppedTreeFieldsData
    (ctx : ActualFailureContext) where
  Path : Type
  paths : Finset Path
  weight : Path -> {x : Real // 0 <= x}
  cost : Path -> Nat
  Y : Nat
  m : Nat
  z : {z : Real // 1 <= z}
  root : Real
  A : Real
  B : Real
  chernoff_input :
    ChernoffShellBudgetData paths (fun p => (weight p : Real)) cost (z : Real)
      root A B m Y erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real)
  Ysh : Path -> Real
  hYsh : forall b, b ∈ paths -> 0 <= Ysh b
  area_small :
    (∑ b ∈ paths, (weight b : Real) * Ysh b) <=
      erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6

namespace ActualShellPaidChernoffStoppedTreeFieldsData

/-- Bundle the visible stopped-tree fields as the standard stopped-tree
Chernoff input. -/
def toStoppedTreeInputData {ctx : ActualFailureContext}
    (data : ActualShellPaidChernoffStoppedTreeFieldsData ctx) :
    ChernoffStoppedTreeInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) where
  Path := data.Path
  paths := data.paths
  weight := data.weight
  cost := data.cost
  Y := data.Y
  m := data.m
  z := data.z
  root := data.root
  A := data.A
  B := data.B
  chernoff_input := data.chernoff_input

/-- Project the visible stopped-tree fields to the raw shell-paid Chernoff
surface. -/
def toShellPaidChernoffRawData {ctx : ActualFailureContext}
    (data : ActualShellPaidChernoffStoppedTreeFieldsData ctx) :
    ActualShellPaidChernoffRawData ctx where
  stoppedTree := data.toStoppedTreeInputData
  Ysh := data.Ysh
  hYsh := data.hYsh
  area_small := data.area_small

end ActualShellPaidChernoffStoppedTreeFieldsData

/--
Actual stopped-tree Chernoff data with the Lemma 22.1 shell budget split into
its two manuscript pieces: pointwise/aggregate moment control and the final
tail comparison.
-/
structure ActualShellPaidChernoffSplitBudgetFieldsData
    (ctx : ActualFailureContext) where
  Path : Type
  paths : Finset Path
  weight : Path -> {x : Real // 0 <= x}
  cost : Path -> Nat
  Y : Nat
  m : Nat
  z : {z : Real // 1 <= z}
  root : Real
  A : Real
  B : Real
  tiltBudget :
    ChernoffPointwiseMomentData paths (fun p => (weight p : Real)) cost
      (z : Real) root A B m
  tailBudget :
    ChernoffTailBudgetData root A (z : Real) erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real) m Y
  Ysh : Path -> Real
  hYsh : forall b, b ∈ paths -> 0 <= Ysh b
  area_small :
    (∑ b ∈ paths, (weight b : Real) * Ysh b) <=
      erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6

namespace ActualShellPaidChernoffSplitBudgetFieldsData

/-- Bundle the split Lemma 22.1 budget fields as the stopped-tree actual
Chernoff data used by the current strongest bridge. -/
def toStoppedTreeFieldsData {ctx : ActualFailureContext}
    (data : ActualShellPaidChernoffSplitBudgetFieldsData ctx) :
    ActualShellPaidChernoffStoppedTreeFieldsData ctx where
  Path := data.Path
  paths := data.paths
  weight := data.weight
  cost := data.cost
  Y := data.Y
  m := data.m
  z := data.z
  root := data.root
  A := data.A
  B := data.B
  chernoff_input := {
    tiltBudget := data.tiltBudget
    tailBudget := data.tailBudget }
  Ysh := data.Ysh
  hYsh := data.hYsh
  area_small := data.area_small

end ActualShellPaidChernoffSplitBudgetFieldsData

/--
Actual stopped-tree Chernoff data with the tail side exposed as the manuscript
exponential-tail comparison.

The pointwise/moment certificate remains separate, and the tail certificate now
records the length condition `m <= lengthSlope * Y`, the exponential decay
bound, and the final phase-budget smallness comparison.
-/
structure ActualShellPaidChernoffExponentialTailFieldsData
    (ctx : ActualFailureContext) where
  Path : Type
  paths : Finset Path
  weight : Path -> {x : Real // 0 <= x}
  cost : Path -> Nat
  Y : Nat
  m : Nat
  z : {z : Real // 1 <= z}
  root : Real
  A : Real
  B : Real
  tiltBudget :
    ChernoffPointwiseMomentData paths (fun p => (weight p : Real)) cost
      (z : Real) root A B m
  tailBudget :
    ChernoffExponentialTailBudgetData root A (z : Real)
      erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : Real) m Y
  Ysh : Path -> Real
  hYsh : forall b, b ∈ paths -> 0 <= Ysh b
  area_small :
    (∑ b ∈ paths, (weight b : Real) * Ysh b) <=
      erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6

namespace ActualShellPaidChernoffExponentialTailFieldsData

/-- Project the exponential-tail presentation to the split shell-budget
presentation. -/
def toSplitBudgetFieldsData {ctx : ActualFailureContext}
    (data : ActualShellPaidChernoffExponentialTailFieldsData ctx) :
    ActualShellPaidChernoffSplitBudgetFieldsData ctx where
  Path := data.Path
  paths := data.paths
  weight := data.weight
  cost := data.cost
  Y := data.Y
  m := data.m
  z := data.z
  root := data.root
  A := data.A
  B := data.B
  tiltBudget := data.tiltBudget
  tailBudget := data.tailBudget.toTailBudgetData
  Ysh := data.Ysh
  hYsh := data.hYsh
  area_small := data.area_small

end ActualShellPaidChernoffExponentialTailFieldsData

/--
Actual stopped-tree Chernoff data with the pointwise tilt and aggregate moment
budget exposed as separate Lemma 22.1 inputs, while the tail side remains in
the manuscript exponential-tail form.
-/
structure ActualShellPaidChernoffTiltMomentExponentialTailFieldsData
    (ctx : ActualFailureContext) where
  Path : Type
  paths : Finset Path
  weight : Path -> {x : Real // 0 <= x}
  cost : Path -> Nat
  Y : Nat
  m : Nat
  z : {z : Real // 1 <= z}
  root : Real
  A : Real
  B : Real
  tilt :
    ChernoffPointwiseTiltData paths (fun p => (weight p : Real)) cost
      (z : Real) B
  momentBudget :
    ChernoffMomentBudgetData paths B root A m
  tailBudget :
    ChernoffExponentialTailBudgetData root A (z : Real)
      erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : Real) m Y
  Ysh : Path -> Real
  hYsh : forall b, b ∈ paths -> 0 <= Ysh b
  area_small :
    (∑ b ∈ paths, (weight b : Real) * Ysh b) <=
      erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6

namespace ActualShellPaidChernoffTiltMomentExponentialTailFieldsData

/-- Bundle the separated tilt and moment certificates as the exponential-tail
Chernoff surface. -/
def toExponentialTailFieldsData {ctx : ActualFailureContext}
    (data : ActualShellPaidChernoffTiltMomentExponentialTailFieldsData ctx) :
    ActualShellPaidChernoffExponentialTailFieldsData ctx where
  Path := data.Path
  paths := data.paths
  weight := data.weight
  cost := data.cost
  Y := data.Y
  m := data.m
  z := data.z
  root := data.root
  A := data.A
  B := data.B
  tiltBudget := {
    tilt := data.tilt
    momentBudget := data.momentBudget }
  tailBudget := data.tailBudget
  Ysh := data.Ysh
  hYsh := data.hYsh
  area_small := data.area_small

end ActualShellPaidChernoffTiltMomentExponentialTailFieldsData

/--
Actual stopped-tree Chernoff data with the finite-family pointwise and moment
budget closed canonically from the total tilted mass.

This is the finite part of Lemma 22.1 in its most concrete form: `B` is the
finite tilted mass, `root = |paths| * B`, `A = 1`, and `m = 0`.  The manuscript
exponential-tail comparison remains a separate large-scale input.
-/
structure ActualShellPaidChernoffFiniteSumExponentialTailFieldsData
    (ctx : ActualFailureContext) where
  Path : Type
  paths : Finset Path
  weight : Path -> {x : Real // 0 <= x}
  cost : Path -> Nat
  Y : Nat
  z : {z : Real // 1 <= z}
  tailBudget :
    ChernoffExponentialTailBudgetData
      ((paths.card : Real) *
        (paths.sum (fun p => (weight p : Real) * (z : Real) ^ cost p)))
      1 (z : Real) erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) 0 Y
  Ysh : Path -> Real
  hYsh : forall b, b ∈ paths -> 0 <= Ysh b
  area_small :
    (∑ b ∈ paths, (weight b : Real) * Ysh b) <=
      erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6

namespace ActualShellPaidChernoffFiniteSumExponentialTailFieldsData

/-- The total finite tilted mass used as the canonical pointwise budget. -/
def tiltedMass {ctx : ActualFailureContext}
    (data : ActualShellPaidChernoffFiniteSumExponentialTailFieldsData ctx) :
    Real :=
  data.paths.sum
    (fun p => (data.weight p : Real) * (data.z : Real) ^ data.cost p)

/-- The canonical finite-family root `|paths| * B`. -/
def finiteRoot {ctx : ActualFailureContext}
    (data : ActualShellPaidChernoffFiniteSumExponentialTailFieldsData ctx) :
    Real :=
  (data.paths.card : Real) * data.tiltedMass

/-- Close the finite pointwise and aggregate moment part using the finite-sum
Lemma 22.1 constructors. -/
def toTiltMomentExponentialTailFieldsData {ctx : ActualFailureContext}
    (data : ActualShellPaidChernoffFiniteSumExponentialTailFieldsData ctx) :
    ActualShellPaidChernoffTiltMomentExponentialTailFieldsData ctx where
  Path := data.Path
  paths := data.paths
  weight := data.weight
  cost := data.cost
  Y := data.Y
  m := 0
  z := data.z
  root := data.finiteRoot
  A := 1
  B := data.tiltedMass
  tilt := ChernoffPointwiseTiltData.ofFiniteSumBudget
    data.paths data.weight data.cost data.z
  momentBudget :=
    (ChernoffPointwiseMomentData.ofFiniteSumBudget
      data.paths data.weight data.cost data.z).momentBudget
  tailBudget := data.tailBudget
  Ysh := data.Ysh
  hYsh := data.hYsh
  area_small := data.area_small

/-- The regular shell-paid Chernoff leaf induced by the canonical finite-sum
Lemma 22.1 data. -/
def toChernoffLeaf {ctx : ActualFailureContext}
    (data : ActualShellPaidChernoffFiniteSumExponentialTailFieldsData ctx) :
    RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real) :=
  data.toTiltMomentExponentialTailFieldsData
    |>.toExponentialTailFieldsData
    |>.toSplitBudgetFieldsData
    |>.toStoppedTreeFieldsData
    |>.toShellPaidChernoffRawData
    |>.toChernoffLeaf

end ActualShellPaidChernoffFiniteSumExponentialTailFieldsData

/--
Actual stopped-tree Chernoff data with the finite-family moment part closed and
the tail side in the zero-length normalization.

This is the tail form naturally paired with the canonical finite-sum
construction: `A = 1` and `m = 0`, so the exponential-tail record's length
condition is automatic and only the ratio `root / z^Y` remains.
-/
structure ActualShellPaidChernoffFiniteSumZeroLengthTailFieldsData
    (ctx : ActualFailureContext) where
  Path : Type
  paths : Finset Path
  weight : Path -> {x : Real // 0 <= x}
  cost : Path -> Nat
  Y : Nat
  z : {z : Real // 1 <= z}
  tailBudget :
    ChernoffZeroLengthExponentialTailData
      ((paths.card : Real) *
        (paths.sum (fun p => (weight p : Real) * (z : Real) ^ cost p)))
      (z : Real) erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) Y
  Ysh : Path -> Real
  hYsh : forall b, b ∈ paths -> 0 <= Ysh b
  area_small :
    (∑ b ∈ paths, (weight b : Real) * Ysh b) <=
      erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6

namespace ActualShellPaidChernoffFiniteSumZeroLengthTailFieldsData

/-- The total finite tilted mass used as the canonical pointwise budget. -/
def tiltedMass {ctx : ActualFailureContext}
    (data : ActualShellPaidChernoffFiniteSumZeroLengthTailFieldsData ctx) :
    Real :=
  data.paths.sum
    (fun p => (data.weight p : Real) * (data.z : Real) ^ data.cost p)

/-- Project the zero-length tail presentation to the finite-sum exponential-tail
actual Chernoff surface. -/
def toFiniteSumExponentialTailFieldsData {ctx : ActualFailureContext}
    (data : ActualShellPaidChernoffFiniteSumZeroLengthTailFieldsData ctx) :
    ActualShellPaidChernoffFiniteSumExponentialTailFieldsData ctx where
  Path := data.Path
  paths := data.paths
  weight := data.weight
  cost := data.cost
  Y := data.Y
  z := data.z
  tailBudget := data.tailBudget.toChernoffExponentialTailBudgetData
  Ysh := data.Ysh
  hYsh := data.hYsh
  area_small := data.area_small

/-- The regular shell-paid Chernoff leaf induced by finite-sum zero-length tail
data. -/
def toChernoffLeaf {ctx : ActualFailureContext}
    (data : ActualShellPaidChernoffFiniteSumZeroLengthTailFieldsData ctx) :
    RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real) :=
  data.toFiniteSumExponentialTailFieldsData.toChernoffLeaf

end ActualShellPaidChernoffFiniteSumZeroLengthTailFieldsData

/--
Actual stopped-tree Chernoff data with the zero-length tail split into the
manuscript numerator root bound and the X-free scalar smallness comparison.
-/
structure ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData
    (ctx : ActualFailureContext) where
  Path : Type
  paths : Finset Path
  weight : Path -> {x : Real // 0 <= x}
  cost : Path -> Nat
  Y : Nat
  z : {z : Real // 1 <= z}
  tailConstant : Real
  tailExponent : Nat
  root_bound :
    ((paths.card : Real) *
        (paths.sum (fun p => (weight p : Real) * (z : Real) ^ cost p))) <=
      tailConstant * (ctx.shell.X : Real) * (z : Real) ^ Y /
        (2 : Real) ^ tailExponent
  tail_small_scalar :
    tailConstant / (2 : Real) ^ tailExponent <=
      erdos260Constants.cStar * erdos260Constants.ξ / 6
  Ysh : Path -> Real
  hYsh : forall b, b ∈ paths -> 0 <= Ysh b
  area_small :
    (∑ b ∈ paths, (weight b : Real) * Ysh b) <=
      erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6

namespace ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData

/-- The total finite tilted mass used as the canonical pointwise budget. -/
def tiltedMass {ctx : ActualFailureContext}
    (data : ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx) :
    Real :=
  data.paths.sum
    (fun p => (data.weight p : Real) * (data.z : Real) ^ data.cost p)

/-- Project numerator-style tail data to the zero-length Chernoff actual
surface. -/
def toZeroLengthTailFieldsData {ctx : ActualFailureContext}
    (data : ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx) :
    ActualShellPaidChernoffFiniteSumZeroLengthTailFieldsData ctx where
  Path := data.Path
  paths := data.paths
  weight := data.weight
  cost := data.cost
  Y := data.Y
  z := data.z
  tailBudget :=
    ChernoffZeroLengthExponentialTailData.ofRootBoundAndScalarSmallness
      data.tailConstant data.tailExponent
      (by linarith [data.z.property])
      (Nat.cast_nonneg ctx.shell.X)
      data.root_bound
      data.tail_small_scalar
  Ysh := data.Ysh
  hYsh := data.hYsh
  area_small := data.area_small

/-- The regular shell-paid Chernoff leaf induced by numerator-style finite-sum
tail data. -/
def toChernoffLeaf {ctx : ActualFailureContext}
    (data : ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx) :
    RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real) :=
  data.toZeroLengthTailFieldsData.toChernoffLeaf

end ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData

/--
Raw actual N.2.0/N.2.1/N.2.2 first-crossing data for one failing shell.

This is the manuscript-facing content of the variation class: branch drops,
shell-`Q` ordered first-crossing records, priority injectivity, drop-density
regularity/first inequality, and the rolling-window budget.
-/
structure ActualRawN2FirstCrossingData
    (ctx : ActualFailureContext) (O_V : Real) where
  Branch : Type
  VarDrop : Real
  Cmul : Nat
  s : Nat
  branches : Finset Branch
  dropMass :
    (T : Real) -> Branch -> (e : Nat) ->
      {x : Real // 0 <= x /\
        x <=
          AppendixN.crossingIndicator (T + ctx.n24CarryLocal.Y)
            (AppendixN.windowSum
              (fun n =>
                (hitGap
                  (ctx.n24CarryLocal.toCarryData
                    erdos260Constants_cPr_le_half
                    ctx.hc0Small ctx.n24SupportCount_pos).a n : Real)) s) e}
  K :
    Finset {e : Nat //
      e ∈ carryHitGapAdmissibleEdgeWindow
        ctx.n24CarryLocal ctx.hc0Small ctx.n24SupportCount_pos s}
  A : Set Real
  labelCount : Nat
  DOrdered :
    Real ->
      {D : AppendixN.FirstCrossingRecordData Branch ctx.shell.Q (Fin labelCount) //
        forall e, D.loIdx e <= D.hiIdx e}
  hinj :
    forall T (e : Nat), forall b,
      b ∈ branches.filter (fun b => (dropMass T b e : Real) ≠ 0) ->
      forall b',
        b' ∈ branches.filter (fun b => (dropMass T b e : Real) ≠ 0) ->
        ((DOrdered T).1).record e b = ((DOrdered T).1).record e b' ->
        ((DOrdered T).1).startResidue b = ((DOrdered T).1).startResidue b' ->
        b = b'
  hA : MeasurableSet A
  hdrop_int :
    MeasureTheory.IntegrableOn
      (carryHitGapDropDensity branches
        (fun T b e => (dropMass T b e : Real))
        (carryHitGapWindowEdgeSet s K)) A MeasureTheory.volume
  hvar :
    VarDrop <=
      (Cmul : Real) * ctx.n24CarryLocal.Y *
        ∫ T in A,
          carryHitGapDropDensity branches
            (fun T b e => (dropMass T b e : Real))
            (carryHitGapWindowEdgeSet s K) T ∂MeasureTheory.volume
  hWindow :
    ((Cmul : Real) *
        (((ctx.shell.Q * labelCount * ctx.shell.Q : Nat) : Real))) *
        ctx.n24CarryLocal.Y *
          (2 *
              (((ctx.n24CarryLocal.toCarryData erdos260Constants_cPr_le_half
                ctx.hc0Small ctx.n24SupportCount_pos).L + carryB ctx.shell.Q + 1 :
                  Nat) : Real) *
            ((carryHitGapWindowEdgeSet s K).card : Real)) <= O_V

namespace ActualRawN2FirstCrossingData

/-- Package raw N.2 first-crossing fields as the closed N.2.1/N.2.2 variation
input consumed by the actual N.24 bridge. -/
def toVariationData {ctx : ActualFailureContext} {O_V : Real}
    (data : ActualRawN2FirstCrossingData ctx O_V) :
    AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos O_V :=
  AppendixNVariationClosedN21N22InputData.ofRawShellQFirstCrossingRecordDensityFields
    data.VarDrop data.Cmul data.s data.branches data.dropMass data.K data.A
    data.labelCount data.DOrdered data.hinj data.hA data.hdrop_int data.hvar
    data.hWindow

end ActualRawN2FirstCrossingData

/--
Raw actual N.3.3 terminal table with the L.6 low/paid bounded-class split.

The N.2 variation package fixes the terminal remainder.  This record then
exposes the exact terminal table, the dense/progress/endpoint/CNL class
dominations, and the L.6 shell-paid split for the bounded class.
-/
structure ActualRawTerminalLowPaidData
    (ctx : ActualFailureContext)
    (chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    {O_V : Real}
    (variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V)
    (O_D O_P O_E O_CNL O_bdd : Real) where
  sigma : Type
  iota : Type
  linIota : LinearOrder iota
  E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) linIota
  row : iota -> AppendixN.TerminalRow
  supp : iota -> Nat
  thr : iota -> Nat
  terminalWeight : OutputObjectV4 -> Real
  hterm :
    (GroundedC1VDSplitData.ofVariation
      variation.toVariationClassData.toVariationClassData).termMass <=
      Finset.sum
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight
  hD :
    AppendixN.classMassV4
      ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight OutputClassV4.densePack <= O_D
  hP :
    AppendixN.classMassV4
      ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight OutputClassV4.progress <= O_P
  hE :
    AppendixN.classMassV4
      ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight OutputClassV4.endpoint <= O_E
  hCNL :
    AppendixN.classMassV4
      ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight OutputClassV4.cnl <= O_CNL
  bddLowPaid :
    ShellPaidBddClassBoundData.LowPaidSplitData chernoffLeaf
      ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight O_bdd

namespace ActualRawTerminalLowPaidData

/-- Reassemble raw terminal inequalities and the L.6 split into the coupled
Bdd/L6 closed N.2/N.3 package. -/
def toBddL6Data
    {ctx : ActualFailureContext}
    {chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    {variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V}
    (data :
      ActualRawTerminalLowPaidData ctx chernoffLeaf variation
        O_D O_P O_E O_CNL O_bdd) :
    ActualClosedN2N3BddL6Data ctx chernoffLeaf
      O_D O_P O_E O_CNL O_bdd O_V where
  variation := variation
  terminalAbsorption := by
    letI : DecidableEq data.sigma := Classical.decEq data.sigma
    letI : LinearOrder data.iota := data.linIota
    exact
      classicalTableRoutedDirectFiveClassTerminalAbsorptionFromRawClosedN33LowPaid
        data.E data.row data.supp data.thr data.terminalWeight
        data.hterm data.hD data.hP data.hE data.hCNL data.bddLowPaid

end ActualRawTerminalLowPaidData

/--
Structured actual N.3.3 terminal package with all non-drop classes still backed
by their manuscript route inputs.

This keeps grouped N.3.1 terminal compression, DensePack support alignment,
Chernoff progress alignment, Return endpoint leakage, CNL Kraft alignment, and
the L.6 low/paid bounded-class split separate until projection.
-/
structure ActualStructuredTerminalLowPaidData
    (ctx : ActualFailureContext)
    (chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    {O_V : Real}
    (variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V)
    (O_D O_P O_E O_CNL O_bdd : Real) where
  sigma : Type
  iota : Type
  linIota : LinearOrder iota
  E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) linIota
  row : iota -> AppendixN.TerminalRow
  supp : iota -> Nat
  thr : iota -> Nat
  terminalWeight : OutputObjectV4 -> Real
  terminalMass :
    @TableRoutedTerminalMassCompressionInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      (GroundedC1VDSplitData.ofVariation
        variation.toVariationClassData.toVariationClassData).termMass
  densePack :
    @TableRoutedDensePackClassSupportInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : Real) O_D
  progress :
    @TableRoutedProgressClassChernoffInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : Real) O_P
  endpoint :
    @TableRoutedEndpointClassReturnInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : Real) O_E
  cnl :
    @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight ctx.shell erdos260Constants.cStar
      erdos260Constants.ξ O_CNL
  bddLowPaid :
    ShellPaidBddClassBoundData.LowPaidSplitData chernoffLeaf
      ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight O_bdd

namespace ActualStructuredTerminalLowPaidData

/-- Project the structured terminal routes to the coupled Bdd/L6 N.2/N.3
package. -/
def toBddL6Data
    {ctx : ActualFailureContext}
    {chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    {variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V}
    (data :
      ActualStructuredTerminalLowPaidData ctx chernoffLeaf variation
        O_D O_P O_E O_CNL O_bdd) :
    ActualClosedN2N3BddL6Data ctx chernoffLeaf
      O_D O_P O_E O_CNL O_bdd O_V where
  variation := variation
  terminalAbsorption := by
    letI : DecidableEq data.sigma := Classical.decEq data.sigma
    letI : LinearOrder data.iota := data.linIota
    exact
      classicalTableRoutedDirectFiveClassTerminalAbsorptionFromCompressedMassDensePackSupportProgressChernoffEndpointReturnCNLKraftClosedN33LowPaid
        data.E data.row data.supp data.thr data.terminalWeight
        data.terminalMass data.densePack data.progress data.endpoint data.cnl
        data.bddLowPaid

end ActualStructuredTerminalLowPaidData

/--
Raw L.6 bounded-class low/paid split fields with the paid part in finite-overlap
form.
-/
structure ActualFiniteOverlapLowPaidSplitFieldsData
    {cStar xi X : Real}
    (leaf : RegularShellPaidChernoff22_1AInputData cStar xi X)
    (objects : Finset OutputObjectV4)
    (terminalWeight : OutputObjectV4 -> Real)
    (O_bdd : Real) where
  wtLow : OutputObjectV4 -> Real
  wtPaid : OutputObjectV4 -> Real
  remLow : Real
  paidMass : Real
  overlap : Real
  mainPaid : Real
  remPaid : Real
  branchPaid : leaf.stoppedTree.Path -> Real
  overlap_nonneg : 0 <= overlap
  paid_le_branchPaid :
    paidMass <= ∑ b ∈ leaf.stoppedTree.paths, branchPaid b
  branchPaid_le_overlap_shellArea :
    forall b, b ∈ leaf.stoppedTree.paths ->
      branchPaid b <= overlap * (leaf.wt0 b * leaf.Ysh b)
  overlap_budget :
    overlap * (cStar * xi * X / 6) <= mainPaid + remPaid
  paid_eq :
    paidMass =
      (∑ o ∈ objects.filter (fun o => o.cls = OutputClassV4.bdd), wtPaid o)
  split :
    forall o, o ∈ objects.filter (fun o => o.cls = OutputClassV4.bdd) ->
      terminalWeight o = wtLow o + wtPaid o
  low_le :
    (∑ o ∈ objects.filter (fun o => o.cls = OutputClassV4.bdd), wtLow o) <=
      remLow
  output_budget : mainPaid + (remLow + remPaid) <= O_bdd

namespace ActualFiniteOverlapLowPaidSplitFieldsData

/-- Package raw finite-overlap L.6 fields as the existing bounded-class split
record. -/
def toFiniteOverlapLowPaidSplitData
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {objects : Finset OutputObjectV4}
    {terminalWeight : OutputObjectV4 -> Real}
    {O_bdd : Real}
    (data :
      ActualFiniteOverlapLowPaidSplitFieldsData leaf objects terminalWeight
        O_bdd) :
    ShellPaidBddClassBoundData.FiniteOverlapLowPaidSplitData leaf objects
      terminalWeight O_bdd where
  wtLow := data.wtLow
  wtPaid := data.wtPaid
  remLow := data.remLow
  embedding := {
    paidMass := data.paidMass
    overlap := data.overlap
    mainPaid := data.mainPaid
    remPaid := data.remPaid
    branchPaid := data.branchPaid
    overlap_nonneg := data.overlap_nonneg
    paid_le_branchPaid := data.paid_le_branchPaid
    branchPaid_le_overlap_shellArea := data.branchPaid_le_overlap_shellArea
    overlap_budget := data.overlap_budget }
  paid_eq := data.paid_eq
  split := data.split
  low_le := data.low_le
  output_budget := data.output_budget

end ActualFiniteOverlapLowPaidSplitFieldsData

/--
Structured actual N.3.3 terminal package with the bounded class paid part still
in the finite-overlap L.6.2 form.
-/
structure ActualStructuredTerminalFiniteOverlapLowPaidData
    (ctx : ActualFailureContext)
    (chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    {O_V : Real}
    (variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V)
    (O_D O_P O_E O_CNL O_bdd : Real) where
  sigma : Type
  iota : Type
  linIota : LinearOrder iota
  E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) linIota
  row : iota -> AppendixN.TerminalRow
  supp : iota -> Nat
  thr : iota -> Nat
  terminalWeight : OutputObjectV4 -> Real
  terminalMass :
    @TableRoutedTerminalMassCompressionInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      (GroundedC1VDSplitData.ofVariation
        variation.toVariationClassData.toVariationClassData).termMass
  densePack :
    @TableRoutedDensePackClassSupportInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : Real) O_D
  progress :
    @TableRoutedProgressClassChernoffInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : Real) O_P
  endpoint :
    @TableRoutedEndpointClassReturnInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : Real) O_E
  cnl :
    @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight ctx.shell erdos260Constants.cStar
      erdos260Constants.ξ O_CNL
  bddFiniteOverlap :
    ShellPaidBddClassBoundData.FiniteOverlapLowPaidSplitData chernoffLeaf
      ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight O_bdd

namespace ActualStructuredTerminalFiniteOverlapLowPaidData

/-- Collapse the finite-overlap L.6.2 paid route to the standard low/paid split
consumed by the existing structured terminal constructor. -/
def toStructuredTerminalLowPaidData
    {ctx : ActualFailureContext}
    {chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    {variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V}
    (data :
      ActualStructuredTerminalFiniteOverlapLowPaidData ctx chernoffLeaf
        variation O_D O_P O_E O_CNL O_bdd) :
    ActualStructuredTerminalLowPaidData ctx chernoffLeaf variation
      O_D O_P O_E O_CNL O_bdd where
  sigma := data.sigma
  iota := data.iota
  linIota := data.linIota
  E := data.E
  row := data.row
  supp := data.supp
  thr := data.thr
  terminalWeight := data.terminalWeight
  terminalMass := data.terminalMass
  densePack := data.densePack
  progress := data.progress
  endpoint := data.endpoint
  cnl := data.cnl
  bddLowPaid := data.bddFiniteOverlap.toLowPaidSplitData

end ActualStructuredTerminalFiniteOverlapLowPaidData

/--
Structured actual N.3.3 terminal package with the bounded class L.6 low/paid
and finite-overlap embedding fully exposed as fields.
-/
structure ActualStructuredTerminalFiniteOverlapFieldsLowPaidData
    (ctx : ActualFailureContext)
    (chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    {O_V : Real}
    (variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V)
    (O_D O_P O_E O_CNL O_bdd : Real) where
  sigma : Type
  iota : Type
  linIota : LinearOrder iota
  E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) linIota
  row : iota -> AppendixN.TerminalRow
  supp : iota -> Nat
  thr : iota -> Nat
  terminalWeight : OutputObjectV4 -> Real
  terminalMass :
    @TableRoutedTerminalMassCompressionInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      (GroundedC1VDSplitData.ofVariation
        variation.toVariationClassData.toVariationClassData).termMass
  densePack :
    @TableRoutedDensePackClassSupportInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : Real) O_D
  progress :
    @TableRoutedProgressClassChernoffInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : Real) O_P
  endpoint :
    @TableRoutedEndpointClassReturnInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : Real) O_E
  cnl :
    @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight ctx.shell erdos260Constants.cStar
      erdos260Constants.ξ O_CNL
  bddFiniteOverlapFields :
    ActualFiniteOverlapLowPaidSplitFieldsData chernoffLeaf
      ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight O_bdd

namespace ActualStructuredTerminalFiniteOverlapFieldsLowPaidData

/-- Package the fully exposed L.6 fields as the finite-overlap terminal route. -/
def toFiniteOverlapLowPaidData
    {ctx : ActualFailureContext}
    {chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    {variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V}
    (data :
      ActualStructuredTerminalFiniteOverlapFieldsLowPaidData ctx chernoffLeaf
        variation O_D O_P O_E O_CNL O_bdd) :
    ActualStructuredTerminalFiniteOverlapLowPaidData ctx chernoffLeaf variation
      O_D O_P O_E O_CNL O_bdd where
  sigma := data.sigma
  iota := data.iota
  linIota := data.linIota
  E := data.E
  row := data.row
  supp := data.supp
  thr := data.thr
  terminalWeight := data.terminalWeight
  terminalMass := data.terminalMass
  densePack := data.densePack
  progress := data.progress
  endpoint := data.endpoint
  cnl := data.cnl
  bddFiniteOverlap :=
    data.bddFiniteOverlapFields.toFiniteOverlapLowPaidSplitData

end ActualStructuredTerminalFiniteOverlapFieldsLowPaidData

/--
Structured actual N.3.3 terminal package with the terminal-mass N.3.1
compression fields exposed directly.
-/
structure ActualStructuredTerminalMassFieldsFiniteOverlapFieldsLowPaidData
    (ctx : ActualFailureContext)
    (chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    {O_V : Real}
    (variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V)
    (O_D O_P O_E O_CNL O_bdd : Real) where
  sigma : Type
  iota : Type
  linIota : LinearOrder iota
  E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) linIota
  row : iota -> AppendixN.TerminalRow
  supp : iota -> Nat
  thr : iota -> Nat
  terminalWeight : OutputObjectV4 -> Real
  terminalCharge : OutputObjectV4 -> Real
  hterm_raw :
    (GroundedC1VDSplitData.ofVariation
      variation.toVariationClassData.toVariationClassData).termMass <=
      Finset.sum
        ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalCharge
  hcompression :
    forall O,
      O ∈
        ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega })) ->
      terminalCharge O <= terminalWeight O
  densePack :
    @TableRoutedDensePackClassSupportInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : Real) O_D
  progress :
    @TableRoutedProgressClassChernoffInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : Real) O_P
  endpoint :
    @TableRoutedEndpointClassReturnInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : Real) O_E
  cnl :
    @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight ctx.shell erdos260Constants.cStar
      erdos260Constants.ξ O_CNL
  bddFiniteOverlapFields :
    ActualFiniteOverlapLowPaidSplitFieldsData chernoffLeaf
      ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight O_bdd

namespace ActualStructuredTerminalMassFieldsFiniteOverlapFieldsLowPaidData

/-- Package raw terminal-mass compression fields as the terminal-field surface. -/
def toTerminalFieldsData
    {ctx : ActualFailureContext}
    {chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    {variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V}
    (data :
      ActualStructuredTerminalMassFieldsFiniteOverlapFieldsLowPaidData ctx
        chernoffLeaf variation O_D O_P O_E O_CNL O_bdd) :
    ActualStructuredTerminalFiniteOverlapFieldsLowPaidData ctx chernoffLeaf
      variation O_D O_P O_E O_CNL O_bdd where
  sigma := data.sigma
  iota := data.iota
  linIota := data.linIota
  E := data.E
  row := data.row
  supp := data.supp
  thr := data.thr
  terminalWeight := data.terminalWeight
  terminalMass :=
    @TableRoutedTerminalMassCompressionInputData.mk data.sigma data.iota
      (Classical.decEq data.sigma) data.linIota data.E data.row data.supp
      data.thr data.terminalWeight
      (GroundedC1VDSplitData.ofVariation
        variation.toVariationClassData.toVariationClassData).termMass
      data.terminalCharge data.hterm_raw data.hcompression
  densePack := data.densePack
  progress := data.progress
  endpoint := data.endpoint
  cnl := data.cnl
  bddFiniteOverlapFields := data.bddFiniteOverlapFields

end ActualStructuredTerminalMassFieldsFiniteOverlapFieldsLowPaidData

/--
Structured actual N.3.3 terminal package with both terminal-mass compression
and DensePack class-support fields exposed directly.
-/
structure ActualStructuredTerminalMassDenseFieldsFiniteOverlapFieldsLowPaidData
    (ctx : ActualFailureContext)
    (chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    {O_V : Real}
    (variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V)
    (O_D O_P O_E O_CNL O_bdd : Real) where
  sigma : Type
  iota : Type
  linIota : LinearOrder iota
  E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) linIota
  row : iota -> AppendixN.TerminalRow
  supp : iota -> Nat
  thr : iota -> Nat
  terminalWeight : OutputObjectV4 -> Real
  terminalCharge : OutputObjectV4 -> Real
  hterm_raw :
    (GroundedC1VDSplitData.ofVariation
      variation.toVariationClassData.toVariationClassData).termMass <=
      Finset.sum
        ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalCharge
  hcompression :
    forall O,
      O ∈
        ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega })) ->
      terminalCharge O <= terminalWeight O
  densePhase :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real)
  densePointOf : OutputObjectV4 -> Nat
  dense_hpoint_mem :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
        densePointOf O ∈ densePhase.densePack.densePackPoints
  dense_hinj :
    forall O1,
      O1 ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
      forall O2,
        O2 ∈
            ((@AppendixN.EventFibre.atoms sigma iota
              (Classical.decEq sigma) linIota E).image
              (fun omega =>
                { cls := (row omega).outputClass
                  supportId := supp omega
                  thresholdLayer := thr omega })).filter
              (fun O => O.cls = OutputClassV4.densePack) ->
          densePointOf O1 = densePointOf O2 -> O1 = O2
  dense_hweight_le_one :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
        terminalWeight O <= 1
  dense_hbudget_le_output : termDensePack densePhase <= O_D
  progress :
    @TableRoutedProgressClassChernoffInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : Real) O_P
  endpoint :
    @TableRoutedEndpointClassReturnInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : Real) O_E
  cnl :
    @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight ctx.shell erdos260Constants.cStar
      erdos260Constants.ξ O_CNL
  bddFiniteOverlapFields :
    ActualFiniteOverlapLowPaidSplitFieldsData chernoffLeaf
      ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight O_bdd

namespace ActualStructuredTerminalMassDenseFieldsFiniteOverlapFieldsLowPaidData

/-- Package raw terminal-mass and DensePack fields as the mass-field surface. -/
def toMassFieldsData
    {ctx : ActualFailureContext}
    {chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    {variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V}
    (data :
      ActualStructuredTerminalMassDenseFieldsFiniteOverlapFieldsLowPaidData ctx
        chernoffLeaf variation O_D O_P O_E O_CNL O_bdd) :
    ActualStructuredTerminalMassFieldsFiniteOverlapFieldsLowPaidData ctx
      chernoffLeaf variation O_D O_P O_E O_CNL O_bdd where
  sigma := data.sigma
  iota := data.iota
  linIota := data.linIota
  E := data.E
  row := data.row
  supp := data.supp
  thr := data.thr
  terminalWeight := data.terminalWeight
  terminalCharge := data.terminalCharge
  hterm_raw := data.hterm_raw
  hcompression := data.hcompression
  densePack :=
    @TableRoutedDensePackClassSupportInputData.mk data.sigma data.iota
      (Classical.decEq data.sigma) data.linIota data.E data.row data.supp
      data.thr data.terminalWeight erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real) O_D data.densePhase
      data.densePointOf data.dense_hpoint_mem data.dense_hinj
      data.dense_hweight_le_one data.dense_hbudget_le_output
  progress := data.progress
  endpoint := data.endpoint
  cnl := data.cnl
  bddFiniteOverlapFields := data.bddFiniteOverlapFields

end ActualStructuredTerminalMassDenseFieldsFiniteOverlapFieldsLowPaidData

/--
Structured actual N.3.3 terminal package with terminal-mass, DensePack, and
progress-class Chernoff fields exposed directly.
-/
structure ActualStructuredTerminalMassDenseProgressFieldsFiniteOverlapFieldsLowPaidData
    (ctx : ActualFailureContext)
    (chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    {O_V : Real}
    (variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V)
    (O_D O_P O_E O_CNL O_bdd : Real) where
  sigma : Type
  iota : Type
  linIota : LinearOrder iota
  E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) linIota
  row : iota -> AppendixN.TerminalRow
  supp : iota -> Nat
  thr : iota -> Nat
  terminalWeight : OutputObjectV4 -> Real
  terminalCharge : OutputObjectV4 -> Real
  hterm_raw :
    (GroundedC1VDSplitData.ofVariation
      variation.toVariationClassData.toVariationClassData).termMass <=
      Finset.sum
        ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalCharge
  hcompression :
    forall O,
      O ∈
        ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega })) ->
      terminalCharge O <= terminalWeight O
  densePhase :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real)
  densePointOf : OutputObjectV4 -> Nat
  dense_hpoint_mem :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
        densePointOf O ∈ densePhase.densePack.densePackPoints
  dense_hinj :
    forall O1,
      O1 ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
      forall O2,
        O2 ∈
            ((@AppendixN.EventFibre.atoms sigma iota
              (Classical.decEq sigma) linIota E).image
              (fun omega =>
                { cls := (row omega).outputClass
                  supportId := supp omega
                  thresholdLayer := thr omega })).filter
              (fun O => O.cls = OutputClassV4.densePack) ->
          densePointOf O1 = densePointOf O2 -> O1 = O2
  dense_hweight_le_one :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
        terminalWeight O <= 1
  dense_hbudget_le_output : termDensePack densePhase <= O_D
  progressPhase :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real)
  progressPathDecEq : DecidableEq progressPhase.chernoff.α
  progressPathOf : OutputObjectV4 -> progressPhase.chernoff.α
  progress_hpath_mem :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
        progressPathOf O ∈
          highCostSet progressPhase.chernoff.paths progressPhase.chernoff.cost
            progressPhase.chernoff.Y
  progress_hinj :
    forall O1,
      O1 ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
      forall O2,
        O2 ∈
            ((@AppendixN.EventFibre.atoms sigma iota
              (Classical.decEq sigma) linIota E).image
              (fun omega =>
                { cls := (row omega).outputClass
                  supportId := supp omega
                  thresholdLayer := thr omega })).filter
              (fun O => O.cls = OutputClassV4.progress) ->
          progressPathOf O1 = progressPathOf O2 -> O1 = O2
  progress_hweight_le_path :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
        terminalWeight O <= progressPhase.chernoff.weight (progressPathOf O)
  progress_hbudget_le_output : termChernoff progressPhase <= O_P
  endpoint :
    @TableRoutedEndpointClassReturnInputData sigma iota
      (Classical.decEq sigma) linIota E row supp thr terminalWeight
      erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : Real) O_E
  cnl :
    @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight ctx.shell erdos260Constants.cStar
      erdos260Constants.ξ O_CNL
  bddFiniteOverlapFields :
    ActualFiniteOverlapLowPaidSplitFieldsData chernoffLeaf
      ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight O_bdd

namespace ActualStructuredTerminalMassDenseProgressFieldsFiniteOverlapFieldsLowPaidData

/-- Package raw progress fields as the mass-and-DensePack terminal surface. -/
def toMassDenseFieldsData
    {ctx : ActualFailureContext}
    {chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    {variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V}
    (data :
      ActualStructuredTerminalMassDenseProgressFieldsFiniteOverlapFieldsLowPaidData
        ctx chernoffLeaf variation O_D O_P O_E O_CNL O_bdd) :
    ActualStructuredTerminalMassDenseFieldsFiniteOverlapFieldsLowPaidData ctx
      chernoffLeaf variation O_D O_P O_E O_CNL O_bdd where
  sigma := data.sigma
  iota := data.iota
  linIota := data.linIota
  E := data.E
  row := data.row
  supp := data.supp
  thr := data.thr
  terminalWeight := data.terminalWeight
  terminalCharge := data.terminalCharge
  hterm_raw := data.hterm_raw
  hcompression := data.hcompression
  densePhase := data.densePhase
  densePointOf := data.densePointOf
  dense_hpoint_mem := data.dense_hpoint_mem
  dense_hinj := data.dense_hinj
  dense_hweight_le_one := data.dense_hweight_le_one
  dense_hbudget_le_output := data.dense_hbudget_le_output
  progress :=
    @TableRoutedProgressClassChernoffInputData.mk data.sigma data.iota
      (Classical.decEq data.sigma) data.linIota data.E data.row data.supp
      data.thr data.terminalWeight erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real) O_P data.progressPhase
      data.progressPathDecEq data.progressPathOf data.progress_hpath_mem
      data.progress_hinj data.progress_hweight_le_path
      data.progress_hbudget_le_output
  endpoint := data.endpoint
  cnl := data.cnl
  bddFiniteOverlapFields := data.bddFiniteOverlapFields

end ActualStructuredTerminalMassDenseProgressFieldsFiniteOverlapFieldsLowPaidData

/--
Structured actual N.3.3 terminal package with terminal-mass, DensePack,
progress, and endpoint-return fields exposed directly.
-/
structure ActualStructuredTerminalMassDenseProgressEndpointFieldsFiniteOverlapFieldsLowPaidData
    (ctx : ActualFailureContext)
    (chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    {O_V : Real}
    (variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V)
    (O_D O_P O_E O_CNL O_bdd : Real) where
  sigma : Type
  iota : Type
  linIota : LinearOrder iota
  E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) linIota
  row : iota -> AppendixN.TerminalRow
  supp : iota -> Nat
  thr : iota -> Nat
  terminalWeight : OutputObjectV4 -> Real
  terminalCharge : OutputObjectV4 -> Real
  hterm_raw :
    (GroundedC1VDSplitData.ofVariation
      variation.toVariationClassData.toVariationClassData).termMass <=
      Finset.sum
        ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalCharge
  hcompression :
    forall O,
      O ∈
        ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega })) ->
      terminalCharge O <= terminalWeight O
  densePhase :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real)
  densePointOf : OutputObjectV4 -> Nat
  dense_hpoint_mem :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
        densePointOf O ∈ densePhase.densePack.densePackPoints
  dense_hinj :
    forall O1,
      O1 ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
      forall O2,
        O2 ∈
            ((@AppendixN.EventFibre.atoms sigma iota
              (Classical.decEq sigma) linIota E).image
              (fun omega =>
                { cls := (row omega).outputClass
                  supportId := supp omega
                  thresholdLayer := thr omega })).filter
              (fun O => O.cls = OutputClassV4.densePack) ->
          densePointOf O1 = densePointOf O2 -> O1 = O2
  dense_hweight_le_one :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
        terminalWeight O <= 1
  dense_hbudget_le_output : termDensePack densePhase <= O_D
  progressPhase :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real)
  progressPathDecEq : DecidableEq progressPhase.chernoff.α
  progressPathOf : OutputObjectV4 -> progressPhase.chernoff.α
  progress_hpath_mem :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
        progressPathOf O ∈
          highCostSet progressPhase.chernoff.paths progressPhase.chernoff.cost
            progressPhase.chernoff.Y
  progress_hinj :
    forall O1,
      O1 ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
      forall O2,
        O2 ∈
            ((@AppendixN.EventFibre.atoms sigma iota
              (Classical.decEq sigma) linIota E).image
              (fun omega =>
                { cls := (row omega).outputClass
                  supportId := supp omega
                  thresholdLayer := thr omega })).filter
              (fun O => O.cls = OutputClassV4.progress) ->
          progressPathOf O1 = progressPathOf O2 -> O1 = O2
  progress_hweight_le_path :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
        terminalWeight O <= progressPhase.chernoff.weight (progressPathOf O)
  progress_hbudget_le_output : termChernoff progressPhase <= O_P
  endpointPhase :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real)
  endpoint_hclass_le_olc :
    AppendixN.classMassV4
      ((@AppendixN.EventFibre.atoms sigma iota
        (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight
      OutputClassV4.endpoint <= endpointPhase.returnPkg.olc
  endpoint_hOrdinaryShort_nonneg : 0 <= endpointPhase.returnPkg.ordinaryShort
  endpoint_hSemiperiodic_nonneg : 0 <= endpointPhase.returnPkg.semiperiodic
  endpoint_hNonlocalLong_nonneg : 0 <= endpointPhase.returnPkg.nonlocalLong
  endpoint_hbudget_le_output : termReturn endpointPhase <= O_E
  cnl :
    @TableRoutedCNLClassKraftInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight ctx.shell erdos260Constants.cStar
      erdos260Constants.ξ O_CNL
  bddFiniteOverlapFields :
    ActualFiniteOverlapLowPaidSplitFieldsData chernoffLeaf
      ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight O_bdd

namespace ActualStructuredTerminalMassDenseProgressEndpointFieldsFiniteOverlapFieldsLowPaidData

/-- Package raw endpoint fields as the mass/DensePack/progress terminal surface. -/
def toMassDenseProgressFieldsData
    {ctx : ActualFailureContext}
    {chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    {variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V}
    (data :
      ActualStructuredTerminalMassDenseProgressEndpointFieldsFiniteOverlapFieldsLowPaidData
        ctx chernoffLeaf variation O_D O_P O_E O_CNL O_bdd) :
    ActualStructuredTerminalMassDenseProgressFieldsFiniteOverlapFieldsLowPaidData
      ctx chernoffLeaf variation O_D O_P O_E O_CNL O_bdd where
  sigma := data.sigma
  iota := data.iota
  linIota := data.linIota
  E := data.E
  row := data.row
  supp := data.supp
  thr := data.thr
  terminalWeight := data.terminalWeight
  terminalCharge := data.terminalCharge
  hterm_raw := data.hterm_raw
  hcompression := data.hcompression
  densePhase := data.densePhase
  densePointOf := data.densePointOf
  dense_hpoint_mem := data.dense_hpoint_mem
  dense_hinj := data.dense_hinj
  dense_hweight_le_one := data.dense_hweight_le_one
  dense_hbudget_le_output := data.dense_hbudget_le_output
  progressPhase := data.progressPhase
  progressPathDecEq := data.progressPathDecEq
  progressPathOf := data.progressPathOf
  progress_hpath_mem := data.progress_hpath_mem
  progress_hinj := data.progress_hinj
  progress_hweight_le_path := data.progress_hweight_le_path
  progress_hbudget_le_output := data.progress_hbudget_le_output
  endpoint :=
    @TableRoutedEndpointClassReturnInputData.mk data.sigma data.iota
      (Classical.decEq data.sigma) data.linIota data.E data.row data.supp
      data.thr data.terminalWeight erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real) O_E data.endpointPhase
      data.endpoint_hclass_le_olc data.endpoint_hOrdinaryShort_nonneg
      data.endpoint_hSemiperiodic_nonneg data.endpoint_hNonlocalLong_nonneg
      data.endpoint_hbudget_le_output
  cnl := data.cnl
  bddFiniteOverlapFields := data.bddFiniteOverlapFields

end ActualStructuredTerminalMassDenseProgressEndpointFieldsFiniteOverlapFieldsLowPaidData

/--
Structured actual N.3.3 terminal package with all table-routed class-provider
fields exposed directly.
-/
structure ActualStructuredTerminalAllClassFieldsFiniteOverlapFieldsLowPaidData
    (ctx : ActualFailureContext)
    (chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    {O_V : Real}
    (variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V)
    (O_D O_P O_E O_CNL O_bdd : Real) where
  sigma : Type
  iota : Type
  linIota : LinearOrder iota
  E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) linIota
  row : iota -> AppendixN.TerminalRow
  supp : iota -> Nat
  thr : iota -> Nat
  terminalWeight : OutputObjectV4 -> Real
  terminalCharge : OutputObjectV4 -> Real
  hterm_raw :
    (GroundedC1VDSplitData.ofVariation
      variation.toVariationClassData.toVariationClassData).termMass <=
      Finset.sum
        ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalCharge
  hcompression :
    forall O,
      O ∈
        ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega })) ->
      terminalCharge O <= terminalWeight O
  densePhase :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real)
  densePointOf : OutputObjectV4 -> Nat
  dense_hpoint_mem :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
        densePointOf O ∈ densePhase.densePack.densePackPoints
  dense_hinj :
    forall O1,
      O1 ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
      forall O2,
        O2 ∈
            ((@AppendixN.EventFibre.atoms sigma iota
              (Classical.decEq sigma) linIota E).image
              (fun omega =>
                { cls := (row omega).outputClass
                  supportId := supp omega
                  thresholdLayer := thr omega })).filter
              (fun O => O.cls = OutputClassV4.densePack) ->
          densePointOf O1 = densePointOf O2 -> O1 = O2
  dense_hweight_le_one :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
        terminalWeight O <= 1
  dense_hbudget_le_output : termDensePack densePhase <= O_D
  progressPhase :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real)
  progressPathDecEq : DecidableEq progressPhase.chernoff.α
  progressPathOf : OutputObjectV4 -> progressPhase.chernoff.α
  progress_hpath_mem :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
        progressPathOf O ∈
          highCostSet progressPhase.chernoff.paths progressPhase.chernoff.cost
            progressPhase.chernoff.Y
  progress_hinj :
    forall O1,
      O1 ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
      forall O2,
        O2 ∈
            ((@AppendixN.EventFibre.atoms sigma iota
              (Classical.decEq sigma) linIota E).image
              (fun omega =>
                { cls := (row omega).outputClass
                  supportId := supp omega
                  thresholdLayer := thr omega })).filter
              (fun O => O.cls = OutputClassV4.progress) ->
          progressPathOf O1 = progressPathOf O2 -> O1 = O2
  progress_hweight_le_path :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
        terminalWeight O <= progressPhase.chernoff.weight (progressPathOf O)
  progress_hbudget_le_output : termChernoff progressPhase <= O_P
  endpointPhase :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real)
  endpoint_hclass_le_olc :
    AppendixN.classMassV4
      ((@AppendixN.EventFibre.atoms sigma iota
        (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight
      OutputClassV4.endpoint <= endpointPhase.returnPkg.olc
  endpoint_hOrdinaryShort_nonneg : 0 <= endpointPhase.returnPkg.ordinaryShort
  endpoint_hSemiperiodic_nonneg : 0 <= endpointPhase.returnPkg.semiperiodic
  endpoint_hNonlocalLong_nonneg : 0 <= endpointPhase.returnPkg.nonlocalLong
  endpoint_hbudget_le_output : termReturn endpointPhase <= O_E
  cnlLeaf :
    CNLStandardWeightedKraftShellInputData ctx.shell erdos260Constants.cStar
      erdos260Constants.ξ
  cnlCleanTerm : Real
  cnl_hclass_le_clean :
    AppendixN.classMassV4
      ((@AppendixN.EventFibre.atoms sigma iota
        (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight
      OutputClassV4.cnl <= cnlCleanTerm
  cnl_hclean_bound :
    0 <= cnlCleanTerm /\
      cnlCleanTerm <=
        erdos260Constants.cStar * erdos260Constants.ξ *
          (ctx.shell.X : Real) / 6
  cnl_hbudget_le_output :
    erdos260Constants.cStar * erdos260Constants.ξ *
      (ctx.shell.X : Real) / 6 <= O_CNL
  bddFiniteOverlapFields :
    ActualFiniteOverlapLowPaidSplitFieldsData chernoffLeaf
      ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight O_bdd

namespace ActualStructuredTerminalAllClassFieldsFiniteOverlapFieldsLowPaidData

/-- Package raw CNL fields as the endpoint-field terminal surface. -/
def toMassDenseProgressEndpointFieldsData
    {ctx : ActualFailureContext}
    {chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    {variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V}
    (data :
      ActualStructuredTerminalAllClassFieldsFiniteOverlapFieldsLowPaidData
        ctx chernoffLeaf variation O_D O_P O_E O_CNL O_bdd) :
    ActualStructuredTerminalMassDenseProgressEndpointFieldsFiniteOverlapFieldsLowPaidData
      ctx chernoffLeaf variation O_D O_P O_E O_CNL O_bdd where
  sigma := data.sigma
  iota := data.iota
  linIota := data.linIota
  E := data.E
  row := data.row
  supp := data.supp
  thr := data.thr
  terminalWeight := data.terminalWeight
  terminalCharge := data.terminalCharge
  hterm_raw := data.hterm_raw
  hcompression := data.hcompression
  densePhase := data.densePhase
  densePointOf := data.densePointOf
  dense_hpoint_mem := data.dense_hpoint_mem
  dense_hinj := data.dense_hinj
  dense_hweight_le_one := data.dense_hweight_le_one
  dense_hbudget_le_output := data.dense_hbudget_le_output
  progressPhase := data.progressPhase
  progressPathDecEq := data.progressPathDecEq
  progressPathOf := data.progressPathOf
  progress_hpath_mem := data.progress_hpath_mem
  progress_hinj := data.progress_hinj
  progress_hweight_le_path := data.progress_hweight_le_path
  progress_hbudget_le_output := data.progress_hbudget_le_output
  endpointPhase := data.endpointPhase
  endpoint_hclass_le_olc := data.endpoint_hclass_le_olc
  endpoint_hOrdinaryShort_nonneg := data.endpoint_hOrdinaryShort_nonneg
  endpoint_hSemiperiodic_nonneg := data.endpoint_hSemiperiodic_nonneg
  endpoint_hNonlocalLong_nonneg := data.endpoint_hNonlocalLong_nonneg
  endpoint_hbudget_le_output := data.endpoint_hbudget_le_output
  cnl :=
    @TableRoutedCNLClassKraftInputData.mk data.sigma data.iota
      (Classical.decEq data.sigma) data.linIota data.E data.row data.supp
      data.thr data.terminalWeight ctx.shell erdos260Constants.cStar
      erdos260Constants.ξ O_CNL data.cnlLeaf data.cnlCleanTerm
      data.cnl_hclass_le_clean data.cnl_hclean_bound
      data.cnl_hbudget_le_output
  bddFiniteOverlapFields := data.bddFiniteOverlapFields

end ActualStructuredTerminalAllClassFieldsFiniteOverlapFieldsLowPaidData

/--
Structured actual N.3.3 terminal package with all table-routed class-provider
fields and the L.6 bounded-class finite-overlap fields exposed directly.
-/
structure ActualStructuredTerminalAllFieldsLowPaidData
    (ctx : ActualFailureContext)
    (chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    {O_V : Real}
    (variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V)
    (O_D O_P O_E O_CNL O_bdd : Real) where
  sigma : Type
  iota : Type
  linIota : LinearOrder iota
  E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) linIota
  row : iota -> AppendixN.TerminalRow
  supp : iota -> Nat
  thr : iota -> Nat
  terminalWeight : OutputObjectV4 -> Real
  terminalCharge : OutputObjectV4 -> Real
  hterm_raw :
    (GroundedC1VDSplitData.ofVariation
      variation.toVariationClassData.toVariationClassData).termMass <=
      Finset.sum
        ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalCharge
  hcompression :
    forall O,
      O ∈
        ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega })) ->
      terminalCharge O <= terminalWeight O
  densePhase :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real)
  densePointOf : OutputObjectV4 -> Nat
  dense_hpoint_mem :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
        densePointOf O ∈ densePhase.densePack.densePackPoints
  dense_hinj :
    forall O1,
      O1 ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
      forall O2,
        O2 ∈
            ((@AppendixN.EventFibre.atoms sigma iota
              (Classical.decEq sigma) linIota E).image
              (fun omega =>
                { cls := (row omega).outputClass
                  supportId := supp omega
                  thresholdLayer := thr omega })).filter
              (fun O => O.cls = OutputClassV4.densePack) ->
          densePointOf O1 = densePointOf O2 -> O1 = O2
  dense_hweight_le_one :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
        terminalWeight O <= 1
  dense_hbudget_le_output : termDensePack densePhase <= O_D
  progressPhase :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real)
  progressPathDecEq : DecidableEq progressPhase.chernoff.α
  progressPathOf : OutputObjectV4 -> progressPhase.chernoff.α
  progress_hpath_mem :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
        progressPathOf O ∈
          highCostSet progressPhase.chernoff.paths progressPhase.chernoff.cost
            progressPhase.chernoff.Y
  progress_hinj :
    forall O1,
      O1 ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
      forall O2,
        O2 ∈
            ((@AppendixN.EventFibre.atoms sigma iota
              (Classical.decEq sigma) linIota E).image
              (fun omega =>
                { cls := (row omega).outputClass
                  supportId := supp omega
                  thresholdLayer := thr omega })).filter
              (fun O => O.cls = OutputClassV4.progress) ->
          progressPathOf O1 = progressPathOf O2 -> O1 = O2
  progress_hweight_le_path :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
        terminalWeight O <= progressPhase.chernoff.weight (progressPathOf O)
  progress_hbudget_le_output : termChernoff progressPhase <= O_P
  endpointPhase :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real)
  endpoint_hclass_le_olc :
    AppendixN.classMassV4
      ((@AppendixN.EventFibre.atoms sigma iota
        (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight
      OutputClassV4.endpoint <= endpointPhase.returnPkg.olc
  endpoint_hOrdinaryShort_nonneg : 0 <= endpointPhase.returnPkg.ordinaryShort
  endpoint_hSemiperiodic_nonneg : 0 <= endpointPhase.returnPkg.semiperiodic
  endpoint_hNonlocalLong_nonneg : 0 <= endpointPhase.returnPkg.nonlocalLong
  endpoint_hbudget_le_output : termReturn endpointPhase <= O_E
  cnlLeaf :
    CNLStandardWeightedKraftShellInputData ctx.shell erdos260Constants.cStar
      erdos260Constants.ξ
  cnlCleanTerm : Real
  cnl_hclass_le_clean :
    AppendixN.classMassV4
      ((@AppendixN.EventFibre.atoms sigma iota
        (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight
      OutputClassV4.cnl <= cnlCleanTerm
  cnl_hclean_bound :
    0 <= cnlCleanTerm /\
      cnlCleanTerm <=
        erdos260Constants.cStar * erdos260Constants.ξ *
          (ctx.shell.X : Real) / 6
  cnl_hbudget_le_output :
    erdos260Constants.cStar * erdos260Constants.ξ *
      (ctx.shell.X : Real) / 6 <= O_CNL
  bddWtLow : OutputObjectV4 -> Real
  bddWtPaid : OutputObjectV4 -> Real
  bddRemLow : Real
  bddPaidMass : Real
  bddOverlap : Real
  bddMainPaid : Real
  bddRemPaid : Real
  bddBranchPaid : chernoffLeaf.stoppedTree.Path -> Real
  bdd_overlap_nonneg : 0 <= bddOverlap
  bdd_paid_le_branchPaid :
    bddPaidMass <=
      ∑ b ∈ chernoffLeaf.stoppedTree.paths, bddBranchPaid b
  bdd_branchPaid_le_overlap_shellArea :
    forall b, b ∈ chernoffLeaf.stoppedTree.paths ->
      bddBranchPaid b <= bddOverlap * (chernoffLeaf.wt0 b * chernoffLeaf.Ysh b)
  bdd_overlap_budget :
    bddOverlap *
        (erdos260Constants.cStar * erdos260Constants.ξ *
          (ctx.shell.X : Real) / 6) <=
      bddMainPaid + bddRemPaid
  bdd_paid_eq :
    bddPaidMass =
      (∑ o ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun o => o.cls = OutputClassV4.bdd),
        bddWtPaid o)
  bdd_split :
    forall o,
      o ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun o => o.cls = OutputClassV4.bdd) ->
        terminalWeight o = bddWtLow o + bddWtPaid o
  bdd_low_le :
    (∑ o ∈
        ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega })).filter
          (fun o => o.cls = OutputClassV4.bdd),
      bddWtLow o) <= bddRemLow
  bdd_output_budget : bddMainPaid + (bddRemLow + bddRemPaid) <= O_bdd

namespace ActualStructuredTerminalAllFieldsLowPaidData

/-- Package the directly exposed L.6 bounded-class fields as the all-class
finite-overlap terminal surface. -/
def toAllClassFieldsFiniteOverlapData
    {ctx : ActualFailureContext}
    {chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    {variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V}
    (data :
      ActualStructuredTerminalAllFieldsLowPaidData ctx chernoffLeaf variation
        O_D O_P O_E O_CNL O_bdd) :
    ActualStructuredTerminalAllClassFieldsFiniteOverlapFieldsLowPaidData ctx
      chernoffLeaf variation O_D O_P O_E O_CNL O_bdd where
  sigma := data.sigma
  iota := data.iota
  linIota := data.linIota
  E := data.E
  row := data.row
  supp := data.supp
  thr := data.thr
  terminalWeight := data.terminalWeight
  terminalCharge := data.terminalCharge
  hterm_raw := data.hterm_raw
  hcompression := data.hcompression
  densePhase := data.densePhase
  densePointOf := data.densePointOf
  dense_hpoint_mem := data.dense_hpoint_mem
  dense_hinj := data.dense_hinj
  dense_hweight_le_one := data.dense_hweight_le_one
  dense_hbudget_le_output := data.dense_hbudget_le_output
  progressPhase := data.progressPhase
  progressPathDecEq := data.progressPathDecEq
  progressPathOf := data.progressPathOf
  progress_hpath_mem := data.progress_hpath_mem
  progress_hinj := data.progress_hinj
  progress_hweight_le_path := data.progress_hweight_le_path
  progress_hbudget_le_output := data.progress_hbudget_le_output
  endpointPhase := data.endpointPhase
  endpoint_hclass_le_olc := data.endpoint_hclass_le_olc
  endpoint_hOrdinaryShort_nonneg := data.endpoint_hOrdinaryShort_nonneg
  endpoint_hSemiperiodic_nonneg := data.endpoint_hSemiperiodic_nonneg
  endpoint_hNonlocalLong_nonneg := data.endpoint_hNonlocalLong_nonneg
  endpoint_hbudget_le_output := data.endpoint_hbudget_le_output
  cnlLeaf := data.cnlLeaf
  cnlCleanTerm := data.cnlCleanTerm
  cnl_hclass_le_clean := data.cnl_hclass_le_clean
  cnl_hclean_bound := data.cnl_hclean_bound
  cnl_hbudget_le_output := data.cnl_hbudget_le_output
  bddFiniteOverlapFields := {
    wtLow := data.bddWtLow
    wtPaid := data.bddWtPaid
    remLow := data.bddRemLow
    paidMass := data.bddPaidMass
    overlap := data.bddOverlap
    mainPaid := data.bddMainPaid
    remPaid := data.bddRemPaid
    branchPaid := data.bddBranchPaid
    overlap_nonneg := data.bdd_overlap_nonneg
    paid_le_branchPaid := data.bdd_paid_le_branchPaid
    branchPaid_le_overlap_shellArea :=
      data.bdd_branchPaid_le_overlap_shellArea
    overlap_budget := data.bdd_overlap_budget
    paid_eq := data.bdd_paid_eq
    split := data.bdd_split
    low_le := data.bdd_low_le
    output_budget := data.bdd_output_budget }

end ActualStructuredTerminalAllFieldsLowPaidData

/--
Structured actual N.3.3 terminal package whose DensePack, progress, and
endpoint routes are pinned to the same closure phase.

The terminal CNL Kraft leaf is supplied by the global CNL provider in the
projection below, so this local terminal surface no longer carries an
independent CNL leaf witness.
-/
structure ActualStructuredTerminalPinnedPhaseAllFieldsLowPaidData
    (ctx : ActualFailureContext)
    (chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    (phase :
      ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : Real))
    {O_V : Real}
    (variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V)
    (O_D O_P O_E O_CNL O_bdd : Real) where
  sigma : Type
  iota : Type
  linIota : LinearOrder iota
  E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) linIota
  row : iota -> AppendixN.TerminalRow
  supp : iota -> Nat
  thr : iota -> Nat
  terminalWeight : OutputObjectV4 -> Real
  terminalCharge : OutputObjectV4 -> Real
  hterm_raw :
    (GroundedC1VDSplitData.ofVariation
      variation.toVariationClassData.toVariationClassData).termMass <=
      Finset.sum
        ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalCharge
  hcompression :
    forall O,
      O ∈
        ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega })) ->
      terminalCharge O <= terminalWeight O
  densePointOf : OutputObjectV4 -> Nat
  dense_hpoint_mem :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
        densePointOf O ∈ phase.densePack.densePackPoints
  dense_hinj :
    forall O1,
      O1 ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
      forall O2,
        O2 ∈
            ((@AppendixN.EventFibre.atoms sigma iota
              (Classical.decEq sigma) linIota E).image
              (fun omega =>
                { cls := (row omega).outputClass
                  supportId := supp omega
                  thresholdLayer := thr omega })).filter
              (fun O => O.cls = OutputClassV4.densePack) ->
          densePointOf O1 = densePointOf O2 -> O1 = O2
  dense_hweight_le_one :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
        terminalWeight O <= 1
  dense_hbudget_le_output : termDensePack phase <= O_D
  progressPathDecEq : DecidableEq phase.chernoff.α
  progressPathOf : OutputObjectV4 -> phase.chernoff.α
  progress_hpath_mem :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
        progressPathOf O ∈
          highCostSet phase.chernoff.paths phase.chernoff.cost
            phase.chernoff.Y
  progress_hinj :
    forall O1,
      O1 ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
      forall O2,
        O2 ∈
            ((@AppendixN.EventFibre.atoms sigma iota
              (Classical.decEq sigma) linIota E).image
              (fun omega =>
                { cls := (row omega).outputClass
                  supportId := supp omega
                  thresholdLayer := thr omega })).filter
              (fun O => O.cls = OutputClassV4.progress) ->
          progressPathOf O1 = progressPathOf O2 -> O1 = O2
  progress_hweight_le_path :
    forall O,
      O ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
        terminalWeight O <= phase.chernoff.weight (progressPathOf O)
  progress_hbudget_le_output : termChernoff phase <= O_P
  endpoint_hclass_le_olc :
    AppendixN.classMassV4
      ((@AppendixN.EventFibre.atoms sigma iota
        (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight
      OutputClassV4.endpoint <= phase.returnPkg.olc
  endpoint_hOrdinaryShort_nonneg : 0 <= phase.returnPkg.ordinaryShort
  endpoint_hSemiperiodic_nonneg : 0 <= phase.returnPkg.semiperiodic
  endpoint_hNonlocalLong_nonneg : 0 <= phase.returnPkg.nonlocalLong
  endpoint_hbudget_le_output : termReturn phase <= O_E
  cnlCleanTerm : Real
  cnl_hclass_le_clean :
    AppendixN.classMassV4
      ((@AppendixN.EventFibre.atoms sigma iota
        (Classical.decEq sigma) linIota E).image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight
      OutputClassV4.cnl <= cnlCleanTerm
  cnl_hclean_bound :
    0 <= cnlCleanTerm /\
      cnlCleanTerm <=
        erdos260Constants.cStar * erdos260Constants.ξ *
          (ctx.shell.X : Real) / 6
  cnl_hbudget_le_output :
    erdos260Constants.cStar * erdos260Constants.ξ *
      (ctx.shell.X : Real) / 6 <= O_CNL
  bddWtLow : OutputObjectV4 -> Real
  bddWtPaid : OutputObjectV4 -> Real
  bddRemLow : Real
  bddPaidMass : Real
  bddOverlap : Real
  bddMainPaid : Real
  bddRemPaid : Real
  bddBranchPaid : chernoffLeaf.stoppedTree.Path -> Real
  bdd_overlap_nonneg : 0 <= bddOverlap
  bdd_paid_le_branchPaid :
    bddPaidMass <=
      ∑ b ∈ chernoffLeaf.stoppedTree.paths, bddBranchPaid b
  bdd_branchPaid_le_overlap_shellArea :
    forall b, b ∈ chernoffLeaf.stoppedTree.paths ->
      bddBranchPaid b <= bddOverlap * (chernoffLeaf.wt0 b * chernoffLeaf.Ysh b)
  bdd_overlap_budget :
    bddOverlap *
        (erdos260Constants.cStar * erdos260Constants.ξ *
          (ctx.shell.X : Real) / 6) <=
      bddMainPaid + bddRemPaid
  bdd_paid_eq :
    bddPaidMass =
      (∑ o ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun o => o.cls = OutputClassV4.bdd),
        bddWtPaid o)
  bdd_split :
    forall o,
      o ∈
          ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun o => o.cls = OutputClassV4.bdd) ->
        terminalWeight o = bddWtLow o + bddWtPaid o
  bdd_low_le :
    (∑ o ∈
        ((@AppendixN.EventFibre.atoms sigma iota
          (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega })).filter
          (fun o => o.cls = OutputClassV4.bdd),
      bddWtLow o) <= bddRemLow
  bdd_output_budget : bddMainPaid + (bddRemLow + bddRemPaid) <= O_bdd

namespace ActualStructuredTerminalAllFieldsLowPaidData

/-- Pin an all-fields terminal package to one actual phase once the three
phase-sensitive routes have been identified with that phase. -/
def toPinnedPhaseAllFieldsLowPaidData
    {ctx : ActualFailureContext}
    {chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)}
    {phase :
      ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : Real)}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    {variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V}
    (data :
      ActualStructuredTerminalAllFieldsLowPaidData ctx chernoffLeaf variation
        O_D O_P O_E O_CNL O_bdd)
    (hdense : data.densePhase = phase)
    (hprogress : data.progressPhase = phase)
    (hendpoint : data.endpointPhase = phase) :
    ActualStructuredTerminalPinnedPhaseAllFieldsLowPaidData ctx
      chernoffLeaf phase variation O_D O_P O_E O_CNL O_bdd where
  sigma := data.sigma
  iota := data.iota
  linIota := data.linIota
  E := data.E
  row := data.row
  supp := data.supp
  thr := data.thr
  terminalWeight := data.terminalWeight
  terminalCharge := data.terminalCharge
  hterm_raw := data.hterm_raw
  hcompression := data.hcompression
  densePointOf := data.densePointOf
  dense_hpoint_mem := by
    cases hdense
    exact data.dense_hpoint_mem
  dense_hinj := data.dense_hinj
  dense_hweight_le_one := data.dense_hweight_le_one
  dense_hbudget_le_output := by
    cases hdense
    exact data.dense_hbudget_le_output
  progressPathDecEq := by
    cases hprogress
    exact data.progressPathDecEq
  progressPathOf := by
    cases hprogress
    exact data.progressPathOf
  progress_hpath_mem := by
    cases hprogress
    exact data.progress_hpath_mem
  progress_hinj := by
    cases hprogress
    exact data.progress_hinj
  progress_hweight_le_path := by
    cases hprogress
    exact data.progress_hweight_le_path
  progress_hbudget_le_output := by
    cases hprogress
    exact data.progress_hbudget_le_output
  endpoint_hclass_le_olc := by
    cases hendpoint
    exact data.endpoint_hclass_le_olc
  endpoint_hOrdinaryShort_nonneg :=
    by
      cases hendpoint
      exact data.endpoint_hOrdinaryShort_nonneg
  endpoint_hSemiperiodic_nonneg :=
    by
      cases hendpoint
      exact data.endpoint_hSemiperiodic_nonneg
  endpoint_hNonlocalLong_nonneg :=
    by
      cases hendpoint
      exact data.endpoint_hNonlocalLong_nonneg
  endpoint_hbudget_le_output := by
    cases hendpoint
    exact data.endpoint_hbudget_le_output
  cnlCleanTerm := data.cnlCleanTerm
  cnl_hclass_le_clean := data.cnl_hclass_le_clean
  cnl_hclean_bound := data.cnl_hclean_bound
  cnl_hbudget_le_output := data.cnl_hbudget_le_output
  bddWtLow := data.bddWtLow
  bddWtPaid := data.bddWtPaid
  bddRemLow := data.bddRemLow
  bddPaidMass := data.bddPaidMass
  bddOverlap := data.bddOverlap
  bddMainPaid := data.bddMainPaid
  bddRemPaid := data.bddRemPaid
  bddBranchPaid := data.bddBranchPaid
  bdd_overlap_nonneg := data.bdd_overlap_nonneg
  bdd_paid_le_branchPaid := data.bdd_paid_le_branchPaid
  bdd_branchPaid_le_overlap_shellArea :=
    data.bdd_branchPaid_le_overlap_shellArea
  bdd_overlap_budget := data.bdd_overlap_budget
  bdd_paid_eq := data.bdd_paid_eq
  bdd_split := data.bdd_split
  bdd_low_le := data.bdd_low_le
  bdd_output_budget := data.bdd_output_budget

end ActualStructuredTerminalAllFieldsLowPaidData

namespace ActualStructuredTerminalPinnedPhaseAllFieldsLowPaidData

/-- Package the pinned-phase terminal fields as the all-fields terminal surface. -/
def toAllFieldsLowPaidData
    {ctx : ActualFailureContext}
    {chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)}
    {phase :
      ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : Real)}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    {variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V}
    (data :
      ActualStructuredTerminalPinnedPhaseAllFieldsLowPaidData ctx
        chernoffLeaf phase variation O_D O_P O_E O_CNL O_bdd)
    (cnlLeaf :
      CNLStandardWeightedKraftShellInputData ctx.shell erdos260Constants.cStar
        erdos260Constants.ξ) :
    ActualStructuredTerminalAllFieldsLowPaidData ctx chernoffLeaf variation
      O_D O_P O_E O_CNL O_bdd where
  sigma := data.sigma
  iota := data.iota
  linIota := data.linIota
  E := data.E
  row := data.row
  supp := data.supp
  thr := data.thr
  terminalWeight := data.terminalWeight
  terminalCharge := data.terminalCharge
  hterm_raw := data.hterm_raw
  hcompression := data.hcompression
  densePhase := phase
  densePointOf := data.densePointOf
  dense_hpoint_mem := data.dense_hpoint_mem
  dense_hinj := data.dense_hinj
  dense_hweight_le_one := data.dense_hweight_le_one
  dense_hbudget_le_output := data.dense_hbudget_le_output
  progressPhase := phase
  progressPathDecEq := data.progressPathDecEq
  progressPathOf := data.progressPathOf
  progress_hpath_mem := data.progress_hpath_mem
  progress_hinj := data.progress_hinj
  progress_hweight_le_path := data.progress_hweight_le_path
  progress_hbudget_le_output := data.progress_hbudget_le_output
  endpointPhase := phase
  endpoint_hclass_le_olc := data.endpoint_hclass_le_olc
  endpoint_hOrdinaryShort_nonneg := data.endpoint_hOrdinaryShort_nonneg
  endpoint_hSemiperiodic_nonneg := data.endpoint_hSemiperiodic_nonneg
  endpoint_hNonlocalLong_nonneg := data.endpoint_hNonlocalLong_nonneg
  endpoint_hbudget_le_output := data.endpoint_hbudget_le_output
  cnlLeaf := cnlLeaf
  cnlCleanTerm := data.cnlCleanTerm
  cnl_hclass_le_clean := data.cnl_hclass_le_clean
  cnl_hclean_bound := data.cnl_hclean_bound
  cnl_hbudget_le_output := data.cnl_hbudget_le_output
  bddWtLow := data.bddWtLow
  bddWtPaid := data.bddWtPaid
  bddRemLow := data.bddRemLow
  bddPaidMass := data.bddPaidMass
  bddOverlap := data.bddOverlap
  bddMainPaid := data.bddMainPaid
  bddRemPaid := data.bddRemPaid
  bddBranchPaid := data.bddBranchPaid
  bdd_overlap_nonneg := data.bdd_overlap_nonneg
  bdd_paid_le_branchPaid := data.bdd_paid_le_branchPaid
  bdd_branchPaid_le_overlap_shellArea :=
    data.bdd_branchPaid_le_overlap_shellArea
  bdd_overlap_budget := data.bdd_overlap_budget
  bdd_paid_eq := data.bdd_paid_eq
  bdd_split := data.bdd_split
  bdd_low_le := data.bdd_low_le
  bdd_output_budget := data.bdd_output_budget

end ActualStructuredTerminalPinnedPhaseAllFieldsLowPaidData

/-- Collapse pinned-phase terminal all-fields data all the way to the structured
terminal low-paid package used by the high-excess bridge. -/
def ActualStructuredTerminalPinnedPhaseAllFieldsLowPaidData.toStructuredTerminalLowPaidData
    {ctx : ActualFailureContext}
    {chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)}
    {phase :
      ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : Real)}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    {variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V}
    (data :
      ActualStructuredTerminalPinnedPhaseAllFieldsLowPaidData ctx
        chernoffLeaf phase variation O_D O_P O_E O_CNL O_bdd)
    (cnlLeaf :
      CNLStandardWeightedKraftShellInputData ctx.shell erdos260Constants.cStar
        erdos260Constants.ξ) :
    ActualStructuredTerminalLowPaidData ctx chernoffLeaf variation
      O_D O_P O_E O_CNL O_bdd :=
  let allFields := data.toAllFieldsLowPaidData cnlLeaf
  let allClassFields := allFields.toAllClassFieldsFiniteOverlapData
  let endpointFields := allClassFields.toMassDenseProgressEndpointFieldsData
  let progressFields := endpointFields.toMassDenseProgressFieldsData
  let denseFields := progressFields.toMassDenseFieldsData
  let massFields := denseFields.toMassFieldsData
  let terminalFields := massFields.toTerminalFieldsData
  let finiteOverlap := terminalFields.toFiniteOverlapLowPaidData
  finiteOverlap.toStructuredTerminalLowPaidData

/-- Collapse pinned-phase all-fields terminal data to the coupled Bdd/L6
N.2/N.3 package used by the older actual bridges. -/
def ActualStructuredTerminalPinnedPhaseAllFieldsLowPaidData.toBddL6Data
    {ctx : ActualFailureContext}
    {chernoffLeaf :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)}
    {phase :
      ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : Real)}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    {variation :
      AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
        ctx.n24SupportCount_pos O_V}
    (data :
      ActualStructuredTerminalPinnedPhaseAllFieldsLowPaidData ctx
        chernoffLeaf phase variation O_D O_P O_E O_CNL O_bdd)
    (cnlLeaf :
      CNLStandardWeightedKraftShellInputData ctx.shell erdos260Constants.cStar
        erdos260Constants.ξ) :
    ActualClosedN2N3BddL6Data ctx chernoffLeaf
      O_D O_P O_E O_CNL O_bdd O_V :=
  (data.toStructuredTerminalLowPaidData cnlLeaf).toBddL6Data

/--
Actual final surface with raw CNL/Return/Run, closed N.2 variation, and raw
N.3.3/L.6 terminal data.

This is a stricter manuscript-facing boundary than
`GlobalAssemblyActualRawCNLRRClosedN2N3BddL6Inputs`: terminal absorption is no
longer bundled, while the same shell-paid Chernoff leaf still feeds both the
phase and the bounded-class L.6 split.
-/
structure GlobalAssemblyActualRawCNLRRRawTerminalLowPaidInputs where
  chernoff : forall ctx : ActualFailureContext,
    RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real)
  cnl : forall ctx : ActualFailureContext,
    ActualCNLRawL112G35Data ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6Data ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52Data ctx
  variation : forall ctx : ActualFailureContext,
    AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos
      (termRun
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualRawTerminalLowPaidData ctx (chernoff ctx) (variation ctx)
      (termDensePack
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualRawCNLRRRawTerminalLowPaidInputs

/-- Project the raw terminal-low-paid interface to the coupled Bdd/L6 closed
N.2/N.3 actual interface. -/
def toBddL6Inputs
    (data : GlobalAssemblyActualRawCNLRRRawTerminalLowPaidInputs) :
    GlobalAssemblyActualRawCNLRRClosedN2N3BddL6Inputs where
  chernoff := data.chernoff
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2n3 := fun ctx => (data.terminal ctx).toBddL6Data

end GlobalAssemblyActualRawCNLRRRawTerminalLowPaidInputs

/-- Final bridge from raw terminal-low-paid actual N.3.3/L.6 data. -/
theorem erdos260_final_actual_rawCNLRRRawTerminalLowPaid
    (data : GlobalAssemblyActualRawCNLRRRawTerminalLowPaidInputs) :
    Erdos260Statement :=
  erdos260_final_actual_rawCNLRRClosedN2N3BddL6 data.toBddL6Inputs

/--
Actual final surface with both N.2 and N.3.3/L.6 opened to raw
manuscript-facing data.

Compared with `GlobalAssemblyActualRawCNLRRRawTerminalLowPaidInputs`, the
variation input is no longer bundled as a closed N.2 package: it is supplied by
raw first-crossing records, drop-density estimates, and the rolling-window
budget.
-/
structure GlobalAssemblyActualRawCNLRRRawN2RawTerminalLowPaidInputs where
  chernoff : forall ctx : ActualFailureContext,
    RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real)
  cnl : forall ctx : ActualFailureContext,
    ActualCNLRawL112G35Data ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6Data ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52Data ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualRawTerminalLowPaidData ctx (chernoff ctx)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualRawCNLRRRawN2RawTerminalLowPaidInputs

/-- Project raw N.2 first-crossing data to the previous closed-N.2 actual
surface. -/
def toRawTerminalLowPaidInputs
    (data : GlobalAssemblyActualRawCNLRRRawN2RawTerminalLowPaidInputs) :
    GlobalAssemblyActualRawCNLRRRawTerminalLowPaidInputs where
  chernoff := data.chernoff
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  variation := fun ctx => (data.n2 ctx).toVariationData
  terminal := data.terminal

end GlobalAssemblyActualRawCNLRRRawN2RawTerminalLowPaidInputs

/-- Final bridge from raw N.2 first-crossing and raw N.3.3/L.6 terminal data. -/
theorem erdos260_final_actual_rawCNLRRRawN2RawTerminalLowPaid
    (data : GlobalAssemblyActualRawCNLRRRawN2RawTerminalLowPaidInputs) :
    Erdos260Statement :=
  erdos260_final_actual_rawCNLRRRawTerminalLowPaid
    data.toRawTerminalLowPaidInputs

/--
Actual final surface with raw N.2 and structured N.3.3/L.6 terminal route
inputs.

This is the strongest local actual theorem boundary in this file: CNL, Return,
Run, N.2, and the N.3.3 terminal classes are all exposed at manuscript-facing
construction surfaces, while carry, DensePack, Tower, and the actual phase
assembly stay closed by the large pinned failure context.
-/
structure GlobalAssemblyActualRawCNLRRRawN2StructuredTerminalLowPaidInputs where
  chernoff : forall ctx : ActualFailureContext,
    RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real)
  cnl : forall ctx : ActualFailureContext,
    ActualCNLRawL112G35Data ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6Data ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52Data ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalLowPaidData ctx (chernoff ctx)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithChernoffLeaf
          (chernoff ctx)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualRawCNLRRRawN2StructuredTerminalLowPaidInputs

/-- Project the structured terminal route inputs to the coupled Bdd/L6 actual
surface. -/
def toBddL6Inputs
    (data : GlobalAssemblyActualRawCNLRRRawN2StructuredTerminalLowPaidInputs) :
    GlobalAssemblyActualRawCNLRRClosedN2N3BddL6Inputs where
  chernoff := data.chernoff
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2n3 := fun ctx => (data.terminal ctx).toBddL6Data

end GlobalAssemblyActualRawCNLRRRawN2StructuredTerminalLowPaidInputs

/-- Final bridge from raw N.2 and structured N.3.3/L.6 terminal route data. -/
theorem erdos260_final_actual_rawCNLRRRawN2StructuredTerminalLowPaid
    (data : GlobalAssemblyActualRawCNLRRRawN2StructuredTerminalLowPaidInputs) :
    Erdos260Statement :=
  erdos260_final_actual_rawCNLRRClosedN2N3BddL6 data.toBddL6Inputs

/--
Actual final surface with the shell-paid Chernoff leaf also opened to its raw
stopped-tree layer-cake data.

This keeps the Chernoff phase and the L.6 bounded-class proof coupled through
the same reconstructed `RegularShellPaidChernoff22_1AInputData`.
-/
structure GlobalAssemblyActualRawChernoffCNLRRRawN2StructuredTerminalLowPaidInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffRawData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLRawL112G35Data ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6Data ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52Data ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalLowPaidData ctx ((chernoff ctx).toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualRawChernoffCNLRRRawN2StructuredTerminalLowPaidInputs

/-- Project raw shell-paid Chernoff data to the previous strongest actual
surface. -/
def toRawN2StructuredTerminalLowPaidInputs
    (data : GlobalAssemblyActualRawChernoffCNLRRRawN2StructuredTerminalLowPaidInputs) :
    GlobalAssemblyActualRawCNLRRRawN2StructuredTerminalLowPaidInputs where
  chernoff := fun ctx => (data.chernoff ctx).toChernoffLeaf
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := data.terminal

end GlobalAssemblyActualRawChernoffCNLRRRawN2StructuredTerminalLowPaidInputs

/-- Final bridge from raw shell-paid Chernoff, raw N.2, and structured
N.3.3/L.6 terminal route data. -/
theorem erdos260_final_actual_rawChernoffCNLRRRawN2StructuredTerminalLowPaid
    (data : GlobalAssemblyActualRawChernoffCNLRRRawN2StructuredTerminalLowPaidInputs) :
    Erdos260Statement :=
  erdos260_final_actual_rawCNLRRRawN2StructuredTerminalLowPaid
    data.toRawN2StructuredTerminalLowPaidInputs

/--
Actual final surface with the shell-paid Chernoff stopped family exposed at
field level.

This is a presentation refinement of the raw Chernoff surface: the stopped-tree
family is visible as paths, weights, costs, tilt/tail scalars, and the Lemma
22.1 shell-budget certificate.
-/
structure GlobalAssemblyActualStoppedTreeChernoffCNLRRRawN2StructuredTerminalLowPaidInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffStoppedTreeFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLRawL112G35Data ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6Data ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52Data ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toShellPaidChernoffRawData.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalLowPaidData ctx
      ((chernoff ctx).toShellPaidChernoffRawData.toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toShellPaidChernoffRawData.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toShellPaidChernoffRawData.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toShellPaidChernoffRawData.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toShellPaidChernoffRawData.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toShellPaidChernoffRawData.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualStoppedTreeChernoffCNLRRRawN2StructuredTerminalLowPaidInputs

/-- Project field-level stopped-tree Chernoff data to the raw shell-paid
Chernoff actual surface. -/
def toRawChernoffInputs
    (data : GlobalAssemblyActualStoppedTreeChernoffCNLRRRawN2StructuredTerminalLowPaidInputs) :
    GlobalAssemblyActualRawChernoffCNLRRRawN2StructuredTerminalLowPaidInputs where
  chernoff := fun ctx => (data.chernoff ctx).toShellPaidChernoffRawData
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := data.terminal

end GlobalAssemblyActualStoppedTreeChernoffCNLRRRawN2StructuredTerminalLowPaidInputs

/-- Final bridge from field-level stopped-tree Chernoff data, raw N.2, and
structured N.3.3/L.6 terminal route data. -/
theorem erdos260_final_actual_stoppedTreeChernoffCNLRRRawN2StructuredTerminalLowPaid
    (data :
      GlobalAssemblyActualStoppedTreeChernoffCNLRRRawN2StructuredTerminalLowPaidInputs) :
    Erdos260Statement :=
  erdos260_final_actual_rawChernoffCNLRRRawN2StructuredTerminalLowPaid
    data.toRawChernoffInputs

/--
Actual final surface with the Chernoff stopped-tree shell budget split into
pointwise/moment and tail-budget components.

This is a smaller but useful step toward the manuscript proof objects: Lemma
22.1's two analytic subcertificates are no longer hidden inside one bundled
`ChernoffShellBudgetData`.
-/
structure GlobalAssemblyActualSplitBudgetChernoffCNLRRRawN2StructuredTerminalLowPaidInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffSplitBudgetFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLRawL112G35Data ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6Data ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52Data ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalLowPaidData ctx
      ((chernoff ctx).toStoppedTreeFieldsData
        |>.toShellPaidChernoffRawData
        |>.toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualSplitBudgetChernoffCNLRRRawN2StructuredTerminalLowPaidInputs

/-- Project the split-budget Chernoff surface to the field-level stopped-tree
surface. -/
def toStoppedTreeChernoffInputs
    (data :
      GlobalAssemblyActualSplitBudgetChernoffCNLRRRawN2StructuredTerminalLowPaidInputs) :
    GlobalAssemblyActualStoppedTreeChernoffCNLRRRawN2StructuredTerminalLowPaidInputs where
  chernoff := fun ctx => (data.chernoff ctx).toStoppedTreeFieldsData
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := data.terminal

end GlobalAssemblyActualSplitBudgetChernoffCNLRRRawN2StructuredTerminalLowPaidInputs

/-- Final bridge from split Chernoff shell-budget data, raw N.2, and structured
N.3.3/L.6 terminal route data. -/
theorem erdos260_final_actual_splitBudgetChernoffCNLRRRawN2StructuredTerminalLowPaid
    (data :
      GlobalAssemblyActualSplitBudgetChernoffCNLRRRawN2StructuredTerminalLowPaidInputs) :
    Erdos260Statement :=
  erdos260_final_actual_stoppedTreeChernoffCNLRRRawN2StructuredTerminalLowPaid
    data.toStoppedTreeChernoffInputs

/--
Actual final surface with the Chernoff tail budget exposed as an exponential
tail comparison.

This separates the pointwise/moment budget from the manuscript large-scale
tail estimate, including the explicit length condition used in the Chernoff
calibration.
-/
structure GlobalAssemblyActualExponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaidInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffExponentialTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLRawL112G35Data ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6Data ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52Data ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalLowPaidData ctx
      ((chernoff ctx).toSplitBudgetFieldsData
        |>.toStoppedTreeFieldsData
        |>.toShellPaidChernoffRawData
        |>.toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((returnPkg ctx).toPackageInputData)
          ((run ctx).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualExponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaidInputs

/-- Project exponential-tail Chernoff data to the split-budget actual surface. -/
def toSplitBudgetChernoffInputs
    (data :
      GlobalAssemblyActualExponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaidInputs) :
    GlobalAssemblyActualSplitBudgetChernoffCNLRRRawN2StructuredTerminalLowPaidInputs where
  chernoff := fun ctx => (data.chernoff ctx).toSplitBudgetFieldsData
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := data.terminal

end GlobalAssemblyActualExponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaidInputs

/-- Final bridge from exponential-tail Chernoff data, raw N.2, and structured
N.3.3/L.6 terminal route data. -/
theorem erdos260_final_actual_exponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaid
    (data :
      GlobalAssemblyActualExponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaidInputs) :
    Erdos260Statement :=
  erdos260_final_actual_splitBudgetChernoffCNLRRRawN2StructuredTerminalLowPaid
    data.toSplitBudgetChernoffInputs

/--
Actual final surface with Return and Run scalar smallness exposed as raw
inequalities.

This keeps the current exponential-tail Chernoff, raw CNL, raw N.2, and
structured N.3.3/L.6 terminal routes, while replacing the bundled Return/Run
smallness packages by their final scalar budget inequalities.
-/
structure GlobalAssemblyActualScalarRRExponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaidInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffExponentialTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLRawL112G35Data ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6ScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52ScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          (((run ctx).toRawData).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalLowPaidData ctx
      ((chernoff ctx).toSplitBudgetFieldsData
        |>.toStoppedTreeFieldsData
        |>.toShellPaidChernoffRawData
        |>.toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          (((run ctx).toRawData).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          (((run ctx).toRawData).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          (((run ctx).toRawData).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          (((run ctx).toRawData).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          (((run ctx).toRawData).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualScalarRRExponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaidInputs

/-- Project scalar Return/Run smallness fields to the previous exponential-tail
actual surface. -/
def toExponentialTailChernoffInputs
    (data :
      GlobalAssemblyActualScalarRRExponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaidInputs) :
    GlobalAssemblyActualExponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaidInputs where
  chernoff := data.chernoff
  cnl := data.cnl
  returnPkg := fun ctx => (data.returnPkg ctx).toRawData
  run := fun ctx => (data.run ctx).toRawData
  n2 := data.n2
  terminal := data.terminal

end GlobalAssemblyActualScalarRRExponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaidInputs

/-- Final bridge from scalar Return/Run smallness, exponential-tail Chernoff,
raw N.2, and structured N.3.3/L.6 terminal route data. -/
theorem erdos260_final_actual_scalarRRExponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaid
    (data :
      GlobalAssemblyActualScalarRRExponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaidInputs) :
    Erdos260Statement :=
  erdos260_final_actual_exponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaid
    data.toExponentialTailChernoffInputs

/--
Actual final surface with Chernoff pointwise tilt and aggregate moment budgets
separated.

This is the current strongest local provider boundary: Chernoff is exposed as
tilt, moment, exponential-tail, and shell-paid layer-cake fields; Return and
Run expose scalar smallness; N.2 and N.3.3 terminal routes are manuscript-facing.
-/
structure GlobalAssemblyActualTiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaidInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffTiltMomentExponentialTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLRawL112G35Data ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6ScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52ScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          (((run ctx).toRawData).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalLowPaidData ctx
      ((chernoff ctx).toExponentialTailFieldsData
        |>.toSplitBudgetFieldsData
        |>.toStoppedTreeFieldsData
        |>.toShellPaidChernoffRawData
        |>.toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          (((run ctx).toRawData).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          (((run ctx).toRawData).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          (((run ctx).toRawData).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          (((run ctx).toRawData).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          (((run ctx).toRawData).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualTiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaidInputs

/-- Project separated Chernoff tilt/moment fields to the scalar Return/Run
exponential-tail actual surface. -/
def toScalarRRExponentialTailInputs
    (data :
      GlobalAssemblyActualTiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaidInputs) :
    GlobalAssemblyActualScalarRRExponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaidInputs where
  chernoff := fun ctx => (data.chernoff ctx).toExponentialTailFieldsData
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := data.terminal

end GlobalAssemblyActualTiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaidInputs

/-- Final bridge from separated Chernoff tilt/moment, scalar Return/Run
smallness, raw N.2, and structured N.3.3/L.6 terminal route data. -/
theorem erdos260_final_actual_tiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaid
    (data :
      GlobalAssemblyActualTiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaidInputs) :
    Erdos260Statement :=
  erdos260_final_actual_scalarRRExponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaid
    data.toScalarRRExponentialTailInputs

/--
Actual final surface with Run L.4.1 split and output absorption separated.

This keeps the current strongest Chernoff/Return/CNL/N.2/N.3.3 boundary, but
opens the run package into the two manuscript components consumed by the
closed L.4.1/L.4.2/I.5.2 constructor.
-/
structure GlobalAssemblyActualSplitRunTiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaidInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffTiltMomentExponentialTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLRawL112G35Data ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6ScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalLowPaidData ctx
      ((chernoff ctx).toExponentialTailFieldsData
        |>.toSplitBudgetFieldsData
        |>.toStoppedTreeFieldsData
        |>.toShellPaidChernoffRawData
        |>.toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualSplitRunTiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaidInputs

/-- Recombine the separated Run data and project to the previous strongest
actual surface. -/
def toTiltMomentChernoffScalarRRInputs
    (data :
      GlobalAssemblyActualSplitRunTiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaidInputs) :
    GlobalAssemblyActualTiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaidInputs where
  chernoff := data.chernoff
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := fun ctx => (data.run ctx).toScalarData
  n2 := data.n2
  terminal := data.terminal

end GlobalAssemblyActualSplitRunTiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaidInputs

/-- Final bridge from split Run L.4.1 data, separated Chernoff tilt/moment,
scalar Return smallness, raw N.2, and structured N.3.3/L.6 terminal routes. -/
theorem erdos260_final_actual_splitRunTiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaid
    (data :
      GlobalAssemblyActualSplitRunTiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaidInputs) :
    Erdos260Statement :=
  erdos260_final_actual_tiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaid
    data.toTiltMomentChernoffScalarRRInputs

/--
Actual final surface with the bounded terminal L.6 paid part exposed in the
finite-overlap form, and Run L.4.1 split/absorption separated.
-/
structure GlobalAssemblyActualFiniteOverlapTerminalSplitRunTiltMomentChernoffScalarRRCNLRRRawN2StructuredInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffTiltMomentExponentialTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLRawL112G35Data ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6ScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalFiniteOverlapLowPaidData ctx
      ((chernoff ctx).toExponentialTailFieldsData
        |>.toSplitBudgetFieldsData
        |>.toStoppedTreeFieldsData
        |>.toShellPaidChernoffRawData
        |>.toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toExponentialTailFieldsData
            |>.toSplitBudgetFieldsData
            |>.toStoppedTreeFieldsData
            |>.toShellPaidChernoffRawData
            |>.toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualFiniteOverlapTerminalSplitRunTiltMomentChernoffScalarRRCNLRRRawN2StructuredInputs

/-- Collapse finite-overlap terminal paid routing and project to the previous
split-Run actual surface. -/
def toSplitRunTiltMomentChernoffScalarRRInputs
    (data :
      GlobalAssemblyActualFiniteOverlapTerminalSplitRunTiltMomentChernoffScalarRRCNLRRRawN2StructuredInputs) :
    GlobalAssemblyActualSplitRunTiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaidInputs where
  chernoff := data.chernoff
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := fun ctx => (data.terminal ctx).toStructuredTerminalLowPaidData

end GlobalAssemblyActualFiniteOverlapTerminalSplitRunTiltMomentChernoffScalarRRCNLRRRawN2StructuredInputs

/-- Final bridge from finite-overlap L.6.2 terminal data, split Run L.4.1 data,
separated Chernoff tilt/moment, scalar Return smallness, and raw N.2. -/
theorem erdos260_final_actual_finiteOverlapTerminalSplitRunTiltMomentChernoffScalarRRCNLRRRawN2Structured
    (data :
      GlobalAssemblyActualFiniteOverlapTerminalSplitRunTiltMomentChernoffScalarRRCNLRRRawN2StructuredInputs) :
    Erdos260Statement :=
  erdos260_final_actual_splitRunTiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaid
    data.toSplitRunTiltMomentChernoffScalarRRInputs

/--
Actual final surface with the finite part of Lemma 22.1 Chernoff closed by the
canonical finite-sum budget.

The remaining provider obligations are now the finite stopped family, the
exponential-tail comparison, shell-paid layer-cake smallness, raw CNL/Return,
split Run, raw N.2 first-crossing, and finite-overlap L.6 terminal routing.
-/
structure GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitRunScalarRRCNLRRRawN2StructuredInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumExponentialTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLRawL112G35Data ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6ScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalFiniteOverlapLowPaidData ctx
      ((chernoff ctx).toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          (((returnPkg ctx).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitRunScalarRRCNLRRRawN2StructuredInputs

/-- Project canonical finite-sum Chernoff data to the previous separated
tilt/moment actual surface. -/
def toFiniteOverlapTerminalSplitRunTiltMomentInputs
    (data :
      GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitRunScalarRRCNLRRRawN2StructuredInputs) :
    GlobalAssemblyActualFiniteOverlapTerminalSplitRunTiltMomentChernoffScalarRRCNLRRRawN2StructuredInputs where
  chernoff := fun ctx => (data.chernoff ctx).toTiltMomentExponentialTailFieldsData
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := data.terminal

end GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitRunScalarRRCNLRRRawN2StructuredInputs

/-- Final bridge from canonical finite-sum Chernoff, finite-overlap L.6.2
terminal data, split Run L.4.1 data, scalar Return smallness, and raw N.2. -/
theorem erdos260_final_actual_finiteSumChernoffFiniteOverlapTerminalSplitRunScalarRRCNLRRRawN2Structured
    (data :
      GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitRunScalarRRCNLRRRawN2StructuredInputs) :
    Erdos260Statement :=
  erdos260_final_actual_finiteOverlapTerminalSplitRunTiltMomentChernoffScalarRRCNLRRRawN2Structured
    data.toFiniteOverlapTerminalSplitRunTiltMomentInputs

/--
Actual final surface with Return I.5.1/M.2/J.4/L.6 split into its local
manuscript certificates.

Compared with
`GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitRunScalarRRCNLRRRawN2StructuredInputs`,
the return provider now supplies short-return, OLC, and nonlocal-long
certificates directly; the final scalar smallness comparison remains explicit.
-/
structure GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitReturnRunRRCNLRawN2StructuredInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumExponentialTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLRawL112G35Data ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalFiniteOverlapLowPaidData ctx
      ((chernoff ctx).toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithChernoffLeaf
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toClusterInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitReturnRunRRCNLRawN2StructuredInputs

/-- Project split Return local certificates to the previous scalar-Return
actual surface. -/
def toFiniteSumChernoffFiniteOverlapTerminalSplitRunInputs
    (data :
      GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitReturnRunRRCNLRawN2StructuredInputs) :
    GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitRunScalarRRCNLRRRawN2StructuredInputs where
  chernoff := data.chernoff
  cnl := data.cnl
  returnPkg := fun ctx => (data.returnPkg ctx).toScalarData
  run := data.run
  n2 := data.n2
  terminal := data.terminal

end GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitReturnRunRRCNLRawN2StructuredInputs

/-- Final bridge from canonical finite-sum Chernoff, split Return, split Run,
finite-overlap L.6.2 terminal data, and raw N.2/CNL. -/
theorem erdos260_final_actual_finiteSumChernoffFiniteOverlapTerminalSplitReturnRunRRCNLRawN2Structured
    (data :
      GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitReturnRunRRCNLRawN2StructuredInputs) :
    Erdos260Statement :=
  erdos260_final_actual_finiteSumChernoffFiniteOverlapTerminalSplitRunScalarRRCNLRRRawN2Structured
    data.toFiniteSumChernoffFiniteOverlapTerminalSplitRunInputs

/--
Actual final surface with CNL supplied by direct code/fibre Nat-budget data.

This avoids projecting CNL back through the cluster-to-ladder leaf: the actual
phase package consumes the direct weighted-Kraft shell leaf obtained from the
code/fibre budget, while N.2 and N.3.3 are still evaluated on that same phase
package.
-/
structure GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumExponentialTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLCodeFibreNatBudgetData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalFiniteOverlapLowPaidData ctx
      ((chernoff ctx).toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- The actual phases assembled from direct code/fibre CNL data. -/
def phases
    (data :
      GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs)
    (ctx : ActualFailureContext) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  ctx.leafPhasesWithWeightedCNL
    ((data.chernoff ctx).toChernoffLeaf)
    ((data.cnl ctx).toWeightedKraftShellInputData)
    ((((data.returnPkg ctx).toScalarData).toRawData).toPackageInputData)
    ((((data.run ctx).toScalarData).toRawData).toPackageInputData)

/-- Definitional phase-class accounting for the code/fibre-CNL actual phases. -/
def accounting
    (data :
      GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs)
    (ctx : ActualFailureContext) :
    PhaseClassAccountingData (data.phases ctx) :=
  actualPhaseClassAccounting (data.phases ctx)

/-- Coupled Bdd/L6 closed N.2/N.3 data for the code/fibre-CNL actual phases. -/
def bddL6Data
    (data :
      GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs)
    (ctx : ActualFailureContext) :
    ActualClosedN2N3BddL6Data ctx ((data.chernoff ctx).toChernoffLeaf)
      (data.accounting ctx).O_D (data.accounting ctx).O_P
      (data.accounting ctx).O_E (data.accounting ctx).O_CNL
      (data.accounting ctx).O_bdd (data.accounting ctx).O_V :=
  ((data.terminal ctx).toStructuredTerminalLowPaidData).toBddL6Data

/-- Project the coupled N.2/N.3 data to the N.24 terminal-variation input. -/
def n24Input
    (data :
      GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs)
    (ctx : ActualFailureContext) :
    CarryHitGapN24TerminalVariationInputData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos (data.accounting ctx).O_D
      (data.accounting ctx).O_P (data.accounting ctx).O_E
      (data.accounting ctx).O_CNL (data.accounting ctx).O_bdd
      (data.accounting ctx).O_V :=
  ((data.bddL6Data ctx).toClosedN2N3InputData.toN24CanonicalYInputData)
    |>.toCanonicalSplitInputData
    |>.toTerminalVariationInputData

/-- Table-routed high-excess data for the code/fibre-CNL actual phases. -/
def toTableRoutedHighExcessData
    (data :
      GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs)
    (ctx : ActualFailureContext) :
    TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData
      (data.phases ctx) ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos where
  accounting := data.accounting ctx
  n24_input := data.n24Input ctx

/-- High-excess charge derived from code/fibre-CNL N.2/N.3 data. -/
def highExcessCharge
    (data :
      GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs)
    (ctx : ActualFailureContext) :
    HighExcessChargeData (data.phases ctx) ctx.n24CarryData :=
  tableRoutedSplitPhaseAccountedToHighExcessData
    (data.toTableRoutedHighExcessData ctx)

/-- Project the code/fibre-CNL actual surface to the final actual-consumption
interface. -/
def toActualInputs
    (data :
      GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    GlobalAssemblyActualInputs where
  carryData := ActualFailureContext.n24CarryData
  chernoff := fun ctx => (data.phases ctx).chernoff
  cnl := fun ctx => (data.phases ctx).cnl
  densePack := fun ctx => (data.phases ctx).densePack
  tower := fun ctx => (data.phases ctx).tower
  returnPkg := fun ctx => (data.phases ctx).returnPkg
  run := fun ctx => (data.phases ctx).run
  highExcessCharge := fun ctx => data.highExcessCharge ctx

end GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Final bridge from canonical finite-sum Chernoff, direct code/fibre CNL,
split Return/Run, finite-overlap L.6.2 terminal data, and raw N.2. -/
theorem erdos260_final_actual_finiteSumChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2Structured
    (data :
      GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    Erdos260Statement :=
  erdos260_final_actual data.toActualInputs

/--
Actual final surface with Chernoff tail in zero-length form.

This is the current lowest Chernoff boundary: finite pointwise/moment data are
closed by the canonical finite-sum construction, and the tail provider supplies
only the zero-length ratio estimate plus final smallness.  CNL is direct
code/fibre Nat-budget, Return and Run are split, and terminal L.6 remains in
finite-overlap form.
-/
structure GlobalAssemblyActualZeroLengthChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumZeroLengthTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLCodeFibreNatBudgetData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalFiniteOverlapLowPaidData ctx
      ((chernoff ctx).toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualZeroLengthChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Project zero-length Chernoff tail data to the finite-sum exponential-tail
code/fibre-CNL actual surface. -/
def toFiniteSumChernoffCodeFibreCNLInputs
    (data :
      GlobalAssemblyActualZeroLengthChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    GlobalAssemblyActualFiniteSumChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff := fun ctx => (data.chernoff ctx).toFiniteSumExponentialTailFieldsData
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := data.terminal

end GlobalAssemblyActualZeroLengthChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Final bridge from zero-length Chernoff tail, direct code/fibre CNL, split
Return/Run, finite-overlap L.6.2 terminal data, and raw N.2. -/
theorem erdos260_final_actual_zeroLengthChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2Structured
    (data :
      GlobalAssemblyActualZeroLengthChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    Erdos260Statement :=
  erdos260_final_actual_finiteSumChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2Structured
    data.toFiniteSumChernoffCodeFibreCNLInputs

/--
Actual final surface with Chernoff tail supplied as a numerator root bound and
an X-free scalar smallness comparison.

This opens the zero-length Chernoff tail one step further while keeping the
same direct code/fibre CNL, split Return/Run, raw N.2, and finite-overlap
terminal surfaces.
-/
structure GlobalAssemblyActualRootBoundChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLCodeFibreNatBudgetData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalFiniteOverlapLowPaidData ctx
      ((chernoff ctx).toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualRootBoundChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Project numerator-style Chernoff tail data to the zero-length actual
surface. -/
def toZeroLengthChernoffInputs
    (data :
      GlobalAssemblyActualRootBoundChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    GlobalAssemblyActualZeroLengthChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff := fun ctx => (data.chernoff ctx).toZeroLengthTailFieldsData
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := data.terminal

end GlobalAssemblyActualRootBoundChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Final bridge from numerator-style Chernoff tail, direct code/fibre CNL,
split Return/Run, finite-overlap L.6.2 terminal data, and raw N.2. -/
theorem erdos260_final_actual_rootBoundChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2Structured
    (data :
      GlobalAssemblyActualRootBoundChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    Erdos260Statement :=
  erdos260_final_actual_zeroLengthChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2Structured
    data.toZeroLengthChernoffInputs

/--
Actual final surface with the L.6 bounded-class finite-overlap terminal data
fully exposed as fields.

This keeps the current root-bound Chernoff tail, code/fibre CNL, split
Return/Run, and raw N.2 boundaries, while removing the last bundled
`FiniteOverlapLowPaidSplitData` terminal field from the strongest endpoint.
-/
structure GlobalAssemblyActualRootBoundChernoffTerminalFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLCodeFibreNatBudgetData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalFiniteOverlapFieldsLowPaidData ctx
      ((chernoff ctx).toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualRootBoundChernoffTerminalFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Project fully exposed terminal L.6 fields to the finite-overlap terminal
actual surface. -/
def toRootBoundChernoffFiniteOverlapTerminalInputs
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    GlobalAssemblyActualRootBoundChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff := data.chernoff
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := fun ctx => (data.terminal ctx).toFiniteOverlapLowPaidData

end GlobalAssemblyActualRootBoundChernoffTerminalFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Final bridge from root-bound Chernoff tail, direct code/fibre CNL, split
Return/Run, raw N.2, and fully exposed finite-overlap terminal L.6 data. -/
theorem erdos260_final_actual_rootBoundChernoffTerminalFieldsSplitReturnRunCodeFibreCNLRawN2Structured
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    Erdos260Statement :=
  erdos260_final_actual_rootBoundChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2Structured
    data.toRootBoundChernoffFiniteOverlapTerminalInputs

/--
Actual final surface with the terminal-mass N.3.1 compression fields exposed.

This removes the bundled `TableRoutedTerminalMassCompressionInputData` from the
strongest terminal endpoint while keeping the DensePack/progress/endpoint/CNL
class routes and the finite-overlap L.6 fields unchanged.
-/
structure GlobalAssemblyActualRootBoundChernoffTerminalMassFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLCodeFibreNatBudgetData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalMassFieldsFiniteOverlapFieldsLowPaidData ctx
      ((chernoff ctx).toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualRootBoundChernoffTerminalMassFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Project raw terminal-mass fields to the strongest existing terminal-field
actual surface. -/
def toTerminalFieldsInputs
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalMassFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    GlobalAssemblyActualRootBoundChernoffTerminalFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff := data.chernoff
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := fun ctx => (data.terminal ctx).toTerminalFieldsData

end GlobalAssemblyActualRootBoundChernoffTerminalMassFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Final bridge from root-bound Chernoff, direct CNL, split Return/Run, raw
N.2, finite-overlap L.6 data, and raw terminal-mass compression fields. -/
theorem erdos260_final_actual_rootBoundChernoffTerminalMassFieldsSplitReturnRunCodeFibreCNLRawN2Structured
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalMassFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    Erdos260Statement :=
  erdos260_final_actual_rootBoundChernoffTerminalFieldsSplitReturnRunCodeFibreCNLRawN2Structured
    data.toTerminalFieldsInputs

/--
Actual final surface with terminal-mass and DensePack support fields exposed.

The remaining terminal class routes are still carried by their structured
providers; this layer only opens the K.1.1 DensePack support certificate.
-/
structure GlobalAssemblyActualRootBoundChernoffTerminalMassDenseFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLCodeFibreNatBudgetData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalMassDenseFieldsFiniteOverlapFieldsLowPaidData ctx
      ((chernoff ctx).toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualRootBoundChernoffTerminalMassDenseFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Project raw DensePack fields to the terminal-mass-field actual surface. -/
def toTerminalMassFieldsInputs
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalMassDenseFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    GlobalAssemblyActualRootBoundChernoffTerminalMassFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff := data.chernoff
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := fun ctx => (data.terminal ctx).toMassFieldsData

end GlobalAssemblyActualRootBoundChernoffTerminalMassDenseFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Final bridge from the surface with raw terminal-mass and DensePack fields. -/
theorem erdos260_final_actual_rootBoundChernoffTerminalMassDenseFieldsSplitReturnRunCodeFibreCNLRawN2Structured
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalMassDenseFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    Erdos260Statement :=
  erdos260_final_actual_rootBoundChernoffTerminalMassFieldsSplitReturnRunCodeFibreCNLRawN2Structured
    data.toTerminalMassFieldsInputs

/--
Actual final surface with terminal-mass, DensePack, and progress-class fields
exposed directly.
-/
structure GlobalAssemblyActualRootBoundChernoffTerminalMassDenseProgressFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLCodeFibreNatBudgetData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalMassDenseProgressFieldsFiniteOverlapFieldsLowPaidData
      ctx
      ((chernoff ctx).toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualRootBoundChernoffTerminalMassDenseProgressFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Project raw progress fields to the terminal-mass/DensePack actual surface. -/
def toTerminalMassDenseFieldsInputs
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalMassDenseProgressFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    GlobalAssemblyActualRootBoundChernoffTerminalMassDenseFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff := data.chernoff
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := fun ctx => (data.terminal ctx).toMassDenseFieldsData

end GlobalAssemblyActualRootBoundChernoffTerminalMassDenseProgressFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Final bridge from the surface with raw terminal-mass, DensePack, and
progress-class fields. -/
theorem erdos260_final_actual_rootBoundChernoffTerminalMassDenseProgressFieldsSplitReturnRunCodeFibreCNLRawN2Structured
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalMassDenseProgressFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    Erdos260Statement :=
  erdos260_final_actual_rootBoundChernoffTerminalMassDenseFieldsSplitReturnRunCodeFibreCNLRawN2Structured
    data.toTerminalMassDenseFieldsInputs

/--
Actual final surface with terminal-mass, DensePack, progress, and endpoint
fields exposed directly.
-/
structure GlobalAssemblyActualRootBoundChernoffTerminalMassDenseProgressEndpointFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLCodeFibreNatBudgetData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalMassDenseProgressEndpointFieldsFiniteOverlapFieldsLowPaidData
      ctx
      ((chernoff ctx).toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualRootBoundChernoffTerminalMassDenseProgressEndpointFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Project raw endpoint fields to the terminal-mass/DensePack/progress surface. -/
def toTerminalMassDenseProgressFieldsInputs
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalMassDenseProgressEndpointFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    GlobalAssemblyActualRootBoundChernoffTerminalMassDenseProgressFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff := data.chernoff
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := fun ctx => (data.terminal ctx).toMassDenseProgressFieldsData

end GlobalAssemblyActualRootBoundChernoffTerminalMassDenseProgressEndpointFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Final bridge from the surface with raw terminal-mass, DensePack, progress,
and endpoint fields. -/
theorem erdos260_final_actual_rootBoundChernoffTerminalMassDenseProgressEndpointFieldsSplitReturnRunCodeFibreCNLRawN2Structured
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalMassDenseProgressEndpointFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    Erdos260Statement :=
  erdos260_final_actual_rootBoundChernoffTerminalMassDenseProgressFieldsSplitReturnRunCodeFibreCNLRawN2Structured
    data.toTerminalMassDenseProgressFieldsInputs

/--
Actual final surface with all table-routed terminal class-provider fields
exposed directly.
-/
structure GlobalAssemblyActualRootBoundChernoffTerminalAllClassFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLCodeFibreNatBudgetData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalAllClassFieldsFiniteOverlapFieldsLowPaidData
      ctx
      ((chernoff ctx).toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualRootBoundChernoffTerminalAllClassFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Project raw CNL terminal fields to the endpoint-field actual surface. -/
def toTerminalMassDenseProgressEndpointFieldsInputs
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalAllClassFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    GlobalAssemblyActualRootBoundChernoffTerminalMassDenseProgressEndpointFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff := data.chernoff
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := fun ctx =>
    (data.terminal ctx).toMassDenseProgressEndpointFieldsData

end GlobalAssemblyActualRootBoundChernoffTerminalAllClassFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Final bridge from the surface with all table-routed terminal class-provider
fields exposed directly. -/
theorem erdos260_final_actual_rootBoundChernoffTerminalAllClassFieldsSplitReturnRunCodeFibreCNLRawN2Structured
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalAllClassFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    Erdos260Statement :=
  erdos260_final_actual_rootBoundChernoffTerminalMassDenseProgressEndpointFieldsSplitReturnRunCodeFibreCNLRawN2Structured
    data.toTerminalMassDenseProgressEndpointFieldsInputs

/--
Actual final surface with all terminal class-provider fields and the L.6
bounded-class finite-overlap fields exposed directly.
-/
structure GlobalAssemblyActualRootBoundChernoffTerminalAllFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLCodeFibreNatBudgetData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalAllFieldsLowPaidData
      ctx
      ((chernoff ctx).toChernoffLeaf)
      ((n2 ctx).toVariationData)
      (termDensePack
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termChernoff
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termReturn
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termCnl
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)
      (termTower
        (ctx.leafPhasesWithWeightedCNL
          ((chernoff ctx).toChernoffLeaf)
          ((cnl ctx).toWeightedKraftShellInputData)
          ((((returnPkg ctx).toScalarData).toRawData).toPackageInputData)
          ((((run ctx).toScalarData).toRawData).toPackageInputData)).toClosurePhaseData)

namespace GlobalAssemblyActualRootBoundChernoffTerminalAllFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Project raw L.6 bounded-class fields to the all-class terminal surface. -/
def toTerminalAllClassFieldsInputs
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalAllFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    GlobalAssemblyActualRootBoundChernoffTerminalAllClassFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff := data.chernoff
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := fun ctx => (data.terminal ctx).toAllClassFieldsFiniteOverlapData

end GlobalAssemblyActualRootBoundChernoffTerminalAllFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Final bridge from the surface with all terminal class-provider and L.6
bounded-class fields exposed directly. -/
theorem erdos260_final_actual_rootBoundChernoffTerminalAllFieldsSplitReturnRunCodeFibreCNLRawN2Structured
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalAllFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    Erdos260Statement :=
  erdos260_final_actual_rootBoundChernoffTerminalAllClassFieldsSplitReturnRunCodeFibreCNLRawN2Structured
    data.toTerminalAllClassFieldsInputs

/-- The actual closure phase assembled by the strongest nonterminal leaves. -/
def actualClosurePhaseFromRootBoundCodeFibreSplitRR
    (ctx : ActualFailureContext)
    (chernoff : ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx)
    (cnl : ActualCNLCodeFibreNatBudgetData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx) :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  (ctx.leafPhasesWithWeightedCNL
    chernoff.toChernoffLeaf
    cnl.toWeightedKraftShellInputData
    ((returnPkg.toScalarData).toRawData).toPackageInputData
    ((run.toScalarData).toRawData).toPackageInputData).toClosurePhaseData

/--
Actual final surface whose terminal routes are pinned to the exact closure
phase assembled from the global Chernoff/CNL/Return/Run leaves.
-/
structure GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLCodeFibreNatBudgetData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (actualClosurePhaseFromRootBoundCodeFibreSplitRR ctx
          (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx)))
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalPinnedPhaseAllFieldsLowPaidData
      ctx
      ((chernoff ctx).toChernoffLeaf)
      (actualClosurePhaseFromRootBoundCodeFibreSplitRR ctx
        (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx))
      ((n2 ctx).toVariationData)
      (termDensePack
        (actualClosurePhaseFromRootBoundCodeFibreSplitRR ctx
          (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx)))
      (termChernoff
        (actualClosurePhaseFromRootBoundCodeFibreSplitRR ctx
          (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx)))
      (termReturn
        (actualClosurePhaseFromRootBoundCodeFibreSplitRR ctx
          (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx)))
      (termCnl
        (actualClosurePhaseFromRootBoundCodeFibreSplitRR ctx
          (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx)))
      (termTower
        (actualClosurePhaseFromRootBoundCodeFibreSplitRR ctx
          (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx)))

namespace GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Project the pinned-phase terminal surface to the all-fields actual surface. -/
def toTerminalAllFieldsInputs
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    GlobalAssemblyActualRootBoundChernoffTerminalAllFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff := data.chernoff
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := fun ctx =>
    (data.terminal ctx).toAllFieldsLowPaidData
      ((data.cnl ctx).toWeightedKraftShellInputData)

end GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs

/-- Final bridge from the surface whose terminal routes consume the actual
assembled closure phase. -/
theorem erdos260_final_actual_rootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunCodeFibreCNLRawN2Structured
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs) :
    Erdos260Statement :=
  erdos260_final_actual_rootBoundChernoffTerminalAllFieldsSplitReturnRunCodeFibreCNLRawN2Structured
    data.toTerminalAllFieldsInputs

/-- The actual closure phase assembled from direct weighted-Kraft CNL data. -/
def actualClosurePhaseFromRootBoundWeightedKraftSplitRR
    (ctx : ActualFailureContext)
    (chernoff : ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx)
    (cnl : ActualCNLWeightedKraftData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx) :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  (ctx.leafPhasesWithWeightedCNL
    chernoff.toChernoffLeaf
    cnl.toWeightedKraftShellInputData
    ((returnPkg.toScalarData).toRawData).toPackageInputData
    ((run.toScalarData).toRawData).toPackageInputData).toClosurePhaseData

/--
Actual final surface using the manuscript-direct weighted-Kraft CNL leaf and
terminal routes pinned to the exact assembled closure phase.
-/
structure GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunWeightedKraftCNLRawN2StructuredInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLWeightedKraftData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRawN2FirstCrossingData ctx
      (termRun
        (actualClosurePhaseFromRootBoundWeightedKraftSplitRR ctx
          (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx)))
  terminal : forall ctx : ActualFailureContext,
    ActualStructuredTerminalPinnedPhaseAllFieldsLowPaidData
      ctx
      ((chernoff ctx).toChernoffLeaf)
      (actualClosurePhaseFromRootBoundWeightedKraftSplitRR ctx
        (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx))
      ((n2 ctx).toVariationData)
      (termDensePack
        (actualClosurePhaseFromRootBoundWeightedKraftSplitRR ctx
          (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx)))
      (termChernoff
        (actualClosurePhaseFromRootBoundWeightedKraftSplitRR ctx
          (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx)))
      (termReturn
        (actualClosurePhaseFromRootBoundWeightedKraftSplitRR ctx
          (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx)))
      (termCnl
        (actualClosurePhaseFromRootBoundWeightedKraftSplitRR ctx
          (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx)))
      (termTower
        (actualClosurePhaseFromRootBoundWeightedKraftSplitRR ctx
          (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx)))

namespace GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunWeightedKraftCNLRawN2StructuredInputs

/-- The actual phases assembled from direct weighted-Kraft CNL data. -/
def phases
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunWeightedKraftCNLRawN2StructuredInputs)
    (ctx : ActualFailureContext) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  ctx.leafPhasesWithWeightedCNL
    ((data.chernoff ctx).toChernoffLeaf)
    ((data.cnl ctx).toWeightedKraftShellInputData)
    ((((data.returnPkg ctx).toScalarData).toRawData).toPackageInputData)
    ((((data.run ctx).toScalarData).toRawData).toPackageInputData)

/-- Definitional phase-class accounting for the weighted-Kraft actual phases. -/
def accounting
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunWeightedKraftCNLRawN2StructuredInputs)
    (ctx : ActualFailureContext) :
    PhaseClassAccountingData (data.phases ctx) :=
  actualPhaseClassAccounting (data.phases ctx)

/-- Coupled Bdd/L6 closed N.2/N.3 data for the weighted-Kraft actual phases. -/
def bddL6Data
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunWeightedKraftCNLRawN2StructuredInputs)
    (ctx : ActualFailureContext) :
    ActualClosedN2N3BddL6Data ctx ((data.chernoff ctx).toChernoffLeaf)
      (data.accounting ctx).O_D (data.accounting ctx).O_P
      (data.accounting ctx).O_E (data.accounting ctx).O_CNL
      (data.accounting ctx).O_bdd (data.accounting ctx).O_V :=
  ((data.terminal ctx).toStructuredTerminalLowPaidData
    ((data.cnl ctx).toWeightedKraftShellInputData)).toBddL6Data

/-- Project the coupled N.2/N.3 data to the N.24 terminal-variation input. -/
def n24Input
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunWeightedKraftCNLRawN2StructuredInputs)
    (ctx : ActualFailureContext) :
    CarryHitGapN24TerminalVariationInputData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos (data.accounting ctx).O_D
      (data.accounting ctx).O_P (data.accounting ctx).O_E
      (data.accounting ctx).O_CNL (data.accounting ctx).O_bdd
      (data.accounting ctx).O_V :=
  ((data.bddL6Data ctx).toClosedN2N3InputData.toN24CanonicalYInputData)
    |>.toCanonicalSplitInputData
    |>.toTerminalVariationInputData

/-- Table-routed high-excess data for the weighted-Kraft actual phases. -/
def toTableRoutedHighExcessData
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunWeightedKraftCNLRawN2StructuredInputs)
    (ctx : ActualFailureContext) :
    TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData
      (data.phases ctx) ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos where
  accounting := data.accounting ctx
  n24_input := data.n24Input ctx

/-- High-excess charge derived on the actual weighted-Kraft phases only. -/
def highExcessCharge
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunWeightedKraftCNLRawN2StructuredInputs)
    (ctx : ActualFailureContext) :
    HighExcessChargeData (data.phases ctx) ctx.n24CarryData :=
  tableRoutedSplitPhaseAccountedToHighExcessData
    (data.toTableRoutedHighExcessData ctx)

/-- Project the weighted-Kraft actual surface to the final actual-consumption
interface. -/
def toActualInputs
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunWeightedKraftCNLRawN2StructuredInputs) :
    GlobalAssemblyActualInputs where
  carryData := ActualFailureContext.n24CarryData
  chernoff := fun ctx => (data.phases ctx).chernoff
  cnl := fun ctx => (data.phases ctx).cnl
  densePack := fun ctx => (data.phases ctx).densePack
  tower := fun ctx => (data.phases ctx).tower
  returnPkg := fun ctx => (data.phases ctx).returnPkg
  run := fun ctx => (data.phases ctx).run
  highExcessCharge := fun ctx => data.highExcessCharge ctx

end GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunWeightedKraftCNLRawN2StructuredInputs

/-- Final bridge from root-bound Chernoff, direct weighted-Kraft CNL, split
Return/Run, raw N.2, and pinned-phase all-fields terminal data. -/
theorem erdos260_final_actual_rootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunWeightedKraftCNLRawN2Structured
    (data :
      GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunWeightedKraftCNLRawN2StructuredInputs) :
    Erdos260Statement :=
  erdos260_final_actual data.toActualInputs

/-- A nonempty provider for the direct weighted-Kraft pinned-phase surface proves
the final statement. -/
theorem erdos260_unconditional_from_rootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunWeightedKraftCNLRawN2Structured_provider
    (hprovider :
      Nonempty
        GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunWeightedKraftCNLRawN2StructuredInputs) :
    Erdos260Statement :=
  hprovider.elim
    erdos260_final_actual_rootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunWeightedKraftCNLRawN2Structured

/--
Current no-input actual provider target for the final theorem.

This is the manuscript-aligned actual-shell surface, not the older all-shell
certificate provider: Chernoff is at the root-bound shell-paid leaf, CNL is the
direct weighted-Kraft leaf, Return/Run are split manuscript leaves, N.2 is raw
first-crossing data, and N.3.3/L.6 is pinned to the actually assembled phase.
-/
abbrev GlobalAssemblyActualCurrentProviderTarget :=
  GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunWeightedKraftCNLRawN2StructuredInputs

/-- Project the current final actual provider target to the actual-consumption
assembly interface. -/
def globalAssemblyActual_from_current_provider
    (data : GlobalAssemblyActualCurrentProviderTarget) :
    GlobalAssemblyActualInputs :=
  data.toActualInputs

/-- Final bridge using the current actual provider target. -/
theorem erdos260_final_actual_currentProviderTarget
    (data : GlobalAssemblyActualCurrentProviderTarget) :
    Erdos260Statement :=
  erdos260_final_actual_rootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunWeightedKraftCNLRawN2Structured
    data

/-- A nonempty current actual provider target proves the final theorem. -/
theorem erdos260_unconditional_from_current_actual_provider
    (hprovider : Nonempty GlobalAssemblyActualCurrentProviderTarget) :
    Erdos260Statement :=
  hprovider.elim erdos260_final_actual_currentProviderTarget

/--
Direct numerator-smallness form of the actual finite-sum Chernoff leaf.

This is the same actual shell-paid 22.1A surface as
`ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData`, but with the
tail constant and dyadic exponent already eliminated.  It is often the cleaner
manuscript endpoint: prove the finite tilted root is at most the phase budget
times `X * z^Y`, while keeping the layer-cake area estimate explicit.
-/
structure ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData
    (ctx : ActualFailureContext) where
  Path : Type
  paths : Finset Path
  weight : Path -> {x : Real // 0 <= x}
  cost : Path -> Nat
  Y : Nat
  z : {z : Real // 1 <= z}
  root_small :
    ((paths.card : Real) *
        (paths.sum (fun p => (weight p : Real) * (z : Real) ^ cost p))) <=
      (erdos260Constants.cStar * erdos260Constants.ξ / 6) *
        (ctx.shell.X : Real) * (z : Real) ^ Y
  Ysh : Path -> Real
  hYsh : forall b, b ∈ paths -> 0 <= Ysh b
  area_small :
    (∑ b ∈ paths, (weight b : Real) * Ysh b) <=
      erdos260Constants.cStar * erdos260Constants.ξ *
        (ctx.shell.X : Real) / 6

namespace ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData

/-- Project the direct root-smallness Chernoff leaf to the current
root-bound/scalar-tail surface by choosing tail exponent zero. -/
def toRootBoundScalarTailFieldsData {ctx : ActualFailureContext}
    (data : ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData ctx) :
    ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx where
  Path := data.Path
  paths := data.paths
  weight := data.weight
  cost := data.cost
  Y := data.Y
  z := data.z
  tailConstant := erdos260Constants.cStar * erdos260Constants.ξ / 6
  tailExponent := 0
  root_bound := by
    simpa [mul_assoc] using data.root_small
  tail_small_scalar := by
    simp
  Ysh := data.Ysh
  hYsh := data.hYsh
  area_small := data.area_small

end ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData

/--
Root-small finite-sum Chernoff data with the proof-v4 tilt and canonical
height already fixed.

This keeps the shell-paid stopped subfamily explicit, but removes two choices
from the final provider: the tilt is `proofV4ChernoffTilt = 3 / 2` and the
height is `Nat.floor ctx.n24CarryLocal.Y`.
-/
structure ActualShellPaidChernoffFiniteSumFixedTiltCanonicalYRootSmallData
    (ctx : ActualFailureContext) where
  Path : Type
  paths : Finset Path
  weight : Path -> {x : Real // 0 <= x}
  cost : Path -> Nat
  root_small :
    ((paths.card : Real) *
        (paths.sum
          (fun p =>
            (weight p : Real) *
              (proofV4ChernoffTilt : Real) ^ cost p))) <=
      (erdos260Constants.cStar * erdos260Constants.ξ / 6) *
        (ctx.shell.X : Real) *
          (proofV4ChernoffTilt : Real) ^ Nat.floor ctx.n24CarryLocal.Y
  Ysh : Path -> Real
  hYsh : forall b, b ∈ paths -> 0 <= Ysh b
  area_small :
    (∑ b ∈ paths, (weight b : Real) * Ysh b) <=
      erdos260Constants.cStar * erdos260Constants.ξ *
        (ctx.shell.X : Real) / 6

namespace ActualShellPaidChernoffFiniteSumFixedTiltCanonicalYRootSmallData

/-- Forget the fixed proof-v4 `z = 3 / 2` and canonical-Y choices to recover
the current root-small Chernoff consumer surface. -/
def toRootSmallTailFieldsData {ctx : ActualFailureContext}
    (data :
      ActualShellPaidChernoffFiniteSumFixedTiltCanonicalYRootSmallData ctx) :
    ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData ctx where
  Path := data.Path
  paths := data.paths
  weight := data.weight
  cost := data.cost
  Y := Nat.floor ctx.n24CarryLocal.Y
  z := ⟨(proofV4ChernoffTilt : Real),
    le_of_lt proofV4ChernoffTilt.property.1⟩
  root_small := by
    simpa using data.root_small
  Ysh := data.Ysh
  hYsh := data.hYsh
  area_small := data.area_small

/-- The regular shell-paid Chernoff leaf induced by fixed-tilt canonical-Y
root-small data. -/
def toChernoffLeaf {ctx : ActualFailureContext}
    (data :
      ActualShellPaidChernoffFiniteSumFixedTiltCanonicalYRootSmallData ctx) :
    RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real) :=
  data.toRootSmallTailFieldsData.toRootBoundScalarTailFieldsData
    |>.toChernoffLeaf

end ActualShellPaidChernoffFiniteSumFixedTiltCanonicalYRootSmallData

/-- The actual closure phase assembled from the direct root-smallness Chernoff
variant and direct weighted-Kraft CNL data. -/
def actualClosurePhaseFromRootSmallWeightedKraftSplitRR
    (ctx : ActualFailureContext)
    (chernoff : ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData ctx)
    (cnl : ActualCNLWeightedKraftData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx) :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  actualClosurePhaseFromRootBoundWeightedKraftSplitRR ctx
    (ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData.toRootBoundScalarTailFieldsData
      chernoff)
    cnl returnPkg run

/-- Raw N.2 target induced by the direct root-smallness Chernoff variant. -/
abbrev ActualRootSmallChernoffRawN2Data
    (ctx : ActualFailureContext)
    (chernoff : ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData ctx)
    (cnl : ActualCNLWeightedKraftData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx) : Type 1 :=
  ActualRawN2FirstCrossingData ctx
    (termRun
      (actualClosurePhaseFromRootSmallWeightedKraftSplitRR ctx
        chernoff cnl returnPkg run))

/-- Pinned all-fields terminal target induced by the direct root-smallness
Chernoff variant and its raw N.2 field. -/
abbrev ActualRootSmallChernoffPinnedTerminalData
    (ctx : ActualFailureContext)
    (chernoff : ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData ctx)
    (cnl : ActualCNLWeightedKraftData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx)
    (n2 : ActualRootSmallChernoffRawN2Data ctx chernoff cnl returnPkg run) :
    Type 1 :=
  let chernoffRoot :=
    ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData.toRootBoundScalarTailFieldsData
      chernoff
  let phase :=
    actualClosurePhaseFromRootSmallWeightedKraftSplitRR ctx
      chernoff cnl returnPkg run
  ActualStructuredTerminalPinnedPhaseAllFieldsLowPaidData
    ctx
    (chernoffRoot.toChernoffLeaf)
    phase
    (n2.toVariationData)
    (termDensePack phase)
    (termChernoff phase)
    (termReturn phase)
    (termCnl phase)
    (termTower phase)

/--
Current final actual provider target with Chernoff supplied in direct
root-smallness form.

All other columns are exactly the current manuscript-aligned consumer surface:
direct weighted-Kraft CNL, split Return/Run, raw N.2, and the pinned
all-fields N.3.3/L.6 terminal package.
-/
structure GlobalAssemblyActualRootSmallChernoffCurrentProviderInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLWeightedKraftData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRootSmallChernoffRawN2Data ctx
      (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx)
  terminal : forall ctx : ActualFailureContext,
    ActualRootSmallChernoffPinnedTerminalData ctx
      (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx) (n2 ctx)

namespace GlobalAssemblyActualRootSmallChernoffCurrentProviderInputs

/-- Project the direct root-smallness provider target to the current final
actual provider target. -/
def toCurrentProviderTarget
    (data : GlobalAssemblyActualRootSmallChernoffCurrentProviderInputs) :
    GlobalAssemblyActualCurrentProviderTarget where
  chernoff := fun ctx =>
    ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData.toRootBoundScalarTailFieldsData
      (data.chernoff ctx)
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := fun ctx => by
    simpa [ActualRootSmallChernoffRawN2Data,
      actualClosurePhaseFromRootSmallWeightedKraftSplitRR]
      using data.n2 ctx
  terminal := fun ctx => by
    simpa [ActualRootSmallChernoffPinnedTerminalData,
      ActualRootSmallChernoffRawN2Data,
      actualClosurePhaseFromRootSmallWeightedKraftSplitRR]
      using data.terminal ctx

end GlobalAssemblyActualRootSmallChernoffCurrentProviderInputs

/-- Final bridge from the root-smallness Chernoff variant of the current
provider target. -/
theorem erdos260_final_actual_rootSmallChernoffCurrentProvider
    (data : GlobalAssemblyActualRootSmallChernoffCurrentProviderInputs) :
    Erdos260Statement :=
  erdos260_final_actual_currentProviderTarget
    (GlobalAssemblyActualRootSmallChernoffCurrentProviderInputs.toCurrentProviderTarget
      data)

/-- A nonempty root-smallness current provider target proves the final theorem. -/
theorem erdos260_unconditional_from_rootSmallChernoff_current_provider
    (hprovider :
      Nonempty GlobalAssemblyActualRootSmallChernoffCurrentProviderInputs) :
    Erdos260Statement :=
  hprovider.elim erdos260_final_actual_rootSmallChernoffCurrentProvider

/-- The actual closure phase assembled from direct root-smallness Chernoff data
and the lower code/fibre Nat-budget CNL surface. -/
def actualClosurePhaseFromRootSmallCodeFibreSplitRR
    (ctx : ActualFailureContext)
    (chernoff : ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData ctx)
    (cnl : ActualCNLCodeFibreNatBudgetData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx) :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  actualClosurePhaseFromRootBoundCodeFibreSplitRR ctx
    (ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData.toRootBoundScalarTailFieldsData
      chernoff)
    cnl returnPkg run

/-- Raw N.2 target induced by root-small Chernoff and code/fibre CNL data. -/
abbrev ActualRootSmallChernoffCodeFibreRawN2Data
    (ctx : ActualFailureContext)
    (chernoff : ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData ctx)
    (cnl : ActualCNLCodeFibreNatBudgetData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx) : Type 1 :=
  ActualRawN2FirstCrossingData ctx
    (termRun
      (actualClosurePhaseFromRootSmallCodeFibreSplitRR ctx
        chernoff cnl returnPkg run))

/-- Pinned all-fields terminal target induced by root-small Chernoff and
code/fibre CNL data. -/
abbrev ActualRootSmallChernoffCodeFibrePinnedTerminalData
    (ctx : ActualFailureContext)
    (chernoff : ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData ctx)
    (cnl : ActualCNLCodeFibreNatBudgetData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx)
    (n2 :
      ActualRootSmallChernoffCodeFibreRawN2Data ctx chernoff cnl returnPkg
        run) :
    Type 1 :=
  let chernoffRoot :=
    ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData.toRootBoundScalarTailFieldsData
      chernoff
  let phase :=
    actualClosurePhaseFromRootSmallCodeFibreSplitRR ctx
      chernoff cnl returnPkg run
  ActualStructuredTerminalPinnedPhaseAllFieldsLowPaidData
    ctx
    (chernoffRoot.toChernoffLeaf)
    phase
    (n2.toVariationData)
    (termDensePack phase)
    (termChernoff phase)
    (termReturn phase)
    (termCnl phase)
    (termTower phase)

/--
Root-small Chernoff current provider with CNL exposed at the direct
code/fibre Nat-budget boundary.

This keeps the same actual pinned phase, Return/Run split scalar fields, raw
N.2, and structured N.3.3/L.6 terminal package as the current provider, while
requiring the CNL data in the lower L.1.2/G.35 code/fibre form.
-/
structure GlobalAssemblyActualRootSmallChernoffCodeFibreCNLCurrentProviderInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLCodeFibreNatBudgetData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRootSmallChernoffCodeFibreRawN2Data ctx
      (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx)
  terminal : forall ctx : ActualFailureContext,
    ActualRootSmallChernoffCodeFibrePinnedTerminalData ctx
      (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx) (n2 ctx)

namespace GlobalAssemblyActualRootSmallChernoffCodeFibreCNLCurrentProviderInputs

/-- Project the root-small/code-fibre provider target to the existing
root-bound/code-fibre pinned-phase surface. -/
def toRootBoundCodeFibrePinnedPhaseInputs
    (data :
      GlobalAssemblyActualRootSmallChernoffCodeFibreCNLCurrentProviderInputs) :
    GlobalAssemblyActualRootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunCodeFibreCNLRawN2StructuredInputs where
  chernoff := fun ctx =>
    ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData.toRootBoundScalarTailFieldsData
      (data.chernoff ctx)
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := fun ctx => by
    simpa [ActualRootSmallChernoffCodeFibreRawN2Data,
      actualClosurePhaseFromRootSmallCodeFibreSplitRR]
      using data.n2 ctx
  terminal := fun ctx => by
    simpa [ActualRootSmallChernoffCodeFibrePinnedTerminalData,
      ActualRootSmallChernoffCodeFibreRawN2Data,
      actualClosurePhaseFromRootSmallCodeFibreSplitRR]
      using data.terminal ctx

end GlobalAssemblyActualRootSmallChernoffCodeFibreCNLCurrentProviderInputs

/-- Final bridge from root-small Chernoff and code/fibre CNL current provider
data. -/
theorem erdos260_final_actual_rootSmallChernoffCodeFibreCNLCurrentProvider
    (data :
      GlobalAssemblyActualRootSmallChernoffCodeFibreCNLCurrentProviderInputs) :
    Erdos260Statement :=
  erdos260_final_actual_rootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunCodeFibreCNLRawN2Structured
    data.toRootBoundCodeFibrePinnedPhaseInputs

/-- A nonempty root-small/code-fibre current provider target proves the final
statement. -/
theorem erdos260_unconditional_from_rootSmallChernoff_codeFibreCNL_current_provider
    (hprovider :
      Nonempty
        GlobalAssemblyActualRootSmallChernoffCodeFibreCNLCurrentProviderInputs) :
    Erdos260Statement :=
  hprovider.elim
    erdos260_final_actual_rootSmallChernoffCodeFibreCNLCurrentProvider

/--
Root-small Chernoff current provider with CNL exposed at the classical
code/fibre Nat-budget boundary.

Compared with `GlobalAssemblyActualRootSmallChernoffCodeFibreCNLCurrentProviderInputs`,
this removes the explicit `DecidableEq Code` field from the provider data and
chooses it internally by `Classical.decEq`.
-/
structure GlobalAssemblyActualRootSmallChernoffClassicalCodeFibreCNLCurrentProviderInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLClassicalCodeFibreNatBudgetData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualRootSmallChernoffCodeFibreRawN2Data ctx
      (chernoff ctx) ((cnl ctx).toCodeFibreNatBudgetData)
      (returnPkg ctx) (run ctx)
  terminal : forall ctx : ActualFailureContext,
    ActualRootSmallChernoffCodeFibrePinnedTerminalData ctx
      (chernoff ctx) ((cnl ctx).toCodeFibreNatBudgetData)
      (returnPkg ctx) (run ctx) (n2 ctx)

namespace GlobalAssemblyActualRootSmallChernoffClassicalCodeFibreCNLCurrentProviderInputs

/-- Project the classical-code CNL current target to the explicit code/fibre
CNL current target. -/
def toCodeFibreCNLCurrentProviderInputs
    (data :
      GlobalAssemblyActualRootSmallChernoffClassicalCodeFibreCNLCurrentProviderInputs) :
    GlobalAssemblyActualRootSmallChernoffCodeFibreCNLCurrentProviderInputs where
  chernoff := data.chernoff
  cnl := fun ctx => (data.cnl ctx).toCodeFibreNatBudgetData
  returnPkg := data.returnPkg
  run := data.run
  n2 := data.n2
  terminal := data.terminal

end GlobalAssemblyActualRootSmallChernoffClassicalCodeFibreCNLCurrentProviderInputs

/-- Final bridge from root-small Chernoff and classical code/fibre CNL current
provider data. -/
theorem erdos260_final_actual_rootSmallChernoffClassicalCodeFibreCNLCurrentProvider
    (data :
      GlobalAssemblyActualRootSmallChernoffClassicalCodeFibreCNLCurrentProviderInputs) :
    Erdos260Statement :=
  erdos260_final_actual_rootSmallChernoffCodeFibreCNLCurrentProvider
    data.toCodeFibreCNLCurrentProviderInputs

/-- A nonempty root-small/classical-code-fibre current provider target proves
the final statement. -/
theorem erdos260_unconditional_from_rootSmallChernoff_classicalCodeFibreCNL_current_provider
    (hprovider :
      Nonempty
        GlobalAssemblyActualRootSmallChernoffClassicalCodeFibreCNLCurrentProviderInputs) :
    Erdos260Statement :=
  hprovider.elim
    erdos260_final_actual_rootSmallChernoffClassicalCodeFibreCNLCurrentProvider

/--
Actual raw N.24 package for the current preferred route.

It keeps the proof-v4 N.2 first-crossing object and the pinned N.3.3/L.6
terminal low-paid object together, so the final provider consumes one
Appendix N.24 datum rather than two separately threaded fields.
-/
structure ActualRootSmallChernoffClassicalCodeFibreRawN24Data
    (ctx : ActualFailureContext)
    (chernoff : ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData ctx)
    (cnl : ActualCNLClassicalCodeFibreNatBudgetData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx) where
  n2 : ActualRootSmallChernoffCodeFibreRawN2Data ctx
    chernoff cnl.toCodeFibreNatBudgetData returnPkg run
  terminal : ActualRootSmallChernoffCodeFibrePinnedTerminalData ctx
    chernoff cnl.toCodeFibreNatBudgetData returnPkg run n2

/-- The actual closure phase assembled from the preferred fixed-tilt Chernoff
and classical code/fibre CNL surfaces. -/
def actualClosurePhaseFromFixedTiltClassicalCodeFibreSplitRR
    (ctx : ActualFailureContext)
    (chernoff :
      ActualShellPaidChernoffFiniteSumFixedTiltCanonicalYRootSmallData ctx)
    (cnl : ActualCNLClassicalCodeFibreNatBudgetData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx) :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  actualClosurePhaseFromRootSmallCodeFibreSplitRR ctx
    chernoff.toRootSmallTailFieldsData cnl.toCodeFibreNatBudgetData
    returnPkg run

/-- Raw N.2 target induced by the preferred fixed-tilt Chernoff and classical
code/fibre CNL surfaces. -/
abbrev ActualFixedTiltChernoffClassicalCodeFibreRawN2Data
    (ctx : ActualFailureContext)
    (chernoff :
      ActualShellPaidChernoffFiniteSumFixedTiltCanonicalYRootSmallData ctx)
    (cnl : ActualCNLClassicalCodeFibreNatBudgetData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx) : Type 1 :=
  ActualRootSmallChernoffCodeFibreRawN2Data ctx
    chernoff.toRootSmallTailFieldsData cnl.toCodeFibreNatBudgetData
    returnPkg run

/-- Pinned terminal target induced by the preferred fixed-tilt Chernoff and
classical code/fibre CNL surfaces. -/
abbrev ActualFixedTiltChernoffClassicalCodeFibrePinnedTerminalData
    (ctx : ActualFailureContext)
    (chernoff :
      ActualShellPaidChernoffFiniteSumFixedTiltCanonicalYRootSmallData ctx)
    (cnl : ActualCNLClassicalCodeFibreNatBudgetData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx)
    (n2 :
      ActualFixedTiltChernoffClassicalCodeFibreRawN2Data ctx chernoff cnl
        returnPkg run) : Type 1 :=
  ActualRootSmallChernoffCodeFibrePinnedTerminalData ctx
    chernoff.toRootSmallTailFieldsData cnl.toCodeFibreNatBudgetData
    returnPkg run n2

/-- All-fields terminal target induced by the preferred fixed-tilt Chernoff and
classical code/fibre CNL surfaces, before the dense/progress/endpoint routes
are pinned to the actual phase. -/
abbrev ActualFixedTiltChernoffClassicalCodeFibreAllFieldsTerminalData
    (ctx : ActualFailureContext)
    (chernoff :
      ActualShellPaidChernoffFiniteSumFixedTiltCanonicalYRootSmallData ctx)
    (cnl : ActualCNLClassicalCodeFibreNatBudgetData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx)
    (n2 :
      ActualFixedTiltChernoffClassicalCodeFibreRawN2Data ctx chernoff cnl
        returnPkg run) : Type 1 :=
  let chernoffRoot :=
    ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData.toRootBoundScalarTailFieldsData
      chernoff.toRootSmallTailFieldsData
  let phase :=
    actualClosurePhaseFromFixedTiltClassicalCodeFibreSplitRR ctx
      chernoff cnl returnPkg run
  ActualStructuredTerminalAllFieldsLowPaidData
    ctx
    (chernoffRoot.toChernoffLeaf)
    (n2.toVariationData)
    (termDensePack phase)
    (termChernoff phase)
    (termReturn phase)
    (termCnl phase)
    (termTower phase)

/-- Fixed-tilt/classical-code-fibre terminal data whose three phase-sensitive
routes are already tied to the actual closure phase.

This is still the all-fields terminal package, but with the phase fixed in the
type rather than carried later by three equality proofs.
-/
abbrev ActualFixedTiltChernoffClassicalCodeFibreActualPhaseAllFieldsTerminalData
    (ctx : ActualFailureContext)
    (chernoff :
      ActualShellPaidChernoffFiniteSumFixedTiltCanonicalYRootSmallData ctx)
    (cnl : ActualCNLClassicalCodeFibreNatBudgetData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx)
    (n2 :
      ActualFixedTiltChernoffClassicalCodeFibreRawN2Data ctx chernoff cnl
        returnPkg run) : Type 1 :=
  let chernoffRoot :=
    ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData.toRootBoundScalarTailFieldsData
      chernoff.toRootSmallTailFieldsData
  let phase :=
    actualClosurePhaseFromFixedTiltClassicalCodeFibreSplitRR ctx
      chernoff cnl returnPkg run
  ActualStructuredTerminalPinnedPhaseAllFieldsLowPaidData
    ctx
    (chernoffRoot.toChernoffLeaf)
    phase
    (n2.toVariationData)
    (termDensePack phase)
    (termChernoff phase)
    (termReturn phase)
    (termCnl phase)
    (termTower phase)

/-- Re-expose actual-phase terminal data at the current all-fields terminal
surface.  The resulting `densePhase`, `progressPhase`, and `endpointPhase`
fields are the actual closure phase by construction. -/
def ActualFixedTiltChernoffClassicalCodeFibreActualPhaseAllFieldsTerminalData.toAllFieldsTerminalData
    {ctx : ActualFailureContext}
    {chernoff :
      ActualShellPaidChernoffFiniteSumFixedTiltCanonicalYRootSmallData ctx}
    {cnl : ActualCNLClassicalCodeFibreNatBudgetData ctx}
    {returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx}
    {run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx}
    {n2 :
      ActualFixedTiltChernoffClassicalCodeFibreRawN2Data ctx chernoff cnl
        returnPkg run}
    (data :
      ActualFixedTiltChernoffClassicalCodeFibreActualPhaseAllFieldsTerminalData
        ctx chernoff cnl returnPkg run n2) :
    ActualFixedTiltChernoffClassicalCodeFibreAllFieldsTerminalData
      ctx chernoff cnl returnPkg run n2 := by
  simpa [ActualFixedTiltChernoffClassicalCodeFibreActualPhaseAllFieldsTerminalData,
    ActualFixedTiltChernoffClassicalCodeFibreAllFieldsTerminalData,
    actualClosurePhaseFromFixedTiltClassicalCodeFibreSplitRR] using
    data.toAllFieldsLowPaidData cnl.toWeightedKraftShellInputData

/-- Pin fixed-tilt/classical-code-fibre all-fields terminal data to the actual
phase once the three phase-sensitive terminal routes are identified with it. -/
def ActualFixedTiltChernoffClassicalCodeFibreAllFieldsTerminalData.toPinnedTerminalData
    {ctx : ActualFailureContext}
    {chernoff :
      ActualShellPaidChernoffFiniteSumFixedTiltCanonicalYRootSmallData ctx}
    {cnl : ActualCNLClassicalCodeFibreNatBudgetData ctx}
    {returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx}
    {run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx}
    {n2 :
      ActualFixedTiltChernoffClassicalCodeFibreRawN2Data ctx chernoff cnl
        returnPkg run}
    (data :
      ActualFixedTiltChernoffClassicalCodeFibreAllFieldsTerminalData ctx
        chernoff cnl returnPkg run n2)
    (hdense :
      data.densePhase =
        actualClosurePhaseFromFixedTiltClassicalCodeFibreSplitRR ctx
          chernoff cnl returnPkg run)
    (hprogress :
      data.progressPhase =
        actualClosurePhaseFromFixedTiltClassicalCodeFibreSplitRR ctx
          chernoff cnl returnPkg run)
    (hendpoint :
      data.endpointPhase =
        actualClosurePhaseFromFixedTiltClassicalCodeFibreSplitRR ctx
          chernoff cnl returnPkg run) :
    ActualFixedTiltChernoffClassicalCodeFibrePinnedTerminalData ctx
      chernoff cnl returnPkg run n2 := by
  simpa [ActualFixedTiltChernoffClassicalCodeFibrePinnedTerminalData,
    ActualFixedTiltChernoffClassicalCodeFibreAllFieldsTerminalData,
    ActualRootSmallChernoffCodeFibrePinnedTerminalData,
    actualClosurePhaseFromFixedTiltClassicalCodeFibreSplitRR,
    actualClosurePhaseFromRootSmallCodeFibreSplitRR] using
    data.toPinnedPhaseAllFieldsLowPaidData hdense hprogress hendpoint

/-- Raw N.24 package specialized to the fixed-tilt canonical-Y Chernoff
surface used by the preferred target. -/
structure ActualFixedTiltChernoffClassicalCodeFibreRawN24Data
    (ctx : ActualFailureContext)
    (chernoff :
      ActualShellPaidChernoffFiniteSumFixedTiltCanonicalYRootSmallData ctx)
    (cnl : ActualCNLClassicalCodeFibreNatBudgetData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx) where
  n2 :
    ActualFixedTiltChernoffClassicalCodeFibreRawN2Data ctx chernoff cnl
      returnPkg run
  terminal :
    ActualFixedTiltChernoffClassicalCodeFibrePinnedTerminalData ctx
      chernoff cnl returnPkg run n2

namespace ActualFixedTiltChernoffClassicalCodeFibreRawN24Data

/-- Project the fixed-tilt raw N.24 package to the previous root-small
raw-N.24 package. -/
def toRootSmallRawN24Data
    {ctx : ActualFailureContext}
    {chernoff :
      ActualShellPaidChernoffFiniteSumFixedTiltCanonicalYRootSmallData ctx}
    {cnl : ActualCNLClassicalCodeFibreNatBudgetData ctx}
    {returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx}
    {run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx}
    (data :
      ActualFixedTiltChernoffClassicalCodeFibreRawN24Data ctx chernoff cnl
        returnPkg run) :
    ActualRootSmallChernoffClassicalCodeFibreRawN24Data ctx
      chernoff.toRootSmallTailFieldsData cnl returnPkg run where
  n2 := data.n2
  terminal := data.terminal

end ActualFixedTiltChernoffClassicalCodeFibreRawN24Data

/-- Preferred current provider with Appendix N.24 exposed as one raw package. -/
structure GlobalAssemblyActualRootSmallChernoffClassicalCodeFibreCNLRawN24ProviderInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLClassicalCodeFibreNatBudgetData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n24 : forall ctx : ActualFailureContext,
    ActualRootSmallChernoffClassicalCodeFibreRawN24Data ctx
      (chernoff ctx) (cnl ctx) (returnPkg ctx) (run ctx)

namespace GlobalAssemblyActualRootSmallChernoffClassicalCodeFibreCNLRawN24ProviderInputs

/-- Project the raw-N.24 preferred target to the previous split N.2/terminal
current target. -/
def toClassicalCodeFibreCNLCurrentProviderInputs
    (data :
      GlobalAssemblyActualRootSmallChernoffClassicalCodeFibreCNLRawN24ProviderInputs) :
    GlobalAssemblyActualRootSmallChernoffClassicalCodeFibreCNLCurrentProviderInputs where
  chernoff := data.chernoff
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n2 := fun ctx => (data.n24 ctx).n2
  terminal := fun ctx => (data.n24 ctx).terminal

end GlobalAssemblyActualRootSmallChernoffClassicalCodeFibreCNLRawN24ProviderInputs

/-- Final bridge from the raw-N.24 preferred provider target. -/
theorem erdos260_final_actual_rootSmallChernoffClassicalCodeFibreCNLRawN24Provider
    (data :
      GlobalAssemblyActualRootSmallChernoffClassicalCodeFibreCNLRawN24ProviderInputs) :
    Erdos260Statement :=
  erdos260_final_actual_rootSmallChernoffClassicalCodeFibreCNLCurrentProvider
    data.toClassicalCodeFibreCNLCurrentProviderInputs

/-- A nonempty root-small/classical-code-fibre/raw-N.24 provider target proves
the final statement. -/
theorem erdos260_unconditional_from_rootSmallChernoff_classicalCodeFibreCNL_rawN24_provider
    (hprovider :
      Nonempty
        GlobalAssemblyActualRootSmallChernoffClassicalCodeFibreCNLRawN24ProviderInputs) :
    Erdos260Statement :=
  hprovider.elim
    erdos260_final_actual_rootSmallChernoffClassicalCodeFibreCNLRawN24Provider

/--
Preferred current provider with the Chernoff column fixed to the proof-v4
tilt `3 / 2` and canonical height `Nat.floor ctx.n24CarryLocal.Y`.

The other four columns remain the current manuscript-aligned actual surfaces:
classical code/fibre CNL, split Return, split Run, and the bundled raw N.24
package.
-/
structure GlobalAssemblyActualFixedTiltChernoffClassicalCodeFibreCNLRawN24ProviderInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumFixedTiltCanonicalYRootSmallData ctx
  cnl : forall ctx : ActualFailureContext,
    ActualCNLClassicalCodeFibreNatBudgetData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n24 : forall ctx : ActualFailureContext,
    ActualFixedTiltChernoffClassicalCodeFibreRawN24Data ctx
      (chernoff ctx)
      (cnl ctx) (returnPkg ctx) (run ctx)

namespace GlobalAssemblyActualFixedTiltChernoffClassicalCodeFibreCNLRawN24ProviderInputs

/-- Project the fixed-tilt canonical-Y Chernoff preferred target to the previous
root-small Chernoff raw-N.24 target. -/
def toRootSmallRawN24ProviderInputs
    (data :
      GlobalAssemblyActualFixedTiltChernoffClassicalCodeFibreCNLRawN24ProviderInputs) :
    GlobalAssemblyActualRootSmallChernoffClassicalCodeFibreCNLRawN24ProviderInputs where
  chernoff := fun ctx => (data.chernoff ctx).toRootSmallTailFieldsData
  cnl := data.cnl
  returnPkg := data.returnPkg
  run := data.run
  n24 := fun ctx => (data.n24 ctx).toRootSmallRawN24Data

end GlobalAssemblyActualFixedTiltChernoffClassicalCodeFibreCNLRawN24ProviderInputs

/-- Final bridge from the fixed-tilt canonical-Y preferred provider target. -/
theorem erdos260_final_actual_fixedTiltChernoffClassicalCodeFibreCNLRawN24Provider
    (data :
      GlobalAssemblyActualFixedTiltChernoffClassicalCodeFibreCNLRawN24ProviderInputs) :
    Erdos260Statement :=
  erdos260_final_actual_rootSmallChernoffClassicalCodeFibreCNLRawN24Provider
    data.toRootSmallRawN24ProviderInputs

/-- A nonempty fixed-tilt/classical-code-fibre/raw-N.24 provider target proves
the final statement. -/
theorem erdos260_unconditional_from_fixedTiltChernoff_classicalCodeFibreCNL_rawN24_provider
    (hprovider :
      Nonempty
        GlobalAssemblyActualFixedTiltChernoffClassicalCodeFibreCNLRawN24ProviderInputs) :
    Erdos260Statement :=
  hprovider.elim
    erdos260_final_actual_fixedTiltChernoffClassicalCodeFibreCNLRawN24Provider

/-- Stable name for the currently preferred no-input target.

The target can be lowered further as more manuscript objects are exposed; the
bridge theorems below are the names used by the audit layer. -/
abbrev GlobalAssemblyActualPreferredProviderTarget :=
  GlobalAssemblyActualFixedTiltChernoffClassicalCodeFibreCNLRawN24ProviderInputs

/-- Final bridge through the stable preferred-provider target. -/
theorem erdos260_final_actual_preferredProviderTarget
    (data : GlobalAssemblyActualPreferredProviderTarget) :
    Erdos260Statement :=
  erdos260_final_actual_fixedTiltChernoffClassicalCodeFibreCNLRawN24Provider
    data

/-- A nonempty preferred actual-provider target proves the final statement. -/
theorem erdos260_unconditional_from_preferred_actual_provider
    (hprovider : Nonempty GlobalAssemblyActualPreferredProviderTarget) :
    Erdos260Statement :=
  hprovider.elim erdos260_final_actual_preferredProviderTarget

/-- Structured audit row for one field of the current actual-shell provider
target. -/
structure Erdos260CurrentActualProviderFieldAudit where
  slot : String
  target : String
  connectedProjection : String
  sourceModule : String
  remainingData : String
  openItems : List String

/-- The six real manuscript data columns still needed for the current
actual-shell no-input target.  These rows are aligned with the fields of
`GlobalAssemblyActualCurrentProviderTarget`. -/
def erdos260CurrentActualProviderFieldAudits :
    List Erdos260CurrentActualProviderFieldAudit :=
  [ { slot := "Chernoff"
      target :=
        "forall ctx, ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx"
      connectedProjection :=
        "ActualShellPaidChernoffFiniteSumRootSmallTailFieldsData.toRootBoundScalarTailFieldsData"
      sourceModule := "ShellPaidChernoffConstruction"
      remainingData :=
        "stopped shell-paid family, nonnegative multipliers, root-small finite-sum tail estimate, layer-cake area smallness, and L.6.2 paid-output embedding"
      openItems := shellPaidChernoff22_1AOpenItems },
    { slot := "CNL"
      target := "forall ctx, ActualCNLWeightedKraftData ctx"
      connectedProjection :=
        "ActualCNLWeightedKraftData.toWeightedKraftShellInputData"
      sourceModule := "CNLSelectedTransitionConstruction"
      remainingData :=
        "surviving selected transitions, Nat BND heights, weighted Kraft bound, and G.35 scalar shell/interval budget"
      openItems := cnlStandardWeightedKraftShellOpenItems },
    { slot := "Return"
      target := "forall ctx, ActualReturnRawI51M2J4L6SplitScalarData ctx"
      connectedProjection :=
        "ActualReturnRawI51M2J4L6SplitScalarData.toScalarData.toRawData.toPackageInputData"
      sourceModule := "ReturnLocalLeafConstruction"
      remainingData :=
        "ordinary-short, semiperiodic, OLC multiplicity, nonlocal-long, and final scalar smallness certificates"
      openItems := returnSeparatedLocalLeafOpenItems },
    { slot := "Run"
      target := "forall ctx, ActualRunRawL41L42I52SplitAbsorptionScalarData ctx"
      connectedProjection :=
        "ActualRunRawL41L42I52SplitAbsorptionScalarData.toScalarData.toRawData.toPackageInputData"
      sourceModule := "RunLocalLeafConstruction"
      remainingData :=
        "L.4.1/L.4.2/I.5.2 trichotomy absorption, half-decrease chain, and scalar smallness certificates"
      openItems := runSeparatedLocalLeafOpenItems },
    { slot := "Appendix N.2"
      target :=
        "forall ctx, ActualRawN2FirstCrossingData ctx (termRun (actual phase ctx))"
      connectedProjection :=
        "ActualRawN2FirstCrossingData.toVariationData / AppendixNVariationClosedN21N22InputData.ofRawShellQFirstCrossingRecordDensityFields"
      sourceModule := "AppendixNVariationLeafConstruction"
      remainingData :=
        "actual shell-Q first-crossing branches, ordered records, injectivity, drop-density integrability, and rolling-window bound"
      openItems := appendixNVariationLeafOpenItems },
    { slot := "Appendix N.3.3/L.6"
      target :=
        "forall ctx, ActualStructuredTerminalPinnedPhaseAllFieldsLowPaidData ctx ..."
      connectedProjection :=
        "ActualStructuredTerminalPinnedPhaseAllFieldsLowPaidData.toStructuredTerminalLowPaidData / toBddL6Data"
      sourceModule := "AppendixNTerminalLeafConstruction"
      remainingData :=
        "same-threshold terminal events, grouped terminal compression, four non-bounded class routes, and L.6 low/paid bounded-class split"
      openItems := classicalTerminalN33SeparatedLeafOpenItems } ]

theorem erdos260CurrentActualProviderFieldAudits_length :
    erdos260CurrentActualProviderFieldAudits.length = 6 := by
  rfl

/-- The six real manuscript data columns still needed for the current
actual-shell no-input target, exposed as short labels for compact reports. -/
def erdos260CurrentActualProviderFields : List String :=
  erdos260CurrentActualProviderFieldAudits.map
    (fun row => row.slot ++ ": " ++ row.target)

theorem erdos260CurrentActualProviderFields_length :
    erdos260CurrentActualProviderFields.length = 6 := by
  simp [erdos260CurrentActualProviderFields,
    erdos260CurrentActualProviderFieldAudits_length]

/-- The final no-input theorem is deliberately left open until the current
actual provider target is inhabited by real manuscript data. -/
def erdos260CurrentActualNoInputOpenItems : List String :=
  [ "construct a non-synthetic value of GlobalAssemblyActualCurrentProviderTarget, or any stronger provider target that projects to it",
    "define erdos260_unconditional by applying erdos260_final_actual_currentProviderTarget to that value",
    "verify #print axioms erdos260_unconditional has only propext, Classical.choice, and Quot.sound" ]

theorem erdos260CurrentActualNoInputOpenItems_nonempty :
    erdos260CurrentActualNoInputOpenItems = [] -> False := by
  intro h
  simp [erdos260CurrentActualNoInputOpenItems] at h

/-- The actual phase package assembled from the proof-v4 leaf-level objects
that are present in the Appendix N audit surface. -/
def actualProofV4LeafPhases
    (ctx : ActualFailureContext)
    (chernoff :
      RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    (cnl :
      CNLStandardWeightedKraftShellInputData ctx.shell
        erdos260Constants.cStar erdos260Constants.ξ)
    (densePack :
      GroundedDensePackLocalData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    (dirtyMultiplicity : DirtyMultiplicityData)
    (tower :
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    (returnPkg :
      ReturnSeparatedLocalLeafInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real))
    (run :
      RunSeparatedLocalLeafInputData erdos260Constants.cStar
        erdos260Constants.ξ (ctx.shell.X : Real)) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  ((GroundedPreTRTSixPhaseLocalData.ofClosedLocalGeometry
      chernoff.toGroundedChernoffLocalData
      cnl.toGroundedCNLLocalData
      densePack
      dirtyMultiplicity).withTRT
    (GroundedTRTLocalPackageInputData.ofClosedTowerReturnRun
      tower.toGroundedTowerLocalData
      returnPkg.toGroundedReturnLocalData
      run.toGroundedRunLocalData)).toSixPhaseFactoryData

/--
Actual proof-v4 leaf surface matching the current Appendix N audit provider.

This is deliberately weaker than the newest raw support-map terminal surface:
it consumes exactly the leaf packages the audit provider already exposes, plus
the high-excess bridge for the phase package assembled from those leaves.
-/
structure GlobalAssemblyActualProofV4LeafInputs where
  chernoff : forall ctx : ActualFailureContext,
    RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real)
  cnl : forall ctx : ActualFailureContext,
    CNLStandardWeightedKraftShellInputData ctx.shell erdos260Constants.cStar
      erdos260Constants.ξ
  densePack : forall ctx : ActualFailureContext,
    GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real)
  dirtyMultiplicity : forall _ctx : ActualFailureContext,
    DirtyMultiplicityData
  tower : forall ctx : ActualFailureContext,
    TowerSeparatedLocalLeafInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real)
  returnPkg : forall ctx : ActualFailureContext,
    ReturnSeparatedLocalLeafInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real)
  run : forall ctx : ActualFailureContext,
    RunSeparatedLocalLeafInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real)
  carryData : forall ctx : ActualFailureContext,
    CarryDataFromFailure ctx.shell erdos260Constants.cPr
  highExcessCharge : forall ctx : ActualFailureContext,
    HighExcessChargeData
      (actualProofV4LeafPhases ctx
        (chernoff ctx) (cnl ctx) (densePack ctx) (dirtyMultiplicity ctx)
        (tower ctx) (returnPkg ctx) (run ctx))
      (carryData ctx)

namespace GlobalAssemblyActualProofV4LeafInputs

/-- Rebuild the exact actual phase consumed by the proof-v4 leaf surface. -/
def phases (data : GlobalAssemblyActualProofV4LeafInputs)
    (ctx : ActualFailureContext) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  actualProofV4LeafPhases ctx (data.chernoff ctx) (data.cnl ctx)
    (data.densePack ctx) (data.dirtyMultiplicity ctx) (data.tower ctx)
    (data.returnPkg ctx) (data.run ctx)

/-- Project the proof-v4 leaf actual surface to the final actual-consumption
interface. -/
def toActualInputs (data : GlobalAssemblyActualProofV4LeafInputs) :
    GlobalAssemblyActualInputs where
  carryData := data.carryData
  chernoff := fun ctx => (data.phases ctx).chernoff
  cnl := fun ctx => (data.phases ctx).cnl
  densePack := fun ctx => (data.phases ctx).densePack
  tower := fun ctx => (data.phases ctx).tower
  returnPkg := fun ctx => (data.phases ctx).returnPkg
  run := fun ctx => (data.phases ctx).run
  highExcessCharge := data.highExcessCharge

end GlobalAssemblyActualProofV4LeafInputs

/-- Final bridge from the exact proof-v4 actual leaf surface. -/
theorem erdos260_final_actual_proofV4_leaf
    (data : GlobalAssemblyActualProofV4LeafInputs) :
    Erdos260Statement :=
  erdos260_final_actual data.toActualInputs

/--
Short name for the strongest existing proof-v4 separated Appendix N leaf
surface.  This is the manuscript-shaped provider boundary currently audited in
`GlobalAppendixNChainCompressionCertificate`.
-/
abbrev AppendixNActualProofV4LeafInputs :=
  GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTerminalSeparatedTRTLocalLeafVariationKMN2N3Inputs

namespace AppendixNActualProofV4LeafInputs

/-- The actual shell is pinned to the manuscript constants. -/
def actualPin (_data : AppendixNActualProofV4LeafInputs)
    (ctx : ActualFailureContext) :
    PinnedManuscriptShell ctx.shell := { hcQ := rfl, hc0 := rfl }

/-- Canonical-Y Appendix N chain package for the actual failing shell. -/
def actualChain (data : AppendixNActualProofV4LeafInputs)
    (ctx : ActualFailureContext) :=
  data.canonicalYChainCompressionAt ctx.shell (data.actualPin ctx)
    ctx.shell_startThreshold_le

/-- The exact six-phase package assembled by the proof-v4 Appendix N leaves. -/
def actualPhases (data : AppendixNActualProofV4LeafInputs)
    (ctx : ActualFailureContext) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) :=
  (data.actualChain ctx).phases.toSixPhaseFactoryData

/-- The carry datum paired with the actual Appendix N chain package. -/
def actualCarryData (data : AppendixNActualProofV4LeafInputs)
    (ctx : ActualFailureContext) :
    CarryDataFromFailure ctx.shell erdos260Constants.cPr :=
  (appendixNGapCanonicalYCarryLocalAt ctx.shell ctx.shell_startThreshold_le).toCarryData
    erdos260Constants_cPr_le_half
    (data.actualPin ctx).hc0Small
    (supportCount_pos_of_appendixNChainCompressionStartThreshold_le
      ctx.shell_startThreshold_le)

/-- The actual high-excess charge bridge derived from the Appendix N package. -/
def actualHighExcessCharge (data : AppendixNActualProofV4LeafInputs)
    (ctx : ActualFailureContext) :
    HighExcessChargeData (data.actualPhases ctx) (data.actualCarryData ctx) :=
  tableRoutedSplitPhaseAccountedToHighExcessData
    ((data.actualChain ctx).toTableRoutedHighExcessData)

/-- The proof-v4 shell-paid Chernoff leaf at the actual failing shell. -/
def actualChernoffLeaf (data : AppendixNActualProofV4LeafInputs)
    (ctx : ActualFailureContext) :
    RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real) :=
  data.chernoff ctx.shell (data.actualPin ctx).hc0Small
    ctx.shell_startThreshold_le

/-- The proof-v4 CNL weighted-Kraft leaf at the actual failing shell. -/
def actualCNLWeightedKraft (data : AppendixNActualProofV4LeafInputs)
    (ctx : ActualFailureContext) :
    CNLStandardWeightedKraftShellInputData ctx.shell
      erdos260Constants.cStar erdos260Constants.ξ :=
  data.cnl ctx.shell (data.actualPin ctx).hc0Small
    ctx.shell_startThreshold_le

/-- The grounded CNL local package induced by the proof-v4 weighted-Kraft leaf. -/
def actualCNLGrounded (data : AppendixNActualProofV4LeafInputs)
    (ctx : ActualFailureContext) :
    GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  (data.actualCNLWeightedKraft ctx).toGroundedCNLLocalData

/-- The CNL factory package induced by the proof-v4 weighted-Kraft leaf. -/
def actualCNLCluster (data : AppendixNActualProofV4LeafInputs)
    (ctx : ActualFailureContext) :
    CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  (data.actualCNLGrounded ctx).toCNLClusterEncodingData

/-- The separated Return leaf of the proof-v4 provider in the current actual
Return split surface. -/
def actualReturnSplit (data : AppendixNActualProofV4LeafInputs)
    (ctx : ActualFailureContext) :
    ActualReturnRawI51M2J4L6SplitScalarData ctx :=
  ActualReturnRawI51M2J4L6SplitScalarData.ofSeparatedLeaf
    (data.returnPkg ctx.shell (data.actualPin ctx) ctx.shell_startThreshold_le)

/-- The separated Return leaf of the proof-v4 provider in the compact actual
Return surface. -/
def actualReturnRaw (data : AppendixNActualProofV4LeafInputs)
    (ctx : ActualFailureContext) :
    ActualReturnRawI51M2J4L6Data ctx :=
  ActualReturnRawI51M2J4L6Data.ofSeparatedLeaf
    (data.returnPkg ctx.shell (data.actualPin ctx) ctx.shell_startThreshold_le)

/-- The separated Run leaf of the proof-v4 provider in the current actual Run
split/absorption surface. -/
def actualRunSplit (data : AppendixNActualProofV4LeafInputs)
    (ctx : ActualFailureContext) :
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx :=
  ActualRunRawL41L42I52SplitAbsorptionScalarData.ofSeparatedLeaf
    (data.run ctx.shell (data.actualPin ctx) ctx.shell_startThreshold_le)

/-- The separated Run leaf of the proof-v4 provider in the compact actual Run
surface. -/
def actualRunRaw (data : AppendixNActualProofV4LeafInputs)
    (ctx : ActualFailureContext) :
    ActualRunRawL41L42I52Data ctx :=
  ActualRunRawL41L42I52Data.ofSeparatedLeaf
    (data.run ctx.shell (data.actualPin ctx) ctx.shell_startThreshold_le)

/-- The proof-v4 canonical-Y variation leaf at the actual failing shell. -/
def actualVariationLeaf (data : AppendixNActualProofV4LeafInputs)
    (ctx : ActualFailureContext) :=
  data.variation ctx.shell (data.actualPin ctx) ctx.shell_startThreshold_le

/-- The proof-v4 separated terminal leaf at the actual failing shell. -/
def actualTerminalLeaf (data : AppendixNActualProofV4LeafInputs)
    (ctx : ActualFailureContext) :=
  data.terminalAbsorption ctx.shell (data.actualPin ctx)
    ctx.shell_startThreshold_le

/--
Restrict the proof-v4 Appendix N leaf provider to the actual-consumption final
interface.

Unlike the older capstone, this conversion asks for charge only on the phase
package actually assembled by `canonicalYChainCompressionAt`.
-/
def toActualInputs (data : AppendixNActualProofV4LeafInputs) :
    GlobalAssemblyActualInputs where
  carryData := data.actualCarryData
  chernoff := fun ctx => (data.actualPhases ctx).chernoff
  cnl := fun ctx => (data.actualPhases ctx).cnl
  densePack := fun ctx => (data.actualPhases ctx).densePack
  tower := fun ctx => (data.actualPhases ctx).tower
  returnPkg := fun ctx => (data.actualPhases ctx).returnPkg
  run := fun ctx => (data.actualPhases ctx).run
  highExcessCharge := fun ctx => data.actualHighExcessCharge ctx

/--
Restrict the proof-v4 Appendix N provider to the explicit leaf-consumption
surface.  This keeps Chernoff, CNL, DensePack, dirty multiplicity, Tower,
Return, and Run exposed in the same constructor shape as the canonical
Appendix N chain.
-/
def toActualProofV4LeafInputs (data : AppendixNActualProofV4LeafInputs) :
    GlobalAssemblyActualProofV4LeafInputs where
  chernoff := data.actualChernoffLeaf
  cnl := data.actualCNLWeightedKraft
  densePack := fun ctx =>
    appendixNGapCanonicalYActualDensePackToGrounded ctx.shell
      (data.actualPin ctx).hc0Small ctx.shell_startThreshold_le
  dirtyMultiplicity := fun ctx =>
    DirtyMultiplicityProofV4ShellFibreInputData.toDirtyMultiplicityData
      (data.dirtyMultiplicity ctx.shell (data.actualPin ctx).hc0Small
        ctx.shell_startThreshold_le)
  tower := fun ctx =>
    data.tower ctx.shell (data.actualPin ctx) ctx.shell_startThreshold_le
  returnPkg := fun ctx =>
    data.returnPkg ctx.shell (data.actualPin ctx) ctx.shell_startThreshold_le
  run := fun ctx =>
    data.run ctx.shell (data.actualPin ctx) ctx.shell_startThreshold_le
  carryData := data.actualCarryData
  highExcessCharge := fun ctx => by
    simpa [actualProofV4LeafPhases, actualChernoffLeaf,
      actualCNLWeightedKraft, actualPhases, actualChain,
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTerminalSeparatedTRTLocalLeafVariationKMN2N3Inputs.canonicalYChainCompressionAt,
      appendixNGapCanonicalYTRTLocalLeaves,
      appendixNGapCanonicalYLeafTRT,
      appendixNGapCanonicalYSmallLargeSubpackagePhaseCore]
      using data.actualHighExcessCharge ctx

end AppendixNActualProofV4LeafInputs

/--
Final actual-consumption bridge from the strongest proof-v4 Appendix N leaf
provider surface.
-/
theorem erdos260_final_actual_from_appendixN_leaf_inputs
    (data : AppendixNActualProofV4LeafInputs) : Erdos260Statement :=
  erdos260_final_actual data.toActualInputs

/--
The exact final provider object still needed for a no-argument theorem,
projected to the actual-consumption assembly interface.
-/
def globalAssemblyActual_from_appendixN_leaf_inputs
    (data : AppendixNActualProofV4LeafInputs) : GlobalAssemblyActualInputs :=
  data.toActualInputs

/--
Final no-argument theorem reduced to the nonemptiness of the strongest
proof-v4 Appendix N manuscript leaf provider.

This is the remaining mathematical certificate to build: a real, non-synthetic
inhabitant of `AppendixNActualProofV4LeafInputs`.
-/
theorem erdos260_unconditional_from_appendixN_leaf_provider
    (hprovider : Nonempty AppendixNActualProofV4LeafInputs) :
    Erdos260Statement := by
  exact hprovider.elim
    erdos260_final_actual_from_appendixN_leaf_inputs

/-- Nonemptiness of the strongest Appendix N manuscript provider gives the
final actual assembly input object. -/
theorem globalAssemblyActualInputs_nonempty_of_appendixN_leaf_provider
    (hprovider : Nonempty AppendixNActualProofV4LeafInputs) :
    Nonempty GlobalAssemblyActualInputs := by
  exact hprovider.elim fun data => Nonempty.intro data.toActualInputs

/--
Final bridge through the explicit proof-v4 leaf-consumption surface, derived
from the strongest Appendix N manuscript provider.
-/
theorem erdos260_final_actual_proofV4_leaf_from_appendixN_leaf_inputs
    (data : AppendixNActualProofV4LeafInputs) : Erdos260Statement :=
  erdos260_final_actual_proofV4_leaf data.toActualProofV4LeafInputs

#print axioms erdos260_final_actual
#print axioms erdos260_final_actual_reduced
#print axioms erdos260_final_actual_grounded
#print axioms erdos260_final_actual_cnlCluster
#print axioms erdos260_final_actual_leaf
#print axioms erdos260_final_actual_n24Leaf
#print axioms erdos260_final_actual_runPackageN24
#print axioms erdos260_final_actual_closedN2RunPackage
#print axioms erdos260_final_actual_closedN2N3RunPackage
#print axioms erdos260_final_actual_rawCNLClosedN2N3RunPackage
#print axioms erdos260_final_actual_rawCNLRRClosedN2N3
#print axioms erdos260_final_actual_rawCNLRRClosedN2N3BddL6
#print axioms erdos260_final_actual_explicitPhaseClosedN2N3BddL6
#print axioms erdos260_unconditional_from_explicitPhaseClosedN2N3BddL6_provider
#print axioms erdos260_final_actual_rawCNLRRRawTerminalLowPaid
#print axioms erdos260_final_actual_rawCNLRRRawN2RawTerminalLowPaid
#print axioms erdos260_final_actual_rawCNLRRRawN2StructuredTerminalLowPaid
#print axioms erdos260_final_actual_rawChernoffCNLRRRawN2StructuredTerminalLowPaid
#print axioms erdos260_final_actual_stoppedTreeChernoffCNLRRRawN2StructuredTerminalLowPaid
#print axioms erdos260_final_actual_splitBudgetChernoffCNLRRRawN2StructuredTerminalLowPaid
#print axioms erdos260_final_actual_exponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaid
#print axioms erdos260_final_actual_scalarRRExponentialTailChernoffCNLRRRawN2StructuredTerminalLowPaid
#print axioms erdos260_final_actual_tiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaid
#print axioms erdos260_final_actual_splitRunTiltMomentChernoffScalarRRCNLRRRawN2StructuredTerminalLowPaid
#print axioms erdos260_final_actual_finiteOverlapTerminalSplitRunTiltMomentChernoffScalarRRCNLRRRawN2Structured
#print axioms erdos260_final_actual_finiteSumChernoffFiniteOverlapTerminalSplitRunScalarRRCNLRRRawN2Structured
#print axioms erdos260_final_actual_finiteSumChernoffFiniteOverlapTerminalSplitReturnRunRRCNLRawN2Structured
#print axioms erdos260_final_actual_finiteSumChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2Structured
#print axioms erdos260_final_actual_zeroLengthChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2Structured
#print axioms erdos260_final_actual_rootBoundChernoffFiniteOverlapTerminalSplitReturnRunCodeFibreCNLRawN2Structured
#print axioms erdos260_final_actual_rootBoundChernoffTerminalFieldsSplitReturnRunCodeFibreCNLRawN2Structured
#print axioms erdos260_final_actual_rootBoundChernoffTerminalMassFieldsSplitReturnRunCodeFibreCNLRawN2Structured
#print axioms erdos260_final_actual_rootBoundChernoffTerminalMassDenseFieldsSplitReturnRunCodeFibreCNLRawN2Structured
#print axioms erdos260_final_actual_rootBoundChernoffTerminalMassDenseProgressFieldsSplitReturnRunCodeFibreCNLRawN2Structured
#print axioms erdos260_final_actual_rootBoundChernoffTerminalMassDenseProgressEndpointFieldsSplitReturnRunCodeFibreCNLRawN2Structured
#print axioms erdos260_final_actual_rootBoundChernoffTerminalAllClassFieldsSplitReturnRunCodeFibreCNLRawN2Structured
#print axioms erdos260_final_actual_rootBoundChernoffTerminalAllFieldsSplitReturnRunCodeFibreCNLRawN2Structured
#print axioms erdos260_final_actual_rootBoundChernoffTerminalPinnedPhaseAllFieldsSplitReturnRunCodeFibreCNLRawN2Structured
#print axioms erdos260_final_actual_currentProviderTarget
#print axioms erdos260_unconditional_from_current_actual_provider
#print axioms erdos260_final_actual_rootSmallChernoffCurrentProvider
#print axioms erdos260_unconditional_from_rootSmallChernoff_current_provider
#print axioms erdos260_final_actual_rootSmallChernoffCodeFibreCNLCurrentProvider
#print axioms erdos260_unconditional_from_rootSmallChernoff_codeFibreCNL_current_provider
#print axioms erdos260_final_actual_rootSmallChernoffClassicalCodeFibreCNLCurrentProvider
#print axioms erdos260_unconditional_from_rootSmallChernoff_classicalCodeFibreCNL_current_provider
#print axioms erdos260_final_actual_rootSmallChernoffClassicalCodeFibreCNLRawN24Provider
#print axioms erdos260_unconditional_from_rootSmallChernoff_classicalCodeFibreCNL_rawN24_provider
#print axioms erdos260_final_actual_fixedTiltChernoffClassicalCodeFibreCNLRawN24Provider
#print axioms erdos260_unconditional_from_fixedTiltChernoff_classicalCodeFibreCNL_rawN24_provider
#print axioms erdos260_final_actual_preferredProviderTarget
#print axioms erdos260_unconditional_from_preferred_actual_provider
#print axioms erdos260_final_actual_proofV4_leaf
#print axioms erdos260_final_actual_from_appendixN_leaf_inputs
#print axioms erdos260_unconditional_from_appendixN_leaf_provider
#print axioms erdos260_final_actual_proofV4_leaf_from_appendixN_leaf_inputs

end

end Erdos260
