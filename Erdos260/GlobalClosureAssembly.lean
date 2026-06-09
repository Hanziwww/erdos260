import Mathlib
import Erdos260.ChernoffDataFactory
import Erdos260.GlobalThresholds
import Erdos260.HighExcessChargeFactory
import Erdos260.ManuscriptClosure
import Erdos260.AppendixI_PhaseMass

/-!
# Global closure assembly

This file is the final assembly layer above `PerFailureAssemblyData`.
It proves that a uniform provider of per-failure assemblies is enough to build
`ManuscriptClosureData`, hence the final target theorem.
-/

namespace Erdos260

noncomputable section

/--
Global per-failure assembly provider.

This is the exact remaining object to inhabit before the theorem becomes
unconditional: constants, a start threshold, and for every failing shell a
complete `PerFailureAssemblyData`.
-/
structure GlobalPerFailureAssembly where
  constants : Erdos260Constants
  startThreshold :
    ∀ (Q : Nat) (d : Nat -> Nat),
      0 < Q -> BinaryDigits d -> ¬ EventuallyZero d ->
      (∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) ->
        Nat
  /-- **Round Α2**: failure hypothesis uses `c0` (strict). -/
  perFailureAssembly :
    ∀ (Q : Nat) (d : Nat -> Nat)
      (hQ : 0 < Q) (hd : BinaryDigits d)
      (hnonterm : ¬ EventuallyZero d)
      (hrational :
        ∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)),
      ∀ X : Nat, Dyadic X ->
        startThreshold Q d hQ hd hnonterm hrational ≤ X ->
        ((supportShell d X).card : ℝ) < constants.c0 * (X : ℝ) ->
          PerFailureAssemblyData constants.cPr constants.cStar constants.ξ X

/-- Convert a global per-failure assembly provider to `GlobalClosureFactory`. -/
def GlobalPerFailureAssembly.toGlobalClosureFactory
    (data : GlobalPerFailureAssembly) :
    GlobalClosureFactory where
  constants := data.constants
  startThreshold := data.startThreshold
  perFailure := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    exact (data.perFailureAssembly Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure).toFactory
      (le_of_lt data.constants.cPr_pos)

/-- Convert a global per-failure assembly provider to manuscript closure data. -/
def GlobalPerFailureAssembly.toManuscriptClosureData
    (data : GlobalPerFailureAssembly) :
    ManuscriptClosureData where
  globalFactory := data.toGlobalClosureFactory

/-- Final target from the global per-failure assembly provider. -/
theorem erdos260Statement_of_globalPerFailureAssembly
    (data : GlobalPerFailureAssembly) :
    Erdos260Statement :=
  erdos260Statement_of_manuscriptClosureData data.toManuscriptClosureData

/--
Coherent collection of all per-shell providers using one shared constants
bundle.  This is the current concrete target for the remaining manuscript
formalization.
-/
structure GlobalAssemblyInputs where
  constants : Erdos260Constants
  /-- **Round Α2**: manuscript-strict requirement `c0 < κ` (the strict
  failure constant is below the manuscript `κ`).  The canonical
  `erdos260Constants` satisfies this via `manuscriptC0_lt_kappa`. -/
  c0_lt_kappa : constants.c0 < manuscriptKappa
  thresholds :
    ∀ (Q : Nat) (d : Nat -> Nat),
      0 < Q -> BinaryDigits d -> ¬ EventuallyZero d ->
      (∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) ->
        PerInstanceThresholds
  carryData :
    ∀ shell : FailingDyadicShell,
      shell.cQ = constants.cQ ->
        CarryDataFromFailure shell constants.cPr
  chernoff :
    ∀ shell : FailingDyadicShell,
      shell.cQ = constants.cQ ->
        ChernoffPathData constants.cStar constants.ξ (shell.X : ℝ)
  cnl :
    ∀ shell : FailingDyadicShell,
      shell.cQ = constants.cQ ->
        CNLClusterEncodingData constants.cStar constants.ξ (shell.X : ℝ)
  densePack :
    ∀ shell : FailingDyadicShell,
      shell.cQ = constants.cQ ->
        DensePackFactoryData constants.cStar constants.ξ (shell.X : ℝ)
  tower :
    ∀ shell : FailingDyadicShell,
      shell.cQ = constants.cQ ->
        TowerTransientFactoryData constants.cStar constants.ξ (shell.X : ℝ)
  returnPkg :
    ∀ shell : FailingDyadicShell,
      shell.cQ = constants.cQ ->
        ReturnFactoryData constants.cStar constants.ξ (shell.X : ℝ)
  run :
    ∀ shell : FailingDyadicShell,
      shell.cQ = constants.cQ ->
        RunFactoryData constants.cStar constants.ξ (shell.X : ℝ)
  highExcessCharge :
    ∀ (shell : FailingDyadicShell)
      (_hcQ : shell.cQ = constants.cQ)
      (phases : SixPhaseFactoryData constants.cStar constants.ξ (shell.X : ℝ))
      (carryData : CarryDataFromFailure shell constants.cPr),
        HighExcessChargeData phases carryData

/-- **Largeness gate (manuscript "sufficiently large dyadic `X`").**

A failing dyadic shell is *above the carry threshold* when its dyadic scale `X` reaches the
manuscript carry-large scale `carryThreshold (carryB Q + 19) = 2^(carryB Q + 25)`, i.e.
`carryB Q + 25 ≤ L` (with `X = 2^L` and `4Q ≤ 2^(carryB Q)`).  This is exactly the
`ShellWindowInputs` scale condition `B + 25 ≤ L` (`carryLarge_of_carryThreshold_le`), below which
the Lemma 21.1 positive-density pressure floor (`CarryDataFromFailure`/`ShellWindowInputs`) is
genuinely unavailable (`AuditAnalyticInputs.audit_carryWindow_forces_scale`).  The floor is an
*asymptotic* statement, established only "for every sufficiently large dyadic `X`"
(proof_v4_unconditional_clean_v5.tex, Thm `positive-dyadic-density`, lines 79/613/639).

Gating the per-shell carry obligation by this **non-trivial, `Q`-dependent** threshold makes the
floor required *only* at shells where it asymptotically holds — genuinely removing the
over-quantification over *all* `cQ`-shells (incl. the small ones for which `CarryDataFromFailure`
is empty).  It is discharged at the consumer from the per-failure `startThreshold ≤ X` hypothesis
(previously discarded as `_hXge`), now pinned to this same carry threshold. -/
def FailingDyadicShell.aboveCarryThreshold (shell : FailingDyadicShell) : Prop :=
  carryThreshold (carryB shell.Q + 19) ≤ shell.X

/--
Core global assembly inputs after discharging the purely bookkeeping threshold
provider.

The constants are pinned to `erdos260Constants`, `c0 < κ` is supplied by
`manuscriptC0_lt_kappa`, and thresholds are supplied by `canonicalThresholds`.
What remains here are the eight provider fields still consumed directly by the
final assembly after the threshold, legacy-ledger, and old local-geometry
compatibility slots have been closed.  The DensePack phase is exposed as the
exact `DensePackFactoryData` needed by `SixPhaseFactoryData`; the K/M side
targets are tracked separately and are not consumed by the final assembly.
-/
structure GlobalAssemblyCoreInputs where
  /-- **Per-failure carry data, gated to sufficiently large scales** (manuscript Lemma 21.1
  positive-density pressure floor, established only for large dyadic `X`).  Required only at
  shells `aboveCarryThreshold`; the consumer discharges the gate from its `startThreshold ≤ X`
  hypothesis.  This removes the over-quantification over *all* `cQ`-shells (incl. small ones where
  the asymptotic floor is unavailable). -/
  carryData :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ -> shell.aboveCarryThreshold ->
        CarryDataFromFailure shell erdos260Constants.cPr
  chernoff :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  cnl :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  densePack :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  tower :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  returnPkg :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  run :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        RunFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- **Phase-mass nonnegativity (manuscript §I / J.1.1 charging).** The per-shell
  Return and Run phase masses are physically nonnegative; discharges the
  `phases.trtNonneg` restriction of `highExcessCharge` for the genuine phase data. -/
  returnRunMassNonneg :
    ∀ (shell : FailingDyadicShell) (hcQ : shell.cQ = erdos260Constants.cQ),
      0 ≤ (returnPkg shell hcQ).massSum + (run shell hcQ).runMass
  highExcessCharge :
    ∀ (shell : FailingDyadicShell)
      (_hcQ : shell.cQ = erdos260Constants.cQ)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : ℝ))
      (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
      (_hphases : phases.trtNonneg),
        HighExcessChargeData phases carryData

def GlobalAssemblyInputs.startThreshold
    (data : GlobalAssemblyInputs)
    (Q : Nat) (d : Nat -> Nat)
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (hnonterm : ¬ EventuallyZero d)
    (hrational :
      ∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) :
    Nat :=
  (data.thresholds Q d hQ hd hnonterm hrational).startThreshold

def GlobalAssemblyInputs.toGlobalThresholdData
    (data : GlobalAssemblyInputs) :
    GlobalThresholdData where
  constants := data.constants
  thresholds := data.thresholds

def GlobalAssemblyInputs.toCarryDataProvider
    (data : GlobalAssemblyInputs) :
    CarryDataProvider where
  constants := data.constants
  data := data.carryData

def GlobalAssemblyInputs.toChernoffDataProvider
    (data : GlobalAssemblyInputs) :
    ChernoffDataProvider where
  constants := data.constants
  data := data.chernoff

def GlobalAssemblyInputs.toCNLClusterEncodingProvider
    (data : GlobalAssemblyInputs) :
    CNLClusterEncodingProvider where
  constants := data.constants
  data := data.cnl

def GlobalAssemblyInputs.toTowerDataProvider
    (data : GlobalAssemblyInputs) :
    TowerDataProvider where
  constants := data.constants
  data := data.tower

def GlobalAssemblyInputs.toReturnDataProvider
    (data : GlobalAssemblyInputs) :
    ReturnDataProvider where
  constants := data.constants
  data := data.returnPkg

def GlobalAssemblyInputs.toRunDataProvider
    (data : GlobalAssemblyInputs) :
    RunDataProvider where
  constants := data.constants
  data := data.run

def GlobalAssemblyInputs.toHighExcessChargeProvider
    (data : GlobalAssemblyInputs) :
    HighExcessChargeProvider where
  constants := data.constants
  data := data.highExcessCharge

def GlobalAssemblyInputs.toGlobalPerFailureAssembly
    (data : GlobalAssemblyInputs) :
    GlobalPerFailureAssembly where
  constants := data.constants
  startThreshold := data.startThreshold
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic _hXge hfailure
    -- **Round Α2**: `hfailure : K < constants.c0 * X` is now the strict
    -- manuscript hypothesis.  We build the c₀-strict shell directly.
    -- The two structural witnesses `c0_pos` and `c0_le_cQ` come from the
    -- constants bundle; `c0_lt_kappa` must be guaranteed by callers
    -- supplying manuscript-strict constants (the canonical
    -- `erdos260Constants` satisfies this via `manuscriptC0_lt_kappa`).
    have hc0_lt_kappa : data.constants.c0 < manuscriptKappa :=
      data.c0_lt_kappa
    let shell :=
      FailingDyadicShell.ofGlobalConstants data.constants Q d X
        hQ hd hnonterm hrational hXdyadic
        data.constants.c0 data.constants.c0_pos
        hc0_lt_kappa data.constants.c0_le_cQ hfailure
    have hcQ : shell.cQ = data.constants.cQ := rfl
    let phases : SixPhaseFactoryData data.constants.cStar data.constants.ξ (X : ℝ) := {
      chernoff := data.chernoff shell hcQ
      cnl := data.cnl shell hcQ
      tower := data.tower shell hcQ
      densePack := data.densePack shell hcQ
      returnPkg := data.returnPkg shell hcQ
      run := data.run shell hcQ }
    let carry := data.carryData shell hcQ
    let charge := data.highExcessCharge shell hcQ phases carry
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carry charge

theorem erdos260Statement_of_globalAssemblyInputs
    (data : GlobalAssemblyInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

def GlobalAssemblyInputs.toManuscriptClosureData
    (data : GlobalAssemblyInputs) :
    ManuscriptClosureData :=
  data.toGlobalPerFailureAssembly.toManuscriptClosureData

def GlobalAssemblyInputs.toClosureCertificate
    (data : GlobalAssemblyInputs) :
    Erdos260ClosureCertificate :=
  data.toManuscriptClosureData.toClosureCertificate

theorem theoremA_of_globalAssemblyInputs
    (data : GlobalAssemblyInputs) :
    TheoremAStatement :=
  theoremA_of_closureCertificate data.toClosureCertificate

def GlobalAssemblyCoreInputs.startThreshold
    (_data : GlobalAssemblyCoreInputs)
    (Q : Nat) (d : Nat -> Nat)
    (_hQ : 0 < Q) (_hd : BinaryDigits d)
    (_hnonterm : ¬ EventuallyZero d)
    (_hrational :
      ∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) :
    Nat :=
  -- **Pinned to the manuscript carry-large scale** (`2^(carryB Q + 25)`), so the per-failure
  -- `startThreshold ≤ X` hypothesis is the genuine "sufficiently large dyadic `X`" gate that
  -- discharges `FailingDyadicShell.aboveCarryThreshold`.  (Previously trivial `canonicalThresholds`
  -- = `0`, which made any largeness gate vacuous.)
  carryThreshold (carryB Q + 19)

def GlobalAssemblyCoreInputs.toGlobalPerFailureAssembly
    (data : GlobalAssemblyCoreInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := data.startThreshold
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    have hcQ : shell.cQ = erdos260Constants.cQ := rfl
    -- The largeness gate is discharged from the (previously ignored) `startThreshold ≤ X`
    -- hypothesis: `shell.aboveCarryThreshold` is definitionally this very inequality, since
    -- `GlobalAssemblyCoreInputs.startThreshold` is pinned to `carryThreshold (carryB Q + 19)`.
    have hlarge : shell.aboveCarryThreshold := hXge
    let phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (X : ℝ) := {
      chernoff := data.chernoff shell hcQ
      cnl := data.cnl shell hcQ
      tower := data.tower shell hcQ
      densePack := data.densePack shell hcQ
      returnPkg := data.returnPkg shell hcQ
      run := data.run shell hcQ }
    let carry := data.carryData shell hcQ hlarge
    let charge := data.highExcessCharge shell hcQ phases carry
      (phases.trtNonneg_of_returnRun_nonneg (data.returnRunMassNonneg shell hcQ))
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carry charge

def GlobalAssemblyCoreInputs.toManuscriptClosureData
    (data : GlobalAssemblyCoreInputs) :
    ManuscriptClosureData :=
  data.toGlobalPerFailureAssembly.toManuscriptClosureData

def GlobalAssemblyCoreInputs.toClosureCertificate
    (data : GlobalAssemblyCoreInputs) :
    Erdos260ClosureCertificate :=
  data.toManuscriptClosureData.toClosureCertificate

/-- Theorem A from the reduced eight-provider core interface. -/
theorem theoremA_of_globalAssemblyCoreInputs
    (data : GlobalAssemblyCoreInputs) :
    TheoremAStatement :=
  theoremA_of_closureCertificate data.toClosureCertificate

/-- Erdős 260 from the reduced eight-provider core interface. -/
theorem erdos260Statement_of_globalAssemblyCoreInputs
    (data : GlobalAssemblyCoreInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

/--
**Top-level Erdős 260 reduction (`erdos260_final`).**

The canonical top-level entry point of the formalization: a complete, checked
reduction of `Erdos260Statement` to the single object `GlobalAssemblyInputs`.
Every algebraic and combinatorial step from `GlobalAssemblyInputs` to the
manuscript target is proved unconditionally (no `sorry`, no `axiom`).

This theorem is **conditional on `GlobalAssemblyInputs`**.  Making the reduced
endpoint fully unconditional is precisely the remaining manuscript content:
inhabiting the eight core provider fields (roadmap phases P1–P10), the deepest
being the central charge
bridge `CarryPressureBridge.highExcess_le_phaseMass` (P9) and the Appendix G
CNL classifier (P3).  The foundational objects and many internal estimates of
those phases are now real theorems (see `LiftState`, `AppendixG_Ladder`,
`StoppedTree`, `finiteDescent_le`, …); the residual is their assembly into the
provider inhabitants. -/
theorem erdos260_final (data : GlobalAssemblyInputs) : Erdos260Statement :=
  erdos260Statement_of_globalAssemblyInputs data

/--
Reduced top-level endpoint after the global-threshold bookkeeping has been
closed canonically.  The remaining hypothesis is the eight-provider
`GlobalAssemblyCoreInputs`.
-/
theorem erdos260_final_core (data : GlobalAssemblyCoreInputs) : Erdos260Statement :=
  erdos260Statement_of_globalAssemblyCoreInputs data

end

end Erdos260
