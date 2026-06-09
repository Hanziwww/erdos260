import Mathlib
import Erdos260.GlobalHighExcessAssembly

/-!
# Global carry assembly

This module pushes one more global slot toward the proof-v4 interface.  The
remaining endpoint no longer needs a raw `CarryDataFromFailure` provider here:
carry data is built from the shell-level parameters consumed by
`CarryDataFromFailure.ofShellAndSupportCount`.

The final theorem in this file assembles a per-failure object directly, so the
grounded high-excess data only has to apply to the carry data produced by this
constructor, not to an arbitrary externally supplied carry package.
-/

namespace Erdos260

noncomputable section

/--
Proof-v4 aligned local carry data for one failing shell.

This is the cleanest constructor currently available in `CarryDataFactory`: the
window lower bound, shell-window geometry, and low-excess upper bound are
proved internally; the remaining fields are the shell parameters, positivity,
support-count start condition, and the numerical allocation inequality.
-/
structure GroundedCarryLocalData (shell : FailingDyadicShell) (cPr : Real) where
  P : Int
  L : Nat
  B : Nat
  r : Nat
  T : Real
  Y : Real
  hY : 0 <= Y
  hP :
    realWeightedValue (natBinaryAsReal shell.d) =
      (P : Real) / (shell.Q : Real)
  hX_eq : shell.X = 2 ^ L
  hX_pos : 1 <= shell.X
  hB : shell.Q * 4 <= 2 ^ B
  hKr : r + 1 <= (supportShell shell.d shell.X).card
  h_supportCount_pos : 1 <= supportCount shell.d shell.X
  hAlloc :
    cPr * (shell.X : Real) * ((r : Real) + 1)
        + ((supportShell shell.d shell.X).card : Real) * Y
        + ((supportShell shell.d shell.X).card : Real) * T
        + ((r : Real) + 1) ^ 2 * ((L : Real) + (B : Real) + 1)
      <= ((r : Real) + 1) * (shell.X : Real)

/-- Build the checked carry package from the proof-v4 aligned local data. -/
def GroundedCarryLocalData.toCarryData
    {shell : FailingDyadicShell} {cPr : Real}
    (data : GroundedCarryLocalData shell cPr) :
    CarryDataFromFailure shell cPr :=
  CarryDataFromFailure.ofShellAndSupportCount shell cPr
    data.P data.L data.B data.r data.T data.Y
    data.hY data.hP data.hX_eq data.hX_pos data.hB data.hKr
    data.h_supportCount_pos data.hAlloc

/-- Per-shell provider for grounded carry data. -/
structure GroundedCarryDataProvider where
  constants : Erdos260Constants
  data :
    forall shell : FailingDyadicShell,
      shell.cQ = constants.cQ ->
        GroundedCarryLocalData shell constants.cPr

/-- Forget grounded carry data to the legacy carry provider. -/
def GroundedCarryDataProvider.toCarryDataProvider
    (provider : GroundedCarryDataProvider) :
    CarryDataProvider where
  constants := provider.constants
  data := by
    intro shell hcQ
    exact (provider.data shell hcQ).toCarryData

/--
Core global assembly where both the carry side and high-excess side use the
structured proof-v4 routes currently available.
-/
structure GlobalAssemblyCoreGroundedCarryHighExcessInputs where
  carry :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCarryLocalData shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ
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

/-- Convert the grounded carry/high-excess interface directly to per-failure assembly. -/
def GlobalAssemblyCoreGroundedCarryHighExcessInputs.toGlobalPerFailureAssembly
    (data : GlobalAssemblyCoreGroundedCarryHighExcessInputs) :
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
      chernoff := data.chernoff shell hcQ
      cnl := data.cnl shell hcQ
      tower := data.tower shell hcQ
      densePack := data.densePack shell hcQ
      returnPkg := data.returnPkg shell hcQ
      run := data.run shell hcQ }
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases
        ((data.carry shell hcQ).toCarryData)
        ((data.highExcess shell hcQ phases).toHighExcessChargeData)

/--
Erdos 260 from the core interface whose carry package and high-excess package
are both supplied through the current proof-v4 aligned constructors.
-/
theorem erdos260_final_core_grounded_carry_highExcess
    (data : GlobalAssemblyCoreGroundedCarryHighExcessInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

end

end Erdos260
