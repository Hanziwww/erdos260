import Erdos260.DirtyFaithfulFamilyCore
import Erdos260.ShellPaidChernoff22_1ALeafConstruction
import Erdos260.CNLScalarBudgetCore
import Erdos260.ReturnCountsCore
import Erdos260.RunL4I52Core
import Erdos260.TowerActiveFloorClosure
import Erdos260.GlobalHighExcessAssembly

namespace Erdos260

noncomputable section

/-!
# Current actual-provider bridge with strict CNL installed

This downstream module records the concrete progress supplied by
`cnlStrictWeightedKraftShellProvider`: the CNL column of the current actual
provider target is no longer a free input.  The sibling Chernoff, Return, Run,
N.2, and N.3.3/L.6 columns remain explicit manuscript data.
-/

/-- Actual current-provider phase after filling the CNL column with the strict
L.1.2/G.35 shell provider. -/
def actualClosurePhaseFromStrictCNLCurrentProvider
    (ctx : ActualFailureContext)
    (chernoff : ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx) :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  actualClosurePhaseFromRootBoundWeightedKraftSplitRR ctx
    chernoff (actualCNLWeightedKraftFromStrictProvider ctx) returnPkg run

/-- Raw N.2 field for the current actual provider after the strict CNL bridge
has been installed. -/
abbrev ActualStrictCNLCurrentRawN2Data
    (ctx : ActualFailureContext)
    (chernoff : ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx) : Type 1 :=
  ActualRawN2FirstCrossingData ctx
    (termRun
      (actualClosurePhaseFromStrictCNLCurrentProvider ctx
        chernoff returnPkg run))

/-- Pinned N.3.3/L.6 terminal field for the current actual provider after the
strict CNL bridge has been installed. -/
abbrev ActualStrictCNLCurrentPinnedTerminalData
    (ctx : ActualFailureContext)
    (chernoff : ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx)
    (returnPkg : ActualReturnRawI51M2J4L6SplitScalarData ctx)
    (run : ActualRunRawL41L42I52SplitAbsorptionScalarData ctx)
    (n2 : ActualStrictCNLCurrentRawN2Data ctx chernoff returnPkg run) :
    Type 1 :=
  let phase :=
    actualClosurePhaseFromStrictCNLCurrentProvider ctx
      chernoff returnPkg run
  ActualStructuredTerminalPinnedPhaseAllFieldsLowPaidData
    ctx
    (chernoff.toChernoffLeaf)
    phase
    (n2.toVariationData)
    (termDensePack phase)
    (termChernoff phase)
    (termReturn phase)
    (termCnl phase)
    (termTower phase)

/-- Current actual-provider target with its CNL field fixed by the strict
shell construction.  This is a downstream reduced boundary, not a replacement
for the upstream six-column current-provider audit. -/
structure GlobalAssemblyActualStrictCNLCurrentProviderInputs where
  chernoff : forall ctx : ActualFailureContext,
    ActualShellPaidChernoffFiniteSumRootBoundScalarTailFieldsData ctx
  returnPkg : forall ctx : ActualFailureContext,
    ActualReturnRawI51M2J4L6SplitScalarData ctx
  run : forall ctx : ActualFailureContext,
    ActualRunRawL41L42I52SplitAbsorptionScalarData ctx
  n2 : forall ctx : ActualFailureContext,
    ActualStrictCNLCurrentRawN2Data ctx
      (chernoff ctx) (returnPkg ctx) (run ctx)
  terminal : forall ctx : ActualFailureContext,
    ActualStrictCNLCurrentPinnedTerminalData ctx
      (chernoff ctx) (returnPkg ctx) (run ctx) (n2 ctx)

namespace GlobalAssemblyActualStrictCNLCurrentProviderInputs

/-- Project the strict-CNL reduced boundary to the current actual-provider
target by installing `actualCNLWeightedKraftFromStrictProvider` in the CNL
slot. -/
def toCurrentProviderTarget
    (data : GlobalAssemblyActualStrictCNLCurrentProviderInputs) :
    GlobalAssemblyActualCurrentProviderTarget where
  chernoff := data.chernoff
  cnl := actualCNLWeightedKraftFromStrictProvider
  returnPkg := data.returnPkg
  run := data.run
  n2 := fun ctx => by
    simpa [ActualStrictCNLCurrentRawN2Data,
      actualClosurePhaseFromStrictCNLCurrentProvider]
      using data.n2 ctx
  terminal := fun ctx => by
    simpa [ActualStrictCNLCurrentPinnedTerminalData,
      ActualStrictCNLCurrentRawN2Data,
      actualClosurePhaseFromStrictCNLCurrentProvider]
      using data.terminal ctx

end GlobalAssemblyActualStrictCNLCurrentProviderInputs

/-- Final theorem bridge from the current-provider boundary with strict CNL
installed. -/
theorem erdos260_final_actual_strictCNLCurrentProvider
    (data : GlobalAssemblyActualStrictCNLCurrentProviderInputs) :
    Erdos260Statement :=
  erdos260_final_actual_currentProviderTarget data.toCurrentProviderTarget

/-- A nonempty strict-CNL current-provider boundary proves the final theorem. -/
theorem erdos260_unconditional_from_strictCNL_current_provider
    (hprovider :
      Nonempty GlobalAssemblyActualStrictCNLCurrentProviderInputs) :
    Erdos260Statement :=
  hprovider.elim erdos260_final_actual_strictCNLCurrentProvider

/-- Nonemptiness of the strict-CNL reduced boundary inhabits the upstream
current actual-provider target. -/
theorem current_actual_provider_nonempty_of_strictCNL_current_provider
    (hprovider :
      Nonempty GlobalAssemblyActualStrictCNLCurrentProviderInputs) :
    Nonempty GlobalAssemblyActualCurrentProviderTarget := by
  exact hprovider.elim fun data =>
    Nonempty.intro data.toCurrentProviderTarget

/-- Nonemptiness of the strict-CNL reduced boundary gives the final
actual-consumption assembly object. -/
theorem globalAssemblyActualInputs_nonempty_of_strictCNL_current_provider
    (hprovider :
      Nonempty GlobalAssemblyActualStrictCNLCurrentProviderInputs) :
    Nonempty GlobalAssemblyActualInputs :=
  globalAssemblyActualInputs_nonempty_of_current_actual_provider
    (current_actual_provider_nonempty_of_strictCNL_current_provider hprovider)

/-- The strict-CNL proof-v4 phase package after the formalized Chernoff, CNL,
DensePack, dirty-multiplicity, and Tower/Return/Run constructors have been
installed. -/
abbrev proofV4StrictCNLLeafPhase
    (towerHall : forall ctx : ActualFailureContext, Class2HallIndexSDRResidual ctx)
    (returnCounts : ReturnCountsResidual)
    (runCover : forall ctx : ActualFailureContext, RunHighExcessAreaCover ctx)
    (ctx : ActualFailureContext) :=
  actualProofV4LeafPhases ctx
    (chernoff22_1ALeafOfShell ctx)
    (cnlStrictWeightedKraftShellProvider
      ctx.shell ctx.hc0Small ctx.shell_startThreshold_le)
    (appendixNGapCanonicalYActualDensePackToGrounded
      ctx.shell ctx.hc0Small ctx.shell_startThreshold_le)
    (faithfulDirtyData ctx)
    (towerSeparatedLocalLeafProviderOfHallResidual towerHall ctx)
    ((returnLeafFromCounts ctx (returnCounts.densePack ctx)
      (returnCounts.olcSlotSmall ctx)).toReturnSeparatedLocalLeafInputData)
    (runSeparatedLocalLeafOfShellOfCover ctx (runCover ctx))

/-- Proof-v4 leaf-consumption surface with the Chernoff model leaf, the CNL leaf,
the dirty-multiplicity leaf, and the Tower/Return/Run leaf constructors fixed by
already formalized actual-context providers.  The Tower field is reduced to the
Hall-marginal Class 2 SDR residual from `TowerActiveFloorClosure`; the Return
field is reduced to the two-count residual from `ReturnCountsCore`; the Run field
is reduced to the single Section 26/I.4.1 cover datum from `RunL4I52Core`.  The
central charge field is reduced from the legacy `HighExcessChargeData` target to
the branch-mass-normalized Appendix I/N data consumed by
`BranchMassGroundedHighExcessLocalData`. -/
structure GlobalAssemblyActualProofV4StrictCNLLeafInputs where
  towerHall : forall ctx : ActualFailureContext, Class2HallIndexSDRResidual ctx
  returnCounts : ReturnCountsResidual
  runCover : forall ctx : ActualFailureContext, RunHighExcessAreaCover ctx
  highExcessBranchMass : forall ctx : ActualFailureContext,
    BranchMassGroundedHighExcessLocalData
      (proofV4StrictCNLLeafPhase towerHall returnCounts runCover ctx)
      ctx.n24CarryData

namespace GlobalAssemblyActualProofV4StrictCNLLeafInputs

/-- The formalized non-vacuous §22 model Chernoff leaf installed in the reduced
proof-v4 surface. -/
def chernoff (_data : GlobalAssemblyActualProofV4StrictCNLLeafInputs)
    (ctx : ActualFailureContext) :
    RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : Real) :=
  chernoff22_1ALeafOfShell ctx

/-- The canonical actual-support DensePack leaf is already determined by the
actual failing shell and the Appendix N start-threshold gate. -/
def densePack (_data : GlobalAssemblyActualProofV4StrictCNLLeafInputs)
    (ctx : ActualFailureContext) :
    GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  appendixNGapCanonicalYActualDensePackToGrounded
    ctx.shell ctx.hc0Small ctx.shell_startThreshold_le

/-- The canonical N.24 carry datum is already determined by the actual failure
context; it is not an extra proof-v4 provider field. -/
def carryData (_data : GlobalAssemblyActualProofV4StrictCNLLeafInputs)
    (ctx : ActualFailureContext) :
    CarryDataFromFailure ctx.shell erdos260Constants.cPr :=
  ctx.n24CarryData

/-- The strict CNL leaf installed in the reduced proof-v4 surface. -/
def cnl (_data : GlobalAssemblyActualProofV4StrictCNLLeafInputs)
    (ctx : ActualFailureContext) :
    CNLStandardWeightedKraftShellInputData ctx.shell
      erdos260Constants.cStar erdos260Constants.ξ :=
  cnlStrictWeightedKraftShellProvider
    ctx.shell ctx.hc0Small ctx.shell_startThreshold_le

/-- The faithful K.2.5 dirty-multiplicity leaf installed in the reduced
proof-v4 surface. -/
def dirtyMultiplicity (_data : GlobalAssemblyActualProofV4StrictCNLLeafInputs)
    (ctx : ActualFailureContext) :
    DirtyMultiplicityData :=
  faithfulDirtyData ctx

/-- The Tower separated leaf reconstructed from the Hall-marginal class-2 SDR
residual. -/
def tower (data : GlobalAssemblyActualProofV4StrictCNLLeafInputs)
    (ctx : ActualFailureContext) :
    TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  towerSeparatedLocalLeafProviderOfHallResidual data.towerHall ctx

/-- The Return separated leaf reconstructed from the two concrete
`ReturnCountsResidual` fields. -/
def returnPkg (data : GlobalAssemblyActualProofV4StrictCNLLeafInputs)
    (ctx : ActualFailureContext) :
    ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  (returnLeafFromCounts ctx (data.returnCounts.densePack ctx)
    (data.returnCounts.olcSlotSmall ctx)).toReturnSeparatedLocalLeafInputData

/-- The Run separated leaf reconstructed from the §26/I.4.1 high-excess cover. -/
def run (data : GlobalAssemblyActualProofV4StrictCNLLeafInputs)
    (ctx : ActualFailureContext) :
    RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  runSeparatedLocalLeafOfShellOfCover ctx (data.runCover ctx)

/-- Rebuild the exact proof-v4 phase package after installing strict CNL. -/
def phases (data : GlobalAssemblyActualProofV4StrictCNLLeafInputs)
    (ctx : ActualFailureContext) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : Real) :=
  actualProofV4LeafPhases ctx (data.chernoff ctx) (data.cnl ctx)
    (data.densePack ctx) (data.dirtyMultiplicity ctx) (data.tower ctx)
    (data.returnPkg ctx) (data.run ctx)

/-- The proof-v4 aligned grounded high-excess datum, rewritten to the named
strict-CNL phase package.  This is the Appendix I/N data still missing at the
current boundary. -/
def highExcessGroundedData
    (data : GlobalAssemblyActualProofV4StrictCNLLeafInputs)
    (ctx : ActualFailureContext) :
    GroundedHighExcessLocalData (data.phases ctx) (data.carryData ctx) := by
  simpa [proofV4StrictCNLLeafPhase, phases, carryData, chernoff, cnl,
    densePack, dirtyMultiplicity, tower, returnPkg, run]
    using (data.highExcessBranchMass ctx).toGroundedHighExcessLocalData

/-- Convert the grounded Appendix I/N high-excess datum to the legacy
`HighExcessChargeData` field consumed by the existing final assembly. -/
def highExcessCharge
    (data : GlobalAssemblyActualProofV4StrictCNLLeafInputs)
    (ctx : ActualFailureContext) :
    HighExcessChargeData (data.phases ctx) (data.carryData ctx) :=
  (data.highExcessGroundedData ctx).toHighExcessChargeData

/-- Project the strict-CNL proof-v4 leaf surface to the existing proof-v4 leaf
surface by filling its CNL field with `cnlStrictWeightedKraftShellProvider`. -/
def toProofV4LeafInputs
    (data : GlobalAssemblyActualProofV4StrictCNLLeafInputs) :
    GlobalAssemblyActualProofV4LeafInputs where
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  dirtyMultiplicity := data.dirtyMultiplicity
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  carryData := data.carryData
  highExcessCharge := data.highExcessCharge

end GlobalAssemblyActualProofV4StrictCNLLeafInputs

/-- Final theorem bridge from the proof-v4 leaf surface with strict CNL
installed. -/
theorem erdos260_final_actual_proofV4_strictCNL_leaf
    (data : GlobalAssemblyActualProofV4StrictCNLLeafInputs) :
    Erdos260Statement :=
  erdos260_final_actual_proofV4_leaf data.toProofV4LeafInputs

/-- A nonempty strict-CNL proof-v4 leaf provider proves the final theorem. -/
theorem erdos260_unconditional_from_proofV4_strictCNL_leaf_provider
    (hprovider :
      Nonempty GlobalAssemblyActualProofV4StrictCNLLeafInputs) :
    Erdos260Statement :=
  hprovider.elim erdos260_final_actual_proofV4_strictCNL_leaf

/-- Nonemptiness of the strict-CNL proof-v4 leaf surface inhabits the existing
proof-v4 leaf provider boundary. -/
theorem proofV4_leaf_provider_nonempty_of_strictCNL_leaf_provider
    (hprovider :
      Nonempty GlobalAssemblyActualProofV4StrictCNLLeafInputs) :
    Nonempty GlobalAssemblyActualProofV4LeafInputs := by
  exact hprovider.elim fun data =>
    Nonempty.intro data.toProofV4LeafInputs

/-- Nonemptiness of the strict-CNL proof-v4 leaf surface gives the final
actual-consumption assembly object. -/
theorem globalAssemblyActualInputs_nonempty_of_proofV4_strictCNL_leaf_provider
    (hprovider :
      Nonempty GlobalAssemblyActualProofV4StrictCNLLeafInputs) :
    Nonempty GlobalAssemblyActualInputs :=
  globalAssemblyActualInputs_nonempty_of_proofV4_leaf_provider
    (proofV4_leaf_provider_nonempty_of_strictCNL_leaf_provider hprovider)

/-- The strict-CNL proof-v4 surface supplies the current actual CNL column
without any sibling leaf data. -/
theorem actualCNLWeightedKraftData_nonempty_of_proofV4_strictCNL_leaf_provider
    (_hprovider :
      Nonempty GlobalAssemblyActualProofV4StrictCNLLeafInputs) :
    Nonempty (forall ctx : ActualFailureContext,
      ActualCNLWeightedKraftData ctx) :=
  actualCNLWeightedKraftData_nonempty_of_strictShellProvider

/-- The strict-CNL proof-v4 surface projects its separated Return leaf to the
current actual Return split-scalar field. -/
theorem actualReturnSplit_nonempty_of_proofV4_strictCNL_leaf_provider
    (hprovider :
      Nonempty GlobalAssemblyActualProofV4StrictCNLLeafInputs) :
    Nonempty
      (forall ctx : ActualFailureContext,
        ActualReturnRawI51M2J4L6SplitScalarData ctx) := by
  exact hprovider.elim fun data =>
    Nonempty.intro fun ctx =>
      ActualReturnRawI51M2J4L6SplitScalarData.ofSeparatedLeaf
        (data.returnPkg ctx)

/-- The strict-CNL proof-v4 surface projects its separated Run leaf to the
current actual Run split/absorption field. -/
theorem actualRunSplit_nonempty_of_proofV4_strictCNL_leaf_provider
    (hprovider :
      Nonempty GlobalAssemblyActualProofV4StrictCNLLeafInputs) :
    Nonempty
      (forall ctx : ActualFailureContext,
        ActualRunRawL41L42I52SplitAbsorptionScalarData ctx) := by
  exact hprovider.elim fun data =>
    Nonempty.intro fun ctx =>
      ActualRunRawL41L42I52SplitAbsorptionScalarData.ofSeparatedLeaf
        (data.run ctx)

/-- The canonical actual-support DensePack leaf is inhabited at the strict-CNL
proof-v4 surface without using any sibling provider field. -/
theorem actualDensePack_nonempty_of_proofV4_strictCNL_leaf_provider
    (_hprovider :
      Nonempty GlobalAssemblyActualProofV4StrictCNLLeafInputs) :
    Nonempty
      (forall ctx : ActualFailureContext,
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (ctx.shell.X : Real)) := by
  exact Nonempty.intro fun ctx =>
    appendixNGapCanonicalYActualDensePackToGrounded
      ctx.shell ctx.hc0Small ctx.shell_startThreshold_le

/-- The canonical N.24 carry datum is inhabited at the strict-CNL proof-v4
surface without using any sibling provider field. -/
theorem actualCarryData_nonempty_of_proofV4_strictCNL_leaf_provider
    (_hprovider :
      Nonempty GlobalAssemblyActualProofV4StrictCNLLeafInputs) :
    Nonempty
      (forall ctx : ActualFailureContext,
        CarryDataFromFailure ctx.shell erdos260Constants.cPr) := by
  exact Nonempty.intro fun ctx => ctx.n24CarryData

/-- The faithful K.2.5 dirty-multiplicity leaf is inhabited at the strict-CNL
proof-v4 surface without using any sibling provider field. -/
theorem actualDirtyMultiplicity_nonempty_of_proofV4_strictCNL_leaf_provider
    (_hprovider :
      Nonempty GlobalAssemblyActualProofV4StrictCNLLeafInputs) :
    Nonempty
      (forall _ctx : ActualFailureContext, DirtyMultiplicityData) := by
  exact Nonempty.intro fun ctx => faithfulDirtyData ctx

/-- The formalized §22 model Chernoff leaf is inhabited at the strict-CNL
proof-v4 surface without using any sibling provider field. -/
theorem actualChernoff_nonempty_of_proofV4_strictCNL_leaf_provider
    (_hprovider :
      Nonempty GlobalAssemblyActualProofV4StrictCNLLeafInputs) :
    Nonempty
      (forall ctx : ActualFailureContext,
        RegularShellPaidChernoff22_1AInputData erdos260Constants.cStar
          erdos260Constants.ξ (ctx.shell.X : Real)) := by
  exact Nonempty.intro fun ctx => chernoff22_1ALeafOfShell ctx

/-- Free proof-v4 leaf fields after the Chernoff, strict CNL, faithful dirty,
DensePack, carry, and Tower/Return/Run leaf constructors have filled their
slots.  These are the remaining manuscript residuals at the Appendix N proof-v4
surface, not new assumptions added to the theorem. -/
def erdos260ProofV4StrictCNLLeafFields : List String :=
  [ "TowerHall: forall ctx, Class2HallIndexSDRResidual ctx",
    "ReturnCounts: ReturnCountsResidual",
    "RunCover: forall ctx, RunHighExcessAreaCover ctx",
    "HighExcessBranchMass: forall ctx, BranchMassGroundedHighExcessLocalData (strict-CNL proof-v4 phase ctx) ctx.n24CarryData" ]

theorem erdos260ProofV4StrictCNLLeafFields_length :
    erdos260ProofV4StrictCNLLeafFields.length = 4 := by
  rfl

/-- The fields removed from the proof-v4 leaf surface by this bridge. -/
def erdos260ProofV4StrictCNLLeafInstalledFields : List String :=
  [ "Chernoff: forall ctx, chernoff22_1ALeafOfShell ctx",
    "CNL: forall ctx, cnlStrictWeightedKraftShellProvider ctx.shell ctx.hc0Small ctx.shell_startThreshold_le",
    "DirtyMultiplicity: forall ctx, faithfulDirtyData ctx",
    "DensePack: forall ctx, appendixNGapCanonicalYActualDensePackToGrounded ctx.shell ctx.hc0Small ctx.shell_startThreshold_le",
    "CarryData: forall ctx, ActualFailureContext.n24CarryData ctx",
    "Tower leaf: towerSeparatedLocalLeafProviderOfHallResidual towerHall ctx",
    "Return leaf: returnLeafFromCounts ctx returnCounts.densePack returnCounts.olcSlotSmall",
    "Run leaf: runSeparatedLocalLeafOfShellOfCover ctx runCover",
    "HighExcessCharge projection: BranchMassGroundedHighExcessLocalData.toGroundedHighExcessLocalData.toHighExcessChargeData" ]

theorem erdos260ProofV4StrictCNLLeafInstalledFields_length :
    erdos260ProofV4StrictCNLLeafInstalledFields.length = 9 := by
  rfl

/-- Remaining Tower residual after `TowerActiveFloorClosure` has reduced the
separated Tower leaf to the Hall-marginal class-2 SDR surface. -/
def erdos260ProofV4StrictCNLLeafTowerHallOpenItems : List String :=
  [ "construct Class2HallIndexSDRResidual for every actual failure context: hit-index descent windows, landing in the support shell, a positive rhoD*L block floor, and the Hall marginal union bound on the real class-2 fibre" ]

theorem erdos260ProofV4StrictCNLLeafTowerHallOpenItems_length :
    erdos260ProofV4StrictCNLLeafTowerHallOpenItems.length = 1 := by
  rfl

/-- The proof-v4 strict-CNL leaf now asks for the branch-mass-normalized Appendix I/N central
charge data, then projects it to the legacy `HighExcessChargeData` slot by the
already-proved route in `GlobalHighExcessAssembly`. -/
def erdos260ProofV4StrictCNLLeafHighExcessOpenItems : List String :=
  [ "construct BranchMassGroundedHighExcessLocalData for every actual strict-CNL proof-v4 phase and ActualFailureContext.n24CarryData, including the N.2.1/N.2.2 window-drop package and phase-mass absorptions; the I.9 branch mass is then definitional" ]

theorem erdos260ProofV4StrictCNLLeafHighExcessOpenItems_length :
    erdos260ProofV4StrictCNLLeafHighExcessOpenItems.length = 1 := by
  rfl

/-- Remaining Return residuals after the M.2.1/J.4/K.4 count bridge has built
the separated Return leaf internally. -/
def erdos260ProofV4StrictCNLLeafReturnCountsOpenItems : List String :=
  [ "construct ReturnCountsResidual.densePack: returnHighExcessMass ctx <= manuscriptCstarSmall * X",
    "construct ReturnCountsResidual.olcSlotSmall: 2 * liftLevelBound X <= cStar * ξ * X / 12" ]

theorem erdos260ProofV4StrictCNLLeafReturnCountsOpenItems_length :
    erdos260ProofV4StrictCNLLeafReturnCountsOpenItems.length = 2 := by
  rfl

/-- Remaining Run residual after `RunL4I52Core` has reduced the separated Run
leaf to the genuine §26/I.4.1 cover datum. -/
def erdos260ProofV4StrictCNLLeafRunCoverOpenItems : List String :=
  [ "construct RunHighExcessAreaCover for every actual failure context: K.1.2/L.20 multiplier, K.1.1 cover, I.4.1 packing, and K.4 smallness" ]

theorem erdos260ProofV4StrictCNLLeafRunCoverOpenItems_length :
    erdos260ProofV4StrictCNLLeafRunCoverOpenItems.length = 1 := by
  rfl

/-- Field-level audit for the proof-v4 leaf surface after Chernoff, CNL,
DirtyMultiplicity, DensePack, CarryData, and the Return/Run leaf constructors
have been installed by
actual-context providers.  These rows align
with the remaining fields of
`GlobalAssemblyActualProofV4StrictCNLLeafInputs`. -/
def erdos260ProofV4StrictCNLLeafFieldAudits :
    List Erdos260CurrentActualProviderFieldAudit :=
  [ { slot := "Tower"
      target :=
        "forall ctx, Class2HallIndexSDRResidual ctx"
      connectedProjection :=
        "towerSeparatedLocalLeafProviderOfHallResidual builds the proof-v4 Tower separated leaf via Class2IndexSDR.ofWindowsHall"
      sourceModule := "TowerActiveFloorClosure / SDRSelectionCore / TowerLocalLeafConstruction"
      remainingData :=
        "Hall-marginal hit-index window data for the real class-2 fibre"
      openItems := erdos260ProofV4StrictCNLLeafTowerHallOpenItems },
    { slot := "Return"
      target :=
        "ReturnCountsResidual"
      connectedProjection :=
        "returnLeafFromCounts builds the proof-v4 Return separated leaf and the current actual Return split"
      sourceModule := "ReturnCountsCore / ReturnM2J4Core / ReturnLocalLeafConstruction"
      remainingData :=
        "dense-pack high-excess mass bound and OLC inverse-tower smallness"
      openItems := erdos260ProofV4StrictCNLLeafReturnCountsOpenItems },
    { slot := "Run"
      target :=
        "forall ctx, RunHighExcessAreaCover ctx"
      connectedProjection :=
        "runSeparatedLocalLeafOfShellOfCover builds the proof-v4 Run separated leaf and the current actual Run split"
      sourceModule := "RunL4I52Core / RunLocalLeafConstruction"
      remainingData :=
        "§26/I.4.1 high-excess run-area cover with multiplier, cover, packing, and smallness"
      openItems := erdos260ProofV4StrictCNLLeafRunCoverOpenItems },
    { slot := "HighExcessBranchMass"
      target :=
        "forall ctx, BranchMassGroundedHighExcessLocalData (proofV4StrictCNLLeafPhase towerHall returnCounts runCover ctx) ctx.n24CarryData"
      connectedProjection :=
        "highExcessBranchMass.toGroundedHighExcessLocalData.toHighExcessChargeData supplies the proof-v4 highExcessCharge field consumed by GlobalAssemblyActualProofV4LeafInputs.toActualInputs"
      sourceModule := "AppendixN_Closure / AppendixI_PhaseMass / GlobalHighExcessAssembly"
      remainingData :=
        "instantiate the branch-mass-normalized central-charge bridge on the strict-CNL proof-v4 phase package and canonical N.24 carry data"
      openItems := erdos260ProofV4StrictCNLLeafHighExcessOpenItems } ]

theorem erdos260ProofV4StrictCNLLeafFieldAudits_length :
    erdos260ProofV4StrictCNLLeafFieldAudits.length = 4 := by
  rfl

/-- TeX-facing row for the four fields that remain at the proof-v4 strict-CNL
leaf boundary.  This is the compact TeX--Lean correspondence table for the
current reduced boundary: every row is still `partial`, and every row names the
next manuscript object that must be supplied before the field can be removed. -/
structure Erdos260ProofV4StrictCNLLeafTexAudit where
  gapId : String
  texSource : String
  mathObject : String
  leanBoundary : String
  status : String
  dependency : String
  nextStep : String

/-- TeX--Lean map for the four external fields of
`GlobalAssemblyActualProofV4StrictCNLLeafInputs`.

The labels refer to `erdos260_short.tex` and `erdos260.tex`.  They deliberately
separate the local TRT leaves (Tower/Return/Run) from the central branch-mass
HighExcess bridge, because the latter must be instantiated on the exact
strict-CNL phase package after the local leaves are real. -/
def erdos260ProofV4StrictCNLLeafTexLeanAudit :
    List Erdos260ProofV4StrictCNLLeafTexAudit :=
  [ { gapId := "PV4-strictCNL-Tower"
      texSource :=
        "erdos260_short.tex: lem:output-map-tower, lem:tower-simple-cycle, " ++
        "lem:tower-fe-ex-estimate, lem:tower-transient-excursion, " ++
        "lem:package-tower; erdos260.tex: D.3/G.3 tower closure"
      mathObject :=
        "Hall-marginal Class-2 index-SDR residual that constructs the proof-v4 TRT Tower leaf"
      leanBoundary :=
        "forall ctx, Class2HallIndexSDRResidual ctx"
      status := "partial"
      dependency :=
        "TowerActiveFloorClosure.towerSeparatedLocalLeafProviderOfHallResidual; SDRSelectionCore.Class2IndexSDR.ofWindowsHall; TowerLocalLeafConstruction"
      nextStep :=
        "construct Class2HallIndexSDRResidual for every actual failure context: hit-index descent windows, support-shell landing, positive rhoD*L block floor, and Hall marginal union bound" },
    { gapId := "PV4-strictCNL-Return"
      texSource :=
        "erdos260_short.tex: lem:output-map-return, " ++
        "lem:return-output-estimate, lem:package-return; " ++
        "erdos260.tex: D.5 return descent and G.2.2 return summability"
      mathObject :=
        "Return-count residual that constructs the ordinary-short, semiperiodic, OLC, and nonlocal-long Return leaf"
      leanBoundary :=
        "ReturnCountsResidual"
      status := "partial"
      dependency :=
        "ReturnCountsCore.returnLeafFromCounts; ReturnM2J4Core; ReturnLocalLeafConstruction"
      nextStep :=
        "construct the dense-pack high-excess mass bound and OLC inverse-tower smallness fields of ReturnCountsResidual" },
    { gapId := "PV4-strictCNL-Run"
      texSource :=
        "erdos260_short.tex: def:run-trichotomy, lem:output-map-run, " ++
        "lem:run-shortening-potential, lem:package-run; " ++
        "erdos260.tex: D.5.2 and G.4 run trichotomy/descent"
      mathObject :=
        "Run high-excess area cover from which the L.4.1/L.4.2/I.5.2 Run leaf is constructed"
      leanBoundary :=
        "forall ctx, RunHighExcessAreaCover ctx"
      status := "partial"
      dependency :=
        "RunL4I52Core.runSeparatedLocalLeafOfShellOfCover; RunLocalLeafConstruction"
      nextStep :=
        "construct the §26/I.4.1 cover data: K.1.2/L.20 multiplier, K.1.1 cover, I.4.1 packing, and K.4 smallness" },
    { gapId := "PV4-strictCNL-HighExcessBranchMass"
      texSource :=
        "erdos260_short.tex: prop:compressed-rrt-budget and " ++
        "Return--Run--Tower compression; erdos260.tex: Appendix I/D phase-mass " ++
        "bridge and § Rolling-window variation-drop closure"
      mathObject :=
        "Branch-mass-normalized Appendix I/N high-excess data for the exact strict-CNL proof-v4 phase package and canonical N.24 carry data"
      leanBoundary :=
        "forall ctx, BranchMassGroundedHighExcessLocalData (proofV4StrictCNLLeafPhase towerHall returnCounts runCover ctx) ctx.n24CarryData"
      status := "partial"
      dependency :=
        "GlobalHighExcessAssembly.BranchMassGroundedHighExcessLocalData.toGroundedHighExcessLocalData; GroundedHighExcessLocalData.toHighExcessChargeData; AppendixN_Closure; AppendixI_PhaseMass"
      nextStep :=
        "instantiate the window-drop/phase-mass charge bridge on the strict-CNL phases after Tower/Return/Run have been constructed from real manuscript data" } ]

theorem erdos260ProofV4StrictCNLLeafTexLeanAudit_length :
    erdos260ProofV4StrictCNLLeafTexLeanAudit.length = 4 := by
  rfl

/-- Status vector for the TeX--Lean proof-v4 strict-CNL field audit. -/
theorem erdos260ProofV4StrictCNLLeafTexLeanAudit_statuses :
    erdos260ProofV4StrictCNLLeafTexLeanAudit.map (fun row => row.status) =
      ["partial", "partial", "partial", "partial"] := by
  rfl

/-- Field-level open-item counts for the proof-v4 strict-CNL leaf boundary. -/
theorem erdos260ProofV4StrictCNLLeafOpenItemCounts :
    erdos260ProofV4StrictCNLLeafFieldAudits.map
        (fun row => row.openItems.length) =
      [1, 2, 1, 1] := by
  rfl

/-- Total field-level open items at the proof-v4 strict-CNL leaf boundary. -/
theorem erdos260ProofV4StrictCNLLeafOpenItemCount_sum :
    (erdos260ProofV4StrictCNLLeafFieldAudits.map
        (fun row => row.openItems.length)).sum = 5 := by
  rfl

/-- Flattened field-level checklist for the proof-v4 strict-CNL leaf boundary. -/
def erdos260ProofV4StrictCNLLeafOpenItems : List String :=
  erdos260ProofV4StrictCNLLeafFieldAudits.flatMap (fun row => row.openItems)

theorem erdos260ProofV4StrictCNLLeafOpenItems_length_eq_sum :
    erdos260ProofV4StrictCNLLeafOpenItems.length =
      (erdos260ProofV4StrictCNLLeafFieldAudits.map
        (fun row => row.openItems.length)).sum := by
  simp [erdos260ProofV4StrictCNLLeafOpenItems]

theorem erdos260ProofV4StrictCNLLeafOpenItems_length :
    erdos260ProofV4StrictCNLLeafOpenItems.length = 5 := by
  rw [erdos260ProofV4StrictCNLLeafOpenItems_length_eq_sum,
    erdos260ProofV4StrictCNLLeafOpenItemCount_sum]

/-- Proof-v4 strict-CNL leaf readiness means that all four remaining provider
fields have been supplied by real manuscript data. -/
def erdos260ProofV4StrictCNLLeafReady : Prop :=
  erdos260ProofV4StrictCNLLeafOpenItems = []

theorem erdos260ProofV4StrictCNLLeaf_not_ready :
    Not erdos260ProofV4StrictCNLLeafReady := by
  intro h
  have hlen := congrArg List.length h
  simp [erdos260ProofV4StrictCNLLeafOpenItems_length] at hlen

/-- The five manuscript data columns still needed after the strict CNL bridge
has filled the current CNL slot. -/
def erdos260StrictCNLCurrentProviderFieldAudits :
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
        "forall ctx, ActualRawN2FirstCrossingData ctx (termRun (strict-CNL actual phase ctx))"
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

theorem erdos260StrictCNLCurrentProviderFieldAudits_length :
    erdos260StrictCNLCurrentProviderFieldAudits.length = 5 := by
  rfl

/-- Open-item counts after the strict CNL current-provider bridge. -/
theorem erdos260StrictCNLCurrentProviderOpenItemCounts :
    erdos260StrictCNLCurrentProviderFieldAudits.map
        (fun row => row.openItems.length) =
      [4, 4, 4, 4, 7] := by
  rfl

/-- Total named open leaf items after the strict CNL bridge. -/
theorem erdos260StrictCNLCurrentProviderOpenItemCount_sum :
    (erdos260StrictCNLCurrentProviderFieldAudits.map
        (fun row => row.openItems.length)).sum = 23 := by
  rfl

/-- Flattened low-level checklist for the strict-CNL current provider boundary. -/
def erdos260StrictCNLCurrentProviderOpenItems : List String :=
  erdos260StrictCNLCurrentProviderFieldAudits.flatMap (fun row => row.openItems)

theorem erdos260StrictCNLCurrentProviderOpenItems_length_eq_sum :
    erdos260StrictCNLCurrentProviderOpenItems.length =
      (erdos260StrictCNLCurrentProviderFieldAudits.map
        (fun row => row.openItems.length)).sum := by
  simp [erdos260StrictCNLCurrentProviderOpenItems]

theorem erdos260StrictCNLCurrentProviderOpenItems_length :
    erdos260StrictCNLCurrentProviderOpenItems.length = 23 := by
  rw [erdos260StrictCNLCurrentProviderOpenItems_length_eq_sum,
    erdos260StrictCNLCurrentProviderOpenItemCount_sum]

/-- The strict-CNL reduced endpoint still has the same final no-input
installation tasks as the upstream current-provider boundary. -/
def erdos260StrictCNLCurrentEndpointOpenItems : List String :=
  erdos260StrictCNLCurrentProviderOpenItems ++
    erdos260CurrentActualNoInputOpenItems

theorem erdos260StrictCNLCurrentEndpointOpenItems_length :
    erdos260StrictCNLCurrentEndpointOpenItems.length = 26 := by
  simp [erdos260StrictCNLCurrentEndpointOpenItems,
    erdos260StrictCNLCurrentProviderOpenItems_length,
    erdos260CurrentActualNoInputOpenItems_length]

/-- Current no-input endpoint readiness after installing strict CNL. -/
def erdos260StrictCNLCurrentEndpointReady : Prop :=
  erdos260StrictCNLCurrentEndpointOpenItems = []

theorem erdos260StrictCNLCurrentEndpoint_not_ready :
    Not erdos260StrictCNLCurrentEndpointReady := by
  intro h
  have hlen := congrArg List.length h
  simp [erdos260StrictCNLCurrentEndpointOpenItems_length] at hlen

#print axioms erdos260_final_actual_strictCNLCurrentProvider
#print axioms erdos260_unconditional_from_strictCNL_current_provider
#print axioms current_actual_provider_nonempty_of_strictCNL_current_provider
#print axioms globalAssemblyActualInputs_nonempty_of_strictCNL_current_provider
#print axioms erdos260_final_actual_proofV4_strictCNL_leaf
#print axioms erdos260_unconditional_from_proofV4_strictCNL_leaf_provider
#print axioms proofV4_leaf_provider_nonempty_of_strictCNL_leaf_provider
#print axioms globalAssemblyActualInputs_nonempty_of_proofV4_strictCNL_leaf_provider
#print axioms actualCNLWeightedKraftData_nonempty_of_proofV4_strictCNL_leaf_provider
#print axioms actualReturnSplit_nonempty_of_proofV4_strictCNL_leaf_provider
#print axioms actualRunSplit_nonempty_of_proofV4_strictCNL_leaf_provider
#print axioms actualDensePack_nonempty_of_proofV4_strictCNL_leaf_provider
#print axioms actualCarryData_nonempty_of_proofV4_strictCNL_leaf_provider
#print axioms actualDirtyMultiplicity_nonempty_of_proofV4_strictCNL_leaf_provider
#print axioms actualChernoff_nonempty_of_proofV4_strictCNL_leaf_provider

end

end Erdos260
