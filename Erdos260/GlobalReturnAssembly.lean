import Mathlib
import Erdos260.GlobalCNLAssembly

/-!
# Global return assembly

This module grounds one piece of the Return phase.  The four-piece
Proposition 23.1 certificate is carried in its proof-v4 split form, with the
ordinary-local-long endpoint contribution nested through the M.2 endpoint
multiplicity estimate.
-/

namespace Erdos260

noncomputable section

/-- M.2 ordinary-local-long endpoint multiplicity estimate. -/
structure ReturnOLCMultiplicityData
    (olc ML X ij epsilonTerm : Real) where
  multiplicity :
    olc <= ML * X * ij + epsilonTerm

/-- M.2 small error half-budget for the ordinary-local-long endpoint term. -/
structure ReturnOLCEpsilonData (epsilonTerm s X ij : Real) where
  epsilon :
    epsilonTerm <= s * X * ij / 2

/-- M.2 `M_L` half-budget for ordinary-local-long endpoint multiplicity. -/
structure ReturnOLCMLBudgetData (ML X ij s : Real) where
  ML_budget :
    ML * X * ij <= s * X * ij / 2

/-- M.2/Prop. 23.1 return-slot budget for the OLC contribution. -/
structure ReturnOLCReturnBudgetData (s X ij c3 xi smallError : Real) where
  return_budget :
    s * X * ij <= c3 * xi * s * X * ij + smallError / 4

/-- M.2 ordinary-local-long endpoint multiplicity certificate in the return slot. -/
structure ReturnOLCData
    (olc ML X ij epsilonTerm s c3 xi smallError : Real) where
  multiplicityData :
    ReturnOLCMultiplicityData olc ML X ij epsilonTerm
  epsilonData :
    ReturnOLCEpsilonData epsilonTerm s X ij
  MLBudgetData :
    ReturnOLCMLBudgetData ML X ij s
  returnBudgetData :
    ReturnOLCReturnBudgetData s X ij c3 xi smallError

namespace ReturnOLCData

/-- M.2-grounded OLC contribution in the exact L.2.2 return-package shape. -/
theorem bound
    {olc ML X ij epsilonTerm s c3 xi smallError : Real}
    (data : ReturnOLCData olc ML X ij epsilonTerm s c3 xi smallError) :
    olc <= c3 * xi * s * X * ij + smallError / 4 :=
  (corollaryM2_2_OLCEndpointMultiplicity
    data.multiplicityData.multiplicity data.epsilonData.epsilon
    data.MLBudgetData.ML_budget).trans
    data.returnBudgetData.return_budget

end ReturnOLCData

/-- L.2.2 ordinary short non-run return bound. -/
structure ReturnOrdinaryShortData
    (ordinaryShort c1 xi s X ij smallError : Real) where
  ordinaryShort_bound :
    ordinaryShort <= c1 * xi * s * X * ij + smallError / 4

/-- L.2.2 semiperiodic short non-run return bound. -/
structure ReturnSemiperiodicShortData
    (semiperiodic c2 xi s X ij smallError : Real) where
  semiperiodic_bound :
    semiperiodic <= c2 * xi * s * X * ij + smallError / 4

/-- L.2.2 ordinary and semiperiodic short-return bounds. -/
structure ReturnShortPiecesData
    (ordinaryShort semiperiodic : Real)
    (c1 c2 xi s X ij smallError : Real) where
  ordinary :
    ReturnOrdinaryShortData ordinaryShort c1 xi s X ij smallError
  semiperiodicData :
    ReturnSemiperiodicShortData semiperiodic c2 xi s X ij smallError

namespace ReturnShortPiecesData

/-- Project the ordinary short-return bound from the split short-piece certificate. -/
theorem ordinaryShort_bound
    {ordinaryShort semiperiodic c1 c2 xi s X ij smallError : Real}
    (data :
      ReturnShortPiecesData ordinaryShort semiperiodic c1 c2 xi s X ij
        smallError) :
    ordinaryShort <= c1 * xi * s * X * ij + smallError / 4 :=
  data.ordinary.ordinaryShort_bound

/-- Project the semiperiodic short-return bound from the split short-piece certificate. -/
theorem semiperiodic_bound
    {ordinaryShort semiperiodic c1 c2 xi s X ij smallError : Real}
    (data :
      ReturnShortPiecesData ordinaryShort semiperiodic c1 c2 xi s X ij
        smallError) :
    semiperiodic <= c2 * xi * s * X * ij + smallError / 4 :=
  data.semiperiodicData.semiperiodic_bound

end ReturnShortPiecesData

/-- L.2.2 nonlocal long-return bound. -/
structure ReturnNonlocalLongData
    (nonlocalLong c4 xi s X ij smallError : Real) where
  nonlocalLong_bound :
    nonlocalLong <= c4 * xi * s * X * ij + smallError / 4

/-- Proposition 23.1 four-piece return package certificate. -/
structure ReturnFourPieceData
    (ordinaryShort semiperiodic olc nonlocalLong : Real)
    (c1 c2 c3 c4 xi s X ij smallError ML epsilonTerm : Real) where
  shortPieces :
    ReturnShortPiecesData ordinaryShort semiperiodic c1 c2 xi s X ij smallError
  olcData : ReturnOLCData olc ML X ij epsilonTerm s c3 xi smallError
  nonlocalLongData :
    ReturnNonlocalLongData nonlocalLong c4 xi s X ij smallError

namespace ReturnFourPieceData

/-- Project the ordinary short-return bound from the short-piece certificate. -/
theorem ordinaryShort_bound
    {ordinaryShort semiperiodic olc nonlocalLong : Real}
    {c1 c2 c3 c4 xi s X ij smallError ML epsilonTerm : Real}
    (data :
      ReturnFourPieceData ordinaryShort semiperiodic olc nonlocalLong
        c1 c2 c3 c4 xi s X ij smallError ML epsilonTerm) :
    ordinaryShort <= c1 * xi * s * X * ij + smallError / 4 :=
  data.shortPieces.ordinaryShort_bound

/-- Project the semiperiodic short-return bound from the short-piece certificate. -/
theorem semiperiodic_bound
    {ordinaryShort semiperiodic olc nonlocalLong : Real}
    {c1 c2 c3 c4 xi s X ij smallError ML epsilonTerm : Real}
    (data :
      ReturnFourPieceData ordinaryShort semiperiodic olc nonlocalLong
        c1 c2 c3 c4 xi s X ij smallError ML epsilonTerm) :
    semiperiodic <= c2 * xi * s * X * ij + smallError / 4 :=
  data.shortPieces.semiperiodic_bound

/-- Project the nonlocal long-return bound. -/
theorem nonlocalLong_bound
    {ordinaryShort semiperiodic olc nonlocalLong : Real}
    {c1 c2 c3 c4 xi s X ij smallError ML epsilonTerm : Real}
    (data :
      ReturnFourPieceData ordinaryShort semiperiodic olc nonlocalLong
        c1 c2 c3 c4 xi s X ij smallError ML epsilonTerm) :
    nonlocalLong <= c4 * xi * s * X * ij + smallError / 4 :=
  data.nonlocalLongData.nonlocalLong_bound

/-- Build the four-piece Return certificate directly from the three elementary
piece bounds and the M.2 OLC endpoint-multiplicity data. -/
def ofOLCMultiplicity
    {ordinaryShort semiperiodic olc nonlocalLong : Real}
    {c1 c2 c3 c4 xi s X ij smallError ML epsilonTerm : Real}
    (ordinaryShort_bound :
      ordinaryShort <= c1 * xi * s * X * ij + smallError / 4)
    (semiperiodic_bound :
      semiperiodic <= c2 * xi * s * X * ij + smallError / 4)
    (olc_multiplicity :
      olc <= ML * X * ij + epsilonTerm)
    (olc_epsilon :
      epsilonTerm <= s * X * ij / 2)
    (olc_ML_budget :
      ML * X * ij <= s * X * ij / 2)
    (olc_return_budget :
      s * X * ij <= c3 * xi * s * X * ij + smallError / 4)
    (nonlocalLong_bound :
      nonlocalLong <= c4 * xi * s * X * ij + smallError / 4) :
    ReturnFourPieceData ordinaryShort semiperiodic olc nonlocalLong
      c1 c2 c3 c4 xi s X ij smallError ML epsilonTerm where
  shortPieces := {
    ordinary := { ordinaryShort_bound := ordinaryShort_bound }
    semiperiodicData := { semiperiodic_bound := semiperiodic_bound } }
  olcData := {
    multiplicityData := { multiplicity := olc_multiplicity }
    epsilonData := { epsilon := olc_epsilon }
    MLBudgetData := { ML_budget := olc_ML_budget }
    returnBudgetData := { return_budget := olc_return_budget } }
  nonlocalLongData := {
    nonlocalLong_bound := nonlocalLong_bound }

/-- The M.2 OLC piece as one of the four Proposition 23.1 bounds. -/
theorem olc_bound
    {ordinaryShort semiperiodic olc nonlocalLong : Real}
    {c1 c2 c3 c4 xi s X ij smallError ML epsilonTerm : Real}
    (data :
      ReturnFourPieceData ordinaryShort semiperiodic olc nonlocalLong
        c1 c2 c3 c4 xi s X ij smallError ML epsilonTerm) :
    olc <= c3 * xi * s * X * ij + smallError / 4 :=
  data.olcData.bound

/-- Proposition 23.1 linear return-package combination. -/
theorem linear_bound
    {ordinaryShort semiperiodic olc nonlocalLong : Real}
    {c1 c2 c3 c4 xi s X ij smallError ML epsilonTerm : Real}
    (data :
      ReturnFourPieceData ordinaryShort semiperiodic olc nonlocalLong
        c1 c2 c3 c4 xi s X ij smallError ML epsilonTerm) :
    ordinaryShort + semiperiodic + olc + nonlocalLong <=
      (c1 + c2 + c3 + c4) * xi * s * X * ij + smallError :=
  proposition23_1_returnPackagesLowerClean
    data.ordinaryShort_bound data.semiperiodic_bound data.olc_bound
    data.nonlocalLong_bound

end ReturnFourPieceData

/--
Proof-v4 aligned Return local data.

The four return pieces are supplied in the proof-v4 split form as a
`ReturnFourPieceData` certificate.  Its OLC component is grounded through
`corollaryM2_2_OLCEndpointMultiplicity`.
-/
structure GroundedReturnLocalData (cStar xi X : Real) where
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
  returnPackage_input :
    ReturnFourPieceData ordinaryShort semiperiodic olc nonlocalLong
      c1 c2 c3 c4 xi s X ij smallError ML epsilonTerm
  hSmall :
    (c1 + c2 + c3 + c4) * xi * s * X * ij + smallError <= cStar * xi * X / 6

/--
Prop. 23.1/M.2 return leaf before it is packed as grounded Return local data:
short-return, OLC, and nonlocal-long certificates remain separate.
-/
structure ReturnLocalLeafInputData (cStar xi X : Real) where
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
    ReturnShortPiecesData ordinaryShort semiperiodic c1 c2 xi s X ij smallError
  olcData :
    ReturnOLCData olc ML X ij epsilonTerm s c3 xi smallError
  nonlocalLongData :
    ReturnNonlocalLongData nonlocalLong c4 xi s X ij smallError
  hSmall :
    (c1 + c2 + c3 + c4) * xi * s * X * ij + smallError <= cStar * xi * X / 6

/-- Proposition 23.1 / I.5.1 final scalar smallness comparison for Return. -/
structure ReturnSmallnessInputData
    (cStar xi X c1 c2 c3 c4 s ij smallError : Real) where
  hSmall :
    (c1 + c2 + c3 + c4) * xi * s * X * ij + smallError <= cStar * xi * X / 6

/--
Prop. 23.1/M.2 return leaf with the four-piece return package and the final
scalar smallness comparison kept as separate proof-v4 inputs.
-/
structure ReturnSeparatedLocalLeafInputData (cStar xi X : Real) where
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
    ReturnShortPiecesData ordinaryShort semiperiodic c1 c2 xi s X ij smallError
  olcData :
    ReturnOLCData olc ML X ij epsilonTerm s c3 xi smallError
  nonlocalLongData :
    ReturnNonlocalLongData nonlocalLong c4 xi s X ij smallError
  smallness :
    ReturnSmallnessInputData cStar xi X c1 c2 c3 c4 s ij smallError

namespace ReturnLocalLeafInputData

/-- Pack the separated Prop. 23.1/M.2 return leaf as grounded Return local data. -/
def toGroundedReturnLocalData
    {cStar xi X : Real}
    (data : ReturnLocalLeafInputData cStar xi X) :
    GroundedReturnLocalData cStar xi X where
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
  returnPackage_input := {
    shortPieces := data.shortPieces
    olcData := data.olcData
    nonlocalLongData := data.nonlocalLongData }
  hSmall := data.hSmall

end ReturnLocalLeafInputData

namespace ReturnSeparatedLocalLeafInputData

/-- Bundle the separated Return package/smallness leaves into the existing
Return local leaf. -/
def toReturnLocalLeafInputData
    {cStar xi X : Real}
    (data : ReturnSeparatedLocalLeafInputData cStar xi X) :
    ReturnLocalLeafInputData cStar xi X where
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

/-- Convert the separated Return leaf to grounded Return local data. -/
def toGroundedReturnLocalData
    {cStar xi X : Real}
    (data : ReturnSeparatedLocalLeafInputData cStar xi X) :
    GroundedReturnLocalData cStar xi X :=
  data.toReturnLocalLeafInputData.toGroundedReturnLocalData

end ReturnSeparatedLocalLeafInputData

/-- Recover the separated Prop. 23.1/M.2 return leaf carried by grounded Return data. -/
def GroundedReturnLocalData.toLocalLeafInputData
    {cStar xi X : Real}
    (data : GroundedReturnLocalData cStar xi X) :
    ReturnLocalLeafInputData cStar xi X where
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
  shortPieces := data.returnPackage_input.shortPieces
  olcData := data.returnPackage_input.olcData
  nonlocalLongData := data.returnPackage_input.nonlocalLongData
  hSmall := data.hSmall

/-- Prop. 23.1 four-piece return certificate, carried in the split manuscript
shape with the M.2 OLC endpoint-multiplicity data nested inside it. -/
def GroundedReturnLocalData.package
    {cStar xi X : Real}
    (data : GroundedReturnLocalData cStar xi X) :
    ReturnFourPieceData data.ordinaryShort data.semiperiodic data.olc
      data.nonlocalLong data.c1 data.c2 data.c3 data.c4 xi data.s X data.ij
      data.smallError data.ML data.epsilonTerm :=
  data.returnPackage_input

/-- Project the ordinary short-return certificate carried by grounded Return data. -/
def GroundedReturnLocalData.ordinaryShortData
    {cStar xi X : Real}
    (data : GroundedReturnLocalData cStar xi X) :
    ReturnOrdinaryShortData data.ordinaryShort data.c1 xi data.s X data.ij
      data.smallError :=
  data.returnPackage_input.shortPieces.ordinary

/-- Project the semiperiodic short-return certificate carried by grounded Return data. -/
def GroundedReturnLocalData.semiperiodicData
    {cStar xi X : Real}
    (data : GroundedReturnLocalData cStar xi X) :
    ReturnSemiperiodicShortData data.semiperiodic data.c2 xi data.s X data.ij
      data.smallError :=
  data.returnPackage_input.shortPieces.semiperiodicData

/-- Project the M.2 OLC endpoint certificate carried by grounded Return data. -/
def GroundedReturnLocalData.olcData
    {cStar xi X : Real}
    (data : GroundedReturnLocalData cStar xi X) :
    ReturnOLCData data.olc data.ML X data.ij data.epsilonTerm data.s data.c3 xi
      data.smallError :=
  data.returnPackage_input.olcData

/-- Project the nonlocal long-return certificate carried by grounded Return data. -/
def GroundedReturnLocalData.nonlocalLongData
    {cStar xi X : Real}
    (data : GroundedReturnLocalData cStar xi X) :
    ReturnNonlocalLongData data.nonlocalLong data.c4 xi data.s X data.ij
      data.smallError :=
  data.returnPackage_input.nonlocalLongData

/-- Convert M.2-grounded return data into the existing return factory package. -/
def GroundedReturnLocalData.toReturnFactoryData
    {cStar xi X : Real}
    (data : GroundedReturnLocalData cStar xi X) :
    ReturnFactoryData cStar xi X where
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
  hOrdinaryShort := data.package.ordinaryShort_bound
  hSemiperiodic := data.package.semiperiodic_bound
  hOLC := data.package.olc_bound
  hNonlocalLong := data.package.nonlocalLong_bound
  hSmall := data.hSmall

/-- M.2-grounded OLC contribution in the exact L.2.2 return-package shape. -/
theorem GroundedReturnLocalData.olc_bound
    {cStar xi X : Real}
    (data : GroundedReturnLocalData cStar xi X) :
    data.olc <= data.c3 * xi * data.s * X * data.ij + data.smallError / 4 :=
  data.package.olc_bound

/-- Proposition 23.1 linear return-package combination with the M.2 OLC bound
already discharged. -/
theorem GroundedReturnLocalData.return_linear_bound
    {cStar xi X : Real}
    (data : GroundedReturnLocalData cStar xi X) :
    data.ordinaryShort + data.semiperiodic + data.olc + data.nonlocalLong <=
      (data.c1 + data.c2 + data.c3 + data.c4) * xi * data.s * X * data.ij +
        data.smallError :=
  data.package.linear_bound

/-- Proposition 23.1 / I.5.1 for the current M.2-grounded return package. -/
theorem GroundedReturnLocalData.nonRunReturn_bound
    {cStar xi X : Real}
    (data : GroundedReturnLocalData cStar xi X) :
    data.ordinaryShort + data.semiperiodic + data.olc + data.nonlocalLong <=
      cStar * xi * X / 6 :=
  data.return_linear_bound.trans data.hSmall

namespace ReturnLocalLeafInputData

/-- Proposition 23.1/M.2 final return bound projected directly from the return leaf. -/
theorem nonRunReturn_bound
    {cStar xi X : Real}
    (data : ReturnLocalLeafInputData cStar xi X) :
    data.ordinaryShort + data.semiperiodic + data.olc + data.nonlocalLong <=
      cStar * xi * X / 6 :=
  data.toGroundedReturnLocalData.nonRunReturn_bound

end ReturnLocalLeafInputData

namespace ReturnSeparatedLocalLeafInputData

/-- Proposition 23.1/M.2 final return bound projected directly from the
separated return leaf. -/
theorem nonRunReturn_bound
    {cStar xi X : Real}
    (data : ReturnSeparatedLocalLeafInputData cStar xi X) :
    data.ordinaryShort + data.semiperiodic + data.olc + data.nonlocalLong <=
      cStar * xi * X / 6 :=
  data.toGroundedReturnLocalData.nonRunReturn_bound

end ReturnSeparatedLocalLeafInputData

/--
Core global assembly where carry, Chernoff, CNL, DensePack, Return, and
high-excess use their current proof-v4 grounded interfaces.
-/
structure GlobalAssemblyCoreGroundedCarryChernoffCNLReturnDensePackHighExcessInputs where
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
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
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

/-- Convert the grounded interface with M.2-return data to per-failure assembly. -/
def GlobalAssemblyCoreGroundedCarryChernoffCNLReturnDensePackHighExcessInputs.toGlobalPerFailureAssembly
    (data : GlobalAssemblyCoreGroundedCarryChernoffCNLReturnDensePackHighExcessInputs) :
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
      returnPkg := (data.returnPkg shell hcQ).toReturnFactoryData
      run := data.run shell hcQ }
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases
        ((data.carry shell hcQ).toCarryData)
        ((data.highExcess shell hcQ phases).toHighExcessChargeData)

/--
Erdos 260 from the core interface whose carry, Chernoff, CNL, Return OLC,
DensePack, and high-excess packages are supplied through proof-v4 aligned
constructors.
-/
theorem erdos260_final_core_grounded_carry_chernoff_cnl_return_densePack_highExcess
    (data : GlobalAssemblyCoreGroundedCarryChernoffCNLReturnDensePackHighExcessInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

end

end Erdos260
