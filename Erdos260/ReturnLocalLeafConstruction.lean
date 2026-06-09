import Mathlib
import Erdos260.GlobalReturnAssembly
import Erdos260.GlobalCarryShellAssembly
import Erdos260.Constants

/-!
# Prop. 23.1/M.2 return separated local leaf construction
-/

namespace Erdos260

noncomputable section

/-- Public constructor for the faithful Prop. I.5.1/M.2/J.4/L.6 return route. -/
def returnSeparatedLocalLeafFromInput
    {cStar xi X : Real}
    (data : ReturnSeparatedLocalLeafInputData cStar xi X) :
    ReturnSeparatedLocalLeafInputData cStar xi X :=
  data

/-- Build the faithful Return leaf from the Prop. 23.1 four-piece package and
the final scalar smallness comparison. -/
def returnSeparatedLocalLeafFromFourPiece
    {cStar xi X : Real}
    {ordinaryShort semiperiodic olc nonlocalLong : Real}
    {c1 c2 c3 c4 s ij smallError ML epsilonTerm : Real}
    (pieces :
      ReturnFourPieceData ordinaryShort semiperiodic olc nonlocalLong
        c1 c2 c3 c4 xi s X ij smallError ML epsilonTerm)
    (smallness :
      ReturnSmallnessInputData cStar xi X c1 c2 c3 c4 s ij smallError) :
    ReturnSeparatedLocalLeafInputData cStar xi X where
  ordinaryShort := ordinaryShort
  semiperiodic := semiperiodic
  olc := olc
  nonlocalLong := nonlocalLong
  c1 := c1
  c2 := c2
  c3 := c3
  c4 := c4
  s := s
  ij := ij
  smallError := smallError
  ML := ML
  epsilonTerm := epsilonTerm
  shortPieces := pieces.shortPieces
  olcData := pieces.olcData
  nonlocalLongData := pieces.nonlocalLongData
  smallness := smallness

/-- Proof-v4 named route for Proposition I.5.1 with M.2/J.4/L.6 residual
handling.

The caller supplies the four return pieces and the scalar smallness comparison;
the constructor keeps the public boundary aligned with the manuscript sections
that close the return leaf. -/
def returnSeparatedLocalLeafFromClosedI51M2J4L6
    {cStar xi X : Real}
    {ordinaryShort semiperiodic olc nonlocalLong : Real}
    {c1 c2 c3 c4 s ij smallError ML epsilonTerm : Real}
    (pieces :
      ReturnFourPieceData ordinaryShort semiperiodic olc nonlocalLong
        c1 c2 c3 c4 xi s X ij smallError ML epsilonTerm)
    (smallness :
      ReturnSmallnessInputData cStar xi X c1 c2 c3 c4 s ij smallError) :
    ReturnSeparatedLocalLeafInputData cStar xi X :=
  returnSeparatedLocalLeafFromFourPiece pieces smallness

/-- Manuscript-shaped package input for the I.5.1/M.2/J.4/L.6 return leaf.

The record names the four return contributions, the constants used by the
four-piece estimate, the proof-v4 `ReturnFourPieceData`, and the final scalar
smallness comparison. -/
structure ReturnClosedI51M2J4L6PackageInputData
    (cStar xi X : Real) where
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
  pieces :
    ReturnFourPieceData ordinaryShort semiperiodic olc nonlocalLong
      c1 c2 c3 c4 xi s X ij smallError ML epsilonTerm
  smallness :
    ReturnSmallnessInputData cStar xi X c1 c2 c3 c4 s ij smallError

namespace ReturnClosedI51M2J4L6PackageInputData

/-- Build the manuscript-shaped return package from the elementary
Prop. I.5.1/M.2/J.4/L.6 subcertificates.

This is the direct proof-v4 route: ordinary short and semiperiodic short
returns, the M.2 OLC multiplicity/epsilon/ML/return budgets, the nonlocal-long
bound, and the final scalar smallness comparison. -/
def ofOLCMultiplicity
    {cStar xi X : Real}
    {ordinaryShort semiperiodic olc nonlocalLong : Real}
    {c1 c2 c3 c4 s ij smallError ML epsilonTerm : Real}
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
      nonlocalLong <= c4 * xi * s * X * ij + smallError / 4)
    (smallness :
      ReturnSmallnessInputData cStar xi X c1 c2 c3 c4 s ij smallError) :
    ReturnClosedI51M2J4L6PackageInputData cStar xi X where
  ordinaryShort := ordinaryShort
  semiperiodic := semiperiodic
  olc := olc
  nonlocalLong := nonlocalLong
  c1 := c1
  c2 := c2
  c3 := c3
  c4 := c4
  s := s
  ij := ij
  smallError := smallError
  ML := ML
  epsilonTerm := epsilonTerm
  pieces :=
    ReturnFourPieceData.ofOLCMultiplicity
      ordinaryShort_bound semiperiodic_bound olc_multiplicity olc_epsilon
      olc_ML_budget olc_return_budget nonlocalLong_bound
  smallness := smallness

/-- Project the manuscript-shaped return package to the separated local leaf
consumed by Appendix N. -/
def toReturnSeparatedLocalLeafInputData
    {cStar xi X : Real}
    (data : ReturnClosedI51M2J4L6PackageInputData cStar xi X) :
    ReturnSeparatedLocalLeafInputData cStar xi X :=
  returnSeparatedLocalLeafFromClosedI51M2J4L6 data.pieces data.smallness

end ReturnClosedI51M2J4L6PackageInputData

/-- Public route from the manuscript-shaped I.5.1/M.2/J.4/L.6 package record. -/
def returnSeparatedLocalLeafFromClosedI51M2J4L6Package
    {cStar xi X : Real}
    (data : ReturnClosedI51M2J4L6PackageInputData cStar xi X) :
    ReturnSeparatedLocalLeafInputData cStar xi X :=
  data.toReturnSeparatedLocalLeafInputData

/-- Public route from elementary Prop. I.5.1/M.2/J.4/L.6 estimates to the
manuscript-shaped return package record. -/
def returnClosedI51M2J4L6PackageFromOLCMultiplicity
    {cStar xi X : Real}
    {ordinaryShort semiperiodic olc nonlocalLong : Real}
    {c1 c2 c3 c4 s ij smallError ML epsilonTerm : Real}
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
      nonlocalLong <= c4 * xi * s * X * ij + smallError / 4)
    (smallness :
      ReturnSmallnessInputData cStar xi X c1 c2 c3 c4 s ij smallError) :
    ReturnClosedI51M2J4L6PackageInputData cStar xi X :=
  ReturnClosedI51M2J4L6PackageInputData.ofOLCMultiplicity
    ordinaryShort_bound semiperiodic_bound olc_multiplicity olc_epsilon
    olc_ML_budget olc_return_budget nonlocalLong_bound smallness

/-- Project an already-grounded proof-v4 I.5.1/M.2/J.4/L.6 return package into
the separated return leaf required by the Appendix N endpoint. -/
def returnSeparatedLocalLeafFromGroundedClosedI51M2J4L6
    {cStar xi X : Real}
    (data : GroundedReturnLocalData cStar xi X) :
    ReturnSeparatedLocalLeafInputData cStar xi X :=
  returnSeparatedLocalLeafFromClosedI51M2J4L6
    data.returnPackage_input
    { hSmall := data.hSmall }

/-- Remaining concrete Prop. I.5.1/M.2/J.4/L.6 data needed before a no-input
return local leaf provider can be installed. -/
def returnSeparatedLocalLeafOpenItems : List String :=
  [ "construct ordinary-short and semiperiodic short-return contributions",
    "build the OLC multiplicity, epsilon, ML-budget, and return-budget data",
    "prove the nonlocal-long return bound",
    "combine these estimates through ReturnFourPieceData.ofOLCMultiplicity and returnSeparatedLocalLeafFromFourPiece" ]

theorem returnSeparatedLocalLeafOpenItems_nonempty :
    returnSeparatedLocalLeafOpenItems = [] -> False := by
  intro h
  simp [returnSeparatedLocalLeafOpenItems] at h

end

end Erdos260
