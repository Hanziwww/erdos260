import Mathlib
import Erdos260.GlobalCarryShellAssembly
import Erdos260.AppendixN_Variation
import Erdos260.Constants

/-!
# N.2.1/N.2.2 canonical-Y variation leaf construction
-/

namespace Erdos260

open Finset MeasureTheory

noncomputable section

/--
Proof-v4 N.2.1/N.2.2 input surface for the canonical-Y variation leaf.

This is the non-synthetic route: a provider must supply the actual
first-crossing branch family, the shell-`Q` priority record, the
drop-density integral certificate, and the final rolling-window budget.
-/
structure AppendixNVariationClosedN21N22InputData
    {shell : FailingDyadicShell}
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
    (O_V : Real) where
  Branch : Type
  VarDrop : Real
  Cmul : Nat
  s : Nat
  branches : Finset Branch
  dropMass :
    (T : Real) -> Branch -> (e : Nat) ->
      {x : Real // 0 <= x ∧
        x <=
          AppendixN.crossingIndicator (T + carryLocal.Y)
            (AppendixN.windowSum
              (fun n =>
                (hitGap
                  (carryLocal.toCarryData erdos260Constants_cPr_le_half
                    hc0Small h_supportCount_pos).a n : Real)) s) e}
  K :
    Finset { e : Nat //
      e ∈ carryHitGapAdmissibleEdgeWindow
        carryLocal hc0Small h_supportCount_pos s}
  A : Set Real
  priority :
    letI : DecidableEq Branch := Classical.decEq Branch
    CarryHitGapShellQCanonicalPriorityRecordData (Branch := Branch) shell
      (fun T e => branches.filter fun b => (dropMass T b e : Real) ≠ 0)
  density :
    CarryHitGapCanonicalDropDensityData branches
      (fun T b e => (dropMass T b e : Real)) VarDrop (Cmul : Real)
      carryLocal.Y (carryHitGapWindowEdgeSet s K) A
  hWindow :
    letI : DecidableEq Branch := Classical.decEq Branch
    ((Cmul : Real) *
        (((shell.Q * priority.labelCount * shell.Q : Nat) : Real))) *
        carryLocal.Y *
          (2 *
            (((carryLocal.toCarryData erdos260Constants_cPr_le_half hc0Small
              h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real) *
                ((carryHitGapWindowEdgeSet s K).card : Real)) <= O_V

namespace AppendixNVariationClosedN21N22InputData

/-- Package the raw proof-v4 N.2.1/N.2.2 first-crossing, priority,
drop-density, and rolling-window data into the closed variation record. -/
def ofFirstCrossingData
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    {Branch : Type}
    (VarDrop : Real)
    (Cmul : Nat)
    (s : Nat)
    (branches : Finset Branch)
    (dropMass :
      (T : Real) -> Branch -> (e : Nat) ->
        {x : Real // 0 <= x /\
          x <=
            AppendixN.crossingIndicator (T + carryLocal.Y)
              (AppendixN.windowSum
                (fun n =>
                  (hitGap
                    (carryLocal.toCarryData erdos260Constants_cPr_le_half
                      hc0Small h_supportCount_pos).a n : Real)) s) e})
    (K :
      Finset { e : Nat //
        e ∈ carryHitGapAdmissibleEdgeWindow
          carryLocal hc0Small h_supportCount_pos s})
    (A : Set Real)
    (priority :
      letI : DecidableEq Branch := Classical.decEq Branch
      CarryHitGapShellQCanonicalPriorityRecordData (Branch := Branch) shell
        (fun T e => branches.filter fun b => (dropMass T b e : Real) ≠ 0))
    (density :
      CarryHitGapCanonicalDropDensityData branches
        (fun T b e => (dropMass T b e : Real)) VarDrop (Cmul : Real)
        carryLocal.Y (carryHitGapWindowEdgeSet s K) A)
    (hWindow :
      letI : DecidableEq Branch := Classical.decEq Branch
      ((Cmul : Real) *
          (((shell.Q * priority.labelCount * shell.Q : Nat) : Real))) *
          carryLocal.Y *
            (2 *
              (((carryLocal.toCarryData erdos260Constants_cPr_le_half
                hc0Small h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real) *
                  ((carryHitGapWindowEdgeSet s K).card : Real)) <= O_V) :
    AppendixNVariationClosedN21N22InputData carryLocal hc0Small
      h_supportCount_pos O_V where
  Branch := Branch
  VarDrop := VarDrop
  Cmul := Cmul
  s := s
  branches := branches
  dropMass := dropMass
  K := K
  A := A
  priority := priority
  density := density
  hWindow := hWindow

/-- Package a shell-`Q` canonical variation input directly into the closed
N.2.1/N.2.2 surface.  This is a tighter provider boundary than
`ofFirstCrossingData`: the first-crossing priority record and the canonical
drop-density certificate are carried as one proof-v4 variation package. -/
def ofShellQVariationInput
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    {Branch : Type}
    (VarDrop : Real)
    (Cmul : Nat)
    (s : Nat)
    (branches : Finset Branch)
    (dropMass :
      (T : Real) -> Branch -> (e : Nat) ->
        {x : Real // 0 <= x /\
          x <=
            AppendixN.crossingIndicator (T + carryLocal.Y)
              (AppendixN.windowSum
                (fun n =>
                  (hitGap
                    (carryLocal.toCarryData erdos260Constants_cPr_le_half
                      hc0Small h_supportCount_pos).a n : Real)) s) e})
    (K :
      Finset {e : Nat //
        e ∈ carryHitGapAdmissibleEdgeWindow
          carryLocal hc0Small h_supportCount_pos s})
    (A : Set Real)
    (variationInput :
      letI : DecidableEq Branch := Classical.decEq Branch
      CarryHitGapShellQCanonicalVariationInputData shell branches
        (fun T b e => (dropMass T b e : Real)) VarDrop (Cmul : Real)
        carryLocal.Y (carryHitGapWindowEdgeSet s K) A)
    (hWindow :
      letI : DecidableEq Branch := Classical.decEq Branch
      ((Cmul : Real) *
          (((shell.Q * variationInput.priority.labelCount * shell.Q : Nat) : Real))) *
          carryLocal.Y *
            (2 *
              (((carryLocal.toCarryData erdos260Constants_cPr_le_half
                hc0Small h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real) *
                  ((carryHitGapWindowEdgeSet s K).card : Real)) <= O_V) :
    AppendixNVariationClosedN21N22InputData carryLocal hc0Small
      h_supportCount_pos O_V where
  Branch := Branch
  VarDrop := VarDrop
  Cmul := Cmul
  s := s
  branches := branches
  dropMass := dropMass
  K := K
  A := A
  priority := by
    letI : DecidableEq Branch := Classical.decEq Branch
    exact variationInput.priority
  density := by
    letI : DecidableEq Branch := Classical.decEq Branch
    exact variationInput.density
  hWindow := by
    letI : DecidableEq Branch := Classical.decEq Branch
    exact hWindow

/-- Build the closed N.2.1/N.2.2 input from the proof-v4 shell-denominator
first-crossing record family, priority injectivity certificate, and the two
canonical drop-density inequalities.

The branch family and `dropMass` encode the first-crossing subfibres; the
ordered record family and injectivity are the N.2.0/N.2.1 lower-label
determinacy data; `regularity` and `firstIneq` are the N.2.2 integral
certificate for the canonical finite edge/branch density. -/
def ofShellQFirstCrossingRecordDensity
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    {Branch : Type}
    (VarDrop : Real)
    (Cmul : Nat)
    (s : Nat)
    (branches : Finset Branch)
    (dropMass :
      (T : Real) -> Branch -> (e : Nat) ->
        {x : Real // 0 <= x /\
          x <=
            AppendixN.crossingIndicator (T + carryLocal.Y)
              (AppendixN.windowSum
                (fun n =>
                  (hitGap
                    (carryLocal.toCarryData erdos260Constants_cPr_le_half
                      hc0Small h_supportCount_pos).a n : Real)) s) e})
    (K :
      Finset {e : Nat //
        e ∈ carryHitGapAdmissibleEdgeWindow
          carryLocal hc0Small h_supportCount_pos s})
    (A : Set Real)
    (labelCount : Nat)
    (recordFamily :
      letI : DecidableEq Branch := Classical.decEq Branch
      CarryHitGapShellQFirstCrossingRecordFamilyData
        (Branch := Branch) (Labels := Fin labelCount) shell)
    (injectivity :
      letI : DecidableEq Branch := Classical.decEq Branch
      CarryHitGapPriorityInjectivityData
        (fun T e => branches.filter fun b => (dropMass T b e : Real) ≠ 0)
        recordFamily.D)
    (regularity :
      CarryHitGapDropDensityRegularityData
        (carryHitGapDropDensity branches
          (fun T b e => (dropMass T b e : Real))
          (carryHitGapWindowEdgeSet s K)) A)
    (firstIneq :
      CarryHitGapDropDensityFirstIneqData
        (carryHitGapDropDensity branches
          (fun T b e => (dropMass T b e : Real))
          (carryHitGapWindowEdgeSet s K))
        VarDrop (Cmul : Real) carryLocal.Y A)
    (hWindow :
      ((Cmul : Real) *
          (((shell.Q * labelCount * shell.Q : Nat) : Real))) *
          carryLocal.Y *
            (2 *
              (((carryLocal.toCarryData erdos260Constants_cPr_le_half
                hc0Small h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real) *
                  ((carryHitGapWindowEdgeSet s K).card : Real)) <= O_V) :
    AppendixNVariationClosedN21N22InputData carryLocal hc0Small
      h_supportCount_pos O_V := by
  letI : DecidableEq Branch := Classical.decEq Branch
  let priority :
      CarryHitGapShellQCanonicalPriorityRecordData (Branch := Branch) shell
        (fun T e => branches.filter fun b => (dropMass T b e : Real) ≠ 0) := {
    labelCount := labelCount
    recordFamily := recordFamily
    injectivity := injectivity }
  let density :
      CarryHitGapCanonicalDropDensityData branches
        (fun T b e => (dropMass T b e : Real)) VarDrop (Cmul : Real)
        carryLocal.Y (carryHitGapWindowEdgeSet s K) A := {
    regularity := regularity
    firstIneq := firstIneq }
  exact
    AppendixNVariationClosedN21N22InputData.ofShellQVariationInput
      VarDrop Cmul s branches dropMass K A
      ({ priority := priority
         density := density } :
        CarryHitGapShellQCanonicalVariationInputData shell branches
          (fun T b e => (dropMass T b e : Real)) VarDrop (Cmul : Real)
          carryLocal.Y (carryHitGapWindowEdgeSet s K) A)
      (by simpa [priority, Nat.cast_mul, Nat.cast_add] using hWindow)

/-- Lowest raw N.2.0/N.2.1/N.2.2 constructor currently exposed.

This takes exactly the manuscript-level shell-`Q` ordered first-crossing record
family, its priority injectivity statement, and the canonical drop-density
regularity/first-inequality fields, then assembles the structured closed N.2
variation input used by the N.24 provider. -/
def ofRawShellQFirstCrossingRecordDensityFields
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    {Branch : Type}
    (VarDrop : Real)
    (Cmul : Nat)
    (s : Nat)
    (branches : Finset Branch)
    (dropMass :
      (T : Real) -> Branch -> (e : Nat) ->
        {x : Real // 0 <= x /\
          x <=
            AppendixN.crossingIndicator (T + carryLocal.Y)
              (AppendixN.windowSum
                (fun n =>
                  (hitGap
                    (carryLocal.toCarryData erdos260Constants_cPr_le_half
                      hc0Small h_supportCount_pos).a n : Real)) s) e})
    (K :
      Finset {e : Nat //
        e ∈ carryHitGapAdmissibleEdgeWindow
          carryLocal hc0Small h_supportCount_pos s})
    (A : Set Real)
    (labelCount : Nat)
    (DOrdered :
      Real ->
        {D : AppendixN.FirstCrossingRecordData Branch shell.Q (Fin labelCount) //
          forall e, D.loIdx e <= D.hiIdx e})
    (hinj :
      forall T (e : Nat), forall b,
        b ∈ branches.filter (fun b => (dropMass T b e : Real) ≠ 0) ->
        forall b',
          b' ∈ branches.filter (fun b => (dropMass T b e : Real) ≠ 0) ->
          ((DOrdered T).1).record e b = ((DOrdered T).1).record e b' ->
          ((DOrdered T).1).startResidue b = ((DOrdered T).1).startResidue b' ->
          b = b')
    (hA : MeasurableSet A)
    (hdrop_int :
      IntegrableOn
        (carryHitGapDropDensity branches
          (fun T b e => (dropMass T b e : Real))
          (carryHitGapWindowEdgeSet s K)) A volume)
    (hvar :
      VarDrop <=
        (Cmul : Real) * carryLocal.Y *
          ∫ T in A,
            carryHitGapDropDensity branches
              (fun T b e => (dropMass T b e : Real))
              (carryHitGapWindowEdgeSet s K) T ∂volume)
    (hWindow :
      ((Cmul : Real) *
          (((shell.Q * labelCount * shell.Q : Nat) : Real))) *
          carryLocal.Y *
            (2 *
              (((carryLocal.toCarryData erdos260Constants_cPr_le_half
                hc0Small h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real) *
                  ((carryHitGapWindowEdgeSet s K).card : Real)) <= O_V) :
    AppendixNVariationClosedN21N22InputData carryLocal hc0Small
      h_supportCount_pos O_V := by
  letI : DecidableEq Branch := Classical.decEq Branch
  let recordFamily :
      CarryHitGapShellQFirstCrossingRecordFamilyData
        (Branch := Branch) (Labels := Fin labelCount) shell := {
    DOrdered := DOrdered }
  let injectivity :
      CarryHitGapPriorityInjectivityData
        (fun T e => branches.filter fun b => (dropMass T b e : Real) ≠ 0)
        recordFamily.D := {
    hinj := by
      intro T e b hb b' hb' hrec hstart
      exact
        hinj T e b hb b' hb'
          (by simpa [recordFamily, CarryHitGapShellQFirstCrossingRecordFamilyData.D] using hrec)
          (by simpa [recordFamily, CarryHitGapShellQFirstCrossingRecordFamilyData.D] using hstart) }
  let regularity :
      CarryHitGapDropDensityRegularityData
        (carryHitGapDropDensity branches
          (fun T b e => (dropMass T b e : Real))
          (carryHitGapWindowEdgeSet s K)) A := {
    hA := hA
    hdrop_int := hdrop_int }
  let firstIneq :
      CarryHitGapDropDensityFirstIneqData
        (carryHitGapDropDensity branches
          (fun T b e => (dropMass T b e : Real))
          (carryHitGapWindowEdgeSet s K))
        VarDrop (Cmul : Real) carryLocal.Y A := {
    hvar := hvar }
  exact
    AppendixNVariationClosedN21N22InputData.ofShellQFirstCrossingRecordDensity
      VarDrop Cmul s branches dropMass K A labelCount recordFamily injectivity
      regularity firstIneq hWindow

/-- Recover the closed N.2.1/N.2.2 input surface from an already-canonical
`Y` variation-class package.

This is a structural bridge, not a new proof route: it keeps the first-crossing
family, shell-`Q` priority record, drop-density certificate, and rolling-window
bound already carried by `CarryHitGapCanonicalYVariationClassData`, while
presenting them at the stricter `AppendixNVariationClosedN21N22InputData`
boundary used by the final N.24 provider. -/
def ofCanonicalYVariationClassData
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapCanonicalYVariationClassData carryLocal hc0Small
        h_supportCount_pos O_V) :
    AppendixNVariationClosedN21N22InputData carryLocal hc0Small
      h_supportCount_pos O_V where
  Branch := data.Branch
  VarDrop := data.VarDrop
  Cmul := data.Cmul
  s := data.s
  branches := data.branches
  dropMass := data.dropMass
  K := data.K
  A := data.A
  priority := data.priority
  density := data.density
  hWindow := by
    letI : DecidableEq data.Branch := Classical.decEq data.Branch
    simpa [CarryHitGapCanonicalYVariationClassData.priority] using data.hWindow

/-- Recover the closed N.2.1/N.2.2 input surface from an already-canonical
variation leaf. -/
def ofCanonicalYVariationLeafData
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapCanonicalYVariationLeafData carryLocal hc0Small
        h_supportCount_pos O_V) :
    AppendixNVariationClosedN21N22InputData carryLocal hc0Small
      h_supportCount_pos O_V :=
  ofCanonicalYVariationClassData data.toVariationClassData

/-- Assemble the canonical-Y variation leaf from the real N.2 proof-v4 data. -/
def toLeaf
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      AppendixNVariationClosedN21N22InputData carryLocal hc0Small
        h_supportCount_pos O_V) :
    CarryHitGapCanonicalYVariationLeafData
      carryLocal hc0Small h_supportCount_pos O_V :=
  CarryHitGapCanonicalYVariationLeafData.ofClosedN21N22
    data.VarDrop data.Cmul data.s data.branches data.dropMass data.K data.A
    data.priority data.density data.hWindow

/-- Project the closed N.2.1/N.2.2 leaf to the canonical-Y variation class
package used by N.24. -/
def toVariationClassData
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      AppendixNVariationClosedN21N22InputData carryLocal hc0Small
        h_supportCount_pos O_V) :
    CarryHitGapCanonicalYVariationClassData carryLocal hc0Small
      h_supportCount_pos O_V :=
  data.toLeaf.toVariationClassData

/-- Project the closed N.2.1/N.2.2 package to the Appendix N window-drop
estimate.  This exposes the N.2.2 reduced-record/coarea estimate at the same
boundary consumed by the final N.24 provider. -/
def toWindowDropEstimateData
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      AppendixNVariationClosedN21N22InputData carryLocal hc0Small
        h_supportCount_pos O_V) :
    AppendixN.WindowDropEstimateData :=
  data.toLeaf.toWindowDropEstimateData

/-- The closed N.2 package satisfies the projected N.2/N.13 window bound. -/
theorem varDrop_le_projected_windowBound
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      AppendixNVariationClosedN21N22InputData carryLocal hc0Small
        h_supportCount_pos O_V) :
    data.VarDrop <=
      (CarryHitGapCanonicalYVariationClassData.toVariationClassData
        data.toVariationClassData).windowBound :=
  data.toLeaf.varDrop_le_projected_windowBound

/-- The closed N.2 package pays the variation-drop mass into the variation
class used by the final N.24 split. -/
theorem varDrop_le_class
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      AppendixNVariationClosedN21N22InputData carryLocal hc0Small
        h_supportCount_pos O_V) :
    data.VarDrop <= O_V :=
  data.toLeaf.varDrop_le_class

end AppendixNVariationClosedN21N22InputData

/-- Public constructor for the faithful N.2 route. -/
def appendixNVariationLeafFromClosedN21N22
    {shell : FailingDyadicShell}
    {pin : PinnedManuscriptShell shell}
    {hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X}
    {O_V : Real}
    (data :
      AppendixNVariationClosedN21N22InputData
        (appendixNGapCanonicalYCarryLocalAt shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        O_V) :
    CarryHitGapCanonicalYVariationLeafData
      (appendixNGapCanonicalYCarryLocalAt shell hXge)
      pin.hc0Small
      (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
      O_V :=
  data.toLeaf

/-- Public constructor for the N.24-facing variation-class projection from the
same closed N.2.1/N.2.2 data. -/
def appendixNVariationClassFromClosedN21N22
    {shell : FailingDyadicShell}
    {pin : PinnedManuscriptShell shell}
    {hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X}
    {O_V : Real}
    (data :
      AppendixNVariationClosedN21N22InputData
        (appendixNGapCanonicalYCarryLocalAt shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        O_V) :
    CarryHitGapCanonicalYVariationClassData
      (appendixNGapCanonicalYCarryLocalAt shell hXge)
      pin.hc0Small
      (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
      O_V :=
  data.toVariationClassData

/-- Proof-v4 N.2/N.3 package at canonical `Y`.

This is the N.24-facing bundle: the N.2 first-crossing variation data fixes the
canonical terminal remainder through the C1-VD split, and the N.3.3 table-routed
terminal absorption package pays that remainder into the five non-drop classes.
-/
structure AppendixNClosedN2N3InputData
    {shell : FailingDyadicShell}
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
    (O_D O_P O_E O_CNL O_bdd O_V : Real) where
  variation :
    AppendixNVariationClosedN21N22InputData carryLocal hc0Small
      h_supportCount_pos O_V
  terminalAbsorption :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
      (GroundedC1VDSplitData.ofVariation
        variation.toVariationClassData.toVariationClassData).termMass
      O_D O_P O_E O_CNL O_bdd

namespace AppendixNClosedN2N3InputData

/-- Recover the closed N.2/N.3 package from the canonical-`Y` N.24 input.

The canonical N.24 package already carries the same N.2.1/N.2.2 variation
class and the same table-routed N.3.3 terminal absorption estimate.  This bridge
exposes those data at the stricter closed N.2/N.3 boundary, so later L.6-backed
work only has to strengthen the bounded class rather than reconstruct the N.2
variation record. -/
def ofN24CanonicalYInputData
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    (data :
      CarryHitGapN24CanonicalYInputData carryLocal hc0Small h_supportCount_pos
        O_D O_P O_E O_CNL O_bdd O_V) :
    AppendixNClosedN2N3InputData carryLocal hc0Small h_supportCount_pos
      O_D O_P O_E O_CNL O_bdd O_V where
  variation :=
    AppendixNVariationClosedN21N22InputData.ofCanonicalYVariationClassData
      data.variation
  terminalAbsorption := by
    simpa [AppendixNVariationClosedN21N22InputData.ofCanonicalYVariationClassData,
      AppendixNVariationClosedN21N22InputData.toVariationClassData,
      AppendixNVariationClosedN21N22InputData.toLeaf,
      CarryHitGapCanonicalYVariationLeafData.toVariationClassData,
      CarryHitGapCanonicalYVariationClassData.ofClosedN21N22,
      CarryHitGapCanonicalYVariationClassData.priority,
      CarryHitGapCanonicalYVariationClassData.density] using
      data.terminalAbsorption

/-- Project the bundled N.2/N.3 proof-v4 data to the canonical-Y N.24 package. -/
def toN24CanonicalYInputData
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    (data :
      AppendixNClosedN2N3InputData carryLocal hc0Small h_supportCount_pos
        O_D O_P O_E O_CNL O_bdd O_V) :
    CarryHitGapN24CanonicalYInputData carryLocal hc0Small h_supportCount_pos
      O_D O_P O_E O_CNL O_bdd O_V :=
  CarryHitGapN24CanonicalYInputData.ofClosedN2N3
    data.variation.toVariationClassData data.terminalAbsorption

/-- Project the bundled N.2/N.3 package back to the N.2 leaf. -/
def variationLeaf
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    (data :
      AppendixNClosedN2N3InputData carryLocal hc0Small h_supportCount_pos
        O_D O_P O_E O_CNL O_bdd O_V) :
    CarryHitGapCanonicalYVariationLeafData carryLocal hc0Small
      h_supportCount_pos O_V :=
  data.variation.toLeaf

end AppendixNClosedN2N3InputData

/-- Public constructor for the canonical-Y N.24 package from closed N.2/N.3
proof-v4 data. -/
def appendixNN24CanonicalYFromClosedN2N3
    {shell : FailingDyadicShell}
    {pin : PinnedManuscriptShell shell}
    {hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    (data :
      AppendixNClosedN2N3InputData
        (appendixNGapCanonicalYCarryLocalAt shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        O_D O_P O_E O_CNL O_bdd O_V) :
    CarryHitGapN24CanonicalYInputData
      (appendixNGapCanonicalYCarryLocalAt shell hXge)
      pin.hc0Small
      (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
      O_D O_P O_E O_CNL O_bdd O_V :=
  data.toN24CanonicalYInputData

/-- Remaining proof-v4 data still needed before a no-input N.2 variation leaf
provider can be installed. -/
def appendixNVariationLeafOpenItems : List String :=
  [ "N.2.0 first-crossing branch family for the carry hit-gap window",
    "N.2.1 shell-Q priority record and injectivity/carry-determinacy certificate",
    "N.2.2 canonical drop-density regularity and integral domination",
    "N.2.2 rolling-window budget comparison for O_V" ]

theorem appendixNVariationLeafOpenItems_nonempty :
    appendixNVariationLeafOpenItems = [] -> False := by
  intro h
  simp [appendixNVariationLeafOpenItems] at h

end

end Erdos260
