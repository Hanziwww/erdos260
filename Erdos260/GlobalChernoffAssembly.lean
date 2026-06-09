import Mathlib
import Erdos260.StoppedTree
import Erdos260.GlobalDensePackAssembly

/-!
# Global Chernoff assembly

This module grounds the Chernoff phase one layer further.  The previous global
interface asked for a `ChernoffPathData` containing a raw exponential-moment
bound.  Here that moment bound is derived from the Lemma 22.1 pointwise
tilt-budget certificate used by the stopped-induction Chernoff lemma.
-/

namespace Erdos260

open Finset MeasureTheory

noncomputable section

/-- Lemma 22.1 pointwise tilted estimate for each regular path. -/
structure ChernoffPointwiseTiltData
    {Path : Type} (paths : Finset Path) (weight : Path -> Real)
    (cost : Path -> Nat) (z B : Real) where
  pointwise :
    forall p, p ∈ paths -> weight p * z ^ cost p <= B

/-- Lemma 22.1 aggregate stopped-tree moment budget. -/
structure ChernoffMomentBudgetData
    {Path : Type} (paths : Finset Path) (B root A : Real) (m : Nat) where
  budget :
    (paths.card : Real) * B <= root * A ^ m

/-- Lemma 22.1 final tail smallness comparison into the Chernoff phase budget. -/
structure ChernoffTailBudgetData
    (root A z cStar xi X : Real) (m Y : Nat) where
  tail_bound :
    root * A ^ m / z ^ Y <= cStar * xi * X / 6

/--
Lemma 22.1 exponential tail certificate.

This is the manuscript-shaped version of the final Chernoff tail comparison:
the stopped tree first gives an exponentially decaying shell tail
`tailConstant * X / 2^tailExponent`, and the large-scale budget then makes that
quantity fit into the Chernoff phase slot.  The length condition records the
`m <= cY` input used in the manuscript derivation of the exponential tail; the
actual exponential comparison is kept as the explicit theorem field here.
-/
structure ChernoffExponentialTailBudgetData
    (root A z cStar xi X : Real) (m Y : Nat) where
  tailConstant : Real
  tailExponent : Nat
  lengthSlope : Nat
  length_condition :
    m <= lengthSlope * Y
  exponential_tail_bound :
    root * A ^ m / z ^ Y <= tailConstant * X / (2 : Real) ^ tailExponent
  exponential_tail_small :
    tailConstant * X / (2 : Real) ^ tailExponent <= cStar * xi * X / 6

/--
Lemma 22.1 exponential-tail comparison in the zero-length normalization used by
the canonical finite carry-Chernoff leaf.  In that leaf the aggregate moment
budget has `A = 1` and `m = 0`, so the manuscript length condition is automatic;
the only remaining content is the exponential tail comparison and the final
large-scale smallness bound.
-/
structure ChernoffZeroLengthExponentialTailData
    (root z cStar xi X : Real) (Y : Nat) where
  tailConstant : Real
  tailExponent : Nat
  exponential_tail_bound :
    root / z ^ Y <= tailConstant * X / (2 : Real) ^ tailExponent
  exponential_tail_small :
    tailConstant * X / (2 : Real) ^ tailExponent <= cStar * xi * X / 6

/-- Lemma 22.1 pointwise tilted estimate plus aggregate moment budget. -/
structure ChernoffPointwiseMomentData
    {Path : Type} (paths : Finset Path) (weight : Path -> Real)
    (cost : Path -> Nat) (z root A B : Real) (m : Nat) where
  tilt :
    ChernoffPointwiseTiltData paths weight cost z B
  momentBudget :
    ChernoffMomentBudgetData paths B root A m

namespace ChernoffPointwiseTiltData

/-- Finite-family pointwise tilted bound with the budget chosen as the total
tilted mass.  This closes the purely finite part of the Lemma 22.1 moment input;
the final Chernoff tail-smallness remains a separate manuscript comparison. -/
def ofFiniteSumBudget
    {Path : Type} (paths : Finset Path)
    (weight : Path -> {x : Real // 0 <= x})
    (cost : Path -> Nat)
    (z : {z : Real // 1 <= z}) :
    ChernoffPointwiseTiltData paths (fun p => (weight p : Real)) cost (z : Real)
      (paths.sum (fun p => (weight p : Real) * (z : Real) ^ cost p)) where
  pointwise := by
    intro p hp
    have hz_nonneg : 0 <= (z : Real) := by linarith [z.property]
    exact Finset.single_le_sum
      (fun q _hq => mul_nonneg (weight q).property (pow_nonneg hz_nonneg _))
      hp

end ChernoffPointwiseTiltData

namespace ChernoffPointwiseMomentData

/-- Finite-family pointwise plus aggregate moment budget with the root chosen as
`|paths|` times the finite tilted-mass budget. -/
def ofFiniteSumBudget
    {Path : Type} (paths : Finset Path)
    (weight : Path -> {x : Real // 0 <= x})
    (cost : Path -> Nat)
    (z : {z : Real // 1 <= z}) :
    ChernoffPointwiseMomentData paths (fun p => (weight p : Real)) cost (z : Real)
      ((paths.card : Real) *
        (paths.sum (fun p => (weight p : Real) * (z : Real) ^ cost p)))
      1
      (paths.sum (fun p => (weight p : Real) * (z : Real) ^ cost p))
      0 where
  tilt := ChernoffPointwiseTiltData.ofFiniteSumBudget paths weight cost z
  momentBudget := {
    budget := by simp }

/-- Project the pointwise regular-edge tilted estimates from the split certificate. -/
theorem pointwise
    {Path : Type} {paths : Finset Path} {weight : Path -> Real}
    {cost : Path -> Nat} {z root A B : Real} {m : Nat}
    (data : ChernoffPointwiseMomentData paths weight cost z root A B m) :
    forall p, p ∈ paths -> weight p * z ^ cost p <= B :=
  data.tilt.pointwise

/-- Project the aggregate stopped-tree moment budget from the split certificate. -/
theorem budget
    {Path : Type} {paths : Finset Path} {weight : Path -> Real}
    {cost : Path -> Nat} {z root A B : Real} {m : Nat}
    (data : ChernoffPointwiseMomentData paths weight cost z root A B m) :
    (paths.card : Real) * B <= root * A ^ m :=
  data.momentBudget.budget

/-- Lemma 22.1 moment bound derived from pointwise regular-edge tilted estimates. -/
theorem moment_bound
    {Path : Type} {paths : Finset Path} {weight : Path -> Real}
    {cost : Path -> Nat} {z root A B : Real} {m : Nat}
    (data : ChernoffPointwiseMomentData paths weight cost z root A B m) :
    ∑ p ∈ paths, weight p * z ^ cost p <= root * A ^ m :=
  (weightedMoment_le_card_mul_of_le data.pointwise).trans data.budget

end ChernoffPointwiseMomentData

namespace ChernoffExponentialTailBudgetData

/-- Collapse the manuscript exponential-tail certificate to the scalar tail
budget expected by the existing Chernoff package. -/
def toTailBudgetData
    {root A z cStar xi X : Real} {m Y : Nat}
    (data : ChernoffExponentialTailBudgetData root A z cStar xi X m Y) :
    ChernoffTailBudgetData root A z cStar xi X m Y where
  tail_bound :=
    data.exponential_tail_bound.trans data.exponential_tail_small

end ChernoffExponentialTailBudgetData

namespace ChernoffZeroLengthExponentialTailData

/-- A numerator-style exponential-tail estimate implies the ratio-style
zero-length tail estimate after dividing by the positive tilt factor. -/
theorem tailBound_of_root_le_scaled
    {root z tailConstant X : Real} {Y tailExponent : Nat}
    (hz_pos : 0 < z)
    (hroot :
      root <= tailConstant * X * z ^ Y / (2 : Real) ^ tailExponent) :
    root / z ^ Y <= tailConstant * X / (2 : Real) ^ tailExponent := by
  have hzpow_pos : 0 < z ^ Y := pow_pos hz_pos Y
  calc
    root / z ^ Y
        <= (tailConstant * X * z ^ Y / (2 : Real) ^ tailExponent) / z ^ Y := by
          exact div_le_div_of_nonneg_right hroot (le_of_lt hzpow_pos)
    _ = tailConstant * X / (2 : Real) ^ tailExponent := by
          field_simp [hzpow_pos.ne']

/-- The zero-length Chernoff smallness comparison is often proved in an
`X`-free scalar form and then multiplied by the nonnegative shell size. -/
theorem tailSmall_of_scalarSmall
    {tailConstant cStar xi X : Real} {tailExponent : Nat}
    (hX_nonneg : 0 <= X)
    (hsmall_scalar :
      tailConstant / (2 : Real) ^ tailExponent <= cStar * xi / 6) :
    tailConstant * X / (2 : Real) ^ tailExponent <= cStar * xi * X / 6 := by
  have hmul := mul_le_mul_of_nonneg_right hsmall_scalar hX_nonneg
  calc
    tailConstant * X / (2 : Real) ^ tailExponent
        = tailConstant / (2 : Real) ^ tailExponent * X := by ring
    _ <= cStar * xi / 6 * X := hmul
    _ = cStar * xi * X / 6 := by ring

/-- Build the zero-length exponential-tail certificate from the actual tail
comparison and the `X`-free scalar smallness comparison. -/
def ofScalarSmallness
    {root z cStar xi X : Real} {Y : Nat}
    (tailConstant : Real)
    (tailExponent : Nat)
    (hX_nonneg : 0 <= X)
    (exponential_tail_bound :
      root / z ^ Y <= tailConstant * X / (2 : Real) ^ tailExponent)
    (exponential_tail_small_scalar :
      tailConstant / (2 : Real) ^ tailExponent <= cStar * xi / 6) :
    ChernoffZeroLengthExponentialTailData root z cStar xi X Y where
  tailConstant := tailConstant
  tailExponent := tailExponent
  exponential_tail_bound := exponential_tail_bound
  exponential_tail_small :=
    tailSmall_of_scalarSmall hX_nonneg exponential_tail_small_scalar

/-- Build the zero-length exponential-tail certificate from a numerator-style
root estimate and an `X`-free scalar smallness estimate. -/
def ofRootBoundAndScalarSmallness
    {root z cStar xi X : Real} {Y : Nat}
    (tailConstant : Real)
    (tailExponent : Nat)
    (hz_pos : 0 < z)
    (hX_nonneg : 0 <= X)
    (root_bound :
      root <= tailConstant * X * z ^ Y / (2 : Real) ^ tailExponent)
    (exponential_tail_small_scalar :
      tailConstant / (2 : Real) ^ tailExponent <= cStar * xi / 6) :
    ChernoffZeroLengthExponentialTailData root z cStar xi X Y :=
  ofScalarSmallness tailConstant tailExponent hX_nonneg
    (tailBound_of_root_le_scaled hz_pos root_bound)
    exponential_tail_small_scalar

/-- Reinsert the automatic `m = 0` length condition and recover the older
manuscript exponential-tail budget record. -/
def toChernoffExponentialTailBudgetData
    {root z cStar xi X : Real} {Y : Nat}
    (data : ChernoffZeroLengthExponentialTailData root z cStar xi X Y) :
    ChernoffExponentialTailBudgetData root 1 z cStar xi X 0 Y where
  tailConstant := data.tailConstant
  tailExponent := data.tailExponent
  lengthSlope := 0
  length_condition := by simp
  exponential_tail_bound := by simpa using data.exponential_tail_bound
  exponential_tail_small := data.exponential_tail_small

end ChernoffZeroLengthExponentialTailData

/-- Lemma 22.1 shell Chernoff certificate: pointwise/aggregate moment control
plus the final tail smallness comparison into the phase budget. -/
structure ChernoffShellBudgetData
    {Path : Type} (paths : Finset Path) (weight : Path -> Real)
    (cost : Path -> Nat) (z root A B : Real) (m Y : Nat)
    (cStar xi X : Real) where
  tiltBudget :
    ChernoffPointwiseMomentData paths weight cost z root A B m
  tailBudget :
    ChernoffTailBudgetData root A z cStar xi X m Y

/--
Proof-v4 aligned Chernoff local data.

The `moment_bound` field of `ChernoffPathData` is derived from the carried
pointwise tilt-budget certificate.  The remaining scalar `manuscript_bound`
is the final tail smallness comparison into the phase budget.
-/
structure GroundedChernoffLocalData (cStar xi X : Real) where
  α : Type
  paths : Finset α
  weight : α -> {x : Real // 0 <= x}
  cost : α -> Nat
  Y : Nat
  m : Nat
  z : {z : Real // 1 <= z}
  root : Real
  A : Real
  B : Real
  chernoff_input :
    ChernoffShellBudgetData paths (fun p => (weight p : Real)) cost (z : Real)
      root A B m Y cStar xi X

/-- Assemble grounded Chernoff local data from the proof-v4 stopped-tree
shell-budget certificate.  The path weights and tilt parameter carry their
nonnegativity/lower-bound facts by type. -/
def GroundedChernoffLocalData.ofClosedStoppedTree
    {cStar xi X : Real}
    {Path : Type}
    (paths : Finset Path)
    (weight : Path -> {x : Real // 0 <= x})
    (cost : Path -> Nat)
    (Y m : Nat)
    (z : {z : Real // 1 <= z})
    (root A B : Real)
    (chernoff_input :
      ChernoffShellBudgetData paths (fun p => (weight p : Real)) cost
        (z : Real) root A B m Y cStar xi X) :
    GroundedChernoffLocalData cStar xi X where
  α := Path
  paths := paths
  weight := weight
  cost := cost
  Y := Y
  m := m
  z := z
  root := root
  A := A
  B := B
  chernoff_input := chernoff_input

/-- Lemma 22.1 stopped-tree shell-budget data before it is packed as grounded
Chernoff local data. -/
structure ChernoffStoppedTreeInputData (cStar xi X : Real) where
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
      root A B m Y cStar xi X

namespace ChernoffStoppedTreeInputData

/-- Convert the stopped-tree shell-budget leaf to the grounded Chernoff package. -/
def toGroundedChernoffLocalData
    {cStar xi X : Real}
    (data : ChernoffStoppedTreeInputData cStar xi X) :
    GroundedChernoffLocalData cStar xi X :=
  GroundedChernoffLocalData.ofClosedStoppedTree data.paths data.weight
    data.cost data.Y data.m data.z data.root data.A data.B data.chernoff_input

/-- Identity alias so shared variation lambdas can use the stopped-tree bridge. -/
def toChernoffStoppedTreeInputData
    {cStar xi X : Real}
    (data : ChernoffStoppedTreeInputData cStar xi X) :
    ChernoffStoppedTreeInputData cStar xi X :=
  data

end ChernoffStoppedTreeInputData

/-- Attach the Lemma 22.1 tilt/moment/tail budget to the concrete stopped-tree
skeleton already built from a carry/failure shell. -/
def CarryStoppedTreeIndexData.toChernoffStoppedTreeInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data : CarryStoppedTreeIndexData carryData)
    (Y m : Nat) (z : {z : Real // 1 <= z}) (root A B : Real)
    (chernoff_input :
      ChernoffShellBudgetData data.paths (fun p => (data.weight p : Real))
        data.cost (z : Real) root A B m Y cStar xi (shell.X : Real)) :
    ChernoffStoppedTreeInputData cStar xi (shell.X : Real) where
  Path := StoppedBranch
  paths := data.paths
  weight := data.weight
  cost := data.cost
  Y := Y
  m := m
  z := z
  root := root
  A := A
  B := B
  chernoff_input := chernoff_input

/-- Direct carry/failure-shell constructor for the Lemma 22.1 stopped-tree leaf.
The path family, weights, and costs are the faithful I.9 skeleton; only the
actual Chernoff tilt/moment/tail certificate remains as input. -/
def CarryDataFromFailure.toChernoffStoppedTreeInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    (carryData : CarryDataFromFailure shell cPr)
    (Y m : Nat) (z : {z : Real // 1 <= z}) (root A B : Real)
    (chernoff_input :
      ChernoffShellBudgetData carryData.stoppedBranches
        (fun p => (carryData.stoppedBranchWeight p : Real))
        carryData.stoppedBranchCost (z : Real) root A B m Y
        cStar xi (shell.X : Real)) :
    ChernoffStoppedTreeInputData cStar xi (shell.X : Real) :=
  carryData.toStoppedTreeIndexData.toChernoffStoppedTreeInputData
    Y m z root A B chernoff_input

/-- Canonical finite tilted mass used to close the pointwise part of the
carry-stopped-tree Lemma 22.1 input. -/
def carryChernoffFiniteTiltMass
    {shell : FailingDyadicShell} {cPr : Real}
    (carryData : CarryDataFromFailure shell cPr) (z : Real) : Real :=
  carryData.stoppedBranches.sum
    (fun p => (carryData.stoppedBranchWeight p : Real) *
      z ^ carryData.stoppedBranchCost p)

/-- Canonical finite root for the carry-stopped-tree Lemma 22.1 moment budget. -/
def carryChernoffFiniteRoot
    {shell : FailingDyadicShell} {cPr : Real}
    (carryData : CarryDataFromFailure shell cPr) (z : Real) : Real :=
  (carryData.stoppedBranches.card : Real) *
    carryChernoffFiniteTiltMass carryData z

/-- The finite tilted mass is exactly the branch weighted moment for the carry
stopped-tree cost. -/
theorem carryChernoffFiniteTiltMass_eq_branchWeightedMoment
    {shell : FailingDyadicShell} {cPr : Real}
    (carryData : CarryDataFromFailure shell cPr) (z : Real) :
    carryChernoffFiniteTiltMass carryData z =
      branchWeightedMoment carryData.stoppedBranches
        (fun p => (carryData.stoppedBranchWeight p : Real)) z := by
  simp [carryChernoffFiniteTiltMass, branchWeightedMoment,
    weightedMoment, CarryDataFromFailure.stoppedBranchCost]

/-- The canonical finite root is the cardinality multiplier times the actual
branch weighted moment. -/
theorem carryChernoffFiniteRoot_eq_card_mul_branchWeightedMoment
    {shell : FailingDyadicShell} {cPr : Real}
    (carryData : CarryDataFromFailure shell cPr) (z : Real) :
    carryChernoffFiniteRoot carryData z =
      (carryData.stoppedBranches.card : Real) *
        branchWeightedMoment carryData.stoppedBranches
          (fun p => (carryData.stoppedBranchWeight p : Real)) z := by
  simp [carryChernoffFiniteRoot,
    carryChernoffFiniteTiltMass_eq_branchWeightedMoment]

/-- Finite-family Lemma 22.1 on the concrete carry stopped tree: once the
high-excess selector has identified the whole stopped family with the
`floor Y` high-cost tail, the actual stopped-branch mass is bounded by the
canonical finite root ratio.  The remaining proof-v4 work is exactly to make
this ratio small enough. -/
theorem CarryDataFromFailure.branchWeightedMass_stoppedBranches_le_finiteRoot_div_pow
    {shell : FailingDyadicShell} {cPr : Real}
    (carryData : CarryDataFromFailure shell cPr)
    (hT_nonneg : 0 <= carryData.T) (hY_nonneg : 0 <= carryData.Y)
    (z : {z : Real // 1 <= z}) :
    branchWeightedMass carryData.stoppedBranches
        (fun p => (carryData.stoppedBranchWeight p : Real)) <=
      carryChernoffFiniteRoot carryData (z : Real) /
        (z : Real) ^ Nat.floor carryData.Y := by
  have hweight :
      forall p, p ∈ carryData.stoppedBranches ->
        0 <= (carryData.stoppedBranchWeight p : Real) := by
    intro p _hp
    exact (carryData.stoppedBranchWeight p).property
  have hmoment :
      branchWeightedMoment carryData.stoppedBranches
          (fun p => (carryData.stoppedBranchWeight p : Real)) (z : Real) <=
        carryChernoffFiniteRoot carryData (z : Real) * (1 : Real) ^ (0 : Nat) := by
    simpa [branchWeightedMoment, carryChernoffFiniteRoot,
      carryChernoffFiniteTiltMass, CarryDataFromFailure.stoppedBranchCost] using
      (ChernoffPointwiseMomentData.ofFiniteSumBudget
        carryData.stoppedBranches carryData.stoppedBranchWeight
        carryData.stoppedBranchCost z).moment_bound
  have htail :
      branchWeightedMass
          (highBranchCostSet carryData.stoppedBranches (Nat.floor carryData.Y))
          (fun p => (carryData.stoppedBranchWeight p : Real)) <=
        carryChernoffFiniteRoot carryData (z : Real) * (1 : Real) ^ (0 : Nat) /
          (z : Real) ^ Nat.floor carryData.Y :=
    branchShellChernoff_bound_of_moment_bound
      (branches := carryData.stoppedBranches)
      (weight := fun p => (carryData.stoppedBranchWeight p : Real))
      (Y := Nat.floor carryData.Y) (m := 0)
      (z := (z : Real)) (root := carryChernoffFiniteRoot carryData (z : Real))
      (A := 1) hweight z.property hmoment
  have htail_eq :
      highBranchCostSet carryData.stoppedBranches (Nat.floor carryData.Y) =
        carryData.stoppedBranches :=
    carryData.highBranchCostSet_floorY_eq_stoppedBranches hT_nonneg hY_nonneg
  simpa [htail_eq] using htail

/-- Analytic version of the finite-family Chernoff bridge: the high-excess mass
selected by the carry recurrence is bounded by the same canonical finite root
ratio.  This combines the faithful I.9 reindexing with the high-cost-tail
identification above. -/
theorem CarryDataFromFailure.highExcessMass_le_finiteRoot_div_pow
    {shell : FailingDyadicShell} {cPr : Real}
    (carryData : CarryDataFromFailure shell cPr)
    (hT_nonneg : 0 <= carryData.T) (hY_nonneg : 0 <= carryData.Y)
    (z : {z : Real // 1 <= z}) :
    highExcessMass
        (highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T <=
      carryChernoffFiniteRoot carryData (z : Real) /
        (z : Real) ^ Nat.floor carryData.Y := by
  have hbranch :=
    carryData.branchWeightedMass_stoppedBranches_le_finiteRoot_div_pow
      hT_nonneg hY_nonneg z
  calc
    highExcessMass
        (highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T
        =
      branchWeightedMass carryData.stoppedBranches
        carryData.stoppedBranchWeightReal :=
          carryData.highExcessMass_eq_stoppedBranchWeightedMass
    _ =
      branchWeightedMass carryData.stoppedBranches
        (fun p => (carryData.stoppedBranchWeight p : Real)) := by
          rfl
    _ <=
      carryChernoffFiniteRoot carryData (z : Real) /
        (z : Real) ^ Nat.floor carryData.Y := hbranch

/-- Lemma 22.1 budget attached to the concrete I.9 stopped-tree skeleton
generated by a carry/failure shell.  This leaves only the actual
tilt/moment/tail certificate as input; the path family, weights, and costs are
definitionally the carry stopped tree. -/
structure CarryChernoffStoppedTreeBudgetData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    (carryData : CarryDataFromFailure shell cPr) where
  Y : Nat
  m : Nat
  z : {z : Real // 1 <= z}
  root : Real
  A : Real
  B : Real
  chernoff_input :
    ChernoffShellBudgetData carryData.stoppedBranches
      (fun p => (carryData.stoppedBranchWeight p : Real))
      carryData.stoppedBranchCost (z : Real) root A B m Y
      cStar xi (shell.X : Real)

/-- Split form of the Lemma 22.1 budget on the concrete I.9 carry stopped tree:
one certificate for the pointwise/aggregate tilted moment estimate and one for
the final scalar tail-smallness comparison. -/
structure CarryChernoffStoppedTreeSplitBudgetData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    (carryData : CarryDataFromFailure shell cPr) where
  Y : Nat
  m : Nat
  z : {z : Real // 1 <= z}
  root : Real
  A : Real
  B : Real
  tiltBudget :
    ChernoffPointwiseMomentData carryData.stoppedBranches
      (fun p => (carryData.stoppedBranchWeight p : Real))
      carryData.stoppedBranchCost (z : Real) root A B m
  tailBudget :
    ChernoffTailBudgetData root A (z : Real) cStar xi (shell.X : Real) m Y

/-- Three-piece form of the Lemma 22.1 budget on the concrete I.9 carry
stopped tree: pointwise tilt, aggregate moment budget, and scalar
tail-smallness are kept as separate manuscript leaves. -/
structure CarryChernoffStoppedTreeSeparatedBudgetData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    (carryData : CarryDataFromFailure shell cPr) where
  Y : Nat
  m : Nat
  z : {z : Real // 1 <= z}
  root : Real
  A : Real
  B : Real
  tilt :
    ChernoffPointwiseTiltData carryData.stoppedBranches
      (fun p => (carryData.stoppedBranchWeight p : Real))
      carryData.stoppedBranchCost (z : Real) B
  momentBudget :
    ChernoffMomentBudgetData carryData.stoppedBranches B root A m
  tailBudget :
    ChernoffTailBudgetData root A (z : Real) cStar xi (shell.X : Real) m Y

/-- Three-piece Lemma 22.1 carry-stopped-tree budget with the final tail in
manuscript exponential-decay form. -/
structure CarryChernoffStoppedTreeExponentialTailData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    (carryData : CarryDataFromFailure shell cPr) where
  Y : Nat
  m : Nat
  z : {z : Real // 1 <= z}
  root : Real
  A : Real
  B : Real
  tilt :
    ChernoffPointwiseTiltData carryData.stoppedBranches
      (fun p => (carryData.stoppedBranchWeight p : Real))
      carryData.stoppedBranchCost (z : Real) B
  momentBudget :
    ChernoffMomentBudgetData carryData.stoppedBranches B root A m
  exponentialTail :
    ChernoffExponentialTailBudgetData root A (z : Real) cStar xi
      (shell.X : Real) m Y

/-- Carry-stopped-tree Lemma 22.1 input with the finite pointwise and aggregate
moment budgets closed canonically.  The only remaining Chernoff content is the
manuscript exponential-tail comparison for that explicit finite budget. -/
structure CarryChernoffFiniteExponentialTailData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    (carryData : CarryDataFromFailure shell cPr) where
  Y : Nat
  Y_floor :
    (Y : Real) <= carryData.Y ∧ carryData.Y < (Y : Real) + 1
  z : {z : Real // 1 <= z}
  exponentialTail :
    ChernoffExponentialTailBudgetData
      (carryChernoffFiniteRoot carryData (z : Real)) 1 (z : Real)
      cStar xi (shell.X : Real) 0 Y

/-- Carry-stopped-tree Lemma 22.1 input with the finite pointwise and aggregate
moment budgets closed canonically, and with the manuscript tilt parameter
restricted to the chosen interval `1 < z < 2`. -/
structure CarryChernoffFiniteZBoundedExponentialTailData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    (carryData : CarryDataFromFailure shell cPr) where
  Y : Nat
  Y_floor :
    (Y : Real) <= carryData.Y ∧ carryData.Y < (Y : Real) + 1
  z : {z : Real // 1 < z ∧ z < 2}
  exponentialTail :
    ChernoffExponentialTailBudgetData
      (carryChernoffFiniteRoot carryData (z : Real)) 1 (z : Real)
      cStar xi (shell.X : Real) 0 Y

/-- Carry-stopped-tree Lemma 22.1 input with both manuscript normalizations
fixed: the tilt parameter lies in `1 < z < 2`, and the Nat shell depth is the
canonical floor `floor(carryData.Y)`.  The conversion back to the older leaf
uses the carry-local proof that `0 <= carryData.Y`; the provider no longer
chooses a separate `Y` or supplies its floor witness. -/
structure CarryChernoffCanonicalYFiniteZBoundedExponentialTailData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    (carryData : CarryDataFromFailure shell cPr) where
  z : {z : Real // 1 < z ∧ z < 2}
  exponentialTail :
    ChernoffExponentialTailBudgetData
      (carryChernoffFiniteRoot carryData (z : Real)) 1 (z : Real)
      cStar xi (shell.X : Real) 0 (Nat.floor carryData.Y)

/-- The fixed manuscript tilt used by the strongest canonical-Y Chernoff leaf. -/
def proofV4ChernoffTilt : {z : Real // 1 < z ∧ z < 2} :=
  ⟨(3 : Real) / 2, by norm_num⟩

/-- Fixed-tilt version of the finite-family Chernoff bridge for the concrete
carry high-excess mass. -/
theorem CarryDataFromFailure.highExcessMass_le_finiteRoot_div_pow_proofV4ChernoffTilt
    {shell : FailingDyadicShell} {cPr : Real}
    (carryData : CarryDataFromFailure shell cPr)
    (hT_nonneg : 0 <= carryData.T) (hY_nonneg : 0 <= carryData.Y) :
    highExcessMass
        (highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T <=
      carryChernoffFiniteRoot carryData (proofV4ChernoffTilt : Real) /
        (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y := by
  let z : {z : Real // 1 <= z} :=
    ⟨(proofV4ChernoffTilt : Real), le_of_lt proofV4ChernoffTilt.property.1⟩
  simpa [z] using
    carryData.highExcessMass_le_finiteRoot_div_pow hT_nonneg hY_nonneg z

/-- Carry-stopped-tree Lemma 22.1 input with all bookkeeping choices fixed:
`Y = floor(carryData.Y)`, `z = 3/2`, and the zero-length moment-budget length
condition discharged internally.  The remaining field is exactly the
manuscript exponential-tail/smallness comparison for that fixed finite budget.
-/
structure CarryChernoffCanonicalYFixedZExponentialTailData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    (carryData : CarryDataFromFailure shell cPr) where
  exponentialTail :
    ChernoffZeroLengthExponentialTailData
      (carryChernoffFiniteRoot carryData (proofV4ChernoffTilt : Real))
      (proofV4ChernoffTilt : Real)
      cStar xi (shell.X : Real) (Nat.floor carryData.Y)

/--
Fixed-`z`, canonical-`Y` carry Chernoff leaf in numerator/scalar form.

This is the final Lemma 22.1 boundary used by proof_v4: prove the explicit
finite-root numerator estimate for `z = 3/2`, and prove the X-free scalar
smallness for the same tail exponent.  Positivity of the shell size and the
division by `z^Y` are closed by the projection below.
-/
structure CarryChernoffCanonicalYFixedZRootScalarInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    (carryData : CarryDataFromFailure shell cPr) where
  tailConstant : Real
  tailExponent : Nat
  root_bound :
    carryChernoffFiniteRoot carryData (proofV4ChernoffTilt : Real) <=
      tailConstant * (shell.X : Real) *
          (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y /
        (2 : Real) ^ tailExponent
  scalar_small :
    tailConstant / (2 : Real) ^ tailExponent <= cStar * xi / 6

/--
Fixed-`z`, canonical-`Y` carry Chernoff leaf in direct root-smallness form.

The older `RootScalar` interface exposed an auxiliary tail constant and dyadic
tail exponent.  Their only use was to prove this single X-free smallness
comparison after multiplying by the nonnegative shell size and the fixed tilt
power.  This structure keeps the remaining Lemma 22.1 content as that direct
numerator estimate.
-/
structure CarryChernoffCanonicalYFixedZRootSmallInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    (carryData : CarryDataFromFailure shell cPr) where
  root_small :
    carryChernoffFiniteRoot carryData (proofV4ChernoffTilt : Real) <=
      (cStar * xi / 6) * (shell.X : Real) *
        (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y

/--
Fixed-`z`, canonical-`Y` carry Chernoff leaf in tail-smallness form.

This is the Lemma 22.1 shape closest to the manuscript: after dividing the
finite tilted root by the positive tilt power `z^Y`, the stopped-tree tail is
small enough for the Chernoff phase budget.  The conversion to numerator form
below closes the routine multiplication by `(3/2)^Y` internally.
-/
structure CarryChernoffCanonicalYFixedZTailSmallInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    (carryData : CarryDataFromFailure shell cPr) where
  tail_small :
    carryChernoffFiniteRoot carryData (proofV4ChernoffTilt : Real) /
        (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y <=
      (cStar * xi / 6) * (shell.X : Real)

/--
Fixed-`z`, canonical-`Y` carry Chernoff leaf in the manuscript 22.1A
layer-cake form.

The already-formalized theorem `lemma22_1A_areaWeightedShellChernoff` converts
the per-level stopped-shell Chernoff estimate into an area-weighted bound.  The
two remaining manuscript bridges are exposed explicitly: the fixed finite
Chernoff root has to be dominated by the area-weighted stopped mass, and the
integrated layer-cake bound has to fit inside the Chernoff phase budget.
-/
structure CarryChernoffCanonicalYFixedZLayerCakeTailInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    (carryData : CarryDataFromFailure shell cPr) where
  wt0 : StoppedBranch -> Real
  Ysh : StoppedBranch -> Real
  chernoff : Real -> Real
  bound : Real
  hYsh : forall b, b ∈ carryData.stoppedBranches -> 0 <= Ysh b
  hchernoff_int : Integrable chernoff volume
  hlevel :
    forall u,
      areaLayerSum carryData.stoppedBranches wt0 Ysh u <= chernoff u
  hbound : ∫ u, chernoff u <= bound
  finiteRoot_le_area :
    carryChernoffFiniteRoot carryData (proofV4ChernoffTilt : Real) /
        (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y <=
      carryData.stoppedBranches.sum (fun b => wt0 b * Ysh b)
  bound_small :
    bound <= (cStar * xi / 6) * (shell.X : Real)

/--
Manuscript-aligned Lemma 22.1A leaf for a regular or shell-paid stopped
subfamily.

Unlike the carry-wide fixed-`z` proxy above, this structure does not identify the
Chernoff family with all high-excess carry branches.  It records the stopped-tree
Chernoff certificate for the selected regular/shell-paid family and the
area-weighted layer-cake estimate used by proof_v4.
-/
structure RegularShellPaidChernoff22_1AInputData (cStar xi X : Real) where
  stoppedTree : ChernoffStoppedTreeInputData cStar xi X
  wt0 : stoppedTree.Path -> Real
  Ysh : stoppedTree.Path -> Real
  chernoff : Real -> Real
  bound : Real
  hYsh : forall b, b ∈ stoppedTree.paths -> 0 <= Ysh b
  hchernoff_int : Integrable chernoff volume
  hlevel :
    forall u, areaLayerSum stoppedTree.paths wt0 Ysh u <= chernoff u
  hbound : ∫ u, chernoff u <= bound
  bound_small : bound <= cStar * xi * X / 6

namespace RegularShellPaidChernoff22_1AInputData

/--
Canonical finite layer-cake constructor for the proof-v4 Lemma 22.1A leaf.

Once the actual stopped regular/shell-paid family and its nonnegative
shell-paid multiplier are known, the `areaLayerSum` function, integrability,
level-set domination, and layer-cake integral are finite-sum bookkeeping.  The
only remaining analytic input at this surface is the final area smallness
comparison for the selected family.
-/
def ofAreaLayerSumStoppedTree
    {cStar xi X : Real}
    (stoppedTree : ChernoffStoppedTreeInputData cStar xi X)
    (Ysh : stoppedTree.Path -> Real)
    (hYsh : forall b, b ∈ stoppedTree.paths -> 0 <= Ysh b)
    (area_small :
      (∑ b ∈ stoppedTree.paths, (stoppedTree.weight b : Real) * Ysh b) <=
        cStar * xi * X / 6) :
    RegularShellPaidChernoff22_1AInputData cStar xi X where
  stoppedTree := stoppedTree
  wt0 := fun p => (stoppedTree.weight p : Real)
  Ysh := Ysh
  chernoff :=
    areaLayerSum stoppedTree.paths
      (fun p => (stoppedTree.weight p : Real)) Ysh
  bound :=
    ∑ b ∈ stoppedTree.paths, (stoppedTree.weight b : Real) * Ysh b
  hYsh := hYsh
  hchernoff_int :=
    areaLayerSum_integrable stoppedTree.paths
      (fun p => (stoppedTree.weight p : Real)) Ysh
  hlevel := by
    intro u
    exact le_rfl
  hbound := by
    rw [integral_areaLayerSum stoppedTree.paths
      (fun p => (stoppedTree.weight p : Real)) Ysh hYsh]
  bound_small := area_small

/-- Project the regular/shell-paid stopped-tree Chernoff leaf to the standard
grounded Chernoff package used by the phase core. -/
def toGroundedChernoffLocalData
    {cStar xi X : Real}
    (data : RegularShellPaidChernoff22_1AInputData cStar xi X) :
    GroundedChernoffLocalData cStar xi X :=
  data.stoppedTree.toGroundedChernoffLocalData

/-- Identity alias so shared variation lambdas can use the stopped-tree bridge. -/
def toChernoffStoppedTreeInputData
    {cStar xi X : Real}
    (data : RegularShellPaidChernoff22_1AInputData cStar xi X) :
    ChernoffStoppedTreeInputData cStar xi X :=
  data.stoppedTree

/-- The layer-cake part of Lemma 22.1A bounds the selected shell-paid area. -/
theorem area_bound
    {cStar xi X : Real}
    (data : RegularShellPaidChernoff22_1AInputData cStar xi X) :
    (∑ b ∈ data.stoppedTree.paths, data.wt0 b * data.Ysh b) <= data.bound :=
  lemma22_1A_areaWeightedShellChernoff data.stoppedTree.paths data.wt0
    data.Ysh data.chernoff data.bound data.hYsh data.hchernoff_int
    data.hlevel data.hbound

/-- The selected shell-paid family fits inside the Chernoff phase budget. -/
theorem shellPaidArea_small
    {cStar xi X : Real}
    (data : RegularShellPaidChernoff22_1AInputData cStar xi X) :
    (∑ b ∈ data.stoppedTree.paths, data.wt0 b * data.Ysh b) <=
      cStar * xi * X / 6 :=
  data.area_bound.trans data.bound_small

end RegularShellPaidChernoff22_1AInputData

namespace CarryChernoffStoppedTreeBudgetData

/-- Pack a carry-stopped-tree budget as the standard Lemma 22.1 stopped-tree
leaf. -/
def toChernoffStoppedTreeInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data : @CarryChernoffStoppedTreeBudgetData shell cPr cStar xi carryData) :
    ChernoffStoppedTreeInputData cStar xi (shell.X : Real) :=
  carryData.toChernoffStoppedTreeInputData data.Y data.m data.z
    data.root data.A data.B data.chernoff_input

end CarryChernoffStoppedTreeBudgetData

namespace CarryChernoffStoppedTreeSplitBudgetData

/-- Merge the split carry-stopped-tree Chernoff data into the compact budget
record. -/
def toCarryChernoffStoppedTreeBudgetData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffStoppedTreeSplitBudgetData shell cPr cStar xi carryData) :
    @CarryChernoffStoppedTreeBudgetData shell cPr cStar xi carryData where
  Y := data.Y
  m := data.m
  z := data.z
  root := data.root
  A := data.A
  B := data.B
  chernoff_input := {
    tiltBudget := data.tiltBudget
    tailBudget := data.tailBudget }

/-- Pack split carry-stopped-tree Chernoff data as the standard Lemma 22.1 leaf. -/
def toChernoffStoppedTreeInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffStoppedTreeSplitBudgetData shell cPr cStar xi carryData) :
    ChernoffStoppedTreeInputData cStar xi (shell.X : Real) :=
  data.toCarryChernoffStoppedTreeBudgetData.toChernoffStoppedTreeInputData

end CarryChernoffStoppedTreeSplitBudgetData

namespace CarryChernoffStoppedTreeSeparatedBudgetData

/-- Assemble the separated Lemma 22.1 carry-stopped-tree Chernoff budget from
the pointwise tilt, aggregate moment, and final tail-smallness leaves. -/
def ofClosedLemma221
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (Y m : Nat)
    (z : {z : Real // 1 <= z})
    (root A B : Real)
    (tilt :
      ChernoffPointwiseTiltData carryData.stoppedBranches
        (fun p => (carryData.stoppedBranchWeight p : Real))
        carryData.stoppedBranchCost (z : Real) B)
    (momentBudget :
      ChernoffMomentBudgetData carryData.stoppedBranches B root A m)
    (tailBudget :
      ChernoffTailBudgetData root A (z : Real) cStar xi (shell.X : Real) m Y) :
    @CarryChernoffStoppedTreeSeparatedBudgetData shell cPr cStar xi
      carryData where
  Y := Y
  m := m
  z := z
  root := root
  A := A
  B := B
  tilt := tilt
  momentBudget := momentBudget
  tailBudget := tailBudget

/-- Carry-stopped-tree Chernoff budget with the finite pointwise/moment part
closed by the total tilted-mass budget.  The remaining input is exactly the final
tail-smallness comparison for that explicit budget choice. -/
def ofFiniteMomentAndTail
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (Y : Nat)
    (z : {z : Real // 1 <= z})
    (tailBudget :
      ChernoffTailBudgetData
        ((carryData.stoppedBranches.card : Real) *
          (carryData.stoppedBranches.sum
            (fun p => (carryData.stoppedBranchWeight p : Real) *
              (z : Real) ^ carryData.stoppedBranchCost p)))
        1 (z : Real) cStar xi (shell.X : Real) 0 Y) :
    @CarryChernoffStoppedTreeSeparatedBudgetData shell cPr cStar xi
      carryData where
  Y := Y
  m := 0
  z := z
  root :=
    ((carryData.stoppedBranches.card : Real) *
      (carryData.stoppedBranches.sum
        (fun p => (carryData.stoppedBranchWeight p : Real) *
          (z : Real) ^ carryData.stoppedBranchCost p)))
  A := 1
  B :=
    carryData.stoppedBranches.sum
      (fun p => (carryData.stoppedBranchWeight p : Real) *
        (z : Real) ^ carryData.stoppedBranchCost p)
  tilt :=
    (ChernoffPointwiseMomentData.ofFiniteSumBudget
      carryData.stoppedBranches carryData.stoppedBranchWeight
      carryData.stoppedBranchCost z).tilt
  momentBudget :=
    (ChernoffPointwiseMomentData.ofFiniteSumBudget
      carryData.stoppedBranches carryData.stoppedBranchWeight
      carryData.stoppedBranchCost z).momentBudget
  tailBudget := tailBudget

/-- Merge the three proof-v4 Chernoff leaves into the two-piece split record. -/
def toCarryChernoffStoppedTreeSplitBudgetData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffStoppedTreeSeparatedBudgetData shell cPr cStar xi
        carryData) :
    @CarryChernoffStoppedTreeSplitBudgetData shell cPr cStar xi carryData where
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

/-- Merge the three proof-v4 Chernoff leaves into the compact budget record. -/
def toCarryChernoffStoppedTreeBudgetData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffStoppedTreeSeparatedBudgetData shell cPr cStar xi
        carryData) :
    @CarryChernoffStoppedTreeBudgetData shell cPr cStar xi carryData :=
  data.toCarryChernoffStoppedTreeSplitBudgetData.toCarryChernoffStoppedTreeBudgetData

/-- Pack three-piece carry-stopped-tree Chernoff data as the standard
Lemma 22.1 leaf. -/
def toChernoffStoppedTreeInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffStoppedTreeSeparatedBudgetData shell cPr cStar xi
        carryData) :
    ChernoffStoppedTreeInputData cStar xi (shell.X : Real) :=
  data.toCarryChernoffStoppedTreeBudgetData.toChernoffStoppedTreeInputData

end CarryChernoffStoppedTreeSeparatedBudgetData

namespace CarryChernoffStoppedTreeExponentialTailData

/-- Forget only the manuscript exponential-tail derivation after deriving the
scalar tail budget. -/
def toCarryChernoffStoppedTreeSeparatedBudgetData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffStoppedTreeExponentialTailData shell cPr cStar xi
        carryData) :
    @CarryChernoffStoppedTreeSeparatedBudgetData shell cPr cStar xi
      carryData where
  Y := data.Y
  m := data.m
  z := data.z
  root := data.root
  A := data.A
  B := data.B
  tilt := data.tilt
  momentBudget := data.momentBudget
  tailBudget := data.exponentialTail.toTailBudgetData

/-- Pack exponential-tail carry Chernoff data as the standard stopped-tree leaf. -/
def toChernoffStoppedTreeInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffStoppedTreeExponentialTailData shell cPr cStar xi
        carryData) :
    ChernoffStoppedTreeInputData cStar xi (shell.X : Real) :=
  data.toCarryChernoffStoppedTreeSeparatedBudgetData.toChernoffStoppedTreeInputData

end CarryChernoffStoppedTreeExponentialTailData

namespace CarryChernoffFiniteExponentialTailData

/-- The Chernoff shell depth is the integer floor of the canonical carry
active floor, recorded as two inequalities so it does not depend on a particular
floor normal form. -/
theorem Y_le_carryY
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffFiniteExponentialTailData shell cPr cStar xi
        carryData) :
    (data.Y : Real) <= carryData.Y :=
  data.Y_floor.1

/-- The canonical carry active floor is strictly below the next integer after
the Chernoff shell depth. -/
theorem carryY_lt_Y_add_one
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffFiniteExponentialTailData shell cPr cStar xi
        carryData) :
    carryData.Y < (data.Y : Real) + 1 :=
  data.Y_floor.2

/-- Expand the canonical finite-budget Chernoff leaf to the fuller
exponential-tail record by filling the pointwise and aggregate moment budgets
from finite summation. -/
def toCarryChernoffStoppedTreeExponentialTailData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffFiniteExponentialTailData shell cPr cStar xi
        carryData) :
    @CarryChernoffStoppedTreeExponentialTailData shell cPr cStar xi
      carryData where
  Y := data.Y
  m := 0
  z := data.z
  root := carryChernoffFiniteRoot carryData (data.z : Real)
  A := 1
  B := carryChernoffFiniteTiltMass carryData (data.z : Real)
  tilt := by
    simpa [carryChernoffFiniteTiltMass] using
      (ChernoffPointwiseMomentData.ofFiniteSumBudget
        carryData.stoppedBranches carryData.stoppedBranchWeight
        carryData.stoppedBranchCost data.z).tilt
  momentBudget := by
    simpa [carryChernoffFiniteRoot, carryChernoffFiniteTiltMass] using
      (ChernoffPointwiseMomentData.ofFiniteSumBudget
        carryData.stoppedBranches carryData.stoppedBranchWeight
        carryData.stoppedBranchCost data.z).momentBudget
  exponentialTail := data.exponentialTail

/-- Project the canonical finite-budget Chernoff leaf to the separated
pointwise/moment/tail record. -/
def toCarryChernoffStoppedTreeSeparatedBudgetData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffFiniteExponentialTailData shell cPr cStar xi
        carryData) :
    @CarryChernoffStoppedTreeSeparatedBudgetData shell cPr cStar xi
      carryData :=
  data.toCarryChernoffStoppedTreeExponentialTailData.toCarryChernoffStoppedTreeSeparatedBudgetData

/-- Pack the canonical finite-budget carry Chernoff leaf as the standard
stopped-tree input. -/
def toChernoffStoppedTreeInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffFiniteExponentialTailData shell cPr cStar xi
        carryData) :
    ChernoffStoppedTreeInputData cStar xi (shell.X : Real) :=
  data.toCarryChernoffStoppedTreeSeparatedBudgetData.toChernoffStoppedTreeInputData

end CarryChernoffFiniteExponentialTailData

namespace CarryChernoffFiniteZBoundedExponentialTailData

/-- The z-bounded Chernoff shell depth is below the canonical carry active floor. -/
theorem Y_le_carryY
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffFiniteZBoundedExponentialTailData shell cPr cStar xi
        carryData) :
    (data.Y : Real) <= carryData.Y :=
  data.Y_floor.1

/-- The canonical carry active floor is strictly below the next z-bounded
Chernoff shell depth. -/
theorem carryY_lt_Y_add_one
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffFiniteZBoundedExponentialTailData shell cPr cStar xi
        carryData) :
    carryData.Y < (data.Y : Real) + 1 :=
  data.Y_floor.2

/-- The z-bounded Lemma 22.1 leaf carries the strict lower tilt choice. -/
theorem z_gt_one
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffFiniteZBoundedExponentialTailData shell cPr cStar xi
        carryData) :
    1 < (data.z : Real) :=
  data.z.property.1

/-- The z-bounded Lemma 22.1 leaf carries the manuscript upper tilt choice. -/
theorem z_lt_two
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffFiniteZBoundedExponentialTailData shell cPr cStar xi
        carryData) :
    (data.z : Real) < 2 :=
  data.z.property.2

/-- Forget the strict upper/lower manuscript tilt bounds and recover the older
finite-tail Chernoff leaf. -/
def toCarryChernoffFiniteExponentialTailData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffFiniteZBoundedExponentialTailData shell cPr cStar xi
        carryData) :
    @CarryChernoffFiniteExponentialTailData shell cPr cStar xi carryData where
  Y := data.Y
  Y_floor := data.Y_floor
  z := ⟨(data.z : Real), le_of_lt data.z_gt_one⟩
  exponentialTail := data.exponentialTail

/-- Project the z-bounded finite-budget Chernoff leaf to the separated
pointwise/moment/tail record. -/
def toCarryChernoffStoppedTreeSeparatedBudgetData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffFiniteZBoundedExponentialTailData shell cPr cStar xi
        carryData) :
    @CarryChernoffStoppedTreeSeparatedBudgetData shell cPr cStar xi
      carryData :=
  data.toCarryChernoffFiniteExponentialTailData.toCarryChernoffStoppedTreeSeparatedBudgetData

/-- Pack the z-bounded finite-budget carry Chernoff leaf as the standard
stopped-tree input. -/
def toChernoffStoppedTreeInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffFiniteZBoundedExponentialTailData shell cPr cStar xi
        carryData) :
    ChernoffStoppedTreeInputData cStar xi (shell.X : Real) :=
  data.toCarryChernoffStoppedTreeSeparatedBudgetData.toChernoffStoppedTreeInputData

end CarryChernoffFiniteZBoundedExponentialTailData

namespace CarryChernoffCanonicalYFiniteZBoundedExponentialTailData

/-- The canonical Chernoff shell depth is the Nat floor of the carry active
floor. -/
def Y
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (_data :
      @CarryChernoffCanonicalYFiniteZBoundedExponentialTailData shell cPr cStar
        xi carryData) : Nat :=
  Nat.floor carryData.Y

/-- The canonical-Y z-bounded leaf carries the strict lower tilt choice. -/
theorem z_gt_one
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFiniteZBoundedExponentialTailData shell cPr cStar
        xi carryData) :
    1 < (data.z : Real) :=
  data.z.property.1

/-- The canonical-Y z-bounded leaf carries the manuscript upper tilt choice. -/
theorem z_lt_two
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFiniteZBoundedExponentialTailData shell cPr cStar
        xi carryData) :
    (data.z : Real) < 2 :=
  data.z.property.2

/-- Forget the canonical Nat-floor choice after deriving the floor inequalities
from nonnegativity of the real carry active floor. -/
def toCarryChernoffFiniteZBoundedExponentialTailData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFiniteZBoundedExponentialTailData shell cPr cStar
        xi carryData)
    (hY_nonneg : 0 <= carryData.Y) :
    @CarryChernoffFiniteZBoundedExponentialTailData shell cPr cStar xi
      carryData where
  Y := Nat.floor carryData.Y
  Y_floor := by
    constructor
    · exact Nat.floor_le hY_nonneg
    · exact Nat.lt_floor_add_one carryData.Y
  z := data.z
  exponentialTail := data.exponentialTail

/-- Project the canonical-Y z-bounded finite-budget Chernoff leaf to the
separated pointwise/moment/tail record. -/
def toCarryChernoffStoppedTreeSeparatedBudgetData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFiniteZBoundedExponentialTailData shell cPr cStar
        xi carryData)
    (hY_nonneg : 0 <= carryData.Y) :
    @CarryChernoffStoppedTreeSeparatedBudgetData shell cPr cStar xi
      carryData :=
  (data.toCarryChernoffFiniteZBoundedExponentialTailData hY_nonneg).toCarryChernoffStoppedTreeSeparatedBudgetData

/-- Pack the canonical-Y z-bounded finite-budget carry Chernoff leaf as the
standard stopped-tree input. -/
def toChernoffStoppedTreeInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFiniteZBoundedExponentialTailData shell cPr cStar
        xi carryData)
    (hY_nonneg : 0 <= carryData.Y) :
    ChernoffStoppedTreeInputData cStar xi (shell.X : Real) :=
  (data.toCarryChernoffStoppedTreeSeparatedBudgetData hY_nonneg).toChernoffStoppedTreeInputData

end CarryChernoffCanonicalYFiniteZBoundedExponentialTailData

namespace CarryChernoffCanonicalYFixedZExponentialTailData

/-- The fixed-z leaf uses the canonical Nat floor of the carry active floor. -/
def Y
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (_data :
      @CarryChernoffCanonicalYFixedZExponentialTailData shell cPr cStar xi
        carryData) : Nat :=
  Nat.floor carryData.Y

/-- Build the fixed-z canonical-Y Chernoff leaf from the zero-length tail
comparison and the `X`-free scalar smallness comparison.  This leaves the
actual Lemma 22.1 exponential tail as the remaining analytic input, while
closing the routine multiplication by the shell size. -/
def ofScalarSmallness
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (tailConstant : Real)
    (tailExponent : Nat)
    (hX_nonneg : 0 <= (shell.X : Real))
    (exponential_tail_bound :
      carryChernoffFiniteRoot carryData (proofV4ChernoffTilt : Real) /
          (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y <=
        tailConstant * (shell.X : Real) / (2 : Real) ^ tailExponent)
    (exponential_tail_small_scalar :
      tailConstant / (2 : Real) ^ tailExponent <= cStar * xi / 6) :
    @CarryChernoffCanonicalYFixedZExponentialTailData shell cPr cStar xi
      carryData where
  exponentialTail :=
    ChernoffZeroLengthExponentialTailData.ofScalarSmallness
      tailConstant tailExponent hX_nonneg exponential_tail_bound
      exponential_tail_small_scalar

/-- Build the fixed-z canonical-Y Chernoff leaf from a numerator-style root
bound and an `X`-free scalar smallness comparison. -/
def ofRootBoundAndScalarSmallness
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (tailConstant : Real)
    (tailExponent : Nat)
    (hX_nonneg : 0 <= (shell.X : Real))
    (root_bound :
      carryChernoffFiniteRoot carryData (proofV4ChernoffTilt : Real) <=
        tailConstant * (shell.X : Real) *
            (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y /
          (2 : Real) ^ tailExponent)
    (exponential_tail_small_scalar :
      tailConstant / (2 : Real) ^ tailExponent <= cStar * xi / 6) :
    @CarryChernoffCanonicalYFixedZExponentialTailData shell cPr cStar xi
      carryData where
  exponentialTail :=
    ChernoffZeroLengthExponentialTailData.ofRootBoundAndScalarSmallness
      tailConstant tailExponent
      (by linarith [proofV4ChernoffTilt.property.1])
      hX_nonneg root_bound exponential_tail_small_scalar

/-- Forget the fixed `z = 3/2` choice to recover the canonical-Y finite-z leaf. -/
def toCarryChernoffCanonicalYFiniteZBoundedExponentialTailData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZExponentialTailData shell cPr cStar xi
        carryData) :
    @CarryChernoffCanonicalYFiniteZBoundedExponentialTailData shell cPr cStar
      xi carryData where
  z := proofV4ChernoffTilt
  exponentialTail := data.exponentialTail.toChernoffExponentialTailBudgetData

/-- Project the fixed-z canonical-Y Chernoff leaf to the separated
pointwise/moment/tail record. -/
def toCarryChernoffStoppedTreeSeparatedBudgetData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZExponentialTailData shell cPr cStar xi
        carryData)
    (hY_nonneg : 0 <= carryData.Y) :
    @CarryChernoffStoppedTreeSeparatedBudgetData shell cPr cStar xi
      carryData :=
  data.toCarryChernoffCanonicalYFiniteZBoundedExponentialTailData
    |>.toCarryChernoffStoppedTreeSeparatedBudgetData hY_nonneg

/-- Pack the fixed-z canonical-Y Chernoff leaf as the standard stopped-tree
input. -/
def toChernoffStoppedTreeInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZExponentialTailData shell cPr cStar xi
        carryData)
    (hY_nonneg : 0 <= carryData.Y) :
    ChernoffStoppedTreeInputData cStar xi (shell.X : Real) :=
  (data.toCarryChernoffStoppedTreeSeparatedBudgetData hY_nonneg).toChernoffStoppedTreeInputData

end CarryChernoffCanonicalYFixedZExponentialTailData

namespace CarryChernoffCanonicalYFixedZRootScalarInputData

/-- Convert the numerator/scalar Lemma 22.1 leaf to the fixed-z exponential
tail certificate. -/
def toCarryChernoffCanonicalYFixedZExponentialTailData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZRootScalarInputData shell cPr cStar xi
        carryData) :
    @CarryChernoffCanonicalYFixedZExponentialTailData shell cPr cStar xi
      carryData :=
  CarryChernoffCanonicalYFixedZExponentialTailData.ofRootBoundAndScalarSmallness
    data.tailConstant data.tailExponent
    (Nat.cast_nonneg shell.X)
    data.root_bound data.scalar_small

/-- Project the numerator/scalar fixed-z leaf to the separated
pointwise/moment/tail record. -/
def toCarryChernoffStoppedTreeSeparatedBudgetData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZRootScalarInputData shell cPr cStar xi
        carryData)
    (hY_nonneg : 0 <= carryData.Y) :
    @CarryChernoffStoppedTreeSeparatedBudgetData shell cPr cStar xi
      carryData :=
  data.toCarryChernoffCanonicalYFixedZExponentialTailData
    |>.toCarryChernoffStoppedTreeSeparatedBudgetData hY_nonneg

/-- Pack the numerator/scalar fixed-z leaf as the standard stopped-tree input. -/
def toChernoffStoppedTreeInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZRootScalarInputData shell cPr cStar xi
        carryData)
    (hY_nonneg : 0 <= carryData.Y) :
    ChernoffStoppedTreeInputData cStar xi (shell.X : Real) :=
  (data.toCarryChernoffStoppedTreeSeparatedBudgetData hY_nonneg).toChernoffStoppedTreeInputData

end CarryChernoffCanonicalYFixedZRootScalarInputData

namespace CarryChernoffCanonicalYFixedZTailSmallInputData

/-- Convert the manuscript tail-smallness form to the direct root-smallness
numerator form by multiplying by the positive fixed tilt power. -/
def toCarryChernoffCanonicalYFixedZRootSmallInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZTailSmallInputData shell cPr cStar xi
        carryData) :
    @CarryChernoffCanonicalYFixedZRootSmallInputData shell cPr cStar xi
      carryData where
  root_small := by
    have hz_pos :
        0 < (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y :=
      pow_pos (by linarith [proofV4ChernoffTilt.property.1]) _
    have h := (div_le_iff₀ hz_pos).1 data.tail_small
    simpa [mul_assoc] using h

/-- Expand the direct fixed-`z` tail-smallness estimate into the layer-cake
record.  The chosen layer-cake weight is the finite tilted root density itself,
so the layer-cake bookkeeping is closed canonically and the only substantive
input remains `tail_small`. -/
def toCarryChernoffCanonicalYFixedZLayerCakeTailInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZTailSmallInputData shell cPr cStar xi
        carryData) :
    @CarryChernoffCanonicalYFixedZLayerCakeTailInputData shell cPr cStar xi
      carryData where
  wt0 := fun b =>
    ((carryData.stoppedBranches.card : Real) *
        ((carryData.stoppedBranchWeight b : Real) *
          (proofV4ChernoffTilt : Real) ^ carryData.stoppedBranchCost b)) /
      (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y
  Ysh := fun _ => 1
  chernoff :=
    areaLayerSum carryData.stoppedBranches
      (fun b =>
        ((carryData.stoppedBranches.card : Real) *
            ((carryData.stoppedBranchWeight b : Real) *
              (proofV4ChernoffTilt : Real) ^ carryData.stoppedBranchCost b)) /
          (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y)
      (fun _ => 1)
  bound := (cStar * xi / 6) * (shell.X : Real)
  hYsh := by
    intro b hb
    norm_num
  hchernoff_int := by
    exact areaLayerSum_integrable carryData.stoppedBranches
      (fun b =>
        ((carryData.stoppedBranches.card : Real) *
            ((carryData.stoppedBranchWeight b : Real) *
              (proofV4ChernoffTilt : Real) ^ carryData.stoppedBranchCost b)) /
          (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y)
      (fun _ => 1)
  hlevel := by
    intro u
    exact le_rfl
  hbound := by
    have hYsh_one :
        forall b, b ∈ carryData.stoppedBranches -> 0 <= (1 : Real) := by
      intro b hb
      norm_num
    rw [integral_areaLayerSum carryData.stoppedBranches
      (fun b =>
        ((carryData.stoppedBranches.card : Real) *
            ((carryData.stoppedBranchWeight b : Real) *
              (proofV4ChernoffTilt : Real) ^ carryData.stoppedBranchCost b)) /
          (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y)
      (fun _ => 1) hYsh_one]
    have hsum :
        (∑ b ∈ carryData.stoppedBranches,
            ((carryData.stoppedBranches.card : Real) *
                ((carryData.stoppedBranchWeight b : Real) *
                  (proofV4ChernoffTilt : Real) ^ carryData.stoppedBranchCost b)) /
              (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y)
          =
        carryChernoffFiniteRoot carryData (proofV4ChernoffTilt : Real) /
          (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y := by
      simp [carryChernoffFiniteRoot, carryChernoffFiniteTiltMass,
        Finset.mul_sum, div_eq_mul_inv, mul_assoc, mul_comm]
    calc
      (∑ b ∈ carryData.stoppedBranches,
          ((carryData.stoppedBranches.card : Real) *
              ((carryData.stoppedBranchWeight b : Real) *
                (proofV4ChernoffTilt : Real) ^ carryData.stoppedBranchCost b)) /
            (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y * 1)
          =
        (∑ b ∈ carryData.stoppedBranches,
            ((carryData.stoppedBranches.card : Real) *
                ((carryData.stoppedBranchWeight b : Real) *
                  (proofV4ChernoffTilt : Real) ^ carryData.stoppedBranchCost b)) /
              (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y) := by
            simp
      _ =
        carryChernoffFiniteRoot carryData (proofV4ChernoffTilt : Real) /
          (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y := hsum
      _ <= (cStar * xi / 6) * (shell.X : Real) := data.tail_small
  finiteRoot_le_area := by
    have hsum :
        (∑ b ∈ carryData.stoppedBranches,
            ((carryData.stoppedBranches.card : Real) *
                ((carryData.stoppedBranchWeight b : Real) *
                  (proofV4ChernoffTilt : Real) ^ carryData.stoppedBranchCost b)) /
              (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y)
          =
        carryChernoffFiniteRoot carryData (proofV4ChernoffTilt : Real) /
          (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y := by
      simp [carryChernoffFiniteRoot, carryChernoffFiniteTiltMass,
        Finset.mul_sum, div_eq_mul_inv, mul_assoc, mul_comm]
    exact le_of_eq <| by
      calc
        carryChernoffFiniteRoot carryData (proofV4ChernoffTilt : Real) /
            (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y
            =
          (∑ b ∈ carryData.stoppedBranches,
              ((carryData.stoppedBranches.card : Real) *
                  ((carryData.stoppedBranchWeight b : Real) *
                    (proofV4ChernoffTilt : Real) ^ carryData.stoppedBranchCost b)) /
                (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y) := hsum.symm
        _ =
          (∑ b ∈ carryData.stoppedBranches,
              ((carryData.stoppedBranches.card : Real) *
                    ((carryData.stoppedBranchWeight b : Real) *
                      (proofV4ChernoffTilt : Real) ^ carryData.stoppedBranchCost b)) /
                  (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y *
                1) := by
            simp
  bound_small := by
    rfl

/-- Guardrail for the carry-specific fixed-z leaf: with the current definitions,
`carryData.stoppedBranches` is the entire high-excess family with
`windowExcessWeight` weights.  Therefore a tail-smallness proof for that whole
family is incompatible with the pressure lower bound whenever the phase budget
constant is smaller than the pressure constant.  The manuscript Chernoff leaf
must instead be attached to the regular/shell-paid phase subfamily. -/
theorem incompatible_with_pressureLower
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZTailSmallInputData shell cPr cStar xi
        carryData)
    (hT_nonneg : 0 <= carryData.T) (hY_nonneg : 0 <= carryData.Y)
    (hX_pos : 0 < (shell.X : Real))
    (hbudget_lt_pressure :
      cStar * xi / 6 < cPr * ((carryData.r : Real) + 1)) :
    False := by
  have hhigh_le_ratio :=
    carryData.highExcessMass_le_finiteRoot_div_pow_proofV4ChernoffTilt
      hT_nonneg hY_nonneg
  have hlower := carryData.highExcessMass_lower
  have hchain :
      cPr * (shell.X : Real) * ((carryData.r : Real) + 1) <=
        (cStar * xi / 6) * (shell.X : Real) :=
    hlower.trans (hhigh_le_ratio.trans data.tail_small)
  have hchain' :
      cPr * ((carryData.r : Real) + 1) <= cStar * xi / 6 := by
    have hmul :
        cPr * ((carryData.r : Real) + 1) * (shell.X : Real) <=
          (cStar * xi / 6) * (shell.X : Real) := by
      calc
        cPr * ((carryData.r : Real) + 1) * (shell.X : Real)
            = cPr * (shell.X : Real) * ((carryData.r : Real) + 1) := by
              ring
        _ <= (cStar * xi / 6) * (shell.X : Real) := hchain
    exact le_of_mul_le_mul_right hmul hX_pos
  exact (not_lt_of_ge hchain') hbudget_lt_pressure

end CarryChernoffCanonicalYFixedZTailSmallInputData

namespace CarryChernoffCanonicalYFixedZRootSmallInputData

/-- Convert the direct root-smallness numerator estimate back to the manuscript
ratio tail-smallness form by dividing by the positive fixed tilt power. -/
def toCarryChernoffCanonicalYFixedZTailSmallInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZRootSmallInputData shell cPr cStar xi
        carryData) :
    @CarryChernoffCanonicalYFixedZTailSmallInputData shell cPr cStar xi
      carryData where
  tail_small := by
    have hz_pos :
        0 < (proofV4ChernoffTilt : Real) ^ Nat.floor carryData.Y :=
      pow_pos (by linarith [proofV4ChernoffTilt.property.1]) _
    exact (div_le_iff₀ hz_pos).2 (by simpa [mul_assoc] using data.root_small)

/-- Forget the direct root-smallness leaf to the older root/scalar interface by
choosing tail constant `cStar * xi / 6` and dyadic tail exponent `0`. -/
def toCarryChernoffCanonicalYFixedZRootScalarInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZRootSmallInputData shell cPr cStar xi
        carryData) :
    @CarryChernoffCanonicalYFixedZRootScalarInputData shell cPr cStar xi
      carryData where
  tailConstant := cStar * xi / 6
  tailExponent := 0
  root_bound := by
    simpa using data.root_small
  scalar_small := by
    simp

/-- Convert the direct root-smallness Lemma 22.1 leaf to the fixed-z exponential
tail certificate. -/
def toCarryChernoffCanonicalYFixedZExponentialTailData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZRootSmallInputData shell cPr cStar xi
        carryData) :
    @CarryChernoffCanonicalYFixedZExponentialTailData shell cPr cStar xi
      carryData :=
  data.toCarryChernoffCanonicalYFixedZRootScalarInputData
    |>.toCarryChernoffCanonicalYFixedZExponentialTailData

/-- Project the direct fixed-z leaf to the separated pointwise/moment/tail
record. -/
def toCarryChernoffStoppedTreeSeparatedBudgetData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZRootSmallInputData shell cPr cStar xi
        carryData)
    (hY_nonneg : 0 <= carryData.Y) :
    @CarryChernoffStoppedTreeSeparatedBudgetData shell cPr cStar xi
      carryData :=
  data.toCarryChernoffCanonicalYFixedZRootScalarInputData
    |>.toCarryChernoffStoppedTreeSeparatedBudgetData hY_nonneg

/-- Pack the direct fixed-z leaf as the standard stopped-tree input. -/
def toChernoffStoppedTreeInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZRootSmallInputData shell cPr cStar xi
        carryData)
    (hY_nonneg : 0 <= carryData.Y) :
    ChernoffStoppedTreeInputData cStar xi (shell.X : Real) :=
  (data.toCarryChernoffStoppedTreeSeparatedBudgetData hY_nonneg).toChernoffStoppedTreeInputData

end CarryChernoffCanonicalYFixedZRootSmallInputData

namespace CarryChernoffCanonicalYFixedZTailSmallInputData

/-- Convert the manuscript tail-smallness leaf to the fixed-z exponential-tail
certificate through the existing root-smallness projection. -/
def toCarryChernoffCanonicalYFixedZExponentialTailData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZTailSmallInputData shell cPr cStar xi
        carryData) :
    @CarryChernoffCanonicalYFixedZExponentialTailData shell cPr cStar xi
      carryData :=
  data.toCarryChernoffCanonicalYFixedZRootSmallInputData
    |>.toCarryChernoffCanonicalYFixedZExponentialTailData

/-- Project the tail-smallness fixed-z leaf to the separated
pointwise/moment/tail record. -/
def toCarryChernoffStoppedTreeSeparatedBudgetData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZTailSmallInputData shell cPr cStar xi
        carryData)
    (hY_nonneg : 0 <= carryData.Y) :
    @CarryChernoffStoppedTreeSeparatedBudgetData shell cPr cStar xi
      carryData :=
  data.toCarryChernoffCanonicalYFixedZRootSmallInputData
    |>.toCarryChernoffStoppedTreeSeparatedBudgetData hY_nonneg

/-- Pack the tail-smallness fixed-z leaf as the standard stopped-tree input. -/
def toChernoffStoppedTreeInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZTailSmallInputData shell cPr cStar xi
        carryData)
    (hY_nonneg : 0 <= carryData.Y) :
    ChernoffStoppedTreeInputData cStar xi (shell.X : Real) :=
  (data.toCarryChernoffStoppedTreeSeparatedBudgetData hY_nonneg).toChernoffStoppedTreeInputData

end CarryChernoffCanonicalYFixedZTailSmallInputData

namespace CarryChernoffCanonicalYFixedZLayerCakeTailInputData

/-- Apply the formalized 22.1A layer-cake theorem to the stopped shell family. -/
theorem area_bound
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZLayerCakeTailInputData shell cPr cStar xi
        carryData) :
    carryData.stoppedBranches.sum (fun b => data.wt0 b * data.Ysh b) <=
      data.bound := by
  simpa using
    (lemma22_1A_areaWeightedShellChernoff carryData.stoppedBranches data.wt0
      data.Ysh data.chernoff data.bound data.hYsh data.hchernoff_int
      data.hlevel data.hbound)

/-- Collapse the 22.1A layer-cake certificate to the fixed-`z` tail-smallness
leaf consumed by the existing stopped-tree Chernoff projection. -/
def toCarryChernoffCanonicalYFixedZTailSmallInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZLayerCakeTailInputData shell cPr cStar xi
        carryData) :
    @CarryChernoffCanonicalYFixedZTailSmallInputData shell cPr cStar xi
      carryData where
  tail_small :=
    data.finiteRoot_le_area.trans (data.area_bound.trans data.bound_small)

/-- Project the layer-cake leaf to the separated stopped-tree budget. -/
def toCarryChernoffStoppedTreeSeparatedBudgetData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZLayerCakeTailInputData shell cPr cStar xi
        carryData)
    (hY_nonneg : 0 <= carryData.Y) :
    @CarryChernoffStoppedTreeSeparatedBudgetData shell cPr cStar xi
      carryData :=
  data.toCarryChernoffCanonicalYFixedZTailSmallInputData
    |>.toCarryChernoffStoppedTreeSeparatedBudgetData hY_nonneg

/-- Pack the layer-cake leaf as the standard stopped-tree Chernoff input. -/
def toChernoffStoppedTreeInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffCanonicalYFixedZLayerCakeTailInputData shell cPr cStar xi
        carryData)
    (hY_nonneg : 0 <= carryData.Y) :
    ChernoffStoppedTreeInputData cStar xi (shell.X : Real) :=
  (data.toCarryChernoffStoppedTreeSeparatedBudgetData hY_nonneg).toChernoffStoppedTreeInputData

end CarryChernoffCanonicalYFixedZLayerCakeTailInputData

/-- Recover the Lemma 22.1 stopped-tree leaf carried by grounded Chernoff data. -/
def GroundedChernoffLocalData.toStoppedTreeInputData
    {cStar xi X : Real}
    (data : GroundedChernoffLocalData cStar xi X) :
    ChernoffStoppedTreeInputData cStar xi X where
  Path := _
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

/-- The real-valued Chernoff path weights underlying the nonnegative masses. -/
def GroundedChernoffLocalData.weightReal
    {cStar xi X : Real} (data : GroundedChernoffLocalData cStar xi X) :
    data.α -> Real :=
  fun p => data.weight p

/-- Chernoff path weights are nonnegative by type. -/
theorem GroundedChernoffLocalData.weight_nonneg
    {cStar xi X : Real} (data : GroundedChernoffLocalData cStar xi X) :
    forall p, p ∈ data.paths -> 0 <= data.weightReal p := by
  intro p _hp
  exact (data.weight p).property

/-- The Chernoff tilt parameter is at least one by type. -/
theorem GroundedChernoffLocalData.z_ge_one
    {cStar xi X : Real} (data : GroundedChernoffLocalData cStar xi X) :
    1 <= (data.z : Real) :=
  data.z.property

/-- Lemma 22.1 pointwise tilted estimate carried by grounded Chernoff data. -/
def GroundedChernoffLocalData.tiltData
    {cStar xi X : Real} (data : GroundedChernoffLocalData cStar xi X) :
    ChernoffPointwiseTiltData data.paths data.weightReal data.cost data.z data.B := by
  simpa [GroundedChernoffLocalData.weightReal] using
    data.chernoff_input.tiltBudget.tilt

/-- Lemma 22.1 aggregate stopped-tree moment budget carried by grounded
Chernoff data. -/
def GroundedChernoffLocalData.momentBudgetData
    {cStar xi X : Real} (data : GroundedChernoffLocalData cStar xi X) :
    ChernoffMomentBudgetData data.paths data.B data.root data.A data.m :=
  data.chernoff_input.tiltBudget.momentBudget

/-- Lemma 22.1 pointwise tilted estimate plus aggregate moment budget, assembled
from the proof-v4 tilt and moment-budget certificates. -/
def GroundedChernoffLocalData.tiltBudget
    {cStar xi X : Real} (data : GroundedChernoffLocalData cStar xi X) :
    ChernoffPointwiseMomentData data.paths data.weightReal data.cost
      data.z data.root data.A data.B data.m := by
  simpa [GroundedChernoffLocalData.weightReal] using
    data.chernoff_input.tiltBudget

/-- Lemma 22.1 final shell-Chernoff tail budget carried by grounded Chernoff
data. -/
def GroundedChernoffLocalData.tailBudget
    {cStar xi X : Real} (data : GroundedChernoffLocalData cStar xi X) :
    ChernoffTailBudgetData data.root data.A data.z cStar xi X data.m data.Y :=
  data.chernoff_input.tailBudget

/-- Lemma 22.1 moment bound derived from pointwise regular-edge tilted estimates. -/
theorem GroundedChernoffLocalData.moment_bound
    {cStar xi X : Real} (data : GroundedChernoffLocalData cStar xi X) :
    ∑ p ∈ data.paths, data.weightReal p * data.z ^ data.cost p <=
      data.root * data.A ^ data.m :=
  data.tiltBudget.moment_bound

/-- The manuscript smallness bound for the resulting shell-Chernoff tail. -/
theorem GroundedChernoffLocalData.tail_bound
    {cStar xi X : Real} (data : GroundedChernoffLocalData cStar xi X) :
    data.root * data.A ^ data.m / data.z ^ data.Y <= cStar * xi * X / 6 :=
  data.tailBudget.tail_bound

/-- Convert pointwise-tilt Chernoff data into the existing path-data package. -/
def GroundedChernoffLocalData.toChernoffPathData
    {cStar xi X : Real}
    (data : GroundedChernoffLocalData cStar xi X) :
    ChernoffPathData cStar xi X where
  α := data.α
  paths := data.paths
  weight := data.weightReal
  cost := data.cost
  Y := data.Y
  m := data.m
  z := data.z
  root := data.root
  A := data.A
  weight_nonneg := data.weight_nonneg
  z_ge_one := data.z_ge_one
  moment_bound := data.moment_bound
  manuscript_bound := data.tail_bound

/-- Final Lemma 22.1 shell-Chernoff bound for the grounded local data. -/
theorem GroundedChernoffLocalData.chernoff_bound
    {cStar xi X : Real} (data : GroundedChernoffLocalData cStar xi X) :
    ∃ Regular : Real,
      0 <= Regular ∧ Regular <= cStar * xi * X / 6 :=
  chernoffPathSpace data.toChernoffPathData

namespace ChernoffStoppedTreeInputData

/-- Final Lemma 22.1 shell-Chernoff bound projected directly from the stopped-tree leaf. -/
theorem chernoff_bound
    {cStar xi X : Real} (data : ChernoffStoppedTreeInputData cStar xi X) :
    ∃ Regular : Real,
      0 <= Regular ∧ Regular <= cStar * xi * X / 6 :=
  data.toGroundedChernoffLocalData.chernoff_bound

end ChernoffStoppedTreeInputData

namespace CarryChernoffStoppedTreeExponentialTailData

/-- Final Lemma 22.1 shell-Chernoff bound projected from the exponential-tail
carry stopped-tree certificate. -/
theorem chernoff_bound
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffStoppedTreeExponentialTailData shell cPr cStar xi
        carryData) :
    ∃ Regular : Real,
      0 <= Regular ∧ Regular <= cStar * xi * (shell.X : Real) / 6 :=
  data.toChernoffStoppedTreeInputData.chernoff_bound

end CarryChernoffStoppedTreeExponentialTailData

namespace CarryChernoffFiniteExponentialTailData

/-- Final Lemma 22.1 shell-Chernoff bound projected from the canonical
finite-budget exponential-tail carry certificate. -/
theorem chernoff_bound
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      @CarryChernoffFiniteExponentialTailData shell cPr cStar xi
        carryData) :
    ∃ Regular : Real,
      0 <= Regular ∧ Regular <= cStar * xi * (shell.X : Real) / 6 :=
  data.toChernoffStoppedTreeInputData.chernoff_bound

end CarryChernoffFiniteExponentialTailData

/--
Core global assembly where carry, Chernoff, DensePack, and high-excess use their
current proof-v4 grounded interfaces.
-/
structure GlobalAssemblyCoreGroundedCarryChernoffDensePackHighExcessInputs where
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
        CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ
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

/-- Convert the grounded carry/Chernoff/DensePack/high-excess interface to per-failure assembly. -/
def GlobalAssemblyCoreGroundedCarryChernoffDensePackHighExcessInputs.toGlobalPerFailureAssembly
    (data : GlobalAssemblyCoreGroundedCarryChernoffDensePackHighExcessInputs) :
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
      cnl := data.cnl shell hcQ
      tower := data.tower shell hcQ
      densePack := (data.densePack shell hcQ).toDensePackFactoryData
      returnPkg := data.returnPkg shell hcQ
      run := data.run shell hcQ }
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases
        ((data.carry shell hcQ).toCarryData)
        ((data.highExcess shell hcQ phases).toHighExcessChargeData)

/--
Erdos 260 from the core interface whose carry, Chernoff, DensePack, and
high-excess packages are supplied through proof-v4 aligned constructors.
-/
theorem erdos260_final_core_grounded_carry_chernoff_densePack_highExcess
    (data : GlobalAssemblyCoreGroundedCarryChernoffDensePackHighExcessInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

end

end Erdos260
