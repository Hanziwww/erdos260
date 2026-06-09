import Mathlib
import Erdos260.GlobalChernoffAssembly
import Erdos260.GlobalCarryShellAssembly
import Erdos260.AppendixL
import Erdos260.Constants

/-!
# Lemma 22.1A shell-paid Chernoff leaf construction

Builds `RegularShellPaidChernoff22_1AInputData` at each small-large failing shell.
The faithful route consumes the actual stopped regular/shell-paid family from
proof-v4 Lemma 22.1A.  No no-input empty-family constructor is exported here:
the final certificate must supply the real stopped shell-paid data.
-/

namespace Erdos260

open MeasureTheory

noncomputable section

/-- Public constructor for the faithful Lemma 22.1A route. -/
def shellPaidChernoff22_1AFromInput
    {cStar xi X : Real}
    (data : RegularShellPaidChernoff22_1AInputData cStar xi X) :
    RegularShellPaidChernoff22_1AInputData cStar xi X :=
  data

/-- Faithful Lemma 22.1A route from a concrete stopped regular/shell-paid
family and its shell-paid multiplier.

The finite layer-cake identity, integrability, and per-level bookkeeping are
closed by `RegularShellPaidChernoff22_1AInputData.ofAreaLayerSumStoppedTree`;
the remaining manuscript input is exactly the final selected-family area
smallness bound from proof_v4 lines 751-792. -/
def shellPaidChernoff22_1AFromAreaLayerSumStoppedTree
    {cStar xi X : Real}
    (stoppedTree : ChernoffStoppedTreeInputData cStar xi X)
    (Ysh : stoppedTree.Path -> Real)
    (hYsh : forall b, b ∈ stoppedTree.paths -> 0 <= Ysh b)
    (area_small :
      (∑ b ∈ stoppedTree.paths, (stoppedTree.weight b : Real) * Ysh b) <=
        cStar * xi * X / 6) :
    RegularShellPaidChernoff22_1AInputData cStar xi X :=
  RegularShellPaidChernoff22_1AInputData.ofAreaLayerSumStoppedTree
    stoppedTree Ysh hYsh area_small

/--
Proof-v4 Lemma 22.1A provider surface tied to the concrete carry
`StoppedBranch` skeleton.

This is the certificate-boundary version of the shell-paid Chernoff leaf: the
stopped-tree path type is no longer an unrelated dependent `Path`, but the
faithful I.9 branch family produced from the carry data.  The remaining fields
are the actual manuscript content: the stopped-tree Chernoff certificate, the
nonnegative shell-paid multiplier, and the proof-v4 layer-cake estimate
`S(u)` whose integral fits inside the phase budget.  The family is a concrete
`Finset StoppedBranch`, not necessarily all carry high-excess branches;
`paths_subset_carry` records the carry alignment without reintroducing the
over-strong whole-carry tail proxy.
-/
structure CarryStoppedBranchShellPaidChernoff22_1AInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    (carryData : CarryDataFromFailure shell cPr) where
  paths : Finset StoppedBranch
  weight : StoppedBranch -> {x : Real // 0 <= x}
  cost : StoppedBranch -> Nat
  paths_subset_carry : paths ⊆ carryData.stoppedBranches
  Y : Nat
  m : Nat
  z : {z : Real // 1 <= z}
  root : Real
  A : Real
  B : Real
  chernoff_input :
    ChernoffShellBudgetData paths
      (fun p => (weight p : Real)) cost (z : Real) root A B m Y
      cStar xi (shell.X : Real)
  Ysh : StoppedBranch -> Real
  hYsh : forall b, b ∈ paths -> 0 <= Ysh b
  chernoff : Real -> Real
  bound : Real
  hchernoff_int : Integrable chernoff volume
  hlevel :
    forall u, areaLayerSum paths (fun b => (weight b : Real)) Ysh u <= chernoff u
  hbound : ∫ u, chernoff u <= bound
  bound_small :
    bound <= cStar * xi * (shell.X : Real) / 6

/-- Identity constructor for the strongest carry-`StoppedBranch` Lemma 22.1A
leaf consumed by the preferred strict endpoint. -/
def carryStoppedBranchShellPaidChernoff22_1AFromInput
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      CarryStoppedBranchShellPaidChernoff22_1AInputData
        (cStar := cStar) (xi := xi) carryData) :
    CarryStoppedBranchShellPaidChernoff22_1AInputData
      (cStar := cStar) (xi := xi) carryData :=
  data

namespace CarryStoppedBranchShellPaidChernoff22_1AInputData

/-- Project the carry-specific shell-paid input to the concrete stopped-tree
Chernoff leaf. -/
def toStoppedTree
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      CarryStoppedBranchShellPaidChernoff22_1AInputData
        (cStar := cStar) (xi := xi) carryData) :
    ChernoffStoppedTreeInputData cStar xi (shell.X : Real) where
  Path := StoppedBranch
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

/-- The shell-paid stopped family is concretely aligned with the carry
`StoppedBranch` skeleton. -/
theorem stoppedTree_paths_subset_carry
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      CarryStoppedBranchShellPaidChernoff22_1AInputData
        (cStar := cStar) (xi := xi) carryData) :
    data.toStoppedTree.paths ⊆ carryData.stoppedBranches := by
  simpa [toStoppedTree] using data.paths_subset_carry

/-- Project the carry-specific proof-v4 Lemma 22.1A package to the standard
regular/shell-paid Chernoff leaf consumed by the final phase core. -/
def toRegularShellPaidChernoff22_1AInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      CarryStoppedBranchShellPaidChernoff22_1AInputData
        (cStar := cStar) (xi := xi) carryData) :
    RegularShellPaidChernoff22_1AInputData cStar xi (shell.X : Real) :=
  { stoppedTree := data.toStoppedTree
    wt0 := fun b => (data.weight b : Real)
    Ysh := data.Ysh
    chernoff := data.chernoff
    bound := data.bound
    hYsh := by
      intro b hb
      exact data.hYsh b (by
        simpa [toStoppedTree] using hb)
    hchernoff_int := data.hchernoff_int
    hlevel := by
      intro u
      simpa [toStoppedTree] using data.hlevel u
    hbound := data.hbound
    bound_small := data.bound_small }

/-- The standard regular/shell-paid leaf produced from the carry-specific route
keeps the same concrete carry-aligned stopped-family boundary. -/
theorem regularShellPaid_paths_subset_carry
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      CarryStoppedBranchShellPaidChernoff22_1AInputData
        (cStar := cStar) (xi := xi) carryData) :
    data.toRegularShellPaidChernoff22_1AInputData.stoppedTree.paths ⊆
      carryData.stoppedBranches := by
  simpa [toRegularShellPaidChernoff22_1AInputData] using
    data.stoppedTree_paths_subset_carry

/-- The carry-specific layer-cake majorant proves the final finite shell-paid
area smallness required by the area-sum boundary. -/
theorem area_small_of_layerCake
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      CarryStoppedBranchShellPaidChernoff22_1AInputData
        (cStar := cStar) (xi := xi) carryData) :
    (∑ b ∈ data.paths, (data.weight b : Real) * data.Ysh b) <=
      cStar * xi * (shell.X : Real) / 6 := by
  exact
    (lemma22_1A_areaWeightedShellChernoff data.paths
      (fun b => (data.weight b : Real)) data.Ysh data.chernoff data.bound
      data.hYsh data.hchernoff_int data.hlevel data.hbound).trans
      data.bound_small

end CarryStoppedBranchShellPaidChernoff22_1AInputData

/-- Build the carry-`StoppedBranch` Lemma 22.1A package from the full stopped
tree attached to the carry/failure shell.

This route fixes the path family, weights, and costs to the concrete I.9 carry
skeleton.  The provider still supplies the actual proof-v4 Chernoff budget,
shell-paid multiplier, layer-cake domination, integrability, and final
smallness estimate. -/
def carryStoppedBranchShellPaidChernoff22_1AFromFullCarryTree
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    (carryData : CarryDataFromFailure shell cPr)
    (Y m : Nat)
    (z : {z : Real // 1 <= z})
    (root A B : Real)
    (chernoff_input :
      ChernoffShellBudgetData carryData.stoppedBranches
        (fun p => (carryData.stoppedBranchWeight p : Real))
        carryData.stoppedBranchCost (z : Real) root A B m Y
        cStar xi (shell.X : Real))
    (Ysh : StoppedBranch -> Real)
    (hYsh : forall b, b ∈ carryData.stoppedBranches -> 0 <= Ysh b)
    (chernoff : Real -> Real)
    (bound : Real)
    (hchernoff_int : Integrable chernoff volume)
    (hlevel :
      forall u,
        areaLayerSum carryData.stoppedBranches
          (fun b => (carryData.stoppedBranchWeight b : Real)) Ysh u <=
            chernoff u)
    (hbound : ∫ u, chernoff u <= bound)
    (bound_small : bound <= cStar * xi * (shell.X : Real) / 6) :
    CarryStoppedBranchShellPaidChernoff22_1AInputData
      (cStar := cStar) (xi := xi) carryData where
  paths := carryData.stoppedBranches
  weight := carryData.stoppedBranchWeight
  cost := carryData.stoppedBranchCost
  paths_subset_carry := by
    intro b hb
    exact hb
  Y := Y
  m := m
  z := z
  root := root
  A := A
  B := B
  chernoff_input := chernoff_input
  Ysh := Ysh
  hYsh := hYsh
  chernoff := chernoff
  bound := bound
  hchernoff_int := hchernoff_int
  hlevel := hlevel
  hbound := hbound
  bound_small := bound_small

/--
Carry-aligned proof-v4 Lemma 22.1A route from the finite layer-cake area sum.

This is the carry-specific analogue of
`RegularShellPaidChernoff22_1AInputData.ofAreaLayerSumStoppedTree`: once the
provider has supplied the concrete stopped regular/shell-paid family, its
nonnegative shell-paid multiplier, the stopped-tree Chernoff budget, and the
final area smallness estimate from proof_v4 lines 751--792, the integrability,
level-set domination, and layer-cake integral bookkeeping are finite-sum facts.
-/
def carryStoppedBranchShellPaidChernoff22_1AFromAreaLayerSumStoppedTree
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (paths : Finset StoppedBranch)
    (weight : StoppedBranch -> {x : Real // 0 <= x})
    (cost : StoppedBranch -> Nat)
    (paths_subset_carry : paths ⊆ carryData.stoppedBranches)
    (Y m : Nat)
    (z : {z : Real // 1 <= z})
    (root A B : Real)
    (chernoff_input :
      ChernoffShellBudgetData paths (fun p => (weight p : Real)) cost
        (z : Real) root A B m Y cStar xi (shell.X : Real))
    (Ysh : StoppedBranch -> Real)
    (hYsh : forall b, b ∈ paths -> 0 <= Ysh b)
    (area_small :
      (∑ b ∈ paths, (weight b : Real) * Ysh b) <=
        cStar * xi * (shell.X : Real) / 6) :
    CarryStoppedBranchShellPaidChernoff22_1AInputData
      (cStar := cStar) (xi := xi) carryData where
  paths := paths
  weight := weight
  cost := cost
  paths_subset_carry := paths_subset_carry
  Y := Y
  m := m
  z := z
  root := root
  A := A
  B := B
  chernoff_input := chernoff_input
  Ysh := Ysh
  hYsh := hYsh
  chernoff := areaLayerSum paths (fun b => (weight b : Real)) Ysh
  bound := ∑ b ∈ paths, (weight b : Real) * Ysh b
  hchernoff_int := areaLayerSum_integrable paths
    (fun b => (weight b : Real)) Ysh
  hlevel := by
    intro u
    exact le_rfl
  hbound := by
    rw [integral_areaLayerSum paths (fun b => (weight b : Real)) Ysh hYsh]
  bound_small := area_small

/-- Structured carry-aligned proof-v4 Lemma 22.1A input in finite layer-cake
form.

This is the final-certificate-friendly boundary for the Chernoff leaf: the
provider supplies the actual stopped shell-paid family, weights/costs, the
nonnegative shell-paid multiplier, and the final area smallness estimate.  The
integrable majorant and layer-cake identity are generated by
`carryStoppedBranchShellPaidChernoff22_1AFromAreaLayerSumStoppedTree`. -/
structure CarryStoppedBranchShellPaidChernoff22_1AAreaLayerSumInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    (carryData : CarryDataFromFailure shell cPr) where
  paths : Finset StoppedBranch
  weight : StoppedBranch -> {x : Real // 0 <= x}
  cost : StoppedBranch -> Nat
  paths_subset_carry : paths ⊆ carryData.stoppedBranches
  Y : Nat
  m : Nat
  z : {z : Real // 1 <= z}
  root : Real
  A : Real
  B : Real
  chernoff_input :
    ChernoffShellBudgetData paths (fun p => (weight p : Real)) cost
      (z : Real) root A B m Y cStar xi (shell.X : Real)
  Ysh : StoppedBranch -> Real
  hYsh : forall b, b ∈ paths -> 0 <= Ysh b
  area_small :
    (∑ b ∈ paths, (weight b : Real) * Ysh b) <=
      cStar * xi * (shell.X : Real) / 6

namespace CarryStoppedBranchShellPaidChernoff22_1AAreaLayerSumInputData

/-- Package the raw proof-v4 22.1A carry-stopped finite layer-cake fields into
the structured final-provider input. -/
def ofAreaLayerSumFields
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (paths : Finset StoppedBranch)
    (weight : StoppedBranch -> {x : Real // 0 <= x})
    (cost : StoppedBranch -> Nat)
    (paths_subset_carry : paths ⊆ carryData.stoppedBranches)
    (Y m : Nat)
    (z : {z : Real // 1 <= z})
    (root A B : Real)
    (chernoff_input :
      ChernoffShellBudgetData paths (fun p => (weight p : Real)) cost
        (z : Real) root A B m Y cStar xi (shell.X : Real))
    (Ysh : StoppedBranch -> Real)
    (hYsh : forall b, b ∈ paths -> 0 <= Ysh b)
    (area_small :
      (∑ b ∈ paths, (weight b : Real) * Ysh b) <=
        cStar * xi * (shell.X : Real) / 6) :
    CarryStoppedBranchShellPaidChernoff22_1AAreaLayerSumInputData
      (cStar := cStar) (xi := xi) carryData where
  paths := paths
  weight := weight
  cost := cost
  paths_subset_carry := paths_subset_carry
  Y := Y
  m := m
  z := z
  root := root
  A := A
  B := B
  chernoff_input := chernoff_input
  Ysh := Ysh
  hYsh := hYsh
  area_small := area_small

/-- Build the finite layer-cake 22.1A input from an already-packaged
carry-stopped-tree Chernoff budget on the full carry skeleton.

The caller still supplies the actual shell-paid multiplier and the final
area-smallness estimate; this constructor only avoids re-listing the full
carry path family, weights, costs, and Lemma 22.1 budget fields. -/
def ofCarryStoppedTreeBudget
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (budget :
      @CarryChernoffStoppedTreeBudgetData shell cPr cStar xi carryData)
    (Ysh : StoppedBranch -> Real)
    (hYsh :
      forall b, b ∈ carryData.stoppedBranches -> 0 <= Ysh b)
    (area_small :
      carryData.stoppedBranches.sum
          (fun b => (carryData.stoppedBranchWeight b : Real) * Ysh b) <=
        cStar * xi * (shell.X : Real) / 6) :
    CarryStoppedBranchShellPaidChernoff22_1AAreaLayerSumInputData
      (cStar := cStar) (xi := xi) carryData where
  paths := carryData.stoppedBranches
  weight := carryData.stoppedBranchWeight
  cost := carryData.stoppedBranchCost
  paths_subset_carry := by
    intro b hb
    exact hb
  Y := budget.Y
  m := budget.m
  z := budget.z
  root := budget.root
  A := budget.A
  B := budget.B
  chernoff_input := budget.chernoff_input
  Ysh := Ysh
  hYsh := hYsh
  area_small := area_small

/-- Project the structured finite layer-cake input to the strongest
carry-`StoppedBranch` Chernoff leaf. -/
def toCarryStoppedBranchShellPaidChernoff22_1AInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      CarryStoppedBranchShellPaidChernoff22_1AAreaLayerSumInputData
        (cStar := cStar) (xi := xi) carryData) :
    CarryStoppedBranchShellPaidChernoff22_1AInputData
      (cStar := cStar) (xi := xi) carryData :=
  carryStoppedBranchShellPaidChernoff22_1AFromAreaLayerSumStoppedTree
    data.paths data.weight data.cost data.paths_subset_carry data.Y data.m
    data.z data.root data.A data.B data.chernoff_input data.Ysh data.hYsh
    data.area_small

end CarryStoppedBranchShellPaidChernoff22_1AAreaLayerSumInputData

namespace CarryStoppedBranchShellPaidChernoff22_1AInputData

/-- Forget only the explicit layer-cake majorant, recovering the structured
finite-area-sum 22.1A input used by the final strict provider. -/
def toAreaLayerSumInputData
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      CarryStoppedBranchShellPaidChernoff22_1AInputData
        (cStar := cStar) (xi := xi) carryData) :
    CarryStoppedBranchShellPaidChernoff22_1AAreaLayerSumInputData
      (cStar := cStar) (xi := xi) carryData where
  paths := data.paths
  weight := data.weight
  cost := data.cost
  paths_subset_carry := data.paths_subset_carry
  Y := data.Y
  m := data.m
  z := data.z
  root := data.root
  A := data.A
  B := data.B
  chernoff_input := data.chernoff_input
  Ysh := data.Ysh
  hYsh := data.hYsh
  area_small := data.area_small_of_layerCake

end CarryStoppedBranchShellPaidChernoff22_1AInputData

/-- Public proof-v4 22.1A route from the structured finite layer-cake input to
the carry-`StoppedBranch` Chernoff leaf. -/
def carryStoppedBranchShellPaidChernoff22_1AFromAreaLayerSumInput
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      CarryStoppedBranchShellPaidChernoff22_1AAreaLayerSumInputData
        (cStar := cStar) (xi := xi) carryData) :
    CarryStoppedBranchShellPaidChernoff22_1AInputData
      (cStar := cStar) (xi := xi) carryData :=
  data.toCarryStoppedBranchShellPaidChernoff22_1AInputData

/-- Public carry-stopped 22.1A route from the raw finite layer-cake fields. -/
def carryStoppedBranchShellPaidChernoff22_1AFromRawAreaLayerSumInput
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (paths : Finset StoppedBranch)
    (weight : StoppedBranch -> {x : Real // 0 <= x})
    (cost : StoppedBranch -> Nat)
    (paths_subset_carry : paths ⊆ carryData.stoppedBranches)
    (Y m : Nat)
    (z : {z : Real // 1 <= z})
    (root A B : Real)
    (chernoff_input :
      ChernoffShellBudgetData paths (fun p => (weight p : Real)) cost
        (z : Real) root A B m Y cStar xi (shell.X : Real))
    (Ysh : StoppedBranch -> Real)
    (hYsh : forall b, b ∈ paths -> 0 <= Ysh b)
    (area_small :
      (∑ b ∈ paths, (weight b : Real) * Ysh b) <=
        cStar * xi * (shell.X : Real) / 6) :
    CarryStoppedBranchShellPaidChernoff22_1AInputData
      (cStar := cStar) (xi := xi) carryData :=
  carryStoppedBranchShellPaidChernoff22_1AFromAreaLayerSumInput
    (CarryStoppedBranchShellPaidChernoff22_1AAreaLayerSumInputData.ofAreaLayerSumFields
      paths weight cost paths_subset_carry Y m z root A B chernoff_input
      Ysh hYsh area_small)

/-- Public carry-stopped 22.1A route from a full carry stopped-tree Chernoff
budget plus the shell-paid multiplier and final area-smallness estimate. -/
def carryStoppedBranchShellPaidChernoff22_1AFromCarryStoppedTreeBudgetAreaLayer
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (budget :
      @CarryChernoffStoppedTreeBudgetData shell cPr cStar xi carryData)
    (Ysh : StoppedBranch -> Real)
    (hYsh :
      forall b, b ∈ carryData.stoppedBranches -> 0 <= Ysh b)
    (area_small :
      carryData.stoppedBranches.sum
          (fun b => (carryData.stoppedBranchWeight b : Real) * Ysh b) <=
        cStar * xi * (shell.X : Real) / 6) :
    CarryStoppedBranchShellPaidChernoff22_1AInputData
      (cStar := cStar) (xi := xi) carryData :=
  carryStoppedBranchShellPaidChernoff22_1AFromAreaLayerSumInput
    (CarryStoppedBranchShellPaidChernoff22_1AAreaLayerSumInputData.ofCarryStoppedTreeBudget
      budget Ysh hYsh area_small)

/-- Public constructor for the faithful carry-`StoppedBranch` Lemma 22.1A route. -/
def shellPaidChernoff22_1AFromCarryStoppedBranchAreaLayerSum
    {shell : FailingDyadicShell} {cPr cStar xi : Real}
    {carryData : CarryDataFromFailure shell cPr}
    (data :
      CarryStoppedBranchShellPaidChernoff22_1AInputData
        (cStar := cStar) (xi := xi) carryData) :
    RegularShellPaidChernoff22_1AInputData cStar xi (shell.X : Real) :=
  data.toRegularShellPaidChernoff22_1AInputData

/-- Remaining proof-v4 data still needed to replace the legacy empty leaf below. -/
def shellPaidChernoff22_1AOpenItems : List String :=
  [ "22.1A stopped regular/shell-paid branch family",
    "nonnegative shell-paid multipliers for the stopped family",
    "final finite layer-cake area smallness bound C_Q X |I_j| 2^{-cY} + o(s X |I_j|)",
    "L.6.2 bounded-overlap embedding of paid terminal outputs into this family" ]

theorem shellPaidChernoff22_1AOpenItems_nonempty :
    shellPaidChernoff22_1AOpenItems = [] -> False := by
  intro h
  simp [shellPaidChernoff22_1AOpenItems] at h

/--
Proof-v4 Lemma L.6.2 bridge from paid terminal outputs to a stopped
regular/shell-paid Chernoff family.

The data records the finite-overlap embedding in L.6.2: the paid terminal mass
is dominated by a bounded-overlap multiple of the shell-paid area carried by the
Lemma 22.1A leaf.  The last field is the numerical bookkeeping that absorbs
that bounded-overlap Chernoff budget into the terminal estimate's main and
remainder terms.
-/
structure ShellPaidTerminalEmbeddingData
    {cStar xi X : Real}
    (leaf : RegularShellPaidChernoff22_1AInputData cStar xi X) where
  paidMass : Real
  overlap : Real
  mainPaid : Real
  remPaid : Real
  overlap_nonneg : 0 <= overlap
  paid_le_shellArea :
    paidMass <=
      overlap * (∑ b ∈ leaf.stoppedTree.paths, leaf.wt0 b * leaf.Ysh b)
  overlap_budget :
    overlap * (cStar * xi * X / 6) <= mainPaid + remPaid

namespace ShellPaidTerminalEmbeddingData

/-- L.6.2 after the stopped shell-paid embedding is connected to Lemma 22.1A. -/
theorem paid_le_mainPaid_add_remPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    (data : ShellPaidTerminalEmbeddingData leaf) :
    data.paidMass <= data.mainPaid + data.remPaid := by
  exact data.paid_le_shellArea.trans
    ((mul_le_mul_of_nonneg_left leaf.shellPaidArea_small data.overlap_nonneg).trans
      data.overlap_budget)

/-- Package L.6.1 and L.6.3 together with the L.6.2 shell-paid embedding as the
`CorrectedResidualWeights` aggregate used downstream. -/
def toCorrectedResidualWeights
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    (data : ShellPaidTerminalEmbeddingData leaf)
    (total low remLow : Real)
    (split : total = low + data.paidMass)
    (low_le : low <= remLow) :
    CorrectedResidualWeights where
  total := total
  low := low
  paid := data.paidMass
  mainPaid := data.mainPaid
  remLow := remLow
  remPaid := data.remPaid
  split := split
  low_le := low_le
  paid_le := data.paid_le_mainPaid_add_remPaid

end ShellPaidTerminalEmbeddingData

/--
Proof-v4 Lemma L.6.2 provider surface in finite-overlap form.

Instead of asking directly for the aggregate inequality
`paidMass <= overlap * sum shellArea`, this record keeps the manuscript-shaped
bounded-overlap routing visible: the paid mass is first distributed over the
stopped shell-paid branches, and each branch contribution is dominated by the
overlap multiple of its shell-paid area.
-/
structure ShellPaidTerminalFiniteOverlapEmbeddingData
    {cStar xi X : Real}
    (leaf : RegularShellPaidChernoff22_1AInputData cStar xi X) where
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

namespace ShellPaidTerminalFiniteOverlapEmbeddingData

/-- Collapse the finite-overlap L.6.2 routing data to the aggregate shell-paid
embedding consumed by the bounded-class residual package. -/
def toShellPaidTerminalEmbeddingData
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    (data : ShellPaidTerminalFiniteOverlapEmbeddingData leaf) :
    ShellPaidTerminalEmbeddingData leaf where
  paidMass := data.paidMass
  overlap := data.overlap
  mainPaid := data.mainPaid
  remPaid := data.remPaid
  overlap_nonneg := data.overlap_nonneg
  paid_le_shellArea := by
    refine data.paid_le_branchPaid.trans ?_
    calc
      (∑ b ∈ leaf.stoppedTree.paths, data.branchPaid b)
          <= ∑ b ∈ leaf.stoppedTree.paths,
              data.overlap * (leaf.wt0 b * leaf.Ysh b) := by
        apply Finset.sum_le_sum
        intro b hb
        exact data.branchPaid_le_overlap_shellArea b hb
      _ = data.overlap *
          (∑ b ∈ leaf.stoppedTree.paths, leaf.wt0 b * leaf.Ysh b) := by
        rw [Finset.mul_sum]
  overlap_budget := data.overlap_budget

/-- L.6.2 aggregate paid bound after combining finite overlap with Lemma 22.1A. -/
theorem paid_le_mainPaid_add_remPaid
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    (data : ShellPaidTerminalFiniteOverlapEmbeddingData leaf) :
    data.paidMass <= data.mainPaid + data.remPaid :=
  data.toShellPaidTerminalEmbeddingData.paid_le_mainPaid_add_remPaid

end ShellPaidTerminalFiniteOverlapEmbeddingData

/--
Proof-v4 N.3.2/L.6 bridge for the bounded-dirty-return terminal class.

The bounded class mass is split into a low-residual part and a paid part.  The
low part is paid by the L.6.3 remainder, while the paid part is routed through
the L.6.2 shell-paid embedding above.  The final `output_budget` field is the
constant bookkeeping that places the combined corrected residual estimate under
the table-routed N.3.3 `O_bdd` class budget.
-/
structure ShellPaidBddClassBoundData
    {cStar xi X : Real}
    (leaf : RegularShellPaidChernoff22_1AInputData cStar xi X)
    (bddMass O_bdd : Real) where
  lowMass : Real
  remLow : Real
  embedding : ShellPaidTerminalEmbeddingData leaf
  split : bddMass = lowMass + embedding.paidMass
  low_le : lowMass <= remLow
  output_budget : embedding.mainPaid + (remLow + embedding.remPaid) <= O_bdd

namespace ShellPaidBddClassBoundData

/-- N.3.2/L.6 provider surface in the manuscript's low/paid split form.

The bounded output class is the `OutputClassV4.bdd` slice of a table-routed
terminal output family.  The provider supplies the L.6.1 split on that slice,
the L.6.3 low-residual bound, the L.6.2 shell-paid embedding for the paid part,
and the final bookkeeping into the `O_bdd` class budget. -/
structure LowPaidSplitData
    {cStar xi X : Real}
    (leaf : RegularShellPaidChernoff22_1AInputData cStar xi X)
    (objects : Finset OutputObjectV4)
    (terminalWeight : OutputObjectV4 -> Real)
    (O_bdd : Real) where
  wtLow : OutputObjectV4 -> Real
  wtPaid : OutputObjectV4 -> Real
  remLow : Real
  embedding : ShellPaidTerminalEmbeddingData leaf
  paid_eq :
    embedding.paidMass =
      (∑ o ∈ objects.filter (fun o => o.cls = OutputClassV4.bdd), wtPaid o)
  split :
    ∀ o ∈ objects.filter (fun o => o.cls = OutputClassV4.bdd),
      terminalWeight o = wtLow o + wtPaid o
  low_le :
    (∑ o ∈ objects.filter (fun o => o.cls = OutputClassV4.bdd), wtLow o) <=
      remLow
  output_budget : embedding.mainPaid + (remLow + embedding.remPaid) <= O_bdd

/-- Low/paid split with the L.6.2 paid part still in finite-overlap form.

This is closer to proof_v4 Lemma L.6.2: the paid terminal outputs are routed to
the stopped shell-paid family with bounded overlap, and only then collapsed to
the aggregate embedding used by `LowPaidSplitData`. -/
structure FiniteOverlapLowPaidSplitData
    {cStar xi X : Real}
    (leaf : RegularShellPaidChernoff22_1AInputData cStar xi X)
    (objects : Finset OutputObjectV4)
    (terminalWeight : OutputObjectV4 -> Real)
    (O_bdd : Real) where
  wtLow : OutputObjectV4 -> Real
  wtPaid : OutputObjectV4 -> Real
  remLow : Real
  embedding : ShellPaidTerminalFiniteOverlapEmbeddingData leaf
  paid_eq :
    embedding.paidMass =
      (∑ o ∈ objects.filter (fun o => o.cls = OutputClassV4.bdd), wtPaid o)
  split :
    ∀ o ∈ objects.filter (fun o => o.cls = OutputClassV4.bdd),
      terminalWeight o = wtLow o + wtPaid o
  low_le :
    (∑ o ∈ objects.filter (fun o => o.cls = OutputClassV4.bdd), wtLow o) <=
      remLow
  output_budget : embedding.mainPaid + (remLow + embedding.remPaid) <= O_bdd

namespace LowPaidSplitData

/-- Convert the literal N.3.2 low/paid split data to the compact L.6-backed
bounded-class certificate used by the terminal absorption package. -/
def toShellPaidBddClassBoundData
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {objects : Finset OutputObjectV4}
    {terminalWeight : OutputObjectV4 -> Real}
    {O_bdd : Real}
    (data : LowPaidSplitData leaf objects terminalWeight O_bdd) :
    ShellPaidBddClassBoundData leaf
      (AppendixN.classMassV4 objects terminalWeight OutputClassV4.bdd)
      O_bdd where
  lowMass :=
    ∑ o ∈ objects.filter (fun o => o.cls = OutputClassV4.bdd), data.wtLow o
  remLow := data.remLow
  embedding := data.embedding
  split := by
    unfold AppendixN.classMassV4
    let bddObjects : Finset OutputObjectV4 :=
      objects.filter (fun obj => obj.cls = OutputClassV4.bdd)
    have hPaid :
        data.embedding.paidMass = Finset.sum bddObjects data.wtPaid := by
      simpa [bddObjects] using data.paid_eq
    have hSplit :
        Finset.sum bddObjects terminalWeight =
          Finset.sum bddObjects (fun obj => data.wtLow obj + data.wtPaid obj) := by
      apply Finset.sum_congr rfl
      intro obj hobj
      exact data.split obj (by simpa [bddObjects] using hobj)
    change
      Finset.sum bddObjects terminalWeight =
        Finset.sum bddObjects data.wtLow + data.embedding.paidMass
    calc
      Finset.sum bddObjects terminalWeight =
          Finset.sum bddObjects (fun obj => data.wtLow obj + data.wtPaid obj) := hSplit
      _ = Finset.sum bddObjects data.wtLow +
          Finset.sum bddObjects data.wtPaid := by
        rw [Finset.sum_add_distrib]
      _ = Finset.sum bddObjects data.wtLow + data.embedding.paidMass := by
        rw [← hPaid]
  low_le := data.low_le
  output_budget := data.output_budget

end LowPaidSplitData

namespace FiniteOverlapLowPaidSplitData

/-- Collapse the finite-overlap L.6.2 paid routing to the standard low/paid
split consumed by the existing N.3.3 bounded-class constructors. -/
def toLowPaidSplitData
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {objects : Finset OutputObjectV4}
    {terminalWeight : OutputObjectV4 -> Real}
    {O_bdd : Real}
    (data : FiniteOverlapLowPaidSplitData leaf objects terminalWeight O_bdd) :
    LowPaidSplitData leaf objects terminalWeight O_bdd where
  wtLow := data.wtLow
  wtPaid := data.wtPaid
  remLow := data.remLow
  embedding := data.embedding.toShellPaidTerminalEmbeddingData
  paid_eq := data.paid_eq
  split := data.split
  low_le := data.low_le
  output_budget := data.output_budget

/-- Convert finite-overlap low/paid data directly to the compact L.6-backed
bounded-class certificate. -/
def toShellPaidBddClassBoundData
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {objects : Finset OutputObjectV4}
    {terminalWeight : OutputObjectV4 -> Real}
    {O_bdd : Real}
    (data : FiniteOverlapLowPaidSplitData leaf objects terminalWeight O_bdd) :
    ShellPaidBddClassBoundData leaf
      (AppendixN.classMassV4 objects terminalWeight OutputClassV4.bdd)
      O_bdd :=
  data.toLowPaidSplitData.toShellPaidBddClassBoundData

end FiniteOverlapLowPaidSplitData

/-- Public constructor for the proof-v4 N.3.2/L.6 bounded-class route from the
literal low/paid split on the bounded output slice. -/
def fromLowPaidSplit
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {objects : Finset OutputObjectV4}
    {terminalWeight : OutputObjectV4 -> Real}
    {O_bdd : Real}
    (data : LowPaidSplitData leaf objects terminalWeight O_bdd) :
    ShellPaidBddClassBoundData leaf
      (AppendixN.classMassV4 objects terminalWeight OutputClassV4.bdd)
      O_bdd :=
  data.toShellPaidBddClassBoundData

/-- Public constructor for the proof-v4 N.3.2/L.6 bounded-class route when the
paid part is supplied in the finite-overlap form of Lemma L.6.2. -/
def fromFiniteOverlapLowPaidSplit
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {objects : Finset OutputObjectV4}
    {terminalWeight : OutputObjectV4 -> Real}
    {O_bdd : Real}
    (data :
      FiniteOverlapLowPaidSplitData leaf objects terminalWeight O_bdd) :
    ShellPaidBddClassBoundData leaf
      (AppendixN.classMassV4 objects terminalWeight OutputClassV4.bdd)
      O_bdd :=
  data.toShellPaidBddClassBoundData

/-- N.3.2 bounded-class output bound after L.6.1, L.6.2, and L.6.3 are combined. -/
theorem bddMass_le_output
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {bddMass O_bdd : Real}
    (data : ShellPaidBddClassBoundData leaf bddMass O_bdd) :
    bddMass <= O_bdd := by
  have hcorr :
      bddMass <= data.embedding.mainPaid + (data.remLow + data.embedding.remPaid) :=
    lemmaL6_correctedResidualWeights
      (data.embedding.toCorrectedResidualWeights
        bddMass data.lowMass data.remLow data.split data.low_le)
  exact hcorr.trans data.output_budget

namespace LowPaidSplitData

/-- The manuscript-shaped low/paid split proves the bounded terminal class
estimate used in N.3.3. -/
theorem bddMass_le_output
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {objects : Finset OutputObjectV4}
    {terminalWeight : OutputObjectV4 -> Real}
    {O_bdd : Real}
    (data : LowPaidSplitData leaf objects terminalWeight O_bdd) :
    AppendixN.classMassV4 objects terminalWeight OutputClassV4.bdd <= O_bdd :=
  ShellPaidBddClassBoundData.bddMass_le_output
    data.toShellPaidBddClassBoundData

end LowPaidSplitData

/-- Turn the L.6-corrected bounded-class bridge into the table-routed N.3.3
bounded-dirty-return class input. -/
def toTableRoutedBddClassInputData
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    {E : AppendixN.EventFibre sigma iota}
    {row : iota -> AppendixN.TerminalRow}
    {supp thr : iota -> Nat}
    {terminalWeight : OutputObjectV4 -> Real}
    {O_bdd : Real}
    (data :
      ShellPaidBddClassBoundData leaf
        (AppendixN.classMassV4
          (E.atoms.image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega }))
          terminalWeight OutputClassV4.bdd)
        O_bdd) :
    TableRoutedBddClassInputData E row supp thr terminalWeight O_bdd where
  hBdd := data.bddMass_le_output

end ShellPaidBddClassBoundData

/--
Table-routed N.3.3 terminal package whose bounded-dirty-return class is backed
by the L.6.1/L.6.2/L.6.3 corrected-residual bridge.

The other four class bounds keep the standard table-routed inputs.  The `bdd`
class is intentionally stronger than a raw `hBdd`: it must be produced from a
low-residual estimate plus a shell-paid embedding into the same Lemma 22.1A
leaf.
-/
structure ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
    {cStar xi X : Real}
    (leaf : RegularShellPaidChernoff22_1AInputData cStar xi X)
    (termMass O_D O_P O_E O_CNL O_bdd : Real) where
  sigma : Type
  iota : Type
  linIota : LinearOrder iota
  E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) linIota
  row : iota -> AppendixN.TerminalRow
  supp : iota -> Nat
  thr : iota -> Nat
  terminalWeight : OutputObjectV4 -> Real
  terminalMass :
    @TableRoutedTerminalMassInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight termMass
  densePack :
    @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight O_D
  progress :
    @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight O_P
  endpoint :
    @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight O_E
  cnl :
    @TableRoutedCNLClassInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight O_CNL
  bddL6 :
    ShellPaidBddClassBoundData leaf
      (AppendixN.classMassV4
        ((@AppendixN.EventFibre.atoms sigma iota
            (Classical.decEq sigma) linIota E).image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalWeight OutputClassV4.bdd)
      O_bdd

namespace ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data

/-- Strengthen an ordinary table-routed N.3.3 package by replacing only the
bounded-dirty-return class with an L.6-backed proof.

The dense-pack, progress, endpoint, clean-CNL, and terminal-mass estimates are
reused from the already-built table-routed package.  The new input is exactly
the additional proof-v4 L.6.1/L.6.2/L.6.3 certificate for the bounded class,
backed by the same shell-paid Chernoff leaf. -/
def ofClassicalTableRoutedDirectAndBddL6
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
        termMass O_D O_P O_E O_CNL O_bdd)
    (bddL6 :
      ShellPaidBddClassBoundData leaf
        (AppendixN.classMassV4
          ((@AppendixN.EventFibre.atoms data.sigma data.iota
              (Classical.decEq data.sigma) data.linIota data.E).image
            (fun omega =>
              { cls := (data.row omega).outputClass
                supportId := data.supp omega
                thresholdLayer := data.thr omega }))
          data.terminalWeight OutputClassV4.bdd)
        O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
      leaf termMass O_D O_P O_E O_CNL O_bdd := by
  letI : DecidableEq data.sigma := Classical.decEq data.sigma
  letI : LinearOrder data.iota := data.linIota
  exact {
    sigma := data.sigma
    iota := data.iota
    linIota := data.linIota
    E := data.E
    row := data.row
    supp := data.supp
    thr := data.thr
    terminalWeight := data.terminalWeight
    terminalMass := data.terminalMass
    densePack := (data.classBounds).densePack
    progress := (data.classBounds).progress
    endpoint := (data.classBounds).endpoint
    cnl := (data.classBounds).cnl
    bddL6 := bddL6 }

/-- Forget only the proof-v4 L.6 explanation of the bounded class, recovering
the direct table-routed N.3.3 terminal package. -/
def toClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
        leaf termMass O_D O_P O_E O_CNL O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
      termMass O_D O_P O_E O_CNL O_bdd := by
  letI : DecidableEq data.sigma := Classical.decEq data.sigma
  letI : LinearOrder data.iota := data.linIota
  exact {
    sigma := data.sigma
    iota := data.iota
    linIota := data.linIota
    E := data.E
    row := data.row
    supp := data.supp
    thr := data.thr
    terminalWeight := data.terminalWeight
    bounds_input := {
      hterm := data.terminalMass.hterm
      hD := data.densePack.hD
      hP := data.progress.hP
      hE := data.endpoint.hE
      hCNL := data.cnl.hCNL
      hBdd := data.bddL6.bddMass_le_output } }

/-- The L.6-backed terminal package still pays terminal mass into the five
non-drop classes. -/
theorem termMass_le_classes
    {cStar xi X : Real}
    {leaf : RegularShellPaidChernoff22_1AInputData cStar xi X}
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
        leaf termMass O_D O_P O_E O_CNL O_bdd) :
    termMass <= O_D + O_P + O_E + O_CNL + O_bdd :=
  data.toClassicalTableRoutedDirectFiveClassTerminalAbsorptionData.termMass_le_classes

end ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data

end

end Erdos260
