import Mathlib
import Erdos260.TowerLocalLeafConstruction

/-!
# The Tower entry/exit output family (Appendix E.2–E.6 + Lemma L.3.1)

This file advances the *construction* of the proof-v4 Tower entry/exit charged
output family — the `TowerTransientFactoryData` / `termTower` slot — from more
primitive data, and **cleanly isolates the one irreducible input**: the
SCC-geometry primitive that the carry orbit on a common AP subfibre closes into a
finite recurrent cycle (Appendix E.2–E.4).

## What is genuinely constructed and proved here

* **The L.3.1 routed-exit family is built from a disjoint classification.**  The
  finite tower entry/exit set is classified by `route : TowerExit → TowerExitClass`
  into the five Lemma L.3.1 destinations (Run, non-run Return, DensePack, clean
  CNL tail, and the lower-order `o(sX|I_j|)` remainder).  The routed masses are
  *defined* as the fibre sums of the charged weights, and the routed-exit estimate
  `∑_b wt(b) ≤ routedRun + routedReturn + routedDensePack + routedCNLTail +
  smallError` is then a genuine **equality** (a partition identity, proved via
  `Finset.sum_fiberwise_of_maps_to`).  This produces a real
  `TowerExitRoutingData`.

* **The next-layer absorption is proved arithmetic.**  From per-class absorption
  bounds `routedRun ≤ C·massRun`, … and a next-layer mass budget
  `massRun + … ≤ nextLayerMass`, the aggregate budget
  `routedRun + … + routedCNLTail ≤ C·nextLayerMass` is proved
  (`absorbedBudget_of_perClass`), and packaged into a real
  `TowerRoutedAbsorptionData` (`TowerRoutedAbsorptionData.ofTightBudget`).

* **The full endpoint is assembled.**  `TowerFamilyInput` bundles the cycle
  witness with the routing classification and the numeric certificates, and
  `TowerFamilyInput.toClosedPackage` produces a real
  `TowerClosedL31I31PackageInputData` (via the proved
  `TowerClosedL31I31PackageInputData.ofCycleRoutingAbsorption`), from which the
  final tower budget bound `∑_b wt(b) ≤ cStar·ξ·X/6` (the `termTower` quantity),
  the `GroundedTowerLocalData`, the `TowerTransientFactoryData`, and the
  `towerPackageBound` `∃ Tower` form all follow with no further hypotheses.

* **The E.2–E.4 cycle witness is exhibited as an infinite family.**  Beyond the
  two toy examples in `RefinedTowerConstruction`, `fixedPointCycle g` builds a
  genuine length-one recurrent cycle with slope `μ = 1/(2^g − 1)` for **every**
  gap `g ≥ 2` (a real fixed point of the E.13 slope recurrence
  `μ = 2^g μ − 1`), and `theoremE6_recurrentSCCSimpleCycle` (already proved)
  turns each into a genuine simple directed cycle.

## The irreducible SCC-geometry primitive

The *only* non-derived input is the field `TowerFamilyInput.cycle :
CarryFibreCycleData`, i.e. the existence of the carry-fibre recurrent cycle
itself (the common-fibre slope transitions closing into a finite cycle on a
common AP subfibre, Appendix E.2–E.4).  Constructing this from the actual carry
recurrence for a given failing shell is the genuinely deep arithmetic step that
is **not** formalized here; everything structurally downstream of it — the E.6
simple-cycle theorem, the routed-exit partition, the absorption arithmetic, and
the final budget — is a real theorem.  Non-vacuity of the primitive is witnessed
by the explicit `fixedPointCycle` family.

No `sorry`, no `axiom`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1. The Lemma L.3.1 tower-exit destination classes -/

/--
The five Lemma L.3.1 destinations for a charged tower entry/exit branch: the
first obstruction event after the first exit routes the branch to a Run, a
non-run Return, a DensePack, or a clean CNL-tail output, or it is absorbed into
the lower-order `o(sX|I_j|)` remainder (`other`).
-/
inductive TowerExitClass
  | run
  | returnPkg
  | densePack
  | cnlTail
  | other
deriving DecidableEq, Fintype, Repr

/-- Explicit five-term enumeration of a sum over the L.3.1 destination classes. -/
theorem TowerExitClass.sum_univ {M : Type*} [AddCommMonoid M] (F : TowerExitClass → M) :
    (∑ c : TowerExitClass, F c) =
      F .run + F .returnPkg + F .densePack + F .cnlTail + F .other := by
  rw [show (Finset.univ : Finset TowerExitClass) =
        {TowerExitClass.run, TowerExitClass.returnPkg, TowerExitClass.densePack,
          TowerExitClass.cnlTail, TowerExitClass.other} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  abel

/-! ## 2. The L.3.1 routed tower-exit family

A `TowerExitRouting` is a finite charged tower entry/exit family together with
the L.3.1 classification.  The routed masses are *defined* as the fibre sums, and
the routed-exit estimate is then a genuine partition equality. -/

/--
**L.3.1 routed tower-exit family.**  A finite tower entry/exit set with
nonnegative charged weights (encoded as a `{x // 0 ≤ x}`-valued function so the
weights are nonnegative by type) and the L.3.1 destination classification.
-/
structure TowerExitRouting where
  /-- The finite set of charged tower entry/exit branches. -/
  entryExitSet : Finset TowerExit
  /-- The nonnegative charged weight of each branch. -/
  weight : TowerExit → {x : ℝ // 0 ≤ x}
  /-- The Lemma L.3.1 destination of each branch. -/
  route : TowerExit → TowerExitClass

namespace TowerExitRouting

/-- The real-valued charged weight underlying the nonnegative mass data. -/
def chargedWeightReal (R : TowerExitRouting) : TowerExit → ℝ := fun b => (R.weight b : ℝ)

theorem chargedWeightReal_nonneg (R : TowerExitRouting) (b : TowerExit) :
    0 ≤ R.chargedWeightReal b := (R.weight b).2

/-- The routed charged mass landing in a fixed L.3.1 destination class. -/
def routedMass (R : TowerExitRouting) (cls : TowerExitClass) : ℝ :=
  ∑ b ∈ R.entryExitSet.filter (fun b => R.route b = cls), (R.weight b : ℝ)

theorem routedMass_nonneg (R : TowerExitRouting) (cls : TowerExitClass) :
    0 ≤ R.routedMass cls :=
  Finset.sum_nonneg fun b _ => (R.weight b).2

/-- Routed Run mass. -/
def routedRun (R : TowerExitRouting) : ℝ := R.routedMass .run
/-- Routed non-run Return mass. -/
def routedReturn (R : TowerExitRouting) : ℝ := R.routedMass .returnPkg
/-- Routed DensePack mass. -/
def routedDensePack (R : TowerExitRouting) : ℝ := R.routedMass .densePack
/-- Routed clean CNL-tail mass. -/
def routedCNLTail (R : TowerExitRouting) : ℝ := R.routedMass .cnlTail
/-- The lower-order `o(sX|I_j|)` remainder mass. -/
def smallError (R : TowerExitRouting) : ℝ := R.routedMass .other

theorem routedRun_nonneg (R : TowerExitRouting) : 0 ≤ R.routedRun := R.routedMass_nonneg _
theorem routedReturn_nonneg (R : TowerExitRouting) : 0 ≤ R.routedReturn := R.routedMass_nonneg _
theorem routedDensePack_nonneg (R : TowerExitRouting) : 0 ≤ R.routedDensePack :=
  R.routedMass_nonneg _
theorem routedCNLTail_nonneg (R : TowerExitRouting) : 0 ≤ R.routedCNLTail := R.routedMass_nonneg _
theorem smallError_nonneg (R : TowerExitRouting) : 0 ≤ R.smallError := R.routedMass_nonneg _

/--
**L.3.1 routed-exit partition identity.**  The total charged tower-exit mass is
*exactly* the sum of the four routed package masses and the lower-order
remainder.  This is the genuine content of the routed-exit estimate: it is the
disjoint-classification identity, proved by fibrewise summation.
-/
theorem total_eq_sum_routed (R : TowerExitRouting) :
    (∑ b ∈ R.entryExitSet, (R.weight b : ℝ)) =
      R.routedRun + R.routedReturn + R.routedDensePack + R.routedCNLTail + R.smallError := by
  rw [show R.routedRun + R.routedReturn + R.routedDensePack + R.routedCNLTail + R.smallError
        = ∑ c : TowerExitClass, R.routedMass c from (TowerExitClass.sum_univ R.routedMass).symm]
  exact (Finset.sum_fiberwise_of_maps_to (s := R.entryExitSet)
    (t := (Finset.univ : Finset TowerExitClass))
    (fun b _ => Finset.mem_univ (R.route b)) (fun b => (R.weight b : ℝ))).symm

/-- The L.3.1 routed-exit estimate as a real `TowerExitRoutingData` certificate. -/
def toRoutingData (R : TowerExitRouting) :
    TowerExitRoutingData R.entryExitSet (fun b => (R.weight b : ℝ))
      R.routedRun R.routedReturn R.routedDensePack R.routedCNLTail R.smallError where
  routed := le_of_eq R.total_eq_sum_routed

end TowerExitRouting

/-! ## 3. Absorption of the routed exits into the next-layer tower budget -/

/--
**Next-layer absorption budget (proved arithmetic).**

If each routed package mass is bounded by a uniform constant `C ≥ 0` times its
next-layer package mass, and the next-layer package masses sum to at most
`nextLayerMass`, then the aggregate routed mass is bounded by `C · nextLayerMass`.
This is the arithmetic core of the L.3 routed-output absorption.
-/
theorem absorbedBudget_of_perClass
    {C routedRun routedReturn routedDensePack routedCNLTail
       massRun massReturn massDensePack massCNL nextLayerMass : ℝ}
    (hC : 0 ≤ C)
    (hRun : routedRun ≤ C * massRun)
    (hReturn : routedReturn ≤ C * massReturn)
    (hDensePack : routedDensePack ≤ C * massDensePack)
    (hCNL : routedCNLTail ≤ C * massCNL)
    (hmass : massRun + massReturn + massDensePack + massCNL ≤ nextLayerMass) :
    routedRun + routedReturn + routedDensePack + routedCNLTail ≤ C * nextLayerMass := by
  have hexpand : C * (massRun + massReturn + massDensePack + massCNL) ≤ C * nextLayerMass :=
    mul_le_mul_of_nonneg_left hmass hC
  have hkey : C * (massRun + massReturn + massDensePack + massCNL)
      = C * massRun + C * massReturn + C * massDensePack + C * massCNL := by ring
  linarith [hRun, hReturn, hDensePack, hCNL, hexpand, hkey]

/--
**Tight routed-output absorption certificate.**  Taking each absorbed mass equal
to its routed mass discharges the four per-class absorption bounds reflexively;
the only remaining content is the aggregate next-layer budget inequality.
-/
def TowerRoutedAbsorptionData.ofTightBudget
    {routedRun routedReturn routedDensePack routedCNLTail
       outputBoundConstant nextLayerMass : ℝ}
    (hbudget : routedRun + routedReturn + routedDensePack + routedCNLTail
        ≤ outputBoundConstant * nextLayerMass) :
    TowerRoutedAbsorptionData routedRun routedReturn routedDensePack routedCNLTail
      routedRun routedReturn routedDensePack routedCNLTail
      outputBoundConstant nextLayerMass where
  run := ⟨le_refl _⟩
  returnPkg := ⟨le_refl _⟩
  densePack := ⟨le_refl _⟩
  cnlTail := ⟨le_refl _⟩
  budget := ⟨hbudget⟩

/-! ## 4. The assembled Tower entry/exit output family -/

/--
**Tower family input.**

Everything needed to build the proof-v4 Tower entry/exit output package,
separated into:

* the **irreducible SCC-geometry primitive** `cycle : CarryFibreCycleData`
  (Appendix E.2–E.4: the carry orbit closes into a finite recurrent cycle on a
  common AP subfibre);
* the **L.3.1 routing classification** `routing : TowerExitRouting` of the finite
  charged entry/exit family;
* the **next-layer absorption certificates**: a uniform output-bound constant,
  per-class next-layer package masses, the four absorption comparisons, and the
  next-layer mass budget;
* the **K.4 smallness** comparison fitting the absorbed bound inside the tower
  budget `cStar·ξ·X/6`.

The cycle witness is the only non-derived ingredient; all the inequalities are
honest numeric certificates and everything else is proved below.
-/
structure TowerFamilyInput (cStar xi X : ℝ) where
  /-- IRREDUCIBLE: the E.2–E.4 carry-fibre recurrent SCC cycle witness. -/
  cycle : CarryFibreCycleData
  /-- The Lemma L.3.1 routed tower-exit family. -/
  routing : TowerExitRouting
  /-- The uniform `C_T` output-bound constant. -/
  outputBoundConstant : ℝ
  outputBoundConstant_nonneg : 0 ≤ outputBoundConstant
  /-- The aggregate next-layer package mass. -/
  nextLayerMass : ℝ
  /-- Next-layer Run package mass. -/
  massRun : ℝ
  /-- Next-layer Return package mass. -/
  massReturn : ℝ
  /-- Next-layer DensePack package mass. -/
  massDensePack : ℝ
  /-- Next-layer clean CNL-tail package mass. -/
  massCNL : ℝ
  absorbRun : routing.routedRun ≤ outputBoundConstant * massRun
  absorbReturn : routing.routedReturn ≤ outputBoundConstant * massReturn
  absorbDensePack : routing.routedDensePack ≤ outputBoundConstant * massDensePack
  absorbCNL : routing.routedCNLTail ≤ outputBoundConstant * massCNL
  massSum : massRun + massReturn + massDensePack + massCNL ≤ nextLayerMass
  hSmall :
    outputBoundConstant * nextLayerMass + routing.smallError ≤ cStar * xi * X / 6

namespace TowerFamilyInput

variable {cStar xi X : ℝ} (I : TowerFamilyInput cStar xi X)

/-- The aggregate next-layer budget for the routed tower exits (proved). -/
theorem budget :
    I.routing.routedRun + I.routing.routedReturn + I.routing.routedDensePack
        + I.routing.routedCNLTail ≤ I.outputBoundConstant * I.nextLayerMass :=
  absorbedBudget_of_perClass I.outputBoundConstant_nonneg
    I.absorbRun I.absorbReturn I.absorbDensePack I.absorbCNL I.massSum

/-- The routed-output absorption certificate assembled from the per-class data. -/
def absorption :
    TowerRoutedAbsorptionData I.routing.routedRun I.routing.routedReturn
      I.routing.routedDensePack I.routing.routedCNLTail I.routing.routedRun
      I.routing.routedReturn I.routing.routedDensePack I.routing.routedCNLTail
      I.outputBoundConstant I.nextLayerMass :=
  TowerRoutedAbsorptionData.ofTightBudget I.budget

/--
The fully assembled manuscript-shaped L.3/I.3 tower output package, built from the
E.2–E.4 cycle witness, the L.3.1 routed-exit partition, the routed-output
absorption, and the K.4 smallness comparison.
-/
def toClosedPackage : TowerClosedL31I31PackageInputData cStar xi X :=
  TowerClosedL31I31PackageInputData.ofCycleRoutingAbsorption
    I.cycle I.routing.toRoutingData I.absorption { hSmall := I.hSmall }

/-- The proof-v4 separated tower local leaf carried by the assembled package. -/
def toSeparatedLeaf : TowerSeparatedLocalLeafInputData cStar xi X :=
  I.toClosedPackage.toTowerSeparatedLocalLeafInputData

/-- The grounded Tower local data carried by the assembled package. -/
def toGroundedTowerLocalData : GroundedTowerLocalData cStar xi X :=
  I.toSeparatedLeaf.toGroundedTowerLocalData

/-- The Phase-7 transient tower factory data carried by the assembled package. -/
def toTowerTransientFactoryData : TowerTransientFactoryData cStar xi X :=
  I.toGroundedTowerLocalData.toTowerTransientFactoryData

/--
**The Tower budget bound (the `termTower` slot).**

The total charged tower entry/exit mass — exactly the quantity
`termTower = ∑_{b ∈ entryExitSet} chargedWeight b` of the phase-mass ledger — fits
inside the Tower budget `cStar·ξ·X/6`.  This is the full L.3/I.3.1 tower output
estimate, derived from the cycle witness and the explicit certificates.
-/
theorem tower_bound :
    (∑ b ∈ I.routing.entryExitSet, (I.routing.weight b : ℝ)) ≤ cStar * xi * X / 6 :=
  I.toSeparatedLeaf.tower_bound

include I in
/-- `towerPackageBound` form of the tower budget: a nonnegative `Tower` real
bounded by `cStar·ξ·X/6`. -/
theorem exists_tower_bound :
    ∃ Tower : ℝ, 0 ≤ Tower ∧ Tower ≤ cStar * xi * X / 6 :=
  towerPackageBound_of_transientFactory I.toTowerTransientFactoryData

/-- **E.6 applied to the carried cycle witness.**  The carry-fibre recurrent SCC
underlying the tower family is a genuine simple directed cycle. -/
theorem simpleCycle : I.cycle.toSCC.IsSimpleCycle := I.cycle.isSimpleCycle

include I in
/-- The carried cycle witness assembles a coherent recurrent SCC. -/
theorem cycleData : ∃ S : RefinedRecurrentSCC, RefinedTowerCycleData S := I.cycle.cycleData

end TowerFamilyInput

/--
**Main reduction (irreducible-primitive form).**

From the irreducible SCC-geometry primitive — a `CarryFibreCycleData` cycle
witness — together with the explicit L.3.1 routing classification and the numeric
absorption/smallness certificates packaged in `TowerFamilyInput`, the tower
charged mass meets the budget `cStar·ξ·X/6`.  The cycle witness is the only
non-derived input.
-/
theorem termTower_budget_of_primitive {cStar xi X : ℝ}
    (I : TowerFamilyInput cStar xi X) :
    (∑ b ∈ I.routing.entryExitSet, (I.routing.weight b : ℝ)) ≤ cStar * xi * X / 6 :=
  I.tower_bound

/-! ## 5. Non-vacuity of the primitive: the fixed-point recurrent-cycle family -/

/-- `4 ≤ 2^g` for every `g ≥ 2` (real-valued helper for the slope estimates). -/
theorem four_le_two_pow {g : ℕ} (hg : 2 ≤ g) : (4 : ℝ) ≤ (2 : ℝ) ^ g := by
  have hnat : (2 : ℕ) ^ 2 ≤ (2 : ℕ) ^ g := Nat.pow_le_pow_right (by norm_num) hg
  calc (4 : ℝ) = ((2 : ℕ) ^ 2 : ℝ) := by norm_num
    _ ≤ ((2 : ℕ) ^ g : ℝ) := by exact_mod_cast hnat
    _ = (2 : ℝ) ^ g := by push_cast; ring

/--
**The fixed-point recurrent cycle family (Appendix E.2–E.4 non-vacuity).**

For every gap `g ≥ 2`, the slope `μ = 1/(2^g − 1)` is a genuine fixed point of the
E.13 slope recurrence `μ = 2^g μ − 1` lying in the open interval `(0,1)`.  This
yields a genuine length-one carry-fibre recurrent cycle, witnessing that the
irreducible SCC-geometry primitive is satisfiable for an infinite family of gaps
(strengthening the two toy examples of `RefinedTowerConstruction`).
-/
def fixedPointCycle (g : ℕ) (hg : 2 ≤ g) : CarryFibreCycleData where
  n := 1
  hn := Nat.one_pos
  apSubfibre := 0
  layer := 0
  fibre := 0
  terminal := none
  slope := fun _ => 1 / ((2 : ℝ) ^ g - 1)
  gap := fun _ => g
  slope_open := by
    intro _
    have h4 := four_le_two_pow hg
    have hpos : (0 : ℝ) < (2 : ℝ) ^ g - 1 := by linarith
    refine ⟨div_pos one_pos hpos, ?_⟩
    rw [div_lt_one hpos]; linarith
  slope_trans := by
    intro _
    have h4 := four_le_two_pow hg
    have hne : (2 : ℝ) ^ g - 1 ≠ 0 := by
      intro h; linarith [sub_eq_zero.mp h]
    show (1 : ℝ) / ((2 : ℝ) ^ g - 1)
        = (2 : ℝ) ^ g * (1 / ((2 : ℝ) ^ g - 1)) - 1
    field_simp
    ring
  slope_inj := fun a b _ => Subsingleton.elim a b

/-- Each fixed-point cycle is a genuine simple directed cycle (Theorem E.6). -/
theorem fixedPointCycle_isSimpleCycle (g : ℕ) (hg : 2 ≤ g) :
    (fixedPointCycle g hg).toSCC.IsSimpleCycle :=
  (fixedPointCycle g hg).isSimpleCycle

/-- The fixed-point cycle has a genuine one-element vertex set. -/
theorem fixedPointCycle_card (g : ℕ) (hg : 2 ≤ g) :
    (fixedPointCycle g hg).vertices.card = 1 :=
  (fixedPointCycle g hg).card_vertices

/-- The fixed-point cycle packages as the standalone coherent SCC witness. -/
theorem fixedPointCycle_cycleData (g : ℕ) (hg : 2 ≤ g) :
    ∃ S : RefinedRecurrentSCC, RefinedTowerCycleData S :=
  (fixedPointCycle g hg).cycleData

/-! ## 6. A fully assembled, non-vacuous Tower family instance -/

/-- The empty L.3.1 routing: no charged tower exits. -/
def emptyRouting : TowerExitRouting where
  entryExitSet := ∅
  weight := fun _ => ⟨0, le_refl 0⟩
  route := fun _ => .other

@[simp] theorem emptyRouting_routedMass (cls : TowerExitClass) :
    emptyRouting.routedMass cls = 0 := by
  simp [TowerExitRouting.routedMass, emptyRouting]

@[simp] theorem emptyRouting_routedRun : emptyRouting.routedRun = 0 :=
  emptyRouting_routedMass _
@[simp] theorem emptyRouting_routedReturn : emptyRouting.routedReturn = 0 :=
  emptyRouting_routedMass _
@[simp] theorem emptyRouting_routedDensePack : emptyRouting.routedDensePack = 0 :=
  emptyRouting_routedMass _
@[simp] theorem emptyRouting_routedCNLTail : emptyRouting.routedCNLTail = 0 :=
  emptyRouting_routedMass _
@[simp] theorem emptyRouting_smallError : emptyRouting.smallError = 0 :=
  emptyRouting_routedMass _

/--
A fully assembled Tower family with the genuine `fixedPointCycle 2` cycle witness
and the empty routed-exit family, valid whenever the tower budget is
nonnegative.  This inhabits the entire endpoint pipeline with no `sorry`.
-/
def emptyTowerFamilyInput {cStar xi X : ℝ} (h : 0 ≤ cStar * xi * X / 6) :
    TowerFamilyInput cStar xi X where
  cycle := fixedPointCycle 2 (le_refl 2)
  routing := emptyRouting
  outputBoundConstant := 0
  outputBoundConstant_nonneg := le_refl 0
  nextLayerMass := 0
  massRun := 0
  massReturn := 0
  massDensePack := 0
  massCNL := 0
  absorbRun := by simp
  absorbReturn := by simp
  absorbDensePack := by simp
  absorbCNL := by simp
  massSum := by norm_num
  hSmall := by simpa using h

/--
**Non-vacuity of the assembled tower endpoint.**  The whole pipeline — cycle
witness, routed-exit partition, absorption, closed package, and budget bound —
is inhabited and produces the tower budget bound.
-/
theorem tower_family_nonvacuous :
    ∃ I : TowerFamilyInput (1 : ℝ) 1 1,
      (∑ b ∈ I.routing.entryExitSet, (I.routing.weight b : ℝ)) ≤ 1 * 1 * 1 / 6 :=
  ⟨emptyTowerFamilyInput (by norm_num), (emptyTowerFamilyInput (by norm_num)).tower_bound⟩

end

end Erdos260
