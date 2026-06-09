import Erdos260.Erdos260UnconditionalSeedClosureV3
import Erdos260.Chernoff221AAreaClosureCore
import Erdos260.Chernoff221ASeedClosure

/-!
# Erdős #260 — the class-0 Chernoff ledger leaf, advanced to the genuine §22 Kraft area sum

This module (NEW; it edits no existing file) advances the four class-0 fields of
`Erdos260MinimalResidualV3` (`Erdos260UnconditionalSeedClosureV3.lean`)

```
chernoffChargeOf : ∀ ctx, ℕ → (faithfulCapacityPhases (v3Budget …) ctx).toClosurePhaseData.chernoff.α
chernoffMaps     : each routed class-0 start lands in highCostSet …       (22.1A shell-paid embedding)
chernoffInj      : distinct progress starts ↦ distinct §22 paths          (K.1.3 endpoint disjointness)
chernoffDom      : windowExcess(k) ≤ chernoff.weight (chargeOf k)          (matched per-path area charge)
```

which together discharge `routedClassMassOf … 0 ≤ termChernoff` via `hChernoffField_ofMatching`.

## The two halves

### (A) The four fields, reduced to the genuine matching residual (over the faithful family)

The four fields are typed against the **faithful four-path §22 model leaf**
`faithfulChern (v3Budget …) = (faithfulCapacityPhases (v3Budget …) ·).toClosurePhaseData.chernoff`,
whose high-cost set has cardinality exactly `4` (`class0_highCostFamily_card`).  Per
`Chernoff221AAreaClosureCore.lean` (`faithful_matching_iff_le_four`), any `chernoffMaps + chernoffInj`
into this family **forces** `|routedFibre … 0| ≤ 4` — the deep-shell-false fixed-family count
collapse — and, since each model weight is `2^{-cost} ≤ 1`, the matched domination `chernoffDom`
forces the uniform unit charge.  So the four fields, taken over the faithful family, **cannot** be
proved unconditionally; we reduce them, via the proved `Chernoff221AAreaMatchedCharge.ofCountDom`, to
the genuine matching residual: the I.4.2 progress count `hcard` and the J.1.7 per-path area
domination `hdom`.  The `_v3`-typed extractions (`chernoffChargeOf_field`, …) carry the **exact** V3
field types, so a coordinator drops them straight into `Erdos260MinimalResidualV3`.

### (B) The genuine §22 stopped-branch family, where the Kraft inequality does real work

The faithful model leaf bakes in the shell-independent area `termChernoff = chernoffModelArea ∈ [1,4]`.
The manuscript's genuine high-cost family is the actual I.9 carry stopped-branch family
`ctx.n24CarryData.stoppedBranches`, with the decaying integer-carry symbolic measure
`wt₀(b) = 2^{-branchShellCost b} = carryThresholdMeasure …` (`genuineCarryChern_weight_faithful`).  Over
THIS family the §22 area family-sum is **derived, not baked in**:

```
chernoffAreaFamilySum (genuineCarryChern ctx) = ∑_{b∈stoppedBranches} 2^{-cost(b)} ≤ 1
```

— and the sole analytic input is the §22 **antichain/Kraft measure-sum** `hKraft`
(`∑_b 2^{-cost(b)} ≤ 1`, proof_v4 line 818: the principal children of a stopped node are disjoint
subsets of `Ω_u`), exactly the explicit hypothesis of
`carryAlignedShellPaidChernoff22_1AOfShell`.  Feeding the genuine matched charge over this family
through `1 ≤ chernoffModelArea = termChernoff` reproduces the **exact** V3 ledger bound
`routedClassMassOf … 0 ≤ termChernoff` — via the genuine, shell-scaling progress count (`≤
|stoppedBranches|`, not the false `4`) and the Kraft area sum, never the four-path count collapse
(`chernoffClass0_hChernoffField_of_kraft`).

## What is fully proved vs reduced

* **PROVED** — the genuine §22 family `genuineCarryChern` (the manuscript `ChernoffPathData` whose
  moment budget IS the Kraft inequality and whose `Y = 0` so the high-cost set is the full family),
  and `chernoffAreaFamilySum_genuineCarryChern_le_one` (the area sum `≤ 1` from `hKraft` alone).  No
  count, no per-path charge enters this; Kraft does all the work.
* **REDUCED** — the four fields (and the ledger bound they establish) reduce to the genuine matching
  residual `(hcard, hdom)` together with the §22 antichain hypothesis `hKraft`.  `hKraft` is the
  sharpest named input (the disjointness of the stopped principal children), carried honestly because
  the formalized `carryThresholdMeasure` is the dyadic value `2^{-prefixGapSum}` with no disjointness
  datum attached.

No `sorry`, `axiom`, `admit`, or `native_decide`; the genuine §22 family is the real carry
stopped-branch family with the decaying integer-carry measure — never an empty/zero/degenerate
stand-in.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The §22 antichain/Kraft measure-sum over the actual stopped branches -/

/-- **The §22 antichain/Kraft measure-sum of a failure context.**  The total decaying integer-carry
symbolic mass `∑_{b∈stoppedBranches} 2^{-branchShellCost b}` of the actual I.9 carry stopped-branch
family.  This is the left-hand side of the manuscript Kraft inequality (proof_v4 line 818); it equals
`∑_b carryThresholdMeasure …` (`genuineCarryChern_weight_faithful`). -/
def chernoffClass0KraftSum (ctx : ActualFailureContext) : ℝ :=
  ∑ b ∈ ctx.n24CarryData.stoppedBranches, (1 / 2 : ℝ) ^ branchShellCost b

/-- **The genuine §22 stopped-branch Chernoff path family, built from the Kraft inequality.**

A real `ChernoffPathData` over the **actual** carry stopped-branch family
`ctx.n24CarryData.stoppedBranches`, with

* `weight b = 2^{-branchShellCost b}` — the genuine decaying integer-carry symbolic measure
  (`carryThresholdMeasure`, not a synthetic weight; `genuineCarryChern_weight_faithful`);
* `cost = branchShellCost`, `Y = 0` (so the high-cost subfamily is the full family);
* the trivial tilt `z = 1`, `m = 0`, `root = A = 1`.

The Chernoff **moment budget** `weightedMoment … 1 ≤ root·A^m = 1` is *exactly* the §22 antichain
Kraft inequality `hK`, and the **manuscript budget** `1 ≤ c⋆ξX/6` is the large-scale floor
(`manuscript_chernoff_budget_ge_one`, from the carry-threshold gate).  So the family is genuinely
inhabited from the single Kraft input. -/
def genuineCarryChern (ctx : ActualFailureContext) (hK : chernoffClass0KraftSum ctx ≤ 1) :
    ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) where
  α := StoppedBranch
  paths := ctx.n24CarryData.stoppedBranches
  weight := fun b => (1 / 2 : ℝ) ^ branchShellCost b
  cost := branchShellCost
  Y := 0
  m := 0
  z := 1
  root := 1
  A := 1
  weight_nonneg := fun b _ => by positivity
  z_ge_one := le_refl 1
  moment_bound := by
    rw [weightedMoment_one]
    have he : (1 : ℝ) * (1 : ℝ) ^ (0 : ℕ) = 1 := by norm_num
    rw [he]
    simpa [weightedMass, chernoffClass0KraftSum] using hK
  manuscript_bound := by
    have h64 : (64 : ℕ) ≤ ctx.shell.X := by
      have h26 : (2 : ℕ) ^ 26 ≤ ctx.shell.X :=
        aboveCarryThreshold_forces_scale
          (aboveCarryThreshold_of_manuscriptLargeThreshold_le ctx.shell ctx.shell_large)
      exact le_trans (by norm_num) h26
    have hb := manuscript_chernoff_budget_ge_one h64
    have he : (1 : ℝ) * (1 : ℝ) ^ (0 : ℕ) / (1 : ℝ) ^ (0 : ℕ) = 1 := by norm_num
    rw [he]
    exact hb

/-- **Faithfulness — the genuine family's weight is the integer-carry threshold measure.**  On a
genuine carry branch `stoppedBranchOf a r k`, the §22 family weight `2^{-cost}` is exactly the
manuscript integer-carry threshold-fibre measure `carryThresholdMeasure Q (carryGapWord …) (r+1)`
(`= |Ω_π|`), not a synthetic stand-in. -/
theorem genuineCarryChern_weight_faithful (ctx : ActualFailureContext)
    (hK : chernoffClass0KraftSum ctx ≤ 1) (k : ℕ) :
    (genuineCarryChern ctx hK).weight
        (stoppedBranchOf ctx.n24CarryData.a ctx.n24CarryData.r k)
      = carryThresholdMeasure ctx.shell.Q
          (carryGapWord ctx.n24CarryData.a k (ctx.n24CarryData.r + 1))
          (ctx.n24CarryData.r + 1) := by
  show (1 / 2 : ℝ) ^ branchShellCost (stoppedBranchOf ctx.n24CarryData.a ctx.n24CarryData.r k) = _
  rw [← carryShellSymbolicWeight_coe]
  exact carryShellSymbolicWeight_eq_carryThresholdMeasure _ _ _ _

/-- **The genuine §22 area family-sum IS the Kraft sum.**  Since `Y = 0`, the high-cost subfamily is
the full stopped-branch family, so `chernoffAreaFamilySum (genuineCarryChern ctx) =
∑_{b∈stoppedBranches} 2^{-cost(b)} = chernoffClass0KraftSum ctx`. -/
theorem chernoffAreaFamilySum_genuineCarryChern_eq (ctx : ActualFailureContext)
    (hK : chernoffClass0KraftSum ctx ≤ 1) :
    chernoffAreaFamilySum (genuineCarryChern ctx hK) = chernoffClass0KraftSum ctx := by
  have hself :
      highCostSet (genuineCarryChern ctx hK).paths (genuineCarryChern ctx hK).cost
          (genuineCarryChern ctx hK).Y
        = (genuineCarryChern ctx hK).paths :=
    highCostSet_eq_self_of_forall_ge (fun p _ => Nat.zero_le _)
  unfold chernoffAreaFamilySum
  rw [hself]
  rfl

/-- **The genuine §22 area family-sum is `≤ 1` — proved from the Kraft inequality alone.**  This is
where the manuscript antichain/Kraft measure-sum (proof_v4 line 818) does the real work: the area
sum of the matched J.1.7 charge over the actual stopped branches is dominated by `1`, a genuine,
deep-shell-satisfiable bound (the measures are disjoint subsets of `Ω_u`), in contrast to the
faithful model leaf's baked-in constant `chernoffModelArea ∈ [1,4]`. -/
theorem chernoffAreaFamilySum_genuineCarryChern_le_one (ctx : ActualFailureContext)
    (hK : chernoffClass0KraftSum ctx ≤ 1) :
    chernoffAreaFamilySum (genuineCarryChern ctx hK) ≤ 1 := by
  rw [chernoffAreaFamilySum_genuineCarryChern_eq ctx hK]
  exact hK

/-! ## 2.  The four V3 class-0 fields, reduced to the genuine matching residual

Over the faithful four-path family the four fields ARE a `Chernoff221AAreaMatchedCharge budget
(faithfulChern budget)` (`Chernoff221AAreaClosureCore.lean`).  We expose the `ofCountDom` builder
specialised to the faithful family — `hne` is discharged by `class0_highCostFamily_nonempty`, leaving
the genuine I.4.2 progress count `hcard` and the J.1.7 per-path area domination `hdom`. -/

/-- **The four V3 class-0 fields, from the genuine matching residual (count + per-path domination).**

`chernoffClass0_of_countDom budget` is the partially-applied `Chernoff221AAreaMatchedCharge.ofCountDom`
over the faithful family `faithfulChern budget`, with the family-nonemptiness `hne` discharged from
`class0_highCostFamily_nonempty`.  Supplying

* `hcard ctx : |routedFibre … 0| ≤ |highCostSet (faithfulChern budget ctx)|` (the I.4.2 progress
  count), and
* `hdom ctx k : windowExcess(k) ≤ (faithfulChern budget ctx).weight (finRankMatch … k)` (the matched
  J.1.7 per-path area domination)

yields a `Chernoff221AAreaMatchedCharge budget (faithfulChern budget)` whose four fields
`.chargeOf / .hmaps / .hinj / .hdom` are, by `@[reducible]` `faithfulChern`, exactly the four
`Erdos260MinimalResidualV3` class-0 fields. -/
def chernoffClass0_of_countDom
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) :=
  Chernoff221AAreaMatchedCharge.ofCountDom budget (faithfulChern budget)
    (fun ctx => class0_highCostFamily_nonempty budget ctx)

/-- **Exact V3 field 1 — `chernoffChargeOf`.**  The matched-charge map carries the exact
`Erdos260MinimalResidualV3.chernoffChargeOf` type (`@[reducible]` `faithfulChern` makes the codomains
defeq). -/
def chernoffChargeOf_field
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (C : Chernoff221AAreaMatchedCharge budget (faithfulChern budget)) :
    ∀ ctx : ActualFailureContext,
      ℕ → ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.α :=
  C.chargeOf

/-- **Exact V3 field 2 — `chernoffMaps`.**  Each routed class-0 start lands in the §22 high-cost
family (the 22.1A shell-paid embedding). -/
theorem chernoffMaps_field
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (C : Chernoff221AAreaMatchedCharge budget (faithfulChern budget)) :
    ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        C.chargeOf ctx k ∈ highCostSet
          ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.paths
          ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.cost
          ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.Y :=
  C.hmaps

/-- **Exact V3 field 3 — `chernoffInj`.**  Distinct progress starts get distinct §22 paths (K.1.3
endpoint disjointness). -/
theorem chernoffInj_field
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (C : Chernoff221AAreaMatchedCharge budget (faithfulChern budget)) :
    ∀ ctx : ActualFailureContext,
      ∀ x ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        ∀ y ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
          C.chargeOf ctx x = C.chargeOf ctx y → x = y :=
  C.hinj

/-- **Exact V3 field 4 — `chernoffDom`.**  The matched J.1.7 per-path area domination
`windowExcess(k) ≤ chernoff.weight (chargeOf k)`. -/
theorem chernoffDom_field
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (C : Chernoff221AAreaMatchedCharge budget (faithfulChern budget)) :
    ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.weight
              (C.chargeOf ctx k) :=
  C.hdom

/-- **The V3 Chernoff ledger field, from the four matched-charge fields.**  Exactly the proposition
discharged by `Erdos260MinimalResidualV3.hChernoffField` — `routedClassMassOf … 0 ≤ termChernoff` —
reproduced through the existing `Chernoff221AAreaMatchedCharge.hChernoffField`. -/
theorem chernoffClass0_hChernoffField
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (C : Chernoff221AAreaMatchedCharge budget (faithfulChern budget)) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 0
        ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  C.hChernoffField

/-! ## 3.  The genuine Kraft route to the V3 ledger bound (deep-shell-satisfiable)

The same ledger bound `routedClassMassOf … 0 ≤ termChernoff`, but proved through the **genuine** §22
stopped-branch family `genuineCarryChern` (where the count is the shell-scaling progress count and
the area is the Kraft sum), not the four-path collapse.  This is the manuscript-faithful route. -/

/-- **The genuine matched J.1.7 area charge over the actual stopped branches.**  `ofCountDom`
specialised to the genuine §22 family `fun ctx => genuineCarryChern ctx (hK ctx)`.  The residual is
`hne` (the stopped family is nonempty), the **shell-scaling** I.4.2 progress count `hcard`
(`|routedFibre … 0| ≤ |stoppedBranches|`, NOT the false `4`), and the J.1.7 per-path area domination
`hdom`. -/
def chernoffClass0_genuine_of_kraftCountDom
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hK : ∀ ctx : ActualFailureContext, chernoffClass0KraftSum ctx ≤ 1) :=
  Chernoff221AAreaMatchedCharge.ofCountDom budget (fun ctx => genuineCarryChern ctx (hK ctx))

/-- **The genuine routed class-0 mass is `≤ 1` — via Kraft.**  The matched area charge over the
actual stopped branches gives `routedClassMassOf … 0 ≤ chernoffAreaFamilySum (genuineCarryChern ctx)`,
and the Kraft inequality bounds that area sum by `1`. -/
theorem chernoffClass0_routedMass_le_one_of_kraft
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hK : ∀ ctx : ActualFailureContext, chernoffClass0KraftSum ctx ≤ 1)
    (C : Chernoff221AAreaMatchedCharge budget (fun ctx => genuineCarryChern ctx (hK ctx)))
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 0 ≤ 1 :=
  le_trans (C.hAreaBound ctx) (chernoffAreaFamilySum_genuineCarryChern_le_one ctx (hK ctx))

/-- **The V3 Chernoff ledger bound, proved via the genuine Kraft route.**

`routedClassMassOf … 0 ≤ termChernoff (faithfulCapacityPhases budget ctx)` — the **exact**
`Erdos260MinimalResidualV3.hChernoffField` proposition — discharged through the genuine §22
stopped-branch family and the Kraft area sum: `routedClassMassOf … 0 ≤ 1 ≤ chernoffModelArea =
termChernoff`.  Unlike `chernoffClass0_hChernoffField`, the count residual here SCALES with the shell
(`≤ |stoppedBranches|`), so this route does not pass through the deep-shell-false `|fibre| ≤ 4`
collapse; the only analytic input is the §22 antichain/Kraft measure-sum `hK`. -/
theorem chernoffClass0_hChernoffField_of_kraft
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hK : ∀ ctx : ActualFailureContext, chernoffClass0KraftSum ctx ≤ 1)
    (C : Chernoff221AAreaMatchedCharge budget (fun ctx => genuineCarryChern ctx (hK ctx)))
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 0
      ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData := by
  have hone := chernoffClass0_routedMass_le_one_of_kraft budget hK C ctx
  have hge : (1 : ℝ) ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData := by
    rw [termChernoff_faithful_eq]
    exact one_le_chernoffModelArea
  exact le_trans hone hge

/-! ## 4.  Specialisation to the wave-12 budget `v3Budget` (for the coordinator's V4 wiring) -/

/-- **The four V3 class-0 fields over the wave-12 budget.**  `chernoffClass0_of_countDom` at
`budget := v3Budget towerCount runChain returnCharge`; its `.chargeOf / .hmaps / .hinj / .hdom` are
the four `Erdos260MinimalResidualV3` class-0 fields. -/
def v3ChernoffClass0_of_countDom
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx) :=
  chernoffClass0_of_countDom (v3Budget towerCount runChain returnCharge)

/-- **The wave-12 V3 Chernoff ledger bound via the genuine Kraft route.**  `routedClassMassOf … 0 ≤
termChernoff (faithfulCapacityPhases (v3Budget …) ctx)` from the genuine stopped-branch matched charge
and the Kraft inequality. -/
theorem v3_chernoffClass0_hChernoffField_of_kraft
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (hK : ∀ ctx : ActualFailureContext, chernoffClass0KraftSum ctx ≤ 1)
    (C : Chernoff221AAreaMatchedCharge (v3Budget towerCount runChain returnCharge)
          (fun ctx => genuineCarryChern ctx (hK ctx)))
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (v3Budget towerCount runChain returnCharge ctx).route 0
      ≤ termChernoff
          (faithfulCapacityPhases (v3Budget towerCount runChain returnCharge) ctx).toClosurePhaseData :=
  chernoffClass0_hChernoffField_of_kraft (v3Budget towerCount runChain returnCharge) hK C ctx

/-! ## 5.  Non-vacuity — the genuine family is real, never a degenerate stand-in -/

/-- **Non-vacuity.**  Whenever the genuine matching residual holds (the stopped family is nonempty,
the shell-scaling count, the per-path domination) at a fixed `hK`, the genuine matched area charge is
inhabited — over the actual carry stopped-branch family with the genuine integer-carry measure, never
an empty/zero/degenerate stand-in. -/
theorem genuineCarryChern_matchedCharge_nonvacuous
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hK : ∀ ctx : ActualFailureContext, chernoffClass0KraftSum ctx ≤ 1)
    (hne : ∀ ctx : ActualFailureContext,
      (highCostSet (genuineCarryChern ctx (hK ctx)).paths (genuineCarryChern ctx (hK ctx)).cost
        (genuineCarryChern ctx (hK ctx)).Y).Nonempty)
    (hcard : ∀ ctx : ActualFailureContext,
      (routedFibre ctx.n24CarryData (budget ctx).route 0).card
        ≤ (highCostSet (genuineCarryChern ctx (hK ctx)).paths (genuineCarryChern ctx (hK ctx)).cost
            (genuineCarryChern ctx (hK ctx)).Y).card)
    (hdom : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ (genuineCarryChern ctx (hK ctx)).weight
              (finRankMatch (routedFibre ctx.n24CarryData (budget ctx).route 0)
                (highCostSet (genuineCarryChern ctx (hK ctx)).paths
                  (genuineCarryChern ctx (hK ctx)).cost (genuineCarryChern ctx (hK ctx)).Y)
                (hne ctx) k)) :
    Nonempty (Chernoff221AAreaMatchedCharge budget (fun ctx => genuineCarryChern ctx (hK ctx))) :=
  ⟨chernoffClass0_genuine_of_kraftCountDom budget hK hne hcard hdom⟩

/-! ## 6.  Honest residual inventory -/

/-- The precise status of the class-0 Chernoff ledger leaf after this module. -/
def chernoffClass0GenuineLeafResiduals : List String :=
  [ "PROVED (Kraft does the work) — chernoffAreaFamilySum_genuineCarryChern_le_one: over the GENUINE " ++
      "§22 carry stopped-branch family genuineCarryChern (weight 2^{-branchShellCost b} = " ++
      "carryThresholdMeasure, genuineCarryChern_weight_faithful; Y = 0 so the high-cost set is the " ++
      "full family), the matched J.1.7 area family-sum chernoffAreaFamilySum = ∑_{b∈stoppedBranches} " ++
      "2^{-cost(b)} ≤ 1 is DERIVED from the single antichain/Kraft input hK. The genuine ChernoffPathData " ++
      "is inhabited from hK alone: its moment budget weightedMoment … 1 ≤ 1 IS the Kraft inequality, " ++
      "and its manuscript budget 1 ≤ c⋆ξX/6 is manuscript_chernoff_budget_ge_one. No count, no per-path " ++
      "charge enters; this REPLACES the faithful model leaf's baked-in constant chernoffModelArea ∈ [1,4].",
    "REDUCED (the four V3 fields, faithful family) — chernoffClass0_of_countDom budget = " ++
      "Chernoff221AAreaMatchedCharge.ofCountDom budget (faithfulChern budget) with hne discharged from " ++
      "class0_highCostFamily_nonempty. The four fields chernoffChargeOf/chernoffMaps/chernoffInj/" ++
      "chernoffDom ARE C.chargeOf/C.hmaps/C.hinj/C.hdom (exact V3 types: chernoffChargeOf_field, " ++
      "chernoffMaps_field, chernoffInj_field, chernoffDom_field). hChernoffField (routedClassMassOf … 0 " ++
      "≤ termChernoff) is chernoffClass0_hChernoffField. Over the faithful four-path leaf this forces " ++
      "the deep-shell-false |routedFibre … 0| ≤ 4 (faithful_matching_iff_le_four) and the unit charge " ++
      "(weights 2^{-cost} ≤ 1), so the four fields CANNOT be proved unconditionally.",
    "ADVANCED (the ledger bound via the genuine Kraft route) — chernoffClass0_hChernoffField_of_kraft " ++
      "(specialised v3_chernoffClass0_hChernoffField_of_kraft): the EXACT V3 ledger proposition " ++
      "routedClassMassOf … 0 ≤ termChernoff is proved through the genuine stopped-branch family via " ++
      "routedClassMassOf … 0 ≤ chernoffAreaFamilySum (genuineCarryChern ctx) ≤ 1 ≤ chernoffModelArea = " ++
      "termChernoff (one_le_chernoffModelArea, termChernoff_faithful_eq). The count residual here is the " ++
      "SHELL-SCALING progress count |routedFibre … 0| ≤ |stoppedBranches| (NOT the false 4), so this " ++
      "route avoids the four-path collapse.",
    "SHARPEST REMAINING HYPOTHESIS (the §22 antichain measure-sum) — hK : ∀ ctx, chernoffClass0KraftSum " ++
      "ctx ≤ 1, i.e. ∑_{b∈ctx.n24CarryData.stoppedBranches} (1/2)^branchShellCost b ≤ 1 (proof_v4 line " ++
      "818: the principal children of a stopped node are DISJOINT subsets of Ω_u, so their integer-carry " ++
      "measures sum to ≤ the parent measure ≤ 1). This is EXACTLY the explicit hKraft argument of " ++
      "carryAlignedShellPaidChernoff22_1AOfShell. It is carried (not proved) because the formalized " ++
      "carryThresholdMeasure Q σ k = (1/2)^prefixGapSum σ k is the bare dyadic value with no " ++
      "disjointness datum attached — the genuinely geometric stopped-tree antichain fact.",
    "MATCHING RESIDUAL (orthogonal to every phase budget) — hcard: the I.4.2 progress count " ++
      "|routedFibre … 0| ≤ |highCostSet (chern ctx)| (against the genuine §22 family this SCALES with " ++
      "the shell); hdom: the J.1.7 per-path area domination windowExcess(k) ≤ (chern ctx).weight " ++
      "(finRankMatch … k) (each progress start charged its OWN §22 path's area weight). Both are fed to " ++
      "the PROVED Chernoff221AAreaMatchedCharge.ofCountDom (order-rank finRankMatch + " ++
      "perOutput_charged_of_injOn). Non-vacuous (genuineCarryChern_matchedCharge_nonvacuous).",
    "COORDINATOR WIRING (into Erdos260MinimalResidualV4 via toV3) — set the four V3 class-0 fields to " ++
      "(v3ChernoffClass0_of_countDom towerCount runChain returnCharge hcard hdom).{chargeOf, hmaps, " ++
      "hinj, hdom}; the resulting Erdos260MinimalResidualV3.hChernoffField is reproduced. The genuine " ++
      "deep-shell-satisfiable ledger bound is v3_chernoffClass0_hChernoffField_of_kraft, available once " ++
      "the §22 antichain hK and the genuine matched charge are supplied." ]

theorem chernoffClass0GenuineLeafResiduals_nonempty :
    chernoffClass0GenuineLeafResiduals ≠ [] := by
  simp [chernoffClass0GenuineLeafResiduals]

/-! ## 7.  Axiom-cleanliness audit -/

#print axioms genuineCarryChern
#print axioms genuineCarryChern_weight_faithful
#print axioms chernoffAreaFamilySum_genuineCarryChern_eq
#print axioms chernoffAreaFamilySum_genuineCarryChern_le_one
#print axioms chernoffClass0_of_countDom
#print axioms chernoffChargeOf_field
#print axioms chernoffMaps_field
#print axioms chernoffInj_field
#print axioms chernoffDom_field
#print axioms chernoffClass0_hChernoffField
#print axioms chernoffClass0_genuine_of_kraftCountDom
#print axioms chernoffClass0_routedMass_le_one_of_kraft
#print axioms chernoffClass0_hChernoffField_of_kraft
#print axioms v3ChernoffClass0_of_countDom
#print axioms v3_chernoffClass0_hChernoffField_of_kraft
#print axioms genuineCarryChern_matchedCharge_nonvacuous

end

end Erdos260
