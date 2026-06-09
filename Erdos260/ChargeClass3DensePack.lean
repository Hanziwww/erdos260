import Erdos260.Erdos260ChargeReduced

/-!
# Class 3 — the DensePack charging bound `hDensePack`, closed onto the proven DensePack output bound

This module (NEW; it edits no existing file) attacks the **class-3 DensePack charging bound**
`hDensePack` of the consolidated faithful charge residual
`Erdos260ChargeResidual` (`Erdos260ChargeReduced.lean`):

```
hDensePack : ∀ ctx : ActualFailureContext,
  routedClassMassOf ctx.n24CarryData (budget ctx).route 3
    ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData
```

i.e. the genuine J.1.1 charging *direction* for the DensePack class: the routed carry **mass** of
the class-3 fibre is dominated by the closed DensePack phase **term** of the faithful assembly.

## The connection to the proven DensePack-under-failure infrastructure

The DensePack *output* bound is **already proven** and reused unchanged here:

* `termDensePack data = (data.densePack.densePackPoints.card : ℝ)`
  (`AppendixI_PhaseMass.termDensePack`) — the phase term **is** the dense-marker point count;
* `corollaryK1_3_densePackUnderFailure` (`DensePack.lean`) — the K.1.1 endpoint-disjoint cover under
  the positive-density failure `markersCard ≤ c_*·X`: `densePackPoints.card ≤ c_*·X·(2 spread+1)`;
* `termDensePack_le_budget` (`AppendixI_PackageBounds.lean`) — chaining the K.1.3 cover with the
  K.4 smallness `data.densePack.hsmall` yields the manuscript per-phase budget
  `termDensePack ≤ c_*·ξ·X/6`.  For the **faithful** assembly the failure hypothesis `ctx.hfailure`
  is already baked into the DensePack leaf `appendixNGapCanonicalYActualDensePackToGrounded`.

What remains to connect the routed carry mass to that proven output bound is the
**J.1.1 routing-to-marker charge** (Lemma J.D): each high-excess start routed to class 3 packs
into a *distinct* dense-marker point (`densePackPoints`) and there carries at most **one unit** of
window-excess mass.  Concretely (the mandate's chain):

```
routedClassMassOf route 3
  ≤ |densePackPoints| · (unit multiplier)          -- routedClassMassOf_le_countMultiplier (count = |densePackPoints|, mult = 1)
  = termDensePack                                   -- termDensePack = densePackPoints.card
  ≤ c_*·ξ·X/6 .                                     -- PROVEN termDensePack_le_budget (K.1.3 + K.4)
```

## What is genuinely CLOSED here (axiom-clean)

Everything downstream of the marker charge is fully discharged from the **proven** DensePack infra:

* `Class3DensePackCharge.fibreCard_le_markerCard` — the **K.1.1 cardinal comparison**
  `|routedFibre 3| ≤ |densePackPoints|`, derived from the injection (`Finset.card_le_card_of_injOn`);
* `Class3DensePackCharge.routedClass3_le_markerCard` — the mandate's `≤ |densePackPoints|·1` step,
  via the proven `routedClassMassOf_le_countMultiplier` (unit multiplier) + the cardinal comparison;
* `Class3DensePackCharge.routedClass3_le_termDensePack` — the **exact `hDensePack` bound**
  `routedClassMassOf route 3 ≤ termDensePack (faithful phases)`, via the proven J.1.8 charged-ledger
  summation `routedDensePack_le_term_of_matching`;
* `Class3DensePackCharge.routedClass3_le_budget` — the **full numeric close**
  `routedClassMassOf route 3 ≤ c_*·ξ·X/6`, chaining the proven `termDensePack_le_budget`;
* `hDensePack_of_class3Charge` — the per-context charge family produces **exactly** the
  `Erdos260ChargeResidual.hDensePack` field.

## The minimal remaining residual (the routing-to-marker injection)

In the `Erdos260ChargeResidual` interface the seven-class routing `(budget ctx).route` is *free*
data (owned by the sibling J.1.1 routing worker), so the relation between the class-3 fibre and the
shell's `densePackPoints` cannot be derived without the genuine J.1.1 / J.D charging content.  That
content is isolated here as the **smallest named residual**, `Class3DensePackCharge`:

* a charging map `markerOf : ℕ → ℕ` of the class-3 fibre,
* `maps_into` — the routing-to-marker **support injection** (each routed-3 start lands in
  `densePackPoints`),
* `matching` — the J.1.1 **matching** (distinct starts pack to distinct markers, the K.1.1
  endpoint-disjointness in carry form),
* `unit_charge` — the J.D **unit charge** (each routed-3 start carries window excess `≤ 1`).

This residual is genuinely satisfiable (non-vacuous): `Class3DensePackCharge.ofSubsetSelf` builds it
from the manuscript situation where the class-3 starts *are* dense-marker points with unit excess
(the identity charging map), with **no** emptiness assumption.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The minimal residual: the J.1.1 / J.D dense-marker charging map for class 3

The routing-to-marker injection plus unit charge — the genuine surviving content connecting the
class-3 routed carry mass to the proven DensePack output bound.  Stated against the **faithful**
capacity assembly `faithfulCapacityPhases budget ctx` and the N.24 carry data `ctx.n24CarryData`,
exactly the data of the `hDensePack` field of `Erdos260ChargeResidual`. -/

/-- **The class-3 DensePack charging residual (J.1.1 routing-to-marker injection + J.D unit charge).**

For a failure context `ctx` and the shared routed budget `budget ctx`, this bundles the genuine
J.1.1 / J.D content that charges the DensePack class onto the shell's dense-marker points:

* `markerOf` — the charging map of each high-excess start to a dense-marker point;
* `maps_into` — the **support injection**: each start routed to class 3 lands in `densePackPoints`
  of the faithful DensePack leaf (the K.1.1 / J.5 dense-density geometry);
* `matching` — the **matching** property: distinct routed-3 starts charge distinct markers (the
  K.1.1 endpoint-disjoint cover read on the carry side);
* `unit_charge` — the **J.D unit charge**: each routed-3 start carries at most one unit of
  window-excess mass.

These four are the only undischarged inputs; everything else (the cardinal comparison, the term
identification, the per-phase budget) is proven from the DensePack-under-failure infrastructure. -/
structure Class3DensePackCharge
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) where
  /-- The J.1.1 / J.D charging map of high-excess starts to dense-marker points. -/
  markerOf : ℕ → ℕ
  /-- **Support injection** — each start routed to class 3 lands in `densePackPoints`. -/
  maps_into : ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
    markerOf k ∈ (faithfulCapacityPhases budget ctx).toClosurePhaseData.densePack.densePackPoints
  /-- **Matching** — distinct routed-3 starts charge distinct markers (K.1.1 carry-side). -/
  matching : ∀ x ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
    ∀ y ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
      markerOf x = markerOf y → x = y
  /-- **J.D unit charge** — each routed-3 start carries window excess `≤ 1`. -/
  unit_charge : ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ 1

namespace Class3DensePackCharge

variable {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    {ctx : ActualFailureContext}

/-! ## 2.  The K.1.1 marker-packing count comparison (discharged from the injection)

The "proven marker-packing count" `|routedFibre 3| ≤ |densePackPoints|` is **not** assumed: it is
derived from the support injection + matching by `Finset.card_le_card_of_injOn`.  This is the K.1.1
endpoint-disjoint cover principle in carry form. -/

/-- **K.1.1 cardinal comparison.**  The class-3 fibre injects into the dense-marker points, so its
cardinality is at most the marker count `|densePackPoints|` — the carry-side K.1.1 endpoint-disjoint
cover, derived (not assumed) from `maps_into` + `matching`. -/
theorem fibreCard_le_markerCard (charge : Class3DensePackCharge budget ctx) :
    (routedFibre ctx.n24CarryData (budget ctx).route 3).card
      ≤ (faithfulCapacityPhases budget ctx).toClosurePhaseData.densePack.densePackPoints.card :=
  Finset.card_le_card_of_injOn charge.markerOf charge.maps_into
    (by
      intro x hx y hy h
      simp only [Finset.mem_coe] at hx hy
      exact charge.matching x hx y hy h)

/-! ## 3.  The routed class-3 mass `≤ |densePackPoints|·1` (the mandate's count×multiplier step)

The proven `routedClassMassOf_le_countMultiplier`, with the **unit multiplier** (`mult = 1`, the J.D
charge) and the **marker count** (`count = |densePackPoints|`, the discharged K.1.1 comparison),
yields `routedClassMassOf route 3 ≤ |densePackPoints|·1 = |densePackPoints|`. -/

/-- **The `≤ |densePackPoints|·(unit multiplier)` step (proven `routedClassMassOf_le_countMultiplier`).**

The mandate's first inequality: with the J.D unit multiplier and the K.1.1 marker-packing count
(`fibreCard_le_markerCard`), the routed class-3 carry mass is at most the dense-marker point count. -/
theorem routedClass3_le_markerCard (charge : Class3DensePackCharge budget ctx) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 3
      ≤ ((faithfulCapacityPhases budget ctx).toClosurePhaseData.densePack.densePackPoints.card : ℝ) := by
  have h :=
    routedClassMassOf_le_countMultiplier ctx.n24CarryData (budget ctx).route 3
      charge.unit_charge (by norm_num)
      (show ((routedFibre ctx.n24CarryData (budget ctx).route 3).card : ℝ)
          ≤ ((faithfulCapacityPhases budget ctx).toClosurePhaseData.densePack.densePackPoints.card : ℝ)
        from by exact_mod_cast charge.fibreCard_le_markerCard)
  simpa using h

/-! ## 4.  The exact `hDensePack` bound `routedClassMassOf route 3 ≤ termDensePack`

Through the proven J.1.8 charged-ledger summation `routedDensePack_le_term_of_matching`: the routed
class-3 mass, charged by the matching marker map with unit per-marker charge, is dominated by the
DensePack phase term (the dense-marker point count, `termDensePack_eq_chargedArea`). -/

/-- **The class-3 charging bound (the exact `Erdos260ChargeResidual.hDensePack` field).**

`routedClassMassOf route 3 ≤ termDensePack (faithfulCapacityPhases budget ctx)`, via the proven
J.1.8 charged-ledger summation `routedDensePack_le_term_of_matching` applied to the matching marker
charge.  This is the genuine J.1.1 charging *direction* for the DensePack class. -/
theorem routedClass3_le_termDensePack (charge : Class3DensePackCharge budget ctx) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 3
      ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  routedDensePack_le_term_of_matching
    (faithfulCapacityPhases budget ctx).toClosurePhaseData
    ctx.n24CarryData (budget ctx).route
    charge.markerOf charge.maps_into charge.matching charge.unit_charge

/-! ## 5.  The full numeric close `routedClassMassOf route 3 ≤ c_*·ξ·X/6`

Chaining the proven DensePack-under-failure budget `termDensePack_le_budget` (K.1.3 cover + K.4
smallness), the routed class-3 carry mass fits the manuscript per-phase pressure slot. -/

/-- **Full class-3 numeric close (the proven DensePack budget).**

`routedClassMassOf route 3 ≤ c_*·ξ·X/6`, the manuscript per-phase floor, by chaining the
`hDensePack` bound with the **proven** `termDensePack_le_budget`. -/
theorem routedClass3_le_budget (charge : Class3DensePackCharge budget ctx) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 3
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  charge.routedClass3_le_termDensePack.trans
    (termDensePack_le_budget (faithfulCapacityPhases budget ctx).toClosurePhaseData)

end Class3DensePackCharge

/-! ## 6.  The `hDensePack` field of `Erdos260ChargeResidual`, from a per-context charge family

A per-context family of class-3 marker charges produces **exactly** the `hDensePack` field of the
consolidated faithful charge residual — the deliverable that plugs into `Erdos260ChargeResidual`. -/

/-- **The `hDensePack` field, from the class-3 marker-charge family.**

For a shared routed budget and a per-context class-3 charging residual, this is the exact type of
the `hDensePack` field of `Erdos260ChargeResidual`.  It plugs in directly (the type matches with no
coercion), closing the DensePack charging bound modulo only the per-context marker injection. -/
theorem hDensePack_of_class3Charge
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (charge : ∀ ctx : ActualFailureContext, Class3DensePackCharge budget ctx) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 3
        ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  fun ctx => (charge ctx).routedClass3_le_termDensePack

/-- **The full per-context class-3 numeric floor, from the marker-charge family.** -/
theorem routedClass3_le_budget_of_class3Charge
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (charge : ∀ ctx : ActualFailureContext, Class3DensePackCharge budget ctx) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 3
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  fun ctx => (charge ctx).routedClass3_le_budget

/-! ## 7.  Non-vacuity — the residual is genuinely satisfiable (non-degenerate witness)

The natural manuscript situation: when the class-3 starts *are* dense-marker points carrying unit
window excess (the J.1.1 routing sends a start to DensePack exactly when it is a dense marker), the
**identity** charging map is a matching support injection with unit charge.  No emptiness is
assumed, so this is a genuine non-degenerate inhabitation of the residual. -/

/-- **Non-vacuity witness — the identity (self-)charging on a dense-marker fibre.**

If the class-3 fibre already sits inside the dense-marker points (`hsub`, the J.5 dense-density
routing) with unit window excess (`hdom`, J.D), the identity map `markerOf := id` is a matching
support injection with unit charge — a genuine `Class3DensePackCharge`.  This shows the residual is
consistent and satisfiable without any degenerate/empty shortcut. -/
def Class3DensePackCharge.ofSubsetSelf
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (hsub : routedFibre ctx.n24CarryData (budget ctx).route 3
      ⊆ (faithfulCapacityPhases budget ctx).toClosurePhaseData.densePack.densePackPoints)
    (hdom : ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ 1) :
    Class3DensePackCharge budget ctx where
  markerOf := id
  maps_into := fun _k hk => hsub hk
  matching := fun _x _hx _y _hy h => h
  unit_charge := hdom

/-! ## 8.  Honest residual inventory -/

/-- The precise status of the class-3 DensePack charging bound after this module. -/
def chargeClass3DensePackResiduals : List String :=
  [ "CLOSED (term bound, the exact hDensePack field) — Class3DensePackCharge.routedClass3_le_termDensePack: " ++
      "routedClassMassOf ctx.n24CarryData (budget ctx).route 3 ≤ termDensePack (faithfulCapacityPhases " ++
      "budget ctx).toClosurePhaseData, via the PROVEN J.1.8 charged-ledger summation " ++
      "routedDensePack_le_term_of_matching. hDensePack_of_class3Charge produces the exact field type.",
    "CLOSED (numeric floor) — Class3DensePackCharge.routedClass3_le_budget: routedClassMassOf route 3 " ++
      "≤ c_*·ξ·X/6, chaining the PROVEN DensePack-under-failure budget termDensePack_le_budget " ++
      "(K.1.3 cover corollaryK1_3_densePackUnderFailure + K.4 smallness; ctx.hfailure is baked into " ++
      "the faithful DensePack leaf appendixNGapCanonicalYActualDensePackToGrounded).",
    "CLOSED (K.1.1 marker-packing count) — Class3DensePackCharge.fibreCard_le_markerCard: " ++
      "|routedFibre 3| ≤ |densePackPoints|, DERIVED from the support injection via " ++
      "Finset.card_le_card_of_injOn (NOT assumed). Class3DensePackCharge.routedClass3_le_markerCard " ++
      "gives the mandate's ≤ |densePackPoints|·1 step via the PROVEN routedClassMassOf_le_countMultiplier.",
    "RESIDUAL (the smallest remaining gap, the J.1.1 routing-to-marker injection) — Class3DensePackCharge: " ++
      "a charging map markerOf with (maps_into) the support injection into densePackPoints, (matching) " ++
      "the K.1.1 endpoint-disjoint matching, and (unit_charge) the J.D unit charge windowExcess ≤ 1. The " ++
      "seven-class routing (budget ctx).route is FREE data in Erdos260ChargeResidual, so this carry↔marker " ++
      "relation is genuinely undischarged here; it is the deep J.1.1/J.D charging content.",
    "NON-VACUOUS — Class3DensePackCharge.ofSubsetSelf builds the residual from the natural manuscript " ++
      "situation (class-3 starts are dense markers with unit excess, identity charging map); no " ++
      "degenerate/empty shortcut is used for the main bound." ]

theorem chargeClass3DensePackResiduals_nonempty : chargeClass3DensePackResiduals ≠ [] := by
  simp [chargeClass3DensePackResiduals]

/-! ## 9.  Axiom-cleanliness audit -/

#print axioms Class3DensePackCharge.fibreCard_le_markerCard
#print axioms Class3DensePackCharge.routedClass3_le_markerCard
#print axioms Class3DensePackCharge.routedClass3_le_termDensePack
#print axioms Class3DensePackCharge.routedClass3_le_budget
#print axioms hDensePack_of_class3Charge
#print axioms routedClass3_le_budget_of_class3Charge
#print axioms Class3DensePackCharge.ofSubsetSelf

end

end Erdos260
