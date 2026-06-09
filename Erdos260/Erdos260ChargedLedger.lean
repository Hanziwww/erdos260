import Erdos260.ChargeClass0Chernoff
import Erdos260.ChargeClass1CNL
import Erdos260.ChargeClass3DensePack
import Erdos260.ChargeClassTRT
import Erdos260.OldResL65Core

/-!
# Erdős #260 — the J.1.1 **charged ledger**, the single residual surface (FINAL consolidation)

This module (NEW; it edits no existing file) is the **final consolidation endpoint**.
The five charging-class workers and the L.6.5 worker each proved that one per-class
charging bound of the consolidated faithful charge residual `Erdos260ChargeResidual`
(`Erdos260ChargeReduced.lean`) follows from one *minimal* residual of the same kind — a
per-class J.1.1 charging map — and that the L.6.5 old-residual smallness is **fully
closed**.  Here those minimal residuals are bundled into a **single** structure
`ChargedLedger`, and the entire theorem is reduced to it:

```
erdos260_chargedledger_reduced : ChargedLedger → Erdos260Statement.
```

So the whole formalization reads "**Erdős #260 follows from the J.1.1 charged ledger**".

## What `ChargedLedger` bundles (ONLY the genuine surviving charging content)

The five workers' minimal residuals, and nothing else:

* `trt : ChargeClassTRTData` — the shared **seven-class J.1.1 routing** `route` together
  with the three single-class phase-capacity fraction budgets (Tower I.3.1 / Return I.5.1
  / Run I.5.2) as per-fibre count×multiplier data.  Its `toBudget` produces the
  `SeparatedPhaseRoutedBudget` shared by every other charging map, and its `hTRT` is the
  joint Tower+Return+Run **N.24 same-threshold compression** bound.
* `chernoff : Class0ChernoffCharge trt.toBudget` — the **class-0** (Chernoff / shell-paid
  progress, 22.1A) charging map (count×multiplier or J.1.7 charging map).
* `cnl : Class1CNLChargeData trt.toBudget` — the **class-1** (clean-CNL Kraft tail,
  L.1.2/G.35) charging map: the J.1.1 charge injection into the surviving clean-CNL
  transition family with the per-codeword Kraft rate.
* `densePack : ∀ ctx, Class3DensePackCharge trt.toBudget ctx` — the **class-3** (DensePack
  marker mass, J.D) routing-to-marker injection with unit charge.
* `hOldRes` — the **class-6** old-residual leakage routing bound `routedClassMassOf
  route 6 ≤ ∑_{k∈K} oldResAt k`, against the genuine nonzero L.6.4 branch mass realised
  by the fully-closed L.6.5 data `oldResIdxVal`/`oldResAtVal`.

## What is DISCHARGED INTERNALLY (not in `ChargedLedger`)

Everything the workers proved is wired in from the proven results, never carried:

* the **L.6.5 smallness** `hpoint`/`hbound_nonneg`/`hdensity` — **fully closed** by
  `oldResL65_hpoint`/`oldResL65_hbound_nonneg`/`oldResL65_hdensity` (the genuine L.20/L.21
  multiplier and the L.22 low-density endpoint count), with the genuine nonzero branch
  mass `oldResIdxVal`/`oldResAtVal` (NOT the degenerate `oldResMass = 0`);
* the **constants** `Cres`/`Y`/`Csupp`/`Ij` (`= C_Q`/`1`/`C_Q`/`ξ`) and the product
  constant `oldResConstVal = C_Q·c_*` with the "choose `c_*` last" condition
  `oldResConstVal_constCond` — closed in `OldResL65Core`/`OldResidualCore`;
* the **phase budgets** (`ClosurePhaseMass ≤ c⋆·ξ·X`), the **three closed phase
  capacities** (Chernoff 22.1A, clean-CNL L.1.2/G.35, DensePack I.4.1/K.1.3), the **N.24
  compression** spine, the **pressure floor** (Lemma 21.1), and the **faithful Dirty**
  absolute-`C` model — all discharged by the spine / faithful assembly inside
  `erdos260_charge_reduced` (`Erdos260ChargeReduced.lean`).

The endpoint is assembled by feeding each charging map through its `hX_of_*` producer
into the consolidated `Erdos260ChargeResidual` (via the fully-closed L.6.5 drop-in
`chargeResidualOfRoutingAndOldRes`) and applying the capstone `erdos260_charge_reduced`.
No degenerate shortcut: the genuine L.6.5 path is used throughout.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The J.1.1 charged ledger

The single residual surface: the seven-class routing + the five per-class J.1.1 charging
maps (Chernoff 0, clean-CNL 1, DensePack 3, the joint Tower+Return+Run 2/4/5, and the
old-residual class 6).  Every other charging map is stated against the budget produced by
the TRT data, so the routing is shared (one J.1.1 routing for the whole ledger). -/

/-- **The J.1.1 charged ledger of Erdős #260.**

The entire surviving content of the theorem, after every closed component has been
discharged internally: the shared seven-class J.1.1 routing (carried by `trt`, exposed as
`trt.toBudget`), and the per-class charging maps for the six closure classes (0/1/3 and
the joint 2/4/5) plus the old-residual class (6).  The L.6.5 smallness, the constants, the
phase budgets, the three closed capacities, the N.24 compression, the faithful Dirty model
and the pressure floor are **all** discharged internally and do **not** appear here. -/
structure ChargedLedger where
  /-- **Classes 2/4/5 + the shared routing.**  The Tower+Return+Run data: the seven-class
  J.1.1 routing `route`, the three single-class phase-capacity fraction budgets (Tower
  I.3.1, Return I.5.1, Run I.5.2) as per-fibre count×multiplier data, and (via `hTRT`) the
  joint N.24 same-threshold (TRT) compression bound.  `trt.toBudget` is the
  `SeparatedPhaseRoutedBudget` shared by every other charging map. -/
  trt : ChargeClassTRTData
  /-- **Class 0 — Chernoff / shell-paid progress (22.1A).**  The J.1.1 charging map of the
  class-0 fibre against the faithful Chernoff term (count×multiplier / J.1.7). -/
  chernoff : Class0ChernoffCharge trt.toBudget
  /-- **Class 1 — clean-CNL Kraft tail (L.1.2/G.35).**  The J.1.1 charge injection of the
  class-1 fibre into the surviving clean-CNL transition family with the per-codeword Kraft
  charge bound. -/
  cnl : Class1CNLChargeData trt.toBudget
  /-- **Class 3 — DensePack marker mass (J.D).**  The per-context routing-to-marker
  injection of the class-3 fibre into the dense-marker points with unit window-excess
  charge. -/
  densePack : ∀ ctx : ActualFailureContext, Class3DensePackCharge trt.toBudget ctx
  /-- **Class 6 — the v5 old-residual leakage (Lemma L.6.4).**  The routed class-6 carry
  mass is dominated by the genuine nonzero L.6.4 branch mass `∑_{k∈K} oldResAt k` realised
  by the fully-closed L.6.5 data (`oldResIdxVal`/`oldResAtVal`), NOT the degenerate
  `oldResMass = 0`. -/
  hOldRes : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (trt.toBudget ctx).route 6
      ≤ ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k

namespace ChargedLedger

/-! ## 2.  The shared budget and the five per-class charging fields

Each accessor exposes a field of the consolidated `Erdos260ChargeResidual`, produced from
the matching minimal charging map through the worker's proven `hX_of_*` producer.  These
are exactly the fields fed into `chargeResidualOfRoutingAndOldRes`. -/

/-- The shared J.1.1 routing + the three single-class fraction budgets, as the
`SeparatedPhaseRoutedBudget` consumed by every charging map (`= trt.toBudget`). -/
def budget (L : ChargedLedger) : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  L.trt.toBudget

/-- **Class 0 — the `hChernoff` field.**  Produced from the class-0 charging map by the
proven `Class0ChernoffCharge.hChernoff` (count×multiplier through
`routedClassMassOf_le_countMultiplier`). -/
theorem hChernoff (L : ChargedLedger) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (L.trt.toBudget ctx).route 0
        ≤ termChernoff (faithfulCapacityPhases L.trt.toBudget ctx).toClosurePhaseData :=
  L.chernoff.hChernoff

/-- **Class 1 — the `hCnl` field.**  Produced from the class-1 charge injection by the
proven `Class1CNLChargeData.hCnl` (the weighted-Kraft reindexing close). -/
theorem hCnl (L : ChargedLedger) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (L.trt.toBudget ctx).route 1
        ≤ termCnl (faithfulCapacityPhases L.trt.toBudget ctx).toClosurePhaseData :=
  fun ctx => L.cnl.hCnl ctx

/-- **Class 3 — the `hDensePack` field.**  Produced from the per-context routing-to-marker
injection family by the proven `hDensePack_of_class3Charge` (the J.1.8 charged-ledger
marker summation). -/
theorem hDensePack (L : ChargedLedger) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (L.trt.toBudget ctx).route 3
        ≤ termDensePack (faithfulCapacityPhases L.trt.toBudget ctx).toClosurePhaseData :=
  hDensePack_of_class3Charge L.trt.toBudget L.densePack

/-- **Classes 2/4/5 — the joint `hTRT` field.**  The TRT data's joint N.24 same-threshold
compression bound (`ChargeClassTRTData.hTRT`). -/
theorem hTRT (L : ChargedLedger) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (L.trt.toBudget ctx).route 2
          + routedClassMassOf ctx.n24CarryData (L.trt.toBudget ctx).route 4
          + routedClassMassOf ctx.n24CarryData (L.trt.toBudget ctx).route 5
        ≤ termTower (faithfulCapacityPhases L.trt.toBudget ctx).toClosurePhaseData
          + termReturn (faithfulCapacityPhases L.trt.toBudget ctx).toClosurePhaseData
          + termRun (faithfulCapacityPhases L.trt.toBudget ctx).toClosurePhaseData :=
  L.trt.hTRT

/-! ## 3.  The 5-field ledger expands to the 15-field consolidated residual

The single bundling step: the five charging fields, together with the **fully-closed**
L.6.5 old-residual data (`oldResIdxVal`/`oldResAtVal` and the closed
`oldResL65_hpoint`/`oldResL65_hbound_nonneg`/`oldResL65_hdensity`, wired in by
`chargeResidualOfRoutingAndOldRes`), reconstitute the genuine 15-field
`Erdos260ChargeResidual`.  The L.6.5 smallness and the constants are supplied internally,
not by the ledger. -/

/-- **Expand the charged ledger into the consolidated faithful charge residual.**

The five charging maps are fed through their producers and combined with the genuine,
fully-closed L.6.5 old-residual analytic inputs (the `chargeResidualOfRoutingAndOldRes`
drop-in of `OldResL65Core`) to reconstruct the 15-field `Erdos260ChargeResidual`.  No
`oldResIdx`/`oldResAt`/`Cres`/`Y`/`Csupp`/`Ij`/`hpoint`/`hbound_nonneg`/`hdensity` is
carried by the ledger — all are discharged here from the proven L.6.5 results. -/
def toChargeResidual (L : ChargedLedger) : Erdos260ChargeResidual :=
  chargeResidualOfRoutingAndOldRes L.trt.toBudget
    L.chernoff.hChernoff
    (fun ctx => L.cnl.hCnl ctx)
    (hDensePack_of_class3Charge L.trt.toBudget L.densePack)
    L.trt.hTRT
    L.hOldRes

@[simp] theorem toChargeResidual_budget (L : ChargedLedger) :
    L.toChargeResidual.budget = L.trt.toBudget := rfl

end ChargedLedger

/-! ## 4.  The final endpoint — Erdős #260 from the J.1.1 charged ledger -/

/-- **Erdős #260, reduced to the J.1.1 charged ledger.**

From the charged ledger — the shared seven-class J.1.1 routing, the five per-class J.1.1
charging maps (Chernoff 0, clean-CNL 1, DensePack 3, the joint Tower+Return+Run 2/4/5, and
the old-residual class 6) — the consolidated faithful charge bridge `erdos260_charge_reduced`
proves `Erdos260Statement`.

Discharged **internally** (NOT in the ledger): the **fully-closed L.6.5** smallness
(`hpoint`/`hbound_nonneg`/`hdensity` via the genuine L.20/L.21 multiplier and L.22
endpoint count over the genuine nonzero branch mass — no degenerate `oldResMass = 0`), the
constants (`Cres`/`Y`/`Csupp`/`Ij`, `oldResConstVal = C_Q·c_*`, the "choose `c_*` last"
condition), the full phase budget `ClosurePhaseMass ≤ c⋆·ξ·X`, the three closed phase
capacities (Chernoff 22.1A, clean-CNL L.1.2/G.35, DensePack I.4.1/K.1.3), the N.24
compression spine, the faithful Dirty absolute-`C` model, and the pressure floor (Lemma
21.1).

The genuine deep theorem that remains is exactly the J.1.1 charged-summability content of
Appendix J.1 / L.2: the five per-class charging maps of the ledger.

No `sorry`/`axiom`/`admit`. -/
theorem erdos260_chargedledger_reduced (L : ChargedLedger) : Erdos260Statement :=
  erdos260_charge_reduced L.toChargeResidual

/-! ## 5.  Honest residual inventory -/

/-- The precise status of the consolidation: the ledger fields (genuine surviving content)
and the components discharged internally. -/
def chargedLedgerResiduals : List String :=
  [ "GENUINE-SURVIVING (the J.1.1 charged ledger, 5 fields) — ChargedLedger bundles ONLY: " ++
      "(trt) ChargeClassTRTData = the shared seven-class J.1.1 routing + the three single-class " ++
      "fraction budgets (Tower I.3.1 / Return I.5.1 / Run I.5.2) + the joint N.24 same-threshold " ++
      "TRT compression hTRT (classes 2/4/5); (chernoff) Class0ChernoffCharge = the class-0 " ++
      "Chernoff/shell-paid 22.1A charging map; (cnl) Class1CNLChargeData = the class-1 clean-CNL " ++
      "L.1.2/G.35 Kraft-tail charge injection; (densePack) Class3DensePackCharge = the class-3 J.D " ++
      "routing-to-marker injection with unit charge; (hOldRes) the class-6 old-residual leakage " ++
      "bound against the genuine nonzero L.6.4 branch mass ∑_{k∈K} oldResAt k.",
    "DISCHARGED INTERNALLY (L.6.5 smallness) — hpoint/hbound_nonneg/hdensity are FULLY CLOSED " ++
      "by oldResL65_hpoint (L.20/L.21), oldResL65_hbound_nonneg, oldResL65_hdensity (L.22 low-" ++
      "density endpoint count), over the genuine nonzero branch mass oldResIdxVal/oldResAtVal. " ++
      "NOT the degenerate oldResMass = 0; wired in via chargeResidualOfRoutingAndOldRes.",
    "DISCHARGED INTERNALLY (constants) — Cres = C_Q, Y = 1, Csupp = C_Q, Ij = ξ; the product " ++
      "constant oldResConstVal = C_Q·c_*; and the 'choose c_* last' condition oldResConstVal_constCond. " ++
      "Closed in OldResL65Core / OldResidualCore.",
    "DISCHARGED INTERNALLY (budgets/capacities/compression/floor) — the full phase budget " ++
      "ClosurePhaseMass ≤ c⋆ξX, the three closed phase capacities (Chernoff 22.1A, clean-CNL " ++
      "L.1.2/G.35, DensePack I.4.1/K.1.3), the N.24 compression spine, the faithful Dirty " ++
      "absolute-C model, and the Lemma 21.1 pressure floor — all discharged by the spine / " ++
      "faithful assembly inside erdos260_charge_reduced.",
    "ENDPOINT — erdos260_chargedledger_reduced : ChargedLedger → Erdos260Statement, via " ++
      "ChargedLedger.toChargeResidual (the 5 fields → the 15-field Erdos260ChargeResidual) and " ++
      "the capstone erdos260_charge_reduced.  The whole formalization now reduces to the J.1.1 " ++
      "charged ledger." ]

theorem chargedLedgerResiduals_nonempty : chargedLedgerResiduals ≠ [] := by
  simp [chargedLedgerResiduals]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms erdos260_chargedledger_reduced
#print axioms ChargedLedger.toChargeResidual
#print axioms ChargedLedger.hChernoff
#print axioms ChargedLedger.hCnl
#print axioms ChargedLedger.hDensePack
#print axioms ChargedLedger.hTRT

end

end Erdos260
