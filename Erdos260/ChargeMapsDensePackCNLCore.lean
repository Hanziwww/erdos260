import Erdos260.ChargeClass3DensePack
import Erdos260.ChargeClass1CNL
import Erdos260.AppendixI_PackageBounds

/-!
# Class-3 (DensePack) and class-1 (clean-CNL) J.1.1 charge-map construction

This module (NEW; it edits no existing file) constructs the two J.1.1 charge maps of the
charged ledger (`Erdos260ChargedLedger.lean`) that route the **class-3 DensePack marker
mass** and the **class-1 clean-CNL Kraft tail** into their faithful phase terms:

```
densePack : ∀ ctx, Class3DensePackCharge trt.toBudget ctx     -- the J.D routing-to-marker injection
cnl       : Class1CNLChargeData trt.toBudget                  -- the L.1.2/G.35 Kraft-tail injection
```

The seven-class routing `(budget ctx).route` is **free** data owned by the sibling J.1.1
priority-routing worker; this module takes it as an interface and reduces both charge maps
to the *smallest* genuine routing-landing residual, discharging everything else from the
PROVEN DensePack-under-failure and clean-CNL infrastructure.

## Class 3 — DensePack (manuscript K.1 / I.4 / J.D, J.1.8)

The faithful DensePack leaf's phase term is the dense-marker point count
`termDensePack data = (data.densePack.densePackPoints.card : ℝ)`
(`AppendixI_PhaseMass.termDensePack`), and its `DensePackData` carries the PROVEN K.1.1/K.1.3
cover (`hcover`/`hcount`/`hsmall`).  This module:

* **Reduces the `hDensePack` bound to a strictly SMALLER residual** than the injection
  residual `Class3DensePackCharge`: the **count residual** `Class3DensePackCountCharge`
  (only the cardinal comparison `|routedFibre 3| ≤ termDensePack` and the J.D unit charge,
  *no explicit injection map*), via the PROVEN count×multiplier core
  `routedClassMassOf_le_countMultiplier` (unit multiplier).  `hDensePack_of_class3CountCharge`
  produces the exact `Erdos260ChargeResidual.hDensePack` field shape from it.
* **Proves the injection residual implies the count residual**
  (`Class3DensePackCharge.toCountCharge`), so the ledger's `Class3DensePackCharge` field is
  never weaker than what the bound needs.
* **Connects the class-3 fibre count to the manuscript K.1.3 bound**
  (`Class3DensePackCharge.fibreCard_le_K13`): `|routedFibre 3| ≤ c_*·X·(2 spread+1)`, by the
  injection's cardinal comparison chained with the PROVEN
  `corollaryK1_3_densePackUnderFailure` on the faithful leaf's own `DensePackData`.
* **Closes the numeric floor** `routedClassMassOf route 3 ≤ c_*·ξ·X/6` from the count residual,
  chaining the PROVEN `termDensePack_le_budget` (K.1.3 cover + K.4 smallness).
* **Constructs the ledger field** `Class3DensePackCharge` from a genuine (non-identity) marker
  landing map valued in the real `densePackPoints` (`Class3DensePackCharge.ofMarker`).

## Class 1 — clean-CNL (manuscript L.1.2 / G.35, J.1.1)

The faithful clean-CNL family is the genuinely-nonempty surviving transition family
`selectedTransitions (liftTransitionsOfShell ctx)` of `cnlLeafFromShellConcrete`.  This module:

* **Constructs the ledger field** `Class1CNLChargeData` from a charge map into that genuine
  surviving family with the per-codeword Kraft charge (reusing the proven
  `Class1CNLChargeData.ofShellCharge`); this is the genuine minimal residual (the H.1/H.2
  per-codeword bound is the orthogonal charging direction, not derivable from a phase budget).
* **Closes the numeric floor** `routedClassMassOf route 1 ≤ c_*·ξ·X/6` from the charge data,
  chaining the PROVEN `termCnl_le_budget` (the weighted-Kraft G.35 budget).
* **Records non-degeneracy** (`class1SurvivingFamily_nonempty`): the charge map targets a
  genuinely nonempty family — never an empty/degenerate stand-in.
* **Derives the uniform shell-normalization corollary**
  (`Class1CNLChargeData.windowExcess_le_shellNorm`): each class-1 start's window excess is at
  most `shellFactor·X·|I_j|`, since every Kraft weight `2^{-c·BND} ≤ 1`.

## The single residual surface

`DensePackCNLChargeData` bundles the two ledger fields; `DensePackCNLChargeData.ofData`
builds it from the smallest routing-landing data (the class-3 marker landing + the class-1
codeword charge map, with their support/injectivity/charge proofs).  This is the genuine
J.1.1 fibre/injection content — the only undischarged input, depending on the routing
interface — with no degenerate/empty shortcut.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  Class 3 — the count residual and its discharge from the proven cover

The `hDensePack` bound `routedClassMassOf route 3 ≤ termDensePack` requires, fundamentally,
only the **cardinal comparison** `|routedFibre 3| ≤ |densePackPoints| = termDensePack` (the
K.1.1 carry-side count) and the **J.D unit charge** (each routed-3 start carries window excess
`≤ 1`).  We isolate exactly these as the count residual — strictly smaller than the injection
residual `Class3DensePackCharge`, which additionally packages an explicit marker map. -/

/-- **The minimal class-3 DensePack count residual.**

For a failure context `ctx` and the shared routed budget `budget ctx`, the two genuinely
irreducible inputs of the `hDensePack` bound:

* `card_le` — the **K.1.1 carry-side count**: the class-3 fibre is at most the dense-marker
  point count `termDensePack`;
* `unit_charge` — the **J.D unit charge**: each routed-3 start carries window excess `≤ 1`.

This is strictly weaker than `Class3DensePackCharge` (no explicit injection map is carried);
`Class3DensePackCharge.toCountCharge` shows the injection residual implies it. -/
structure Class3DensePackCountCharge
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) where
  /-- **K.1.1 carry-side count** — the class-3 fibre is at most the dense-marker count. -/
  card_le : ((routedFibre ctx.n24CarryData (budget ctx).route 3).card : ℝ)
    ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData
  /-- **J.D unit charge** — each routed-3 start carries window excess `≤ 1`. -/
  unit_charge : ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ 1

namespace Class3DensePackCountCharge

variable {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    {ctx : ActualFailureContext}

/-- **The exact `Erdos260ChargeResidual.hDensePack` bound, from the count residual.**

`routedClassMassOf route 3 ≤ termDensePack (faithfulCapacityPhases budget ctx)`, derived from
the count residual via the PROVEN count×multiplier core `routedClassMassOf_le_countMultiplier`
with the J.D unit multiplier (`mult = 1`) and the K.1.1 count (`count = termDensePack`). -/
theorem routedClass3_le_termDensePack (R : Class3DensePackCountCharge budget ctx) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 3
      ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData := by
  have h := routedClassMassOf_le_countMultiplier ctx.n24CarryData (budget ctx).route 3
    R.unit_charge (by norm_num : (0 : ℝ) ≤ 1) R.card_le
  simpa only [mul_one] using h

/-- **The full class-3 numeric floor, from the count residual.**

`routedClassMassOf route 3 ≤ c_*·ξ·X/6`, chaining the `hDensePack` bound with the PROVEN
DensePack-under-failure budget `termDensePack_le_budget` (K.1.3 cover + K.4 smallness). -/
theorem routedClass3_le_budget (R : Class3DensePackCountCharge budget ctx) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 3
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  R.routedClass3_le_termDensePack.trans
    (termDensePack_le_budget (faithfulCapacityPhases budget ctx).toClosurePhaseData)

end Class3DensePackCountCharge

/-- **The injection residual implies the count residual.**

A `Class3DensePackCharge` (the ledger's marker-injection field) yields the smaller count
residual: its `fibreCard_le_markerCard` (the K.1.1 cardinal comparison, derived from the
injection) supplies `card_le`, and its `unit_charge` carries over verbatim. -/
def Class3DensePackCharge.toCountCharge
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    {ctx : ActualFailureContext} (charge : Class3DensePackCharge budget ctx) :
    Class3DensePackCountCharge budget ctx where
  card_le := by
    have h : ((routedFibre ctx.n24CarryData (budget ctx).route 3).card : ℝ)
        ≤ ((faithfulCapacityPhases budget ctx).toClosurePhaseData.densePack.densePackPoints.card : ℝ) := by
      exact_mod_cast charge.fibreCard_le_markerCard
    simpa only [termDensePack] using h
  unit_charge := charge.unit_charge

/-- **The class-3 fibre count obeys the manuscript K.1.3 bound** `|routedFibre 3| ≤
c_*·X·(2 spread+1)`.

The injection's cardinal comparison `|routedFibre 3| ≤ |densePackPoints|`
(`fibreCard_le_markerCard`) chained with the PROVEN K.1.3 cover under failure
`corollaryK1_3_densePackUnderFailure`, applied to the faithful leaf's own `DensePackData`
(`hcover`/`hcount`).  This exhibits the genuine reuse of the proven DensePack-under-failure
output bound on the carry side. -/
theorem Class3DensePackCharge.fibreCard_le_K13
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    {ctx : ActualFailureContext} (charge : Class3DensePackCharge budget ctx) :
    ((routedFibre ctx.n24CarryData (budget ctx).route 3).card : ℝ)
      ≤ (faithfulCapacityPhases budget ctx).toClosurePhaseData.densePack.cStarSmall
          * (ctx.shell.X : ℝ)
          * ((2 * (faithfulCapacityPhases budget ctx).toClosurePhaseData.densePack.spread + 1 : ℕ) : ℝ) := by
  have hcard : ((routedFibre ctx.n24CarryData (budget ctx).route 3).card : ℝ)
      ≤ ((faithfulCapacityPhases budget ctx).toClosurePhaseData.densePack.densePackPoints.card : ℝ) := by
    exact_mod_cast charge.fibreCard_le_markerCard
  exact hcard.trans
    (corollaryK1_3_densePackUnderFailure
      (faithfulCapacityPhases budget ctx).toClosurePhaseData.densePack.hcover
      (faithfulCapacityPhases budget ctx).toClosurePhaseData.densePack.hcount)

/-- **Construct the ledger field `Class3DensePackCharge` from a genuine marker landing map.**

The honest manuscript construction: each high-excess class-3 start `k` packs to a dense-marker
point `m k` (the J.5 dense-density geometry), distinct starts pack to distinct markers (the
K.1.1 endpoint-disjoint cover, carry side), and each carries unit window excess (J.D).  This
generalizes `Class3DensePackCharge.ofSubsetSelf` (the identity map, where the starts *are*
markers) to a genuine non-identity landing into the real `densePackPoints`. -/
def Class3DensePackCharge.ofMarker
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) (m : ℕ → ℕ)
    (hinto : ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
      m k ∈ (faithfulCapacityPhases budget ctx).toClosurePhaseData.densePack.densePackPoints)
    (hinj : ∀ x ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
      ∀ y ∈ routedFibre ctx.n24CarryData (budget ctx).route 3, m x = m y → x = y)
    (hunit : ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ 1) :
    Class3DensePackCharge budget ctx where
  markerOf := m
  maps_into := hinto
  matching := hinj
  unit_charge := hunit

/-- **The `hDensePack` field, from the per-context count-residual family.**

The exact type of the `Erdos260ChargeResidual.hDensePack` field, produced from the SMALLER
count residual (no explicit injection map).  Drop-in equivalent to `hDensePack_of_class3Charge`
but consuming the minimal carry-count data. -/
theorem hDensePack_of_class3CountCharge
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (charge : ∀ ctx : ActualFailureContext, Class3DensePackCountCharge budget ctx) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 3
        ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  fun ctx => (charge ctx).routedClass3_le_termDensePack

/-! ## 2.  Class 1 — the clean-CNL charge map into the genuine surviving family

The class-1 bound `routedClassMassOf route 1 ≤ termCnl` is genuinely the weighted-Kraft
charging (`Class1CNLChargeData`, closed in `ChargeClass1CNL.lean`): the per-codeword Kraft
charge is the orthogonal H.1/H.2 charging direction, not derivable from a phase budget.  Here
we add the numeric-floor close (via the proven G.35 budget), the non-degeneracy of the target
family, and the uniform shell-normalization corollary. -/

/-- **The full class-1 numeric floor, from the clean-CNL charge data.**

`routedClassMassOf route 1 ≤ c_*·ξ·X/6`, chaining the `hCnl` bound with the PROVEN clean-CNL
G.35 budget `termCnl_le_budget` (the weighted-Kraft tail `≤ 2^M·shellFactor·X·|I_j| ≤ c_*·ξ·X/6`
of `cnlLeafFromShellConcrete`). -/
theorem Class1CNLChargeData.routedClass1_le_budget
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (R : Class1CNLChargeData budget) (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 1
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (R.hCnl ctx).trans
    (termCnl_le_budget (faithfulCapacityPhases budget ctx).toClosurePhaseData
      ctx.shell.X_pos_real.le)

/-- **Non-degeneracy: the class-1 charge map targets a genuinely nonempty family.**

The faithful clean-CNL family the charge map ranges over is the surviving transition family
`selectedTransitions (liftTransitionsOfShell ctx)`, which is genuinely nonempty
(`selectedTransitions_liftTransitionsOfShell_nonempty`) — never an empty/degenerate stand-in. -/
theorem class1SurvivingFamily_nonempty
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    (faithfulCnlData budget ctx).paths.Nonempty := by
  rw [faithfulCnlData_paths]
  exact selectedTransitions_liftTransitionsOfShell_nonempty ctx

/-- **Uniform shell-normalization corollary of the per-codeword Kraft charge.**

Each class-1 start's window excess is at most `shellFactor·X·|I_j|`: the per-codeword Kraft
charge `windowExcess(k) ≤ 2^{-(c·BND(g k))}·shellFactor·X·|I_j|` holds with Kraft weight
`2^{-(c·BND)} ≤ 1` (the exponent is nonpositive since `c = 1` and the BND height is a
nonnegative `Nat` cast). -/
theorem Class1CNLChargeData.windowExcess_le_shellNorm
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (R : Class1CNLChargeData budget) (ctx : ActualFailureContext)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1) :
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ (faithfulCnlData budget ctx).shellFactor * (ctx.shell.X : ℝ)
          * (faithfulCnlData budget ctx).Ij := by
  have hexp_nonneg : 0 ≤ (faithfulCnlData budget ctx).c
      * (faithfulCnlData budget ctx).BNDHeight (R.chargeMap ctx k) := by
    simp only [faithfulCnlData_c, faithfulCnlData_BNDHeight, one_mul]
    exact Nat.cast_nonneg _
  have hE : (2 : ℝ) ^ (-((faithfulCnlData budget ctx).c
      * (faithfulCnlData budget ctx).BNDHeight (R.chargeMap ctx k))) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (neg_nonpos.mpr hexp_nonneg)
    simpa using h
  have hpos : 0 ≤ (faithfulCnlData budget ctx).shellFactor * (ctx.shell.X : ℝ)
      * (faithfulCnlData budget ctx).Ij :=
    mul_nonneg (mul_nonneg (faithfulCnlData budget ctx).shellFactor_nonneg
      ctx.shell.X_pos_real.le) (faithfulCnlData budget ctx).Ij_nonneg
  refine (R.hcharge ctx k hk).trans ?_
  calc (2 : ℝ) ^ (-((faithfulCnlData budget ctx).c
            * (faithfulCnlData budget ctx).BNDHeight (R.chargeMap ctx k)))
          * (faithfulCnlData budget ctx).shellFactor * (ctx.shell.X : ℝ)
          * (faithfulCnlData budget ctx).Ij
      = (2 : ℝ) ^ (-((faithfulCnlData budget ctx).c
            * (faithfulCnlData budget ctx).BNDHeight (R.chargeMap ctx k)))
          * ((faithfulCnlData budget ctx).shellFactor * (ctx.shell.X : ℝ)
              * (faithfulCnlData budget ctx).Ij) := by ring
    _ ≤ 1 * ((faithfulCnlData budget ctx).shellFactor * (ctx.shell.X : ℝ)
              * (faithfulCnlData budget ctx).Ij) := mul_le_mul_of_nonneg_right hE hpos
    _ = (faithfulCnlData budget ctx).shellFactor * (ctx.shell.X : ℝ)
          * (faithfulCnlData budget ctx).Ij := one_mul _

/-! ## 3.  The single DensePack+CNL charge-map residual surface

The genuine surviving J.1.1 fibre/injection content for the two classes, bundled into one
structure over the shared routed budget — the deliverable that produces both ledger fields. -/

/-- **The combined class-3 DensePack + class-1 clean-CNL charge-map residual.**

Over the shared routed budget, the two J.1.1 charge maps of the ledger:

* `densePack` — the per-context class-3 routing-to-marker injection (`Class3DensePackCharge`);
* `cnl` — the class-1 clean-CNL Kraft-tail charge injection (`Class1CNLChargeData`).

These are exactly the `ChargedLedger` fields `densePack` and `cnl`; everything downstream (the
phase-term bounds, the numeric floors) is discharged here from the proven infrastructure. -/
structure DensePackCNLChargeData
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) where
  /-- The class-3 DensePack routing-to-marker injection (per context). -/
  densePack : ∀ ctx : ActualFailureContext, Class3DensePackCharge budget ctx
  /-- The class-1 clean-CNL Kraft-tail charge injection. -/
  cnl : Class1CNLChargeData budget

namespace DensePackCNLChargeData

variable {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}

/-- **The `hDensePack` field (class 3), from the combined residual.** -/
theorem hDensePack (D : DensePackCNLChargeData budget) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 3
        ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  fun ctx => (D.densePack ctx).routedClass3_le_termDensePack

/-- **The `hCnl` field (class 1), from the combined residual.** -/
theorem hCnl (D : DensePackCNLChargeData budget) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 1
        ≤ termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  fun ctx => D.cnl.hCnl ctx

/-- **The class-3 numeric floor, from the combined residual.** -/
theorem routedClass3_le_budget (D : DensePackCNLChargeData budget) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 3
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  fun ctx => (D.densePack ctx).routedClass3_le_budget

/-- **The class-1 numeric floor, from the combined residual.** -/
theorem routedClass1_le_budget (D : DensePackCNLChargeData budget) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 1
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  fun ctx => D.cnl.routedClass1_le_budget ctx

end DensePackCNLChargeData

/-- **Build the combined charge-map residual from the smallest routing-landing data.**

The genuine J.1.1 fibre/injection content for both classes, with no degenerate/empty shortcut:

* class 3 — a per-context marker landing map `m ctx` into the real `densePackPoints`
  (`hinto`), distinct routed-3 starts to distinct markers (`hinj3`, the K.1.1 endpoint-disjoint
  cover), each carrying unit window excess (`hunit3`, J.D);
* class 1 — a per-context charge map `g ctx` into the genuinely-nonempty surviving clean-CNL
  family `selectedTransitions (liftTransitionsOfShell ctx)` (`hmem1`), injective on the class-1
  fibre (`hinj1`), with the per-codeword Kraft charge (`hcharge1`, K.1.2/L.20 at the Kraft rate
  `2^{-BND}·shellFactor·X·|I_j|`).

All of these depend on the routing interface; they are the irreducible surviving content. -/
def DensePackCNLChargeData.ofData
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (m : ∀ _ctx : ActualFailureContext, ℕ → ℕ)
    (hinto : ∀ ctx : ActualFailureContext, ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
      m ctx k ∈ (faithfulCapacityPhases budget ctx).toClosurePhaseData.densePack.densePackPoints)
    (hinj3 : ∀ ctx : ActualFailureContext, ∀ x ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
      ∀ y ∈ routedFibre ctx.n24CarryData (budget ctx).route 3, m ctx x = m ctx y → x = y)
    (hunit3 : ∀ ctx : ActualFailureContext, ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ 1)
    (g : ∀ _ctx : ActualFailureContext, ℕ → CNLTransition)
    (hmem1 : ∀ ctx : ActualFailureContext, ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
      g ctx k ∈ selectedTransitions (liftTransitionsOfShell ctx))
    (hinj1 : ∀ ctx : ActualFailureContext, ∀ k₁ ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
      ∀ k₂ ∈ routedFibre ctx.n24CarryData (budget ctx).route 1, g ctx k₁ = g ctx k₂ → k₁ = k₂)
    (hcharge1 : ∀ ctx : ActualFailureContext, ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ (2 : ℝ) ^ (-(bndHeightNatOfShell ctx (g ctx k) : ℝ))
            * (cnlShellFactorOfShell ctx : ℝ) * (ctx.shell.X : ℝ) * (cnlIjOfShell ctx : ℝ)) :
    DensePackCNLChargeData budget where
  densePack := fun ctx =>
    Class3DensePackCharge.ofMarker budget ctx (m ctx) (hinto ctx) (hinj3 ctx) (hunit3 ctx)
  cnl := Class1CNLChargeData.ofShellCharge budget g hmem1 hinj1 hcharge1

/-! ## 4.  Honest residual inventory -/

/-- The precise status of the class-3 and class-1 charge-map construction after this module. -/
def chargeMapsDensePackCNLStatus : List String :=
  [ "CLOSED (class 3, the exact hDensePack bound from the SMALLEST residual) — " ++
      "Class3DensePackCountCharge.routedClass3_le_termDensePack: routedClassMassOf route 3 ≤ " ++
      "termDensePack, from only the K.1.1 carry-side count (|routedFibre 3| ≤ termDensePack) and " ++
      "the J.D unit charge, via the PROVEN routedClassMassOf_le_countMultiplier (unit multiplier). " ++
      "Strictly smaller than the injection residual Class3DensePackCharge; " ++
      "Class3DensePackCharge.toCountCharge proves the injection residual implies it. " ++
      "hDensePack_of_class3CountCharge produces the exact Erdos260ChargeResidual.hDensePack field.",
    "CLOSED (class 3, K.1.3 connection) — Class3DensePackCharge.fibreCard_le_K13: " ++
      "|routedFibre 3| ≤ c_*·X·(2 spread+1), the injection's cardinal comparison chained with the " ++
      "PROVEN corollaryK1_3_densePackUnderFailure on the faithful leaf's own DensePackData " ++
      "(hcover/hcount). The genuine reuse of the DensePack-under-failure output bound, carry side.",
    "CLOSED (class 3, numeric floor) — Class3DensePackCountCharge.routedClass3_le_budget: " ++
      "routedClassMassOf route 3 ≤ c_*·ξ·X/6, chaining the PROVEN termDensePack_le_budget " ++
      "(K.1.3 cover + K.4 smallness; ctx.hfailure baked into the faithful DensePack leaf).",
    "CONSTRUCTED (class 3 ledger field) — Class3DensePackCharge.ofMarker: builds the ledger " ++
      "field from a genuine non-identity marker landing map into the real densePackPoints " ++
      "(generalizing ofSubsetSelf's identity map). No emptiness assumed.",
    "CLOSED (class 1, numeric floor) — Class1CNLChargeData.routedClass1_le_budget: " ++
      "routedClassMassOf route 1 ≤ c_*·ξ·X/6, chaining hCnl with the PROVEN termCnl_le_budget " ++
      "(the weighted-Kraft G.35 budget of cnlLeafFromShellConcrete).",
    "NON-DEGENERATE (class 1) — class1SurvivingFamily_nonempty: the charge map targets the " ++
      "genuinely nonempty surviving family selectedTransitions (liftTransitionsOfShell ctx); " ++
      "Class1CNLChargeData.windowExcess_le_shellNorm: each class-1 window excess ≤ shellFactor·X·|I_j| " ++
      "(every Kraft weight 2^{-c·BND} ≤ 1).",
    "CONSTRUCTED (both ledger fields) — DensePackCNLChargeData.ofData: builds the combined " ++
      "residual (densePack : ∀ ctx, Class3DensePackCharge budget ctx; cnl : Class1CNLChargeData " ++
      "budget) from the smallest routing-landing data (class-3 marker landing + class-1 codeword " ++
      "charge map, with support/injectivity/charge). Reuses ofMarker and the proven ofShellCharge.",
    "MINIMAL RESIDUAL (the J.1.1 fibre/injection, depends on the routing interface) — the four " ++
      "class-3 inputs (m/hinto/hinj3/hunit3) and four class-1 inputs (g/hmem1/hinj1/hcharge1) of " ++
      "ofData. The seven-class routing (budget ctx).route is FREE data owned by the sibling J.1.1 " ++
      "routing worker, so the carry↔marker and carry↔codeword landings are genuinely undischarged " ++
      "here; they are the deep J.1.1/J.D/H.1-H.2 charging content. No degenerate/empty shortcut." ]

theorem chargeMapsDensePackCNLStatus_nonempty : chargeMapsDensePackCNLStatus ≠ [] := by
  simp [chargeMapsDensePackCNLStatus]

/-! ## 5.  Axiom-cleanliness audit -/

#print axioms Class3DensePackCountCharge.routedClass3_le_termDensePack
#print axioms Class3DensePackCountCharge.routedClass3_le_budget
#print axioms Class3DensePackCharge.toCountCharge
#print axioms Class3DensePackCharge.fibreCard_le_K13
#print axioms Class3DensePackCharge.ofMarker
#print axioms hDensePack_of_class3CountCharge
#print axioms Class1CNLChargeData.routedClass1_le_budget
#print axioms class1SurvivingFamily_nonempty
#print axioms Class1CNLChargeData.windowExcess_le_shellNorm
#print axioms DensePackCNLChargeData.hDensePack
#print axioms DensePackCNLChargeData.hCnl
#print axioms DensePackCNLChargeData.ofData

end

end Erdos260
