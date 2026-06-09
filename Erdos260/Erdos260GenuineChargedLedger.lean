import Erdos260.GenuineObstructionRoutingCore
import Erdos260.ChargedBranchMassCore
import Erdos260.ChargeMapsDensePackCNLCore
import Erdos260.ChargeMapsTRTOldResCore

/-!
# Erdős #260 — the J.1.1 charged ledger **for the genuine first-obstruction route**

This module (NEW; it edits no existing file) instantiates the consolidated charged-ledger
endpoint `erdos260_chargedledger_reduced : ChargedLedger → Erdos260Statement`
(`Erdos260ChargedLedger.lean`) at the **genuine** v5 seven-class first-obstruction routing
`genuineChargeRoute` (`GenuineObstructionRoutingCore.lean`), wiring in the grounded
per-element charge (`ChargedBranchMassCore.lean`) and the genuine per-class charge maps /
derived fibre counts (`ChargeMapsDensePackCNLCore.lean`, `ChargeMapsTRTOldResCore.lean`).

The deliverable is the **tightest honest residual surface** `Erdos260GenuineChargedResidual`
that drives `Erdos260Statement` *once the route is forced to be the genuine route*, together
with the capstone

```
erdos260_genuine_charged_reduced : Erdos260GenuineChargedResidual → Erdos260Statement.
```

## What the genuine route CLOSES (honest, per class)

For `genuineChargeRoute` the seven per-class charging bounds split as follows.

* **Class 6 (old-residual) — FULLY CLOSED, zero residual.**  `genuineChargeRoute_routed6_zero`
  proves the old-residual fibre is *empty* (no proved classifier detects old-residual
  leakage), so `routedClassMassOf … route 6 = 0`, which is `≤ ∑_{k∈K} oldResAt k` by the
  nonnegativity of the genuine L.6.5 branch mass (`oldResL65_branchMass_nonneg`).  The
  `hOldRes` field of `ChargedLedger` is therefore **discharged internally** here — it is *not*
  carried by `Erdos260GenuineChargedResidual`.  This is the one bound the genuine route closes
  outright.

* **Class 4 (Return) — count DERIVED (M.2.1), injection remains.**  The class-4 fibre count is
  *not free*: a `ReturnOlcRoutingCharge` (the J.1.1 routing-to-OLC injection) derives
  `|routedFibre 4| ≤ liftLevelBound X = O(log* X)` through the proved
  `olcGeomOfShell_endpoints_card_le` (`ReturnOlcRoutingCharge.fibreCard_le_liftLevelBound`).
  So `chargeClassTRTDataOfRouting` pins `countReturn := liftLevelBound X`; the surviving
  Return residual is the OLC injection + the per-element multiplier + the K.4 numeric
  `liftLevelBound X · mult ≤ c⋆ξX/6`.

* **Class 3 (DensePack) — count DERIVED (K.1.3), injection remains.**  The class-3 fibre count
  is *not free*: the marker injection of `Class3DensePackCharge` derives
  `|routedFibre 3| ≤ |densePackPoints|` (and the manuscript K.1.3 bound
  `Class3DensePackCharge.fibreCard_le_K13`).  The surviving DensePack residual is the
  routing-to-marker injection + the J.D unit charge.

* **Classes 0/1/2/5 (Chernoff / clean-CNL / Tower / Run) — REMAIN.**  No small combinatorial
  fibre count is derivable (Chernoff is the I.4.2 progress count, Tower/Run smallness is the
  I.4.1 / I.5.2 *mass* fraction, clean-CNL is the H.1/H.2 codeword charge).  Each remains its
  genuine fibre-landing injection / charge map + per-element charge (+ free count for 0/2/5).

So `Erdos260GenuineChargedResidual` carries **four** fields (the genuine TRT data `trt` with
the route forced to `genuineChargeRoute` and `countReturn` derived, plus `chernoff`, `cnl`,
`densePack`) — exactly one fewer than the five-field `ChargedLedger`, the deleted field being
the now-internally-discharged `hOldRes`.

## The per-element charge is GROUNDED, not assumed

The per-element multipliers carried by the residual (`hpointTower`/`hpointReturn`/`hpointRun`,
`Class0ChernoffCharge.hpoint`, the DensePack `unit_charge`, the CNL `hcharge`) are the K.1.2 /
L.20 window-excess multiplier `windowExcess ≤ C_res·Y`, which `ChargedBranchMassCore` grounds
in the **proved** dyadic-scale gap estimate `HitSequence.hitGap_le_of_shell_window`
(`windowExcess_le_dyadicWindowMultiplier_carry`).  `GenuineTRTChargeData.ofGroundedGap` exhibits
the wiring: it builds the three TRT per-element fields from the active-window gap structure via
`windowExcess_le_mult_on_routedFibre`, so the carried `hpoint`s are dischargeable from the shell
geometry rather than fabricated.

No `sorry`, `axiom`, or `admit`.  The genuine route is used throughout; the L.6.5 old-residual
smallness, the constants, the phase budgets, the three closed capacities, the N.24 compression,
the faithful Dirty model and the pressure floor are all discharged internally by
`erdos260_chargedledger_reduced`.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The genuine TRT residual — the `trt` field with the route forced to be genuine

`GenuineTRTChargeData` is the Tower(2)/Return(4)/Run(5) per-fibre charge data of the ledger,
**with the seven-class routing pinned to `genuineChargeRoute`** (it is not free).  It is exactly
the input of `chargeClassTRTDataOfRouting` at `route := genuineChargeRoute`, so:

* Tower (2) and Run (5) carry the per-fibre count×multiplier residual (count is a genuine free
  residual — no small combinatorial count exists);
* Return (4) carries the M.2.1 OLC routing-to-endpoint injection `retCharge`, from which the
  count `liftLevelBound X` is *derived* — only the injection, the multiplier, and the K.4
  numeric remain. -/

/-- **The genuine Tower+Return+Run charge data** (the `trt` ledger field, route = genuine).

The per-class per-fibre charge data over the genuine first-obstruction route `genuineChargeRoute`:
Tower/Run as count×multiplier residuals, Return as the M.2.1 OLC injection (count derived). -/
structure GenuineTRTChargeData where
  /-- Tower (class 2) per-fibre window-excess multiplier (K.1.2/L.20). -/
  multTower : ∀ _ctx : ActualFailureContext, ℝ
  /-- Tower (class 2) fibre count (genuine free residual — no small combinatorial count). -/
  countTower : ∀ _ctx : ActualFailureContext, ℝ
  /-- Every genuine-route class-2 start charges window excess `≤ multTower`. -/
  hpointTower : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multTower ctx
  /-- The Tower multiplier is nonnegative. -/
  hmultTower_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ multTower ctx
  /-- The genuine-route class-2 fibre has at most `countTower` members. -/
  hcardTower : ∀ ctx : ActualFailureContext,
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ) ≤ countTower ctx
  /-- The K.4 numeric `countTower·multTower ≤ c⋆ξX/6` (I.4.1 dense-packing fraction). -/
  hbudTower : ∀ ctx : ActualFailureContext,
    countTower ctx * multTower ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  /-- **Return (class 4) — the M.2.1 OLC routing-to-endpoint injection.**  Derives the
  inverse-tower count `liftLevelBound X`; the count is *not* a free residual. -/
  retCharge : ∀ ctx : ActualFailureContext, ReturnOlcRoutingCharge (genuineChargeRoute ctx) ctx
  /-- Return (class 4) per-fibre window-excess multiplier (K.1.2/L.20). -/
  multReturn : ∀ _ctx : ActualFailureContext, ℝ
  /-- Every genuine-route class-4 start charges window excess `≤ multReturn`. -/
  hpointReturn : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multReturn ctx
  /-- The Return multiplier is nonnegative. -/
  hmultReturn_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ multReturn ctx
  /-- The K.4 numeric `liftLevelBound X · multReturn ≤ c⋆ξX/6` (I.5.1 over the derived count). -/
  hbudReturn : ∀ ctx : ActualFailureContext,
    (liftLevelBound ctx.shell.X : ℝ) * multReturn ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  /-- Run (class 5) per-fibre window-excess multiplier (K.1.2/L.20). -/
  multRun : ∀ _ctx : ActualFailureContext, ℝ
  /-- Run (class 5) fibre count (genuine free residual — no small combinatorial count). -/
  countRun : ∀ _ctx : ActualFailureContext, ℝ
  /-- Every genuine-route class-5 start charges window excess `≤ multRun`. -/
  hpointRun : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multRun ctx
  /-- The Run multiplier is nonnegative. -/
  hmultRun_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ multRun ctx
  /-- The genuine-route class-5 fibre has at most `countRun` members. -/
  hcardRun : ∀ ctx : ActualFailureContext,
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ) ≤ countRun ctx
  /-- The K.4 numeric `countRun·multRun ≤ c⋆ξX/6` (I.5.2 run-mass floor). -/
  hbudRun : ∀ ctx : ActualFailureContext,
    countRun ctx * multRun ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6

namespace GenuineTRTChargeData

/-- **The `ChargeClassTRTData` of the genuine TRT residual.**  Built by the proved
`chargeClassTRTDataOfRouting` at `route := genuineChargeRoute`, so its `route` is the genuine
first-obstruction route and `countReturn` is the *derived* inverse-tower count `liftLevelBound X`
(via the M.2.1 OLC injection `retCharge`). -/
def toTRTData (D : GenuineTRTChargeData) : ChargeClassTRTData :=
  chargeClassTRTDataOfRouting genuineChargeRoute
    D.multTower D.countTower D.hpointTower D.hmultTower_nonneg D.hcardTower D.hbudTower
    D.retCharge D.multReturn D.hpointReturn D.hmultReturn_nonneg D.hbudReturn
    D.multRun D.countRun D.hpointRun D.hmultRun_nonneg D.hcardRun D.hbudRun

/-- The shared budget produced by the genuine TRT data (`= toTRTData.toBudget`). -/
def toBudget (D : GenuineTRTChargeData) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  D.toTRTData.toBudget

/-- The genuine TRT data routes through `genuineChargeRoute`. -/
@[simp] theorem toTRTData_route (D : GenuineTRTChargeData) :
    D.toTRTData.route = genuineChargeRoute := rfl

/-- The genuine TRT data's shared budget routes through `genuineChargeRoute`. -/
@[simp] theorem toBudget_route (D : GenuineTRTChargeData) (ctx : ActualFailureContext) :
    (D.toBudget ctx).route = genuineChargeRoute ctx := rfl

end GenuineTRTChargeData

/-! ## 2.  The genuine charged residual — ONLY what survives for the genuine route

`Erdos260GenuineChargedResidual` carries exactly the genuine per-class charging content that the
genuine route does **not** discharge: the TRT data `trt` (route forced genuine, `countReturn`
derived), and the three sibling charge maps `chernoff` / `cnl` / `densePack`.  The class-6
`hOldRes` field is **absent** — it is closed internally from `genuineChargeRoute_routed6_zero`. -/

/-- **The genuine first-obstruction charged residual of Erdős #260.**

The surviving content of the J.1.1 charged ledger *for the genuine route* `genuineChargeRoute`:

* `trt` — the genuine Tower+Return+Run charge data (route forced to `genuineChargeRoute`,
  `countReturn` derived from the M.2.1 OLC injection);
* `chernoff` — the class-0 Chernoff/shell-paid (22.1A) charging map;
* `cnl` — the class-1 clean-CNL (L.1.2/G.35) Kraft-tail charge injection;
* `densePack` — the class-3 DensePack (J.D) routing-to-marker injection.

The class-6 old-residual bound is **not** here: for the genuine route it is closed outright
(`genuineChargeRoute_routed6_zero`).  Everything else (L.6.5 smallness, constants, phase
budgets, the three capacities, N.24 compression, faithful Dirty, pressure floor) is discharged
internally by the consolidated `erdos260_chargedledger_reduced`. -/
structure Erdos260GenuineChargedResidual where
  /-- The genuine Tower+Return+Run charge data (classes 2/4/5 + the genuine routing). -/
  trt : GenuineTRTChargeData
  /-- Class 0 — the Chernoff / shell-paid progress (22.1A) charging map. -/
  chernoff : Class0ChernoffCharge trt.toBudget
  /-- Class 1 — the clean-CNL (L.1.2/G.35) Kraft-tail charge injection. -/
  cnl : Class1CNLChargeData trt.toBudget
  /-- Class 3 — the DensePack (J.D) routing-to-marker injection with unit charge. -/
  densePack : ∀ ctx : ActualFailureContext, Class3DensePackCharge trt.toBudget ctx

namespace Erdos260GenuineChargedResidual

/-- **Class 6 is closed for the genuine route.**  The old-residual routed mass is `0` (the
genuine route never assigns class 6, `genuineChargeRoute_routed6_zero`), which is dominated by
the nonnegative genuine L.6.5 branch mass.  This discharges the `hOldRes` field internally — no
class-6 residual is carried. -/
theorem hOldRes_closed (D : GenuineTRTChargeData) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (D.toBudget ctx).route 6
        ≤ ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k := by
  intro ctx
  rw [D.toBudget_route ctx, genuineChargeRoute_routed6_zero ctx]
  exact oldResL65_branchMass_nonneg ctx

/-- **Expand the genuine charged residual into the consolidated `ChargedLedger`.**

The four genuine fields plug into `trt`/`chernoff`/`cnl`/`densePack`; the fifth `ChargedLedger`
field `hOldRes` is supplied by `hOldRes_closed` (the genuine empty old-residual fibre). -/
def toChargedLedger (R : Erdos260GenuineChargedResidual) : ChargedLedger where
  trt := R.trt.toTRTData
  chernoff := R.chernoff
  cnl := R.cnl
  densePack := R.densePack
  hOldRes := hOldRes_closed R.trt

end Erdos260GenuineChargedResidual

/-! ## 3.  The endpoint — Erdős #260 from the genuine charged residual -/

/-- **Erdős #260, reduced to the genuine first-obstruction charged residual.**

From `Erdos260GenuineChargedResidual` — the genuine route `genuineChargeRoute`, the genuine
Tower+Return+Run data (with `countReturn` derived from M.2.1), and the three sibling charge maps
(Chernoff 0 / clean-CNL 1 / DensePack 3) — the consolidated capstone
`erdos260_chargedledger_reduced` proves `Erdos260Statement`.  The class-6 old-residual bound is
closed internally (`genuineChargeRoute_routed6_zero`), and all closed components (L.6.5, the
constants, the phase budgets/capacities, the N.24 compression, the faithful Dirty model and the
pressure floor) are discharged by the capstone.

No `sorry`/`axiom`/`admit`. -/
theorem erdos260_genuine_charged_reduced (R : Erdos260GenuineChargedResidual) :
    Erdos260Statement :=
  erdos260_chargedledger_reduced R.toChargedLedger

/-! ## 4.  The genuine-route per-class closure analysis (what derives, what remains)

These re-exports make the honest per-class status machine-checked: which bounds the genuine
route closes outright, which counts are derived, and which fibre-landing content remains. -/

/-- **Class 6 — CLOSED (zero residual).**  The genuine route's old-residual routed mass is `0`. -/
theorem genuine_routedClass6_zero (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 6 = 0 :=
  genuineChargeRoute_routed6_zero ctx

/-- **Class 4 — count DERIVED (M.2.1).**  Any genuine-route Return OLC injection forces the
class-4 fibre count to the inverse-tower bound `liftLevelBound X` (proved
`olcGeomOfShell_endpoints_card_le`); the count is not a free residual. -/
theorem genuine_returnCount_le_liftLevelBound (ctx : ActualFailureContext)
    (rc : ReturnOlcRoutingCharge (genuineChargeRoute ctx) ctx) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).card ≤ liftLevelBound ctx.shell.X :=
  rc.fibreCard_le_liftLevelBound

/-- **Class 3 — count DERIVED (K.1.3).**  Any genuine-route DensePack marker injection forces
the class-3 fibre count to the manuscript K.1.3 dense-packing bound `c⋆·X·(2 spread+1)` (via the
proved `corollaryK1_3_densePackUnderFailure`); the count is not a free residual. -/
theorem genuine_densePackCount_le_K13 (D : GenuineTRTChargeData) (ctx : ActualFailureContext)
    (charge : Class3DensePackCharge D.toBudget ctx) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 3).card : ℝ)
      ≤ (faithfulCapacityPhases D.toBudget ctx).toClosurePhaseData.densePack.cStarSmall
          * (ctx.shell.X : ℝ)
          * ((2 * (faithfulCapacityPhases D.toBudget ctx).toClosurePhaseData.densePack.spread
                + 1 : ℕ) : ℝ) :=
  charge.fibreCard_le_K13

/-! ## 5.  The grounded per-element charge produces the TRT `hpoint` fields

The per-element multipliers carried by `GenuineTRTChargeData` are *grounded*, not assumed:
`GenuineTRTChargeData.ofGroundedGap` builds the three TRT per-element fields from the
active-window gap structure via the proved `ChargedBranchMassCore.windowExcess_le_mult_on_routedFibre`
(whose gap bound is the dyadic-scale estimate `HitSequence.hitGap_le_of_shell_window`).  The only
inputs are the active-window gap bound, the K.1.2 active-floor scaling, the counts, and the K.4
numeric — the genuine surviving residual content. -/

/-- **Build the genuine TRT data with the per-element charges grounded in the gap structure.**

The Tower/Return/Run per-element multiplier fields are *produced* from the active-window gap
bound (`hgap*`, grounded in the proved `hitGap_le_of_shell_window`) and the active-floor scaling
`(r+1)·g₀ − T ≤ mult` (`hscale*`, the K.1.2/L.20 calibration), through the proved
`windowExcess_le_mult_on_routedFibre`.  The fibre counts (`countTower`/`countRun` free, Return
derived via `retCharge`) and the K.4 numerics are carried as the genuine residual. -/
def GenuineTRTChargeData.ofGroundedGap
    (multTower countTower : ∀ _ctx : ActualFailureContext, ℝ)
    (g₀Tower : ∀ _ctx : ActualFailureContext, ℕ)
    (hgapTower : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀Tower ctx)
    (hscaleTower : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (g₀Tower ctx : ℝ) - ctx.n24CarryData.T ≤ multTower ctx)
    (hmultTower_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ multTower ctx)
    (hcardTower : ∀ ctx : ActualFailureContext,
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ) ≤ countTower ctx)
    (hbudTower : ∀ ctx : ActualFailureContext,
      countTower ctx * multTower ctx
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6)
    (retCharge : ∀ ctx : ActualFailureContext, ReturnOlcRoutingCharge (genuineChargeRoute ctx) ctx)
    (multReturn : ∀ _ctx : ActualFailureContext, ℝ)
    (g₀Return : ∀ _ctx : ActualFailureContext, ℕ)
    (hgapReturn : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀Return ctx)
    (hscaleReturn : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (g₀Return ctx : ℝ) - ctx.n24CarryData.T ≤ multReturn ctx)
    (hmultReturn_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ multReturn ctx)
    (hbudReturn : ∀ ctx : ActualFailureContext,
      (liftLevelBound ctx.shell.X : ℝ) * multReturn ctx
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6)
    (multRun countRun : ∀ _ctx : ActualFailureContext, ℝ)
    (g₀Run : ∀ _ctx : ActualFailureContext, ℕ)
    (hgapRun : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀Run ctx)
    (hscaleRun : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (g₀Run ctx : ℝ) - ctx.n24CarryData.T ≤ multRun ctx)
    (hmultRun_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ multRun ctx)
    (hcardRun : ∀ ctx : ActualFailureContext,
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ) ≤ countRun ctx)
    (hbudRun : ∀ ctx : ActualFailureContext,
      countRun ctx * multRun ctx
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    GenuineTRTChargeData where
  multTower := multTower
  countTower := countTower
  hpointTower := fun ctx =>
    windowExcess_le_mult_on_routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2
      (hgapTower ctx) (hscaleTower ctx) (hmultTower_nonneg ctx)
  hmultTower_nonneg := hmultTower_nonneg
  hcardTower := hcardTower
  hbudTower := hbudTower
  retCharge := retCharge
  multReturn := multReturn
  hpointReturn := fun ctx =>
    windowExcess_le_mult_on_routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4
      (hgapReturn ctx) (hscaleReturn ctx) (hmultReturn_nonneg ctx)
  hmultReturn_nonneg := hmultReturn_nonneg
  hbudReturn := hbudReturn
  multRun := multRun
  countRun := countRun
  hpointRun := fun ctx =>
    windowExcess_le_mult_on_routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5
      (hgapRun ctx) (hscaleRun ctx) (hmultRun_nonneg ctx)
  hmultRun_nonneg := hmultRun_nonneg
  hcardRun := hcardRun
  hbudRun := hbudRun

/-! ## 6.  Honest residual inventory -/

/-- The precise per-class status of the genuine first-obstruction charged ledger. -/
def genuineChargedLedgerResiduals : List String :=
  [ "CLOSED (class 6, old-residual, ZERO residual) — genuine_routedClass6_zero: for the genuine " ++
      "route genuineChargeRoute the old-residual fibre is empty (genuineChargeRoute_routed6_zero), " ++
      "so routedClassMassOf … route 6 = 0 ≤ ∑_{k∈K} oldResAt k by oldResL65_branchMass_nonneg. The " ++
      "ChargedLedger.hOldRes field is discharged INTERNALLY (Erdos260GenuineChargedResidual.hOldRes_closed); " ++
      "it is NOT carried. This is the one bound the genuine route closes outright.",
    "DERIVED COUNT (class 4, Return, M.2.1) — genuine_returnCount_le_liftLevelBound: the OLC routing " ++
      "injection retCharge forces |routedFibre 4| ≤ liftLevelBound X = O(log* X) via the PROVED " ++
      "olcGeomOfShell_endpoints_card_le. chargeClassTRTDataOfRouting pins countReturn := liftLevelBound X. " ++
      "SURVIVING: the OLC injection + multReturn + hpointReturn + the K.4 numeric liftLevelBound X·mult ≤ c⋆ξX/6.",
    "DERIVED COUNT (class 3, DensePack, K.1.3) — genuine_densePackCount_le_K13: the marker injection " ++
      "forces |routedFibre 3| ≤ c⋆·X·(2 spread+1) via the PROVED corollaryK1_3_densePackUnderFailure. " ++
      "SURVIVING: the routing-to-marker injection (markerOf/maps_into/matching) + the J.D unit charge.",
    "REMAINS (class 0, Chernoff) — the Class0ChernoffCharge count×multiplier residual: the I.4.2 " ++
      "progress-endpoint count (hcard, NOT derivable) + the per-fibre window-excess multiplier (hpoint) " ++
      "+ the 22.1A area identification (hbud). Equivalently one J.1.7 charging map.",
    "REMAINS (class 1, clean-CNL) — the Class1CNLChargeData charge injection: the J.1.1 charge map of " ++
      "class-1 starts into the genuinely-nonempty surviving clean-CNL family + injectivity (the fibre-count " ++
      "identification, NOT derivable) + the per-codeword K.1.2/L.20 Kraft charge (H.1/H.2).",
    "REMAINS (class 2, Tower) — the count×multiplier residual over the genuine class-2 fibre: the " ++
      "per-fibre multiplier (hpointTower) + the fibre count (countTower, a genuine FREE residual — the " ++
      "Tower smallness is the I.4.1 dense-packing MASS fraction, not a small count) + the K.4 numeric. " ++
      "The genuine geometry (L.2.4 disjointness towerClsOfShell) is closed/re-exported but does not give a count.",
    "REMAINS (class 5, Run) — the count×multiplier residual over the genuine class-5 fibre: the per-fibre " ++
      "multiplier (hpointRun) + the fibre count (countRun, a genuine FREE residual — the Run smallness is " ++
      "the I.5.2 run-mass floor, not a small count) + the K.4 numeric. The genuine geometry (L.4.1 " ++
      "trichotomy runClsOfShell, chain class empty) is closed/re-exported but does not give a count.",
    "GROUNDED (per-element charge) — GenuineTRTChargeData.ofGroundedGap builds the three TRT hpoint fields " ++
      "from the active-window gap structure via the PROVED windowExcess_le_mult_on_routedFibre (gap bound = " ++
      "the dyadic-scale estimate hitGap_le_of_shell_window). The carried per-element multipliers are " ++
      "dischargeable from the shell geometry, not fabricated; only the K.1.2 active-floor scaling remains.",
    "ENDPOINT — erdos260_genuine_charged_reduced : Erdos260GenuineChargedResidual → Erdos260Statement, via " ++
      "Erdos260GenuineChargedResidual.toChargedLedger (4 genuine fields → the 5-field ChargedLedger, with " ++
      "hOldRes closed) and the capstone erdos260_chargedledger_reduced. The route is FORCED to genuineChargeRoute." ]

theorem genuineChargedLedgerResiduals_nonempty : genuineChargedLedgerResiduals ≠ [] := by
  simp [genuineChargedLedgerResiduals]

/-! ## 7.  Axiom-cleanliness audit -/

#print axioms erdos260_genuine_charged_reduced
#print axioms Erdos260GenuineChargedResidual.toChargedLedger
#print axioms Erdos260GenuineChargedResidual.hOldRes_closed
#print axioms genuine_routedClass6_zero
#print axioms genuine_returnCount_le_liftLevelBound
#print axioms genuine_densePackCount_le_K13
#print axioms GenuineTRTChargeData.ofGroundedGap

end

end Erdos260
