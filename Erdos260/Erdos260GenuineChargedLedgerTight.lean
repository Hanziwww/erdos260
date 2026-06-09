import Erdos260.Erdos260GenuineChargedLedger
import Erdos260.DensePackInjectionCore
import Erdos260.ReturnInjectionCore

/-!
# Erdős #260 — the TIGHTEST genuine first-obstruction charged-ledger endpoint

This module (NEW; it edits no existing file) wires the two **wave-7 fibre-landing injection
reductions** into the genuine charged-ledger endpoint
`erdos260_genuine_charged_reduced : Erdos260GenuineChargedResidual → Erdos260Statement`
(`Erdos260GenuineChargedLedger.lean`), producing a strictly tighter endpoint

```
erdos260_genuine_charged_reduced_tight : Erdos260GenuineChargedResidualTight → Erdos260Statement.
```

Two of the four `Erdos260GenuineChargedResidual` fields are replaced by their **smaller landing
residuals**, leaving the other two (and the genuinely-free Tower/Run counts) exactly as before.

## What shrank (wave-7) vs. what is unchanged

* **DensePack (class 3) — SHRUNK.**  The wave-6 ledger carried the *full*
  `densePack : ∀ ctx, Class3DensePackCharge trt.toBudget ctx` (the marker injection **plus** the
  J.D unit charge).  The tight residual carries instead only the
  `GenuineDensePackLanding trt.toBudget ctx` marker-landing residual (`markerOf`/`lands`/
  `endpointInj` — the J.5/J.D/K.1.1 classifier↔marker geometry) plus the active-window gap
  structure (`densePackG0`/`densePackGap`/`densePackScale`); the J.D unit charge is then
  **discharged** (not assumed) through `densePackChargeFamily` (via the proved
  `windowExcess_le_one_on_routedFibre`).

* **Return (class 4) — SHRUNK.**  The wave-6 ledger carried an opaque
  `retCharge : ∀ ctx, ReturnOlcRoutingCharge (genuineChargeRoute ctx) ctx` inside its `trt` field.
  The tight residual carries instead only the M.2.1 **self-referential lift-chain level
  assignment** (`retLevel`/`retBound`/`retChain`/`retInj` — the `ofLiftChainLevels` inputs); the
  full `ReturnOlcRoutingCharge` is then **built** through `genuineReturnOlcRoutingCharge`
  (`ReturnOlcRoutingCharge.ofLiftChainLevels`, via the proved `IsLiftChain.card_le`).

* **Chernoff (class 0) / clean-CNL (class 1) — UNCHANGED.**  `Class0ChernoffCharge` (I.4.2 progress
  count + 22.1A charge) and `Class1CNLChargeData` (H.1/H.2 Kraft codeword charge) are carried
  verbatim against the same budget — no small combinatorial count is derivable for them.

* **Tower (class 2) / Run (class 5) free counts — UNCHANGED.**  `countTower`/`countRun` remain the
  genuine *free* residual mass-fraction counts (the I.4.1 dense-packing fraction / the I.5.2
  run-mass floor — mass bounds, not small counts), carried as before with their per-fibre
  multipliers and K.4 numerics.

## How the endpoint is proved

`Erdos260GenuineChargedResidualTight.toResidual` rebuilds the wave-6
`Erdos260GenuineChargedResidual` from the tight data by feeding the two landing residuals through
the proved wave-7 builders:

* the lift-chain levels → `genuineReturnOlcRoutingCharge` → the `retCharge` field of
  `GenuineTRTChargeData` (so `countReturn = liftLevelBound X` is still *derived* downstream);
* the marker-landing family + gap structure → `densePackChargeFamily` → the
  `∀ ctx, Class3DensePackCharge trt.toBudget ctx` ledger field.

The endpoint is then `erdos260_genuine_charged_reduced` applied to the rebuilt residual — so no
protected endpoint is weakened, and nothing new is fabricated.

The budget used for the Chernoff/CNL/DensePack fields is `trt.toBudget` (the genuine route packaged
with its three routed-fraction slot bounds **derived** from the Tower/Return/Run charge data), not
a `genuineBudget` taking those slot bounds as free hypotheses — i.e. the tight residual does *not*
assume the routed-fraction budgets, it derives them, exactly as the wave-6 ledger does.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The tight genuine TRT charge data — Return shrunk to the M.2.1 lift-chain levels

`GenuineTRTChargeDataTight` is `GenuineTRTChargeData` with its opaque `retCharge` field replaced by
the **smallest honest Return residual**: the self-referential lift-chain level assignment
(`retLevel`/`retBound`/`retChain`/`retInj`, the `ReturnOlcRoutingCharge.ofLiftChainLevels` inputs).
Tower (2) and Run (5) keep their free count×multiplier residuals verbatim. -/

/-- **The tight genuine Tower+Return+Run charge data.**

Identical to `GenuineTRTChargeData` except the Return (class 4) OLC injection is replaced by its
landing residual: the M.2.1 self-referential nesting-level assignment of the long-return starts. -/
structure GenuineTRTChargeDataTight where
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
  /-- **Return (class 4) — the M.2.1 self-referential nesting-level assignment** of the long-return
  starts (the `ReturnOlcRoutingCharge.ofLiftChainLevels` level map). -/
  retLevel : ∀ _ctx : ActualFailureContext, ℕ → ℕ
  /-- **M.2.1 shell-scale bound** — every class-4 start's nesting level sits below the shell `X`. -/
  retBound : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4, retLevel ctx k ≤ ctx.shell.X
  /-- **M.2.1 self-referential lift congruence** — `level x + 2^(level x) ≤ level y` whenever
  `level x < level y` (proof_v4 §J.4 / K.2.4–K.2.5: nonseparated nested refinements jump by
  `≥ 2^{δ_i}`). -/
  retChain : ∀ ctx : ActualFailureContext,
    ∀ x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      ∀ y ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
        retLevel ctx x < retLevel ctx y → retLevel ctx x + 2 ^ retLevel ctx x ≤ retLevel ctx y
  /-- **M.2.1 endpoint disjointness** — distinct class-4 starts receive distinct nesting levels. -/
  retInj : ∀ ctx : ActualFailureContext,
    ∀ x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      ∀ y ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
        retLevel ctx x = retLevel ctx y → x = y
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

namespace GenuineTRTChargeDataTight

/-- **The Return OLC routing charge, BUILT from the lift-chain levels.**  Through the proved
`genuineReturnOlcRoutingCharge` (`ReturnOlcRoutingCharge.ofLiftChainLevels`), the M.2.1 level
assignment produces the full `ReturnOlcRoutingCharge` for the genuine route — so the downstream
inverse-tower count `liftLevelBound X` is still derived. -/
def retCharge (D : GenuineTRTChargeDataTight) :
    ∀ ctx : ActualFailureContext, ReturnOlcRoutingCharge (genuineChargeRoute ctx) ctx :=
  fun ctx =>
    genuineReturnOlcRoutingCharge ctx (D.retLevel ctx) (D.retBound ctx) (D.retChain ctx)
      (D.retInj ctx)

/-- **Expand the tight TRT data into the wave-6 `GenuineTRTChargeData`.**  The Tower/Run/Return
multiplier data is carried verbatim; the `retCharge` field is supplied by `retCharge` (the M.2.1
lift-chain build). -/
def toGenuineTRT (D : GenuineTRTChargeDataTight) : GenuineTRTChargeData where
  multTower := D.multTower
  countTower := D.countTower
  hpointTower := D.hpointTower
  hmultTower_nonneg := D.hmultTower_nonneg
  hcardTower := D.hcardTower
  hbudTower := D.hbudTower
  retCharge := D.retCharge
  multReturn := D.multReturn
  hpointReturn := D.hpointReturn
  hmultReturn_nonneg := D.hmultReturn_nonneg
  hbudReturn := D.hbudReturn
  multRun := D.multRun
  countRun := D.countRun
  hpointRun := D.hpointRun
  hmultRun_nonneg := D.hmultRun_nonneg
  hcardRun := D.hcardRun
  hbudRun := D.hbudRun

/-- The shared budget produced by the tight TRT data (`= toGenuineTRT.toBudget`). -/
def toBudget (D : GenuineTRTChargeDataTight) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  D.toGenuineTRT.toBudget

/-- The tight TRT data's shared budget routes through `genuineChargeRoute`. -/
@[simp] theorem toBudget_route (D : GenuineTRTChargeDataTight) (ctx : ActualFailureContext) :
    (D.toBudget ctx).route = genuineChargeRoute ctx := rfl

end GenuineTRTChargeDataTight

/-! ## 2.  The tightest genuine charged residual

`Erdos260GenuineChargedResidualTight` carries the tight TRT data (Return = lift-chain levels), the
unchanged Chernoff/CNL charge maps, and the DensePack **landing** residual (`GenuineDensePackLanding`
+ active-window gap structure) in place of the full class-3 charge. -/

/-- **The tightest genuine first-obstruction charged residual of Erdős #260.**

The wave-6 `Erdos260GenuineChargedResidual` with its two largest fields replaced by their
fibre-landing residuals:

* `trt` — the tight Tower+Return+Run data: Return reduced to the M.2.1 lift-chain levels
  (`ReturnOlcRoutingCharge.ofLiftChainLevels` inputs), Tower/Run free counts unchanged;
* `chernoff` / `cnl` — the class-0 Chernoff and class-1 clean-CNL charge maps, **unchanged**;
* `densePackLanding` — the class-3 DensePack **marker-landing** residual `GenuineDensePackLanding`
  (J.5/J.D/K.1.1), in place of the full `Class3DensePackCharge`;
* `densePackG0` / `densePackGap` / `densePackScale` — the active-window gap structure from which the
  J.D unit charge is discharged. -/
structure Erdos260GenuineChargedResidualTight where
  /-- The tight Tower+Return+Run charge data (Return = M.2.1 lift-chain levels). -/
  trt : GenuineTRTChargeDataTight
  /-- Class 0 — the Chernoff / shell-paid progress (22.1A) charging map (UNCHANGED). -/
  chernoff : Class0ChernoffCharge trt.toBudget
  /-- Class 1 — the clean-CNL (L.1.2/G.35) Kraft-tail charge injection (UNCHANGED). -/
  cnl : Class1CNLChargeData trt.toBudget
  /-- **Class 3 — the DensePack J.5/J.D/K.1.1 marker-landing residual** (SHRUNK): the marker map
  `markerOf` with support into `densePackPoints` (`lands`) and the endpoint-disjoint injectivity
  (`endpointInj`), phrased on the genuine classifier condition `towerClsOfShell · = densePack`. -/
  densePackLanding : ∀ ctx : ActualFailureContext, GenuineDensePackLanding trt.toBudget ctx
  /-- The active-window gap ceiling on the class-3 descent window (for the J.D unit charge). -/
  densePackG0 : ActualFailureContext → ℕ
  /-- The active-window gap bound on the class-3 descent window. -/
  densePackGap : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (trt.toBudget ctx).route 3,
      ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ densePackG0 ctx
  /-- The K.1.2 active-floor scaling giving the J.D unit charge `windowExcess ≤ 1`. -/
  densePackScale : ∀ ctx : ActualFailureContext,
    ((ctx.n24CarryData.r : ℝ) + 1) * (densePackG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1

namespace Erdos260GenuineChargedResidualTight

/-- **The class-3 DensePack charge family, BUILT from the marker landing + gap structure.**  The
proved `densePackChargeFamily` turns the `GenuineDensePackLanding` marker injection and the
active-window gap structure into the full `∀ ctx, Class3DensePackCharge trt.toBudget ctx` ledger
field (discharging the J.D unit charge via `windowExcess_le_one_on_routedFibre`). -/
def densePackCharge (R : Erdos260GenuineChargedResidualTight) :
    ∀ ctx : ActualFailureContext, Class3DensePackCharge R.trt.toBudget ctx :=
  densePackChargeFamily R.trt.toBudget (fun _ctx => rfl)
    R.densePackLanding R.densePackG0 R.densePackGap R.densePackScale

/-- **Expand the tight residual into the wave-6 `Erdos260GenuineChargedResidual`.**  The Chernoff
and CNL fields are carried verbatim; the Return charge is built from the lift-chain levels (inside
`trt.toGenuineTRT`) and the DensePack charge from the marker landing (via `densePackCharge`). -/
def toResidual (R : Erdos260GenuineChargedResidualTight) : Erdos260GenuineChargedResidual where
  trt := R.trt.toGenuineTRT
  chernoff := R.chernoff
  cnl := R.cnl
  densePack := R.densePackCharge

end Erdos260GenuineChargedResidualTight

/-! ## 3.  The tightest endpoint — Erdős #260 from the tight genuine charged residual -/

/-- **Erdős #260, reduced to the TIGHTEST genuine first-obstruction charged residual.**

From `Erdos260GenuineChargedResidualTight` — the genuine route `genuineChargeRoute`, the tight
Tower+Return+Run data (Return = M.2.1 lift-chain levels, Tower/Run free counts), the unchanged
Chernoff/CNL charge maps, and the DensePack marker-landing residual + gap structure — the wave-6
capstone `erdos260_genuine_charged_reduced` (via `toResidual`, which feeds the two landing residuals
through the proved `genuineReturnOlcRoutingCharge` / `densePackChargeFamily`) proves
`Erdos260Statement`.

This is strictly tighter than `erdos260_genuine_charged_reduced`: the DensePack field shrank from
the full `Class3DensePackCharge` to the `GenuineDensePackLanding` marker geometry, and the Return
contribution shrank from an opaque `ReturnOlcRoutingCharge` to the M.2.1 lift-chain level
assignment.  No protected endpoint is weakened.

No `sorry`/`axiom`/`admit`. -/
theorem erdos260_genuine_charged_reduced_tight (R : Erdos260GenuineChargedResidualTight) :
    Erdos260Statement :=
  erdos260_genuine_charged_reduced R.toResidual

/-! ## 4.  The genuine-route per-class closure analysis for the tight residual

These re-exports make machine-checked the fact that the two shrunk residuals still force their
derived counts: the Return lift-chain levels force the inverse-tower count, and the DensePack marker
landing forces the K.1.3 dense-packing count. -/

/-- **Class 4 — count DERIVED through the lift-chain levels.**  The Return charge built from the
tight residual's M.2.1 lift-chain level assignment forces the inverse-tower count
`|routedFibre 4| ≤ liftLevelBound X` (via the proved `fibreCard_le_liftLevelBound`). -/
theorem tight_returnCount_le_liftLevelBound (R : Erdos260GenuineChargedResidualTight)
    (ctx : ActualFailureContext) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).card ≤ liftLevelBound ctx.shell.X :=
  (R.trt.retCharge ctx).fibreCard_le_liftLevelBound

/-- **Class 3 — count DERIVED through the marker landing.**  The DensePack charge built from the
tight residual's marker landing forces the K.1.3 dense-packing count
`|densePack starts| ≤ c⋆·X·(2 spread+1)` (via the proved `corollaryK1_3_densePackUnderFailure`). -/
theorem tight_densePackCount_le_K13 (R : Erdos260GenuineChargedResidualTight)
    (ctx : ActualFailureContext) :
    ((genuineDensePackStarts ctx).card : ℝ)
      ≤ (faithfulCapacityPhases R.trt.toBudget ctx).toClosurePhaseData.densePack.cStarSmall
          * (ctx.shell.X : ℝ)
          * ((2 * (faithfulCapacityPhases R.trt.toBudget ctx).toClosurePhaseData.densePack.spread
                + 1 : ℕ) : ℝ) :=
  genuineDensePackStarts_card_le_K13 (fun _ctx => rfl) ctx (R.densePackCharge ctx)

/-! ## 5.  Honest residual inventory -/

/-- The precise per-class status of the tightest genuine charged ledger, naming what shrank. -/
def genuineChargedLedgerTightResiduals : List String :=
  [ "SHRUNK (class 3, DensePack) — the densePack field shrank from the FULL Class3DensePackCharge " ++
      "(marker injection + J.D unit charge) to the GenuineDensePackLanding marker-landing residual " ++
      "(markerOf/lands/endpointInj — the J.5/J.D/K.1.1 classifier↔marker geometry) plus the " ++
      "active-window gap structure (densePackG0/densePackGap/densePackScale). The J.D unit charge is " ++
      "DISCHARGED, not assumed, via densePackChargeFamily (windowExcess_le_one_on_routedFibre). The " ++
      "K.1.3 dense-packing count is still derived (tight_densePackCount_le_K13).",
    "SHRUNK (class 4, Return) — the trt.retCharge field shrank from an opaque ReturnOlcRoutingCharge " ++
      "to the M.2.1 self-referential lift-chain level assignment (retLevel/retBound/retChain/retInj, " ++
      "the ofLiftChainLevels inputs). The full ReturnOlcRoutingCharge is BUILT via " ++
      "genuineReturnOlcRoutingCharge (IsLiftChain.card_le), and the inverse-tower count " ++
      "liftLevelBound X is still derived (tight_returnCount_le_liftLevelBound).",
    "UNCHANGED (class 0, Chernoff) — Class0ChernoffCharge carried verbatim (I.4.2 progress count + " ++
      "per-fibre 22.1A window-excess multiplier). No small combinatorial count is derivable.",
    "UNCHANGED (class 1, clean-CNL) — Class1CNLChargeData carried verbatim (H.1/H.2 Kraft codeword " ++
      "charge map + injective fibre-count identification). No small combinatorial count is derivable.",
    "UNCHANGED (class 2/5, Tower/Run free counts) — countTower/countRun remain the genuine FREE " ++
      "residual mass-fraction counts (the I.4.1 dense-packing fraction / the I.5.2 run-mass floor — " ++
      "mass bounds, not small counts), with their per-fibre multipliers and the K.4 numerics.",
    "ENDPOINT — erdos260_genuine_charged_reduced_tight : Erdos260GenuineChargedResidualTight → " ++
      "Erdos260Statement, via Erdos260GenuineChargedResidualTight.toResidual (feeding the two landing " ++
      "residuals through genuineReturnOlcRoutingCharge / densePackChargeFamily into the wave-6 " ++
      "erdos260_genuine_charged_reduced). The route is FORCED to genuineChargeRoute; no protected " ++
      "endpoint is weakened.",
    "IRREDUCIBLE RESIDUAL — exactly the classifier↔phase-object landing geometry: for DensePack the " ++
      "J.5/J.D/K.1.1 marker landing (towerClsOfShell · = densePack starts pack injectively into " ++
      "densePackPoints), for Return the M.2.1 OLC nesting (each long-return start gets a distinct " ++
      "self-referentially-spaced lift level ≤ X), plus the Chernoff/CNL charge injections and the " ++
      "genuinely-free Tower/Run mass-fraction counts." ]

theorem genuineChargedLedgerTightResiduals_nonempty :
    genuineChargedLedgerTightResiduals ≠ [] := by
  simp [genuineChargedLedgerTightResiduals]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms erdos260_genuine_charged_reduced_tight
#print axioms GenuineTRTChargeDataTight.toGenuineTRT
#print axioms GenuineTRTChargeDataTight.retCharge
#print axioms Erdos260GenuineChargedResidualTight.densePackCharge
#print axioms Erdos260GenuineChargedResidualTight.toResidual
#print axioms tight_returnCount_le_liftLevelBound
#print axioms tight_densePackCount_le_K13

end

end Erdos260
