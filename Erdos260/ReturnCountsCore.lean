import Mathlib
import Erdos260.ReturnM2J4Core
import Erdos260.Return

/-!
# L.2.2 / M.2 / K.4 Return-dynamics residuals on the canonical OLC scales

This module attacks the **genuine return-dynamics residuals** of the Erdős #260 Return leaf — the
fields

```
retCls, retOrdinaryShort, retSemiperiodic, retNonlocalLong, retOlcReturnBudget, retHSmall
```

of `Erdos260PhaseCoresV2` (`Erdos260ReducedToCoresV2.lean`), at the proved canonical OLC scales
`retSCanonical = 2·M_L` and `retIjCanonical = 1/X` pinned in `ReturnM2J4Core.lean`.

## The genuine counting mechanism used here

The three **L.2.2** non-OLC routed-mass counts are bounded *not* by per-element charge slack but by
the **routing conservation identity** itself (`highExcessMass_eq_sum_routedClassMassOf`): for *any*
classifier `cls : ℕ → Fin 3`, the three routed masses are nonnegative and sum to the single total
high-excess carry mass

```
routedClassMassOf cls 0 + routedClassMassOf cls 1 + routedClassMassOf cls 2
  = highExcessMass (highExcessStarts …) …,
```

so each routed mass is `≤ highExcessMass …` (`routedClassMass_le_highExcess`).  This collapses all
three L.2.2 counts to the *single* manuscript dense-packing fraction
`highExcessMass … ≤ c_* · X` — which is exactly the `centralDensePack` residual already carried by
`Erdos260PhaseCoresV2` (the I.4.1/I.4.2 carry-mass budget, Lemma 21.1).  This is the faithful
"same fact, not many" collapse the manuscript predicts for the Return non-OLC counts.

## What is genuinely CLOSED (no residual)

* `returnCls` — a concrete **same-threshold priority routing** of each high-excess start by its
  window excess against the active floor `Y` (small → ordinary-short `0`, medium → semiperiodic `1`,
  large → nonlocal-long `2`), mirroring the proved `runClsOfShell` trichotomy.
* `returnOlcReturnBudget` — the **M.2 / Prop. 23.1** OLC return-slot routing, *closed outright*: at
  `c₃ = 1/ξ = 16` the slot `s·X·|I_j|` sits inside `c₃·ξ·s·X·|I_j| + smallError/4` for any
  `smallError ≥ 0`.

## What is CLOSED modulo a single named residual each

* `returnOrdinaryShort` / `returnSemiperiodic` / `returnNonlocalLong` — each routed L.2.2 mass is
  `≤ highExcessMass …` (proved) `≤ c_* · X = smallError/4` (the `densePack` residual, = the existing
  `centralDensePack` field).
* `returnHSmall` — the **K.4** four-piece smallness, reduced by `linarith` over the pinned constants
  to the single **J.4/K.2.5 inverse-tower** residual `2·M_L ≤ cStar·ξ·X/12` (`olcSlotSmall`): the OLC
  slot `2·M_L = o(X)`.  The dense-packing part `4·c_*·X ≤ cStar·ξ·X/12` is pure pinned-constant
  arithmetic (`return_four_cStarSmall_le`).

Both residuals are bundled in `ReturnCountsResidual`; from it every Return field discharges, and the
genuine `ReturnClosedI51M2J4L6PackageInputData` Return leaf is assembled (`returnLeafFromCounts`)
through the faithful `returnLeafOfShellM2J4` (M.2.1 geometry + Prop. 23.1 four-piece assembly).

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

set_option maxHeartbeats 1000000

noncomputable section

/-! ## Part A — the concrete L.2.2 same-threshold priority routing classifier -/

/-- **The L.2.2 same-threshold return priority routing classifier.**

A genuine deterministic trichotomy of each high-excess carry start `k` by its window excess relative
to the active floor `Y` (the manuscript "same threshold" `T`/`Y`):

* small excess `≤ Y`             → ordinary-short, class `0`;
* medium excess `≤ 2·Y`          → semiperiodic short non-run, class `1`;
* large excess `> 2·Y`           → nonlocal long, class `2`.

This mirrors the proved Run trichotomy `runClsOfShell` (which routes high window excess to its
local-spike class).  It is a concrete function of the *actual* shell return geometry, never free
data. -/
def returnCls (ctx : ActualFailureContext) : ℕ → Fin 3 := fun k =>
  if windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ ctx.n24CarryData.Y then (0 : Fin 3)
  else if windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ 2 * ctx.n24CarryData.Y then (1 : Fin 3)
  else (2 : Fin 3)

/-! ## Part B — the concrete K.4 per-class constants and small-error -/

/-- Ordinary-short class constant `C₁ := 0` (the whole non-OLC mass is carried in `smallError`). -/
def returnC1 (_ : ActualFailureContext) : ℝ := 0

/-- Semiperiodic class constant `C₂ := 0`. -/
def returnC2 (_ : ActualFailureContext) : ℝ := 0

/-- OLC return-slot class constant `C₃ := 16 = 1/ξ`, exactly cancelling `ξ` in the M.2 routing. -/
def returnC3 (_ : ActualFailureContext) : ℝ := 16

/-- Nonlocal-long class constant `C₄ := 0`. -/
def returnC4 (_ : ActualFailureContext) : ℝ := 0

/-- The K.4 small-error `smallError := 4·c_*·X`, so `smallError/4 = c_*·X` is exactly the
dense-packing fraction each routed L.2.2 mass is bounded by. -/
def returnSmallError (ctx : ActualFailureContext) : ℝ := 4 * manuscriptCstarSmall * (ctx.shell.X : ℝ)

/-- The total high-excess carry mass of the shell (the `centralDensePack` quantity). -/
def returnHighExcessMass (ctx : ActualFailureContext) : ℝ :=
  highExcessMass
    (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
      ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
    (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T

/-! ## Part C — pinned-constant values and the canonical scale identities -/

theorem returnXi_val : erdos260Constants.ξ = (1 : ℝ) / 16 := rfl

theorem returnCstar_val : erdos260Constants.cStar = (31 : ℝ) / 16 := rfl

theorem returnSmallError_nonneg (ctx : ActualFailureContext) : 0 ≤ returnSmallError ctx := by
  have hX : 0 ≤ (ctx.shell.X : ℝ) := ctx.shell.X_nonneg_real
  have heq : returnSmallError ctx = manuscriptCstarSmall * (ctx.shell.X : ℝ) * 4 := by
    unfold returnSmallError; ring
  rw [heq]
  exact mul_nonneg (mul_nonneg manuscriptCstarSmall_pos.le hX) (by norm_num)

/-- **The canonical OLC return scale collapses to `2·M_L`.**  `retSCanonical·X·retIjCanonical
= (2·M_L)·X·(1/X) = 2·M_L` since `X > 0`. -/
theorem retCanonScale_eq (ctx : ActualFailureContext) :
    retSCanonical ctx * (ctx.shell.X : ℝ) * retIjCanonical ctx
      = 2 * (liftLevelBound ctx.shell.X : ℝ) := by
  have hX : (ctx.shell.X : ℝ) ≠ 0 := ne_of_gt ctx.shell.X_pos_real
  show 2 * (liftLevelBound ctx.shell.X : ℝ) * (ctx.shell.X : ℝ) * (1 / (ctx.shell.X : ℝ))
      = 2 * (liftLevelBound ctx.shell.X : ℝ)
  rw [mul_one_div, mul_div_assoc, div_self hX, mul_one]

/-- The canonical block fraction is tight: `X·retIjCanonical = X·(1/X) = 1`. -/
theorem returnCanonIj_eq (ctx : ActualFailureContext) :
    (ctx.shell.X : ℝ) * retIjCanonical ctx = 1 := by
  have hX : (ctx.shell.X : ℝ) ≠ 0 := ne_of_gt ctx.shell.X_pos_real
  show (ctx.shell.X : ℝ) * (1 / (ctx.shell.X : ℝ)) = 1
  rw [mul_one_div, div_self hX]

/-- **K.4 dense-packing constant arithmetic** (pure pinned-constant inequality):
`4·c_* ≤ cStar·ξ/12`.  With the pinned values `4·(17/268435456) ≤ (31/256)/12`. -/
theorem return_four_cStarSmall_le :
    4 * manuscriptCstarSmall ≤ erdos260Constants.cStar * erdos260Constants.ξ / 12 := by
  rw [returnXi_val, returnCstar_val]
  unfold manuscriptCstarSmall manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps manuscriptXi
  norm_num

/-! ## Part D — the routing conservation collapse: each routed mass `≤ highExcessMass` -/

/-- **The L.2.2 routing collapse (PROVED, no residual).**

For the concrete classifier `returnCls`, each routed class mass is dominated by the *single* total
high-excess carry mass: the three masses are nonnegative and sum to `highExcessMass …`
(`highExcessMass_eq_sum_routedClassMassOf`), so any one of them is `≤` the total.  This is the
faithful reduction of all three manuscript counts (synchronizing-set / short-return-envelope /
return-length) to the one dense-packing fraction. -/
theorem routedClassMass_le_highExcess (ctx : ActualFailureContext) (i : Fin 3) :
    routedClassMassOf ctx.n24CarryData (returnCls ctx) i ≤ returnHighExcessMass ctx := by
  have hsum := highExcessMass_eq_sum_routedClassMassOf ctx.n24CarryData (returnCls ctx)
  unfold returnHighExcessMass
  rw [hsum]
  exact Finset.single_le_sum
    (fun j _ => routedClassMassOf_nonneg ctx.n24CarryData (returnCls ctx) j)
    (Finset.mem_univ i)

/-! ## Part E — the six Return-field obligations (per-context form) -/

/-- **`retOrdinaryShort` (closed modulo `densePack`).**  The class-`0` routed mass is
`≤ highExcessMass … ≤ c_*·X = smallError/4`. -/
theorem returnOrdinaryShort (ctx : ActualFailureContext)
    (hDP : returnHighExcessMass ctx ≤ manuscriptCstarSmall * (ctx.shell.X : ℝ)) :
    routedClassMassOf ctx.n24CarryData (returnCls ctx) 0
      ≤ returnC1 ctx * erdos260Constants.ξ * retSCanonical ctx * (ctx.shell.X : ℝ)
          * retIjCanonical ctx + returnSmallError ctx / 4 := by
  have hb : routedClassMassOf ctx.n24CarryData (returnCls ctx) 0
      ≤ manuscriptCstarSmall * (ctx.shell.X : ℝ) :=
    le_trans (routedClassMass_le_highExcess ctx 0) hDP
  have heq : returnC1 ctx * erdos260Constants.ξ * retSCanonical ctx * (ctx.shell.X : ℝ)
        * retIjCanonical ctx + returnSmallError ctx / 4 = manuscriptCstarSmall * (ctx.shell.X : ℝ) := by
    unfold returnC1 returnSmallError; ring
  rw [heq]; exact hb

/-- **`retSemiperiodic` (closed modulo `densePack`).** -/
theorem returnSemiperiodic (ctx : ActualFailureContext)
    (hDP : returnHighExcessMass ctx ≤ manuscriptCstarSmall * (ctx.shell.X : ℝ)) :
    routedClassMassOf ctx.n24CarryData (returnCls ctx) 1
      ≤ returnC2 ctx * erdos260Constants.ξ * retSCanonical ctx * (ctx.shell.X : ℝ)
          * retIjCanonical ctx + returnSmallError ctx / 4 := by
  have hb : routedClassMassOf ctx.n24CarryData (returnCls ctx) 1
      ≤ manuscriptCstarSmall * (ctx.shell.X : ℝ) :=
    le_trans (routedClassMass_le_highExcess ctx 1) hDP
  have heq : returnC2 ctx * erdos260Constants.ξ * retSCanonical ctx * (ctx.shell.X : ℝ)
        * retIjCanonical ctx + returnSmallError ctx / 4 = manuscriptCstarSmall * (ctx.shell.X : ℝ) := by
    unfold returnC2 returnSmallError; ring
  rw [heq]; exact hb

/-- **`retNonlocalLong` (closed modulo `densePack`).** -/
theorem returnNonlocalLong (ctx : ActualFailureContext)
    (hDP : returnHighExcessMass ctx ≤ manuscriptCstarSmall * (ctx.shell.X : ℝ)) :
    routedClassMassOf ctx.n24CarryData (returnCls ctx) 2
      ≤ returnC4 ctx * erdos260Constants.ξ * retSCanonical ctx * (ctx.shell.X : ℝ)
          * retIjCanonical ctx + returnSmallError ctx / 4 := by
  have hb : routedClassMassOf ctx.n24CarryData (returnCls ctx) 2
      ≤ manuscriptCstarSmall * (ctx.shell.X : ℝ) :=
    le_trans (routedClassMass_le_highExcess ctx 2) hDP
  have heq : returnC4 ctx * erdos260Constants.ξ * retSCanonical ctx * (ctx.shell.X : ℝ)
        * retIjCanonical ctx + returnSmallError ctx / 4 = manuscriptCstarSmall * (ctx.shell.X : ℝ) := by
    unfold returnC4 returnSmallError; ring
  rw [heq]; exact hb

/-- **`retOlcReturnBudget` (CLOSED, no residual).**  At `c₃ = 16 = 1/ξ` the M.2 routing reads
`s·X·|I_j| ≤ s·X·|I_j| + smallError/4`, which holds since `smallError ≥ 0`. -/
theorem returnOlcReturnBudget (ctx : ActualFailureContext) :
    retSCanonical ctx * (ctx.shell.X : ℝ) * retIjCanonical ctx
      ≤ returnC3 ctx * erdos260Constants.ξ * retSCanonical ctx * (ctx.shell.X : ℝ)
          * retIjCanonical ctx + returnSmallError ctx / 4 := by
  have hprod : returnC3 ctx * erdos260Constants.ξ * retSCanonical ctx * (ctx.shell.X : ℝ)
        * retIjCanonical ctx = retSCanonical ctx * (ctx.shell.X : ℝ) * retIjCanonical ctx := by
    unfold returnC3
    rw [returnXi_val]; ring
  have hse : 0 ≤ returnSmallError ctx / 4 := by
    have := returnSmallError_nonneg ctx; linarith
  rw [hprod]; linarith

/-- **`retHSmall` (closed modulo `olcSlotSmall`).**  The four-piece K.4 combination evaluates to
`2·M_L + 4·c_*·X` (since `(C₁+C₂+C₃+C₄)·ξ·s·X·|I_j| = 16·ξ·(2·M_L) = 2·M_L`); it is `≤ cStar·ξ·X/6`
by `linarith` from the J.4 inverse-tower residual `2·M_L ≤ cStar·ξ·X/12` and the dense-packing
arithmetic `4·c_*·X ≤ cStar·ξ·X/12`. -/
theorem returnHSmall (ctx : ActualFailureContext)
    (hML : 2 * (liftLevelBound ctx.shell.X : ℝ)
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12) :
    (returnC1 ctx + returnC2 ctx + returnC3 ctx + returnC4 ctx) * erdos260Constants.ξ
          * retSCanonical ctx * (ctx.shell.X : ℝ) * retIjCanonical ctx + returnSmallError ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  have hA := retCanonScale_eq ctx
  have hprod : (returnC1 ctx + returnC2 ctx + returnC3 ctx + returnC4 ctx) * erdos260Constants.ξ
        * retSCanonical ctx * (ctx.shell.X : ℝ) * retIjCanonical ctx
      = 2 * (liftLevelBound ctx.shell.X : ℝ) := by
    have hsum : returnC1 ctx + returnC2 ctx + returnC3 ctx + returnC4 ctx = 16 := by
      unfold returnC1 returnC2 returnC3 returnC4; norm_num
    rw [hsum, returnXi_val]
    calc (16 : ℝ) * (1 / 16) * retSCanonical ctx * (ctx.shell.X : ℝ) * retIjCanonical ctx
        = retSCanonical ctx * (ctx.shell.X : ℝ) * retIjCanonical ctx := by ring
      _ = 2 * (liftLevelBound ctx.shell.X : ℝ) := hA
  have hse : returnSmallError ctx = 4 * manuscriptCstarSmall * (ctx.shell.X : ℝ) := rfl
  have hX : 0 ≤ (ctx.shell.X : ℝ) := ctx.shell.X_nonneg_real
  have h4c : 4 * manuscriptCstarSmall * (ctx.shell.X : ℝ)
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12 := by
    calc 4 * manuscriptCstarSmall * (ctx.shell.X : ℝ)
        ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12) * (ctx.shell.X : ℝ) :=
          mul_le_mul_of_nonneg_right return_four_cStarSmall_le hX
      _ = erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12 := by ring
  rw [hprod, hse]
  linarith [hML, h4c]

/-! ## Part F — the residual bundle and the field-shaped (`∀ ctx`) discharges -/

/-- **The two genuine Return-counting residuals.**

After the conservation collapse and the canonical pinning, the entire Return leaf reduces to:

* `densePack` — the I.4.1/I.4.2 dense-packing fraction `highExcessMass … ≤ c_*·X` (identical to the
  `centralDensePack` field of `Erdos260PhaseCoresV2`; the manuscript "same fact" collision);
* `olcSlotSmall` — the J.4/K.2.5 inverse-tower smallness `2·M_L ≤ cStar·ξ·X/12` (the OLC slot is
  `o(X)`, the manuscript order-of-quantifiers choice of `X` large after all constants). -/
structure ReturnCountsResidual where
  densePack : ∀ ctx : ActualFailureContext,
    returnHighExcessMass ctx ≤ manuscriptCstarSmall * (ctx.shell.X : ℝ)
  olcSlotSmall : ∀ ctx : ActualFailureContext,
    2 * (liftLevelBound ctx.shell.X : ℝ)
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12

/-- The `retOrdinaryShort` field, discharged for all contexts from the residual bundle. -/
theorem retOrdinaryShort_field (h : ReturnCountsResidual) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (returnCls ctx) 0
        ≤ returnC1 ctx * erdos260Constants.ξ * retSCanonical ctx * (ctx.shell.X : ℝ)
            * retIjCanonical ctx + returnSmallError ctx / 4 :=
  fun ctx => returnOrdinaryShort ctx (h.densePack ctx)

/-- The `retSemiperiodic` field, discharged for all contexts from the residual bundle. -/
theorem retSemiperiodic_field (h : ReturnCountsResidual) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (returnCls ctx) 1
        ≤ returnC2 ctx * erdos260Constants.ξ * retSCanonical ctx * (ctx.shell.X : ℝ)
            * retIjCanonical ctx + returnSmallError ctx / 4 :=
  fun ctx => returnSemiperiodic ctx (h.densePack ctx)

/-- The `retNonlocalLong` field, discharged for all contexts from the residual bundle. -/
theorem retNonlocalLong_field (h : ReturnCountsResidual) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (returnCls ctx) 2
        ≤ returnC4 ctx * erdos260Constants.ξ * retSCanonical ctx * (ctx.shell.X : ℝ)
            * retIjCanonical ctx + returnSmallError ctx / 4 :=
  fun ctx => returnNonlocalLong ctx (h.densePack ctx)

/-- The `retOlcReturnBudget` field, discharged for all contexts (no residual needed). -/
theorem retOlcReturnBudget_field :
    ∀ ctx : ActualFailureContext,
      retSCanonical ctx * (ctx.shell.X : ℝ) * retIjCanonical ctx
        ≤ returnC3 ctx * erdos260Constants.ξ * retSCanonical ctx * (ctx.shell.X : ℝ)
            * retIjCanonical ctx + returnSmallError ctx / 4 :=
  fun ctx => returnOlcReturnBudget ctx

/-- The `retHSmall` field, discharged for all contexts from the residual bundle. -/
theorem retHSmall_field (h : ReturnCountsResidual) :
    ∀ ctx : ActualFailureContext,
      (returnC1 ctx + returnC2 ctx + returnC3 ctx + returnC4 ctx) * erdos260Constants.ξ
            * retSCanonical ctx * (ctx.shell.X : ℝ) * retIjCanonical ctx + returnSmallError ctx
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  fun ctx => returnHSmall ctx (h.olcSlotSmall ctx)

/-! ## Part G — capstone: the genuine Return leaf assembled from the residual bundle

Using the faithful `returnLeafOfShellM2J4` (M.2.1 nesting geometry `olcGeomOfShell` + the Prop. 23.1
four-piece assembly internalized) at the canonical scales `s = retSCanonical`, `|I_j| = retIjCanonical`,
the genuine Return separated local leaf package is built from just the two residuals. -/

/-- **The genuine Return I.5.1/M.2/J.4/L.6 leaf package, assembled from the residual bundle.**

This is the actual `ReturnClosedI51M2J4L6PackageInputData` consumed downstream by
`ActualFailureContext.leafPhases`, with the concrete classifier, K.4 constants, and canonical scales,
proved through the faithful M.2.1 + Prop. 23.1 assembly. -/
def returnLeafFromCounts (ctx : ActualFailureContext)
    (hDP : returnHighExcessMass ctx ≤ manuscriptCstarSmall * (ctx.shell.X : ℝ))
    (hML : 2 * (liftLevelBound ctx.shell.X : ℝ)
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12) :
    ReturnClosedI51M2J4L6PackageInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) :=
  returnLeafOfShellM2J4 ctx (returnCls ctx)
    (returnC1 ctx) (returnC2 ctx) (returnC3 ctx) (returnC4 ctx)
    (retSCanonical ctx) (retIjCanonical ctx) (returnSmallError ctx)
    (le_of_eq rfl)
    (le_of_eq (returnCanonIj_eq ctx).symm)
    (returnOlcReturnBudget ctx)
    (returnOrdinaryShort ctx hDP)
    (returnSemiperiodic ctx hDP)
    (returnNonlocalLong ctx hDP)
    (returnHSmall ctx hML)

/-- **The Prop. 23.1 four-piece lower-clean combination on the actual return geometry.**

Direct use of the proved `proposition23_1_returnPackagesLowerClean`: the three routed L.2.2 masses
plus the OLC return slot are bounded by `(C₁+C₂+C₃+C₄)·ξ·s·X·|I_j| + smallError`. -/
theorem returnPackagesLowerClean_ofCounts (ctx : ActualFailureContext)
    (hDP : returnHighExcessMass ctx ≤ manuscriptCstarSmall * (ctx.shell.X : ℝ)) :
    routedClassMassOf ctx.n24CarryData (returnCls ctx) 0
        + routedClassMassOf ctx.n24CarryData (returnCls ctx) 1
        + retSCanonical ctx * (ctx.shell.X : ℝ) * retIjCanonical ctx
        + routedClassMassOf ctx.n24CarryData (returnCls ctx) 2
      ≤ (returnC1 ctx + returnC2 ctx + returnC3 ctx + returnC4 ctx) * erdos260Constants.ξ
          * retSCanonical ctx * (ctx.shell.X : ℝ) * retIjCanonical ctx + returnSmallError ctx :=
  proposition23_1_returnPackagesLowerClean
    (returnOrdinaryShort ctx hDP)
    (returnSemiperiodic ctx hDP)
    (returnOlcReturnBudget ctx)
    (returnNonlocalLong ctx hDP)

/-- **The genuine Return budget on the actual return geometry.**  The three routed L.2.2 masses
plus the OLC return slot fit the manuscript return floor `cStar·ξ·X/6`, from the two residuals. -/
theorem returnBudget_ofCounts (ctx : ActualFailureContext)
    (hDP : returnHighExcessMass ctx ≤ manuscriptCstarSmall * (ctx.shell.X : ℝ))
    (hML : 2 * (liftLevelBound ctx.shell.X : ℝ)
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12) :
    routedClassMassOf ctx.n24CarryData (returnCls ctx) 0
        + routedClassMassOf ctx.n24CarryData (returnCls ctx) 1
        + retSCanonical ctx * (ctx.shell.X : ℝ) * retIjCanonical ctx
        + routedClassMassOf ctx.n24CarryData (returnCls ctx) 2
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  le_trans (returnPackagesLowerClean_ofCounts ctx hDP) (returnHSmall ctx hML)

/-! ## Axiom audit -/

#print axioms returnCls
#print axioms routedClassMass_le_highExcess
#print axioms returnOrdinaryShort
#print axioms returnSemiperiodic
#print axioms returnNonlocalLong
#print axioms returnOlcReturnBudget
#print axioms returnHSmall
#print axioms returnLeafFromCounts
#print axioms returnBudget_ofCounts

end

end Erdos260
