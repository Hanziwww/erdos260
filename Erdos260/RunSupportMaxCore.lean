import Erdos260.RunSupportClosure
import Erdos260.Erdos260CapstoneFinal
import Erdos260.ActiveWindowContainmentCore
import Erdos260.ChargedBranchMassCore

/-!
# Run support closure, corrected core: the pointwise-max product residual

This module is the closure pass over the remaining Run / Class 5 residual
`RunClass5LeafSupportProductCoreResidual` (`RunSupportClosure.lean`).  It does
NOT fully close the Run line unconditionally; instead it proves an
**obstruction** against the current product-core shape and installs the
corrected minimal residual.

## The obstruction (honest finding)

The product-core residual demands

  `c0 * #runBaseFibre * stageMassOf ctx stageOf 0 <= (cStar*xi/12) * #supportShell`,

where the multiplier slot was pinned to the FULL base-stage mass
`stageMassOf ctx stageOf 0` (the canonical pin of `RunResidualClosure.lean`).
But every member of the base-stage fibre is a high-excess start, so
`stageMassOf ctx stageOf 0 >= #runBaseFibre * Y`.  Hence the product-core
residual forces the QUADRATIC sparsity

  `c0 * (#runBaseFibre)^2 * Y <= (cStar*xi/12) * #supportShell`
  (`runSupportProductCore_forces_quadratic_support`), and with `ctx.hfailure`
  `(#runBaseFibre)^2 * Y <= (cStar*xi/12) * X`
  (`runSupportProductCore_forces_quadratic_X`),

and, through the finite L.4.2 half-decrease and the exact I.6S partition,

  `#runBaseFibre * routedClassMassOf ... 5 <= cStar*xi*X/6`
  (`runSupportProductCore_forces_card_mul_runFloor`),

i.e. `#runBaseFibre` TIMES the I.5.2 run floor.  The manuscript Section 26 /
I.4.1 content is only the LINEAR sparsity `#runBaseFibre ~ X/Y` of the
base-stage fibre; for the genuine I.6S stage map (with `#runBaseFibre ~ X/Y`
members of the base output `O_0`) the quadratic demand fails by a factor
`#runBaseFibre`.  So the product-core residual is a factor-`N` over-claim
created by the multiplier pin `mult := stageMassOf ctx stageOf 0`; it is not
the manuscript's Run atom and cannot be closed from the Section 26 estimates.

## The corrected minimal residual

`RunClass5LeafSupportMaxCoreResidual` replaces the summed multiplier by the
genuine pointwise K.1.2/L.20 multiplier: the MAX window excess over the
base-stage fibre (`runBaseMaxExcess`).  Its product inequality

  `c0 * #runBaseFibre * runBaseMaxExcess <= (cStar*xi/12) * #supportShell`

forces only the LINEAR sparsity `c0 * #runBaseFibre * Y <= (cStar*xi/12) *
#supportShell` (`runSupportMaxCore_forces_linear_support`) — exactly the
manuscript-shaped Section 26 statement.  The corrected residual is proved to be

* implied by the old product-core residual (`toSupportMaxCoreResidual` on
  `RunClass5LeafSupportProductCoreResidual` — the shrink is sound and loses
  nothing), and
* EQUIVALENT to the sharp leaf residual `RunClass5LeafResidual`
  (`RunClass5LeafSupportMaxCoreResidual.toLeafResidual` and
  `RunClass5LeafResidual.toSupportMaxCoreResidual`),

so it is the correct minimal Run / Class 5 core: three fields (`stageOf`,
finite `hhalf`, the max-form Section 26 product bound), with the downstream
genuine leaf, the I.5.2 run floor, and the two-atom capstone all reachable
through it (`erdos260_ofSupportMaxCore_and_highExcess`).

## The dyadic ceiling on the multiplier (push pass)

Sections 7-8 ground the pointwise-max multiplier in the PROVED dyadic shell
geometry: under the shared K.1 active-window interior condition (the same
boundary residual the class-0/1/3/4 seed closures retain), every base-stage
window excess — hence `runBaseMaxExcess` itself — is at most the canonical
matched K.1.2/L.20 ceiling `runDyadicMult = max 0 ((r+1)*(L+B+1) - T)`, all
parameters read off `ctx` (`hitGap_le_runDyadicG0_of_window`, the proved
`HitSequence.hitGap_le_of_shell_window`).  This yields a windowExcess-free
sufficient entry point `RunClass5LeafSupportDyadicCountResidual` (stage map,
finite half-decrease, interior condition, and one scalar count numeric at the
canonical multiplier) with a proved bridge into the max-form residual and the
capstone.  An obstruction-style audit (`runSupportDyadicCount_forces_mult_X`)
records honestly that the count form pins the multiplier slot to the FULL
active-window cap — at the pinned deep-shell calibration (`r ~ kappa*L`,
`g0 = L+B+1`, `T = 2L+1`, `Y = L/64`) a factor `~ L` above the manuscript's
K.1.2/L.20 multiplier (the deep-shell blow-up audited in
`RunLeafUnconditional`/`TowerRunDeepCore`) — so the max-form residual remains
the honest minimal core and the count form is strictly an entry point.

No `sorry`, `axiom`, `admit`, `native_decide`, or empty/degenerate witness is
introduced: `runBaseMaxExcess` is the actual maximal charged window excess of
the genuine base-stage fibre, and all bridges keep the actual I.6S stage map.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The genuine pointwise multiplier: the max base-fibre window excess -/

/-- The maximal charged window excess over the actual base-stage fibre
(`0` when the fibre is empty).  This is the canonical genuine value of the
K.1.2/L.20 pointwise multiplier slot of `RunClass5LeafResidual`. -/
def runBaseMaxExcess (ctx : ActualFailureContext) (stageOf : Nat -> Nat) : Real :=
  if h : (runBaseFibre ctx stageOf).Nonempty then
    (runBaseFibre ctx stageOf).sup' h
      (fun k => windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ctx.n24CarryData.T)
  else 0

/-- Every base-stage fibre member's window excess is at most the max excess. -/
theorem windowExcess_le_runBaseMaxExcess (ctx : ActualFailureContext)
    (stageOf : Nat -> Nat) :
    ∀ k ∈ runBaseFibre ctx stageOf,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        <= runBaseMaxExcess ctx stageOf := by
  intro k hk
  have hne : (runBaseFibre ctx stageOf).Nonempty := ⟨k, hk⟩
  unfold runBaseMaxExcess
  rw [dif_pos hne]
  exact Finset.le_sup'
    (fun j => windowExcess (hitGap ctx.n24CarryData.a) j ctx.n24CarryData.r
      ctx.n24CarryData.T) hk

/-- The max base-fibre excess is nonnegative. -/
theorem runBaseMaxExcess_nonneg (ctx : ActualFailureContext) (stageOf : Nat -> Nat) :
    0 <= runBaseMaxExcess ctx stageOf := by
  by_cases h : (runBaseFibre ctx stageOf).Nonempty
  case pos =>
    obtain ⟨k, hk⟩ := h
    exact le_trans (windowExcess_nonneg _ _ _ _)
      (windowExcess_le_runBaseMaxExcess ctx stageOf k hk)
  case neg =>
    unfold runBaseMaxExcess
    rw [dif_neg h]

/-- The max base-fibre excess is below any uniform pointwise bound. -/
theorem runBaseMaxExcess_le_of_pointBound (ctx : ActualFailureContext)
    (stageOf : Nat -> Nat) {mult : Real} (hmult_nonneg : 0 <= mult)
    (hpoint : ∀ k ∈ runBaseFibre ctx stageOf,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        <= mult) :
    runBaseMaxExcess ctx stageOf <= mult := by
  unfold runBaseMaxExcess
  split_ifs with h
  · exact Finset.sup'_le h _ hpoint
  · exact hmult_nonneg

/-- The max base-fibre excess is at most the summed base-stage mass
(the old product-core multiplier): max <= sum of nonnegatives. -/
theorem runBaseMaxExcess_le_stageMass (ctx : ActualFailureContext)
    (stageOf : Nat -> Nat) :
    runBaseMaxExcess ctx stageOf <= stageMassOf ctx stageOf 0 :=
  runBaseMaxExcess_le_of_pointBound ctx stageOf (stageMassOf_nonneg ctx stageOf 0)
    (runBaseFibre_windowExcess_le_stageMass ctx stageOf)

/-- The max base-fibre excess vanishes when the base-stage fibre is empty. -/
theorem runBaseMaxExcess_eq_zero_of_card_eq_zero (ctx : ActualFailureContext)
    (stageOf : Nat -> Nat) (hcard : (runBaseFibre ctx stageOf).card = 0) :
    runBaseMaxExcess ctx stageOf = 0 := by
  have h : ¬ (runBaseFibre ctx stageOf).Nonempty := by
    rw [Finset.card_eq_zero] at hcard
    rw [hcard]
    exact Finset.not_nonempty_empty
  unfold runBaseMaxExcess
  rw [dif_neg h]

/-! ## 2.  The active-floor lower side of the base-stage fibre

Every base-stage fibre member is a high-excess start of the actual N.24 carry
data, so its window excess is at least the active floor `Y`. -/

/-- Each base-stage fibre member has window excess at least the active floor `Y`. -/
theorem runBaseFibre_Y_le_windowExcess (ctx : ActualFailureContext)
    (stageOf : Nat -> Nat) :
    ∀ k ∈ runBaseFibre ctx stageOf,
      ctx.n24CarryData.Y
        <= windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          ctx.n24CarryData.T := by
  intro k hk
  have hroute : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 :=
    (Finset.mem_filter.mp hk).1
  have hmem : k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
      ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y :=
    (Finset.mem_filter.mp hroute).1
  exact (mem_highExcessStarts.mp hmem).2

/-- The base-stage mass dominates `#runBaseFibre * Y` (sum over the fibre of the
per-member active floor). -/
theorem runBaseFibre_card_mul_Y_le_stageMass (ctx : ActualFailureContext)
    (stageOf : Nat -> Nat) :
    ((runBaseFibre ctx stageOf).card : Real) * ctx.n24CarryData.Y
      <= stageMassOf ctx stageOf 0 := by
  calc ((runBaseFibre ctx stageOf).card : Real) * ctx.n24CarryData.Y
      = ∑ _k ∈ runBaseFibre ctx stageOf, ctx.n24CarryData.Y := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ <= ∑ k ∈ runBaseFibre ctx stageOf,
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ctx.n24CarryData.T :=
        Finset.sum_le_sum (runBaseFibre_Y_le_windowExcess ctx stageOf)
    _ = stageMassOf ctx stageOf 0 := rfl

/-! ## 3.  OBSTRUCTION — the product-core residual quadratically over-claims

The multiplier pin `mult := stageMassOf ctx stageOf 0` makes the product-core
inequality a factor-`#runBaseFibre` over-claim relative to the manuscript
Section 26 sparsity. -/

/-- **Through the finite L.4.2 half-decrease and the exact I.6S partition, the
product-core witness bounds the full class-5 mass by twice its base-stage
mass** (the descent doubling `wt_aug(O_0) <= 2*wt(O_0)`). -/
theorem runSupportProductCore_classMass_le_two_stageMass {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportProductCoreResidual ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      <= 2 * stageMassOf ctx R.stageOf 0 := by
  rw [runClass5_genuine_stageSum_eq ctx R.stageOf]
  exact halfChain_sum_le (stageMassOf ctx R.stageOf) (stageMassOf_nonneg ctx R.stageOf)
    (runHalf_total_of_finite ctx R.stageOf R.hhalf) (runStageLen ctx R.stageOf)

/-- **The product-core residual forces QUADRATIC base-fibre sparsity (support
form).**  Since every base-stage member carries excess `>= Y`, the pinned
multiplier `stageMassOf ctx stageOf 0 >= #runBaseFibre * Y`, so the product
bound demands `c0 * (#runBaseFibre)^2 * Y <= (cStar*xi/12) * #supportShell` —
quadratic in the fibre count, whereas the manuscript Section 26 / I.4.1
sparsity of the base run output is only linear. -/
theorem runSupportProductCore_forces_quadratic_support {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportProductCoreResidual ctx) :
    erdos260Constants.c0 *
        (((runBaseFibre ctx R.stageOf).card : Real) ^ 2 * ctx.n24CarryData.Y)
      <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) *
        ((supportShell ctx.d ctx.X).card : Real) := by
  have hc0N : 0 <= erdos260Constants.c0 * ((runBaseFibre ctx R.stageOf).card : Real) :=
    mul_nonneg erdos260Constants.c0_pos.le (Nat.cast_nonneg _)
  calc erdos260Constants.c0 *
          (((runBaseFibre ctx R.stageOf).card : Real) ^ 2 * ctx.n24CarryData.Y)
      = erdos260Constants.c0 * ((runBaseFibre ctx R.stageOf).card : Real) *
          (((runBaseFibre ctx R.stageOf).card : Real) * ctx.n24CarryData.Y) := by
        ring
    _ <= erdos260Constants.c0 * ((runBaseFibre ctx R.stageOf).card : Real) *
          stageMassOf ctx R.stageOf 0 :=
        mul_le_mul_of_nonneg_left (runBaseFibre_card_mul_Y_le_stageMass ctx R.stageOf) hc0N
    _ <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) *
          ((supportShell ctx.d ctx.X).card : Real) := R.hproduct

/-- **The product-core residual forces quadratic sparsity against the shell
scale `X`** (consuming the positive-density failure `ctx.hfailure`):
`(#runBaseFibre)^2 * Y <= (cStar*xi/12) * X`.  For the genuine I.6S stage map
the manuscript predicts `#runBaseFibre ~ X/Y`, under which this reads
`X^2/Y <= (cStar*xi/12) * X`, i.e. `X <= (cStar*xi/12) * Y` — false for every
deep shell (`Y ~ epsilon*L << X`).  Hence the genuine manuscript witness cannot
satisfy the product-core residual; the pin `mult := stageMassOf 0` over-claims
by a factor `#runBaseFibre`. -/
theorem runSupportProductCore_forces_quadratic_X {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportProductCoreResidual ctx) :
    ((runBaseFibre ctx R.stageOf).card : Real) ^ 2 * ctx.n24CarryData.Y
      <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) * (ctx.X : Real) := by
  have hA : 0 <= erdos260Constants.cStar * erdos260Constants.ξ / 12 :=
    div_nonneg
      (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
      (by norm_num)
  have hchain : erdos260Constants.c0 *
      (((runBaseFibre ctx R.stageOf).card : Real) ^ 2 * ctx.n24CarryData.Y)
      <= erdos260Constants.c0 *
        ((erdos260Constants.cStar * erdos260Constants.ξ / 12) * (ctx.X : Real)) :=
    calc erdos260Constants.c0 *
            (((runBaseFibre ctx R.stageOf).card : Real) ^ 2 * ctx.n24CarryData.Y)
        <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) *
            ((supportShell ctx.d ctx.X).card : Real) :=
          runSupportProductCore_forces_quadratic_support R
      _ <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) *
            (erdos260Constants.c0 * (ctx.X : Real)) :=
          mul_le_mul_of_nonneg_left (le_of_lt ctx.hfailure) hA
      _ = erdos260Constants.c0 *
            ((erdos260Constants.cStar * erdos260Constants.ξ / 12) * (ctx.X : Real)) := by
          ring
  exact le_of_mul_le_mul_left hchain erdos260Constants.c0_pos

/-- **The product-core residual forces `#runBaseFibre` TIMES the I.5.2 run
floor:** `#runBaseFibre * routedClassMassOf ... 5 <= cStar*xi*X/6`.  The
manuscript run floor is the `#runBaseFibre = 1` instance; demanding it scaled
by the full base-fibre count is the precise quantitative over-claim of the
product-core form. -/
theorem runSupportProductCore_forces_card_mul_runFloor {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportProductCoreResidual ctx) :
    ((runBaseFibre ctx R.stageOf).card : Real) *
        routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      <= erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6 := by
  have hN : (0 : Real) <= ((runBaseFibre ctx R.stageOf).card : Real) := Nat.cast_nonneg _
  have hA : 0 <= erdos260Constants.cStar * erdos260Constants.ξ / 12 :=
    div_nonneg
      (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
      (by norm_num)
  have hbase : erdos260Constants.c0 *
      (((runBaseFibre ctx R.stageOf).card : Real) * stageMassOf ctx R.stageOf 0)
      <= erdos260Constants.c0 *
        ((erdos260Constants.cStar * erdos260Constants.ξ / 12) * (ctx.X : Real)) :=
    calc erdos260Constants.c0 *
            (((runBaseFibre ctx R.stageOf).card : Real) * stageMassOf ctx R.stageOf 0)
        = erdos260Constants.c0 * ((runBaseFibre ctx R.stageOf).card : Real) *
            stageMassOf ctx R.stageOf 0 := by ring
      _ <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) *
            ((supportShell ctx.d ctx.X).card : Real) := R.hproduct
      _ <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) *
            (erdos260Constants.c0 * (ctx.X : Real)) :=
          mul_le_mul_of_nonneg_left (le_of_lt ctx.hfailure) hA
      _ = erdos260Constants.c0 *
            ((erdos260Constants.cStar * erdos260Constants.ξ / 12) * (ctx.X : Real)) := by
          ring
  have hNM : ((runBaseFibre ctx R.stageOf).card : Real) * stageMassOf ctx R.stageOf 0
      <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) * (ctx.X : Real) :=
    le_of_mul_le_mul_left hbase erdos260Constants.c0_pos
  calc ((runBaseFibre ctx R.stageOf).card : Real) *
          routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      <= ((runBaseFibre ctx R.stageOf).card : Real) *
          (2 * stageMassOf ctx R.stageOf 0) :=
        mul_le_mul_of_nonneg_left (runSupportProductCore_classMass_le_two_stageMass R) hN
    _ = 2 * (((runBaseFibre ctx R.stageOf).card : Real) * stageMassOf ctx R.stageOf 0) := by
        ring
    _ <= 2 * ((erdos260Constants.cStar * erdos260Constants.ξ / 12) * (ctx.X : Real)) := by
        linarith [hNM]
    _ = erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6 := by
        rw [ActualFailureContext.shell_X]
        ring

/-! ## 4.  The corrected minimal residual: the pointwise-max product core -/

/-- **The corrected minimal Run / Class 5 residual (max-form product core).**

Exactly three fields remain:

* `stageOf` — the genuine I.6S charge/stage map of the class-5 fibre;
* `hhalf` — the finite L.4.2 mass half-decrease on within-descent steps;
* `hproduct` — the Section 26 support-relative product bound with the GENUINE
  pointwise K.1.2/L.20 multiplier `runBaseMaxExcess` (the max charged window
  excess over the base-stage fibre), NOT the summed base mass.

This form forces only the linear manuscript sparsity
(`runSupportMaxCore_forces_linear_support`) and is equivalent to the sharp
leaf residual `RunClass5LeafResidual` (`toLeafResidual` /
`RunClass5LeafResidual.toSupportMaxCoreResidual`). -/
structure RunClass5LeafSupportMaxCoreResidual (ctx : ActualFailureContext) where
  /-- The I.6S charge/stage map of the class-5 fibre. -/
  stageOf : Nat -> Nat
  /-- The finite L.4.2 mass half-decrease on genuine within-descent steps. -/
  hhalf : forall i, i + 1 < runStageLen ctx stageOf ->
    stageMassOf ctx stageOf (i + 1) <= (1 / 2) * stageMassOf ctx stageOf i
  /-- The support-relative Section 26 product bound at the pointwise-max multiplier. -/
  hproduct :
    erdos260Constants.c0 * ((runBaseFibre ctx stageOf).card : Real) *
        runBaseMaxExcess ctx stageOf
      <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) *
        ((supportShell ctx.d ctx.X).card : Real)

/-- **The corrected residual forces only the LINEAR manuscript sparsity:**
`c0 * #runBaseFibre * Y <= (cStar*xi/12) * #supportShell` — exactly the
Section 26 / I.4.1 shape `#runBaseFibre ~ X/Y`, with no quadratic blow-up. -/
theorem runSupportMaxCore_forces_linear_support {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportMaxCoreResidual ctx) :
    erdos260Constants.c0 * ((runBaseFibre ctx R.stageOf).card : Real) *
        ctx.n24CarryData.Y
      <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) *
        ((supportShell ctx.d ctx.X).card : Real) := by
  by_cases hne : (runBaseFibre ctx R.stageOf).Nonempty
  case pos =>
    obtain ⟨k, hk⟩ := hne
    have hYmax : ctx.n24CarryData.Y <= runBaseMaxExcess ctx R.stageOf :=
      le_trans (runBaseFibre_Y_le_windowExcess ctx R.stageOf k hk)
        (windowExcess_le_runBaseMaxExcess ctx R.stageOf k hk)
    have hc0N : 0 <= erdos260Constants.c0 *
        ((runBaseFibre ctx R.stageOf).card : Real) :=
      mul_nonneg erdos260Constants.c0_pos.le (Nat.cast_nonneg _)
    exact le_trans (mul_le_mul_of_nonneg_left hYmax hc0N) R.hproduct
  case neg =>
    have hcard : (runBaseFibre ctx R.stageOf).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.not_nonempty_iff_eq_empty.mp hne
    have hS : (0 : Real) <= ((supportShell ctx.d ctx.X).card : Real) := Nat.cast_nonneg _
    have hA : 0 <= erdos260Constants.cStar * erdos260Constants.ξ / 12 :=
      div_nonneg
        (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
        (by norm_num)
    rw [hcard]
    simpa using mul_nonneg hA hS

/-! ## 5.  The corrected residual is sound and minimal

Sound: the old product-core residual implies it (the multiplier shrinks from
the summed mass to the pointwise max).  Minimal: it is equivalent to the sharp
leaf residual `RunClass5LeafResidual`. -/

namespace RunClass5LeafSupportProductCoreResidual

/-- **Sound shrink** — the old product-core residual implies the corrected
max-form residual (max excess <= summed base mass). -/
def toSupportMaxCoreResidual {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportProductCoreResidual ctx) :
    RunClass5LeafSupportMaxCoreResidual ctx where
  stageOf := R.stageOf
  hhalf := R.hhalf
  hproduct := by
    have hc0N : 0 <= erdos260Constants.c0 *
        ((runBaseFibre ctx R.stageOf).card : Real) :=
      mul_nonneg erdos260Constants.c0_pos.le (Nat.cast_nonneg _)
    exact le_trans
      (mul_le_mul_of_nonneg_left (runBaseMaxExcess_le_stageMass ctx R.stageOf) hc0N)
      R.hproduct

/-- The shrink keeps the actual I.6S stage map. -/
@[simp] theorem toSupportMaxCoreResidual_stageOf {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportProductCoreResidual ctx) :
    R.toSupportMaxCoreResidual.stageOf = R.stageOf := rfl

end RunClass5LeafSupportProductCoreResidual

namespace RunClass5LeafSupportMaxCoreResidual

/-- **The sharp leaf residual from the corrected max-form residual.**  The
pointwise multiplier is the genuine max base-fibre excess; the per-hit floor is
reconstructed honestly as `#supportShell / #runBaseFibre` on a nonempty fibre. -/
def toLeafResidual {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportMaxCoreResidual ctx) : RunClass5LeafResidual ctx where
  stageOf := R.stageOf
  hhalf := R.hhalf
  mult := runBaseMaxExcess ctx R.stageOf
  hmult_nonneg := runBaseMaxExcess_nonneg ctx R.stageOf
  hpoint := windowExcess_le_runBaseMaxExcess ctx R.stageOf
  rhoL :=
    if hN : (runBaseFibre ctx R.stageOf).card = 0 then 1
    else ((supportShell ctx.d ctx.X).card : Real) /
      ((runBaseFibre ctx R.stageOf).card : Real)
  hrhoL_pos := by
    by_cases hN : (runBaseFibre ctx R.stageOf).card = 0
    case pos =>
      simp [hN]
    case neg =>
      have hS : 0 < ((supportShell ctx.d ctx.X).card : Real) :=
        actualFailureContext_supportShell_card_pos ctx
      have hNpos : 0 < ((runBaseFibre ctx R.stageOf).card : Real) := by
        exact_mod_cast Nat.pos_of_ne_zero hN
      simp [hN, div_pos hS hNpos]
  hpack := by
    by_cases hN : (runBaseFibre ctx R.stageOf).card = 0
    case pos =>
      have hS : (0 : Real) <= ((supportShell ctx.d ctx.X).card : Real) :=
        Nat.cast_nonneg _
      simp [hN]
    case neg =>
      have hNreal : Ne ((runBaseFibre ctx R.stageOf).card : Real) 0 := by
        exact_mod_cast hN
      have hcalc :
          ((runBaseFibre ctx R.stageOf).card : Real) *
              (((supportShell ctx.d ctx.X).card : Real) /
                ((runBaseFibre ctx R.stageOf).card : Real))
            <= ((supportShell ctx.d ctx.X).card : Real) := by
        calc
          ((runBaseFibre ctx R.stageOf).card : Real) *
              (((supportShell ctx.d ctx.X).card : Real) /
                ((runBaseFibre ctx R.stageOf).card : Real))
              = ((supportShell ctx.d ctx.X).card : Real) := by
                field_simp [hNreal]
          _ <= ((supportShell ctx.d ctx.X).card : Real) := le_rfl
      simpa [hN] using hcalc
  hsmall := by
    by_cases hN : (runBaseFibre ctx R.stageOf).card = 0
    case pos =>
      have hmax : runBaseMaxExcess ctx R.stageOf = 0 :=
        runBaseMaxExcess_eq_zero_of_card_eq_zero ctx R.stageOf hN
      have hA : 0 <= erdos260Constants.cStar * erdos260Constants.ξ / 12 :=
        div_nonneg
          (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
          (by norm_num)
      simpa [hN, hmax] using hA
    case neg =>
      have hSpos : 0 < ((supportShell ctx.d ctx.X).card : Real) :=
        actualFailureContext_supportShell_card_pos ctx
      have hNpos : 0 < ((runBaseFibre ctx R.stageOf).card : Real) := by
        exact_mod_cast Nat.pos_of_ne_zero hN
      have hS_ne : Ne ((supportShell ctx.d ctx.X).card : Real) 0 := ne_of_gt hSpos
      have hN_ne : Ne ((runBaseFibre ctx R.stageOf).card : Real) 0 := ne_of_gt hNpos
      have hmain : (erdos260Constants.c0 *
          ((runBaseFibre ctx R.stageOf).card : Real) *
            runBaseMaxExcess ctx R.stageOf) /
          ((supportShell ctx.d ctx.X).card : Real)
          <= erdos260Constants.cStar * erdos260Constants.ξ / 12 := by
        rw [div_le_iff₀ hSpos]
        exact R.hproduct
      have hcalc : (erdos260Constants.c0 /
          (((supportShell ctx.d ctx.X).card : Real) /
            ((runBaseFibre ctx R.stageOf).card : Real))) *
            runBaseMaxExcess ctx R.stageOf
          <= erdos260Constants.cStar * erdos260Constants.ξ / 12 := by
        calc (erdos260Constants.c0 /
            (((supportShell ctx.d ctx.X).card : Real) /
              ((runBaseFibre ctx R.stageOf).card : Real))) *
              runBaseMaxExcess ctx R.stageOf
            = (erdos260Constants.c0 *
                ((runBaseFibre ctx R.stageOf).card : Real) *
                  runBaseMaxExcess ctx R.stageOf) /
                ((supportShell ctx.d ctx.X).card : Real) := by
              field_simp [hS_ne, hN_ne]
          _ <= erdos260Constants.cStar * erdos260Constants.ξ / 12 := hmain
      simpa [hN] using hcalc

/-- The leaf residual built from the corrected core keeps the actual I.6S stage map. -/
@[simp] theorem toLeafResidual_stageOf {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportMaxCoreResidual ctx) :
    R.toLeafResidual.stageOf = R.stageOf := rfl

/-- The leaf residual built from the corrected core carries the genuine
pointwise-max multiplier. -/
@[simp] theorem toLeafResidual_mult {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportMaxCoreResidual ctx) :
    R.toLeafResidual.mult = runBaseMaxExcess ctx R.stageOf := rfl

end RunClass5LeafSupportMaxCoreResidual

namespace RunClass5LeafResidual

/-- **Minimality (converse bridge)** — the sharp leaf residual implies the
corrected max-form residual, so the two are equivalent surfaces.  The max
excess sits below the leaf's pointwise multiplier, and the K.4 smallness plus
the I.4.1 packing reassemble the support-relative product bound. -/
def toSupportMaxCoreResidual {ctx : ActualFailureContext}
    (R : RunClass5LeafResidual ctx) : RunClass5LeafSupportMaxCoreResidual ctx where
  stageOf := R.stageOf
  hhalf := R.hhalf
  hproduct := by
    have hA : 0 <= erdos260Constants.cStar * erdos260Constants.ξ / 12 :=
      div_nonneg
        (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
        (by norm_num)
    have hN : (0 : Real) <= ((runBaseFibre ctx R.stageOf).card : Real) :=
      Nat.cast_nonneg _
    have hc0N : 0 <= erdos260Constants.c0 *
        ((runBaseFibre ctx R.stageOf).card : Real) :=
      mul_nonneg erdos260Constants.c0_pos.le hN
    have hmax_le : runBaseMaxExcess ctx R.stageOf <= R.mult :=
      runBaseMaxExcess_le_of_pointBound ctx R.stageOf R.hmult_nonneg R.hpoint
    have hsmall' : erdos260Constants.c0 * R.mult
        <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) * R.rhoL := by
      have h := R.hsmall
      rw [div_mul_eq_mul_div, div_le_iff₀ R.hrhoL_pos] at h
      exact h
    calc erdos260Constants.c0 * ((runBaseFibre ctx R.stageOf).card : Real) *
            runBaseMaxExcess ctx R.stageOf
        <= erdos260Constants.c0 * ((runBaseFibre ctx R.stageOf).card : Real) *
            R.mult :=
          mul_le_mul_of_nonneg_left hmax_le hc0N
      _ = ((runBaseFibre ctx R.stageOf).card : Real) *
            (erdos260Constants.c0 * R.mult) := by ring
      _ <= ((runBaseFibre ctx R.stageOf).card : Real) *
            ((erdos260Constants.cStar * erdos260Constants.ξ / 12) * R.rhoL) :=
          mul_le_mul_of_nonneg_left hsmall' hN
      _ = (erdos260Constants.cStar * erdos260Constants.ξ / 12) *
            (((runBaseFibre ctx R.stageOf).card : Real) * R.rhoL) := by ring
      _ <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) *
            ((supportShell ctx.d ctx.X).card : Real) :=
          mul_le_mul_of_nonneg_left R.hpack hA

/-- The converse bridge keeps the actual I.6S stage map. -/
@[simp] theorem toSupportMaxCoreResidual_stageOf {ctx : ActualFailureContext}
    (R : RunClass5LeafResidual ctx) :
    R.toSupportMaxCoreResidual.stageOf = R.stageOf := rfl

end RunClass5LeafResidual

/-! ## 6.  Family bridges, the genuine leaf, the run floor, and the capstone -/

/-- Family bridge from the corrected max-form residual to the sharp leaf residual. -/
def runClass5LeafResidual_ofSupportMaxCoreResidual
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx) :
    forall ctx : ActualFailureContext, RunClass5LeafResidual ctx :=
  fun ctx => (R ctx).toLeafResidual

/-- Family converse: the sharp leaf residual gives the corrected residual. -/
def runSupportMaxCoreResidual_ofLeafResidual
    (R : forall ctx : ActualFailureContext, RunClass5LeafResidual ctx) :
    forall ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx :=
  fun ctx => (R ctx).toSupportMaxCoreResidual

/-- Family bridge from the old product-core residual to the corrected residual
(the shrink loses nothing). -/
def runSupportMaxCoreResidual_ofProductCoreResidual
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportProductCoreResidual ctx) :
    forall ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx :=
  fun ctx => (R ctx).toSupportMaxCoreResidual

/-- The genuine Run class-5 leaf from the corrected max-form residual. -/
def runClass5GenuineLeaf_ofSupportMaxCoreResidual
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx) :
    forall ctx : ActualFailureContext, RunClass5GenuineLeaf ctx :=
  runLeafFromResidual (runClass5LeafResidual_ofSupportMaxCoreResidual R)

/-- The I.5.2 run floor obtained from the corrected max-form residual. -/
theorem runClass5SupportMaxCoreResidual_runFloor
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx)
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      <= erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6 :=
  runLeafFromResidual_runFloor (runClass5LeafResidual_ofSupportMaxCoreResidual R) ctx

/-- The definitive two-atom capstone residual, with the Run atom supplied in the
corrected max-form. -/
def erdos260CapstoneFinalResidual_ofSupportMaxCore
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx)
    (he : HighExcessRoutingCountResidual) : Erdos260CapstoneFinalResidual where
  runResidual := runClass5LeafResidual_ofSupportMaxCoreResidual R
  highExcessResidual := he

/-- Erdős 260 from the corrected max-form Run residual plus the P9 routing atom. -/
theorem erdos260_ofSupportMaxCore_and_highExcess
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx)
    (he : HighExcessRoutingCountResidual) : Erdos260Statement :=
  erdos260_capstone_final (erdos260CapstoneFinalResidual_ofSupportMaxCore R he)

/-! ## 7.  The dyadic ceiling on the pointwise-max multiplier (CLOSED)

The genuine pointwise multiplier `runBaseMaxExcess` is not a free quantity: on
base-stage fibres satisfying the shared K.1 active-window interior condition
(the same boundary geometry the class-0/1/3/4 seed closures retain), it is
PROVED to sit below the canonical matched K.1.2/L.20 ceiling
`runDyadicMult ctx = max 0 ((r+1)*(L+B+1) - T)`, every parameter read off the
actual failure context.  The load-bearing input is the proved dyadic-scale
adjacent-hit-gap estimate `HitSequence.hitGap_le_of_shell_window` on the
actual carry hits. -/

/-- **The dyadic-shell gap ceiling `L + B + 1`, read from the failure context.**
The shared dyadic adjacent-hit-gap scale of the class-0/1/3/4 seed closures
(`class0ShellGapScale`, `densePackDyadicG0`, `returnDyadicG0`): a property of
the carry hit sequence, not of the class.  `L = Classical.choose
ctx.shell.hXdyadic` (the dyadic exponent `X = 2^L`) and `B = carryB
ctx.shell.Q` (the carry-denominator scale `Q*4 <= 2^B`). -/
def runDyadicG0 (ctx : ActualFailureContext) : Nat :=
  Classical.choose ctx.shell.hXdyadic + carryB ctx.shell.Q + 1

/-- **The canonical matched K.1.2/L.20 window-excess ceiling**
`max 0 ((r+1)*(L+B+1) - T)` — the active-window worst-case charge, nonnegative
by construction, with every parameter read off `ctx`. -/
def runDyadicMult (ctx : ActualFailureContext) : Real :=
  max 0 (((ctx.n24CarryData.r : Real) + 1) * (runDyadicG0 ctx : Real)
    - ctx.n24CarryData.T)

theorem runDyadicMult_nonneg (ctx : ActualFailureContext) :
    0 <= runDyadicMult ctx :=
  le_max_left _ _

/-- The active-floor scaling `(r+1)*g0 - T` is dominated by the matched
ceiling (by definition of the `max`). -/
theorem run_scale_le_runDyadicMult (ctx : ActualFailureContext) :
    ((ctx.n24CarryData.r : Real) + 1) * (runDyadicG0 ctx : Real)
        - ctx.n24CarryData.T
      <= runDyadicMult ctx :=
  le_max_right _ _

/-- The shell scale is positive: `1 <= X = 2^L`. -/
theorem runShellX_pos (ctx : ActualFailureContext) : 1 <= ctx.shell.X := by
  rw [Classical.choose_spec ctx.shell.hXdyadic]
  exact Nat.one_le_two_pow

/-- **The dyadic-scale gap bound on the active window, grounded in `ctx`.**
`hitGap a j <= L + B + 1` for every index `j` within reach of the shell
window — the PROVED `HitSequence.hitGap_le_of_shell_window` on the actual
carry hit sequence, with `eta = P/Q`, `X = 2^L`, `1 <= X`, `Q*4 <= 2^B` all
discharged from the shell. -/
theorem hitGap_le_runDyadicG0_of_window (ctx : ActualFailureContext)
    {r₀ : Nat} (hReach : r₀ + 1 <= (supportShell ctx.shell.d ctx.shell.X).card)
    {j : Nat}
    (hj : j < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + r₀) :
    hitGap ctx.n24CarryData.a j <= runDyadicG0 ctx :=
  ctx.n24CarryData.carry.hits.hitGap_le_of_shell_window
    ctx.shell.hd ctx.shell.hQ
    (Classical.choose_spec ctx.shell.hrational)
    (Classical.choose_spec ctx.shell.hXdyadic)
    (runShellX_pos ctx)
    (carryB_spec ctx.shell.hQ)
    hReach hj

/-- **The base-stage window excesses are capped by the canonical dyadic
ceiling** on every base-stage fibre satisfying the K.1 active-window interior
condition `k + r + 1 < firstIndexAbove X + #supportShell` (the manuscript
endpoint geometry; false only for the `<= r + 1` top boundary starts). -/
theorem runBaseFibre_windowExcess_le_runDyadicMult (ctx : ActualFailureContext)
    (stageOf : Nat -> Nat)
    (hinterior : ∀ k ∈ runBaseFibre ctx stageOf,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) :
    ∀ k ∈ runBaseFibre ctx stageOf,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          ctx.n24CarryData.T
        <= runDyadicMult ctx := by
  intro k hk
  refine windowExcess_le_window_gap_multiplier (g₀ := runDyadicG0 ctx) ?_
    (run_scale_le_runDyadicMult ctx) (runDyadicMult_nonneg ctx)
  intro j _hjlo hjhi
  have hK1 : 1 <= (supportShell ctx.shell.d ctx.shell.X).card :=
    le_trans (Nat.le_add_left 1 ctx.n24CarryData.r) (r_add_one_le_width ctx)
  have hint := hinterior k hk
  refine hitGap_le_runDyadicG0_of_window ctx
    (r₀ := (supportShell ctx.shell.d ctx.shell.X).card - 1) (by omega) ?_
  omega

/-- **The pointwise-max multiplier is capped by the canonical dyadic ceiling**
under the K.1 interior condition: `runBaseMaxExcess <= runDyadicMult`. -/
theorem runBaseMaxExcess_le_runDyadicMult (ctx : ActualFailureContext)
    (stageOf : Nat -> Nat)
    (hinterior : ∀ k ∈ runBaseFibre ctx stageOf,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) :
    runBaseMaxExcess ctx stageOf <= runDyadicMult ctx :=
  runBaseMaxExcess_le_of_pointBound ctx stageOf (runDyadicMult_nonneg ctx)
    (runBaseFibre_windowExcess_le_runDyadicMult ctx stageOf hinterior)

/-- **Sharpness — the ceiling dominates the active floor** on every nonempty
interior base-stage fibre: `Y <= runDyadicMult`.  The collapse from the
realized max to the canonical ceiling loses at most the genuine
`[Y, runDyadicMult]` multiplier window; the ceiling is never a degenerate
(sub-floor) stand-in. -/
theorem Y_le_runDyadicMult_of_interior (ctx : ActualFailureContext)
    (stageOf : Nat -> Nat)
    (hinterior : ∀ k ∈ runBaseFibre ctx stageOf,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card)
    (hne : (runBaseFibre ctx stageOf).Nonempty) :
    ctx.n24CarryData.Y <= runDyadicMult ctx := by
  obtain ⟨k, hk⟩ := hne
  exact le_trans (runBaseFibre_Y_le_windowExcess ctx stageOf k hk)
    (runBaseFibre_windowExcess_le_runDyadicMult ctx stageOf hinterior k hk)

/-! ## 8.  The dyadic-count entry point (sufficient, audited as an over-claim)

Replacing the realized max `runBaseMaxExcess` by its proved ceiling
`runDyadicMult` removes every `windowExcess` quantity from the interface: the
residual becomes a stage map, the finite half-decrease, the shared K.1
interior boundary condition, and ONE scalar count numeric.  The bridge into
the max-form residual is proved, so the entry point is sound.  It is NOT
minimal: the audit below shows it pins the multiplier slot to the full
active-window cap, a factor `~ L` above the manuscript multiplier in deep
shells, so the max-form residual stays the honest core. -/

/-- **The windowExcess-free dyadic-count residual (sufficient entry point).**

* `stageOf` — the I.6S charge/stage map;
* `hhalf` — the finite L.4.2 mass half-decrease;
* `hinterior` — the shared K.1 active-window interior condition on the
  base-stage fibre (the boundary residual every sibling class retains);
* `hcount` — the single scalar Section 26 count numeric at the canonical
  matched ceiling `runDyadicMult`. -/
structure RunClass5LeafSupportDyadicCountResidual (ctx : ActualFailureContext) where
  /-- The I.6S charge/stage map of the class-5 fibre. -/
  stageOf : Nat -> Nat
  /-- The finite L.4.2 mass half-decrease on genuine within-descent steps. -/
  hhalf : forall i, i + 1 < runStageLen ctx stageOf ->
    stageMassOf ctx stageOf (i + 1) <= (1 / 2) * stageMassOf ctx stageOf i
  /-- The K.1 active-window interior condition on the base-stage fibre. -/
  hinterior : ∀ k ∈ runBaseFibre ctx stageOf,
    k + ctx.n24CarryData.r + 1
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card
  /-- The Section 26 count numeric at the canonical dyadic ceiling. -/
  hcount :
    erdos260Constants.c0 * ((runBaseFibre ctx stageOf).card : Real) *
        runDyadicMult ctx
      <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) *
        ((supportShell ctx.d ctx.X).card : Real)

namespace RunClass5LeafSupportDyadicCountResidual

/-- **Sound bridge** — the dyadic-count entry point implies the corrected
max-form residual (the realized max sits below the canonical ceiling). -/
def toSupportMaxCoreResidual {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportDyadicCountResidual ctx) :
    RunClass5LeafSupportMaxCoreResidual ctx where
  stageOf := R.stageOf
  hhalf := R.hhalf
  hproduct := by
    have hc0N : 0 <= erdos260Constants.c0 *
        ((runBaseFibre ctx R.stageOf).card : Real) :=
      mul_nonneg erdos260Constants.c0_pos.le (Nat.cast_nonneg _)
    exact le_trans
      (mul_le_mul_of_nonneg_left
        (runBaseMaxExcess_le_runDyadicMult ctx R.stageOf R.hinterior) hc0N)
      R.hcount

/-- The bridge keeps the actual I.6S stage map. -/
@[simp] theorem toSupportMaxCoreResidual_stageOf {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportDyadicCountResidual ctx) :
    R.toSupportMaxCoreResidual.stageOf = R.stageOf := rfl

/-- The sharp leaf residual from the dyadic-count entry point. -/
def toLeafResidual {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportDyadicCountResidual ctx) :
    RunClass5LeafResidual ctx :=
  R.toSupportMaxCoreResidual.toLeafResidual

/-- The leaf bridge keeps the actual I.6S stage map. -/
@[simp] theorem toLeafResidual_stageOf {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportDyadicCountResidual ctx) :
    R.toLeafResidual.stageOf = R.stageOf := rfl

end RunClass5LeafSupportDyadicCountResidual

/-- **AUDIT — the count form pins the multiplier slot to the full
active-window cap** (consuming the positive-density failure `ctx.hfailure`):
it demands `#runBaseFibre * runDyadicMult <= (cStar*xi/12) * X`.  At the
pinned deep-shell calibration (`r ~ kappa*L`, `g0 = L+B+1`, `T = 2L+1`,
`Y = L/64`) the cap `runDyadicMult ~ kappa*L^2 ~ 64*kappa*L*Y` is a factor
`~ L` above the manuscript's K.1.2/L.20 multiplier, so against the genuine
`#runBaseFibre ~ X/Y` sparsity this demand is a factor-`L` over-claim — the
same deep-shell blow-up audited in `RunLeafUnconditional`/`TowerRunDeepCore`.
Hence the count form is strictly an entry point; the max-form residual is the
honest minimal surface. -/
theorem runSupportDyadicCount_forces_mult_X {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportDyadicCountResidual ctx) :
    ((runBaseFibre ctx R.stageOf).card : Real) * runDyadicMult ctx
      <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) * (ctx.X : Real) := by
  have hA : 0 <= erdos260Constants.cStar * erdos260Constants.ξ / 12 :=
    div_nonneg
      (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
      (by norm_num)
  have hchain : erdos260Constants.c0 *
      (((runBaseFibre ctx R.stageOf).card : Real) * runDyadicMult ctx)
      <= erdos260Constants.c0 *
        ((erdos260Constants.cStar * erdos260Constants.ξ / 12) * (ctx.X : Real)) :=
    calc erdos260Constants.c0 *
            (((runBaseFibre ctx R.stageOf).card : Real) * runDyadicMult ctx)
        = erdos260Constants.c0 * ((runBaseFibre ctx R.stageOf).card : Real) *
            runDyadicMult ctx := by ring
      _ <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) *
            ((supportShell ctx.d ctx.X).card : Real) := R.hcount
      _ <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) *
            (erdos260Constants.c0 * (ctx.X : Real)) :=
          mul_le_mul_of_nonneg_left (le_of_lt ctx.hfailure) hA
      _ = erdos260Constants.c0 *
            ((erdos260Constants.cStar * erdos260Constants.ξ / 12) * (ctx.X : Real)) := by
          ring
  exact le_of_mul_le_mul_left hchain erdos260Constants.c0_pos

/-- The dyadic-count entry point still forces only the LINEAR manuscript
sparsity (through the proved bridge). -/
theorem runSupportDyadicCount_forces_linear_support {ctx : ActualFailureContext}
    (R : RunClass5LeafSupportDyadicCountResidual ctx) :
    erdos260Constants.c0 * ((runBaseFibre ctx R.stageOf).card : Real) *
        ctx.n24CarryData.Y
      <= (erdos260Constants.cStar * erdos260Constants.ξ / 12) *
        ((supportShell ctx.d ctx.X).card : Real) :=
  runSupportMaxCore_forces_linear_support R.toSupportMaxCoreResidual

/-- Family bridge from the dyadic-count entry point to the corrected max-form
residual. -/
def runSupportMaxCoreResidual_ofDyadicCountResidual
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportDyadicCountResidual ctx) :
    forall ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx :=
  fun ctx => (R ctx).toSupportMaxCoreResidual

/-- Family bridge from the dyadic-count entry point to the sharp leaf residual. -/
def runClass5LeafResidual_ofSupportDyadicCountResidual
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportDyadicCountResidual ctx) :
    forall ctx : ActualFailureContext, RunClass5LeafResidual ctx :=
  fun ctx => (R ctx).toLeafResidual

/-- The genuine Run class-5 leaf from the dyadic-count entry point. -/
def runClass5GenuineLeaf_ofSupportDyadicCountResidual
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportDyadicCountResidual ctx) :
    forall ctx : ActualFailureContext, RunClass5GenuineLeaf ctx :=
  runLeafFromResidual (runClass5LeafResidual_ofSupportDyadicCountResidual R)

/-- The I.5.2 run floor obtained from the dyadic-count entry point. -/
theorem runClass5SupportDyadicCountResidual_runFloor
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportDyadicCountResidual ctx)
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      <= erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6 :=
  runLeafFromResidual_runFloor (runClass5LeafResidual_ofSupportDyadicCountResidual R) ctx

/-- Erdős 260 from the dyadic-count entry point plus the P9 routing atom. -/
theorem erdos260_ofSupportDyadicCount_and_highExcess
    (R : forall ctx : ActualFailureContext, RunClass5LeafSupportDyadicCountResidual ctx)
    (he : HighExcessRoutingCountResidual) : Erdos260Statement :=
  erdos260_ofSupportMaxCore_and_highExcess
    (runSupportMaxCoreResidual_ofDyadicCountResidual R) he

/-! ## 9.  Honest status -/

/-- Honest status of the corrected-core pass. -/
def runSupportMaxCoreStatus : List String :=
  [ "NOT FULLY CLOSED - the Run/Class 5 line still carries a genuine residual; no unconditional construction of the corrected max-form residual is possible from the formalised carry data alone (the Section 26 linear sparsity is the manuscript's irreducible positive-density input).",
    "OBSTRUCTION (proved) - the previous minimal residual RunClass5LeafSupportProductCoreResidual quadratically over-claims: its multiplier pin mult := stageMassOf ctx stageOf 0 >= #runBaseFibre * Y forces c0 * (#runBaseFibre)^2 * Y <= (cStar*xi/12) * #supportShell (runSupportProductCore_forces_quadratic_support), (#runBaseFibre)^2 * Y <= (cStar*xi/12) * X (runSupportProductCore_forces_quadratic_X), and #runBaseFibre * routedClassMassOf ... 5 <= cStar*xi*X/6 (runSupportProductCore_forces_card_mul_runFloor) - #runBaseFibre TIMES the I.5.2 run floor. For the genuine I.6S map with #runBaseFibre ~ X/Y the quadratic demand reads X <= (cStar*xi/12)*Y, false in every deep shell; the manuscript witness cannot satisfy the product-core form.",
    "CORRECTED MINIMAL RESIDUAL - RunClass5LeafSupportMaxCoreResidual: stageOf, finite hhalf, and c0 * #runBaseFibre * runBaseMaxExcess <= (cStar*xi/12) * #supportShell, with runBaseMaxExcess the genuine pointwise K.1.2/L.20 multiplier (max charged window excess of the base-stage fibre). It forces only the LINEAR manuscript sparsity c0 * #runBaseFibre * Y <= (cStar*xi/12) * #supportShell (runSupportMaxCore_forces_linear_support).",
    "EQUIVALENCE (proved both ways) - RunClass5LeafSupportMaxCoreResidual.toLeafResidual and RunClass5LeafResidual.toSupportMaxCoreResidual: the corrected core is logically equivalent to the sharp leaf residual RunClass5LeafResidual, hence it is the true minimal surface of the Run/Class 5 atom; the old product-core implies it (toSupportMaxCoreResidual on the product core), so no downstream consumer is lost.",
    "DOWNSTREAM (proved) - runClass5GenuineLeaf_ofSupportMaxCoreResidual, runClass5SupportMaxCoreResidual_runFloor, and erdos260_ofSupportMaxCore_and_highExcess: the genuine leaf, the I.5.2 run floor, and the two-atom capstone all flow from the corrected residual.",
    "CLOSED (dyadic ceiling on the multiplier) - runDyadicG0 = L + carryB Q + 1 and runDyadicMult = max 0 ((r+1)*(L+B+1) - T), all parameters read off ctx; hitGap_le_runDyadicG0_of_window grounds the gap bound in the PROVED HitSequence.hitGap_le_of_shell_window on the actual carry hits; runBaseFibre_windowExcess_le_runDyadicMult and runBaseMaxExcess_le_runDyadicMult cap the genuine pointwise-max multiplier by the canonical matched ceiling under the shared K.1 active-window interior condition (the same boundary residual the class-0/1/3/4 seed closures retain); Y_le_runDyadicMult_of_interior shows the ceiling dominates the active floor on nonempty interior fibres (never a sub-floor stand-in).",
    "ENTRY POINT + AUDIT (dyadic-count form, sufficient but NOT minimal) - RunClass5LeafSupportDyadicCountResidual: stageOf, finite hhalf, the K.1 interior condition, and the ONE scalar numeric c0 * #runBaseFibre * runDyadicMult <= (cStar*xi/12) * #supportShell - no windowExcess quantity left in the interface. Sound bridge toSupportMaxCoreResidual (hence leaf, floor, capstone: erdos260_ofSupportDyadicCount_and_highExcess). AUDIT runSupportDyadicCount_forces_mult_X: the count form demands #runBaseFibre * runDyadicMult <= (cStar*xi/12) * X, pinning the multiplier slot to the full active-window cap - at the pinned deep-shell calibration (r ~ kappa*L, g0 = L+B+1, T = 2L+1, Y = L/64) a factor ~L above the manuscript K.1.2/L.20 multiplier (the deep-shell blow-up audited in RunLeafUnconditional/TowerRunDeepCore). So the count form is strictly an entry point; the max-form residual stays the honest minimal core.",
    "IRREDUCIBLE CORE (unchanged) - the three max-form fields cannot be pinned canonically: stageOf is the genuine shell-dependent I.6S charge partition (the only shell-independent choices are degenerate single-stage maps that collapse hproduct to the harder full-mass bound); hhalf is the genuine L.4.2 nested-support content (the formalized period half-decrease runFOfShell_halfDecrease is at word level, not stage-mass level); and hproduct at the genuine pointwise-max multiplier is the manuscript Section 26 positive-density linear sparsity #runBaseFibre ~ X/Y, not derivable from ctx.hfailure through the formalized chain." ]

theorem runSupportMaxCoreStatus_nonempty : runSupportMaxCoreStatus != [] := by
  simp [runSupportMaxCoreStatus]

/-! ## 10.  Axiom-cleanliness audit -/

#print axioms runBaseMaxExcess
#print axioms windowExcess_le_runBaseMaxExcess
#print axioms runBaseMaxExcess_nonneg
#print axioms runBaseMaxExcess_le_of_pointBound
#print axioms runBaseMaxExcess_le_stageMass
#print axioms runBaseMaxExcess_eq_zero_of_card_eq_zero
#print axioms runBaseFibre_Y_le_windowExcess
#print axioms runBaseFibre_card_mul_Y_le_stageMass
#print axioms runSupportProductCore_classMass_le_two_stageMass
#print axioms runSupportProductCore_forces_quadratic_support
#print axioms runSupportProductCore_forces_quadratic_X
#print axioms runSupportProductCore_forces_card_mul_runFloor
#print axioms runSupportMaxCore_forces_linear_support
#print axioms RunClass5LeafSupportProductCoreResidual.toSupportMaxCoreResidual
#print axioms RunClass5LeafSupportMaxCoreResidual.toLeafResidual
#print axioms RunClass5LeafResidual.toSupportMaxCoreResidual
#print axioms runClass5LeafResidual_ofSupportMaxCoreResidual
#print axioms runSupportMaxCoreResidual_ofLeafResidual
#print axioms runSupportMaxCoreResidual_ofProductCoreResidual
#print axioms runClass5GenuineLeaf_ofSupportMaxCoreResidual
#print axioms runClass5SupportMaxCoreResidual_runFloor
#print axioms erdos260CapstoneFinalResidual_ofSupportMaxCore
#print axioms erdos260_ofSupportMaxCore_and_highExcess
#print axioms runDyadicG0
#print axioms runDyadicMult
#print axioms runDyadicMult_nonneg
#print axioms run_scale_le_runDyadicMult
#print axioms runShellX_pos
#print axioms hitGap_le_runDyadicG0_of_window
#print axioms runBaseFibre_windowExcess_le_runDyadicMult
#print axioms runBaseMaxExcess_le_runDyadicMult
#print axioms Y_le_runDyadicMult_of_interior
#print axioms RunClass5LeafSupportDyadicCountResidual.toSupportMaxCoreResidual
#print axioms RunClass5LeafSupportDyadicCountResidual.toLeafResidual
#print axioms runSupportDyadicCount_forces_mult_X
#print axioms runSupportDyadicCount_forces_linear_support
#print axioms runSupportMaxCoreResidual_ofDyadicCountResidual
#print axioms runClass5LeafResidual_ofSupportDyadicCountResidual
#print axioms runClass5GenuineLeaf_ofSupportDyadicCountResidual
#print axioms runClass5SupportDyadicCountResidual_runFloor
#print axioms erdos260_ofSupportDyadicCount_and_highExcess

end

end Erdos260
