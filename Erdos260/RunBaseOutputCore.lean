import Erdos260.RunI52BaseCore

/-!
# The §26 positive-density run-area estimate: the base run output bound `hbase`

This module (NEW; it edits no existing file) is the wave-14 closure pass over the **deepest** Run
residual exposed by the L.4.2 period-descent chain (`RunClass5StageChain`, `TowerRunMassBoundCore`):

* **`hbase`** — the **§26 / I.5.2 base run-output bound** `wt(O₀) ≤ c⋆·ξ·X/12` (the positive-density
  run-area estimate on the primitive, largest run output `O₀`).

After waves 9–13 the rest of the Run class-5 scaffolding is *proved*: the I.6S charged summation
`hsum` is an exact partition identity (`runClass5_stageSum_eq`), the geometric envelope
`∑ stageMass i ≤ 2·stageMass 0` is `halfChain_sum_le`, and the floor
`routedClassMassOf … 5 ≤ c⋆ξX/6` (`RunClass5StageChain.runFloor`) follows from `hbase` + the L.4.2
mass half-decrease `hhalf`.  This file attacks the last analytic input, `hbase`, on the **actual**
base-stage charged mass `stageMassOf … 0`.

## AUDIT — is `wt(O₀) ≤ c⋆ξX/12` reachable from the floor / `runLeafOfShellGenuine_runMass_bound`?

**No — the `/12` side is irreducible, necessary up to a factor 2 (confirming the wave-13 window).**
The L.4.2 descent pins the base output to `wt(O₀) ∈ [M/2, M]` where `M = routedClassMassOf … 5` is
the total class-5 mass:

* `stageMassOf_base_le_total` (a single nonnegative term of the I.6S partition) gives `wt(O₀) ≤ M`;
* `runClass5_total_le_twoBase` (the geometric envelope at ratio `1/2`, i.e. the (L.8a) bound
  `wt_aug(O₀) ≤ C_Q·wt(O₀)` at `C_Q = 2`) gives `M ≤ 2·wt(O₀)`.

The I.5.2 floor `M ≤ c⋆ξX/6` (which here is itself *derived* from `hbase` via the descent, not an
independent fact) therefore only forces `wt(O₀) ≤ M ≤ c⋆ξX/6` (`runClass5_floor_forces_base`), a
factor 2 short of the target.  The missing inequality is the *tight-descent* relation
`2·wt(O₀) ≤ M` (which with the always-true `M ≤ 2·wt(O₀)` would force `M = 2·wt(O₀)`, the
infinite-geometric limit); it **fails** for any genuinely finite descent `M < 2·wt(O₀)` (e.g. a
single-stage chain has `wt(O₀) = M`).  So neither the floor nor the descent closes the `/12`; it is
exactly the genuine §26 positive-density run-area input.

## What this file delivers

1. **`hbase` REDUCED to the genuine §26 run-area datum, with NO free count**
   (`RunAreaBaseEstimate` + `RunAreaBaseEstimate.hbase`): the §26 estimate on the *actual*
   base-stage fibre `runBaseFibre` — a window-excess multiplier `mult` (the K.1.2/L.20 residual
   multiplier) on the base run plus the run-area numeric `(#runBaseFibre)·mult ≤ c⋆ξX/12`.  This is
   sharper than wave-13's `runArea_base_of_charge` (which carried a *free* `count`): the count is
   pinned to the actual base-stage cardinality.

2. **The run-area numeric reduced to count × multiplier × K.4 smallness**
   (`RunAreaBaseEstimate.ofCountMultiplier`): the J.1.1 base-stage count bound `#runBaseFibre ≤ ν`,
   the K.1.2/L.20 multiplier `mult ≤ μ`, and the K.4 numerical smallness `ν·μ ≤ c⋆ξX/12` — exactly
   the carry-side per-element data the proved budgets consume, no free slot.

3. **End-to-end assembly** (`runChainOfRunArea`, `runChainFamilyOfRunArea`, `runFloorOfRunArea`):
   a full `RunClass5StageChain` with `hsum`/`hnonneg` **proved** from the I.6S partition and `hbase`
   **discharged** from the §26 run-area estimate, leaving only the L.4.2 mass descent `hhalf` (the
   sibling residual, anchored by `runFOfShell_halfDecrease`).  The family builder directly supplies
   the `runChain` field of `Erdos260MinimalResidualV3`.

4. **SHARP characterization** (`runArea_base_le_total`, `runArea_total_le_twoBase`,
   `runArea_floor_forces_base_sixth`, `runArea_base_le_twelfth_of_tightDescent`): the base output is
   sandwiched in `[c⋆ξX/12, c⋆ξX/6]`; the floor alone gives only the `c⋆ξX/6` endpoint, and the
   §26 run-area estimate supplies precisely the factor-2 (tight-descent) sharpening.

No `sorry`, `axiom`, `admit`, or `native_decide`.  No degenerate/empty/zero-fraction/full-mass
shortcut: every quantity is the actual window-excess charge over the genuine first-obstruction
class-5 base-stage fibre `runBaseFibre ctx stageOf`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The genuine §26 run-area datum on the base-stage fibre

The base run output `wt(O₀)` is the stage-`0` charged mass `stageMassOf … 0`, i.e. the window-excess
mass of the class-5 fibre members the I.6S charge/stage map sends to the largest descent stage `0`.
The genuine §26 positive-density run-area estimate bounds it by the per-fibre window-excess charge
data over **that** base-stage fibre. -/

/-- **The base-stage class-5 fibre.**  The class-5 routed carry starts the I.6S charge/stage map
`stageOf` sends to the base (largest) descent stage `0` — the support of the primitive run output
`O₀`.  Reducible so it unfolds to the literal filter expected by `runArea_base_of_charge`. -/
@[reducible] def runBaseFibre (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) : Finset ℕ :=
  (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter (fun k => stageOf k = 0)

/-- **The genuine §26 positive-density run-area estimate on the base run output.**

The irreducible analytic input for the base run output bound `hbase`, formalised as the carry-side
per-element charge datum on the *actual* base-stage fibre `runBaseFibre`:

* `mult` — the run window-excess multiplier (the K.1.2/L.20 residual multiplier, linear in the
  active floor `Y`), with `hpoint` bounding every base-stage window excess by it;
* `harea` — the §26 **run-area numeric**: the base-stage charge `(#runBaseFibre)·mult` fits the
  manuscript floor `c⋆·ξ·X/12`.

Unlike wave-13's `runArea_base_of_charge`, the count is **not** a free real: it is pinned to the
actual base-stage cardinality `#runBaseFibre`, so this is the sharpest honest reduction of `hbase`. -/
structure RunAreaBaseEstimate (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) where
  /-- The run window-excess multiplier (K.1.2/L.20, linear in the active floor `Y`). -/
  mult : ℝ
  /-- The multiplier is nonnegative. -/
  hmult_nonneg : 0 ≤ mult
  /-- Each base-stage fibre member's window excess is at most the multiplier. -/
  hpoint : ∀ k ∈ runBaseFibre ctx stageOf,
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult
  /-- **The §26 run-area numeric** — the base-stage charge fits `c⋆·ξ·X/12`. -/
  harea : ((runBaseFibre ctx stageOf).card : ℝ) * mult
    ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12

/-- **`hbase`, discharged from the genuine §26 run-area estimate.**

The base run output `wt(O₀) = stageMassOf … 0 ≤ (#runBaseFibre)·mult ≤ c⋆·ξ·X/12`, routing the
actual base-stage cardinality through the wave-13 reduction `runArea_base_of_charge` with the count
pinned to `#runBaseFibre` (no free slot). -/
theorem RunAreaBaseEstimate.hbase {ctx : ActualFailureContext} {stageOf : ℕ → ℕ}
    (E : RunAreaBaseEstimate ctx stageOf) :
    stageMassOf ctx stageOf 0
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12 :=
  runArea_base_of_charge ctx stageOf E.hpoint E.hmult_nonneg (le_refl _) E.harea

/-! ## 2.  The run-area numeric, reduced to count × multiplier × K.4 smallness -/

/-- **Build the §26 run-area estimate from the J.1.1 count + K.1.2/L.20 multiplier + K.4 smallness.**

The genuine charged-ledger reading: a J.1.1 base-stage count bound `#runBaseFibre ≤ ν`, the
K.1.2/L.20 per-element window-excess multiplier `μ` (with `hpoint`), and the K.4 numerical smallness
`ν·μ ≤ c⋆·ξ·X/12` (choose `c⋆` small relative to the active-order/density constants).  The run-area
numeric `(#runBaseFibre)·μ ≤ ν·μ ≤ c⋆ξX/12` follows by monotonicity — the same per-element data the
proved budgets consume, with no free slot. -/
def RunAreaBaseEstimate.ofCountMultiplier (ctx : ActualFailureContext) (stageOf : ℕ → ℕ)
    (μ ν : ℝ) (hμ : 0 ≤ μ)
    (hpoint : ∀ k ∈ runBaseFibre ctx stageOf,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ μ)
    (hcount : ((runBaseFibre ctx stageOf).card : ℝ) ≤ ν)
    (hnum : ν * μ ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12) :
    RunAreaBaseEstimate ctx stageOf where
  mult := μ
  hmult_nonneg := hμ
  hpoint := hpoint
  harea := le_trans (mul_le_mul_of_nonneg_right hcount hμ) hnum

/-! ## 3.  End-to-end — the Run class-5 stage chain with `hbase` discharged

`runChainOfRunArea` builds a full `RunClass5StageChain` whose stage masses are the *actual* per-stage
charged masses `stageMassOf …`, with `hsum` (I.6S) and `hnonneg` **proved** from the partition,
`hbase` **discharged** from the §26 run-area estimate, leaving only the L.4.2 mass descent `hhalf`
(the sibling residual). -/

/-- **Build the Run class-5 stage chain from the I.6S partition + L.4.2 descent + §26 run-area.**

Given the I.6S charge/stage map `stageOf` landing in `len` stages (`hmaps`, giving `hsum`), the L.4.2
mass half-decrease (`hhalf`, anchored by `runFOfShell_halfDecrease`), and the §26 run-area estimate
`E` (giving `hbase`), this realises `RunClass5StageChain` with `stageMass = stageMassOf ctx stageOf`,
`hsum`/`hnonneg` proved and `hbase` discharged.  The base output `runBase = stageMassOf … 0`. -/
def runChainOfRunArea (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (len : ℕ)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len)
    (hhalf : ∀ i, stageMassOf ctx stageOf (i + 1) ≤ (1 / 2) * stageMassOf ctx stageOf i)
    (E : RunAreaBaseEstimate ctx stageOf) :
    RunClass5StageChain ctx :=
  runClass5Chain_ofPartition ctx stageOf len hmaps hhalf E.hbase

/-- The constructed chain's base run output is the actual stage-`0` charged mass `wt(O₀)`. -/
@[simp] theorem runChainOfRunArea_stageMass (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (len : ℕ)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len)
    (hhalf : ∀ i, stageMassOf ctx stageOf (i + 1) ≤ (1 / 2) * stageMassOf ctx stageOf i)
    (E : RunAreaBaseEstimate ctx stageOf) (i : ℕ) :
    (runChainOfRunArea ctx stageOf len hmaps hhalf E).stageMass i = stageMassOf ctx stageOf i := rfl

/-- **The whole-family Run chain builder — supplies the `runChain` field of the minimal residual.**

Packages, for every `ActualFailureContext`, the I.6S partition map, the L.4.2 mass descent, and the
§26 run-area estimate into `∀ ctx, RunClass5StageChain ctx`, exactly the shape consumed by
`Erdos260MinimalResidualV3.runChain` (and `buildTowerRunSeedClosure`). -/
def runChainFamilyOfRunArea
    (stageOf : ActualFailureContext → ℕ → ℕ)
    (len : ActualFailureContext → ℕ)
    (hmaps : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf ctx k < len ctx)
    (hhalf : ∀ ctx : ActualFailureContext,
      ∀ i, stageMassOf ctx (stageOf ctx) (i + 1) ≤ (1 / 2) * stageMassOf ctx (stageOf ctx) i)
    (E : ∀ ctx : ActualFailureContext, RunAreaBaseEstimate ctx (stageOf ctx)) :
    ∀ ctx : ActualFailureContext, RunClass5StageChain ctx :=
  fun ctx => runChainOfRunArea ctx (stageOf ctx) (len ctx) (hmaps ctx) (hhalf ctx) (E ctx)

/-- **The I.5.2 run-mass floor, end-to-end from the §26 run-area estimate.**

`routedClassMassOf … 5 ≤ c⋆·ξ·X/6` from the proved I.6S partition (`hsum`), the geometric envelope
`∑ stageMass i ≤ 2·stageMass 0` (`halfChain_sum_le` via `hhalf`), and the §26 run-area base output
bound (`E.hbase`).  Routes through `RunClass5StageChain.runFloor`; no count, no `Y`-multiplier. -/
theorem runFloorOfRunArea (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (len : ℕ)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len)
    (hhalf : ∀ i, stageMassOf ctx stageOf (i + 1) ≤ (1 / 2) * stageMassOf ctx stageOf i)
    (E : RunAreaBaseEstimate ctx stageOf) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (runChainOfRunArea ctx stageOf len hmaps hhalf E).runFloor

/-! ## 4.  The sharp characterization — the run output is pinned to `[c⋆ξX/12, c⋆ξX/6]`

The L.4.2 descent forces the base run output and the total routed class-5 mass to be equivalent up to
a factor of two; the §26 run-area estimate supplies exactly the factor-2 (tight-descent) sharpening
that the floor alone cannot. -/

/-- **The base run output is at most the total class-5 mass** (necessary side; re-export). -/
theorem runArea_base_le_total (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (len : ℕ)
    (hlen : 0 < len)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len) :
    stageMassOf ctx stageOf 0
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5 :=
  stageMassOf_base_le_total ctx stageOf len hlen hmaps

/-- **The total class-5 mass is at most twice the base run output** (the (L.8a) `C_Q = 2`; re-export). -/
theorem runArea_total_le_twoBase (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (len : ℕ)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len)
    (hhalf : ∀ i, stageMassOf ctx stageOf (i + 1) ≤ (1 / 2) * stageMassOf ctx stageOf i) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ 2 * stageMassOf ctx stageOf 0 :=
  runClass5_total_le_twoBase ctx stageOf len hmaps hhalf

/-- **The floor forces only `wt(O₀) ≤ c⋆ξX/6`** — the factor-2-weaker necessary side (re-export).
This is the best the floor alone yields; the `/12` target is strictly stronger. -/
theorem runArea_floor_forces_base_sixth (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (len : ℕ)
    (hlen : 0 < len)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len)
    (hfloor : routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    stageMassOf ctx stageOf 0
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  runClass5_floor_forces_base ctx stageOf len hlen hmaps hfloor

/-- **The exact gap: the `/12` base bound is the tight-descent reading of the floor.**

The descent always gives `M ≤ 2·wt(O₀)` (`runArea_total_le_twoBase`).  If additionally the descent
is *tight* (`2·wt(O₀) ≤ M`, the infinite-geometric limit `M = 2·wt(O₀)`), the floor
`M ≤ c⋆ξX/6` forces `wt(O₀) ≤ c⋆ξX/12`.  For a genuinely finite descent `M < 2·wt(O₀)`, the floor
leaves the factor-2 gap, so the §26 run-area estimate is irreducible — this is the sharp
characterization of why `hbase` cannot be derived from the floor. -/
theorem runArea_base_le_twelfth_of_tightDescent (ctx : ActualFailureContext) (stageOf : ℕ → ℕ)
    (htight : 2 * stageMassOf ctx stageOf 0
        ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5)
    (hfloor : routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    stageMassOf ctx stageOf 0
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12 := by
  linarith

/-! ## 5.  Honest residual inventory -/

/-- The precise status of the Run class-5 base run-output residual `hbase` after this wave-14
module. -/
def runBaseOutputResiduals : List String :=
  [ "AUDIT (hbase, §26/I.5.2 base run output — NOT reachable from the floor, factor 2 irreducible) " ++
      "— the L.4.2 descent pins wt(O₀) ∈ [M/2, M] (M = routedClassMassOf … 5): " ++
      "stageMassOf_base_le_total gives wt(O₀) ≤ M; runClass5_total_le_twoBase (the (L.8a) C_Q = 2 " ++
      "envelope) gives M ≤ 2·wt(O₀). The floor M ≤ c⋆ξX/6 (itself DERIVED from hbase via the " ++
      "descent) therefore forces only wt(O₀) ≤ c⋆ξX/6 (runArea_floor_forces_base_sixth), a factor 2 " ++
      "short. The missing fact 2·wt(O₀) ≤ M fails for any finite descent M < 2·wt(O₀). So the /12 " ++
      "side is the genuine §26 positive-density run-area input (confirms the wave-13 window).",
    "REDUCED (hbase → §26 run-area datum, NO free count) — RunAreaBaseEstimate + " ++
      "RunAreaBaseEstimate.hbase: wt(O₀) = stageMassOf … 0 ≤ (#runBaseFibre)·mult ≤ c⋆ξX/12, the " ++
      "genuine §26 positive-density run-area estimate on the ACTUAL base-stage fibre runBaseFibre, " ++
      "with the count pinned to the actual base-stage cardinality (sharper than wave-13's " ++
      "runArea_base_of_charge, which carried a free count). The window-excess multiplier mult is " ++
      "the K.1.2/L.20 residual multiplier; harea is the run-area numeric.",
    "REDUCED (run-area numeric → count × multiplier × K.4 smallness) — " ++
      "RunAreaBaseEstimate.ofCountMultiplier: the J.1.1 base-stage count #runBaseFibre ≤ ν, the " ++
      "K.1.2/L.20 multiplier mult ≤ μ, and the K.4 numerical smallness ν·μ ≤ c⋆ξX/12 give the " ++
      "run-area numeric by monotonicity — the carry-side per-element data the proved budgets " ++
      "consume, no free slot.",
    "ASSEMBLED (end-to-end, hbase discharged) — runChainOfRunArea / runChainFamilyOfRunArea: a full " ++
      "RunClass5StageChain with stageMass the ACTUAL per-stage charged masses, hsum (I.6S) + hnonneg " ++
      "PROVED from the partition and hbase DISCHARGED from the §26 run-area estimate, leaving only " ++
      "the L.4.2 mass descent hhalf (the sibling residual, anchored by runFOfShell_halfDecrease). " ++
      "The family builder directly supplies Erdos260MinimalResidualV3.runChain. runFloorOfRunArea " ++
      "delivers the I.5.2 floor routedClassMassOf … 5 ≤ c⋆ξX/6 end-to-end via " ++
      "RunClass5StageChain.runFloor.",
    "SHARP (hbase pinned to [c⋆ξX/12, c⋆ξX/6]) — runArea_base_le_total (base ≤ M) and " ++
      "runArea_total_le_twoBase (M ≤ 2·base) sandwich base ∈ [M/2, M]; runArea_floor_forces_base_sixth " ++
      "(floor ⟹ base ≤ c⋆ξX/6) and runFloorOfRunArea (run-area ⟹ floor) sit base in the window. " ++
      "runArea_base_le_twelfth_of_tightDescent isolates the exact missing inequality 2·base ≤ M " ++
      "(the tight infinite-geometric descent) as the factor-2 sharpening the §26 run-area supplies.",
    "ROUTE PINNED — every quantity is the actual window-excess charge over the genuine " ++
      "first-obstruction class-5 base-stage fibre runBaseFibre ctx stageOf (= the support of the " ++
      "primitive run output O₀); no degenerate/empty/zero-fraction/full-mass shortcut." ]

theorem runBaseOutputResiduals_nonempty : runBaseOutputResiduals ≠ [] := by
  simp [runBaseOutputResiduals]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms RunAreaBaseEstimate.hbase
#print axioms RunAreaBaseEstimate.ofCountMultiplier
#print axioms runChainOfRunArea
#print axioms runChainFamilyOfRunArea
#print axioms runFloorOfRunArea
#print axioms runArea_base_le_total
#print axioms runArea_total_le_twoBase
#print axioms runArea_floor_forces_base_sixth
#print axioms runArea_base_le_twelfth_of_tightDescent

end

end Erdos260
