import Erdos260.RunClass5GenuineLeaf

/-!
# The Run class-5 leaf, reduced to its sharpest residual (Appendix L.4 / §26)

This module (NEW; it edits no existing file) is the closure pass over the **Run / Class 5 /
Appendix L.4** analytic atom of `Erdos260CapstoneAssembly`:

* `runLeaf : ∀ ctx : ActualFailureContext, RunClass5GenuineLeaf ctx`.

`RunClass5GenuineLeaf ctx` (`RunClass5GenuineLeaf.lean:151`) is the codebase's sharpest single-Lean-type
core of the Run class-5 period-descent chain (the `runChain` field of `Erdos260MinimalResidualV3`).  Its
three fields are exactly the manuscript's irreducible Run class-5 analytic data, over the genuine
first-obstruction class-5 fibre `routedFibre … (genuineChargeRoute ctx) 5`:

1. **`stageOf : ℕ → ℕ`** — the I.6S charge/stage map (Def. J.1.2), sending each class-5 routed carry
   start to its L.4.2 nested-support descent stage `O_i`;
2. **`hhalf`** — the FINITE L.4.2 nested-support mass half-decrease `wt(O_{i+1}) ≤ wt(O_i)/2`, only on the
   genuine within-descent steps `i + 1 < runStageLen ctx stageOf`;
3. **`cover : RunBaseAreaCover ctx stageOf`** — the §26 positive-density base run-area cover (the `/12`
   base output `wt(O₀) ≤ c⋆ξX/12`).

## Honest determination — which of the three fields are constructible from `ctx.hfailure`?

**None of the three is independently closable; the leaf is a genuine residual.**

* **Field 1 (`stageOf`)** is genuinely shell-dependent geometric data — the I.6S charge partition of the
  *actual* class-5 fibre onto the descent stages.  Fixing it canonically is unsound: the *only*
  shell-independent choices are degenerate.  In particular a single-stage map (`stageOf ≡ 0`) makes
  `runStageLen = 1`, the half-decrease VACUOUS, and `runBaseFibre` the *whole* class-5 fibre — collapsing
  `cover` to the strictly harder full-mass half-floor `routedClassMassOf … 5 ≤ c⋆ξX/12` (forbidden).
* **Field 2 (`hhalf`)** is the genuine L.4.2 nested-support half-decrease; it is true for the genuine
  I.6S map but is not derivable for an arbitrary map.
* **Field 3 (`cover`)** is the hardest and the genuine §26 input.  `RunBaseAreaCore.lean` notes it is
  "irreducible from the descent floor" (the floor forces only `wt(O₀) ≤ c⋆ξX/6`, a factor 2 short,
  `runArea_floor_gives_only_sixth`); the `/12` must come from the positive-density failure `ctx.hfailure`.
  The honest dense-marker route is moreover the **deep-shell-false** apparatus audited in
  `TowerRunDeepCore.lean` (the K.4 smallness `hsmall`, with `mult ≥ Y ≍ εL`, blows up by a factor `≍ L`):
  the genuine §26 sparsity `#runBaseFibre ≲ X/Y` of the base-stage fibre is the manuscript's irreducible
  positive-density analytic input, *not* obtainable from `ctx.hfailure` through the formalised chain.

So the Run class-5 atom is **REDUCED, not closed**, and this file delivers the sharpest reduction.

## What this file delivers

* **`RunBaseAreaCover.ofSupportNumeric`** — the §26 base run-area cover from its sharpest **support-relative
  numeric** form (the spread-0 specialisation: the K.1.1 endpoint-disjoint cover is trivialised — each
  base-stage fibre member is its own marker — leaving exactly the genuine I.4.1 dense-marker hit packing
  `#runBaseFibre · ρ_D L ≤ #supportShell` and the K.4 numerical smallness `(c₀/ρ_D L)·mult ≤ c⋆ξ/12`).
  This is the Run analogue of how the Tower side replaced the four-field `Class2DenseMarkerCover` by the
  sharp count residual (`TowerRunDeepCore.class2_subMass_of_activeFloorCount`): the same support-relative
  bound `12 c₀ · #runBaseFibre · mult ≤ c⋆ξ · #supportShell` that the *general* cover yields
  (`X` cancels via `RunBaseAreaCover.harea`) is here witnessed by an explicit per-hit floor `ρ_D L`.

* **`RunClass5LeafResidual ctx`** — the sharpest per-context Run class-5 residual, bundling the genuine
  I.6S charge map `stageOf`, the FINITE L.4.2 half-decrease `hhalf`, and the §26 base run-area in its
  support-relative numeric form (`mult`/`hpoint`/`rhoL`/`hpack`/`hsmall`).  This drops the three K.1.1
  combinatorial fields (`spread`, `markersCard`, `hcover`) of the full `RunBaseAreaCover` — the sharpest
  honest shape of the Run class-5 leaf.

* **`runLeafFromResidual : (∀ ctx, RunClass5LeafResidual ctx) → (∀ ctx, RunClass5GenuineLeaf ctx)`** — the
  PROVED reduction (the headline `runLeafFromResidual` of the task), building the full §26 cover from the
  support-relative numeric and assembling the genuine leaf for every failure context.  The downstream
  chain `RunClass5GenuineLeaf.toChain → RunClass5StageChain.runFloor → runFactoryOfSlot` then supplies the
  Run factory datum the capstone consumes, end-to-end (`runLeafFromResidual_runFloor`).

* **`runLeafFamilyOfCover`** — the alternative bridge for a coordinator already holding the *full*
  manuscript K.1.1/I.4.1/K.4 dense-marker cover `RunBaseAreaCover` (no reformulation): it feeds the leaf
  directly.

No `sorry`, `axiom`, `admit`, or `native_decide`; no degenerate / empty / vacuous / zero / `PEmpty`
witness and no false hypothesis: every quantity is the actual window-excess charge over the genuine
first-obstruction class-5 base-stage fibre `runBaseFibre ctx stageOf`, the per-hit floor `ρ_D L > 0` is
the genuine I.4.1 density datum, and the packing genuinely consumes the shell support count.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The §26 base run-area cover from its sharpest support-relative numeric form

The full `RunBaseAreaCover` carries the K.1.1 endpoint-disjoint cover (`spread`, `markersCard`,
`hcover`), the I.4.1 hit packing (`hpack`), and the K.4 smallness (`hsmall`).  Setting the cover spread
to `0` (each base-stage fibre member is its own marker, `markersCard := #runBaseFibre`) trivialises the
K.1.1 fields and yields the §26 base run-area cover from the genuine I.4.1 packing + K.4 smallness alone,
both at neighbourhood width `1`.  The resulting support-relative bound is exactly the one the general
cover produces (`RunBaseAreaCover.harea`): `12 c₀ · #runBaseFibre · mult ≤ c⋆ξ · #supportShell`. -/

/-- **The §26 base run-area cover, from the support-relative numeric (spread-0 form).**

The genuine §26 / I.4.1 datum on the base-stage fibre `runBaseFibre`, presented at its sharpest:

* `mult`/`hmult_nonneg`/`hpoint` — the K.1.2/L.20 run window-excess multiplier;
* `rhoL`/`hrhoL_pos` — the genuine per-hit dense-marker floor `ρ_D L > 0`;
* `hpack` — the I.4.1 dense-marker hit packing `#runBaseFibre · ρ_D L ≤ #supportShell` (each base-stage
  member packs its own `ρ_D L` hits into the shell support);
* `hsmall` — the K.4 numerical smallness `(c₀/ρ_D L)·mult ≤ c⋆ξ/12` (at neighbourhood width `1`).

This drops the K.1.1 cover fields `spread`/`markersCard`/`hcover` (set `spread := 0`,
`markersCard := #runBaseFibre`), the Run analogue of the Tower active-floor count shrink. -/
def RunBaseAreaCover.ofSupportNumeric (ctx : ActualFailureContext) (stageOf : ℕ → ℕ)
    (mult : ℝ) (hmult_nonneg : 0 ≤ mult)
    (hpoint : ∀ k ∈ runBaseFibre ctx stageOf,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult)
    (rhoL : ℝ) (hrhoL_pos : 0 < rhoL)
    (hpack : ((runBaseFibre ctx stageOf).card : ℝ) * rhoL
      ≤ ((supportShell ctx.d ctx.X).card : ℝ))
    (hsmall : (erdos260Constants.c0 / rhoL) * mult
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 12) :
    RunBaseAreaCover ctx stageOf where
  mult := mult
  hmult_nonneg := hmult_nonneg
  hpoint := hpoint
  spread := 0
  markersCard := (runBaseFibre ctx stageOf).card
  rhoL := rhoL
  hrhoL_pos := hrhoL_pos
  hcover := by simp
  hpack := by simpa using hpack
  hsmall := by
    have h1 : ((2 * 0 + 1 : ℕ) : ℝ) = 1 := by norm_num
    rw [h1, mul_one]
    exact hsmall

/-- **Sanity — the support-numeric cover delivers the same base output bound `hbase`.**
`wt(O₀) = stageMassOf … 0 ≤ c⋆ξX/12`, via `RunBaseAreaCover.hbase` of the constructed cover. -/
theorem RunBaseAreaCover.ofSupportNumeric_hbase (ctx : ActualFailureContext) (stageOf : ℕ → ℕ)
    (mult : ℝ) (hmult_nonneg : 0 ≤ mult)
    (hpoint : ∀ k ∈ runBaseFibre ctx stageOf,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult)
    (rhoL : ℝ) (hrhoL_pos : 0 < rhoL)
    (hpack : ((runBaseFibre ctx stageOf).card : ℝ) * rhoL
      ≤ ((supportShell ctx.d ctx.X).card : ℝ))
    (hsmall : (erdos260Constants.c0 / rhoL) * mult
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 12) :
    stageMassOf ctx stageOf 0
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12 :=
  (RunBaseAreaCover.ofSupportNumeric ctx stageOf mult hmult_nonneg hpoint rhoL hrhoL_pos
    hpack hsmall).hbase

/-! ## 2.  The sharpest per-context Run class-5 residual -/

/-- **The sharpest Run class-5 leaf residual.**  The single per-context datum that discharges the
genuine Run class-5 leaf `RunClass5GenuineLeaf ctx`, bundling exactly the manuscript's irreducible
Appendix L.4 / §26 data over the genuine first-obstruction class-5 fibre:

* `stageOf` — the I.6S charge/stage map (Def. J.1.2);
* `hhalf` — the FINITE L.4.2 nested-support mass half-decrease, only on the within-descent steps
  `i + 1 < runStageLen ctx stageOf`;
* `mult`/`hmult_nonneg`/`hpoint` — the K.1.2/L.20 run window-excess multiplier on the base-stage fibre;
* `rhoL`/`hrhoL_pos`/`hpack`/`hsmall` — the §26 base run-area in its support-relative numeric form (the
  genuine I.4.1 hit packing + K.4 smallness, K.1.1 trivialised).

Strictly sharper than `RunClass5GenuineLeaf` itself: it drops the three K.1.1 combinatorial cover fields
`spread`/`markersCard`/`hcover` of the full `RunBaseAreaCover`. -/
structure RunClass5LeafResidual (ctx : ActualFailureContext) where
  /-- The I.6S charge/stage map of the class-5 fibre onto the L.4.2 descent stages. -/
  stageOf : ℕ → ℕ
  /-- The FINITE L.4.2 nested-support mass half-decrease on the within-descent shortenings. -/
  hhalf : ∀ i, i + 1 < runStageLen ctx stageOf →
    stageMassOf ctx stageOf (i + 1) ≤ (1 / 2) * stageMassOf ctx stageOf i
  /-- The K.1.2/L.20 run window-excess multiplier on the base-stage fibre. -/
  mult : ℝ
  /-- The multiplier is nonnegative. -/
  hmult_nonneg : 0 ≤ mult
  /-- Each base-stage fibre member's window excess is at most the multiplier. -/
  hpoint : ∀ k ∈ runBaseFibre ctx stageOf,
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult
  /-- The genuine per-hit dense-marker floor `ρ_D L`. -/
  rhoL : ℝ
  /-- The per-hit floor is positive. -/
  hrhoL_pos : 0 < rhoL
  /-- **The I.4.1 dense-marker hit packing** — each base-stage member packs `ρ_D L` hits into the shell
  support count. -/
  hpack : ((runBaseFibre ctx stageOf).card : ℝ) * rhoL
    ≤ ((supportShell ctx.d ctx.X).card : ℝ)
  /-- **The K.4 numerical smallness** at the run-area budget `c⋆·ξ/12` (neighbourhood width `1`). -/
  hsmall : (erdos260Constants.c0 / rhoL) * mult
    ≤ erdos260Constants.cStar * erdos260Constants.ξ / 12

namespace RunClass5LeafResidual

/-- **The §26 base run-area cover of the residual** (spread-0 form). -/
def cover {ctx : ActualFailureContext} (R : RunClass5LeafResidual ctx) :
    RunBaseAreaCover ctx R.stageOf :=
  RunBaseAreaCover.ofSupportNumeric ctx R.stageOf R.mult R.hmult_nonneg R.hpoint
    R.rhoL R.hrhoL_pos R.hpack R.hsmall

/-- **The genuine Run class-5 leaf, from the sharp residual.**  Assembles `RunClass5GenuineLeaf ctx`
from the I.6S charge map, the finite L.4.2 half-decrease, and the §26 base run-area cover built from the
support-relative numeric. -/
def toLeaf {ctx : ActualFailureContext} (R : RunClass5LeafResidual ctx) :
    RunClass5GenuineLeaf ctx where
  stageOf := R.stageOf
  hhalf := R.hhalf
  cover := R.cover

/-- The leaf built from the residual uses the **actual** per-stage charged window-excess masses
`wt(O_i)`, never a synthetic geometric weight (non-degeneracy, by `rfl`). -/
@[simp] theorem toLeaf_stageMass {ctx : ActualFailureContext} (R : RunClass5LeafResidual ctx)
    (i : ℕ) : R.toLeaf.toChain.stageMass i = stageMassOf ctx R.stageOf i := rfl

end RunClass5LeafResidual

/-! ## 3.  The reduction `runLeafFromResidual` -/

/-- **The Run class-5 leaf, reduced to the sharpest residual (the headline reduction).**

`∀ ctx, RunClass5GenuineLeaf ctx` is supplied for every failure context by the sharp residual
`∀ ctx, RunClass5LeafResidual ctx` — the I.6S charge partition + the FINITE L.4.2 nested-support
half-decrease + the §26 base run-area in its support-relative numeric form (K.1.1 combinatorics
trivialised).  This is the genuine remaining Appendix L.4 / §26 analytic input of the Run class-5 atom;
no degenerate witness is supplied. -/
def runLeafFromResidual (R : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx) :
    ∀ ctx : ActualFailureContext, RunClass5GenuineLeaf ctx :=
  fun ctx => (R ctx).toLeaf

/-- **The I.5.2 run floor, end-to-end from the sharp residual.**  `routedClassMassOf … 5 ≤ c⋆ξX/6`
(`wt_aug(O₀) ≤ C_*ξX/6`) via `RunClass5GenuineLeaf.toChain` → `RunClass5StageChain.runFloor`; no count,
no `Y`-multiplier (the geometric envelope absorbs the spikes). -/
theorem runLeafFromResidual_runFloor
    (R : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx) (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  ((runLeafFromResidual R ctx).toChain).runFloor

/-- The reduced family uses the actual per-stage charged masses (by `rfl`). -/
@[simp] theorem runLeafFromResidual_stageMass
    (R : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx) (ctx : ActualFailureContext)
    (i : ℕ) :
    ((runLeafFromResidual R ctx).toChain).stageMass i = stageMassOf ctx (R ctx).stageOf i := rfl

/-! ## 4.  The alternative bridge — from the full manuscript K.1.1/I.4.1/K.4 cover

A coordinator already holding the *full* §26 dense-marker cover (the literal manuscript K.1.1
endpoint-disjoint cover + I.4.1 packing + K.4 smallness, with a non-trivial `spread`) feeds the leaf
directly, with no reformulation. -/

/-- **The genuine Run class-5 leaf, from the I.6S map + finite L.4.2 half-decrease + the FULL §26
dense-marker cover.**  No reformulation of the cover: this is the literal manuscript datum. -/
def runLeafFamilyOfCover
    (stageOf : ActualFailureContext → ℕ → ℕ)
    (hhalf : ∀ ctx : ActualFailureContext, ∀ i, i + 1 < runStageLen ctx (stageOf ctx) →
      stageMassOf ctx (stageOf ctx) (i + 1) ≤ (1 / 2) * stageMassOf ctx (stageOf ctx) i)
    (cover : ∀ ctx : ActualFailureContext, RunBaseAreaCover ctx (stageOf ctx)) :
    ∀ ctx : ActualFailureContext, RunClass5GenuineLeaf ctx :=
  fun ctx => { stageOf := stageOf ctx, hhalf := hhalf ctx, cover := cover ctx }

/-- The full-cover family also delivers the I.5.2 floor end-to-end. -/
theorem runLeafFamilyOfCover_runFloor
    (stageOf : ActualFailureContext → ℕ → ℕ)
    (hhalf : ∀ ctx : ActualFailureContext, ∀ i, i + 1 < runStageLen ctx (stageOf ctx) →
      stageMassOf ctx (stageOf ctx) (i + 1) ≤ (1 / 2) * stageMassOf ctx (stageOf ctx) i)
    (cover : ∀ ctx : ActualFailureContext, RunBaseAreaCover ctx (stageOf ctx))
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  ((runLeafFamilyOfCover stageOf hhalf cover ctx).toChain).runFloor

/-! ## 5.  Honest residual inventory -/

/-- The precise status of the Run / Class 5 / Appendix L.4 atom after this module. -/
def runLeafUnconditionalResiduals : List String :=
  [ "STATUS — REDUCED, not closed. ∀ ctx, RunClass5GenuineLeaf ctx is NOT fully unconditional: its " ++
      "three fields are the manuscript's irreducible Run class-5 analytic data, and the §26 base " ++
      "run-area cover is the genuinely open positive-density input (RunBaseAreaCore.lean:29: " ++
      "'irreducible from the descent floor').",
    "FIELD 1 (stageOf, I.6S charge map, Def. J.1.2) — OPEN (genuine shell-dependent geometric data). " ++
      "No sound shell-independent choice: the only such choices are degenerate (a single-stage map " ++
      "makes hhalf vacuous and collapses the cover to the harder full-mass half-floor).",
    "FIELD 2 (hhalf, FINITE L.4.2 nested-support half-decrease) — OPEN (the genuine L.4.2 content). " ++
      "Already sharpened from ∀ i to i+1 < runStageLen by RunClass5GenuineLeaf (the tail is free, " ++
      "runHalf_total_of_finite); the within-descent shortenings remain genuine.",
    "FIELD 3 (cover, §26 base run-area) — OPEN, the hardest. The descent floor forces only " ++
      "wt(O₀) ≤ c⋆ξX/6 (runArea_floor_gives_only_sixth), a factor 2 short of the /12; the dense-marker " ++
      "route is the deep-shell-false apparatus audited in TowerRunDeepCore (K.4 smallness blows up by " ++
      "≍ L when mult ≥ Y ≍ εL). The genuine §26 sparsity #runBaseFibre ≲ X/Y is the irreducible input.",
    "REDUCED (cover → support-relative numeric) — RunBaseAreaCover.ofSupportNumeric: the §26 cover from " ++
      "the spread-0 form (each base-stage member its own marker), keeping the genuine I.4.1 packing " ++
      "#runBaseFibre·ρ_D L ≤ #supportShell + the K.4 smallness (c₀/ρ_D L)·mult ≤ c⋆ξ/12, dropping the " ++
      "K.1.1 combinatorial fields spread/markersCard/hcover. The Run analogue of the Tower " ++
      "Class2ActiveFloorCount shrink; yields the same support-relative bound as RunBaseAreaCover.harea " ++
      "(X cancels), witnessed by an explicit ρ_D L > 0.",
    "REDUCTION (PROVED) — runLeafFromResidual: (∀ ctx, RunClass5LeafResidual ctx) ⟹ " ++
      "(∀ ctx, RunClass5GenuineLeaf ctx). RunClass5LeafResidual is the sharpest per-context Run class-5 " ++
      "residual (stageOf + finite hhalf + the support-relative §26 numeric), dropping the three K.1.1 " ++
      "fields of the full cover. runLeafFromResidual_runFloor delivers routedClassMassOf … 5 ≤ c⋆ξX/6 " ++
      "end-to-end via RunClass5StageChain.runFloor.",
    "ALTERNATIVE BRIDGE — runLeafFamilyOfCover: for the FULL manuscript K.1.1/I.4.1/K.4 dense-marker " ++
      "cover RunBaseAreaCover (non-trivial spread, no reformulation), feeds the leaf directly.",
    "NON-DEGENERATE — every quantity is the actual window-excess charge over the genuine " ++
      "first-obstruction class-5 base-stage fibre runBaseFibre ctx stageOf; ρ_D L > 0; the packing " ++
      "genuinely consumes #supportShell. No empty/zero/vacuous/full-mass shortcut.",
    "DOWNSTREAM (all PROVED, not residual) — len/hmaps (runStageLen/runStageLen_maps), hsum (I.6S " ++
      "exact partition, runClass5_stageSum_eq), hnonneg (stageMassOf_nonneg), the half-decrease TAIL " ++
      "(runHalf_total_of_finite), and the I.5.2 floor (RunClass5StageChain.runFloor) are discharged by " ++
      "RunClass5GenuineLeaf.toChain — they are NOT residual." ]

theorem runLeafUnconditionalResiduals_nonempty : runLeafUnconditionalResiduals ≠ [] := by
  simp [runLeafUnconditionalResiduals]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms RunBaseAreaCover.ofSupportNumeric
#print axioms RunBaseAreaCover.ofSupportNumeric_hbase
#print axioms RunClass5LeafResidual.toLeaf
#print axioms runLeafFromResidual
#print axioms runLeafFromResidual_runFloor
#print axioms runLeafFamilyOfCover
#print axioms runLeafFamilyOfCover_runFloor

end

end Erdos260
