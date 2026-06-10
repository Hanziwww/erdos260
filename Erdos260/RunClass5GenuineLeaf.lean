import Erdos260.RunBaseAreaCore

/-!
# The genuine Run class-5 leaf — the sharpest reduction of `runChain`

This module (NEW; it edits no existing file) is the wave-17 closure pass over the Run class-5
period-descent chain `RunClass5StageChain` (`TowerRunMassBoundCore.lean`), i.e. the `runChain` field
of `Erdos260MinimalResidualV3` (`Erdos260UnconditionalSeedClosureV3.lean`):

* `runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx`.

Waves 9–15 reduced the chain to four inputs over the genuine first-obstruction class-5 fibre
`routedFibre … (genuineChargeRoute ctx) 5`: an I.6S charge/stage map `stageOf` with a descent length
`len` and the cover relation `hmaps` (giving `hsum` exactly, `runClass5_stageSum_eq`), the L.4.2 mass
half-decrease `hhalf` (`stageMass (i+1) ≤ stageMass i / 2`), and the §26 positive-density base
run-area bound `hbase` (`wt(O₀) = stageMass 0 ≤ c⋆ξX/12`, discharged from `ctx.hfailure` by
`RunBaseAreaCover.harea`).  This matches the manuscript exactly: Lemma L.4.2 gives `|O_{i+1}| ≤ c|O_i|`
with `c ≤ 1/2` and the descent doubling `wt_aug(O₀) ≤ 2·wt(O₀)` (L.8a), and the §26 run-slot remark
gives `wt(O₀) ≤ C_*ξX/12`, hence `wt_aug(O₀) ≤ C_*ξX/6`.

## What this file delivers (the sharper reduction)

The wave-14/15 builders (`runChainOfRunArea`, `runChainOfBaseAreaCover`) still carry the descent
length `len`, the cover relation `hmaps`, and the *total* half-decrease `∀ i, hhalf`.  Here we
discharge all three of those:

1. **`runStageLen` — the canonical descent length (no free `len`, no free `hmaps`).**  Taking
   `len := (image stageOf over the class-5 fibre).sup id + 1`, the cover relation `hmaps` is
   **proved** (`runStageLen_maps`): every fibre member maps below `len`.  Beyond `len` every charged
   stage mass is `0` (`stageMassOf_eq_zero_of_len_le`), so `hsum` is even an exact partition identity
   at this length (`runClass5_genuine_stageSum_eq`).

2. **`runHalf_total_of_finite` — the half-decrease tail is FREE.**  Only the genuine within-descent
   steps `i+1 < len` need the L.4.2 half-decrease: for `i+1 ≥ len` the next stage mass is `0`, so
   `0 ≤ stageMass i / 2` holds automatically.  Hence the residual `hhalf` shrinks from `∀ i` to the
   finite L.4.2 descent.

3. **`RunClass5GenuineLeaf` — the single genuine remaining input, as one Lean type.**  Bundling the
   I.6S stage map `stageOf`, the finite L.4.2 half-decrease `hhalf`, and the §26 base run-area cover
   `cover : RunBaseAreaCover ctx stageOf`, the full `RunClass5StageChain` is built outright
   (`toChain`), with `len`/`hmaps`/`hsum`/`hnonneg`/`hbase` and the half-decrease tail all
   discharged.  `runChain_of_genuineLeaf` then supplies the `runChain` field for every context.

The chain's stage masses are the **actual** per-stage charged window-excess masses
`stageMassOf ctx stageOf i` (`toChain_stageMass`, by `rfl`), never a synthetic geometric weight — no
degenerate / single-stage / empty-fibre shortcut (a single-stage map collapses `hbase` to the harder
half-floor on the full mass).

## Honest status

**REDUCED**, not closed: the remaining genuine input is `∀ ctx, RunClass5GenuineLeaf ctx`, whose
three fields are exactly the manuscript's irreducible Run class-5 analytic data — the I.6S charge
partition (Def. J.1.2), the L.4.2 nested-support half-decrease, and the §26 positive-density
run-area cover.  No `sorry`, `axiom`, `admit`, or `native_decide`; no degenerate witness is supplied
for any of those fields.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The canonical descent length — `len` and `hmaps` discharged from `stageOf` alone

The class-5 fibre `routedFibre … 5` is finite, so the image of any stage map `stageOf` over it is a
finite set of stage indices.  One more than its supremum is a descent length that covers every fibre
member, so the cover relation `hmaps` becomes a theorem and the higher charged stages vanish. -/

/-- **The canonical L.4.2 descent length of a stage map.**  One more than the largest stage index
that the I.6S charge/stage map `stageOf` assigns to any class-5 fibre member.  Chosen so that the
cover relation `hmaps` holds automatically (`runStageLen_maps`). -/
def runStageLen (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) : ℕ :=
  ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).image stageOf).sup id + 1

/-- **The cover relation `hmaps` is PROVED at the canonical length.**  Every class-5 fibre member is
charged to a descent stage `< runStageLen` — no free `len`, no free `hmaps`. -/
theorem runStageLen_maps (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) :
    ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5,
      stageOf k < runStageLen ctx stageOf := by
  intro k hk
  have hle : stageOf k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).image stageOf).sup id :=
    Finset.le_sup (f := id) (Finset.mem_image_of_mem stageOf hk)
  unfold runStageLen
  omega

/-- **The charged stage masses vanish beyond the canonical descent length.**  For `i ≥ runStageLen`
no class-5 fibre member is charged to stage `i` (they all map strictly below), so the stage-`i`
charged window-excess mass is `0`. -/
theorem stageMassOf_eq_zero_of_len_le (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) {i : ℕ}
    (hi : runStageLen ctx stageOf ≤ i) :
    stageMassOf ctx stageOf i = 0 := by
  have hempty : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
      (fun k => stageOf k = i) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro k hk
    have hlt : stageOf k < runStageLen ctx stageOf := runStageLen_maps ctx stageOf k hk
    omega
  unfold stageMassOf
  rw [hempty, Finset.sum_empty]

/-- **The I.6S charged summation is EXACT at the canonical length** (sanity / non-degeneracy).  At
`len = runStageLen`, the routed class-5 mass equals the sum of the actual per-stage charged masses
with no loss — the manuscript J.1.8 charged-ledger reindexing on the full descent. -/
theorem runClass5_genuine_stageSum_eq (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      = ∑ i ∈ Finset.range (runStageLen ctx stageOf), stageMassOf ctx stageOf i :=
  runClass5_stageSum_eq ctx stageOf (runStageLen ctx stageOf) (runStageLen_maps ctx stageOf)

/-! ## 2.  The half-decrease tail is free — only the genuine L.4.2 descent steps are required

The structural field `RunClass5StageChain.hhalf` is `∀ i, stageMass (i+1) ≤ stageMass i / 2`.  Beyond
the descent length the next stage mass is `0`, so the only steps that carry content are the genuine
L.4.2 shortenings `i+1 < runStageLen`. -/

/-- **Extend the finite L.4.2 half-decrease to all stages.**  Given the genuine mass-level
half-decrease only on the within-descent steps `i+1 < runStageLen` (the manuscript L.4.2 shortenings
`|O_{i+1}| ≤ |O_i|/2`), the total half-decrease `∀ i, stageMass (i+1) ≤ stageMass i / 2` holds: the
out-of-range steps have `stageMass (i+1) = 0 ≤ stageMass i / 2`. -/
theorem runHalf_total_of_finite (ctx : ActualFailureContext) (stageOf : ℕ → ℕ)
    (hhalf : ∀ i, i + 1 < runStageLen ctx stageOf →
      stageMassOf ctx stageOf (i + 1) ≤ (1 / 2) * stageMassOf ctx stageOf i) :
    ∀ i, stageMassOf ctx stageOf (i + 1) ≤ (1 / 2) * stageMassOf ctx stageOf i := by
  intro i
  by_cases h : i + 1 < runStageLen ctx stageOf
  · exact hhalf i h
  · have h0 : stageMassOf ctx stageOf (i + 1) = 0 :=
      stageMassOf_eq_zero_of_len_le ctx stageOf (by omega)
    have hnn : 0 ≤ (1 / 2 : ℝ) * stageMassOf ctx stageOf i :=
      mul_nonneg (by norm_num) (stageMassOf_nonneg ctx stageOf i)
    rw [h0]; linarith

/-! ## 3.  The genuine Run class-5 leaf — the single remaining input, as one Lean type

The three fields below are exactly the manuscript's irreducible Run class-5 analytic data, all over
the genuine first-obstruction class-5 fibre and the actual charged window-excess masses. -/

/-- **The genuine Run class-5 leaf datum.**  The single remaining input of the period-descent chain
`RunClass5StageChain`, after `len`/`hmaps`/`hsum`/`hnonneg`/`hbase`/(half-decrease tail) are all
discharged:

* `stageOf` — the I.6S charge/stage map (Def. J.1.2) sending each class-5 routed carry start to its
  L.4.2 nested-support descent stage `O_i`;
* `hhalf` — the **finite** L.4.2 mass half-decrease, only on the genuine within-descent shortenings
  `i+1 < runStageLen` (`|O_{i+1}| ≤ |O_i|/2`, anchored in the actual shell by
  `runFOfShell_halfDecrease`);
* `cover` — the §26 positive-density base run-area cover on the actual base-stage fibre
  `runBaseFibre ctx stageOf` (`RunBaseAreaCover`: the K.1.1 cover + I.4.1 packing + K.4 smallness),
  discharging `hbase` genuinely from `ctx.hfailure`. -/
structure RunClass5GenuineLeaf (ctx : ActualFailureContext) where
  /-- The I.6S charge/stage map of the class-5 fibre onto the L.4.2 descent stages. -/
  stageOf : ℕ → ℕ
  /-- The finite L.4.2 mass half-decrease on the genuine within-descent shortenings. -/
  hhalf : ∀ i, i + 1 < runStageLen ctx stageOf →
    stageMassOf ctx stageOf (i + 1) ≤ (1 / 2) * stageMassOf ctx stageOf i
  /-- The §26 positive-density base run-area cover (discharges `hbase` from `ctx.hfailure`). -/
  cover : RunBaseAreaCover ctx stageOf

/-- **The full L.4.2 period-descent chain, built from the genuine leaf datum.**  The chain at the
canonical descent length `runStageLen`, with the cover relation `hmaps` proved
(`runStageLen_maps`), the half-decrease completed from the finite data (`runHalf_total_of_finite`),
`hsum`/`hnonneg` proved from the I.6S partition, and `hbase` discharged from the §26 cover. -/
def RunClass5GenuineLeaf.toChain {ctx : ActualFailureContext}
    (G : RunClass5GenuineLeaf ctx) : RunClass5StageChain ctx :=
  runChainOfBaseAreaCover ctx G.stageOf (runStageLen ctx G.stageOf)
    (runStageLen_maps ctx G.stageOf)
    (runHalf_total_of_finite ctx G.stageOf G.hhalf)
    G.cover

/-- The built chain uses the **actual** per-stage charged window-excess masses `wt(O_i)`, never a
synthetic geometric weight (non-degeneracy, by `rfl`). -/
@[simp] theorem RunClass5GenuineLeaf.toChain_stageMass {ctx : ActualFailureContext}
    (G : RunClass5GenuineLeaf ctx) (i : ℕ) :
    G.toChain.stageMass i = stageMassOf ctx G.stageOf i := rfl

/-- The built chain's base run output is the actual base-stage charged mass `wt(O₀)`. -/
@[simp] theorem RunClass5GenuineLeaf.toChain_base {ctx : ActualFailureContext}
    (G : RunClass5GenuineLeaf ctx) :
    G.toChain.stageMass 0 = stageMassOf ctx G.stageOf 0 := rfl

/-! ## 4.  The reduction of `runChain` -/

/-- **The reduction of `runChain`, to the genuine Run class-5 leaf.**

`runChain : ∀ ctx, RunClass5StageChain ctx` is supplied for every context by the genuine leaf datum
`∀ ctx, RunClass5GenuineLeaf ctx`.  This is the sharpest current reduction of the `runChain` field of
`Erdos260MinimalResidualV3`: the only remaining input is the I.6S charge partition + the finite L.4.2
half-decrease + the §26 base run-area cover, all over the genuine first-obstruction class-5 fibre. -/
def runChain_of_genuineLeaf
    (G : ∀ ctx : ActualFailureContext, RunClass5GenuineLeaf ctx) :
    ∀ ctx : ActualFailureContext, RunClass5StageChain ctx :=
  fun ctx => (G ctx).toChain

/-- **The I.5.2 run floor, end-to-end from the genuine leaf.**  `routedClassMassOf … 5 ≤ c⋆ξX/6`
(`wt_aug(O₀) ≤ C_*ξX/6`) via `RunClass5StageChain.runFloor`; no count, no `Y`-multiplier. -/
theorem runFloor_of_genuineLeaf
    (G : ∀ ctx : ActualFailureContext, RunClass5GenuineLeaf ctx)
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (runChain_of_genuineLeaf G ctx).runFloor

/-! ## 5.  Variant — the base bound supplied as the §26 run-area numeric estimate

If a coordinator prefers to supply the base run-output bound directly as the wave-14 run-area numeric
estimate `RunAreaBaseEstimate` (count × multiplier with the numeric `(#runBaseFibre)·mult ≤ c⋆ξX/12`)
rather than as the K.1.1/I.4.1/K.4 cover, the same `len`/`hmaps`/half-tail discharge applies. -/

/-- **The L.4.2 chain from the I.6S stage map + finite L.4.2 half-decrease + §26 run-area estimate.**
Same discharge as `toChain`, with `hbase` taken from the run-area numeric estimate
`RunAreaBaseEstimate ctx stageOf` instead of the cover. -/
def runChain_of_genuineLeafEstimate (ctx : ActualFailureContext) (stageOf : ℕ → ℕ)
    (hhalf : ∀ i, i + 1 < runStageLen ctx stageOf →
      stageMassOf ctx stageOf (i + 1) ≤ (1 / 2) * stageMassOf ctx stageOf i)
    (E : RunAreaBaseEstimate ctx stageOf) :
    RunClass5StageChain ctx :=
  runChainOfRunArea ctx stageOf (runStageLen ctx stageOf)
    (runStageLen_maps ctx stageOf)
    (runHalf_total_of_finite ctx stageOf hhalf)
    E

/-- The estimate-variant chain also uses the actual per-stage charged masses (by `rfl`). -/
@[simp] theorem runChain_of_genuineLeafEstimate_stageMass (ctx : ActualFailureContext)
    (stageOf : ℕ → ℕ)
    (hhalf : ∀ i, i + 1 < runStageLen ctx stageOf →
      stageMassOf ctx stageOf (i + 1) ≤ (1 / 2) * stageMassOf ctx stageOf i)
    (E : RunAreaBaseEstimate ctx stageOf) (i : ℕ) :
    (runChain_of_genuineLeafEstimate ctx stageOf hhalf E).stageMass i
      = stageMassOf ctx stageOf i := rfl

/-! ## 6.  Honest residual inventory -/

/-- The precise status of the Run class-5 `runChain` field after this wave-17 module. -/
def runClass5GenuineLeafResiduals : List String :=
  [ "REDUCED (runChain → RunClass5GenuineLeaf, single Lean type) — runChain_of_genuineLeaf: " ++
      "∀ ctx, RunClass5GenuineLeaf ctx ⟹ ∀ ctx, RunClass5StageChain ctx (the runChain field of " ++
      "Erdos260MinimalResidualV3). The leaf has exactly three genuine fields over the genuine " ++
      "first-obstruction class-5 fibre: stageOf (the I.6S charge/stage map, Def. J.1.2), the FINITE " ++
      "L.4.2 mass half-decrease hhalf (only on within-descent steps i+1 < runStageLen), and the §26 " ++
      "positive-density base run-area cover RunBaseAreaCover ctx stageOf.",
    "DISCHARGED (len + hmaps) — runStageLen / runStageLen_maps: the descent length is the canonical " ++
      "(image stageOf over the class-5 fibre).sup id + 1, so the cover relation hmaps " ++
      "(stageOf k < len for every fibre member) is PROVED, not assumed. The wave-14/15 builders " ++
      "carried len and hmaps as free inputs; here they are gone.",
    "DISCHARGED (hsum, I.6S charged summation EXACT) — runClass5_genuine_stageSum_eq: at the " ++
      "canonical length, routedClassMassOf … 5 = ∑_{i<runStageLen} stageMassOf … i exactly (the " ++
      "J.1.8 charged-ledger reindexing on the full descent, no loss). stageMassOf … i is the ACTUAL " ++
      "window-excess mass charged to stage i.",
    "DISCHARGED (hnonneg) — stageMassOf_nonneg: each charged stage mass is a sum of nonnegative " ++
      "window excesses.",
    "DISCHARGED (half-decrease TAIL) — runHalf_total_of_finite + stageMassOf_eq_zero_of_len_le: " ++
      "beyond the descent length every charged stage mass is 0, so the only steps carrying L.4.2 " ++
      "content are the genuine within-descent shortenings i+1 < runStageLen; the residual hhalf " ++
      "shrinks from ∀ i to the finite L.4.2 descent.",
    "DISCHARGED (hbase, §26 base run output) — via RunBaseAreaCover (cover field): wt(O₀) = " ++
      "stageMassOf … 0 ≤ c⋆ξX/12 is delivered by RunBaseAreaCover.harea, the SAME positive-density " ++
      "algebra (consuming ctx.hfailure: #supportShell < c₀X) that proves the Tower class-2 sub-mass. " ++
      "Matches the §26 run-slot remark wt(O₀) ≤ C_*ξX/12 ⟹ wt_aug(O₀) ≤ C_*ξX/6 (L.8a, C_Q=2).",
    "DELIVERED (the I.5.2 floor) — runFloor_of_genuineLeaf: routedClassMassOf … 5 ≤ c⋆ξX/6 " ++
      "end-to-end via RunClass5StageChain.runFloor (the geometric envelope ∑ stageMass i ≤ " ++
      "2·stageMass 0 absorbs the spikes with NO Y-multiplier; no deep-shell blow-up).",
    "GENUINE REMAINING INPUT (as a Lean type) — ∀ ctx, RunClass5GenuineLeaf ctx, i.e. the I.6S " ++
      "charge partition + the finite L.4.2 nested-support half-decrease + the §26 positive-density " ++
      "run-area cover. NO degenerate witness is supplied (a single-stage map collapses hbase to the " ++
      "harder half-floor on the full mass; an empty-fibre cover forces #runBaseFibre = 0); the leaf " ++
      "fields are the manuscript's irreducible Run class-5 analytic data.",
    "VARIANT (estimate form) — runChain_of_genuineLeafEstimate: same len/hmaps/half-tail discharge, " ++
      "with hbase supplied as the wave-14 run-area numeric estimate RunAreaBaseEstimate " ++
      "((#runBaseFibre)·mult ≤ c⋆ξX/12) instead of the cover." ]

theorem runClass5GenuineLeafResiduals_nonempty : runClass5GenuineLeafResiduals ≠ [] := by
  simp [runClass5GenuineLeafResiduals]

/-! ## 7.  Axiom-cleanliness audit -/

#print axioms runStageLen_maps
#print axioms stageMassOf_eq_zero_of_len_le
#print axioms runClass5_genuine_stageSum_eq
#print axioms runHalf_total_of_finite
#print axioms RunClass5GenuineLeaf.toChain
#print axioms runChain_of_genuineLeaf
#print axioms runFloor_of_genuineLeaf
#print axioms runChain_of_genuineLeafEstimate

end

end Erdos260
