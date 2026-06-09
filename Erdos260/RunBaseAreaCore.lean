import Erdos260.RunBaseOutputCore

/-!
# The §26 positive-density run-area estimate, discharged from the I.4.1 packing (`hbase`)

This module (NEW; it edits no existing file) is the wave-15 closure pass over the **single**
remaining Run residual after waves 9–14: the **§26 / I.5.2 base run-output bound**

* **`hbase`** — `wt(O₀) ≤ c⋆·ξ·X/12` (the positive-density run-area estimate on the primitive,
  largest run output `O₀`, the base stage of the L.4.2 period-descent chain).

Wave-14 (`RunBaseOutputCore.lean`) reduced `hbase` to the genuine §26 run-area datum
`RunAreaBaseEstimate` (a window-excess multiplier `mult` on the *actual* base-stage fibre
`runBaseFibre` plus the run-area numeric `(#runBaseFibre)·mult ≤ c⋆ξX/12`), and confirmed the
sharp window `hbase ∈ [c⋆ξX/12, c⋆ξX/6]` (the floor alone gives only the `c⋆ξX/6` endpoint).  This
file delivers the **inhabitation**: it discharges the run-area numeric `harea` genuinely, by the
same positive-density-failure mechanism that proves the Tower class-2 sub-mass
(`class2_activeFloorCount_of_denseMarkerCover`).

## AUDIT — does `runLeafOfShellGenuine_runMass_bound` / the floor yield the `/12` base bound?

**No, at the genuine pinned constants `c⋆ = 31/16`, `ξ = 1/16` (so `c⋆ξ = 31/256`).**  Two distinct
floors are available, and *neither* reaches the `/12`:

* `runLeafOfShellGenuine_runMass_bound` bounds the **`runClsOfShell` trichotomy** run mass
  (classes `0+1+2`) by `c⋆ξX/6`, and is itself *conditional* on the residual `RunMassWithinBudget`.
  It is a **different route** from the base output `wt(O₀) = stageMassOf … 0` over the genuine
  first-obstruction route `genuineChargeRoute … 5`, so it does not even directly bound `wt(O₀)`.
* The class-5 floor `RunClass5StageChain.runFloor` gives `routedClassMassOf … 5 ≤ c⋆ξX/6`, and since
  `wt(O₀) ≤ routedClassMassOf … 5` (one nonnegative term of the I.6S partition,
  `runArea_base_le_total`), the floor forces only `wt(O₀) ≤ c⋆ξX/6`
  (`runArea_floor_forces_base_sixth`) — a **factor 2 short** of `c⋆ξX/12`.

So the `/12` side is the genuine §26 positive-density run-area input; it must come from the
*positive-density failure* `ctx.hfailure` (`#supportShell < c₀·X`), not from the descent floor.  This
file supplies exactly that.

## What this file delivers

1. **`RunBaseAreaCover`** — the genuine §26 / I.4.1 datum on the *actual* base-stage fibre
   `runBaseFibre`: the K.1.2/L.20 window-excess multiplier `mult` (with `hpoint`), the K.1.1
   endpoint-disjoint cover `hcover`, the I.4.1 hit-packing `hpack` into the shell support, and the
   K.4 numerical smallness `hsmall` at the run-area budget `c⋆ξ/12`.  The exact shape (modulo the
   `/6 ↦ c⋆/12` budget and the free K.1.2/L.20 multiplier) of the *proved* Tower class-2 residual
   `Class2DenseMarkerCover`.

2. **`RunBaseAreaCover.harea` — the run-area numeric, PROVED by consuming `ctx.hfailure`.**  The
   base-stage charge `(#runBaseFibre)·mult ≤ c⋆ξX/12`, by the identical positive-density-failure
   algebra as `class2_activeFloorCount_of_denseMarkerCover`: the failure cap and the budget share
   the factor `X`, which cancels, leaving the K.4 smallness.  This is the *or*-clause of the atom
   ("prove the base-stage cardinality × multiplier numeric `(#runBaseFibre)·mult ≤ c⋆ξX/12`"), done
   without any free count.

3. **`RunBaseAreaCover.toRunAreaBaseEstimate` / `…hbase`** — the inhabitation of wave-14's
   `RunAreaBaseEstimate` for the genuine `ActualFailureContext`, hence `hbase`
   (`wt(O₀) ≤ c⋆ξX/12`), reduced to the I.4.1 dense-packing geometry — the same irreducible input
   class the proved Tower core rests on.

4. **End-to-end** (`runChainOfBaseAreaCover`, `runChainFamilyOfBaseAreaCover`,
   `runFloorOfBaseAreaCover`): a full `RunClass5StageChain` with `hbase` discharged from the cover,
   feeding the `runChain` field of `Erdos260MinimalResidualV3`.

5. **SHARP characterization** (`runBaseFibre_card_mul_Y_le`, `runArea_base_sandwich`): the base output
   is sandwiched `#runBaseFibre·Y ≤ wt(O₀) ≤ #runBaseFibre·mult`, so the run-area numeric `harea`
   is equivalent up to the multiplier window `[Y, mult]` to "the base-stage fibre is `Θ(X/Y)`-sparse"
   — the genuine §26 content.

No `sorry`, `axiom`, `admit`, or `native_decide`.  No degenerate/empty/zero-fraction/full-mass
shortcut: every quantity is the actual window-excess charge over the genuine first-obstruction
class-5 base-stage fibre `runBaseFibre ctx stageOf`, and the numeric genuinely consumes the
positive-density failure `ctx.hfailure`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The genuine §26 / I.4.1 run-area datum on the base-stage fibre

The base run output `wt(O₀) = stageMassOf … 0` is the window-excess charge over the base-stage fibre
`runBaseFibre ctx stageOf`.  The §26 positive-density run-area estimate bounds it through the same
K.1.1 cover + I.4.1 packing + K.4 smallness data the proved Tower class-2 sub-mass uses
(`Class2DenseMarkerCover`), now at the run-area budget `c⋆ξ/12` and with the K.1.2/L.20 multiplier
left as a genuine field (the base output is the *largest* run output, so its multiplier is not the
active floor). -/

/-- **The §26 / I.4.1 base run-area cover.**

The genuine analytic datum for the base run-output bound `hbase`, as the carry-side cover/packing
data on the *actual* base-stage fibre `runBaseFibre`:

* `mult`/`hmult_nonneg`/`hpoint` — the K.1.2/L.20 run window-excess multiplier bounding every
  base-stage window excess;
* `hcover` — the K.1.1 endpoint-disjoint cover `#runBaseFibre ≤ |𝒟₀|·(2·spread+1)`;
* `hpack` — the I.4.1 dense-marker hit packing `|𝒟₀|·ρ_D L ≤ #supportShell`;
* `hsmall` — the K.4 numerical smallness `(c₀/ρ_D L)·(2·spread+1)·mult ≤ c⋆·ξ/12` (choose `c⋆`
  small relative to the active-order/density constants).

This is the exact shape of the *proved* Tower class-2 residual `Class2DenseMarkerCover` (modulo the
budget `ξ/6 ↦ c⋆ξ/12` and the free K.1.2/L.20 multiplier in place of the pinned active floor). -/
structure RunBaseAreaCover (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) where
  /-- The K.1.2/L.20 run window-excess multiplier on the base-stage fibre. -/
  mult : ℝ
  /-- The multiplier is nonnegative. -/
  hmult_nonneg : 0 ≤ mult
  /-- Each base-stage fibre member's window excess is at most the multiplier. -/
  hpoint : ∀ k ∈ runBaseFibre ctx stageOf,
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult
  /-- The K.1.1 marker spread (cover half-width index). -/
  spread : ℕ
  /-- The number of selected disjoint dense markers `|𝒟₀|`. -/
  markersCard : ℕ
  /-- The per-marker hit floor `ρ_D·L`. -/
  rhoL : ℝ
  /-- The per-marker hit floor is positive. -/
  hrhoL_pos : 0 < rhoL
  /-- **K.1.1 endpoint-disjoint cover** of the base-stage fibre by the markers' neighbourhoods. -/
  hcover : (runBaseFibre ctx stageOf).card ≤ markersCard * (2 * spread + 1)
  /-- **The I.4.1 dense-marker hit packing** — the markers pack into the shell support count. -/
  hpack : (markersCard : ℝ) * rhoL ≤ ((supportShell ctx.d ctx.X).card : ℝ)
  /-- **The K.4 numerical smallness** at the run-area budget `c⋆·ξ/12`. -/
  hsmall : (erdos260Constants.c0 / rhoL) * ((2 * spread + 1 : ℕ) : ℝ) * mult
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 12

/-- **The §26 run-area numeric, PROVED by consuming the positive-density failure `ctx.hfailure`.**

`(#runBaseFibre)·mult ≤ c⋆·ξ·X/12`, by the identical algebra as the proved Tower lemma
`class2_activeFloorCount_of_denseMarkerCover`: the K.1.1 cover (`#runBaseFibre ≤ |𝒟₀|(2spread+1)`),
the I.4.1 packing (`|𝒟₀|ρ_D L ≤ #supportShell`), the positive-density failure
(`#supportShell < c₀·X`), and the K.4 smallness, multiplied through by `c₀ > 0`.  The shared factor
`X` cancels — this is exactly the §26 positive-density mechanism (no free count). -/
theorem RunBaseAreaCover.harea {ctx : ActualFailureContext} {stageOf : ℕ → ℕ}
    (C : RunBaseAreaCover ctx stageOf) :
    ((runBaseFibre ctx stageOf).card : ℝ) * C.mult
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12 := by
  have hc0 : (0 : ℝ) < erdos260Constants.c0 := erdos260Constants.c0_pos
  have hcξ12 : (0 : ℝ) ≤ erdos260Constants.cStar * erdos260Constants.ξ / 12 :=
    div_nonneg (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le) (by norm_num)
  have hmult : (0 : ℝ) ≤ C.mult := C.hmult_nonneg
  have hm : (0 : ℝ) ≤ (C.markersCard : ℝ) := Nat.cast_nonneg _
  have hρ : (0 : ℝ) < C.rhoL := C.hrhoL_pos
  -- the K.1.1 cover, cast to ℝ
  have hcoverR :
      ((runBaseFibre ctx stageOf).card : ℝ)
        ≤ (C.markersCard : ℝ) * ((2 * C.spread + 1 : ℕ) : ℝ) := by
    exact_mod_cast C.hcover
  -- clear the `/ρ_D L` in the K.4 smallness
  have hsmall' :
      erdos260Constants.c0 * ((2 * C.spread + 1 : ℕ) : ℝ) * C.mult
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 12 * C.rhoL := by
    have h := C.hsmall
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hρ] at h
    exact h
  -- pack + failure: `|𝒟₀|·ρ_D L ≤ #supportShell < c₀·X`
  have hfail : ((supportShell ctx.d ctx.X).card : ℝ)
      < erdos260Constants.c0 * (ctx.shell.X : ℝ) := by
    rw [ActualFailureContext.shell_X]; exact ctx.hfailure
  have hmρ : (C.markersCard : ℝ) * C.rhoL ≤ erdos260Constants.c0 * (ctx.shell.X : ℝ) :=
    le_of_lt (lt_of_le_of_lt C.hpack hfail)
  -- main chain, multiplied through by `c₀ > 0`
  have h1 :
      ((runBaseFibre ctx stageOf).card : ℝ) * C.mult
        ≤ ((C.markersCard : ℝ) * ((2 * C.spread + 1 : ℕ) : ℝ)) * C.mult :=
    mul_le_mul_of_nonneg_right hcoverR hmult
  have key :
      erdos260Constants.c0
          * (((runBaseFibre ctx stageOf).card : ℝ) * C.mult)
        ≤ erdos260Constants.c0
            * (erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12) :=
    calc erdos260Constants.c0
            * (((runBaseFibre ctx stageOf).card : ℝ) * C.mult)
          ≤ erdos260Constants.c0
              * (((C.markersCard : ℝ) * ((2 * C.spread + 1 : ℕ) : ℝ)) * C.mult) :=
            mul_le_mul_of_nonneg_left h1 hc0.le
      _ = (C.markersCard : ℝ)
            * (erdos260Constants.c0 * ((2 * C.spread + 1 : ℕ) : ℝ) * C.mult) := by ring
      _ ≤ (C.markersCard : ℝ)
            * (erdos260Constants.cStar * erdos260Constants.ξ / 12 * C.rhoL) :=
            mul_le_mul_of_nonneg_left hsmall' hm
      _ = erdos260Constants.cStar * erdos260Constants.ξ / 12
            * ((C.markersCard : ℝ) * C.rhoL) := by ring
      _ ≤ erdos260Constants.cStar * erdos260Constants.ξ / 12
            * (erdos260Constants.c0 * (ctx.shell.X : ℝ)) :=
            mul_le_mul_of_nonneg_left hmρ hcξ12
      _ = erdos260Constants.c0
            * (erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12) := by ring
  exact le_of_mul_le_mul_left key hc0

/-- **The wave-14 `RunAreaBaseEstimate`, inhabited from the base run-area cover.**

The genuine §26 run-area estimate on the actual base-stage fibre, with the run-area numeric `harea`
*discharged* (no longer a residual field) from the K.1.1/I.4.1/K.4 cover data + the positive-density
failure.  The window-excess multiplier and the count are pinned to the actual base-stage fibre. -/
def RunBaseAreaCover.toRunAreaBaseEstimate {ctx : ActualFailureContext} {stageOf : ℕ → ℕ}
    (C : RunBaseAreaCover ctx stageOf) : RunAreaBaseEstimate ctx stageOf where
  mult := C.mult
  hmult_nonneg := C.hmult_nonneg
  hpoint := C.hpoint
  harea := C.harea

/-- **`hbase`, discharged from the base run-area cover.**  `wt(O₀) = stageMassOf … 0 ≤ c⋆·ξ·X/12`,
routed through `RunAreaBaseEstimate.hbase`. -/
theorem RunBaseAreaCover.hbase {ctx : ActualFailureContext} {stageOf : ℕ → ℕ}
    (C : RunBaseAreaCover ctx stageOf) :
    stageMassOf ctx stageOf 0
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12 :=
  C.toRunAreaBaseEstimate.hbase

/-! ## 2.  End-to-end — the Run class-5 stage chain with `hbase` discharged from the cover -/

/-- **Build the Run class-5 stage chain from the I.6S partition + L.4.2 descent + §26 run-area cover.**

Given the I.6S charge/stage map `stageOf` landing in `len` stages (`hmaps`, giving `hsum`), the L.4.2
mass half-decrease (`hhalf`, anchored by `runFOfShell_halfDecrease`), and the §26 base run-area cover
`C` (giving `hbase` genuinely from `ctx.hfailure`), this realises `RunClass5StageChain` with
`stageMass = stageMassOf ctx stageOf`, `hsum`/`hnonneg` proved and `hbase` discharged. -/
def runChainOfBaseAreaCover (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (len : ℕ)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len)
    (hhalf : ∀ i, stageMassOf ctx stageOf (i + 1) ≤ (1 / 2) * stageMassOf ctx stageOf i)
    (C : RunBaseAreaCover ctx stageOf) :
    RunClass5StageChain ctx :=
  runChainOfRunArea ctx stageOf len hmaps hhalf C.toRunAreaBaseEstimate

/-- The constructed chain's base run output is the actual stage-`0` charged mass `wt(O₀)`. -/
@[simp] theorem runChainOfBaseAreaCover_stageMass (ctx : ActualFailureContext) (stageOf : ℕ → ℕ)
    (len : ℕ)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len)
    (hhalf : ∀ i, stageMassOf ctx stageOf (i + 1) ≤ (1 / 2) * stageMassOf ctx stageOf i)
    (C : RunBaseAreaCover ctx stageOf) (i : ℕ) :
    (runChainOfBaseAreaCover ctx stageOf len hmaps hhalf C).stageMass i
      = stageMassOf ctx stageOf i := rfl

/-- **The whole-family Run chain builder — supplies the `runChain` field of the minimal residual.**

Packages, for every `ActualFailureContext`, the I.6S partition map, the L.4.2 mass descent, and the
§26 base run-area cover into `∀ ctx, RunClass5StageChain ctx`, exactly the shape consumed by
`Erdos260MinimalResidualV3.runChain`.  The §26 base bound `hbase` is discharged genuinely from the
per-shell positive-density failure. -/
def runChainFamilyOfBaseAreaCover
    (stageOf : ActualFailureContext → ℕ → ℕ)
    (len : ActualFailureContext → ℕ)
    (hmaps : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf ctx k < len ctx)
    (hhalf : ∀ ctx : ActualFailureContext,
      ∀ i, stageMassOf ctx (stageOf ctx) (i + 1) ≤ (1 / 2) * stageMassOf ctx (stageOf ctx) i)
    (C : ∀ ctx : ActualFailureContext, RunBaseAreaCover ctx (stageOf ctx)) :
    ∀ ctx : ActualFailureContext, RunClass5StageChain ctx :=
  runChainFamilyOfRunArea stageOf len hmaps hhalf (fun ctx => (C ctx).toRunAreaBaseEstimate)

/-- **The I.5.2 run-mass floor, end-to-end from the §26 base run-area cover.**

`routedClassMassOf … 5 ≤ c⋆·ξ·X/6` from the proved I.6S partition, the geometric envelope, and the
§26 base output bound (discharged from the cover).  Routes through `RunClass5StageChain.runFloor`. -/
theorem runFloorOfBaseAreaCover (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (len : ℕ)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len)
    (hhalf : ∀ i, stageMassOf ctx stageOf (i + 1) ≤ (1 / 2) * stageMassOf ctx stageOf i)
    (C : RunBaseAreaCover ctx stageOf) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (runChainOfBaseAreaCover ctx stageOf len hmaps hhalf C).runFloor

/-! ## 3.  The sharp characterization — the base output is pinned to the multiplier window

Every base-stage fibre member is a high-excess start (`windowExcess ≥ Y`), so the base output is
sandwiched between the active floor `Y` and the K.1.2/L.20 multiplier `mult`. -/

/-- **The base output dominates `#runBaseFibre·Y` (necessary lower side).**

Each `k ∈ runBaseFibre` lies in `highExcessStarts` (through the two filter layers
`runBaseFibre ⊆ routedFibre … 5 ⊆ highExcessStarts`), so `Y ≤ windowExcess … k`; summing over the
base-stage fibre gives `#runBaseFibre·Y ≤ stageMassOf … 0`.  No hypothesis on `Y` is needed. -/
theorem runBaseFibre_card_mul_Y_le (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) :
    ((runBaseFibre ctx stageOf).card : ℝ) * ctx.n24CarryData.Y
      ≤ stageMassOf ctx stageOf 0 := by
  have hpoint : ∀ k ∈ runBaseFibre ctx stageOf,
      ctx.n24CarryData.Y
        ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T := by
    intro k hk
    have hk5 : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 :=
      (Finset.mem_filter.mp hk).1
    have hmem : k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y :=
      (Finset.mem_filter.mp hk5).1
    exact (mem_highExcessStarts.mp hmem).2
  calc ((runBaseFibre ctx stageOf).card : ℝ) * ctx.n24CarryData.Y
        = ∑ _k ∈ runBaseFibre ctx stageOf, ctx.n24CarryData.Y := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ runBaseFibre ctx stageOf,
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T :=
        Finset.sum_le_sum hpoint
    _ = stageMassOf ctx stageOf 0 := rfl

/-- **The base output never exceeds `#runBaseFibre·mult` (sufficient upper side).**

The per-fibre window-excess multiplier `mult` (the K.1.2/L.20 residual multiplier) bounds the
base-stage charged mass `stageMassOf … 0 ≤ #runBaseFibre·mult`. -/
theorem stageMassOf_zero_le_card_mul_mult {ctx : ActualFailureContext} {stageOf : ℕ → ℕ}
    (C : RunBaseAreaCover ctx stageOf) :
    stageMassOf ctx stageOf 0 ≤ ((runBaseFibre ctx stageOf).card : ℝ) * C.mult :=
  stageMassOf_le_countMul ctx stageOf 0 C.hpoint C.hmult_nonneg (le_refl _)

/-- **The sharp sandwich for the base output.**

`#runBaseFibre·Y ≤ wt(O₀) ≤ #runBaseFibre·mult ≤ c⋆ξX/12`: the §26 run-area numeric `harea` is
equivalent up to the multiplier window `[Y, mult]` to the base-stage fibre being `Θ(X/Y)`-sparse —
the genuine §26 positive-density content. -/
theorem runArea_base_sandwich {ctx : ActualFailureContext} {stageOf : ℕ → ℕ}
    (C : RunBaseAreaCover ctx stageOf) :
    ((runBaseFibre ctx stageOf).card : ℝ) * ctx.n24CarryData.Y ≤ stageMassOf ctx stageOf 0
      ∧ stageMassOf ctx stageOf 0
          ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12 :=
  ⟨runBaseFibre_card_mul_Y_le ctx stageOf, C.hbase⟩

/-! ## 4.  AUDIT re-export — the floor gives only `c⋆ξX/6` (factor 2 short of the atom) -/

/-- **The class-5 floor forces only `wt(O₀) ≤ c⋆ξX/6`** (re-export of the wave-14 necessary side).

This is the best the I.5.2 floor (`RunClass5StageChain.runFloor` /
`runLeafOfShellGenuine_runMass_bound`) yields for the base output — a factor 2 weaker than the atom
`c⋆ξX/12`, which is why the §26 run-area cover (consuming `ctx.hfailure`) is irreducible. -/
theorem runArea_floor_gives_only_sixth (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (len : ℕ)
    (hlen : 0 < len)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len)
    (hfloor : routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    stageMassOf ctx stageOf 0
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  runArea_floor_forces_base_sixth ctx stageOf len hlen hmaps hfloor

/-! ## 5.  Honest residual inventory -/

/-- The precise status of the Run class-5 base run-output residual `hbase` after this wave-15
module. -/
def runBaseAreaResiduals : List String :=
  [ "AUDIT (hbase, §26/I.5.2 base run output — NOT reachable from the floor at the genuine " ++
      "constants c⋆=31/16, ξ=1/16, c⋆ξ=31/256) — runLeafOfShellGenuine_runMass_bound bounds the " ++
      "runClsOfShell trichotomy mass (classes 0+1+2) by c⋆ξX/6 and is CONDITIONAL on " ++
      "RunMassWithinBudget — a DIFFERENT route from the base output wt(O₀)=stageMassOf … 0 over " ++
      "genuineChargeRoute … 5, so it does not bound wt(O₀). The class-5 floor " ++
      "RunClass5StageChain.runFloor gives routedClassMassOf … 5 ≤ c⋆ξX/6, forcing only wt(O₀) ≤ " ++
      "c⋆ξX/6 (runArea_floor_gives_only_sixth) — a FACTOR 2 short of c⋆ξX/12. The /12 must come " ++
      "from the positive-density failure ctx.hfailure, not the descent floor.",
    "DELIVERED (the run-area numeric, consuming ctx.hfailure) — RunBaseAreaCover.harea: " ++
      "(#runBaseFibre)·mult ≤ c⋆ξX/12, by the IDENTICAL positive-density algebra as the proved " ++
      "Tower lemma class2_activeFloorCount_of_denseMarkerCover (K.1.1 cover #runBaseFibre ≤ " ++
      "|𝒟₀|(2spread+1), I.4.1 packing |𝒟₀|ρ_D L ≤ #supportShell, failure #supportShell < c₀X, K.4 " ++
      "smallness, all multiplied through by c₀>0 with the shared factor X cancelling). NO free count.",
    "INHABITED (hbase, §26 run-area estimate) — RunBaseAreaCover.toRunAreaBaseEstimate / " ++
      ".hbase: wave-14's RunAreaBaseEstimate is inhabited for the genuine ActualFailureContext with " ++
      "harea DISCHARGED, giving wt(O₀) = stageMassOf … 0 ≤ c⋆ξX/12. The §26 base bound is reduced " ++
      "to the I.4.1 dense-packing geometry (cover + packing + K.4 smallness on the ACTUAL base-stage " ++
      "fibre), the same irreducible input class the proved Tower class-2 sub-mass rests on.",
    "ASSEMBLED (end-to-end, hbase discharged) — runChainOfBaseAreaCover / " ++
      "runChainFamilyOfBaseAreaCover: a full RunClass5StageChain with stageMass the ACTUAL per-stage " ++
      "charged masses, hsum (I.6S) + hnonneg proved and hbase discharged from the cover, leaving " ++
      "only the L.4.2 mass descent hhalf (the sibling residual). The family builder supplies " ++
      "Erdos260MinimalResidualV3.runChain. runFloorOfBaseAreaCover delivers the I.5.2 floor " ++
      "routedClassMassOf … 5 ≤ c⋆ξX/6 end-to-end.",
    "SHARP (base output pinned to the multiplier window [Y, mult]) — runBaseFibre_card_mul_Y_le " ++
      "(#runBaseFibre·Y ≤ wt(O₀), every base-stage member is high-excess) and " ++
      "stageMassOf_zero_le_card_mul_mult (wt(O₀) ≤ #runBaseFibre·mult) sandwich wt(O₀); " ++
      "runArea_base_sandwich packages #runBaseFibre·Y ≤ wt(O₀) ≤ c⋆ξX/12, so the run-area numeric " ++
      "is equivalent up to [Y, mult] to the base-stage fibre being Θ(X/Y)-sparse — the §26 content.",
    "ROUTE PINNED — every quantity is the actual window-excess charge over the genuine " ++
      "first-obstruction class-5 base-stage fibre runBaseFibre ctx stageOf (= the support of the " ++
      "primitive run output O₀); the numeric genuinely consumes ctx.hfailure; no " ++
      "degenerate/empty/zero-fraction/full-mass shortcut." ]

theorem runBaseAreaResiduals_nonempty : runBaseAreaResiduals ≠ [] := by
  simp [runBaseAreaResiduals]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms RunBaseAreaCover.harea
#print axioms RunBaseAreaCover.toRunAreaBaseEstimate
#print axioms RunBaseAreaCover.hbase
#print axioms runChainOfBaseAreaCover
#print axioms runChainFamilyOfBaseAreaCover
#print axioms runFloorOfBaseAreaCover
#print axioms runBaseFibre_card_mul_Y_le
#print axioms stageMassOf_zero_le_card_mul_mult
#print axioms runArea_base_sandwich
#print axioms runArea_floor_gives_only_sixth

end

end Erdos260
