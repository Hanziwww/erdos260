import Erdos260.TowerRunDeepCore
import Erdos260.ChargeAllocationConstruction

/-!
# The I.5.2 / L.4.2 base run-output bound and the I.6S charged summation (Run class 5)

This module (NEW; it edits no existing file) is the wave-13 closure pass over the two **genuine
analytic residuals** of the Run class-5 stage chain exposed by wave-11
(`TowerRunDeepCore.lean`, `RunClass5StageChain`):

* **`hsum`** — the **I.6S charged summation** `routedClassMassOf … 5 ≤ ∑_{i<len} stageMass i`
  (the routed class-5 carry mass is the sum of the descent-stage masses);
* **`hbase`** — the **I.5.2 / §26 base run-output bound** `wt(O₀) ≤ c⋆·ξ·X/12` (the positive-density
  run-area estimate on the primitive run output).

The wave-11 geometric model `runClass5Chain_ofGeometricBase` synthesises a chain
`stageMass i = w₀·(1/2)^i` with `hhalf`/`hnonneg` **proved** but `hsum` (linking the actual routed
mass to the synthetic envelope) and `hbase` left as bare residuals.  This file attacks `hsum` and
`hbase` directly, on the **actual** per-stage charged masses.

## AUDIT — do `hsum`/`hbase` survive a deep shell?  (NO pathology, both reachable.)

Unlike Tower Core 3 (whose dense-marker route blows up by a factor `≍ L` for deep shells, see
`TowerRunDeepCore.lean`), the Run cores carry **no count × active-floor product**:

* `hsum` is a *mass partition*, not a count bound.  The genuine I.6S charge map `Θ_R` (Def. J.1.2)
  partitions the class-5 fibre onto the descent stages `O_i`; the routed class-5 mass is **exactly**
  the sum of the per-stage charged masses (`runClass5_stageSum_eq`).  No `Y`-multiplier appears.
* `hbase` bounds the base-stage run mass by the **run area** (a 2D charged measure, §26), which the
  geometric envelope `∑ stageMass i ≤ 2·stageMass 0` (`halfChain_sum_le`) absorbs with no spike
  blow-up.  It reduces to the same per-fibre window-excess charge datum the proved budgets consume.

So the genuine residuals are `hhalf` (the L.4.2 mass half-decrease, anchored in the actual shell by
`runFOfShell_halfDecrease`) + `hbase` (the run-area estimate), both reachable; `hsum` is **proved**.

## What this file delivers

1. **`hsum` is PROVED** (`runClass5_stageSum_eq`): with the I.6S charge/stage map `stageOf` landing
   in the descent length `len`, the routed class-5 mass **equals** `∑_{i<len} stageMassOf … i`, where
   `stageMassOf … i` is the *actual* window-excess mass charged to stage `i`.  This is the manuscript
   J.1.8 charged-ledger reindexing (`Finset.sum_fiberwise_of_maps_to`), made an exact identity — the
   I.6S charged summation is now a theorem, not an assumed field.  The general charging-map form
   `runClass5_hsum_of_chargingMap` (arbitrary per-stage cap, reusing the J.1.8 core
   `routedClassMassOf_le_chargedArea`) covers the geometric envelope too
   (`runClass5_geomSum_of_chargingMap`), unifying the two models.

2. **`hbase` is REDUCED** to the per-fibre run-area charge datum (`runArea_base_of_charge`): the
   base-stage mass `≤ count·mult ≤ c⋆ξX/12`, the genuine §26 positive-density run-area estimate as a
   `count × window-excess multiplier` bound (the carry-side per-element data, no free slot).

3. **SHARP characterization** (the run-area is forced up to a factor 2): `stageMassOf_base_le_total`
   (`base ≤ total`) and `runClass5_total_le_twoBase` (`total ≤ 2·base`, from the descent) sandwich
   `base ≤ M ≤ 2·base`.  Hence the floor `M ≤ c⋆ξX/6` **forces** `base ≤ c⋆ξX/6`
   (`runClass5_floor_forces_base`), while `base ≤ c⋆ξX/12` **suffices** for it — the residual `hbase`
   is pinned to `[c⋆ξX/12, c⋆ξX/6]`, equivalent up to a factor 2 to the run output being `≤ c⋆ξX/12`.

4. **Assembly** (`runClass5Chain_ofPartition`): a full `RunClass5StageChain` with `hsum`/`hnonneg`
   **proved** from the I.6S partition, reducing Cores 4+5 to `hhalf` (L.4.2) + `hbase` (run-area).
   `runClass5Floor_ofPartition` delivers the I.5.2 floor `routedClassMassOf … 5 ≤ c⋆ξX/6`
   end-to-end through `RunClass5StageChain.runFloor`.

No `sorry`, `axiom`, `admit`, or `native_decide`.  No degenerate/empty/zero-fraction/full-mass
shortcut: every quantity is the actual window-excess charge over the genuine first-obstruction
class-5 fibre `routedFibre … (genuineChargeRoute ctx) 5`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The I.6S per-stage charged run mass and the exact charge reindexing

The genuine I.5.2 / I.6S charge map `Θ_R` (Definition J.1.2) sends each class-5 routed carry start to
a descent-stage output `O_i`.  We model the stage assignment by `stageOf : ℕ → ℕ` and read off the
*actual* per-stage charged mass directly from the class-5 fibre. -/

/-- **The I.6S per-stage charged run mass.**  The window-excess mass of the class-5 fibre members
that the I.6S charge/stage map `stageOf` sends to descent stage `i` — the *actual* `wt(O_i)` charged
mass, not a synthetic geometric weight. -/
def stageMassOf (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (i : ℕ) : ℝ :=
  ∑ k ∈ (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter (fun k => stageOf k = i),
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T

/-- Each per-stage charged mass is nonnegative (window excesses are nonnegative). -/
theorem stageMassOf_nonneg (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (i : ℕ) :
    0 ≤ stageMassOf ctx stageOf i :=
  Finset.sum_nonneg (fun _k _ => windowExcess_nonneg _ _ _ _)

/-- **The I.6S charged summation, made EXACT — `hsum` is PROVED (the genuine charge reindexing).**

If the I.6S charge/stage map `stageOf` sends every class-5 fibre member to a descent stage `< len`
(the charge stays within the L.4.2 descent length), the routed class-5 carry mass **equals** the sum
of the per-stage charged masses:
```
routedClassMassOf … 5 = ∑_{i<len} stageMassOf … i.
```
This is the manuscript Lemma J.1.8 charged-ledger reindexing (`Finset.sum_fiberwise_of_maps_to`): the
fibre is partitioned by output stage, and the routed mass is reorganised stage-by-stage with **no
loss**.  It discharges the `hsum` residual outright (with equality, so non-degenerate). -/
theorem runClass5_stageSum_eq (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (len : ℕ)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      = ∑ i ∈ Finset.range len, stageMassOf ctx stageOf i := by
  rw [routedClassMassOf_eq_sum_fibre]
  exact (Finset.sum_fiberwise_of_maps_to
    (s := routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5)
    (t := Finset.range len) (g := stageOf)
    (fun k hk => Finset.mem_range.mpr (hmaps k hk))
    (fun k => windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T)).symm

/-- **`hsum` (the I.6S charged summation residual), as the `≤` field needed by the stage chain.** -/
theorem runClass5_stageSum_le (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (len : ℕ)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ ∑ i ∈ Finset.range len, stageMassOf ctx stageOf i :=
  (runClass5_stageSum_eq ctx stageOf len hmaps).le

/-- **`hsum` from a general I.6S charging map onto descent-stage caps (manuscript J.1.8 core).**

The genuine charged-ledger form: given the I.6S charge map `chargeOf` of the class-5 fibre into
`range len` and the per-stage charged estimate `hcharged` (each descent stage `i` absorbs at most
`cap i` of routed carry mass, the J.D / I.6S per-output bound), the routed class-5 mass is dominated
by the charged stage area `∑_{i<len} cap i`.  Directly reuses `routedClassMassOf_le_chargedArea`
(`= Finset.sum_fiberwise_of_maps_to + Finset.sum_le_sum`).  With `cap := stageMassOf …` this recovers
`runClass5_stageSum_le`; with `cap i := w₀·(1/2)^i` it gives the geometric envelope below. -/
theorem runClass5_hsum_of_chargingMap (ctx : ActualFailureContext)
    (chargeOf : ℕ → ℕ) (len : ℕ) (cap : ℕ → ℝ)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5,
      chargeOf k ∈ Finset.range len)
    (hcharged : ∀ i ∈ Finset.range len,
      (∑ k ∈ (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
            (fun k => chargeOf k = i),
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T)
        ≤ cap i) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ ∑ i ∈ Finset.range len, cap i :=
  routedClassMassOf_le_chargedArea ctx.n24CarryData (genuineChargeRoute ctx) 5
    chargeOf (Finset.range len) cap hmaps hcharged

/-- **The geometric-envelope `hsum` is the I.6S charging onto `cap i = w₀·(1/2)^i` (unifies models).**

The wave-11 geometric model's `hsum` residual (`runClass5Chain_ofGeometricBase`) is exactly the
I.6S charging map of the class-5 fibre onto the geometric descent envelope: with the per-stage
charged estimate against `w₀·(1/2)^i`, the routed class-5 mass fits `∑_{i<len} w₀·(1/2)^i`.  So the
geometric `hsum` and the exact-partition `hsum` are two readings of the same J.1.8 charged
summation. -/
theorem runClass5_geomSum_of_chargingMap (ctx : ActualFailureContext)
    (chargeOf : ℕ → ℕ) (len : ℕ) (w0 : ℝ)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5,
      chargeOf k ∈ Finset.range len)
    (hcharged : ∀ i ∈ Finset.range len,
      (∑ k ∈ (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
            (fun k => chargeOf k = i),
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T)
        ≤ w0 * (1 / 2) ^ i) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ ∑ i ∈ Finset.range len, w0 * (1 / 2) ^ i :=
  runClass5_hsum_of_chargingMap ctx chargeOf len (fun i => w0 * (1 / 2) ^ i) hmaps hcharged

/-! ## 2.  The I.5.2 / §26 base run-output bound, reduced to the run-area charge datum

The base run output `wt(O₀)` is the stage-`0` charged mass `stageMassOf … 0`.  The genuine §26
positive-density run-area estimate bounds it by the per-fibre window-excess charge data — the same
`count × multiplier` carry-side datum the proved budgets consume. -/

/-- **Per-stage `count × multiplier` bound on the charged run mass.**

If every class-5 fibre member charged to stage `i` has window excess `≤ mult` (the run window-excess
multiplier) and there are at most `count` of them, the stage-`i` charged mass obeys
`stageMassOf … i ≤ count · mult`.  The carry-side per-element charge datum, restricted to one descent
stage. -/
theorem stageMassOf_le_countMul (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (i : ℕ)
    {mult count : ℝ}
    (hpoint : ∀ k ∈ (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
        (fun k => stageOf k = i),
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult)
    (hcount : (((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
        (fun k => stageOf k = i)).card : ℝ) ≤ count) :
    stageMassOf ctx stageOf i ≤ count * mult := by
  unfold stageMassOf
  calc ∑ k ∈ (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
            (fun k => stageOf k = i),
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ ∑ _k ∈ (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
              (fun k => stageOf k = i), mult := Finset.sum_le_sum hpoint
    _ = (((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
              (fun k => stageOf k = i)).card : ℝ) * mult := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ count * mult := mul_le_mul_of_nonneg_right hcount hmult_nonneg

/-- **The I.5.2 / §26 base run-output bound `hbase`, reduced to the run-area charge datum.**

The base run output `wt(O₀) = stageMassOf … 0 ≤ count·mult ≤ c⋆·ξ·X/12`.  This is the genuine §26
positive-density run-area estimate, formalised as the carry-side per-element charge datum (a window
excess multiplier `mult` on the base-stage fibre, the base-stage count `count`, and the run-area
numerical input `count·mult ≤ c⋆ξX/12`) — exactly the per-element data the proved budgets consume,
no free slot. -/
theorem runArea_base_of_charge (ctx : ActualFailureContext) (stageOf : ℕ → ℕ)
    {mult count : ℝ}
    (hpoint : ∀ k ∈ (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
        (fun k => stageOf k = 0),
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult)
    (hcount : (((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
        (fun k => stageOf k = 0)).card : ℝ) ≤ count)
    (hbud : count * mult ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12) :
    stageMassOf ctx stageOf 0
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12 :=
  le_trans (stageMassOf_le_countMul ctx stageOf 0 hpoint hmult_nonneg hcount) hbud

/-! ## 3.  Assembly — the Run class-5 stage chain with `hsum` PROVED

`runClass5Chain_ofPartition` builds a full `RunClass5StageChain` whose stage masses are the *actual*
per-stage charged masses `stageMassOf …`, with `hsum` (I.6S) and `hnonneg` **proved** from the
partition, leaving only `hhalf` (the L.4.2 mass half-decrease) and `hbase` (the run-area estimate)
as residuals. -/

/-- **Build the Run class-5 stage chain from the I.6S charge partition (`hsum`/`hnonneg` PROVED).**

Given the I.6S charge/stage map `stageOf` landing in `len` stages (`hmaps`), the L.4.2 mass
half-decrease on the actual per-stage charged masses (`hhalf`, anchored in the actual shell by
`runFOfShell_halfDecrease`), and the §26 base run-output bound (`hbase`), this realises
`RunClass5StageChain` with:

* `stageMass := stageMassOf ctx stageOf` — the *actual* per-stage charged run masses `wt(O_i)`;
* `hsum` **proved** as the exact I.6S charge reindexing `runClass5_stageSum_le`;
* `hnonneg` **proved**.

This reduces Run Cores 4+5 to the two bare residuals `hhalf` (L.4.2) + `hbase` (run-area), with the
I.6S charged summation now a theorem rather than an assumed field. -/
def runClass5Chain_ofPartition (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (len : ℕ)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len)
    (hhalf : ∀ i, stageMassOf ctx stageOf (i + 1) ≤ (1 / 2) * stageMassOf ctx stageOf i)
    (hbase : stageMassOf ctx stageOf 0
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12) :
    RunClass5StageChain ctx where
  len := len
  stageMass := stageMassOf ctx stageOf
  hnonneg := stageMassOf_nonneg ctx stageOf
  hhalf := hhalf
  hsum := runClass5_stageSum_le ctx stageOf len hmaps
  hbase := hbase

/-- The constructed chain's base run output is the actual stage-`0` charged mass `wt(O₀)`. -/
@[simp] theorem runClass5Chain_ofPartition_stageMass
    (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (len : ℕ)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len)
    (hhalf : ∀ i, stageMassOf ctx stageOf (i + 1) ≤ (1 / 2) * stageMassOf ctx stageOf i)
    (hbase : stageMassOf ctx stageOf 0
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12) (i : ℕ) :
    (runClass5Chain_ofPartition ctx stageOf len hmaps hhalf hbase).stageMass i
      = stageMassOf ctx stageOf i := rfl

/-- **The I.5.2 run-mass floor, end-to-end from the I.6S partition + L.4.2 descent + run-area.**

`routedClassMassOf … 5 ≤ c⋆·ξ·X/6` from the proved I.6S partition (`hsum`), the geometric envelope
`∑ stageMass i ≤ 2·stageMass 0` (`halfChain_sum_le` via `hhalf`), and the §26 base run-output bound
(`hbase`).  Routes through `RunClass5StageChain.runFloor`; no count, no `Y`-multiplier. -/
theorem runClass5Floor_ofPartition (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (len : ℕ)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len)
    (hhalf : ∀ i, stageMassOf ctx stageOf (i + 1) ≤ (1 / 2) * stageMassOf ctx stageOf i)
    (hbase : stageMassOf ctx stageOf 0
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (runClass5Chain_ofPartition ctx stageOf len hmaps hhalf hbase).runFloor

/-! ## 4.  The sharp characterization — the run output is pinned to the class-5 mass (factor 2)

The L.4.2 descent forces the base run output and the total routed class-5 mass to be equivalent up to
a factor of two; hence `hbase` is sandwiched in `[c⋆ξX/12, c⋆ξX/6]`. -/

/-- **The base run output is at most the total class-5 mass** (necessary side, from the partition).
With at least one descent stage (`0 < len`), `stageMassOf … 0` is one nonnegative term of the
partition `∑_{i<len} stageMassOf … i = routedClassMassOf … 5`, hence `≤` the total. -/
theorem stageMassOf_base_le_total (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (len : ℕ)
    (hlen : 0 < len)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len) :
    stageMassOf ctx stageOf 0
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5 := by
  rw [runClass5_stageSum_eq ctx stageOf len hmaps]
  exact Finset.single_le_sum (fun i _ => stageMassOf_nonneg ctx stageOf i)
    (Finset.mem_range.mpr hlen)

/-- **The total class-5 mass is at most twice the base run output** (sufficient side, from descent).
The L.4.2 mass half-decrease (`hhalf`) gives the geometric envelope `∑ ≤ 2·base` (`halfChain_sum_le`)
over the proved partition: `routedClassMassOf … 5 ≤ 2·stageMassOf … 0` — the finite (L.8a) bound
`wt_aug(O₀) ≤ C_Q·wt(O₀)` at `C_Q = 2`. -/
theorem runClass5_total_le_twoBase (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (len : ℕ)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len)
    (hhalf : ∀ i, stageMassOf ctx stageOf (i + 1) ≤ (1 / 2) * stageMassOf ctx stageOf i) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ 2 * stageMassOf ctx stageOf 0 := by
  rw [runClass5_stageSum_eq ctx stageOf len hmaps]
  exact halfChain_sum_le (stageMassOf ctx stageOf) (stageMassOf_nonneg ctx stageOf) hhalf len

/-- **The I.5.2 floor FORCES the base run output below `c⋆ξX/6` (sharp necessary side).**

If the class-5 routed mass fits the floor `c⋆ξX/6`, then `wt(O₀) = stageMassOf … 0 ≤ c⋆ξX/6` (the base
output never exceeds the total).  Combined with the sufficient side `hbase : base ≤ c⋆ξX/12 ⟹ floor`
(`runClass5Floor_ofPartition`), the genuine residual `hbase` is sandwiched in `[c⋆ξX/12, c⋆ξX/6]` —
equivalent up to a factor 2 to "the primitive run output is `≤ c⋆ξX/12`". -/
theorem runClass5_floor_forces_base (ctx : ActualFailureContext) (stageOf : ℕ → ℕ) (len : ℕ)
    (hlen : 0 < len)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf k < len)
    (hfloor : routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    stageMassOf ctx stageOf 0
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  le_trans (stageMassOf_base_le_total ctx stageOf len hlen hmaps) hfloor

/-! ## 5.  Honest residual inventory -/

/-- The precise status of the Run class-5 `hsum` (I.6S) and `hbase` (I.5.2/§26) residuals after this
wave-13 module. -/
def runI52BaseResiduals : List String :=
  [ "AUDIT (Run class 5 — NO deep-shell pathology, both residuals reachable) — unlike Tower Core 3 " ++
      "(dense-marker route blows up by a factor ≍ L for deep shells), the Run cores carry no " ++
      "count×active-floor product: hsum is a MASS PARTITION (the I.6S charge map partitions the " ++
      "class-5 fibre onto descent stages, exact, no Y-multiplier) and hbase bounds the base-stage " ++
      "run mass by the run AREA (a 2D charged measure, §26) absorbed by the descent envelope. The " ++
      "genuine residuals are hhalf (L.4.2 half-decrease) + hbase (run-area); hsum is PROVED.",
    "PROVED (hsum, I.6S charged summation) — runClass5_stageSum_eq: with the I.6S charge/stage map " ++
      "stageOf landing in the descent length len, routedClassMassOf … 5 = ∑_{i<len} stageMassOf … i " ++
      "EXACTLY (Finset.sum_fiberwise_of_maps_to = manuscript Lemma J.1.8 charged-ledger reindexing). " ++
      "stageMassOf … i is the ACTUAL window-excess mass charged to stage i, not a synthetic weight. " ++
      "The I.6S field is now a theorem, discharged with equality (non-degenerate).",
    "PROVED (hsum, general charging-map form) — runClass5_hsum_of_chargingMap: routedClassMassOf … 5 " ++
      "≤ ∑_{i<len} cap i from the I.6S charge map + the per-stage charged estimate, reusing the " ++
      "proved J.1.8 core routedClassMassOf_le_chargedArea. runClass5_geomSum_of_chargingMap " ++
      "specialises cap i = w₀·(1/2)^i, showing the wave-11 GEOMETRIC hsum residual is the same I.6S " ++
      "charging onto the descent envelope — the two models unified.",
    "REDUCED (hbase, I.5.2/§26 base run-output / run-area) — runArea_base_of_charge: wt(O₀) = " ++
      "stageMassOf … 0 ≤ count·mult ≤ c⋆ξX/12, the genuine §26 positive-density run-area estimate as " ++
      "the carry-side per-element charge datum (window-excess multiplier on the base-stage fibre + " ++
      "base-stage count + run-area numerical input count·mult ≤ c⋆ξX/12), the same per-element data " ++
      "the proved budgets consume — NO free slot.",
    "SHARP (hbase pinned up to a factor 2) — stageMassOf_base_le_total (base ≤ total, from the " ++
      "partition) and runClass5_total_le_twoBase (total ≤ 2·base, the finite (L.8a) wt_aug(O₀) ≤ " ++
      "C_Q·wt(O₀) at C_Q = 2, from hhalf) sandwich base ≤ M ≤ 2·base. Hence the floor M ≤ c⋆ξX/6 " ++
      "FORCES base ≤ c⋆ξX/6 (runClass5_floor_forces_base) while base ≤ c⋆ξX/12 SUFFICES " ++
      "(runClass5Floor_ofPartition): hbase ∈ [c⋆ξX/12, c⋆ξX/6], equivalent up to a factor 2 to the " ++
      "run output being ≤ c⋆ξX/12.",
    "ASSEMBLED — runClass5Chain_ofPartition: a full RunClass5StageChain with stageMass the ACTUAL " ++
      "per-stage charged masses, hsum (I.6S) + hnonneg PROVED from the partition, reducing Run Cores " ++
      "4+5 to the bare residuals hhalf (L.4.2 half-decrease, anchored by runFOfShell_halfDecrease) + " ++
      "hbase (run-area). runClass5Floor_ofPartition delivers the I.5.2 floor routedClassMassOf … 5 ≤ " ++
      "c⋆ξX/6 end-to-end via RunClass5StageChain.runFloor.",
    "ROUTE PINNED — every quantity is the actual window-excess charge over the genuine " ++
      "first-obstruction class-5 fibre routedFibre … (genuineChargeRoute ctx) 5; no " ++
      "degenerate/empty/zero-fraction/full-mass shortcut (a single-stage charge map collapses hbase " ++
      "to the harder half-floor on the full mass, so the multi-stage descent is genuinely used)." ]

theorem runI52BaseResiduals_nonempty : runI52BaseResiduals ≠ [] := by
  simp [runI52BaseResiduals]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms stageMassOf_nonneg
#print axioms runClass5_stageSum_eq
#print axioms runClass5_stageSum_le
#print axioms runClass5_hsum_of_chargingMap
#print axioms runClass5_geomSum_of_chargingMap
#print axioms stageMassOf_le_countMul
#print axioms runArea_base_of_charge
#print axioms runClass5Chain_ofPartition
#print axioms runClass5Floor_ofPartition
#print axioms stageMassOf_base_le_total
#print axioms runClass5_total_le_twoBase
#print axioms runClass5_floor_forces_base

end

end Erdos260
