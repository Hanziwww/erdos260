import Erdos260.DensePackV3Closure
import Erdos260.ChargeCalibrationAuditCore
import Erdos260.CNLMultiChargeUnconditional

/-!
# DensePack scale settlement — the class-3 V3 scalar is a mis-calibrated residual surface;
the corrected (amortized) surface

This module (NEW; it edits no existing file) SETTLES the class-3 ("dense packing") scale
question for the V3/P9 surface and delivers the corrected class-3 residual surface.

## The settled question (Step 1)

The published V3 surface (`P9V3RunResidual.hScale`, `DensePackV3Residue.hScale`,
`DensePackV3WindowFloorResidue.hScale`, `DensePackV3WindowScaleResidue.hScale`,
`DensePackClass3GenuineResidue.floor`) carries the scalar field

```
hScale : ∀ ctx, ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ)
                  − ctx.n24CarryData.T ≤ 1
```

With the canonical pins (all verified here against the actual definitions)
`T = 2L + 1` (`cnlMulti_n24_T_eq`), `densePackDyadicG0 ctx = L + B + 1`
(`densePackDyadicG0_cast_eq`), `1 ≤ B = carryB Q ≤ L` (`carryB_ctx_ge_one`,
`carryB_ctx_le_shellLadderDepth`, from the largeness gate `B + 25 ≤ L`):

* **`r = 0` shells**: the field evaluates to `(L+B+1) − (2L+1) = B − L ≤ 0 ≤ 1` — TRUE
  (`densePack_hScale_holds_of_r_eq_zero`);
* **`r ≥ 1` shells**: `(r+1)(L+B+1) − (2L+1) ≥ 2(L+B+1) − (2L+1) = 2B + 1 ≥ 3 > 1` — the field
  FAILS on EVERY deep shell (`densePack_hScale_fails_of_r_ge_one`);
* hence per shell `hScale-form ↔ r = 0` (`densePack_hScale_iff_r_eq_zero`), and the `r = 0`
  regime is exactly the explicit range `L ≤ 15420` (`n24_r_eq_zero_iff_L_le`, both directions;
  `κ = 17/2^18`);
* so the UNIVERSAL field is exactly as strong as global shallowness:
  `densePack_hScale_universal_iff_all_shallow`.  Any provider of the V3 scale field — in
  particular any `P9V3RunResidual` — forces every hypothetical failing shell to satisfy
  `r = 0`, i.e. `L ≤ 15420` (`p9V3RunResidual_forces_shallow`,
  `p9V3RunResidual_forces_L_le`, and the analogous obstruction theorems for all four
  published class-3 residues).

**Epistemics**: `ActualFailureContext` models a hypothetical failing shell of the global
contradiction argument.  Proving "the field fails at every deep ctx" is a theorem of the model;
it identifies the universal scalar as an over-strong, mis-calibrated residual surface to be
REPAIRED (no honest per-class provider may certify that all failing shells are shallow), not
supplied.  These obstruction theorems are first-class deliverables.

## The corrected scale relation (the repaired calibration)

For any high-excess start whose descent window is interior to the dyadic shell window, the
gap window obeys `T + Y ≤ gapWindow ≤ (r+1)·(L+B+1)` — i.e. the active floor dominates the
threshold PLUS the excess floor, the opposite calibration direction to the broken `≤ T + 1`:

* `highExcess_gapWindow_ge` — `T + Y ≤ gapWindow` (from `Y ≤ windowExcess` and `Y > 0`);
* `densePack_correctedScale_of_window` / `densePack_correctedScale_of_interior` —
  `T + Y ≤ (r+1)·densePackDyadicG0 ctx` (per-gap bound by the PROVED dyadic ceiling
  `hitGap_le_densePackDyadicG0_of_window`).

Consequence (the class-3 shallow-regime closure): on `r = 0` shells the corrected relation is
absurd (`2L+1+Y ≤ L+B+1` contradicts `B ≤ L`, `Y > 0`), so interior dense starts cannot exist —
`genuineDensePackStarts ctx = ∅` and the class-3 fibre is EMPTY
(`genuineDensePackStarts_eq_empty_of_r_eq_zero`, `routedFibre_three_eq_empty_of_r_eq_zero`).
Class 3 has NO exact window-excess pin analogous to class 1's
(`windowExcess_eq_Y_of_mem_class1Fibre`): the classifier `towerClsOfShell` never inspects
`windowExcess`, so on deep shells the class-3 excess is only sandwiched
`Y ≤ windowExcess ≤ positivePart ((r+1)(L+B+1) − T)`.

## The corrected class-3 residual surface (Step 2)

Where the old bridge needs the over-strong scalar: `hDensePack_field_ofCardLe` consumes
`hscale` ONLY through `windowExcess_le_one_on_routedFibre` to get the J.D unit charge
`windowExcess ≤ 1`, so that `mass ≤ card·1 ≤ |densePackPoints| = termDensePack`.  That unit
charge is unavailable on deep shells (the honest per-element cap is
`densePackCorrectedMult ctx = positivePart ((r+1)(L+B+1) − T) ≥ 2B+1 ≥ 3` for `r ≥ 1`,
`densePackCorrectedMult_ge_of_r_ge_one`).  The repaired surface replaces
(count bound + J.D unit charge) by the AMORTIZED cover, faithful to K.1.1/K.1.2 (the marker
charge `ŵt(b) ≤ C_Q·Y·|I_j|` scales with the active floor; it is not a uniform unit):

```
DensePackCorrectedResidue budget :=
  density        : ∀ ctx, densePackEndpointDensity ctx            (K.1.1 coarea hit-density)
  interior       : ∀ ctx, ∀ k ∈ genuineDensePackStarts ctx,
                     k + r + 1 < firstIndexAbove X + K            (K.1 window-interior)
  amortizedCover : ∀ ctx, |genuineDensePackStarts ctx| · densePackCorrectedMult ctx
                     ≤ termDensePack (faithfulCapacityPhases budget ctx)   (corrected K.1.2)
```

Every component is satisfiable on every shell regime — none is false on `r ≥ 1` shells, and on
`r = 0` shells the amortized cover is PROVABLY FREE (`densePackCorrectedMult = 0`,
`amortizedCover_of_r_eq_zero`).  The old residues map INTO the corrected one
(`DensePackCorrectedResidue.ofV3Residue`, `.ofClass3GenuineResidue`) — no strength is lost.

* Bridge: `DensePackCorrectedResidue.hDensePackField` derives the exact class-3 ledger field
  `routedClassMassOf … 3 ≤ termDensePack (faithfulCapacityPhases budget ctx)` consumed by the
  final assembly, via the proved `windowExcess_le_mult_on_routedFibre` +
  `routedClassMassOf_le_countMultiplier` and the amortized cover.  No `hScale`.
* Endpoint: `P9V3CorrectedRunResidual` mirrors `P9V3RunResidual` with the four DensePack
  fields replaced by the corrected residue; `erdos260_p9V3_of_densePackCorrected` reaches
  `Erdos260Statement` through the public ctx-pinned ledger bridge
  (`P9CtxPinnedLedgerResidual.toStatement`), with Chernoff/CNL/TRT/class-6 discharged by the
  same public closers the V3 endpoint uses.  Downstream consumers can now avoid `hScale`.

## Bonus (descent-side density residual)

The `UpperBandMatchSource` period-calibration component `hpb` is the genuinely mixed criterion:
with `spread = L + B + 1`, `hpb ⟺ ord_2(q₀) ≤ B + 3` (`upperBand_periodCalibration_iff`).
`ord_2(7) = 3` (`orderOf_two_zmod_seven`) so the criterion HOLDS at `q₀ = 7` for every `B ≥ 1`;
`ord_2(11) = 10` (`orderOf_two_zmod_eleven`) so it FAILS at `q₀ = 11` whenever `B ≤ 6`
(i.e. `Q < 16`).

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## 1.  Step 1 — the per-regime settlement of the V3 class-3 scalar field

All arithmetic is re-verified here directly against the canonical pins; nothing is assumed
beyond the `rfl`-level parameter pins and the largeness gate. -/

/-- **The V3 class-3 scalar field FAILS on every deep shell (`r ≥ 1`).**
With `T = 2L+1`, `densePackDyadicG0 = L+B+1`, `B ≥ 1`:
`(r+1)(L+B+1) − (2L+1) ≥ 2(L+B+1) − (2L+1) = 2B+1 ≥ 3 > 1`.  This is the exact Lean form of
the `hScale` field of `P9V3RunResidual` / `DensePackV3WindowScaleResidue`. -/
theorem densePack_hScale_fails_of_r_ge_one (ctx : ActualFailureContext)
    (hr : 1 ≤ ctx.n24CarryData.r) :
    ¬ (((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ)
        - ctx.n24CarryData.T ≤ 1) := by
  intro hle
  have hrR : (1 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := by exact_mod_cast hr
  have hBR : (1 : ℝ) ≤ (carryB ctx.shell.Q : ℝ) := by
    exact_mod_cast carryB_ctx_ge_one ctx
  have hLR : (0 : ℝ) ≤ (shellLadderDepth ctx : ℝ) := Nat.cast_nonneg _
  rw [densePackDyadicG0_cast_eq, cnlMulti_n24_T_eq] at hle
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) - 1)
    (by linarith : (0 : ℝ) ≤ (shellLadderDepth ctx : ℝ) + (carryB ctx.shell.Q : ℝ) + 1)]

/-- **The V3 class-3 scalar field HOLDS on every shallow shell (`r = 0`).**
There it evaluates to `(L+B+1) − (2L+1) = B − L ≤ 0 ≤ 1`, by the largeness gate `B ≤ L`. -/
theorem densePack_hScale_holds_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ)
      - ctx.n24CarryData.T ≤ 1 := by
  have hBL : (carryB ctx.shell.Q : ℝ) ≤ (shellLadderDepth ctx : ℝ) := by
    exact_mod_cast carryB_ctx_le_shellLadderDepth ctx
  rw [densePackDyadicG0_cast_eq, cnlMulti_n24_T_eq, hr]
  push_cast
  linarith

/-- **The sharp per-shell verdict**: the V3 class-3 scalar field holds at `ctx` iff the descent
order vanishes. -/
theorem densePack_hScale_iff_r_eq_zero (ctx : ActualFailureContext) :
    (((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ)
        - ctx.n24CarryData.T ≤ 1)
      ↔ ctx.n24CarryData.r = 0 := by
  constructor
  · intro h
    by_contra hne
    exact densePack_hScale_fails_of_r_ge_one ctx (Nat.one_le_iff_ne_zero.mpr hne) h
  · exact densePack_hScale_holds_of_r_eq_zero ctx

/-- **The `r = 0` regime is EXACTLY the explicit shell range `L ≤ 15420`** (both directions;
the sibling `n24_r_eq_zero_of_L_le` is the backward half).  `r = ⌊κL⌋` with `κ = 17/2^18`,
and `17·15420 = 262140 < 262144 = 2^18 < 262157 = 17·15421`. -/
theorem n24_r_eq_zero_iff_L_le (ctx : ActualFailureContext) :
    ctx.n24CarryData.r = 0 ↔ shellLadderDepth ctx ≤ 15420 := by
  constructor
  · intro h
    by_contra hgt
    have h' : 15421 ≤ shellLadderDepth ctx := by omega
    have h15421 : (15421 : ℝ) ≤ (shellLadderDepth ctx : ℝ) := by exact_mod_cast h'
    rw [n24CarryData_r_eq_floor ctx, Nat.floor_eq_zero] at h
    have hk : manuscriptKappa = 17 / 262144 := by
      unfold manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps
      norm_num
    rw [hk] at h
    linarith
  · exact n24_r_eq_zero_of_L_le ctx

/-- The V3 class-3 scalar field holds at `ctx` iff the shell is in the explicit numeral range
`L ≤ 15420`. -/
theorem densePack_hScale_iff_L_le (ctx : ActualFailureContext) :
    (((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ)
        - ctx.n24CarryData.T ≤ 1)
      ↔ shellLadderDepth ctx ≤ 15420 :=
  (densePack_hScale_iff_r_eq_zero ctx).trans (n24_r_eq_zero_iff_L_le ctx)

/-! ### The universal field is exactly global shallowness — the obstruction corollaries -/

/-- **The universal V3 scale field is EQUIVALENT to "every failing shell is shallow".**
This is the precise sense in which the published scalar is over-strong: a universal provider
would certify `r = 0` (equivalently `L ≤ 15420`) on every hypothetical failing shell, which no
honest class-3 estimate can do. -/
theorem densePack_hScale_universal_iff_all_shallow :
    (∀ ctx : ActualFailureContext,
        ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ)
          - ctx.n24CarryData.T ≤ 1)
      ↔ ∀ ctx : ActualFailureContext, ctx.n24CarryData.r = 0 :=
  ⟨fun h ctx => (densePack_hScale_iff_r_eq_zero ctx).mp (h ctx),
    fun h ctx => densePack_hScale_holds_of_r_eq_zero ctx (h ctx)⟩

/-- The universal V3 scale field forces every hypothetical failing shell into the explicit
range `L ≤ 15420`. -/
theorem densePack_hScale_universal_forces_L_le
    (h : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ)
        - ctx.n24CarryData.T ≤ 1) :
    ∀ ctx : ActualFailureContext, shellLadderDepth ctx ≤ 15420 :=
  fun ctx => (densePack_hScale_iff_L_le ctx).mp (h ctx)

/-- **Refutation interface.**  A single failing context with `L > 15420` rules out the universal
published V3 scale field.  This is just the contrapositive form of
`densePack_hScale_universal_forces_L_le`, packaged for audit consumers that need to reject the old
surface rather than derive shallowness from it. -/
theorem not_densePack_hScale_universal_of_deep_ctx
    (ctx : ActualFailureContext) (hdeep : 15420 < shellLadderDepth ctx) :
    ¬ (∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ)
        - ctx.n24CarryData.T ≤ 1) := by
  intro h
  have hle := densePack_hScale_universal_forces_L_le h ctx
  omega

/-- **OBSTRUCTION — any `P9V3RunResidual` forces every failing shell to be shallow.**  Its
`hScale` field is the universal scalar, so it certifies `r = 0` everywhere. -/
theorem p9V3RunResidual_forces_shallow (R : P9V3RunResidual) :
    ∀ ctx : ActualFailureContext, ctx.n24CarryData.r = 0 :=
  fun ctx => (densePack_hScale_iff_r_eq_zero ctx).mp (R.hScale ctx)

/-- Any `P9V3RunResidual` forces every failing shell into the range `L ≤ 15420`. -/
theorem p9V3RunResidual_forces_L_le (R : P9V3RunResidual) :
    ∀ ctx : ActualFailureContext, shellLadderDepth ctx ≤ 15420 :=
  fun ctx => (n24_r_eq_zero_iff_L_le ctx).mp (p9V3RunResidual_forces_shallow R ctx)

/-- **Refutation interface for the old P9/V3 surface.**  If one actual failure context lies above
the shallow range, then the old `P9V3RunResidual` surface cannot be inhabited. -/
theorem not_nonempty_p9V3RunResidual_of_deep_ctx
    (ctx : ActualFailureContext) (hdeep : 15420 < shellLadderDepth ctx) :
    ¬ Nonempty P9V3RunResidual := by
  rintro ⟨R⟩
  have hle := p9V3RunResidual_forces_L_le R ctx
  omega

/-- **OBSTRUCTION — any `DensePackV3Residue` forces every failing shell to be shallow** (its
`floor` field yields the universal scalar through `densePackScaleField_of_floorLe`). -/
theorem densePackV3Residue_forces_shallow
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (R : DensePackV3Residue budget) :
    ∀ ctx : ActualFailureContext, ctx.n24CarryData.r = 0 :=
  fun ctx => (densePack_hScale_iff_r_eq_zero ctx).mp (R.hScale ctx)

/-- **OBSTRUCTION — any `DensePackV3WindowFloorResidue` forces every failing shell shallow.** -/
theorem densePackV3WindowFloorResidue_forces_shallow
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (R : DensePackV3WindowFloorResidue budget) :
    ∀ ctx : ActualFailureContext, ctx.n24CarryData.r = 0 :=
  fun ctx => (densePack_hScale_iff_r_eq_zero ctx).mp (R.hScale ctx)

/-- A deep context rules out the older density/window/floor DensePack V3 residue. -/
theorem not_nonempty_densePackV3Residue_of_deep_ctx
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (ctx : ActualFailureContext) (hdeep : 15420 < shellLadderDepth ctx) :
    ¬ Nonempty (DensePackV3Residue budget) := by
  rintro ⟨R⟩
  have hr := densePackV3Residue_forces_shallow R ctx
  have hle := (n24_r_eq_zero_iff_L_le ctx).mp hr
  omega

/-- A deep context rules out the older window/floor DensePack V3 residue. -/
theorem not_nonempty_densePackV3WindowFloorResidue_of_deep_ctx
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (ctx : ActualFailureContext) (hdeep : 15420 < shellLadderDepth ctx) :
    ¬ Nonempty (DensePackV3WindowFloorResidue budget) := by
  rintro ⟨R⟩
  have hr := densePackV3WindowFloorResidue_forces_shallow R ctx
  have hle := (n24_r_eq_zero_iff_L_le ctx).mp hr
  omega

/-- **OBSTRUCTION — any `DensePackV3WindowScaleResidue` forces every failing shell shallow.** -/
theorem densePackV3WindowScaleResidue_forces_shallow
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (R : DensePackV3WindowScaleResidue budget) :
    ∀ ctx : ActualFailureContext, ctx.n24CarryData.r = 0 :=
  fun ctx => (densePack_hScale_iff_r_eq_zero ctx).mp (R.hScale ctx)

/-- A deep context rules out the older window/scale DensePack V3 residue. -/
theorem not_nonempty_densePackV3WindowScaleResidue_of_deep_ctx
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (ctx : ActualFailureContext) (hdeep : 15420 < shellLadderDepth ctx) :
    ¬ Nonempty (DensePackV3WindowScaleResidue budget) := by
  rintro ⟨R⟩
  have hr := densePackV3WindowScaleResidue_forces_shallow R ctx
  have hle := (n24_r_eq_zero_iff_L_le ctx).mp hr
  omega

/-- **OBSTRUCTION — any `DensePackClass3GenuineResidue` forces every failing shell shallow**
(its K.1.2 `floor` field is the scalar in floor form, `densePackScale_iff_floorLe`). -/
theorem densePackClass3GenuineResidue_forces_shallow
    (R : DensePackClass3GenuineResidue) :
    ∀ ctx : ActualFailureContext, ctx.n24CarryData.r = 0 :=
  fun ctx => (densePack_hScale_iff_r_eq_zero ctx).mp
    ((densePackScale_iff_floorLe ctx).mpr (R.floor ctx))

/-- A deep context rules out the older class-3 genuine residue because its `floor` field is exactly
the published V3 scale surface in floor form. -/
theorem not_nonempty_densePackClass3GenuineResidue_of_deep_ctx
    (ctx : ActualFailureContext) (hdeep : 15420 < shellLadderDepth ctx) :
    ¬ Nonempty DensePackClass3GenuineResidue := by
  rintro ⟨R⟩
  have hr := densePackClass3GenuineResidue_forces_shallow R ctx
  have hle := (n24_r_eq_zero_iff_L_le ctx).mp hr
  omega

/-! ## 2.  The corrected scale relation `T + Y ≤ (r+1) · densePackDyadicG0`

The repaired K.1.2 calibration: on any interior high-excess descent window the active floor
`(r+1)(L+B+1)` dominates `T + Y` — the opposite direction to the broken `≤ T + 1`.  The per-gap
bound is the PROVED dyadic ceiling `hitGap_le_densePackDyadicG0_of_window`; the window lower
bound is the high-excess membership itself. -/

/-- **High-excess starts have `T + Y ≤ gapWindow`.**  Membership gives
`Y ≤ windowExcess = positivePart (gapWindow − T)`, and `Y > 0` rules out the zero branch. -/
theorem highExcess_gapWindow_ge (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y) :
    ctx.n24CarryData.T + ctx.n24CarryData.Y
      ≤ (gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℝ) := by
  have hY : (0 : ℝ) < ctx.n24CarryData.Y := n24CarryData_Y_pos ctx
  have hhe : ctx.n24CarryData.Y
      ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T :=
    (mem_highExcessStarts.mp hk).2
  unfold windowExcess positivePart at hhe
  rcases le_max_iff.mp hhe with h | h
  · linarith
  · linarith

/-- **The corrected scale relation (reach form).**  For a high-excess start `k` whose descent
window `[k, k+r]` stays below `firstIndexAbove X + r₀` for a reach `r₀ + 1 ≤ |supportShell|`,
the proved dyadic gap ceiling gives `T + Y ≤ gapWindow ≤ (r+1)·densePackDyadicG0 ctx`. -/
theorem densePack_correctedScale_of_window (ctx : ActualFailureContext) {k r₀ : ℕ}
    (hk : k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
    (hReach : r₀ + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hwin : k + ctx.n24CarryData.r
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + r₀) :
    ctx.n24CarryData.T + ctx.n24CarryData.Y
      ≤ ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) := by
  have hfwd := highExcess_gapWindow_ge ctx hk
  have hgapj : ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r →
      hitGap ctx.n24CarryData.a j ≤ densePackDyadicG0 ctx := by
    intro j _hkj hjr
    exact hitGap_le_densePackDyadicG0_of_window ctx hReach (by omega)
  have hgw : gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ≤ (ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx :=
    gapWindow_le_of_pointwise_on_range hgapj
  have hgwR : (gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℝ)
      ≤ ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) := by
    calc (gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℝ)
        ≤ (((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx : ℕ) : ℝ) := by
          exact_mod_cast hgw
      _ = ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) := by
          push_cast; ring
  linarith

/-- **The corrected scale relation (interior form).**  For a genuine dense start whose window
is interior (`k + r + 1 < firstIndexAbove X + K`), with the maximal uniform reach `K − 1`. -/
theorem densePack_correctedScale_of_interior (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ genuineDensePackStarts ctx)
    (hinterior : k + ctx.n24CarryData.r + 1
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card) :
    ctx.n24CarryData.T + ctx.n24CarryData.Y
      ≤ ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) := by
  have hhe : k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
      ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y :=
    ((mem_genuineDensePackStarts ctx k).mp hk).1
  have hpos : 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card := one_le_width ctx
  refine densePack_correctedScale_of_window ctx hhe
    (densePackWindowReach_add_one_le ctx) ?_
  show k + ctx.n24CarryData.r
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + ((supportShell ctx.shell.d ctx.shell.X).card - 1)
  omega

/-! ### The shallow-regime class-3 closure: interior dense starts cannot exist at `r = 0`

On `r = 0` shells the corrected relation reads `2L + 1 + Y ≤ L + B + 1`, absurd against
`B ≤ L` and `Y > 0`.  So the window-interior residual forces the class-3 fibre EMPTY on every
shallow shell — the class-3 analogue of the class-1 pin is emptiness, not an excess pin. -/

/-- **`r = 0` shells with interior dense windows have NO genuine dense starts.** -/
theorem genuineDensePackStarts_eq_empty_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hinterior : ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) :
    genuineDensePackStarts ctx = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have hcs := densePack_correctedScale_of_interior ctx hk (hinterior k hk)
  have hY : (0 : ℝ) < ctx.n24CarryData.Y := n24CarryData_Y_pos ctx
  have hBL : (carryB ctx.shell.Q : ℝ) ≤ (shellLadderDepth ctx : ℝ) := by
    exact_mod_cast carryB_ctx_le_shellLadderDepth ctx
  rw [cnlMulti_n24_T_eq, densePackDyadicG0_cast_eq, hr] at hcs
  push_cast at hcs
  linarith

/-- **`r = 0` shells with interior dense windows have an EMPTY class-3 routed fibre** (any
budget routing through the genuine first-obstruction route). -/
theorem routedFibre_three_eq_empty_of_r_eq_zero
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hroute : ∀ ctx : ActualFailureContext, (budget ctx).route = genuineChargeRoute ctx)
    (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hinterior : ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) :
    routedFibre ctx.n24CarryData (budget ctx).route 3 = ∅ := by
  rw [routedFibre_three_eq_densePackStarts hroute ctx]
  exact genuineDensePackStarts_eq_empty_of_r_eq_zero ctx hr hinterior

/-- The faithful class-3 phase term is nonnegative (it is a marker count). -/
theorem termDensePack_faithful_nonneg
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    0 ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData := by
  unfold termDensePack
  exact Nat.cast_nonneg _

/-- **`r = 0` shells: the class-3 ledger field closes OUTRIGHT from the interior residual**
(the routed mass is the empty sum). -/
theorem class3Ledger_of_r_eq_zero
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hroute : ∀ ctx : ActualFailureContext, (budget ctx).route = genuineChargeRoute ctx)
    (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hinterior : ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 3
      ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData := by
  rw [routedClassMassOf_eq_sum_fibre,
    routedFibre_three_eq_empty_of_r_eq_zero budget hroute ctx hr hinterior,
    Finset.sum_empty]
  exact termDensePack_faithful_nonneg budget ctx

/-! ## 3.  The corrected per-element multiplier and the corrected class-3 residual surface -/

/-- **The corrected per-element class-3 charge cap**: the positive part of the active-floor
excess `(r+1)·(L+B+1) − T`.  This is the honest per-element `windowExcess` cap available from
the proved dyadic gap ceiling — `0` on shallow shells, `≥ 2B+1 ≥ 3` on deep shells (so the
J.D unit charge `≤ 1` is exactly the `r = 0` collapse). -/
def densePackCorrectedMult (ctx : ActualFailureContext) : ℝ :=
  positivePart (((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ)
    - ctx.n24CarryData.T)

/-- The corrected multiplier is definitionally the positive part of the audit module's
`activeFloorExcess`. -/
theorem densePackCorrectedMult_eq_posPart_activeFloorExcess (ctx : ActualFailureContext) :
    densePackCorrectedMult ctx = positivePart (activeFloorExcess ctx) := rfl

/-- The corrected multiplier is nonnegative. -/
theorem densePackCorrectedMult_nonneg (ctx : ActualFailureContext) :
    0 ≤ densePackCorrectedMult ctx :=
  positivePart_nonneg _

/-- **Shallow shells: the corrected multiplier vanishes** (`B − L ≤ 0`). -/
theorem densePackCorrectedMult_eq_zero_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    densePackCorrectedMult ctx = 0 := by
  unfold densePackCorrectedMult
  apply positivePart_eq_zero_of_nonpos
  have hBL : (carryB ctx.shell.Q : ℝ) ≤ (shellLadderDepth ctx : ℝ) := by
    exact_mod_cast carryB_ctx_le_shellLadderDepth ctx
  rw [densePackDyadicG0_cast_eq, cnlMulti_n24_T_eq, hr]
  push_cast
  linarith

/-- **Deep shells: the corrected multiplier is at least `2B + 1 ≥ 3`** — the honest gap to the
J.D unit charge that the old `hScale` field papered over. -/
theorem densePackCorrectedMult_ge_of_r_ge_one (ctx : ActualFailureContext)
    (hr : 1 ≤ ctx.n24CarryData.r) :
    2 * (carryB ctx.shell.Q : ℝ) + 1 ≤ densePackCorrectedMult ctx := by
  have hself := self_le_positivePart
    (((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T)
  have hrR : (1 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := by exact_mod_cast hr
  have hBR : (0 : ℝ) ≤ (carryB ctx.shell.Q : ℝ) := Nat.cast_nonneg _
  have hLR : (0 : ℝ) ≤ (shellLadderDepth ctx : ℝ) := Nat.cast_nonneg _
  have hkey : 2 * (carryB ctx.shell.Q : ℝ) + 1
      ≤ ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ)
        - ctx.n24CarryData.T := by
    rw [densePackDyadicG0_cast_eq, cnlMulti_n24_T_eq]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) - 1)
      (by linarith : (0 : ℝ) ≤ (shellLadderDepth ctx : ℝ) + (carryB ctx.shell.Q : ℝ) + 1)]
  exact hkey.trans hself

/-- The corrected multiplier fits a unit charge iff the shell is shallow — the old scalar
field's verdict transfers verbatim to the corrected cap. -/
theorem densePackCorrectedMult_le_one_iff_r_eq_zero (ctx : ActualFailureContext) :
    densePackCorrectedMult ctx ≤ 1 ↔ ctx.n24CarryData.r = 0 := by
  constructor
  · intro h
    by_contra hne
    have h1 := densePackCorrectedMult_ge_of_r_ge_one ctx (Nat.one_le_iff_ne_zero.mpr hne)
    have hB : (1 : ℝ) ≤ (carryB ctx.shell.Q : ℝ) := by
      exact_mod_cast carryB_ctx_ge_one ctx
    linarith
  · intro h
    rw [densePackCorrectedMult_eq_zero_of_r_eq_zero ctx h]
    norm_num

/-- **The corrected class-3 residual surface.**  The three components, each jointly satisfiable
on every shell regime (none is false on `r ≥ 1` shells), faithful to K.1.1/K.1.2:

* `density` — the K.1.1 coarea hit-density at the descent endpoints (unchanged from the
  published surface; budget-independent; gives the endpoint-disjoint count);
* `interior` — the K.1 active-window interior containment for the dense starts (unchanged;
  the boundary term is the `≤ r+1` top starts);
* `amortizedCover` — the CORRECTED K.1.2 calibration: the dense-marker term absorbs the
  class-3 count at the amortized per-element rate `densePackCorrectedMult ctx`
  (`= positivePart ((r+1)(L+B+1) − T)`), replacing the deep-shell-false J.D unit rate.  On
  `r = 0` shells it is provably free (`amortizedCover_of_r_eq_zero`); on deep shells both
  sides scale with the dense geometry. -/
structure DensePackCorrectedResidue
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) where
  /-- K.1.1 coarea hit-density at the descent endpoints (the deep residual). -/
  density : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx
  /-- K.1 active-window interior containment for the dense starts. -/
  interior : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
    k + ctx.n24CarryData.r + 1
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card
  /-- Corrected K.1.2 amortized cover: count × corrected multiplier ≤ marker term. -/
  amortizedCover : ∀ ctx : ActualFailureContext,
    ((genuineDensePackStarts ctx).card : ℝ) * densePackCorrectedMult ctx
      ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData

/-- **The amortized cover is FREE on shallow shells** — at `r = 0` the corrected multiplier is
`0`, so the cover inequality is `0 ≤ termDensePack`.  (Contrast: the old scalar was FALSE on
all deep shells; the corrected component is a tautology on all shallow ones and a genuine,
satisfiable constraint on deep ones.) -/
theorem amortizedCover_of_r_eq_zero
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) (hr : ctx.n24CarryData.r = 0) :
    ((genuineDensePackStarts ctx).card : ℝ) * densePackCorrectedMult ctx
      ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData := by
  rw [densePackCorrectedMult_eq_zero_of_r_eq_zero ctx hr, mul_zero]
  exact termDensePack_faithful_nonneg budget ctx

namespace DensePackCorrectedResidue

variable {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}

/-- Build the corrected residue with the interior component drawn from the shared
`WindowInteriorResidual` (Cores 8/10/13 reuse). -/
def ofWindowInterior
    (density : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx)
    (W : WindowInteriorResidual budget)
    (amortizedCover : ∀ ctx : ActualFailureContext,
      ((genuineDensePackStarts ctx).card : ℝ) * densePackCorrectedMult ctx
        ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData) :
    DensePackCorrectedResidue budget where
  density := density
  interior := W.densePackInterior
  amortizedCover := amortizedCover

/-- Build the corrected residue from a cover hypothesis gated to DEEP shells only — the
shallow case is discharged by `amortizedCover_of_r_eq_zero`. -/
def ofDeepCover
    (density : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx)
    (interior : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card)
    (deepCover : ∀ ctx : ActualFailureContext, 1 ≤ ctx.n24CarryData.r →
      ((genuineDensePackStarts ctx).card : ℝ) * densePackCorrectedMult ctx
        ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData) :
    DensePackCorrectedResidue budget where
  density := density
  interior := interior
  amortizedCover := fun ctx => by
    rcases Nat.eq_zero_or_pos ctx.n24CarryData.r with hr | hr
    · exact amortizedCover_of_r_eq_zero budget ctx hr
    · exact deepCover ctx hr

/-- **The K.1.1 endpoint-disjoint count** (same as the published surface — the corrected
residue loses nothing of the old count API). -/
theorem densePackCount (R : DensePackCorrectedResidue budget) :
    ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card ≤ (densePackMarkers budget ctx).card :=
  densePackCount_ofEndpointDensity budget R.density

/-- The corrected residue keeps the maximal V3 reach `K − 1`. -/
abbrev windowReach (_R : DensePackCorrectedResidue budget) :
    ActualFailureContext → ℕ :=
  densePackWindowReach

/-- The maximal reach lies inside the support shell. -/
theorem hReach (R : DensePackCorrectedResidue budget) :
    ∀ ctx : ActualFailureContext,
      R.windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
  densePackWindowReach_add_one_le

/-- The V3 containment field, derived from the interior component. -/
theorem hContain (R : DensePackCorrectedResidue budget) :
    ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + densePackWindowReach ctx := by
  intro ctx k hk
  have hint := R.interior ctx k hk
  have hpos : 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card := one_le_width ctx
  show k + ctx.n24CarryData.r
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + ((supportShell ctx.shell.d ctx.shell.X).card - 1)
  omega

/-- The grounded class-3 descent-window gap bound (the proved dyadic ceiling, via the
interior containment). -/
theorem hgap (R : DensePackCorrectedResidue budget)
    (hroute : ∀ ctx : ActualFailureContext, (budget ctx).route = genuineChargeRoute ctx) :
    ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r →
          hitGap ctx.n24CarryData.a j ≤ densePackDyadicG0 ctx :=
  densePackGap_ofContainment budget hroute densePackWindowReach
    densePackWindowReach_add_one_le R.hContain

/-- **The corrected per-element charge**: every routed class-3 start carries window excess at
most `densePackCorrectedMult ctx` — the honest replacement of the J.D unit charge. -/
theorem windowExcess_le_corrected (R : DensePackCorrectedResidue budget)
    (hroute : ∀ ctx : ActualFailureContext, (budget ctx).route = genuineChargeRoute ctx) :
    ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ densePackCorrectedMult ctx :=
  fun ctx =>
    windowExcess_le_mult_on_routedFibre ctx.n24CarryData ((budget ctx).route) 3
      (R.hgap hroute ctx) (self_le_positivePart _) (positivePart_nonneg _)

/-- **THE BRIDGE — the corrected residue yields the exact class-3 ledger field** consumed by
the final assembly, with NO use of the over-strong scalar: the per-element corrected charge is
summed by the proved count×multiplier core and absorbed by the amortized cover. -/
theorem hDensePackField (R : DensePackCorrectedResidue budget)
    (hroute : ∀ ctx : ActualFailureContext, (budget ctx).route = genuineChargeRoute ctx) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 3
        ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData := by
  intro ctx
  have hcard : ((routedFibre ctx.n24CarryData (budget ctx).route 3).card : ℝ)
      ≤ ((genuineDensePackStarts ctx).card : ℝ) := by
    rw [routedFibre_three_eq_densePackStarts hroute ctx]
  have hmass := routedClassMassOf_le_countMultiplier ctx.n24CarryData
    ((budget ctx).route) 3 (R.windowExcess_le_corrected hroute ctx)
    (densePackCorrectedMult_nonneg ctx) hcard
  exact hmass.trans (R.amortizedCover ctx)

/-- **The published over-strong residue maps INTO the corrected one** (no strength lost): the
old scalar caps the corrected multiplier by `1`, and the density already gives the count
against the marker term. -/
def ofV3Residue (R : DensePackV3Residue budget) : DensePackCorrectedResidue budget where
  density := R.density
  interior := R.windowInterior.densePackInterior
  amortizedCover := fun ctx => by
    have hmult_le_one : densePackCorrectedMult ctx ≤ 1 := by
      have h := R.hScale ctx
      unfold densePackCorrectedMult positivePart
      exact max_le h (by norm_num)
    have hcard : ((genuineDensePackStarts ctx).card : ℝ)
        ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData := by
      have h := densePackCount_ofEndpointDensity budget R.density ctx
      unfold termDensePack
      exact_mod_cast h
    calc ((genuineDensePackStarts ctx).card : ℝ) * densePackCorrectedMult ctx
        ≤ ((genuineDensePackStarts ctx).card : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hmult_le_one (Nat.cast_nonneg _)
      _ = ((genuineDensePackStarts ctx).card : ℝ) := mul_one _
      _ ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData := hcard

/-- **The published class-3 genuine-leaf residue maps INTO the corrected one** (its `floor`
field is the scalar in floor form). -/
def ofClass3GenuineResidue (R : DensePackClass3GenuineResidue) :
    DensePackCorrectedResidue budget where
  density := R.density
  interior := R.interior
  amortizedCover := fun ctx => by
    have hscale : ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ)
        - ctx.n24CarryData.T ≤ 1 :=
      (densePackScale_iff_floorLe ctx).mpr (R.floor ctx)
    have hmult_le_one : densePackCorrectedMult ctx ≤ 1 := by
      unfold densePackCorrectedMult positivePart
      exact max_le hscale (by norm_num)
    have hcard : ((genuineDensePackStarts ctx).card : ℝ)
        ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData := by
      have h := densePackCount_ofEndpointDensity budget R.density ctx
      unfold termDensePack
      exact_mod_cast h
    calc ((genuineDensePackStarts ctx).card : ℝ) * densePackCorrectedMult ctx
        ≤ ((genuineDensePackStarts ctx).card : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hmult_le_one (Nat.cast_nonneg _)
      _ = ((genuineDensePackStarts ctx).card : ℝ) := mul_one _
      _ ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData := hcard

end DensePackCorrectedResidue

/-! ## 4.  The corrected P9/V3 endpoint — downstream consumers can avoid `hScale`

`P9V3RunResidual` cannot be inhabited without the over-strong scalar (its `hScale` field), so
the corrected endpoint bypasses it: the five ledger bounds are assembled directly into the
public ctx-pinned ledger residual `P9CtxPinnedLedgerResidual` (the exact input surface of the
charge-reduced final endpoint), with Chernoff / clean-CNL / joint-TRT / class-6 discharged by
the SAME public closers the V3 endpoint uses, and class 3 discharged by the corrected
residue's bridge. -/

/-- **The corrected P9/V3 run-shaped residual.**  Identical to `P9V3RunResidual` except the
four DensePack fields (`densePackCount`/`windowReach`/`hReach`/`hContain`/`hScale`) are
replaced by the single corrected class-3 residue — in particular NO `hScale`. -/
structure P9V3CorrectedRunResidual where
  /-- Tower / class 2 active-floor count for the route that defines the V3 budget. -/
  towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx
  /-- Run / class 5, the sharp Section 26 leaf residual. -/
  runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx
  /-- Return / class 4 per-slice matched charge for the V3 budget. -/
  returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx
  /-- Chernoff / class 0 matched charge injection against the canonical V3 phases. -/
  chernoff : Class0ChernoffInjection
    (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)
  /-- Clean-CNL / class 1 matched Kraft charge injection against the canonical V3 phases. -/
  cnl : Class1CNLInjection
    (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)
  /-- DensePack / class 3 — the corrected residual surface (NO over-strong scalar). -/
  densePack : DensePackCorrectedResidue
    (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)

namespace P9V3CorrectedRunResidual

/-- The five ctx-pinned ledger bounds, assembled with the class-3 slot served by the corrected
bridge (`DensePackCorrectedResidue.hDensePackField`) instead of the `hScale`-based
`hDensePack_field_ofCardLe`. -/
def toLedger (R : P9V3CorrectedRunResidual) : P9CtxPinnedLedgerResidual where
  budget := v3Budget R.towerCount (p9V3RunChainOfResidual R.runResidual) R.returnCharge
  hChernoff := R.chernoff.hChernoffField
  hCnl := R.cnl.hCnlField
  hDensePack := R.densePack.hDensePackField (fun _ => rfl)
  hTRT := seedHTRT (v3Budget R.towerCount (p9V3RunChainOfResidual R.runResidual) R.returnCharge)
  hOldRes := fun ctx => by
    show routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 6
        ≤ ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k
    rw [genuineChargeRoute_routed6_zero ctx]
    exact oldResL65_branchMass_nonneg ctx

/-- The corrected P9/V3 endpoint reaches the final statement through the public ctx-pinned
ledger bridge. -/
theorem toStatement (R : P9V3CorrectedRunResidual) : Erdos260Statement :=
  R.toLedger.toStatement

end P9V3CorrectedRunResidual

/-- **P9/V3 endpoint with class 3 carried by the CORRECTED residual surface** — the downstream
replacement for `erdos260_p9V3_of_densePackV3`-style endpoints, consuming
`DensePackCorrectedResidue` instead of the deep-shell-false `hScale` field. -/
theorem erdos260_p9V3_of_densePackCorrected
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (cnl : Class1CNLInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (densePack : DensePackCorrectedResidue
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)) :
    Erdos260Statement :=
  P9V3CorrectedRunResidual.toStatement
    ⟨towerCount, runResidual, returnCharge, chernoff, cnl, densePack⟩

/-- The old `hScale`-based P9/V3 surface maps into the corrected endpoint (sanity: the corrected
lane is not weaker than the published one on its satisfiable domain). -/
theorem erdos260_p9V3_of_densePackV3_via_corrected
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (cnl : Class1CNLInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (densePack : DensePackV3Residue
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)) :
    Erdos260Statement :=
  erdos260_p9V3_of_densePackCorrected towerCount runResidual returnCharge chernoff cnl
    (DensePackCorrectedResidue.ofV3Residue densePack)

/-! ## 5.  Bonus — the descent-side `upperBandSource` period-calibration criterion

`UpperBandMatchSource.hpb` is `L + ord_2(q₀) ≤ proofV4DensePackSpread shell + 2` with
`proofV4DensePackSpread shell = L + B + 1`; so it is EXACTLY the denominator-order criterion
`ord_2(q₀) ≤ B + 3` — genuinely mixed across denominators. -/

/-- **The `hpb` period calibration of `UpperBandMatchSource` is exactly `ord_2(q₀) ≤ B + 3`.** -/
theorem upperBand_periodCalibration_iff (ctx : ActualFailureContext) :
    (Classical.choose ctx.shell.hXdyadic
        + orderOf (2 : ZMod (canonicalCenter ctx).q0)
      ≤ proofV4DensePackSpread ctx.shell + 2)
      ↔ orderOf (2 : ZMod (canonicalCenter ctx).q0) ≤ carryB ctx.shell.Q + 3 := by
  unfold proofV4DensePackSpread
  omega

/-- `ord_2(7) = 3` (so the criterion HOLDS at `q₀ = 7`: `3 ≤ B + 3` for every `B`). -/
theorem orderOf_two_zmod_seven : orderOf (2 : ZMod 7) = 3 := by
  have h3 : (2 : ZMod 7) ^ 3 = 1 := by decide
  have hdvd := orderOf_dvd_of_pow_eq_one h3
  have hpow := pow_orderOf_eq_one (2 : ZMod 7)
  have h1 : (2 : ZMod 7) ^ 1 ≠ 1 := by decide
  have henum : orderOf (2 : ZMod 7) = 1 ∨ orderOf (2 : ZMod 7) = 3 := by
    have hmem := Nat.mem_divisors.mpr ⟨hdvd, (by norm_num : (3 : ℕ) ≠ 0)⟩
    rw [show Nat.divisors 3 = {1, 3} from by decide] at hmem
    simpa using hmem
  rcases henum with h | h
  · rw [h] at hpow; exact absurd hpow h1
  · exact h

/-- `ord_2(11) = 10` (so the criterion FAILS at `q₀ = 11` whenever `B ≤ 6`, i.e. `Q < 16`). -/
theorem orderOf_two_zmod_eleven : orderOf (2 : ZMod 11) = 10 := by
  have h10 : (2 : ZMod 11) ^ 10 = 1 := by decide
  have hdvd := orderOf_dvd_of_pow_eq_one h10
  have hpow := pow_orderOf_eq_one (2 : ZMod 11)
  have h1 : (2 : ZMod 11) ^ 1 ≠ 1 := by decide
  have h2 : (2 : ZMod 11) ^ 2 ≠ 1 := by decide
  have h5 : (2 : ZMod 11) ^ 5 ≠ 1 := by decide
  have henum : orderOf (2 : ZMod 11) = 1 ∨ orderOf (2 : ZMod 11) = 2
      ∨ orderOf (2 : ZMod 11) = 5 ∨ orderOf (2 : ZMod 11) = 10 := by
    have hmem := Nat.mem_divisors.mpr ⟨hdvd, (by norm_num : (10 : ℕ) ≠ 0)⟩
    rw [show Nat.divisors 10 = {1, 2, 5, 10} from by decide] at hmem
    simpa using hmem
  rcases henum with h | h | h | h
  · rw [h] at hpow; exact absurd hpow h1
  · rw [h] at hpow; exact absurd hpow h2
  · rw [h] at hpow; exact absurd hpow h5
  · exact h

/-- The `q₀ = 7` instance of the criterion holds for every carry scale `B`. -/
theorem upperBand_ord_criterion_holds_q7 (B : ℕ) :
    orderOf (2 : ZMod 7) ≤ B + 3 := by
  rw [orderOf_two_zmod_seven]; omega

/-- The `q₀ = 11` instance of the criterion fails for every carry scale `B ≤ 6` (`Q < 16`). -/
theorem upperBand_ord_criterion_fails_q11 (B : ℕ) (hB : B ≤ 6) :
    ¬ orderOf (2 : ZMod 11) ≤ B + 3 := by
  rw [orderOf_two_zmod_eleven]; omega

/-! ## 6.  Honest status inventory -/

/-- Machine-readable status of the class-3 scale settlement and the corrected surface. -/
def densePackScaleObstructionStatus : List String :=
  [ "SETTLED (r >= 1 verdict) - densePack_hScale_fails_of_r_ge_one: the V3 class-3 scalar " ++
      "((r+1)*(densePackDyadicG0 ctx) - T <= 1) is FALSE on every shell with r >= 1. With the " ++
      "verified pins T = 2L+1 (cnlMulti_n24_T_eq), densePackDyadicG0 = L+B+1 " ++
      "(densePackDyadicG0_cast_eq), B >= 1: (r+1)(L+B+1) - (2L+1) >= 2B+1 >= 3 > 1.",
    "SETTLED (r = 0 verdict) - densePack_hScale_holds_of_r_eq_zero: on r = 0 shells the same " ++
      "scalar is TRUE, evaluating to B - L <= 0 (largeness gate B <= L). Sharp per-shell iff: " ++
      "densePack_hScale_iff_r_eq_zero; explicit-range form densePack_hScale_iff_L_le with the " ++
      "two-sided boundary pin n24_r_eq_zero_iff_L_le (r = 0 iff L <= 15420, kappa = 17/2^18).",
    "OBSTRUCTION (the universal field is global shallowness) - " ++
      "densePack_hScale_universal_iff_all_shallow: (forall ctx, hScale-form) iff (forall ctx, " ++
      "r = 0). Hence any provider of the published class-3 surface certifies every failing " ++
      "shell shallow: p9V3RunResidual_forces_shallow / _forces_L_le, " ++
      "densePackV3Residue_forces_shallow, densePackV3WindowFloorResidue_forces_shallow, " ++
      "densePackV3WindowScaleResidue_forces_shallow, densePackClass3GenuineResidue_forces_shallow. " ++
      "The scalar is a mis-calibrated residual surface to be REPAIRED, not supplied. The " ++
      "contrapositive audit interfaces not_densePack_hScale_universal_of_deep_ctx, " ++
      "not_nonempty_p9V3RunResidual_of_deep_ctx, and the analogous not_nonempty_* residue theorems " ++
      "reject the old surface as soon as one actual failure context has L > 15420.",
    "CORRECTED SCALE RELATION (proved) - densePack_correctedScale_of_window / _of_interior: " ++
      "for any high-excess start with an interior descent window, T + Y <= gapWindow <= " ++
      "(r+1)*densePackDyadicG0 ctx (highExcess_gapWindow_ge + the PROVED dyadic ceiling " ++
      "hitGap_le_densePackDyadicG0_of_window). The active floor dominates T + Y - the opposite " ++
      "calibration direction to the broken <= T + 1.",
    "CLASS-3 SHALLOW CLOSURE (proved; the class-3 analogue of the class-1 pin is EMPTINESS) - " ++
      "on r = 0 shells the corrected relation is absurd (2L+1+Y <= L+B+1 contradicts B <= L, " ++
      "Y > 0), so interior dense starts cannot exist: genuineDensePackStarts_eq_empty_of_r_eq_zero, " ++
      "routedFibre_three_eq_empty_of_r_eq_zero, class3Ledger_of_r_eq_zero. NO unconditional " ++
      "window-excess pin exists for class 3 (towerClsOfShell never inspects windowExcess); on " ++
      "deep shells the excess is only sandwiched Y <= wE <= densePackCorrectedMult.",
    "WHERE THE OLD BRIDGE NEEDS THE SCALAR (documented) - hDensePack_field_ofCardLe consumes " ++
      "hscale ONLY via windowExcess_le_one_on_routedFibre to get the J.D unit charge wE <= 1, " ++
      "then mass <= card * 1 <= termDensePack. The honest per-element cap is " ++
      "densePackCorrectedMult = positivePart((r+1)(L+B+1) - T): = 0 at r = 0 " ++
      "(densePackCorrectedMult_eq_zero_of_r_eq_zero), >= 2B+1 >= 3 at r >= 1 " ++
      "(densePackCorrectedMult_ge_of_r_ge_one); unit-charge fit iff r = 0 " ++
      "(densePackCorrectedMult_le_one_iff_r_eq_zero). So the unit-charge route is exactly the " ++
      "r = 0 collapse and the old derivation genuinely needs the over-strong scalar.",
    "CORRECTED SURFACE - DensePackCorrectedResidue budget: density (K.1.1 coarea hit-density, " ++
      "unchanged) + interior (K.1 window-interior containment, unchanged) + amortizedCover " ++
      "(CORRECTED K.1.2: |genuineDensePackStarts| * densePackCorrectedMult <= termDensePack - " ++
      "the marker term absorbs the count at the amortized active-floor rate, faithful to the " ++
      "manuscript marker charge wt(b) <= C_Q*Y*|I_j| which SCALES with the active floor). Every " ++
      "component satisfiable on every regime; on r = 0 the cover is provably FREE " ++
      "(amortizedCover_of_r_eq_zero); nothing is false on r >= 1 shells. Constructors: " ++
      "ofWindowInterior (shared residual reuse), ofDeepCover (deep-gated cover), ofV3Residue / " ++
      "ofClass3GenuineResidue (the published surfaces map IN - no strength lost).",
    "BRIDGE (proved) - DensePackCorrectedResidue.hDensePackField: the corrected residue yields " ++
      "the EXACT class-3 ledger field routedClassMassOf ... 3 <= termDensePack(faithfulCapacityPhases " ++
      "budget ctx) consumed by the final assembly, via windowExcess_le_corrected (the proved " ++
      "windowExcess_le_mult_on_routedFibre) + routedClassMassOf_le_countMultiplier + amortizedCover. " ++
      "The old count API survives: densePackCount / windowReach / hReach / hContain / hgap.",
    "ENDPOINT (proved) - P9V3CorrectedRunResidual + erdos260_p9V3_of_densePackCorrected: the " ++
      "P9/V3 endpoint with class 3 carried by the corrected residue, reaching Erdos260Statement " ++
      "through the public ctx-pinned ledger bridge (P9CtxPinnedLedgerResidual.toStatement), with " ++
      "Chernoff (Class0ChernoffInjection.hChernoffField), clean-CNL (Class1CNLInjection.hCnlField), " ++
      "joint TRT (seedHTRT) and class-6 vacancy (genuineChargeRoute_routed6_zero) discharged by " ++
      "the same public closers as the V3 endpoint. erdos260_p9V3_of_densePackV3_via_corrected " ++
      "routes the old surface through the corrected lane.",
    "WHAT THE FINAL ASSEMBLY MUST CONSUME - the class-3 slot needs only the ledger field " ++
      "routedClassMassOf ctx.n24CarryData (budget ctx).route 3 <= termDensePack " ++
      "(faithfulCapacityPhases budget ctx).toClosurePhaseData; provide it via " ++
      "DensePackCorrectedResidue.hDensePackField (corrected lane) instead of the hScale-based " ++
      "hDensePack_field_ofCardLe / P9V3RunResidual.hScale (which forces global shallowness).",
    "BONUS (descent-side density residual, settled) - upperBand_periodCalibration_iff: the " ++
      "UpperBandMatchSource.hpb period calibration L + ord_2(q0) <= spread + 2 is EXACTLY " ++
      "ord_2(q0) <= carryB Q + 3 (spread = L+B+1). Genuinely mixed: ord_2(7) = 3 " ++
      "(orderOf_two_zmod_seven; holds for all B - upperBand_ord_criterion_holds_q7), ord_2(11) " ++
      "= 10 (orderOf_two_zmod_eleven; fails for all B <= 6, i.e. Q < 16 - " ++
      "upperBand_ord_criterion_fails_q11). The hdens/W/hcop components remain separate residuals.",
    "RESIDUAL (honest, what remains open on the corrected lane) - the amortized cover " ++
      "amortizedCover on deep shells (the corrected K.1.2 marker-budget content), the K.1.1 " ++
      "hit-density density, and the K.1 interior containment interior; plus the orthogonal " ++
      "Tower/Run/Return/Chernoff/CNL slots of P9V3CorrectedRunResidual, unchanged. None of " ++
      "these is provably false on any shell regime - unlike the retired scalar." ]

theorem densePackScaleObstructionStatus_nonempty :
    densePackScaleObstructionStatus ≠ [] := by
  simp [densePackScaleObstructionStatus]

/-! ## 7.  Axiom-cleanliness audit -/

#print axioms densePack_hScale_fails_of_r_ge_one
#print axioms densePack_hScale_holds_of_r_eq_zero
#print axioms densePack_hScale_iff_r_eq_zero
#print axioms n24_r_eq_zero_iff_L_le
#print axioms densePack_hScale_iff_L_le
#print axioms densePack_hScale_universal_iff_all_shallow
#print axioms densePack_hScale_universal_forces_L_le
#print axioms not_densePack_hScale_universal_of_deep_ctx
#print axioms p9V3RunResidual_forces_shallow
#print axioms p9V3RunResidual_forces_L_le
#print axioms not_nonempty_p9V3RunResidual_of_deep_ctx
#print axioms densePackV3Residue_forces_shallow
#print axioms densePackV3WindowFloorResidue_forces_shallow
#print axioms densePackV3WindowScaleResidue_forces_shallow
#print axioms densePackClass3GenuineResidue_forces_shallow
#print axioms not_nonempty_densePackV3Residue_of_deep_ctx
#print axioms not_nonempty_densePackV3WindowFloorResidue_of_deep_ctx
#print axioms not_nonempty_densePackV3WindowScaleResidue_of_deep_ctx
#print axioms not_nonempty_densePackClass3GenuineResidue_of_deep_ctx
#print axioms highExcess_gapWindow_ge
#print axioms densePack_correctedScale_of_window
#print axioms densePack_correctedScale_of_interior
#print axioms genuineDensePackStarts_eq_empty_of_r_eq_zero
#print axioms routedFibre_three_eq_empty_of_r_eq_zero
#print axioms class3Ledger_of_r_eq_zero
#print axioms densePackCorrectedMult_eq_zero_of_r_eq_zero
#print axioms densePackCorrectedMult_ge_of_r_ge_one
#print axioms densePackCorrectedMult_le_one_iff_r_eq_zero
#print axioms amortizedCover_of_r_eq_zero
#print axioms DensePackCorrectedResidue.ofWindowInterior
#print axioms DensePackCorrectedResidue.ofDeepCover
#print axioms DensePackCorrectedResidue.densePackCount
#print axioms DensePackCorrectedResidue.hContain
#print axioms DensePackCorrectedResidue.hgap
#print axioms DensePackCorrectedResidue.windowExcess_le_corrected
#print axioms DensePackCorrectedResidue.hDensePackField
#print axioms DensePackCorrectedResidue.ofV3Residue
#print axioms DensePackCorrectedResidue.ofClass3GenuineResidue
#print axioms P9V3CorrectedRunResidual.toLedger
#print axioms P9V3CorrectedRunResidual.toStatement
#print axioms erdos260_p9V3_of_densePackCorrected
#print axioms erdos260_p9V3_of_densePackV3_via_corrected
#print axioms upperBand_periodCalibration_iff
#print axioms orderOf_two_zmod_seven
#print axioms orderOf_two_zmod_eleven
#print axioms upperBand_ord_criterion_holds_q7
#print axioms upperBand_ord_criterion_fails_q11
#print axioms densePackScaleObstructionStatus_nonempty

end

end Erdos260
