import Erdos260.CNLKraftCountCore
import Erdos260.DensePackCoverCore

/-!
# Charge-calibration audit — the active-floor calibration family (Cores 2 / 7 / 14) is
false-for-deep-shells, exactly like the CNL Kraft budget (Core 11)

This module (NEW; it edits no existing file) audits the **calibration family** of residual cores —
the ones that bound the *shell-scaling* active floor `(r+1)·(L+B+1)` against a *fixed / per-slice*
ceiling `T + c`:

* **Core 14** — the DensePack K.1.2 active-floor calibration `hScale`:
  `(r+1)·(L+B+1) − T ≤ 1`;
* **Core 7** — the H.4 / 2.2.1.A shell-Chernoff calibration `(r+1)·(L+B+1) − T ≤ 1/4`; and
* **Core 2** — the return-nesting per-slice calibration `(r+1)·(L+B+1) − T ≤ c` (`0 ≤ c ≤ 2`).

with the genuine N.24 carry values
`r = proofV4CarryOrder ctx.shell = ⌊κ·L⌋` (`κ = manuscriptKappa = 17/2^18`),
`T = 2·L + manuscriptCQ_T = 2L + 1`, `B = carryB ctx.shell.Q ≥ 1`,
`L = shellLadderDepth ctx` (`ctx.shell.X = 2^L`), pinned definitionally by `n24CarryData_r_eq` /
`n24CarryData_T_eq` (`CNLKraftCountCore.lean`).

## The crux — the active-floor excess grows like `κ·L²`, beating the linear ceiling `2L`

The shared calibration quantity is the **active-floor excess**

```
activeFloorExcess ctx := (r+1)·(L+B+1) − T = (r+1)·(densePackDyadicG0 ctx) − T ,
```

i.e. the LHS of `densePackScale_iff_floorLe` (`DensePackCoverCore.lean`), and definitionally the CNL
`cnlActiveMult ctx`.  We prove the same dichotomy that closed CNL Core 11:

* **`activeFloorExcess_nonpos_of_r_zero`** — shallow shells (`r = 0`, `L ≤ ⌊1/κ⌋`) give
  `activeFloorExcess ctx = B − L ≤ 0` (the largeness gate `carryB Q + 25 ≤ L`); and
* **`activeFloorExcess_ge_of_r_pos`** — deep shells (`r ≥ 1`, `L ≥ ⌈1/κ⌉ ≈ 15421`) give
  `activeFloorExcess ctx ≥ 2·carryB Q + 1 ≥ 3`;
* **`activeFloorExcess_ge_quadratic`** — and *unboundedly*: for every shell
  `activeFloorExcess ctx ≥ κ·L² − 2·L`.  Since `κ > 0` (`manuscriptKappa_pos`) the quadratic
  `κ·L²` dominates the linear ceiling `2L`, so the excess `→ ∞` as the shells deepen.  This is the
  honest reason a *uniform* `(r+1)(L+B+1) − T ≤ c` charge cannot hold past the first active layer.

## The sharp iff — each calibration core holds iff `r = 0`

For any fixed ceiling `c` with `0 ≤ c ≤ 2 < 3 ≤ 2·carryB Q + 1`:

```
activeFloorExcess ctx ≤ c  ↔  ctx.n24CarryData.r = 0      (activeFloorExcess_le_iff_r_zero)
```

so each calibration core is **closed exactly on the manuscript first active layer** (`r = 0`,
shallow shells `L < ⌈1/κ⌉`) and **provably FALSE for every deep shell `r ≥ 1`**
(`calibration_false_of_r_pos`).  Instantiating:

* Core 14 (`densePack_hScale_iff_r_zero`, `c = 1`) — and, through `densePackScale_iff_floorLe`,
  `densePack_floorLe_iff_r_zero`: `densePackActiveFloor ctx − 1 ≤ T ↔ r = 0`;
* Core 7 (`chernoff_calibration_iff_r_zero`, `c = 1/4`); and
* Core 2 (`return_calibration_iff_r_zero`, any per-slice ceiling `0 ≤ c ≤ 2`).

This is the *same shape* as the three sibling wave-11 results — `cnl_hbudget_iff_r_zero` (CNL Core 11)
and `densePackScale_iff_floorLe` (DensePack Core 14): a residual that bounds a shell-scaling quantity
by a fixed / per-slice one collapses to `r = 0`.

## The documented matched-charge fix direction (NOT implemented here)

The uniform ceiling is an **encoding artefact**, not the manuscript charge.  The manuscript (§I.0,
§N.2, K.1.2) charges the window excess against the **normalized rolling-window variation / coarea
density** — an *amortized per-element* charge that scales with the active floor — not a uniform
worst-case ceiling.  Concretely: the corrected calibration is the **matched per-element charge**
already supported by the `cnlBudgetOfShell`-style bounds (each codeword pays its own window-excess
unit, summed against the Kraft tiling), so the per-element charge tracks `(r+1)(L+B+1)` instead of
being capped by a single `T + c`.  Replacing the uniform `(r+1)(L+B+1) − T ≤ c` field by the matched
per-element window-excess charge removes the deep-shell residual `r ≥ 1` characterized below.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The shared calibration quantity — the active-floor excess `(r+1)(L+B+1) − T` -/

/-- **The active-floor excess** `(r+1)·(L+B+1) − T`, the shared calibration quantity of Cores 2/7/14.
It is exactly the LHS of `densePackScale_iff_floorLe` and definitionally the CNL `cnlActiveMult`. -/
def activeFloorExcess (ctx : ActualFailureContext) : ℝ :=
  ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T

/-- The dyadic gap ceiling cast to `ℝ`: `densePackDyadicG0 ctx = L + B + 1`. -/
theorem densePackDyadicG0_cast_eq (ctx : ActualFailureContext) :
    (densePackDyadicG0 ctx : ℝ)
      = (shellLadderDepth ctx : ℝ) + (carryB ctx.shell.Q : ℝ) + 1 := by
  unfold densePackDyadicG0 shellLadderDepth
  push_cast
  ring

/-- The genuine descent order is the proof-v4 floor order with `L = shellLadderDepth ctx`:
`r = ⌊κ·L⌋`. -/
theorem n24CarryData_r_eq_floor (ctx : ActualFailureContext) :
    ctx.n24CarryData.r = Nat.floor (manuscriptKappa * (shellLadderDepth ctx : ℝ)) := by
  rw [n24CarryData_r_eq]; rfl

/-! ## 2.  The sign dichotomy — shallow shells nonpositive, deep shells `≥ 3` -/

/-- **Shallow shells (`r = 0`): the active-floor excess is nonpositive.**  Here
`activeFloorExcess ctx = (L+B+1) − (2L+1) = B − L ≤ 0` (the largeness gate `carryB Q + 25 ≤ L`). -/
theorem activeFloorExcess_nonpos_of_r_zero (ctx : ActualFailureContext)
    (h : ctx.n24CarryData.r = 0) : activeFloorExcess ctx ≤ 0 := by
  have hB : (carryB ctx.shell.Q : ℝ) ≤ (shellLadderDepth ctx : ℝ) := by
    exact_mod_cast carryB_ctx_le_shellLadderDepth ctx
  unfold activeFloorExcess
  rw [densePackDyadicG0_cast_eq, n24CarryData_T_eq, h,
    show (manuscriptCQ_T : ℝ) = 1 from by norm_num [manuscriptCQ_T]]
  push_cast
  nlinarith [hB]

/-- **Deep shells (`r ≥ 1`): the active-floor excess is at least `2·carryB Q + 1 ≥ 3`.**  Here
`activeFloorExcess ctx = (r+1)(L+B+1) − (2L+1) ≥ 2(L+B+1) − (2L+1) = 2B+1`. -/
theorem activeFloorExcess_ge_of_r_pos (ctx : ActualFailureContext)
    (h : 1 ≤ ctx.n24CarryData.r) :
    2 * (carryB ctx.shell.Q : ℝ) + 1 ≤ activeFloorExcess ctx := by
  have hr : (1 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := by exact_mod_cast h
  have hL : (0 : ℝ) ≤ (shellLadderDepth ctx : ℝ) := Nat.cast_nonneg _
  have hB : (0 : ℝ) ≤ (carryB ctx.shell.Q : ℝ) := Nat.cast_nonneg _
  unfold activeFloorExcess
  rw [densePackDyadicG0_cast_eq, n24CarryData_T_eq,
    show (manuscriptCQ_T : ℝ) = 1 from by norm_num [manuscriptCQ_T]]
  nlinarith [hr, hL, hB,
    mul_nonneg (by linarith : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) - 1)
      (by linarith : (0 : ℝ) ≤ (shellLadderDepth ctx : ℝ) + (carryB ctx.shell.Q : ℝ) + 1)]

/-- **Deep shells: the active-floor excess exceeds `3`.** -/
theorem activeFloorExcess_gt_two_of_r_pos (ctx : ActualFailureContext)
    (h : 1 ≤ ctx.n24CarryData.r) : 2 < activeFloorExcess ctx := by
  have hge := activeFloorExcess_ge_of_r_pos ctx h
  have hB : (1 : ℝ) ≤ (carryB ctx.shell.Q : ℝ) := by exact_mod_cast carryB_ctx_ge_one ctx
  linarith

/-! ## 3.  The crux — the active-floor excess grows quadratically (`≥ κ·L² − 2L`), unbounded -/

/-- **The active-floor excess is bounded below by the quadratic `κ·L² − 2·L`.**

With the genuine values `r = ⌊κ·L⌋` (so `κ·L < r + 1`), `T = 2L+1` and `B ≥ 1`,
`(r+1)(L+B+1) − T ≥ κ·L² − 2·L`.  Since `κ = manuscriptKappa > 0`, the quadratic `κ·L²` dominates the
linear ceiling `2L`, so the excess is **unbounded** as the shells deepen — the uniform calibration
`(r+1)(L+B+1) − T ≤ c` cannot survive deep shells. -/
theorem activeFloorExcess_ge_quadratic (ctx : ActualFailureContext) :
    manuscriptKappa * (shellLadderDepth ctx : ℝ) ^ 2 - 2 * (shellLadderDepth ctx : ℝ)
      ≤ activeFloorExcess ctx := by
  have hL : (0 : ℝ) ≤ (shellLadderDepth ctx : ℝ) := Nat.cast_nonneg _
  have hr : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := Nat.cast_nonneg _
  have hB : (1 : ℝ) ≤ (carryB ctx.shell.Q : ℝ) := by exact_mod_cast carryB_ctx_ge_one ctx
  have hfloor : manuscriptKappa * (shellLadderDepth ctx : ℝ) < (ctx.n24CarryData.r : ℝ) + 1 := by
    rw [n24CarryData_r_eq_floor ctx]
    exact Nat.lt_floor_add_one _
  unfold activeFloorExcess
  rw [densePackDyadicG0_cast_eq, n24CarryData_T_eq,
    show (manuscriptCQ_T : ℝ) = 1 from by norm_num [manuscriptCQ_T]]
  nlinarith [hL, hr, hB, hfloor,
    mul_nonneg (by linarith : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) + 1)
      (by linarith : (0 : ℝ) ≤ (carryB ctx.shell.Q : ℝ)),
    mul_nonneg
      (by linarith : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) + 1
        - manuscriptKappa * (shellLadderDepth ctx : ℝ)) hL]

/-! ## 4.  The sharp iff — each calibration core holds iff `r = 0` -/

/-- **The sharp characterisation of the calibration family.**  For any fixed ceiling `c` with
`0 ≤ c ≤ 2`, the uniform calibration `activeFloorExcess ctx ≤ c` holds **iff** the descent order
vanishes.  Forwards: if `r ≥ 1` then `activeFloorExcess ≥ 2·carryB Q + 1 ≥ 3 > 2 ≥ c`, contradiction.
Backwards: `r = 0 ⇒ activeFloorExcess ≤ 0 ≤ c`. -/
theorem activeFloorExcess_le_iff_r_zero (ctx : ActualFailureContext) (c : ℝ)
    (hc0 : 0 ≤ c) (hc2 : c ≤ 2) :
    activeFloorExcess ctx ≤ c ↔ ctx.n24CarryData.r = 0 := by
  constructor
  · intro hle
    by_contra hne
    have h1 : 1 ≤ ctx.n24CarryData.r := Nat.one_le_iff_ne_zero.mpr hne
    have hgt := activeFloorExcess_gt_two_of_r_pos ctx h1
    linarith
  · intro h
    have := activeFloorExcess_nonpos_of_r_zero ctx h
    linarith

/-- **The calibration family is provably FALSE for every deep shell.**  For any ceiling `c ≤ 2`, if
`r ≥ 1` then the uniform calibration `activeFloorExcess ctx ≤ c` fails. -/
theorem calibration_false_of_r_pos (ctx : ActualFailureContext) (c : ℝ) (hc2 : c ≤ 2)
    (h : 1 ≤ ctx.n24CarryData.r) : ¬ activeFloorExcess ctx ≤ c := by
  intro hle
  have hgt := activeFloorExcess_gt_two_of_r_pos ctx h
  linarith

/-! ## 5.  The three named calibration cores -/

/-- **Core 14 (DensePack `hScale`).**  The K.1.2 active-floor calibration `(r+1)(L+B+1) − T ≤ 1`
holds iff `r = 0` (stated on the literal `densePackScale_iff_floorLe` LHS). -/
theorem densePack_hScale_iff_r_zero (ctx : ActualFailureContext) :
    (((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1)
      ↔ ctx.n24CarryData.r = 0 :=
  activeFloorExcess_le_iff_r_zero ctx 1 (by norm_num) (by norm_num)

/-- **Core 14, via `densePackScale_iff_floorLe`.**  The threshold lower bound
`densePackActiveFloor ctx − 1 ≤ T` (the manuscript K.1.2 calibration's floor form) holds iff `r = 0`.
Chains the DensePack `densePackScale_iff_floorLe` reduction through the sharp iff. -/
theorem densePack_floorLe_iff_r_zero (ctx : ActualFailureContext) :
    densePackActiveFloor ctx - 1 ≤ ctx.n24CarryData.T ↔ ctx.n24CarryData.r = 0 :=
  (densePackScale_iff_floorLe ctx).symm.trans (densePack_hScale_iff_r_zero ctx)

/-- **Core 7 (shell-Chernoff `≤ 1/4`).**  The H.4 / 2.2.1.A calibration `(r+1)(L+B+1) − T ≤ 1/4`
holds iff `r = 0`. -/
theorem chernoff_calibration_iff_r_zero (ctx : ActualFailureContext) :
    activeFloorExcess ctx ≤ 1 / 4 ↔ ctx.n24CarryData.r = 0 :=
  activeFloorExcess_le_iff_r_zero ctx (1 / 4) (by norm_num) (by norm_num)

/-- **Core 2 (return-nesting, per-slice ceiling).**  For any per-slice return ceiling `0 ≤ c ≤ 2`,
the calibration `(r+1)(L+B+1) − T ≤ c` holds iff `r = 0`. -/
theorem return_calibration_iff_r_zero (ctx : ActualFailureContext) (c : ℝ)
    (hc0 : 0 ≤ c) (hc2 : c ≤ 2) :
    activeFloorExcess ctx ≤ c ↔ ctx.n24CarryData.r = 0 :=
  activeFloorExcess_le_iff_r_zero ctx c hc0 hc2

/-- **Core 14 is false for deep shells.** -/
theorem densePack_hScale_false_of_r_pos (ctx : ActualFailureContext)
    (h : 1 ≤ ctx.n24CarryData.r) :
    ¬ (((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :=
  calibration_false_of_r_pos ctx 1 (by norm_num) h

/-- **Core 7 is false for deep shells.** -/
theorem chernoff_calibration_false_of_r_pos (ctx : ActualFailureContext)
    (h : 1 ≤ ctx.n24CarryData.r) : ¬ activeFloorExcess ctx ≤ 1 / 4 :=
  calibration_false_of_r_pos ctx (1 / 4) (by norm_num) h

/-! ## 6.  Honest residual inventory -/

/-- The precise per-core status of the active-floor calibration family (Cores 2 / 7 / 14) after this
module. -/
def chargeCalibrationAuditResiduals : List String :=
  [ "SHARED QUANTITY (proved) — activeFloorExcess ctx = (r+1)·(L+B+1) − T = (r+1)·(densePackDyadicG0 " ++
      "ctx) − T, the LHS of densePackScale_iff_floorLe and definitionally cnlActiveMult. Genuine N.24 " ++
      "values: r = proofV4CarryOrder ctx.shell = ⌊κ·L⌋ (κ = manuscriptKappa = 17/2^18, n24CarryData_r_eq " ++
      "/ n24CarryData_r_eq_floor), T = 2·L + manuscriptCQ_T = 2L+1 (n24CarryData_T_eq), B = carryB Q ≥ 1, " ++
      "L = shellLadderDepth ctx (X = 2^L).",
    "SIGN DICHOTOMY (proved) — activeFloorExcess_nonpos_of_r_zero: r = 0 ⇒ activeFloorExcess = B − L " ++
      "≤ 0 (largeness gate carryB Q + 25 ≤ L); activeFloorExcess_ge_of_r_pos: r ≥ 1 ⇒ activeFloorExcess " ++
      "≥ 2·carryB Q + 1 ≥ 3 (> 2, activeFloorExcess_gt_two_of_r_pos). Mirrors CNL Core 11's " ++
      "cnlActiveMult dichotomy exactly.",
    "ACTIVE-FLOOR SCALE / UNBOUNDED (proved, THE CRUX) — activeFloorExcess_ge_quadratic: for EVERY " ++
      "shell activeFloorExcess ctx ≥ κ·L² − 2·L. Since κ = manuscriptKappa > 0 (manuscriptKappa_pos), " ++
      "the quadratic κ·L² (from r = ⌊κL⌋ growing) dominates the linear ceiling 2L, so the excess → ∞ as " ++
      "shells deepen. A FIXED/PER-SLICE ceiling (r+1)(L+B+1) − T ≤ c therefore cannot survive deep shells.",
    "SHARP IFF (proved) — activeFloorExcess_le_iff_r_zero: for any ceiling 0 ≤ c ≤ 2 (< 3 ≤ 2·carryB " ++
      "Q + 1), the calibration activeFloorExcess ctx ≤ c holds IFF ctx.n24CarryData.r = 0. So each " ++
      "calibration core is closed EXACTLY on the manuscript first active layer (r = 0, shallow shells " ++
      "L < ⌈1/κ⌉ ≈ 15421) and is FALSE for every deep shell r ≥ 1 (calibration_false_of_r_pos).",
    "CORE 14 (proved) — densePack_hScale_iff_r_zero: DensePack hScale (r+1)(L+B+1) − T ≤ 1 ↔ r = 0; " ++
      "densePack_floorLe_iff_r_zero: via densePackScale_iff_floorLe, densePackActiveFloor ctx − 1 ≤ T ↔ " ++
      "r = 0. densePack_hScale_false_of_r_pos: false for r ≥ 1.",
    "CORE 7 (proved) — chernoff_calibration_iff_r_zero: the shell-Chernoff calibration activeFloorExcess " ++
      "ctx ≤ 1/4 ↔ r = 0; chernoff_calibration_false_of_r_pos: false for r ≥ 1.",
    "CORE 2 (proved) — return_calibration_iff_r_zero: for any per-slice return ceiling 0 ≤ c ≤ 2, " ++
      "activeFloorExcess ctx ≤ c ↔ r = 0. False for r ≥ 1 via calibration_false_of_r_pos.",
    "FIX DIRECTION (documented, NOT implemented) — the uniform ceiling is an encoding artefact. The " ++
      "manuscript (§I.0, §N.2, K.1.2) charges window excess against the NORMALIZED ROLLING-WINDOW " ++
      "VARIATION / COAREA DENSITY — an amortized PER-ELEMENT charge that scales with the active floor — " ++
      "NOT a uniform worst-case ceiling. The corrected calibration is the matched per-element " ++
      "window-excess charge already supported by cnlBudgetOfShell-style bounds (each codeword pays its " ++
      "own unit, summed against the Kraft tiling), so the charge tracks (r+1)(L+B+1) instead of being " ++
      "capped by a single T + c. This removes the deep-shell residual r ≥ 1 characterized above." ]

theorem chargeCalibrationAuditResiduals_nonempty : chargeCalibrationAuditResiduals ≠ [] := by
  simp [chargeCalibrationAuditResiduals]

/-! ## 7.  Axiom-cleanliness audit -/

#print axioms densePackDyadicG0_cast_eq
#print axioms n24CarryData_r_eq_floor
#print axioms activeFloorExcess_nonpos_of_r_zero
#print axioms activeFloorExcess_ge_of_r_pos
#print axioms activeFloorExcess_gt_two_of_r_pos
#print axioms activeFloorExcess_ge_quadratic
#print axioms activeFloorExcess_le_iff_r_zero
#print axioms calibration_false_of_r_pos
#print axioms densePack_hScale_iff_r_zero
#print axioms densePack_floorLe_iff_r_zero
#print axioms chernoff_calibration_iff_r_zero
#print axioms return_calibration_iff_r_zero
#print axioms densePack_hScale_false_of_r_pos
#print axioms chernoff_calibration_false_of_r_pos

end

end Erdos260
