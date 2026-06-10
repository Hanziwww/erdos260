import Erdos260.TowerActiveFloorClosure
import Erdos260.ActiveWindowContainmentCore
import Erdos260.ChargeCalibrationAuditCore

/-!
# Tower / Class 2 — the shallow-shell UNCONDITIONAL closure and the sharp deep-shell residual

This module (NEW; it edits no existing file) closes the V3/P9 Tower slot

```
towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx
```

(the §I.4 active-floor count `(★) #fibre₂ · positivePart (2·Y) ≤ ξ·X/6` + boundary exclusion,
`TowerRunDeepCore.lean`) **unconditionally on every shallow shell**, and reduces the deep shells to
one named window/Hall residual, wired through the existing
`Class2HallIndexSDRResidual → Class2IndexSDR → … → Class2ActiveFloorCount` chain
(`TowerActiveFloorClosure.lean`, `SDRSelectionCore.lean`, `TowerSDRCore.lean`,
`TowerK13PackingExistenceCore.lean`, `TowerI41PackingCore.lean`) — none of whose proofs are
duplicated here.

## What is CLOSED UNCONDITIONALLY here

1. **Boundary exclusion, for every shell, every route, every class**
   (`routedFibre_zero_notMem` / `class2_hbdry_unconditional`): the carry start set is the dyadic
   shell index window `Ico (firstIndexAbove X) (firstIndexAbove X + |supportShell|)`
   (`n24Starts_eq_window`), and `firstIndexAbove X ≥ 1` because the shell has a support hit at or
   below `X` (`HitSequence.firstIndexAbove_pos_of_supportCount_pos` + `ctx.n24SupportCount_pos`).
   So `0` is never a routed start.  One of the two `Class2ActiveFloorCount` fields is therefore
   **never** a residual.

2. **The shallow-shell count `(★)`, with NO SDR machinery**
   (`class2_count_of_shallow` / `class2ActiveFloorCount_ofShallow`): for every actual failing shell
   with `L = shellLadderDepth ctx ≤ 328965` (`X = 2^L ≤ 2^328965`),

   `#fibre₂ · positivePart (2Y) ≤ |supportShell| · 2εL < c₀X · 2εL ≤ (ξ/6)·X`,

   using only the genuine window containment (`#fibre₂ ≤ |supportShell|`, since the fibre filters
   the start window), the **positive-density failure cap** `|supportShell| < c₀·X` (`ctx.hfailure`),
   the `rfl`-pinned active floor `Y = εL` (`towerSD_Y_eq`), and the K.4 numerics
   `2c₀ε·L ≤ ξ/6 ⟺ L ≤ 328965` (`towerShallow_scalar`).  In particular **every shell with
   `r = ⌊κL⌋ ≤ 20`** is closed (`r ≤ 20 ⟺ L ≤ 323824`, `class2ActiveFloorCount_of_r_le_20`).

3. **The threshold is sharp** (`towerShallow_scalar_false_of_deep`,
   `towerDemand_le_one_iff_shallow`): with the pinned constants (`c₀ = κ/64`, `κ = 17/2^18`,
   `ε = 1/64`, `ξ = 1/16`) the direct width-cap scalar `2c₀ε·L ≤ ξ/6` holds **iff** the demanded
   per-start density `y* := ρ_D·L ≤ 1` **iff** `L ≤ 328965` (`51·L ≤ 2^24`; note
   `51 · 328965 = 2^24 − 1`).  This realizes the `⌈y*⌉` case split: `⌈y*⌉ ≤ 1` ⟺ the count is free
   (via the genuine routed data, not a fabricated witness); `⌈y*⌉ ≥ 2` ⟺ the deep regime.

## Calibration pins (all verified against `erdos260Constants` / K.4)

* `towerSD_Y_eq` — `Y = ε·L` by `rfl` through the whole `GapData → … → n24CarryData` chain (the
  same pin as `n24CarryData_Y_eq` of `CNLMultiChargeUnconditional.lean`, restated here under a
  module-local name because that sibling module is not in this import closure);
* `ActualFailureContext.shell_d` — the raw-vs-shell digit-word agreement `ctx.shell.d = ctx.d`
  (`rfl`; the `shell_X` twin already exists upstream with `@[simp]`, the `d` form did not);
* `towerRhoD := 3κ/64 = 51/2^24 ≈ 3.04·10⁻⁶` — the formalization's density parameter, achieving
  **exact equality** in the K.4 uniform bound: `2·(c₀·ε) = (ξ/6)·ρ_D = κ/2048`
  (`towerUniform_exact`, `towerUniform_eq_kappa_div`);
* `towerSparsityBlock := ⌈3(r+1)/64⌉` (ℕ ceiling division `(3(r+1)+63)/64`) — the per-start block
  size, with `ρ_D·L ≤ m₀` proved from `r = ⌊κL⌋` (`towerRhoD_mul_L_le_block`); `m₀ = 1` for
  `r ≤ 20` (`towerSparsityBlock_eq_one_of_r_le_20`) and `m₀ ≥ 2` exactly in the deep regime.

## The deep-shell residual (REDUCED, honestly NOT closed)

`Class2DeepShellWindowData ctx` — demanded **only** for `L ≥ 328966` (equivalently `r ≥ 21`,
`r_ge_21_of_deep`) — carries exactly the two genuinely-open K.1.3/§25.1 data:

* `hlands` — per-start hit-index windows landing in the shell (dischargeable outright by
  `Class2DeepShellWindowData.ofRangeWindows` whenever the windows sit inside the genuine start
  window, via the closed landing lemma `towerSD_window_lands`); and
* `hmarg` — the **Hall marginal** `m₀·|S| ≤ |⋃_{k∈S} W k|` over the genuine class-2 fibre — the
  no-large-run semiperiodic density + maximal-disjoint-selection content.

The wiring `Class2DeepShellWindowData → Class2HallIndexSDRResidual → Class2IndexSDR →
Class2ActiveFloorCount` reuses the existing proved bridges verbatim.  The total surface is

```
class2ActiveFloorCount_ofShallowDeep :
  Class2DeepShellResidual → ∀ ctx, Class2ActiveFloorCount ctx
```

with `Class2DeepShellResidual := ∀ ctx, 328965 < L → Class2DeepShellWindowData ctx` — i.e. the
exact `P9V3RunResidual.towerCount` / `Erdos260MinimalResidualV3.towerCount` /
`TowerRunGenuineResidual.towerCount` field shape from the deep windows alone.

## Honesty notes

* The deep residual is **genuine**: the §25.1 semiperiodic window matching (and the Fine–Wilf
  periodicity it rides on) is not available unconditionally in this formalization — the proved
  `HitSequence` gap bounds control the *total* shell support, never the *per-start* ownership
  (see the `TowerSDRCore` audit) — so we do **not** fabricate `hmarg`.
* The residual is a true **weakening** of the manuscript demand: the formal structure leaves the
  density rate free (constrained only by the K.4 `huniform`), and our pinned rate
  `ρ_D = 3κ/64 = 51/2^24` is `16777216/204 ≈ 82241×` smaller than the manuscript's `q₀ = 1` rate
  `ρ₀(Q) = 1/(4q₀) = 1/4` — and smaller than `1/(4q₀)` for every `q₀ ≤ 82241`.
* No vacuous/degenerate witnesses: the shallow closure runs over the genuine routed class-2 fibre
  of `genuineChargeRoute` with the genuine carry data; the boundary exclusion and the landing
  lemma are proved from the real hit enumeration; the deep windows are demanded only on genuinely
  deep shells.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## 0.  The raw-vs-shell field agreement `shell_d` (the `shell_X` twin)

`ActualFailureContext.shell_X` (`ctx.shell.X = ctx.X`, `@[simp]`) exists upstream; the digit-word
form did not.  It holds by `rfl` through `FailingDyadicShell.ofGlobalConstants`. -/

/-- The pinned shell's digit word is the raw context digit word (definitional). -/
@[simp] theorem ActualFailureContext.shell_d (ctx : ActualFailureContext) :
    ctx.shell.d = ctx.d := rfl

/-! ## 1.  Calibration pins — `Y = εL`, `r = ⌊κL⌋`, and the exact-equality density rate

All `rfl`-level or `norm_num`-level facts about the canonical N.24 carry datum and the pinned
K.4 constants.  (`n24CarryData_r_eq_floor` is imported from `ChargeCalibrationAuditCore`;
`n24CarryData_T_eq` from `CNLKraftCountCore`.) -/

/-- **The active floor is `Y = ε·L`** — by `rfl` through the whole conversion chain
`GapData → appendixNGapCanonicalYCarryLocalAt → toCarryData = n24CarryData`.  (Same content as
`n24CarryData_Y_eq` in the sibling `CNLMultiChargeUnconditional.lean`, which is not in this
import closure; restated under a module-local name to avoid any future name clash.) -/
theorem towerSD_Y_eq (ctx : ActualFailureContext) :
    ctx.n24CarryData.Y = manuscriptEps * (shellLadderDepth ctx : ℝ) := rfl

/-- The active floor is nonnegative (`ε > 0`, `L ≥ 0`). -/
theorem towerSD_Y_nonneg (ctx : ActualFailureContext) : 0 ≤ ctx.n24CarryData.Y := by
  rw [towerSD_Y_eq ctx]
  exact mul_nonneg manuscriptEps_pos.le (Nat.cast_nonneg _)

/-- The I.3 active-floor calibration `2·Y ≤ 2·ε·L` holds with **equality** at the pinned data. -/
theorem towerSD_calib (ctx : ActualFailureContext) :
    2 * ctx.n24CarryData.Y ≤ 2 * manuscriptEps * (shellLadderDepth ctx : ℝ) :=
  le_of_eq (by rw [towerSD_Y_eq ctx]; ring)

/-- The dyadic ladder depth is positive in `ℝ` (the largeness gate gives `L ≥ 28`). -/
theorem towerSD_L_pos (ctx : ActualFailureContext) :
    (0 : ℝ) < (shellLadderDepth ctx : ℝ) := by
  have h : (28 : ℝ) ≤ (shellLadderDepth ctx : ℝ) := by
    exact_mod_cast shellLadderDepth_ge ctx
  linarith

/-- Numeric value of the manuscript order constant: `κ = 17/2^18 = 17/262144`. -/
theorem towerKappa_eq : manuscriptKappa = 17 / 262144 := by
  unfold manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps
  norm_num

/-- **The Tower density rate** `ρ_D := 3κ/64` — the formalization's free density parameter of the
`Class2HallIndexSDRResidual` surface, pinned at the rate that makes the K.4 uniform bound an
**exact equality** (`towerUniform_exact`).  The manuscript's own fixed density is `ρ₀(Q) = 1/(4q₀)`;
leaving the rate free and pinning it this low is a strict *weakening* of the manuscript demand
(see the module docstring), hence honest. -/
def towerRhoD : ℝ := 3 * manuscriptKappa / 64

/-- Numeric value: `ρ_D = 51/2^24 = 51/16777216 ≈ 3.04·10⁻⁶`. -/
theorem towerRhoD_eq : towerRhoD = 51 / 16777216 := by
  unfold towerRhoD manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps
  norm_num

/-- `ρ_D > 0`. -/
theorem towerRhoD_pos : 0 < towerRhoD := by
  rw [towerRhoD_eq]; norm_num

/-- **The K.4 uniform bound holds with EXACT EQUALITY at `ρ_D = 3κ/64`**:
`2·(c₀·ε) = (ξ/6)·ρ_D` (both sides `= 17/2^29`). -/
theorem towerUniform_exact :
    2 * (erdos260Constants.c0 * manuscriptEps) = erdos260Constants.ξ / 6 * towerRhoD := by
  have hc0 : erdos260Constants.c0 = manuscriptC0 := rfl
  have hxi : erdos260Constants.ξ = manuscriptXi := rfl
  rw [hc0, hxi]
  unfold towerRhoD manuscriptC0 manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps
    manuscriptXi
  norm_num

/-- The shared value of the exact equality is `κ/2048`. -/
theorem towerUniform_eq_kappa_div :
    2 * (erdos260Constants.c0 * manuscriptEps) = manuscriptKappa / 2048 := by
  have hc0 : erdos260Constants.c0 = manuscriptC0 := rfl
  rw [hc0]
  unfold manuscriptC0 manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps
  norm_num

/-- **The sparsity block size** `m₀ := ⌈3(r+1)/64⌉` (ℕ ceiling division), the per-start owned-block
size of the deep-shell Hall surface. -/
def towerSparsityBlock (ctx : ActualFailureContext) : ℕ :=
  (3 * (ctx.n24CarryData.r + 1) + 63) / 64

/-- `m₀ ≥ 1` always. -/
theorem towerSparsityBlock_pos (ctx : ActualFailureContext) :
    1 ≤ towerSparsityBlock ctx := by
  unfold towerSparsityBlock; omega

/-- **`m₀ = 1` on every shell with `r ≤ 20`** — the sparsity constraint is automatic there. -/
theorem towerSparsityBlock_eq_one_of_r_le_20 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r ≤ 20) : towerSparsityBlock ctx = 1 := by
  unfold towerSparsityBlock; omega

/-- **The density floor `ρ_D·L ≤ m₀`** — from the genuine order pin `r = ⌊κL⌋` (so `κL < r+1`)
and the ceiling division (`3(r+1) ≤ 64·m₀`). -/
theorem towerRhoD_mul_L_le_block (ctx : ActualFailureContext) :
    towerRhoD * (shellLadderDepth ctx : ℝ) ≤ (towerSparsityBlock ctx : ℝ) := by
  have hfloor : manuscriptKappa * (shellLadderDepth ctx : ℝ) < (ctx.n24CarryData.r : ℝ) + 1 := by
    rw [n24CarryData_r_eq_floor ctx]
    exact Nat.lt_floor_add_one _
  have hblock : 3 * (ctx.n24CarryData.r + 1) ≤ 64 * towerSparsityBlock ctx := by
    unfold towerSparsityBlock; omega
  have hblockR : (3 : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ 64 * (towerSparsityBlock ctx : ℝ) := by exact_mod_cast hblock
  unfold towerRhoD
  nlinarith [hfloor, hblockR]

/-! ## 2.  The sharp shallow/deep threshold — `L ≤ 328965` ⟺ `ρ_D·L ≤ 1` (`51·L ≤ 2^24`)

The demanded per-start density is `y* := ρ_D·L`; `⌈y*⌉ ≤ 1` (the free regime) is exactly
`51·L ≤ 16777216`, i.e. `L ≤ 328965` (note `51·328965 = 16777215 = 2^24 − 1`: one short of
exact).  Beyond it, `⌈y*⌉ ≥ 2` and the genuine deep residual is needed. -/

/-- The shallow-shell depth bound `L ≤ 328965` (`X = 2^L ≤ 2^328965`). -/
def towerShallowDepthBound : ℕ := 328965

/-- **The `⌈y*⌉` dichotomy**: the demanded density `y* = ρ_D·n ≤ 1` iff `n ≤ 328965`. -/
theorem towerDemand_le_one_iff_shallow (n : ℕ) :
    towerRhoD * (n : ℝ) ≤ 1 ↔ n ≤ towerShallowDepthBound := by
  rw [towerRhoD_eq]
  constructor
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    have hn : (328966 : ℝ) ≤ (n : ℝ) := by
      have : 328966 ≤ n := by unfold towerShallowDepthBound at hcon; omega
      exact_mod_cast this
    linarith
  · intro h
    have hn : (n : ℝ) ≤ 328965 := by
      have : n ≤ 328965 := by unfold towerShallowDepthBound at h; omega
      exact_mod_cast this
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith

/-- **The shallow scalar**: `c₀·(2ε·L) ≤ ξ/6` for `L ≤ 328965` — the direct width-cap budget
(numerically: `17·L/2^29 ≤ 1/96 ⟺ 1632·L ≤ 2^29`). -/
theorem towerShallow_scalar {L : ℝ} (hL0 : 0 ≤ L)
    (hL : L ≤ (towerShallowDepthBound : ℝ)) :
    erdos260Constants.c0 * (2 * manuscriptEps * L) ≤ erdos260Constants.ξ / 6 := by
  have hc0 : erdos260Constants.c0 = 17 / 16777216 := by
    have h : erdos260Constants.c0 = manuscriptC0 := rfl
    rw [h]
    unfold manuscriptC0 manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps
    norm_num
  have hxi : erdos260Constants.ξ = manuscriptXi := rfl
  have heps : manuscriptEps = 1 / 64 := rfl
  have hb : (towerShallowDepthBound : ℝ) = 328965 := by
    unfold towerShallowDepthBound; norm_num
  rw [hb] at hL
  rw [hc0, hxi, heps]
  unfold manuscriptXi
  linarith

/-- **Sharpness — the direct width-cap argument FAILS on every deep shell**: for `L ≥ 328966` the
scalar `c₀·(2ε·L) ≤ ξ/6` is false.  (This refutes only the *direct* shallow argument, not the
count `(★)` itself; the deep count needs the genuine per-start sparsity.) -/
theorem towerShallow_scalar_false_of_deep {L : ℝ}
    (hL : (328966 : ℝ) ≤ L) :
    ¬ erdos260Constants.c0 * (2 * manuscriptEps * L) ≤ erdos260Constants.ξ / 6 := by
  intro hle
  have hc0 : erdos260Constants.c0 = 17 / 16777216 := by
    have h : erdos260Constants.c0 = manuscriptC0 := rfl
    rw [h]
    unfold manuscriptC0 manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps
    norm_num
  have hxi : erdos260Constants.ξ = manuscriptXi := rfl
  have heps : manuscriptEps = 1 / 64 := rfl
  rw [hc0, hxi, heps] at hle
  unfold manuscriptXi at hle
  linarith

/-- **Deep shells have `r ≥ 21`**: `L ≥ 328966 ⟹ κ·L ≥ 21 ⟹ r = ⌊κL⌋ ≥ 21`. -/
theorem r_ge_21_of_deep (ctx : ActualFailureContext)
    (hdeep : towerShallowDepthBound < shellLadderDepth ctx) :
    21 ≤ ctx.n24CarryData.r := by
  have hL : (328966 : ℝ) ≤ (shellLadderDepth ctx : ℝ) := by
    have : 328966 ≤ shellLadderDepth ctx := by
      unfold towerShallowDepthBound at hdeep; omega
    exact_mod_cast this
  have h21 : (21 : ℝ) ≤ manuscriptKappa * (shellLadderDepth ctx : ℝ) := by
    rw [towerKappa_eq]
    linarith
  rw [n24CarryData_r_eq_floor ctx]
  exact Nat.le_floor h21

/-- **`r ≤ 20` shells are shallow**: `r ≤ 20 ⟹ L ≤ 323824 ≤ 328965`.  (Contrapositive of
`r_ge_21_of_deep`.) -/
theorem shallow_of_r_le_20 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r ≤ 20) :
    shellLadderDepth ctx ≤ towerShallowDepthBound := by
  by_contra hcon
  rw [not_le] at hcon
  have := r_ge_21_of_deep ctx hcon
  omega

/-- `m₀ ≥ 2` on every deep shell (`r ≥ 21`). -/
theorem two_le_towerSparsityBlock_of_deep (ctx : ActualFailureContext)
    (hdeep : towerShallowDepthBound < shellLadderDepth ctx) :
    2 ≤ towerSparsityBlock ctx := by
  have hr := r_ge_21_of_deep ctx hdeep
  unfold towerSparsityBlock
  omega

/-! ## 3.  Unconditional field discharges — boundary exclusion and the width cap

These hold for **every** actual failure context, with no shallow/deep hypothesis. -/

/-- **Boundary exclusion, closed unconditionally for EVERY route and class**: the carry start set
is the window `Ico (firstIndexAbove X) (firstIndexAbove X + |supportShell|)`, and
`firstIndexAbove X ≥ 1` because the shell has a support hit at or below `X`.  So `0` is never a
routed start. -/
theorem routedFibre_zero_notMem (ctx : ActualFailureContext)
    (route : ℕ → Fin 7) (cls : Fin 7) :
    0 ∉ routedFibre ctx.n24CarryData route cls := by
  intro h0
  have hwin : shellStart ctx ≤ 0 :=
    (mem_window_of_mem_fibre ctx route cls h0).1
  have hpos : 1 ≤ shellStart ctx :=
    ctx.n24CarryData.carry.hits.firstIndexAbove_pos_of_supportCount_pos
      ctx.n24SupportCount_pos
  omega

/-- **The `hbdry` field of `Class2ActiveFloorCount` is a theorem** (not a residual). -/
theorem class2_hbdry_unconditional (ctx : ActualFailureContext) :
    0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 :=
  routedFibre_zero_notMem ctx (genuineChargeRoute ctx) 2

/-- **The class-2 fibre count is capped by the shell width**: the fibre filters the start window
`Ico i (i + K)` of width `K = |supportShell d X|`. -/
theorem class2_fibre_card_le_shellWidth (ctx : ActualFailureContext) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card ≤ shellWidth ctx := by
  have hsub : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2
      ⊆ ctx.n24CarryData.starts :=
    fun k hk => mem_starts_of_mem_fibre ctx (genuineChargeRoute ctx) 2 hk
  have hcard := Finset.card_le_card hsub
  rw [n24Starts_eq_window, Nat.card_Ico] at hcard
  omega

/-- **The positive-density failure cap in shell-field form**: `|supportShell| < c₀·X`
(`ctx.hfailure`, transported through the `rfl` pins `shell_d` / `shell_X`). -/
theorem class2_shellWidth_lt_c0X (ctx : ActualFailureContext) :
    ((shellWidth ctx : ℕ) : ℝ) < erdos260Constants.c0 * (ctx.shell.X : ℝ) := by
  have h := ctx.hfailure
  unfold shellWidth
  rw [ActualFailureContext.shell_d, ActualFailureContext.shell_X]
  exact h

/-! ## 4.  The shallow-shell unconditional closure

For `L ≤ 328965` the count `(★)` follows outright:
`#fibre₂ · 2εL ≤ |supportShell| · 2εL < c₀X · 2εL ≤ (ξ/6)·X`. -/

/-- **The shallow-shell active-floor count `(★)`, unconditional.** -/
theorem class2_count_of_shallow (ctx : ActualFailureContext)
    (hshallow : shellLadderDepth ctx ≤ towerShallowDepthBound) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ)
        * positivePart (2 * ctx.n24CarryData.Y)
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  have hL0 : (0 : ℝ) ≤ (shellLadderDepth ctx : ℝ) := Nat.cast_nonneg _
  have hX0 : (0 : ℝ) ≤ (ctx.shell.X : ℝ) := Nat.cast_nonneg _
  have hYnn : (0 : ℝ) ≤ 2 * ctx.n24CarryData.Y := by
    have h := towerSD_Y_nonneg ctx; linarith
  have hp : positivePart (2 * ctx.n24CarryData.Y)
      = 2 * manuscriptEps * (shellLadderDepth ctx : ℝ) := by
    rw [le_positivePart_self hYnn, towerSD_Y_eq ctx]; ring
  have hcardR : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ)
      ≤ ((shellWidth ctx : ℕ) : ℝ) := by
    exact_mod_cast class2_fibre_card_le_shellWidth ctx
  have hwidth : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ)
      ≤ erdos260Constants.c0 * (ctx.shell.X : ℝ) :=
    le_trans hcardR (class2_shellWidth_lt_c0X ctx).le
  have hscalar := towerShallow_scalar (L := (shellLadderDepth ctx : ℝ)) hL0
    (by exact_mod_cast hshallow)
  have hpnn : (0 : ℝ) ≤ positivePart (2 * ctx.n24CarryData.Y) := positivePart_nonneg _
  calc ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ)
        * positivePart (2 * ctx.n24CarryData.Y)
      ≤ (erdos260Constants.c0 * (ctx.shell.X : ℝ))
          * positivePart (2 * ctx.n24CarryData.Y) :=
        mul_le_mul_of_nonneg_right hwidth hpnn
    _ = (erdos260Constants.c0 * (2 * manuscriptEps * (shellLadderDepth ctx : ℝ)))
          * (ctx.shell.X : ℝ) := by rw [hp]; ring
    _ ≤ erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
        mul_le_mul_of_nonneg_right hscalar hX0
    _ = erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by ring

/-- **The shallow-shell Tower core, closed unconditionally**: a full `Class2ActiveFloorCount`
for every actual failing shell with `L ≤ 328965` — both fields are theorems. -/
def class2ActiveFloorCount_ofShallow (ctx : ActualFailureContext)
    (hshallow : shellLadderDepth ctx ≤ towerShallowDepthBound) :
    Class2ActiveFloorCount ctx where
  hbdry := class2_hbdry_unconditional ctx
  hcount := class2_count_of_shallow ctx hshallow

/-- The shallow-shell I.4.1 slot, end-to-end: `routedClassMassOf … 2 ≤ ξ·X/6`. -/
theorem class2TowerSubMass_ofShallow (ctx : ActualFailureContext)
    (hshallow : shellLadderDepth ctx ≤ towerShallowDepthBound) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (class2ActiveFloorCount_ofShallow ctx hshallow).htowerSubMass

/-- **The `r ≤ 20` regime is closed**: every shell with descent order `r = ⌊κL⌋ ≤ 20`
(equivalently `L ≤ 323824`, `X ≤ 2^323824`) carries an unconditional `Class2ActiveFloorCount`. -/
def class2ActiveFloorCount_of_r_le_20 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r ≤ 20) : Class2ActiveFloorCount ctx :=
  class2ActiveFloorCount_ofShallow ctx (shallow_of_r_le_20 ctx hr)

/-! ## 5.  The deep-shell landing lemma (closed) and the named deep residual

`towerSD_window_lands` discharges the shell-landing obligation for ANY hit index inside the
genuine start window — `X < a j ≤ 2X` and `d (a j) = 1` come from the hit sequence itself
(`firstIndexAbove_spec`, `a_le_two_mul_of_lt_add_card`, `hit_mem_supportShell`).  What remains
genuinely open on deep shells is only the **Hall marginal** at block size `m₀`. -/

/-- **Window landing, closed unconditionally**: every hit index in the genuine start window
`[firstIndexAbove X, firstIndexAbove X + |supportShell|)` lands in the dyadic shell support. -/
theorem towerSD_window_lands (ctx : ActualFailureContext) {j : ℕ}
    (hlo : shellStart ctx ≤ j) (hhi : j < shellStart ctx + shellWidth ctx) :
    ctx.n24CarryData.a j ∈ supportShell ctx.d ctx.X := by
  have hgt : ctx.shell.X < ctx.n24CarryData.a j := by
    have hspec : ctx.shell.X < ctx.n24CarryData.a (shellStart ctx) :=
      ctx.n24CarryData.carry.hits.firstIndexAbove_spec ctx.shell.X
    have hmono : ctx.n24CarryData.a (shellStart ctx) ≤ ctx.n24CarryData.a j :=
      ctx.n24CarryData.carry.hits.strict.monotone hlo
    exact lt_of_lt_of_le hspec hmono
  have hle : ctx.n24CarryData.a j ≤ 2 * ctx.shell.X :=
    ctx.n24CarryData.carry.hits.a_le_two_mul_of_lt_add_card ctx.shell.X hhi
  have hmem := ctx.n24CarryData.carry.hits.hit_mem_supportShell hgt hle
  rwa [ActualFailureContext.shell_d, ActualFailureContext.shell_X] at hmem

/-- **The deep-shell window residual** — the genuinely open K.1.3/§25.1 data for ONE deep shell:

* `W k` — the (possibly overlapping) hit-index descent window owned by the class-2 start `k`;
* `hlands` — each window index lands in the shell under the genuine carry enumeration
  (dischargeable via `ofRangeWindows` + the closed `towerSD_window_lands`);
* `hmarg` — **the Hall marginal** `m₀·|S| ≤ |⋃_{k∈S} W k|` over the genuine class-2 fibre, at the
  pinned block size `m₀ = ⌈3(r+1)/64⌉ ≥ ρ_D·L` — the no-large-run semiperiodic density +
  maximal-disjoint-selection content (manuscript Appendix K.2 Fine–Wilf + Lemma K.1.3).

All scalar/boundary fields of the Hall surface are *pinned theorems* here, not data. -/
structure Class2DeepShellWindowData (ctx : ActualFailureContext) where
  /-- The hit-index descent window owned by each class-2 start. -/
  W : ℕ → Finset ℕ
  /-- Each owned window index lands in the shell under the genuine carry enumeration. -/
  hlands : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      ∀ j ∈ W k, ctx.n24CarryData.a j ∈ supportShell ctx.d ctx.X
  /-- **The Hall marginal** at the pinned block size `m₀`. -/
  hmarg : ∀ S ⊆ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      towerSparsityBlock ctx * S.card ≤ (S.biUnion W).card

namespace Class2DeepShellWindowData

/-- **The landing field discharged**: build the deep window residual from windows contained in the
genuine start range `[firstIndexAbove X, firstIndexAbove X + |supportShell|)` — only the Hall
marginal remains as data. -/
def ofRangeWindows (ctx : ActualFailureContext)
    (W : ℕ → Finset ℕ)
    (hrange : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      W k ⊆ Finset.Ico (shellStart ctx) (shellStart ctx + shellWidth ctx))
    (hmarg : ∀ S ⊆ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      towerSparsityBlock ctx * S.card ≤ (S.biUnion W).card) :
    Class2DeepShellWindowData ctx where
  W := W
  hlands := by
    intro k hk j hj
    have hjmem := hrange k hk hj
    rw [Finset.mem_Ico] at hjmem
    exact towerSD_window_lands ctx hjmem.1 hjmem.2
  hmarg := hmarg

/-- **Wiring into the existing Hall surface** (no proof duplicated): the deep window residual
inhabits `Class2HallIndexSDRResidual` with every scalar/boundary field supplied by the pinned
theorems — `ρ_D = 3κ/64`, `ε = 1/64`, `L = shellLadderDepth`, `Y = εL`, the exact K.4 equality,
the proved boundary exclusion, and the proved block floor `ρ_D·L ≤ m₀`. -/
def toHallResidual {ctx : ActualFailureContext}
    (D : Class2DeepShellWindowData ctx) : Class2HallIndexSDRResidual ctx where
  rhoD := towerRhoD
  eps := manuscriptEps
  L := (shellLadderDepth ctx : ℝ)
  hrhoD_pos := towerRhoD_pos
  hL_pos := towerSD_L_pos ctx
  hYnn := towerSD_Y_nonneg ctx
  hcalib := towerSD_calib ctx
  huniform := le_of_eq towerUniform_exact
  hbdry := class2_hbdry_unconditional ctx
  W := D.W
  m := towerSparsityBlock ctx
  hmfloor := towerRhoD_mul_L_le_block ctx
  hlands := D.hlands
  hmarg := D.hmarg

end Class2DeepShellWindowData

/-- Per-context form of the proved chain `Class2IndexSDR → Class2ShellSDR →
Class2OwnershipPacking → Class2AreaPacking → Class2ActiveFloorCount` (the body of the existing
`towerCount_ofIndexSDR`, exposed per context for the shallow/deep case split). -/
def class2ActiveFloorCountOfIndexSDR {ctx : ActualFailureContext}
    (S : Class2IndexSDR ctx) : Class2ActiveFloorCount ctx :=
  Class2ActiveFloorCount.ofAreaPacking
    (Class2AreaPacking.ofOwnershipPacking
      (Class2OwnershipPacking.ofShellSDR S.toShellSDR))

/-- **The Tower core from the deep window residual** (any shell): Hall selection → index SDR →
ownership/area packing → active-floor count, all through the existing proved bridges. -/
def Class2DeepShellWindowData.toActiveFloorCount {ctx : ActualFailureContext}
    (D : Class2DeepShellWindowData ctx) : Class2ActiveFloorCount ctx :=
  class2ActiveFloorCountOfIndexSDR D.toHallResidual.toIndexSDR

/-! ## 6.  The total bridge — shallow closed + deep residual ⟹ the full V3 Tower field -/

/-- **The deep-shell residual surface**: window/Hall data demanded ONLY on genuinely deep shells
(`L ≥ 328966`, equivalently `r ≥ 21`).  Shallow shells are closed unconditionally and demand
nothing. -/
abbrev Class2DeepShellResidual : Type :=
  ∀ ctx : ActualFailureContext,
    towerShallowDepthBound < shellLadderDepth ctx → Class2DeepShellWindowData ctx

/-- **The total bridge**: the deep-shell residual alone discharges the full V3/P9 Tower field
`∀ ctx, Class2ActiveFloorCount ctx` — shallow shells (`L ≤ 328965`) go through the unconditional
direct closure, deep shells through the Hall/SDR chain. -/
def class2ActiveFloorCount_ofShallowDeep (R : Class2DeepShellResidual) :
    ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx := fun ctx =>
  if h : shellLadderDepth ctx ≤ towerShallowDepthBound then
    class2ActiveFloorCount_ofShallow ctx h
  else
    (R ctx (by omega)).toActiveFloorCount

/-- The routed class-2 Tower sub-mass slot from the total bridge: `routedClassMassOf … 2 ≤ ξ·X/6`
for every failing shell. -/
theorem class2TowerSubMass_ofShallowDeep (R : Class2DeepShellResidual)
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (class2ActiveFloorCount_ofShallowDeep R ctx).htowerSubMass

/-- **The exact `P9V3RunResidual.towerCount` / `Erdos260MinimalResidualV3.towerCount` /
`TowerRunGenuineResidual.towerCount` field shape**, from the deep windows alone. -/
def p9V3TowerCount_ofShallowDeep (R : Class2DeepShellResidual) :
    ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  class2ActiveFloorCount_ofShallowDeep R

/-- The I.3.1 Tower separated-leaf provider from the shallow/deep surface (feeds the global
assembly's `tower` slot through the existing `TowerClass2GenuineLeaf` endpoint). -/
def towerSeparatedLocalLeafProviderOfShallowDeep (R : Class2DeepShellResidual) :
    ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ) :=
  towerSeparatedLocalLeafProviderOfActiveFloorCount (class2ActiveFloorCount_ofShallowDeep R)

/-! ## 7.  Honest machine-readable status -/

/-- The precise status of the Tower / Class 2 closure after this module. -/
def towerShallowDeepStatus : List String :=
  [ "CLOSED UNCONDITIONALLY (boundary exclusion, EVERY shell/route/class) — " ++
      "routedFibre_zero_notMem / class2_hbdry_unconditional: 0 is never a routed start, since " ++
      "starts = Ico (firstIndexAbove X) (firstIndexAbove X + |supportShell|) (n24Starts_eq_window) " ++
      "and firstIndexAbove X >= 1 (firstIndexAbove_pos_of_supportCount_pos + n24SupportCount_pos). " ++
      "The hbdry field of Class2ActiveFloorCount is a THEOREM, not a residual.",
    "CLOSED UNCONDITIONALLY (shallow shells L <= 328965, X <= 2^328965) — " ++
      "class2ActiveFloorCount_ofShallow / class2_count_of_shallow: the count (*) " ++
      "#fibre2 * positivePart(2Y) <= xi*X/6 holds outright via #fibre2 <= |supportShell| " ++
      "(window containment, class2_fibre_card_le_shellWidth) < c0*X (the genuine failure cap " ++
      "ctx.hfailure, class2_shellWidth_lt_c0X) and the K.4 scalar 2*c0*eps*L <= xi/6 " ++
      "(towerShallow_scalar). NO SDR/dense-marker/Hall machinery. In particular every r <= 20 " ++
      "shell (L <= 323824, X <= 2^323824) is closed: class2ActiveFloorCount_of_r_le_20.",
    "SHARP THRESHOLD (proved both ways) — towerShallow_scalar holds iff the demanded per-start " ++
      "density y* = rhoD*L <= 1 iff L <= 328965 (towerDemand_le_one_iff_shallow; 51*L <= 2^24, " ++
      "and 51*328965 = 2^24 - 1). towerShallow_scalar_false_of_deep: the direct width-cap " ++
      "argument FAILS for every L >= 328966 — the ceil(y*) <= 1 vs >= 2 case split is exact. " ++
      "Deep shells have r >= 21 (r_ge_21_of_deep) and m0 >= 2 (two_le_towerSparsityBlock_of_deep).",
    "CALIBRATION PINS (rfl / norm_num, verified against erdos260Constants and K.4) — " ++
      "towerSD_Y_eq: Y = eps*L by rfl through the GapData -> ... -> n24CarryData chain (the " ++
      "CNLMultiChargeUnconditional n24CarryData_Y_eq pin, restated module-locally); " ++
      "ActualFailureContext.shell_d: ctx.shell.d = ctx.d by rfl (@[simp], the shell_X twin); " ++
      "towerRhoD = 3*kappa/64 = 51/2^24 with EXACT K.4 equality 2*(c0*eps) = (xi/6)*rhoD = " ++
      "kappa/2048 (towerUniform_exact, towerUniform_eq_kappa_div); towerSparsityBlock m0 = " ++
      "ceil(3(r+1)/64) with rhoD*L <= m0 proved from r = floor(kappa*L) " ++
      "(towerRhoD_mul_L_le_block); m0 = 1 for r <= 20 (towerSparsityBlock_eq_one_of_r_le_20).",
    "CLOSED UNCONDITIONALLY (deep landing geometry) — towerSD_window_lands: every hit index in " ++
      "the genuine start window lands in supportShell d X (X < a j <= 2X via firstIndexAbove_spec " ++
      "/ a_le_two_mul_of_lt_add_card, d(a j) = 1 from the hit sequence). " ++
      "Class2DeepShellWindowData.ofRangeWindows discharges the hlands field outright for windows " ++
      "inside the start range.",
    "REDUCED (deep shells L >= 328966, NOT closed) — Class2DeepShellResidual: per deep shell, " ++
      "windows W k plus the HALL MARGINAL m0*|S| <= |biUnion W| over the genuine class-2 fibre. " ++
      "This is the single genuinely open datum: the no-large-run semiperiodic per-start density " ++
      "+ maximal-disjoint selection (manuscript Appendix K.2 Fine-Wilf + Lemma K.1.3). It is NOT " ++
      "provable from the formalized band conditions: Fine-Wilf applies only to genuinely periodic " ++
      "windows and the Sec. 25.1 semiperiodic matching is not available unconditionally; the " ++
      "proved HitSequence gap bounds control the TOTAL shell support, never per-start ownership " ++
      "(TowerSDRCore audit). No fabricated witness is supplied.",
    "WIRED THROUGH EXISTING BRIDGES (no duplicated proofs) — Class2DeepShellWindowData." ++
      "toHallResidual supplies every scalar/boundary field of Class2HallIndexSDRResidual from " ++
      "the pinned theorems; then the proved chain toIndexSDR (Hall selection, SDRSelectionCore) " ++
      "-> toShellSDR -> Class2OwnershipPacking.ofShellSDR -> Class2AreaPacking." ++
      "ofOwnershipPacking -> Class2ActiveFloorCount.ofAreaPacking (class2ActiveFloorCount" ++
      "OfIndexSDR) delivers the Tower core.",
    "TOTAL BRIDGE (proved) — class2ActiveFloorCount_ofShallowDeep : Class2DeepShellResidual -> " ++
      "forall ctx, Class2ActiveFloorCount ctx, by the L <= 328965 case split. " ++
      "p9V3TowerCount_ofShallowDeep is the exact towerCount field shape of P9V3RunResidual / " ++
      "Erdos260MinimalResidualV3 / TowerRunGenuineResidual; class2TowerSubMass_ofShallowDeep " ++
      "gives the routed I.4.1 slot <= xi*X/6; towerSeparatedLocalLeafProviderOfShallowDeep " ++
      "feeds the I.3.1 leaf endpoint.",
    "HONESTY (density rate is a true WEAKENING of the manuscript demand) — the formal Hall " ++
      "surface leaves rhoD free, constrained only by the K.4 huniform; the pin rhoD = 3*kappa/64 " ++
      "= 51/2^24 ~ 3.04e-6 is 16777216/204 ~ 82241x smaller than the manuscript's q0 = 1 density " ++
      "rho0(Q) = 1/(4*q0) = 1/4, and smaller than 1/(4*q0) for every q0 <= 82241. The deep " ++
      "residual therefore demands strictly less than the manuscript supplies at those denominators.",
    "NON-DEGENERATE — every closure runs over the genuine routed class-2 fibre of " ++
      "genuineChargeRoute with the genuine carry data ctx.n24CarryData (real hit enumeration, " ++
      "real start window, real failure cap); the shallow closure fabricates no window, marker, " ++
      "or singleton witness; the deep residual is demanded only on genuinely deep shells and " ++
      "carries the real Hall data." ]

theorem towerShallowDeepStatus_nonempty : towerShallowDeepStatus ≠ [] := by
  simp [towerShallowDeepStatus]

/-! ## 8.  Axiom-cleanliness audit -/

#print axioms ActualFailureContext.shell_d
#print axioms towerSD_Y_eq
#print axioms towerSD_Y_nonneg
#print axioms towerSD_calib
#print axioms towerSD_L_pos
#print axioms towerKappa_eq
#print axioms towerRhoD_eq
#print axioms towerRhoD_pos
#print axioms towerUniform_exact
#print axioms towerUniform_eq_kappa_div
#print axioms towerSparsityBlock_pos
#print axioms towerSparsityBlock_eq_one_of_r_le_20
#print axioms towerRhoD_mul_L_le_block
#print axioms towerDemand_le_one_iff_shallow
#print axioms towerShallow_scalar
#print axioms towerShallow_scalar_false_of_deep
#print axioms r_ge_21_of_deep
#print axioms shallow_of_r_le_20
#print axioms two_le_towerSparsityBlock_of_deep
#print axioms routedFibre_zero_notMem
#print axioms class2_hbdry_unconditional
#print axioms class2_fibre_card_le_shellWidth
#print axioms class2_shellWidth_lt_c0X
#print axioms class2_count_of_shallow
#print axioms class2ActiveFloorCount_ofShallow
#print axioms class2TowerSubMass_ofShallow
#print axioms class2ActiveFloorCount_of_r_le_20
#print axioms towerSD_window_lands
#print axioms Class2DeepShellWindowData.ofRangeWindows
#print axioms Class2DeepShellWindowData.toHallResidual
#print axioms class2ActiveFloorCountOfIndexSDR
#print axioms Class2DeepShellWindowData.toActiveFloorCount
#print axioms class2ActiveFloorCount_ofShallowDeep
#print axioms class2TowerSubMass_ofShallowDeep
#print axioms p9V3TowerCount_ofShallowDeep
#print axioms towerSeparatedLocalLeafProviderOfShallowDeep
#print axioms towerShallowDeepStatus_nonempty

end

end Erdos260
