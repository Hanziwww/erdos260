import Erdos260.DensePackScaleObstruction
import Erdos260.ReturnAnchoredUnconditional
import Erdos260.DensePackLandsShiftCore

/-!
# DensePack corrected closure — the class-3 routing pin, the per-regime collapse, and the
faithful marker term

This module (NEW; it edits no existing file) pushes the class-3 ("dense packing") corrected
atom `DensePackCorrectedResidue` (`DensePackScaleObstruction.lean`) to its sharpest checked
boundary.  Everything here is budget-generic and additive.

## 1.  The class-3 routing pin (the analogue of `mem_class1Fibre_iff` / `mem_class4Fibre_iff`)

Class 3 fires on the FIRST branch of `genuineChargeRoute` (`towerClsOfShell = densePack`),
so — unlike class 4 — there is no exceptional `cnlTail` sub-branch to exclude.  The sharp
membership characterization is

```
k ∈ genuineDensePackStarts ctx
  ⟺ k ∈ starts ∧ 129·L + 64 ≤ 64·gapWindow(k, r) ∧ canonGap q K_k = 3
```

(`mem_densePackStarts_iff`, `mem_class3Fibre_iff`, `densePackStarts_eq_pinnedFilter`): the
high-excess floor in exact `ℕ` form (`Y_le_windowExcess_iff_gapWindow`) plus the E.13 band-3
window `4·K_k ≤ q < 8·K_k` (`canonGap_eq_three_iff`).  Consequences: the orbit band/step pins
(`densePackStarts_orbit_band`, `densePackStarts_orbit_step`: the successor numerator is
EXACTLY `8·K_k − q`), and the small-modulus closure `q < 5 ⟹ genuineDensePackStarts = ∅`
(`densePackStarts_empty_of_modulus_lt_five` — the band-3 window needs `q ≥ 4` and `q` odd).

**No orbit-only count bound exists**: at `q = 7, K = 1` the slope orbit is a band-3 FIXED
POINT (`slopeOrbit_seven_one_fixed`, `band3_pin_all_indices_q7`), so the band pin alone never
bounds `|genuineDensePackStarts|`.  Count bounds must come from the gap-window pin.

## 2.  The gate geometry: emptiness is the interior field on gated shells

Under the numeric gate `class3Gate ctx := 64·(r+1)·(L+B+1) < 129·L + 64`, the PROVED dyadic
gap ceiling `hitGap ≤ L+B+1` (`n24_hitGap_le_window`) forces every dense start's descent
window past the shell-window top (`densePackStarts_window_overrun`), confining the start set
to the top `r + 1` boundary band (`densePackStarts_card_le_of_gapCeiling`).  Hence on gated
shells the K.1 interior field is EQUIVALENT to start-set emptiness
(`class3Interior_iff_densePackStarts_empty`) — the exact class-3 analogue of the Return
module's `class4Interior_iff_fibre_empty`.  Regime pins: the gate holds automatically at
`r = 0` (all `L ≤ 15420`; there the start set is pinned inside the SINGLE topmost window
start, `densePackStarts_top_of_r_eq_zero`) and FAILS on every `r ≥ 2` shell
(`not_class3Gate_of_r_ge_two`), so the gate boundary lives entirely inside `r ≤ 1`.

**Why full unconditional emptiness is out of reach at this layer**: the one gap the ceiling
cannot reach is `hitGap a (i+K−1) = a(i+K) − a(i+K−1)` — the first hit after the dyadic shell
is unconstrained by the model, so a topmost-band start can carry an arbitrarily large gap
window, satisfying the high-excess pin.  This is the same top-band escape that stopped the
class-1 and class-4 emptiness attempts; the honest closure is the equivalence above plus the
named arithmetic forms below.

## 3.  The faithful class-3 marker term and the deep-shell cover in exact `ℕ` form

`termDensePack (faithfulCapacityPhases budget ctx) = |proofV4DensePackActualPoints ctx.shell|`
definitionally (`termDensePack_faithful_eq` — the class-3 mirror of `termCnl_faithful_eq`,
through the proved marker audit `densePackMarkers_eq_actualPoints`).  On deep shells the
corrected multiplier is the exact `ℕ` cast `(r+1)·(L+B+1) − (2L+1)`
(`densePackCorrectedMult_eq_natCast_of_r_ge_one`), so the amortized cover is EQUIVALENT to
the pure `ℕ` inequality

```
|genuineDensePackStarts ctx| · ((r+1)·(L+B+1) − (2L+1)) ≤ |proofV4DensePackActualPoints ctx.shell|
```

(`amortizedCover_iff_nat_of_r_ge_one`), with the named sufficient form by the unconditional
width count `|starts₃| ≤ K` (`amortizedCover_of_width_arith`) and the forcing direction: on
deep marker-free shells any cover provider certifies start-set emptiness
(`densePackStarts_empty_of_cover_marker_free`).

## 4.  The named emptiness atom, the regime-split residual, and the bridges

* `Class3StartsEmpty := ∀ ctx, genuineDensePackStarts ctx = ∅` — the single named Prop that
  closes the WHOLE corrected atom: `DensePackCorrectedResidue.ofStartsEmpty` inhabits
  `DensePackCorrectedResidue budget` for EVERY budget (density and interior vacuous, cover
  free), no `hroute` needed.  `class3StartsEmpty_iff_pinned` is its necessary-and-sufficient
  arithmetic form; `class3StartsEmpty_of_pinned_arithmetic` folds in the proved band closure
  (`q ≥ 5`); `class3StartsEmpty_of_regime_arithmetic` additionally folds the proved top-band
  confinement into the gated case.  Endpoint: `erdos260_p9V3_of_class3StartsEmpty`.
* `DensePackRegimeSplitResidual budget` — the sharpest per-regime surface: `gatedEmpty` (one
  emptiness Prop on gated shells — including ALL `r = 0`) + the three corrected fields gated
  to UNGATED shells only.  `DensePackRegimeSplitResidual.toCorrected` and
  `DensePackCorrectedResidue.toRegimeSplit` prove the two surfaces EQUIVALENT
  (`nonempty_densePackCorrected_iff_regimeSplit`) — so the corrected atom IS exactly:
  "gated emptiness" + "deep ungated density/interior/cover", and nothing more is hidden.
  Endpoint: `erdos260_p9V3_of_densePackRegimeSplit`.
* Obstruction-side consequences of the equivalence: ANY provider of the corrected residue
  certifies start-set emptiness on every gated shell
  (`DensePackCorrectedResidue.densePackStarts_empty_of_gate`, with `r = 0` / `L ≤ 15420`
  numeral forms) — the interior field is exactly that strong there, no stronger.

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## 1.  The E.13 band-3 pin and the sharp class-3 membership characterization -/

/-- The L.3.1 band classifier hits `densePack` exactly on band index `3`. -/
theorem towerExitClassOfGap_eq_densePack_iff (g : ℕ) :
    towerExitClassOfGap g = TowerExitClass.densePack ↔ g = 3 := by
  constructor
  · intro h
    rcases g with _ | _ | _ | _ | _ | n
    · cases h
    · cases h
    · cases h
    · rfl
    · cases h
    · cases h
  · intro h
    subst h
    rfl

/-- **The E.13 band-3 window**: `canonGap q K = 3` iff `4K ≤ q < 8K` (for `K ≥ 1`). -/
theorem canonGap_eq_three_iff {q K : ℕ} (hK : 1 ≤ K) :
    canonGap q K = 3 ↔ 4 * K ≤ q ∧ q < 8 * K := by
  unfold canonGap
  constructor
  · intro h
    have hlog : Nat.log 2 (q / K) = 2 := by omega
    have hne : q / K ≠ 0 := by
      intro h0
      rw [h0, Nat.log_zero_right] at hlog
      exact absurd hlog (by norm_num)
    have h4 : 4 ≤ q / K := by
      have hpow := Nat.pow_log_le_self 2 hne
      rw [hlog] at hpow
      norm_num at hpow
      exact hpow
    have h8 : q / K < 8 := by
      have hpow := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (q / K)
      rw [hlog] at hpow
      norm_num at hpow
      exact hpow
    exact ⟨(Nat.le_div_iff_mul_le hK).mp h4, (Nat.div_lt_iff_lt_mul hK).mp h8⟩
  · rintro ⟨h4, h8⟩
    have h4' : 4 ≤ q / K := (Nat.le_div_iff_mul_le hK).mpr h4
    have h8' : q / K < 8 := (Nat.div_lt_iff_lt_mul hK).mpr h8
    have hlog : Nat.log 2 (q / K) = 2 :=
      Nat.log_eq_of_pow_le_of_lt_pow (by norm_num; omega) (by norm_num; omega)
    omega

/-- The L.3.1 classifier routes to `densePack` exactly on band index `3` of the recurrent
slope orbit. -/
theorem towerClsOfShell_eq_densePack_iff (ctx : ActualFailureContext) (k : ℕ) :
    towerClsOfShell ctx k = TowerExitClass.densePack
      ↔ canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 3 := by
  rw [towerClsOfShell_eq_band]
  exact towerExitClassOfGap_eq_densePack_iff _

/-- **The sharp class-3 membership characterization** (the class-3 analogue of
`mem_class1Fibre_iff` / `mem_class4Fibre_iff`, stated on the budget-free
`genuineDensePackStarts`): `k` is a genuine dense start iff `k` is a carry-window start with
the high-excess gap-window floor `129L + 64 ≤ 64·gapWindow` and the E.13 band-3 pin
`canonGap q K_k = 3`. -/
theorem mem_densePackStarts_iff (ctx : ActualFailureContext) (k : ℕ) :
    k ∈ genuineDensePackStarts ctx
      ↔ k ∈ ctx.n24CarryData.starts
        ∧ 129 * shellLadderDepth ctx + 64
            ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 3 := by
  rw [mem_genuineDensePackStarts, mem_highExcessStarts,
    Y_le_windowExcess_iff_gapWindow, towerClsOfShell_eq_band,
    towerExitClassOfGap_eq_densePack_iff, and_assoc]

/-- **The sharp class-3 fibre membership characterization** on the genuine route. -/
theorem mem_class3Fibre_iff (ctx : ActualFailureContext) (k : ℕ) :
    k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 3
      ↔ k ∈ ctx.n24CarryData.starts
        ∧ 129 * shellLadderDepth ctx + 64
            ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 3 := by
  rw [mem_routedFibre, genuineChargeRoute_eq_three_iff, ← mem_genuineDensePackStarts,
    mem_densePackStarts_iff]

/-- The sharp class-3 fibre membership characterization, for any budget routing through the
genuine first-obstruction route. -/
theorem mem_class3Fibre_iff_of_route
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (hroute : ∀ ctx : ActualFailureContext, (budget ctx).route = genuineChargeRoute ctx)
    (ctx : ActualFailureContext) (k : ℕ) :
    k ∈ routedFibre ctx.n24CarryData (budget ctx).route 3
      ↔ k ∈ ctx.n24CarryData.starts
        ∧ 129 * shellLadderDepth ctx + 64
            ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 3 :=
  (mem_routedFibre_three_iff_densePack hroute ctx k).trans (mem_densePackStarts_iff ctx k)

/-- The class-3 fibre of the bare genuine route IS the dense start set (route-literal form of
the classifier↔fibre bridge). -/
theorem class3Fibre_eq_densePackStarts (ctx : ActualFailureContext) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 3 = genuineDensePackStarts ctx := by
  ext k
  rw [mem_routedFibre, genuineChargeRoute_eq_three_iff, ← mem_genuineDensePackStarts]

/-- **The dense start set IS the doubly-pinned window filter** (irreducible arithmetic form). -/
theorem densePackStarts_eq_pinnedFilter (ctx : ActualFailureContext) :
    genuineDensePackStarts ctx
      = ctx.n24CarryData.starts.filter (fun k =>
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ∧ canonGap (class1SlopeDatum ctx).q
                (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 3) := by
  ext k
  rw [Finset.mem_filter, mem_densePackStarts_iff]

/-! ## 2.  The orbit pins and the small-modulus closure -/

/-- **The class-3 band pin**: every genuine dense start has its slope-orbit canonical-gap
band index EXACTLY `3`. -/
theorem densePackStarts_canonGap_eq (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ genuineDensePackStarts ctx) :
    canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 3 :=
  ((mem_densePackStarts_iff ctx k).mp hk).2.2

/-- **The class-3 orbit-band pin**: the slope-orbit numerator at every dense start sits in
the dyadic band `4·K_k ≤ q < 8·K_k`, i.e. `q/8 < K_k ≤ q/4`. -/
theorem densePackStarts_orbit_band (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ genuineDensePackStarts ctx) :
    4 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
        ≤ (class1SlopeDatum ctx).q
      ∧ (class1SlopeDatum ctx).q
        < 8 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k := by
  have hband := densePackStarts_canonGap_eq ctx hk
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k
  exact (canonGap_eq_three_iff horb.1).mp hband

/-- **The class-3 orbit-step pin**: at every dense start the E.12/E.13 successor numerator is
EXACTLY `8·K_k − q` (the band-3 carry-doubling step). -/
theorem densePackStarts_orbit_step (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ genuineDensePackStarts ctx) :
    slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (k + 1)
      = 8 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
        - (class1SlopeDatum ctx).q := by
  have hband := densePackStarts_canonGap_eq ctx hk
  have hstep : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (k + 1)
      = boundedSlopeStep (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) := rfl
  rw [hstep]
  unfold boundedSlopeStep
  rw [hband]
  norm_num

/-- **A nonempty dense start set forces an odd modulus `q ≥ 5`**: the band `4K ≤ q` needs
`q ≥ 4`, and `q` is odd. -/
theorem modulus_ge_five_of_densePackStarts_nonempty (ctx : ActualFailureContext)
    (h : (genuineDensePackStarts ctx).Nonempty) :
    5 ≤ (class1SlopeDatum ctx).q := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨h4, h8⟩ := densePackStarts_orbit_band ctx hk
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k
  obtain ⟨m, hm⟩ := (class1SlopeDatum ctx).hq_odd
  have h1 := horb.1
  omega

/-- **Small-modulus closure**: the dense start set is PROVABLY EMPTY on every shell whose
closed AP-subfibre modulus is `< 5` (`q ∈ {1, 3}`) — the E.13 band-3 window `4K ≤ q < 8K` is
unsatisfiable below `q = 5`. -/
theorem densePackStarts_empty_of_modulus_lt_five (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q < 5) :
    genuineDensePackStarts ctx = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have h5 := modulus_ge_five_of_densePackStarts_nonempty ctx ⟨k, hk⟩
  omega

/-! ### The band-3 fixed point — no orbit-only count bound exists

At `q = 7, K = 1` the canonical band is `3` and the E.13 step fixes `K`: the orbit is
band-3-pinned at EVERY index.  So the third (band) pin alone can never bound
`|genuineDensePackStarts|`; count bounds must come from the gap-window pin (§3). -/

/-- `canonGap 7 1 = 3` (the band-3 window `4 ≤ 7 < 8` at `K = 1`). -/
theorem canonGap_seven_one : canonGap 7 1 = 3 := by
  unfold canonGap
  rw [Nat.div_one]
  have hlog : Nat.log 2 7 = 2 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  omega

/-- The E.13 step fixes `K = 1` at `q = 7`: `2^3·1 − 7 = 1`. -/
theorem boundedSlopeStep_seven_one : boundedSlopeStep 7 1 = 1 := by
  unfold boundedSlopeStep
  rw [canonGap_seven_one]
  norm_num

/-- **The band-3 fixed point**: the recurrent slope orbit at `q = 7, K₀ = 1` is constantly
`1`. -/
theorem slopeOrbit_seven_one_fixed : ∀ j : ℕ, slopeOrbit 7 1 j = 1 := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      show boundedSlopeStep 7 (slopeOrbit 7 1 j) = 1
      rw [ih]
      exact boundedSlopeStep_seven_one

/-- **No orbit-only count bound**: at the band-3 fixed point `q = 7, K₀ = 1` EVERY index
carries the band-3 pin, so the band pin alone never bounds the dense-start count. -/
theorem band3_pin_all_indices_q7 (j : ℕ) :
    canonGap 7 (slopeOrbit 7 1 j) = 3 := by
  rw [slopeOrbit_seven_one_fixed j]
  exact canonGap_seven_one

/-! ## 3.  The numeric gate, the window confinement, and the count bounds -/

/-- **The class-3 numeric gate**: the proved dyadic gap ceiling `(r+1)(L+B+1)` undercuts the
high-excess gap-window pin `(129L+64)/64`.  Under it every dense start is confined to the top
`r + 1` boundary band of the shell window. -/
def class3Gate (ctx : ActualFailureContext) : Prop :=
  64 * ((ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
    < 129 * shellLadderDepth ctx + 64

/-- The gate holds automatically on every `r = 0` shell (largeness gate `B + 25 ≤ L`). -/
theorem class3Gate_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) : class3Gate ctx := by
  unfold class3Gate
  have hB : carryB ctx.shell.Q + 25 ≤ shellLadderDepth ctx := ctx.shell_carryLarge
  rw [hr]
  omega

/-- The gate holds on every shell in the explicit numeral range `L ≤ 15420` (`r = ⌊κL⌋ = 0`). -/
theorem class3Gate_of_L_le (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 15420) : class3Gate ctx :=
  class3Gate_of_r_eq_zero ctx (n24_r_eq_zero_of_L_le ctx hL)

/-- **The gate FAILS on every `r ≥ 2` shell**: `64·3·(L+B+1) ≥ 192L > 129L + 64`. -/
theorem not_class3Gate_of_r_ge_two (ctx : ActualFailureContext)
    (hr : 2 ≤ ctx.n24CarryData.r) : ¬ class3Gate ctx := by
  unfold class3Gate
  rw [not_lt]
  have h3 : 3 * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
      ≤ (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hL : 28 ≤ shellLadderDepth ctx := shellLadderDepth_ge ctx
  omega

/-- The gate confines the descent order: `class3Gate ctx → r ≤ 1` (the gate boundary lives
entirely inside the `r ≤ 1` shells). -/
theorem class3Gate_r_le_one (ctx : ActualFailureContext) (hg : class3Gate ctx) :
    ctx.n24CarryData.r ≤ 1 := by
  by_contra h
  exact not_class3Gate_of_r_ge_two ctx (by omega) hg

/-- Every dense start lies in the dyadic shell index window `i ≤ k < i + K`. -/
theorem densePackStarts_mem_window (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ genuineDensePackStarts ctx) :
    ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X ≤ k
      ∧ k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card := by
  have hstart : k ∈ ctx.n24CarryData.starts := genuineDensePackStarts_subset_starts ctx hk
  rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hstart
  exact hstart

/-- **The window-overrun pin.**  Under the numeric gate, every dense start's descent window
must overrun the shell window: `firstIndexAbove X + |supportShell d X| ≤ k + r + 1`.  (The
proved ceiling `hitGap ≤ L+B+1` on the window interior caps `gapWindow` below the high-excess
pin.) -/
theorem densePackStarts_window_overrun (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ genuineDensePackStarts ctx)
    (hnum : class3Gate ctx) :
    ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card
      ≤ k + ctx.n24CarryData.r + 1 := by
  unfold class3Gate at hnum
  by_contra hint
  have hint' : k + ctx.n24CarryData.r + 1
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card := Nat.lt_of_not_le hint
  have hgap : ∀ m ∈ Finset.range (ctx.n24CarryData.r + 1),
      hitGap ctx.n24CarryData.a (k + m)
        ≤ shellLadderDepth ctx + carryB ctx.shell.Q + 1 := by
    intro m hm
    rw [Finset.mem_range] at hm
    exact n24_hitGap_le_window ctx (by omega)
  have hsum : gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ≤ (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
    unfold gapWindow
    calc ∑ m ∈ Finset.range (ctx.n24CarryData.r + 1), hitGap ctx.n24CarryData.a (k + m)
        ≤ ∑ _m ∈ Finset.range (ctx.n24CarryData.r + 1),
            (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := Finset.sum_le_sum hgap
      _ = (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hY : ctx.n24CarryData.Y
      ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T :=
    (mem_highExcessStarts.mp ((mem_genuineDensePackStarts ctx k).mp hk).1).2
  have hpin := (Y_le_windowExcess_iff_gapWindow ctx k).mp hY
  have h64 : 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ≤ 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) :=
    Nat.mul_le_mul_left 64 hsum
  omega

/-- **The boundary-band cardinality bound**: under the numeric gate the dense start set has
at most `r + 1` elements (it sits inside the top `r + 1` positions of the shell window). -/
theorem densePackStarts_card_le_of_gapCeiling (ctx : ActualFailureContext)
    (hnum : class3Gate ctx) :
    (genuineDensePackStarts ctx).card ≤ ctx.n24CarryData.r + 1 := by
  have hsub : genuineDensePackStarts ctx
      ⊆ Finset.Ico
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1))
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) := by
    intro k hk
    have hover := densePackStarts_window_overrun ctx hk hnum
    have hwin := densePackStarts_mem_window ctx hk
    rw [Finset.mem_Ico]
    omega
  calc (genuineDensePackStarts ctx).card
      ≤ (Finset.Ico
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1))
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card)).card :=
        Finset.card_le_card hsub
    _ ≤ ctx.n24CarryData.r + 1 := by
        rw [Nat.card_Ico]
        omega

/-- **The unconditional width count**: `|genuineDensePackStarts| ≤ K = |supportShell d X|`
(no gate needed — the start set lives in the shell index window). -/
theorem densePackStarts_card_le_width (ctx : ActualFailureContext) :
    (genuineDensePackStarts ctx).card ≤ (supportShell ctx.shell.d ctx.shell.X).card := by
  have h := genuineDensePackStarts_card_le_starts ctx
  have hcard : ctx.n24CarryData.starts.card = (supportShell ctx.shell.d ctx.shell.X).card := by
    rw [cnlMulti_starts_eq_window, Nat.card_Ico]
    omega
  omega

/-- **`r = 0` shells: the dense start set is pinned to the SINGLE topmost window start**
`k = firstIndexAbove X + |supportShell d X| − 1` (the gate is automatic). -/
theorem densePackStarts_top_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) {k : ℕ}
    (hk : k ∈ genuineDensePackStarts ctx) :
    k + 1 = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card := by
  have hover := densePackStarts_window_overrun ctx hk (class3Gate_of_r_eq_zero ctx hr)
  have hwin := densePackStarts_mem_window ctx hk
  omega

/-- **`r = 0` shells: at most ONE genuine dense start.** -/
theorem densePackStarts_card_le_one_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    (genuineDensePackStarts ctx).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro x hx y hy
  have hxe := densePackStarts_top_of_r_eq_zero ctx hr hx
  have hye := densePackStarts_top_of_r_eq_zero ctx hr hy
  omega

/-- Every shell with `L ≤ 15420` has at most ONE genuine dense start (the explicit-numeral
form of the `r = 0` boundary pinning). -/
theorem densePackStarts_card_le_one_of_L_le (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 15420) :
    (genuineDensePackStarts ctx).card ≤ 1 :=
  densePackStarts_card_le_one_of_r_eq_zero ctx (n24_r_eq_zero_of_L_le ctx hL)

/-! ## 4.  The K.1 gate dichotomy: on gated shells the interior field IS emptiness -/

/-- **The K.1 dichotomy.**  Under the numeric gate, the class-3 active-window interior field
is EQUIVALENT to the emptiness of the dense start set: a member would have to sit in the top
`r + 1` boundary band (overrun) and strictly below it (interior) at once.  The exact class-3
analogue of the Return module's `class4Interior_iff_fibre_empty`. -/
theorem class3Interior_iff_densePackStarts_empty (ctx : ActualFailureContext)
    (hnum : class3Gate ctx) :
    (∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card)
      ↔ genuineDensePackStarts ctx = ∅ := by
  constructor
  · intro hint
    rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    have h1 := hint k hk
    have h2 := densePackStarts_window_overrun ctx hk hnum
    omega
  · intro hempty k hk
    rw [hempty] at hk
    exact absurd hk (Finset.notMem_empty k)

/-- **`r = 0` shells: emptiness is ONE membership fact** — the dense start set is empty iff
the single topmost window start is not a genuine dense start. -/
theorem densePackStarts_empty_iff_top_notMem_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    genuineDensePackStarts ctx = ∅
      ↔ ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - 1
          ∉ genuineDensePackStarts ctx := by
  constructor
  · intro hempty
    rw [hempty]
    exact Finset.notMem_empty _
  · intro htop
    rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    have htopk := densePackStarts_top_of_r_eq_zero ctx hr hk
    have hke : k = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card - 1 := by omega
    rw [hke] at hk
    exact htop hk

/-- The K.1.1 coarea hit-density holds VACUOUSLY on any shell with an empty dense start set
(the brief's `r = 0` density check: density is free exactly where emptiness is available). -/
theorem densePackEndpointDensity_of_empty (ctx : ActualFailureContext)
    (h : genuineDensePackStarts ctx = ∅) :
    densePackEndpointDensity ctx := by
  intro k hk
  rw [h] at hk
  exact absurd hk (Finset.notMem_empty k)

/-- On gated shells the interior field already yields the K.1.1 density (via emptiness) — the
density component is NOT an independent residual there. -/
theorem densePackEndpointDensity_of_gate_interior (ctx : ActualFailureContext)
    (hg : class3Gate ctx)
    (hint : ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) :
    densePackEndpointDensity ctx :=
  densePackEndpointDensity_of_empty ctx
    ((class3Interior_iff_densePackStarts_empty ctx hg).mp hint)

/-! ## 5.  The faithful class-3 marker term and the deep-shell cover in exact `ℕ` form -/

/-- **The faithful class-3 phase term, evaluated** (the class-3 mirror of
`termCnl_faithful_eq`): for EVERY budget, `termDensePack` of the faithful capacity phases is
the cardinality of the shell's own actual-support marker set. -/
theorem termDensePack_faithful_eq
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData
      = ((proofV4DensePackActualPoints ctx.shell).card : ℝ) := by
  show ((densePackMarkers budget ctx).card : ℝ)
      = ((proofV4DensePackActualPoints ctx.shell).card : ℝ)
  rw [densePackMarkers_eq_actualPoints]

/-- The deep-shell corrected multiplier in `ℕ`: `(r+1)·(L+B+1) − (2L+1)` is positive for
`r ≥ 1` (it is `≥ 2B + 1 ≥ 3`). -/
theorem densePack_natMult_pos_of_r_ge_one (ctx : ActualFailureContext)
    (hr : 1 ≤ ctx.n24CarryData.r) :
    0 < (ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
        - (2 * shellLadderDepth ctx + 1) := by
  have h2 : 2 * densePackDyadicG0 ctx
      ≤ (ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx :=
    Nat.mul_le_mul_right _ (by omega)
  have hBL : carryB ctx.shell.Q + 25 ≤ shellLadderDepth ctx := ctx.shell_carryLarge
  have hG0 : densePackDyadicG0 ctx
      = shellLadderDepth ctx + carryB ctx.shell.Q + 1 := rfl
  omega

/-- **The deep-shell corrected multiplier is an exact `ℕ` cast**: for `r ≥ 1`,
`densePackCorrectedMult ctx = ((r+1)·(L+B+1) − (2L+1) : ℕ)` (the positive part is the value
itself; the `ℕ` subtraction does not truncate). -/
theorem densePackCorrectedMult_eq_natCast_of_r_ge_one (ctx : ActualFailureContext)
    (hr : 1 ≤ ctx.n24CarryData.r) :
    densePackCorrectedMult ctx
      = (((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
          - (2 * shellLadderDepth ctx + 1) : ℕ) : ℝ) := by
  have hge : 2 * shellLadderDepth ctx + 1
      ≤ (ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx := by
    have h2 : 2 * densePackDyadicG0 ctx
        ≤ (ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx :=
      Nat.mul_le_mul_right _ (by omega)
    have hBL : carryB ctx.shell.Q + 25 ≤ shellLadderDepth ctx := ctx.shell_carryLarge
    have hG0 : densePackDyadicG0 ctx
        = shellLadderDepth ctx + carryB ctx.shell.Q + 1 := rfl
    omega
  have hx : (0 : ℝ) ≤ ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ)
      - ctx.n24CarryData.T := by
    rw [densePackDyadicG0_cast_eq, cnlMulti_n24_T_eq]
    have hrR : (1 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := by exact_mod_cast hr
    have hBR : (1 : ℝ) ≤ (carryB ctx.shell.Q : ℝ) := by
      exact_mod_cast carryB_ctx_ge_one ctx
    have hLR : (0 : ℝ) ≤ (shellLadderDepth ctx : ℝ) := Nat.cast_nonneg _
    nlinarith
  unfold densePackCorrectedMult
  rw [le_positivePart_self hx, Nat.cast_sub hge]
  push_cast
  rw [cnlMulti_n24_T_eq]

/-- **The deep-shell amortized cover is a pure `ℕ` inequality**: for `r ≥ 1` (any budget),
the corrected K.1.2 cover holds iff
`|genuineDensePackStarts| · ((r+1)·(L+B+1) − (2L+1)) ≤ |proofV4DensePackActualPoints|`. -/
theorem amortizedCover_iff_nat_of_r_ge_one
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) (hr : 1 ≤ ctx.n24CarryData.r) :
    (((genuineDensePackStarts ctx).card : ℝ) * densePackCorrectedMult ctx
        ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData)
      ↔ (genuineDensePackStarts ctx).card
            * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
                - (2 * shellLadderDepth ctx + 1))
          ≤ (proofV4DensePackActualPoints ctx.shell).card := by
  rw [termDensePack_faithful_eq budget ctx,
    densePackCorrectedMult_eq_natCast_of_r_ge_one ctx hr, ← Nat.cast_mul, Nat.cast_le]

/-- **A named sufficient arithmetic form of the deep cover**: the unconditional width count
`|genuineDensePackStarts| ≤ K` reduces the cover to the start-free shell inequality
`K · ((r+1)·(L+B+1) − (2L+1)) ≤ |actualPoints|`. -/
theorem amortizedCover_of_width_arith
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) (hr : 1 ≤ ctx.n24CarryData.r)
    (h : (supportShell ctx.shell.d ctx.shell.X).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card) :
    ((genuineDensePackStarts ctx).card : ℝ) * densePackCorrectedMult ctx
      ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData := by
  rw [amortizedCover_iff_nat_of_r_ge_one budget ctx hr]
  exact le_trans (Nat.mul_le_mul_right _ (densePackStarts_card_le_width ctx)) h

/-- **The forcing direction of the deep cover**: on a deep (`r ≥ 1`) marker-free shell
(`proofV4DensePackActualPoints = ∅`), ANY amortized-cover provider certifies start-set
emptiness — the corrected K.1.2 component carries genuine content there. -/
theorem densePackStarts_empty_of_cover_marker_free
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) (hr : 1 ≤ ctx.n24CarryData.r)
    (hcover : ((genuineDensePackStarts ctx).card : ℝ) * densePackCorrectedMult ctx
        ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData)
    (hfree : proofV4DensePackActualPoints ctx.shell = ∅) :
    genuineDensePackStarts ctx = ∅ := by
  rw [amortizedCover_iff_nat_of_r_ge_one budget ctx hr, hfree, Finset.card_empty,
    Nat.le_zero, Nat.mul_eq_zero] at hcover
  rcases hcover with h | h
  · exact Finset.card_eq_zero.mp h
  · have hpos := densePack_natMult_pos_of_r_ge_one ctx hr
    omega

/-! ## 6.  The named emptiness atom `Class3StartsEmpty` and its closure power -/

/-- **The class-3 emptiness atom**: the genuine dense start set is empty on every
hypothetical failing shell.  Budget-free and route-free. -/
def Class3StartsEmpty : Prop :=
  ∀ ctx : ActualFailureContext, genuineDensePackStarts ctx = ∅

/-- **The emptiness atom in its sharpest necessary-and-sufficient arithmetic form**: no
carry-window start simultaneously realizes the gap-window floor and the band-3 pin. -/
theorem class3StartsEmpty_iff_pinned :
    Class3StartsEmpty
      ↔ ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
          ¬(129 * shellLadderDepth ctx + 64
                ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ∧ canonGap (class1SlopeDatum ctx).q
                (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 3) := by
  constructor
  · intro hemp ctx k hkstart hpins
    have hmem : k ∈ genuineDensePackStarts ctx :=
      (mem_densePackStarts_iff ctx k).mpr ⟨hkstart, hpins.1, hpins.2⟩
    rw [hemp ctx] at hmem
    exact Finset.notMem_empty k hmem
  · intro h ctx
    rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    rw [mem_densePackStarts_iff] at hk
    exact h ctx k hk.1 ⟨hk.2.1, hk.2.2⟩

/-- **The pinned arithmetic SUFFICIENT condition with the proved band closure folded in**: to
close the emptiness atom it suffices to refute the simultaneous pins on the shells surviving
the small-modulus closure (`q ≥ 5`), for window starts only. -/
theorem class3StartsEmpty_of_pinned_arithmetic
    (h : ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      5 ≤ (class1SlopeDatum ctx).q →
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) ≠ 3) :
    Class3StartsEmpty := by
  rw [class3StartsEmpty_iff_pinned]
  intro ctx k hkstart hpins
  obtain ⟨hgw, hband⟩ := hpins
  have hq5 : 5 ≤ (class1SlopeDatum ctx).q := by
    have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
      (class1SlopeDatum ctx).hK₀_lt k
    obtain ⟨h4, h8⟩ := (canonGap_eq_three_iff horb.1).mp hband
    obtain ⟨m, hm⟩ := (class1SlopeDatum ctx).hq_odd
    have h1 := horb.1
    omega
  exact h ctx k hkstart hq5 hgw hband

/-- **The pinned arithmetic sufficient condition with the proved TOP-BAND confinement also
folded in**: on gated shells the pins need only be refuted on the top `r + 1` boundary band
(`i + K ≤ k + r + 1`); ungated shells keep the full window obligation. -/
theorem class3StartsEmpty_of_regime_arithmetic
    (hgated : ∀ ctx : ActualFailureContext, class3Gate ctx →
      ∀ k ∈ ctx.n24CarryData.starts,
        ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card ≤ k + ctx.n24CarryData.r + 1 →
        ¬(129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          ∧ canonGap (class1SlopeDatum ctx).q
              (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 3))
    (hungated : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
      ∀ k ∈ ctx.n24CarryData.starts,
        ¬(129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          ∧ canonGap (class1SlopeDatum ctx).q
              (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 3)) :
    Class3StartsEmpty := by
  intro ctx
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have hmem := (mem_densePackStarts_iff ctx k).mp hk
  by_cases hg : class3Gate ctx
  · exact hgated ctx hg k hmem.1 (densePackStarts_window_overrun ctx hk hg)
      ⟨hmem.2.1, hmem.2.2⟩
  · exact hungated ctx hg k hmem.1 ⟨hmem.2.1, hmem.2.2⟩

namespace DensePackCorrectedResidue

variable {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}

/-- **FULL closure of the corrected class-3 atom from the single named emptiness Prop** (any
budget, NO route hypothesis): density and interior are vacuous, the amortized cover is the
free `0 ≤ termDensePack`. -/
def ofStartsEmpty (hempty : Class3StartsEmpty) :
    DensePackCorrectedResidue budget where
  density := fun ctx => densePackEndpointDensity_of_empty ctx (hempty ctx)
  interior := fun ctx => by
    intro k hk
    rw [hempty ctx] at hk
    exact absurd hk (Finset.notMem_empty k)
  amortizedCover := fun ctx => by
    rw [hempty ctx]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    exact termDensePack_faithful_nonneg budget ctx

/-- **OBSTRUCTION-SIDE consequence of the K.1 gate dichotomy**: ANY provider of the corrected
residue certifies start-set emptiness on every gated shell (its interior field is exactly
that strong there). -/
theorem densePackStarts_empty_of_gate (R : DensePackCorrectedResidue budget)
    (ctx : ActualFailureContext) (hg : class3Gate ctx) :
    genuineDensePackStarts ctx = ∅ :=
  (class3Interior_iff_densePackStarts_empty ctx hg).mp (R.interior ctx)

/-- Any corrected-residue provider certifies start-set emptiness on every `r = 0` shell. -/
theorem densePackStarts_empty_of_r_eq_zero (R : DensePackCorrectedResidue budget)
    (ctx : ActualFailureContext) (hr : ctx.n24CarryData.r = 0) :
    genuineDensePackStarts ctx = ∅ :=
  R.densePackStarts_empty_of_gate ctx (class3Gate_of_r_eq_zero ctx hr)

/-- Any corrected-residue provider certifies start-set emptiness on every shell with
`L ≤ 15420`. -/
theorem densePackStarts_empty_of_L_le (R : DensePackCorrectedResidue budget)
    (ctx : ActualFailureContext) (hL : shellLadderDepth ctx ≤ 15420) :
    genuineDensePackStarts ctx = ∅ :=
  R.densePackStarts_empty_of_gate ctx (class3Gate_of_L_le ctx hL)

end DensePackCorrectedResidue

/-- The class-3 routed fibre of any genuine-routed budget is empty under the emptiness atom. -/
theorem routedFibre_three_empty_of_class3StartsEmpty
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hroute : ∀ ctx : ActualFailureContext, (budget ctx).route = genuineChargeRoute ctx)
    (hempty : Class3StartsEmpty) (ctx : ActualFailureContext) :
    routedFibre ctx.n24CarryData (budget ctx).route 3 = ∅ := by
  rw [routedFibre_three_eq_densePackStarts hroute ctx]
  exact hempty ctx

/-- **The exact class-3 ledger field from the emptiness atom** (the capstone's `hDensePack`
slot, via the corrected bridge). -/
theorem class3Ledger_of_class3StartsEmpty
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hroute : ∀ ctx : ActualFailureContext, (budget ctx).route = genuineChargeRoute ctx)
    (hempty : Class3StartsEmpty) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 3
        ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  (DensePackCorrectedResidue.ofStartsEmpty hempty).hDensePackField hroute

/-! ## 7.  The regime-split residual — the sharpest per-regime surface, EQUIVALENT to the
corrected atom -/

/-- **The class-3 regime-split residual.**  On gated shells (all `r = 0`, part of `r = 1`)
the whole atom is the single emptiness Prop; on ungated shells (the rest of `r = 1`, all
`r ≥ 2`) the three corrected components are kept verbatim.  Equivalent to
`DensePackCorrectedResidue budget` (see `toCorrected` / `toRegimeSplit`); strictly sharper in
presentation: nothing is asked on gated shells beyond emptiness. -/
structure DensePackRegimeSplitResidual
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) where
  /-- Gated shells: the dense start set is empty (equivalent to the K.1 interior there). -/
  gatedEmpty : ∀ ctx : ActualFailureContext, class3Gate ctx →
    genuineDensePackStarts ctx = ∅
  /-- Ungated shells: the K.1.1 coarea hit-density at the descent endpoints. -/
  ungatedDensity : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
    densePackEndpointDensity ctx
  /-- Ungated shells: the K.1 active-window interior containment. -/
  ungatedInterior : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
    ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card
  /-- Ungated shells: the corrected K.1.2 amortized cover. -/
  ungatedCover : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
    ((genuineDensePackStarts ctx).card : ℝ) * densePackCorrectedMult ctx
      ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData

namespace DensePackRegimeSplitResidual

variable {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}

/-- **The regime split rebuilds the full corrected residue**: gated shells discharge all
three components through emptiness; ungated shells use the split data verbatim. -/
def toCorrected (R : DensePackRegimeSplitResidual budget) :
    DensePackCorrectedResidue budget where
  density := fun ctx => by
    by_cases hg : class3Gate ctx
    · exact densePackEndpointDensity_of_empty ctx (R.gatedEmpty ctx hg)
    · exact R.ungatedDensity ctx hg
  interior := fun ctx => by
    by_cases hg : class3Gate ctx
    · intro k hk
      rw [R.gatedEmpty ctx hg] at hk
      exact absurd hk (Finset.notMem_empty k)
    · exact R.ungatedInterior ctx hg
  amortizedCover := fun ctx => by
    by_cases hg : class3Gate ctx
    · rw [R.gatedEmpty ctx hg]
      simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
      exact termDensePack_faithful_nonneg budget ctx
    · exact R.ungatedCover ctx hg

end DensePackRegimeSplitResidual

/-- **The corrected residue projects onto the regime split** — `gatedEmpty` is the K.1 gate
dichotomy applied to the interior field; the ungated components restrict. -/
def DensePackCorrectedResidue.toRegimeSplit
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (R : DensePackCorrectedResidue budget) :
    DensePackRegimeSplitResidual budget where
  gatedEmpty := fun ctx hg => R.densePackStarts_empty_of_gate ctx hg
  ungatedDensity := fun ctx _ => R.density ctx
  ungatedInterior := fun ctx _ => R.interior ctx
  ungatedCover := fun ctx _ => R.amortizedCover ctx

/-- **The two surfaces are EQUIVALENT** — the corrected class-3 atom IS exactly "gated
emptiness + ungated density/interior/cover"; the split hides no strength and adds none. -/
theorem nonempty_densePackCorrected_iff_regimeSplit
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) :
    Nonempty (DensePackCorrectedResidue budget)
      ↔ Nonempty (DensePackRegimeSplitResidual budget) :=
  ⟨fun ⟨R⟩ => ⟨R.toRegimeSplit⟩, fun ⟨S⟩ => ⟨S.toCorrected⟩⟩

/-- Build the corrected residue directly from the four per-regime components (the parent
assembly's convenience constructor). -/
def densePackCorrectedOfRegimes
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (gatedEmpty : ∀ ctx : ActualFailureContext, class3Gate ctx →
      genuineDensePackStarts ctx = ∅)
    (ungatedDensity : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
      densePackEndpointDensity ctx)
    (ungatedInterior : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card)
    (ungatedCover : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
      ((genuineDensePackStarts ctx).card : ℝ) * densePackCorrectedMult ctx
        ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData) :
    DensePackCorrectedResidue budget :=
  DensePackRegimeSplitResidual.toCorrected
    ⟨gatedEmpty, ungatedDensity, ungatedInterior, ungatedCover⟩

/-! ## 8.  Endpoints -/

/-- **Erdős #260 (P9/V3 endpoint) with the class-3 slot reduced to the single named Prop
`Class3StartsEmpty`** (other atoms as hypotheses) — the class-3 mirror of
`erdos260_p9V3_of_class1FibreEmpty`. -/
theorem erdos260_p9V3_of_class3StartsEmpty
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (cnl : Class1CNLInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (hempty : Class3StartsEmpty) :
    Erdos260Statement :=
  erdos260_p9V3_of_densePackCorrected towerCount runResidual returnCharge chernoff cnl
    (DensePackCorrectedResidue.ofStartsEmpty hempty)

/-- **Erdős #260 (P9/V3 endpoint) with the class-3 slot carried by the regime-split
residual** — the sharpest per-regime input surface. -/
theorem erdos260_p9V3_of_densePackRegimeSplit
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (cnl : Class1CNLInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (split : DensePackRegimeSplitResidual
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)) :
    Erdos260Statement :=
  erdos260_p9V3_of_densePackCorrected towerCount runResidual returnCharge chernoff cnl
    split.toCorrected

/-! ## 9.  Honest status inventory -/

/-- Machine-readable status of the class-3 corrected-closure boundary after this module. -/
def densePackCorrectedClosureStatus : List String :=
  [ "PIN SETTLED (the class-3 routing pin, all shells) - mem_densePackStarts_iff / " ++
      "mem_class3Fibre_iff / mem_class3Fibre_iff_of_route / densePackStarts_eq_pinnedFilter: " ++
      "k is a genuine dense start IFF k is a carry-window start with the high-excess " ++
      "gap-window floor 129L+64 <= 64*gapWindow AND the E.13 band-3 pin canonGap q K_k = 3 " ++
      "(towerExitClassOfGap_eq_densePack_iff + canonGap_eq_three_iff: 4K <= q < 8K). Class 3 " ++
      "is the FIRST genuineChargeRoute branch, so unlike class 4 there is no exceptional " ++
      "sub-branch. Orbit pins: densePackStarts_orbit_band, densePackStarts_orbit_step " ++
      "(successor numerator EXACTLY 8K-q).",
    "CLOSED (small modulus) - densePackStarts_empty_of_modulus_lt_five: the dense start set " ++
      "is empty on every shell with AP-subfibre modulus q < 5 " ++
      "(modulus_ge_five_of_densePackStarts_nonempty: band-3 needs q >= 4 and q odd).",
    "OBSTRUCTION (no orbit-only count bound) - slopeOrbit_seven_one_fixed / " ++
      "band3_pin_all_indices_q7: at q = 7, K0 = 1 the slope orbit is a band-3 FIXED POINT " ++
      "(boundedSlopeStep 7 1 = 1), so EVERY index carries the band-3 pin; the band pin alone " ++
      "never bounds |genuineDensePackStarts|. Count bounds must use the gap-window pin.",
    "COUNT BOUNDS - densePackStarts_card_le_of_gapCeiling: under the numeric gate class3Gate " ++
      "(64(r+1)(L+B+1) < 129L+64) the start set sits in the top r+1 boundary band " ++
      "(densePackStarts_window_overrun) so card <= r+1; densePackStarts_card_le_width: " ++
      "unconditional card <= K = |supportShell|; r = 0: pinned to the SINGLE topmost window " ++
      "start (densePackStarts_top_of_r_eq_zero, card <= 1, numeral form L <= 15420). Gate " ++
      "regime pins: automatic at r = 0 (class3Gate_of_r_eq_zero), FAILS on every r >= 2 " ++
      "shell (not_class3Gate_of_r_ge_two), so the gate boundary lives inside r <= 1 " ++
      "(class3Gate_r_le_one).",
    "GATE DICHOTOMY (the class-3 analogue of class4Interior_iff_fibre_empty) - " ++
      "class3Interior_iff_densePackStarts_empty: on gated shells the K.1 interior field is " ++
      "EQUIVALENT to start-set emptiness; on r = 0 shells emptiness is ONE membership fact " ++
      "(densePackStarts_empty_iff_top_notMem_of_r_eq_zero). Hence ANY corrected-residue " ++
      "provider certifies gated emptiness (DensePackCorrectedResidue.densePackStarts_empty_" ++
      "of_gate / _of_r_eq_zero / _of_L_le) and the density component is NOT independent " ++
      "there (densePackEndpointDensity_of_gate_interior).",
    "WHY FULL UNCONDITIONAL EMPTINESS IS OUT OF REACH AT THIS LAYER - the proved ceiling " ++
      "n24_hitGap_le_window covers only indices j with j+1 < i+K; the single top gap " ++
      "hitGap a (i+K-1) = a(i+K) - a(i+K-1) is the first hit AFTER the dyadic shell and is " ++
      "unconstrained by the model, so a topmost-band start can satisfy the high-excess pin " ++
      "with one huge gap. This is the same top-band escape that stopped the class-1 and " ++
      "class-4 emptiness attempts; genuine emptiness needs the manuscript K.1 boundary " ++
      "geometry, supplied here as the named atoms below.",
    "FAITHFUL TERM EVALUATED - termDensePack_faithful_eq (the class-3 mirror of " ++
      "termCnl_faithful_eq): termDensePack(faithfulCapacityPhases budget ctx) = " ++
      "|proofV4DensePackActualPoints ctx.shell| for EVERY budget, through the proved marker " ++
      "audit densePackMarkers_eq_actualPoints. The term is a marker COUNT (nonnegative, " ++
      "termDensePack_faithful_nonneg), not an X-scaled mass.",
    "DEEP COVER IN EXACT NAT FORM - densePackCorrectedMult_eq_natCast_of_r_ge_one: on r >= 1 " ++
      "shells the corrected multiplier is the exact Nat cast (r+1)(L+B+1) - (2L+1) (positive, " ++
      "densePack_natMult_pos_of_r_ge_one); amortizedCover_iff_nat_of_r_ge_one: the corrected " ++
      "K.1.2 cover holds IFF |starts3| * ((r+1)(L+B+1) - (2L+1)) <= |actualPoints| in Nat; " ++
      "named sufficient form amortizedCover_of_width_arith (via the unconditional width " ++
      "count); forcing direction densePackStarts_empty_of_cover_marker_free: on deep " ++
      "marker-free shells any cover provider certifies emptiness.",
    "NAMED ATOM (full closure from one Prop) - Class3StartsEmpty := forall ctx, " ++
      "genuineDensePackStarts ctx = empty. DensePackCorrectedResidue.ofStartsEmpty inhabits " ++
      "the WHOLE corrected atom for EVERY budget with NO route hypothesis (density and " ++
      "interior vacuous, cover free). Sharp forms: class3StartsEmpty_iff_pinned (necessary " ++
      "AND sufficient); class3StartsEmpty_of_pinned_arithmetic (band closure q >= 5 folded " ++
      "in); class3StartsEmpty_of_regime_arithmetic (top-band confinement folded into the " ++
      "gated case). Transports: routedFibre_three_empty_of_class3StartsEmpty, " ++
      "class3Ledger_of_class3StartsEmpty (the exact capstone hDensePack field).",
    "REGIME SPLIT (equivalent surface) - DensePackRegimeSplitResidual budget: gatedEmpty " ++
      "(one emptiness Prop on gated shells, including ALL r = 0) + ungatedDensity/" ++
      "ungatedInterior/ungatedCover (the three corrected components on UNGATED shells only). " ++
      "DensePackRegimeSplitResidual.toCorrected and DensePackCorrectedResidue.toRegimeSplit " ++
      "prove the surfaces EQUIVALENT (nonempty_densePackCorrected_iff_regimeSplit): the " ++
      "corrected atom IS exactly gated emptiness + deep ungated K.1.1/K.1/K.1.2. " ++
      "Constructor densePackCorrectedOfRegimes; endpoints erdos260_p9V3_of_class3StartsEmpty " ++
      "and erdos260_p9V3_of_densePackRegimeSplit.",
    "RESIDUAL (honest, what remains open) - (a) gatedEmpty: emptiness on gated shells, " ++
      "equivalently no top-band start carries the two pins (the r = 0 case is the single " ++
      "topmost-start exclusion); (b) on ungated shells (part of r = 1, all r >= 2): the " ++
      "K.1.1 hit-density, the K.1 interior containment, and the corrected K.1.2 Nat cover " ++
      "|starts3| * ((r+1)(L+B+1) - (2L+1)) <= |actualPoints|. None of these is provably " ++
      "false on any regime (contrast the retired hScale scalar); all are implied by the " ++
      "single Class3StartsEmpty." ]

theorem densePackCorrectedClosureStatus_nonempty :
    densePackCorrectedClosureStatus ≠ [] := by
  simp [densePackCorrectedClosureStatus]

/-! ## 10.  Axiom-cleanliness audit -/

#print axioms towerExitClassOfGap_eq_densePack_iff
#print axioms canonGap_eq_three_iff
#print axioms towerClsOfShell_eq_densePack_iff
#print axioms mem_densePackStarts_iff
#print axioms mem_class3Fibre_iff
#print axioms mem_class3Fibre_iff_of_route
#print axioms class3Fibre_eq_densePackStarts
#print axioms densePackStarts_eq_pinnedFilter
#print axioms densePackStarts_canonGap_eq
#print axioms densePackStarts_orbit_band
#print axioms densePackStarts_orbit_step
#print axioms modulus_ge_five_of_densePackStarts_nonempty
#print axioms densePackStarts_empty_of_modulus_lt_five
#print axioms canonGap_seven_one
#print axioms boundedSlopeStep_seven_one
#print axioms slopeOrbit_seven_one_fixed
#print axioms band3_pin_all_indices_q7
#print axioms class3Gate_of_r_eq_zero
#print axioms class3Gate_of_L_le
#print axioms not_class3Gate_of_r_ge_two
#print axioms class3Gate_r_le_one
#print axioms densePackStarts_mem_window
#print axioms densePackStarts_window_overrun
#print axioms densePackStarts_card_le_of_gapCeiling
#print axioms densePackStarts_card_le_width
#print axioms densePackStarts_top_of_r_eq_zero
#print axioms densePackStarts_card_le_one_of_r_eq_zero
#print axioms densePackStarts_card_le_one_of_L_le
#print axioms class3Interior_iff_densePackStarts_empty
#print axioms densePackStarts_empty_iff_top_notMem_of_r_eq_zero
#print axioms densePackEndpointDensity_of_empty
#print axioms densePackEndpointDensity_of_gate_interior
#print axioms termDensePack_faithful_eq
#print axioms densePack_natMult_pos_of_r_ge_one
#print axioms densePackCorrectedMult_eq_natCast_of_r_ge_one
#print axioms amortizedCover_iff_nat_of_r_ge_one
#print axioms amortizedCover_of_width_arith
#print axioms densePackStarts_empty_of_cover_marker_free
#print axioms class3StartsEmpty_iff_pinned
#print axioms class3StartsEmpty_of_pinned_arithmetic
#print axioms class3StartsEmpty_of_regime_arithmetic
#print axioms DensePackCorrectedResidue.ofStartsEmpty
#print axioms DensePackCorrectedResidue.densePackStarts_empty_of_gate
#print axioms DensePackCorrectedResidue.densePackStarts_empty_of_r_eq_zero
#print axioms DensePackCorrectedResidue.densePackStarts_empty_of_L_le
#print axioms routedFibre_three_empty_of_class3StartsEmpty
#print axioms class3Ledger_of_class3StartsEmpty
#print axioms DensePackRegimeSplitResidual.toCorrected
#print axioms DensePackCorrectedResidue.toRegimeSplit
#print axioms nonempty_densePackCorrected_iff_regimeSplit
#print axioms densePackCorrectedOfRegimes
#print axioms erdos260_p9V3_of_class3StartsEmpty
#print axioms erdos260_p9V3_of_densePackRegimeSplit
#print axioms densePackCorrectedClosureStatus_nonempty

end

end Erdos260
