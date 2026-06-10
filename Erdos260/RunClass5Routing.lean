import Erdos260.RunSupportMaxCore
import Erdos260.ReturnAnchoredUnconditional

/-!
# Run / Class 5 — the routing pin settled (`RunClass5Routing`)

This module (NEW; it edits no existing file) settles the **class-5 routing pin** of the
genuine first-obstruction route — the Run analogue of the proved class-1 analysis
(`mem_class1Fibre_iff`, `CNLMultiChargeUnconditional`) and class-4 analysis
(`mem_class4Fibre_iff`, `ReturnAnchoredUnconditional`) — and converts it into the
sharpest honest closure surface for the Run atom
`RunClass5LeafSupportMaxCoreResidual` (`RunSupportMaxCore`).

## The settled routing pin (CLOSED)

The genuine route reaches class `5` through exactly two branches
(`genuineChargeRoute_eq_five_iff`): the L.3.1 tower exit `run` — the E.13 **band-1**
window `canonGap q K_k = 1`, i.e. `q < 2·K_k` (`canonGap_eq_one_iff`,
`towerExitClassOfGap_eq_run_iff`) — or the `cnlTail` band-4 exit refined by the run
classifier's local-spike band `runClsOfShell ctx k = 1`, i.e. `k ≠ 0` and the HEAVY
window floor `2Y ≤ windowExcess`, in exact `ℕ` form `130L + 64 ≤ 64·gapWindow`
(`two_Y_le_windowExcess_iff_gapWindow`, `runClsOfShell_eq_one_iff`).  Hence the **sharp
membership characterization** (`mem_class5Fibre_iff`, `class5Fibre_eq_pinnedFilter`):

  `k ∈ fibre₅  ↔  k ∈ starts ∧ 129L + 64 ≤ 64·gapWindow(k)
                  ∧ (canonGap q K_k = 1 ∨ (canonGap q K_k = 4 ∧ 130L + 64 ≤ 64·gapWindow(k)))`.

## What is PROVED about the pinned fibre (all unconditional)

* **Orbit-band pin** — every class-5 start has its slope-orbit numerator in the top
  dyadic band `q < 2·K_k` or in the band-4 window `8·K_k ≤ q < 16·K_k`
  (`class5Fibre_orbit_band`); below modulus `9` only the band-1 branch survives
  (`class5Fibre_canonGap_eq_one_of_modulus_lt_nine`).
* **Small-modulus emptiness (genuine, from the routing arithmetic)** — at modulus
  `q = 3` (the only odd modulus `2 ≤ q < 5`) the recurrent slope orbit is CONSTANT `1`
  from index `1` on (`slopeOrbit_three_tail`, `boundedSlopeStep_three`), its band is
  `canonGap 3 1 = 2` (the `returnPkg` band), and `0` is never a carry-window start —
  so the class-5 fibre is PROVABLY EMPTY: `class5Fibre_empty_of_modulus_lt_five`.
  (Sanity: this routes the `q = 3` mass to class 4, NOT to emptiness of all classes.)
* **Boundary confinement under the K.1 numeric gate** `64(r+1)(L+B+1) < 129L + 64`
  (automatic on every `r = 0` shell, i.e. ALL `L ≤ 15420`): every class-5 start
  overruns the shell window (`class5Fibre_window_overrun`), so the fibre sits in the
  top `r + 1` boundary band, `|fibre₅| ≤ r + 1` (`class5Fibre_card_le_of_gapCeiling`);
  at `r = 0` it is pinned to the SINGLE topmost window start
  (`class5Fibre_top_of_r_eq_zero`, `class5Fibre_card_le_one_of_r_eq_zero`,
  `class5Fibre_card_le_one_of_L_le`).

## The honest closure surfaces of the Run atom (proved bridges)

With the zero stage map `stageOf := fun _ => 0` the I.6S stage geometry COLLAPSES:
`runStageLen = 1` (`runStageLen_zeroStage`), so the finite L.4.2 half-decrease `hhalf`
is VACUOUS, and `runBaseFibre = fibre₅` (`runBaseFibre_zeroStage`).  Hence:

* `runCoreOfClass5ProductBound` — the whole Run atom from the ONE product inequality
  `c0·|fibre₅|·maxExcess ≤ (c⋆ξ/12)·|supportShell|`;
* `runCoreOfClass5FibreEmpty` — **a genuine FULL closure from fibre-emptiness**: the
  empty fibre has count `0` and max excess `0`, so the product bound is `0 ≤ nonneg`.
  Family form `runCoreOfClass5FibreEmptyFamily`, capstone endpoint
  `erdos260_of_class5FibreEmpty_and_highExcess`, and the necessary-and-sufficient
  arithmetic form `class5Fibre_empty_iff_pinned`;
* `runCoreOfModulusLtFive` — the UNCONDITIONAL closure on every shell with closed
  AP-subfibre modulus `< 5` (the proved `q = 3` emptiness);
* `class5Fibre_empty_of_gate_interior` / `runCoreOfGateInterior` — under the numeric
  gate, the shared K.1 active-window interior condition (the boundary residual every
  sibling class retains) ALONE forces fibre-emptiness, hence the FULL Run closure;
* `runCoreOfGateBoundary` — the strictly smaller gate-side residual: a window-excess
  bound on the `≤ r + 1` top boundary starts (a fibre-free, purely boundary-band
  datum) plus ONE scalar numeric at count `r + 1` closes the atom.

## Why NOT a fully unconditional `runCoreUnconditional` (honest obstruction)

Unconditional emptiness of the class-5 fibre is NOT provable from the routing
arithmetic: the band-1 window `q < 2K < 2q` is realized along the recurrent orbit for
moduli `q ≥ 5` (e.g. `q = 5`: the orbit `1 → 3 → 1 → …` alternates through the band-1
numerator `3`), so the band pin alone cannot refute membership; and on the surviving
boundary band the window excess has NO formalized ceiling (the dyadic gap estimate
`hitGap ≤ L + B + 1` covers only `j + 1 < firstIndexAbove X + |supportShell|`, which
the overrun starts escape by construction).  As in the class-1/class-4 analyses, the
hit-gap floor (a property of the actual hit sequence) and the band pin (a property of
the recurrent slope orbit) remain mutually unconstrained in the model.  The residual
surfaces above are therefore the sharpest honest forms.

No `sorry`, `axiom`, `admit`, or `native_decide`; no degenerate witness — the zero
stage map closures are exercised only on the genuinely empty fibre or with the
genuine product datum.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The E.13 band-1 window and the `run` band readout -/

/-- The L.3.1 band classifier hits `run` exactly on band index `1`. -/
theorem towerExitClassOfGap_eq_run_iff (g : ℕ) :
    towerExitClassOfGap g = TowerExitClass.run ↔ g = 1 := by
  constructor
  · intro h
    rcases g with _ | _ | _ | _ | _ | n
    · cases h
    · rfl
    · cases h
    · cases h
    · cases h
    · cases h
  · intro h
    subst h
    rfl

/-- **The E.13 band-1 window**: `canonGap q K = 1` iff `q < 2K` (for `K ≥ 1`) — the
topmost dyadic band, immediate re-entry. -/
theorem canonGap_eq_one_iff {q K : ℕ} (hK : 1 ≤ K) :
    canonGap q K = 1 ↔ q < 2 * K := by
  unfold canonGap
  constructor
  · intro h
    have hlog : Nat.log 2 (q / K) = 0 := by omega
    have h2 : q / K < 2 := by
      rcases Nat.log_eq_zero_iff.mp hlog with h' | h'
      · exact h'
      · omega
    exact (Nat.div_lt_iff_lt_mul hK).mp h2
  · intro h
    have h2 : q / K < 2 := (Nat.div_lt_iff_lt_mul hK).mpr h
    have hlog : Nat.log 2 (q / K) = 0 := Nat.log_eq_zero_iff.mpr (Or.inl h2)
    omega

/-! ## 2.  The run classifier's local-spike band in exact `ℕ` form -/

/-- The heavy window floor `2Y ≤ windowExcess` in exact `ℕ` form: with the pinned
`T = 2L + 1` and `Y = L/64` it reads `130·L + 64 ≤ 64·gapWindow` (the class-5 analogue
of `Y_le_windowExcess_iff_gapWindow`). -/
theorem two_Y_le_windowExcess_iff_gapWindow (ctx : ActualFailureContext) (k : ℕ) :
    2 * ctx.n24CarryData.Y
        ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ↔ 130 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r := by
  rw [cnlMulti_n24_T_eq, n24CarryData_Y_eq_div]
  have hL : (28 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
    exact_mod_cast shellLadderDepth_ge ctx
  unfold windowExcess positivePart
  constructor
  · intro h
    by_cases hle : ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ)
        - (2 * ((shellLadderDepth ctx : ℕ) : ℝ) + 1) ≤ 0
    · rw [max_eq_right hle] at h
      linarith
    · rw [max_eq_left (not_le.mp hle).le] at h
      have hreal : (130 : ℝ) * ((shellLadderDepth ctx : ℕ) : ℝ) + 64
          ≤ 64 * ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ) := by
        linarith
      exact_mod_cast hreal
  · intro h
    have hreal : (130 : ℝ) * ((shellLadderDepth ctx : ℕ) : ℝ) + 64
        ≤ 64 * ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [max_eq_left (by linarith)]
    linarith

/-- The L.4.1 run classifier selects the local-spike class `1` exactly on the heavy
band: `k ≠ 0` (not the boundary start) and `2Y ≤ windowExcess`. -/
theorem runClsOfShell_eq_one_iff (ctx : ActualFailureContext) (k : ℕ) :
    runClsOfShell ctx k = 1
      ↔ k ≠ 0
        ∧ 2 * ctx.n24CarryData.Y
            ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
              ctx.n24CarryData.T := by
  constructor
  · intro h
    unfold runClsOfShell at h
    split_ifs at h with h0 h2
    · exact absurd h (by decide)
    · exact ⟨h0, h2⟩
    · exact absurd h (by decide)
  · rintro ⟨h0, h2⟩
    unfold runClsOfShell
    rw [if_neg h0, if_pos h2]

/-! ## 3.  The sharp class-5 membership characterization (the routing pin)

The genuine first-obstruction route reaches class `5` either through the L.3.1 `run`
exit (the E.13 band-1 window) or through the `cnlTail` catch-all refined by the run
classifier's local-spike band (band-4 with the HEAVY floor `2Y ≤ windowExcess`).  This
is the class-5 analogue of the proved `mem_class1Fibre_iff` / `mem_class4Fibre_iff`. -/

/-- **The class-5 band pin**: every class-5 routed start of the genuine route is
band-1, or band-4 with the heavy gap-window floor `130L + 64 ≤ 64·gapWindow`. -/
theorem class5Fibre_band_pin (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5) :
    canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 1
      ∨ (canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4
          ∧ 130 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r) := by
  have hroute : genuineChargeRoute ctx k = 5 := (Finset.mem_filter.mp hk).2
  rcases (genuineChargeRoute_eq_five_iff ctx k).mp hroute with h | ⟨ht, hrun⟩
  · left
    rw [towerClsOfShell_eq_band] at h
    exact (towerExitClassOfGap_eq_run_iff _).mp h
  · right
    rw [towerClsOfShell_eq_band] at ht
    refine ⟨(towerExitClassOfGap_eq_cnlTail_iff _).mp ht, ?_⟩
    have h2Y := ((runClsOfShell_eq_one_iff ctx k).mp hrun).2
    exact (two_Y_le_windowExcess_iff_gapWindow ctx k).mp h2Y

/-- **The sharp class-5 membership characterization** (the class-5 analogue of
`mem_class1Fibre_iff` / `mem_class4Fibre_iff`): `k ∈ fibre₅` iff `k` is a carry-window
start with the high-excess gap-window floor `129L + 64 ≤ 64·gapWindow` and EITHER the
E.13 band-1 pin `canonGap q K_k = 1` OR the band-4 pin `canonGap q K_k = 4` with the
heavy floor `130L + 64 ≤ 64·gapWindow`. -/
theorem mem_class5Fibre_iff (ctx : ActualFailureContext) (k : ℕ) :
    k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5
      ↔ k ∈ ctx.n24CarryData.starts
        ∧ 129 * shellLadderDepth ctx + 64
            ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ (canonGap (class1SlopeDatum ctx).q
              (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 1
          ∨ (canonGap (class1SlopeDatum ctx).q
                (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4
              ∧ 130 * shellLadderDepth ctx + 64
                  ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r)) := by
  constructor
  · intro hk
    have hhigh := mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1
    exact ⟨hhigh.1, (Y_le_windowExcess_iff_gapWindow ctx k).mp hhigh.2,
      class5Fibre_band_pin ctx hk⟩
  · rintro ⟨hstart, hgw, hband⟩
    refine Finset.mem_filter.mpr
      ⟨mem_highExcessStarts.mpr
        ⟨hstart, (Y_le_windowExcess_iff_gapWindow ctx k).mpr hgw⟩, ?_⟩
    refine (genuineChargeRoute_eq_five_iff ctx k).mpr ?_
    rcases hband with h1 | ⟨h4, hheavy⟩
    · left
      rw [towerClsOfShell_eq_band]
      exact (towerExitClassOfGap_eq_run_iff _).mpr h1
    · right
      refine ⟨?_, ?_⟩
      · rw [towerClsOfShell_eq_band]
        exact (towerExitClassOfGap_eq_cnlTail_iff _).mpr h4
      · refine (runClsOfShell_eq_one_iff ctx k).mpr ⟨?_, ?_⟩
        · intro hk0
          rw [hk0] at hstart
          exact zero_notMem_n24Starts ctx hstart
        · exact (two_Y_le_windowExcess_iff_gapWindow ctx k).mpr hheavy

/-- **The class-5 fibre IS the pinned window filter** (irreducible arithmetic form). -/
theorem class5Fibre_eq_pinnedFilter (ctx : ActualFailureContext) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5
      = ctx.n24CarryData.starts.filter (fun k =>
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ∧ (canonGap (class1SlopeDatum ctx).q
                  (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 1
              ∨ (canonGap (class1SlopeDatum ctx).q
                    (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4
                  ∧ 130 * shellLadderDepth ctx + 64
                      ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r))) := by
  ext k
  rw [Finset.mem_filter, mem_class5Fibre_iff]

/-- **The class-5 orbit-band pin**: the slope-orbit numerator at every class-5 start
sits in the topmost dyadic band `q < 2·K_k` (band 1) or in the band-4 window
`8·K_k ≤ q < 16·K_k`. -/
theorem class5Fibre_orbit_band (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5) :
    (class1SlopeDatum ctx).q
        < 2 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
      ∨ (8 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q
          ∧ (class1SlopeDatum ctx).q
            < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) := by
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k
  rcases class5Fibre_band_pin ctx hk with h1 | ⟨h4, _⟩
  · exact Or.inl ((canonGap_eq_one_iff horb.1).mp h1)
  · exact Or.inr ((canonGap_eq_four_iff horb.1).mp h4)

/-- **The class-5 orbit-step pin**: at every class-5 start the E.12/E.13 successor
numerator is EXACTLY `2·K_k − q` (band-1 step) or `16·K_k − q` (band-4 step). -/
theorem class5Fibre_orbit_step (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5) :
    slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (k + 1)
        = 2 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
          - (class1SlopeDatum ctx).q
      ∨ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (k + 1)
        = 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
          - (class1SlopeDatum ctx).q := by
  have hstep : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (k + 1)
      = boundedSlopeStep (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) := rfl
  rcases class5Fibre_band_pin ctx hk with h1 | ⟨h4, _⟩
  · left
    rw [hstep]
    unfold boundedSlopeStep
    rw [h1]
    norm_num
  · right
    rw [hstep]
    unfold boundedSlopeStep
    rw [h4]
    norm_num

/-- **Below modulus `9` only the band-1 branch survives**: the band-4 window
`8K ≤ q < 16K` needs `q ≥ 9` (odd `q`, `K ≥ 1`), so on shells with closed AP-subfibre
modulus `< 9` every class-5 start carries the band-1 pin `canonGap q K_k = 1`. -/
theorem class5Fibre_canonGap_eq_one_of_modulus_lt_nine (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q < 9) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5) :
    canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 1 := by
  rcases class5Fibre_band_pin ctx hk with h1 | ⟨h4, _⟩
  · exact h1
  · exfalso
    have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
      (class1SlopeDatum ctx).hK₀_lt k
    obtain ⟨h8, h16⟩ := (canonGap_eq_four_iff horb.1).mp h4
    have h1k := horb.1
    obtain ⟨m, hm⟩ := (class1SlopeDatum ctx).hq_odd
    omega

/-! ## 4.  Genuine small-modulus emptiness: the `q = 3` orbit never leaves band 2

At the smallest admissible modulus `q = 3` the E.13 step is constant: both admissible
numerators step to `1` (`boundedSlopeStep_three`), so the recurrent orbit is the
constant `1` from index `1` on, whose band is `canonGap 3 1 = 2` — the `returnPkg`
band, neither `run` (band 1) nor `cnlTail` (band 4).  Since `0` is never a
carry-window start, the class-5 fibre is provably EMPTY.  (The mass is routed to
class 4 — NOT an all-classes-empty degeneracy.) -/

private theorem nat_log_two_three : Nat.log 2 3 = 1 :=
  Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)

/-- `canonGap 3 1 = 2`: the constant `q = 3` orbit value sits in the `returnPkg` band. -/
theorem canonGap_three_one : canonGap 3 1 = 2 := by
  unfold canonGap
  norm_num [nat_log_two_three]

/-- `canonGap 3 2 = 1` (the band-1 base case, reachable only at orbit index `0`). -/
theorem canonGap_three_two : canonGap 3 2 = 1 := by
  unfold canonGap
  norm_num [Nat.log_one_right]

/-- **The `q = 3` E.13 step is constant `1`** on the admissible numerators `{1, 2}`. -/
theorem boundedSlopeStep_three {K : ℕ} (hK1 : 1 ≤ K) (hK3 : K < 3) :
    boundedSlopeStep 3 K = 1 := by
  unfold boundedSlopeStep
  interval_cases K
  · norm_num [canonGap_three_one]
  · norm_num [canonGap_three_two]

/-- **The `q = 3` recurrent slope orbit is constant `1` from index `1` on.** -/
theorem slopeOrbit_three_tail (K₀ : ℕ) (hK1 : 1 ≤ K₀) (hK3 : K₀ < 3) :
    ∀ j : ℕ, slopeOrbit 3 K₀ (j + 1) = 1 := by
  intro j
  induction j with
  | zero =>
    have h : slopeOrbit 3 K₀ 1 = boundedSlopeStep 3 (slopeOrbit 3 K₀ 0) := rfl
    have h0 : slopeOrbit 3 K₀ 0 = K₀ := rfl
    rw [h, h0]
    exact boundedSlopeStep_three hK1 hK3
  | succ j ih =>
    have h : slopeOrbit 3 K₀ (j + 1 + 1)
        = boundedSlopeStep 3 (slopeOrbit 3 K₀ (j + 1)) := rfl
    rw [h, ih]
    exact boundedSlopeStep_three le_rfl (by norm_num)

/-- **Small-modulus closure (genuine emptiness THEOREM)**: the class-5 routed fibre of
the genuine route is PROVABLY EMPTY on every shell whose closed AP-subfibre modulus is
`< 5` (i.e. `q = 3`, the only odd modulus `≥ 2` below `5`): the orbit at every
carry-window index (`≥ 1`) is the constant `1`, whose band `canonGap 3 1 = 2` is
neither `run` nor `cnlTail`. -/
theorem class5Fibre_empty_of_modulus_lt_five (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q < 5) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have hq2 : 2 ≤ (class1SlopeDatum ctx).q := (class1SlopeDatum ctx).hq2
  obtain ⟨m, hm⟩ := (class1SlopeDatum ctx).hq_odd
  have hq3 : (class1SlopeDatum ctx).q = 3 := by omega
  have hstart : k ∈ ctx.n24CarryData.starts :=
    (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0] at hstart
    exact zero_notMem_n24Starts ctx hstart
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hKlt : (class1SlopeDatum ctx).K₀ < 3 := by
    have h := (class1SlopeDatum ctx).hK₀_lt
    omega
  have horb1 : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (j + 1) = 1 := by
    rw [hq3]
    exact slopeOrbit_three_tail (class1SlopeDatum ctx).K₀ (class1SlopeDatum ctx).hK₀_pos
      hKlt j
  rcases class5Fibre_band_pin ctx hk with h1 | ⟨h4, _⟩
  · rw [horb1, hq3, canonGap_three_one] at h1
    omega
  · rw [horb1, hq3, canonGap_three_one] at h4
    omega

/-! ## 5.  Boundary confinement under the K.1 numeric gate (mirror of class 1/4)

The carry starts are definitionally the dyadic shell window and the PROVED gap ceiling
`hitGap ≤ L + B + 1` holds strictly inside it.  The class-5 floor demands
`64·gapWindow ≥ 129L + 64`, so under the numeric gate `64(r+1)(L+B+1) < 129L + 64`
every class-5 start must push its descent window past the ceiling's reach. -/

/-- Every class-5 routed start lies in the dyadic shell index window `i ≤ k < i + K`. -/
theorem class5Fibre_mem_window (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5) :
    ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X ≤ k
      ∧ k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card := by
  have hstart : k ∈ ctx.n24CarryData.starts :=
    (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1
  rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hstart
  exact hstart

/-- **The window-overrun pin.**  Under the numeric gate `64·(r+1)·(L+B+1) < 129·L + 64`,
every class-5 start's descent window must overrun the shell window:
`firstIndexAbove X + |supportShell d X| ≤ k + r + 1`. -/
theorem class5Fibre_window_overrun (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card
      ≤ k + ctx.n24CarryData.r + 1 := by
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
  have hfloor : 129 * shellLadderDepth ctx + 64
      ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r :=
    ((mem_class5Fibre_iff ctx k).mp hk).2.1
  have h64 : 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ≤ 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) :=
    Nat.mul_le_mul_left 64 hsum
  omega

/-- **The boundary-band cardinality bound**: under the numeric gate
`64·(r+1)·(L+B+1) < 129·L + 64` the class-5 fibre has at most `r + 1` elements (it sits
inside the top `r + 1` positions of the shell window). -/
theorem class5Fibre_card_le_of_gapCeiling (ctx : ActualFailureContext)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card
      ≤ ctx.n24CarryData.r + 1 := by
  have hsub : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5
      ⊆ Finset.Ico
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1))
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) := by
    intro k hk
    have hover := class5Fibre_window_overrun ctx hk hnum
    have hwin := class5Fibre_mem_window ctx hk
    rw [Finset.mem_Ico]
    omega
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card
      ≤ (Finset.Ico
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1))
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card)).card :=
        Finset.card_le_card hsub
    _ ≤ ctx.n24CarryData.r + 1 := by
        rw [Nat.card_Ico]
        omega

/-- **The K.1 numeric gate holds automatically on every `r = 0` shell** (from the
largeness gate `B + 25 ≤ L`). -/
theorem class5_gate_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64 := by
  have hB : carryB ctx.shell.Q + 25 ≤ shellLadderDepth ctx := ctx.shell_carryLarge
  rw [hr]
  omega

/-- The K.1 numeric gate in explicit-numeral form: automatic on every shell with
`L ≤ 15420` (the whole `r = ⌊κL⌋ = 0` regime). -/
theorem class5_gate_of_L_le (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 15420) :
    64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64 :=
  class5_gate_of_r_eq_zero ctx (n24_r_eq_zero_of_L_le ctx hL)

/-- **`r = 0` shells: the class-5 fibre is pinned to the SINGLE topmost window start**
`k = firstIndexAbove X + |supportShell d X| − 1`. -/
theorem class5Fibre_top_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5) :
    k + 1 = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card := by
  have hover := class5Fibre_window_overrun ctx hk (class5_gate_of_r_eq_zero ctx hr)
  have hwin := class5Fibre_mem_window ctx hk
  omega

/-- **`r = 0` shells: at most ONE class-5 routed start** (`|fibre₅| ≤ 1`). -/
theorem class5Fibre_card_le_one_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro x hx y hy
  have hxe := class5Fibre_top_of_r_eq_zero ctx hr hx
  have hye := class5Fibre_top_of_r_eq_zero ctx hr hy
  omega

/-- **Every shell with `L ≤ 15420` has at most ONE class-5 routed start** (the
explicit-numeral form of the `r = 0` boundary pinning). -/
theorem class5Fibre_card_le_one_of_L_le (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 15420) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card ≤ 1 :=
  class5Fibre_card_le_one_of_r_eq_zero ctx (n24_r_eq_zero_of_L_le ctx hL)

/-! ## 6.  The zero-stage collapse of the I.6S geometry

With the constant stage map `stageOf := fun _ => 0` the canonical stage length is `1`,
so the finite L.4.2 half-decrease field is VACUOUS and the base-stage fibre is the
whole class-5 fibre.  This makes the max-core residual collapse to its single product
inequality — and makes fibre-emptiness an honest FULL closure. -/

/-- The canonical stage length of the zero stage map is `1`. -/
theorem runStageLen_zeroStage (ctx : ActualFailureContext) :
    runStageLen ctx (fun _ => 0) = 1 := by
  unfold runStageLen
  have hsup : (((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).image
      (fun _ => 0)).sup id) = 0 := by
    refine Nat.le_antisymm ?_ (Nat.zero_le _)
    refine Finset.sup_le ?_
    intro b hb
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hb
    exact le_of_eq hx.symm
  rw [hsup]

/-- The base-stage fibre of the zero stage map is the whole class-5 fibre. -/
theorem runBaseFibre_zeroStage (ctx : ActualFailureContext) :
    runBaseFibre ctx (fun _ => 0)
      = routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 := by
  unfold runBaseFibre
  exact Finset.filter_true_of_mem (fun k _ => rfl)

/-! ## 7.  The honest closure surfaces of the Run atom -/

/-- **The Run atom from the single class-5 product inequality.**  At the zero stage
map the half-decrease is vacuous (`runStageLen = 1`) and the base-stage fibre is the
whole fibre, so the corrected max-form residual is EXACTLY the one Section 26 product
bound `c0·|fibre₅|·maxExcess ≤ (c⋆ξ/12)·|supportShell|`. -/
def runCoreOfClass5ProductBound (ctx : ActualFailureContext)
    (h : erdos260Constants.c0
          * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
          * runBaseMaxExcess ctx (fun _ => 0)
        ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
          * ((supportShell ctx.d ctx.X).card : ℝ)) :
    RunClass5LeafSupportMaxCoreResidual ctx where
  stageOf := fun _ => 0
  hhalf := by
    intro i hi
    rw [runStageLen_zeroStage] at hi
    exact absurd hi (by omega)
  hproduct := by
    rw [runBaseFibre_zeroStage]
    exact h

/-- **FULL honest closure of the Run atom from class-5 fibre-emptiness.**  The empty
fibre has base-stage count `0` and pointwise-max excess `0` (this is the genuine value
of the K.1.2/L.20 multiplier on an empty fibre, not a fabricated witness), so the
product bound is `0 ≤ nonneg` and the half-decrease is vacuous. -/
def runCoreOfClass5FibreEmpty (ctx : ActualFailureContext)
    (h : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 = ∅) :
    RunClass5LeafSupportMaxCoreResidual ctx :=
  runCoreOfClass5ProductBound ctx (by
    have hcard0 : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card = 0 := by
      rw [h, Finset.card_empty]
    have hbase0 : (runBaseFibre ctx (fun _ => 0)).card = 0 := by
      rw [runBaseFibre_zeroStage, hcard0]
    have hmax : runBaseMaxExcess ctx (fun _ => 0) = 0 :=
      runBaseMaxExcess_eq_zero_of_card_eq_zero ctx (fun _ => 0) hbase0
    rw [hcard0, hmax]
    have hA : 0 ≤ erdos260Constants.cStar * erdos260Constants.ξ / 12 :=
      div_nonneg
        (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
        (by norm_num)
    have hS : (0 : ℝ) ≤ ((supportShell ctx.d ctx.X).card : ℝ) := Nat.cast_nonneg _
    simpa using mul_nonneg hA hS)

/-- **The family form: class-5 fibre-emptiness at every context closes the whole
`runCore` capstone field.** -/
def runCoreOfClass5FibreEmptyFamily
    (h : ∀ ctx : ActualFailureContext,
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 = ∅) :
    ∀ ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx :=
  fun ctx => runCoreOfClass5FibreEmpty ctx (h ctx)

/-- **Erdős 260 from class-5 fibre-emptiness plus the P9 routing atom** — the capstone
endpoint with the Run atom discharged by the emptiness theorem. -/
theorem erdos260_of_class5FibreEmpty_and_highExcess
    (h : ∀ ctx : ActualFailureContext,
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 = ∅)
    (he : HighExcessRoutingCountResidual) : Erdos260Statement :=
  erdos260_ofSupportMaxCore_and_highExcess (runCoreOfClass5FibreEmptyFamily h) he

/-- **The UNCONDITIONAL Run-atom closure on every small-modulus shell** (`q < 5`,
i.e. `q = 3`): the proved orbit-band emptiness theorem discharges the whole
max-core residual. -/
def runCoreOfModulusLtFive (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q < 5) :
    RunClass5LeafSupportMaxCoreResidual ctx :=
  runCoreOfClass5FibreEmpty ctx (class5Fibre_empty_of_modulus_lt_five ctx hq)

/-- **The class-5 emptiness residual in its sharpest necessary-and-sufficient
arithmetic form**: the fibre is empty IFF no carry-window start simultaneously
realizes the high-excess gap-window floor and the band-1 / heavy-band-4 pin. -/
theorem class5Fibre_empty_iff_pinned (ctx : ActualFailureContext) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 = ∅
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          ¬(129 * shellLadderDepth ctx + 64
                ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ∧ (canonGap (class1SlopeDatum ctx).q
                  (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 1
              ∨ (canonGap (class1SlopeDatum ctx).q
                    (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4
                  ∧ 130 * shellLadderDepth ctx + 64
                      ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r))) := by
  constructor
  · intro hemp k hkstart hpins
    have hmem : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 :=
      (mem_class5Fibre_iff ctx k).mpr ⟨hkstart, hpins.1, hpins.2⟩
    rw [hemp] at hmem
    exact Finset.notMem_empty k hmem
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    rw [mem_class5Fibre_iff] at hk
    exact h k hk.1 ⟨hk.2.1, hk.2.2⟩

/-! ## 8.  The gate-side closures: interior ⟹ empty ⟹ closed; boundary-band entry -/

/-- **Under the K.1 numeric gate, the shared K.1 active-window interior condition
forces class-5 fibre-emptiness**: an interior start cannot overrun the shell window,
but every class-5 start must (`class5Fibre_window_overrun`). -/
theorem class5Fibre_empty_of_gate_interior (ctx : ActualFailureContext)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64)
    (hinterior : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have hover := class5Fibre_window_overrun ctx hk hnum
  have hint := hinterior k hk
  omega

/-- **FULL Run-atom closure from the gate plus the K.1 interior condition** — on gated
shells the interior boundary residual (the same condition every sibling class
retains) ALONE discharges the entire max-core residual. -/
def runCoreOfGateInterior (ctx : ActualFailureContext)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64)
    (hinterior : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) :
    RunClass5LeafSupportMaxCoreResidual ctx :=
  runCoreOfClass5FibreEmpty ctx (class5Fibre_empty_of_gate_interior ctx hnum hinterior)

/-- **The strictly smaller gate-side residual: the boundary-band entry point.**

Under the K.1 numeric gate the class-5 fibre is confined to the top `r + 1` boundary
band of the shell window, so the max-core residual follows from a window-excess bound
`M` on the boundary band ALONE — a fibre-free, purely boundary-band datum
(`hM` quantifies over window positions, never over the routed fibre) — together with
ONE scalar Section 26 numeric at the PROVED count `r + 1`. -/
def runCoreOfGateBoundary (ctx : ActualFailureContext)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64)
    {M : ℝ} (hM_nonneg : 0 ≤ M)
    (hM : ∀ k : ℕ,
      ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card ≤ k + ctx.n24CarryData.r + 1 →
      k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card →
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ M)
    (hcount : erdos260Constants.c0 * ((ctx.n24CarryData.r + 1 : ℕ) : ℝ) * M
        ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
          * ((supportShell ctx.d ctx.X).card : ℝ)) :
    RunClass5LeafSupportMaxCoreResidual ctx :=
  runCoreOfClass5ProductBound ctx (by
    have hNle : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
        ≤ ((ctx.n24CarryData.r + 1 : ℕ) : ℝ) := by
      exact_mod_cast class5Fibre_card_le_of_gapCeiling ctx hnum
    have hmaxle : runBaseMaxExcess ctx (fun _ => 0) ≤ M := by
      refine runBaseMaxExcess_le_of_pointBound ctx (fun _ => 0) hM_nonneg ?_
      intro k hk
      rw [runBaseFibre_zeroStage] at hk
      exact hM k (class5Fibre_window_overrun ctx hk hnum)
        (class5Fibre_mem_window ctx hk).2
    have hN_nonneg : (0 : ℝ)
        ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ) :=
      Nat.cast_nonneg _
    calc erdos260Constants.c0
            * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
            * runBaseMaxExcess ctx (fun _ => 0)
        ≤ erdos260Constants.c0
            * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ) * M :=
          mul_le_mul_of_nonneg_left hmaxle
            (mul_nonneg erdos260Constants.c0_pos.le hN_nonneg)
      _ ≤ erdos260Constants.c0 * ((ctx.n24CarryData.r + 1 : ℕ) : ℝ) * M :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hNle erdos260Constants.c0_pos.le) hM_nonneg
      _ ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
            * ((supportShell ctx.d ctx.X).card : ℝ) := hcount)

/-! ## 9.  The ungated split reduction: interior ceiling + boundary band

Without any gate hypothesis, every class-5 start is either INTERIOR to the shell
window — where the PROVED dyadic ceiling caps its window excess by the canonical
matched K.1.2/L.20 multiplier `runDyadicMult ctx` — or in the top `r + 1` boundary
band.  So the pointwise-max multiplier of the max-core residual is at most
`max (runDyadicMult ctx) M` for any boundary-band excess bound `M`, and the residual
reduces to ONE scalar numeric at that split multiplier: the only `windowExcess`
quantity left in the interface is the boundary-band bound. -/

/-- **The per-point interior dyadic ceiling**: any window position whose descent
window stays inside the shell window has window excess at most the canonical matched
ceiling `runDyadicMult ctx` (the per-point form of the proved
`runBaseFibre_windowExcess_le_runDyadicMult`). -/
theorem class5_windowExcess_le_runDyadicMult_of_interior (ctx : ActualFailureContext)
    {k : ℕ}
    (hint : k + ctx.n24CarryData.r + 1
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card) :
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ runDyadicMult ctx := by
  refine windowExcess_le_window_gap_multiplier (g₀ := runDyadicG0 ctx) ?_
    (run_scale_le_runDyadicMult ctx) (runDyadicMult_nonneg ctx)
  intro j _hjlo hjhi
  have hK1 : 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
    le_trans (Nat.le_add_left 1 ctx.n24CarryData.r) (r_add_one_le_width ctx)
  refine hitGap_le_runDyadicG0_of_window ctx
    (r₀ := (supportShell ctx.shell.d ctx.shell.X).card - 1) (by omega) ?_
  omega

/-- **The ungated split entry point.**  The max-core residual from a boundary-band
window-excess bound `M` (a fibre-free top-band datum) and ONE scalar numeric at the
split multiplier `max (runDyadicMult ctx) M`: interior starts are ceilinged by the
PROVED canonical multiplier, boundary starts by `M`.  No gate hypothesis. -/
def runCoreOfSplitBoundary (ctx : ActualFailureContext)
    {M : ℝ}
    (hM : ∀ k : ℕ,
      ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card ≤ k + ctx.n24CarryData.r + 1 →
      k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card →
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ M)
    (hcount : erdos260Constants.c0
          * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
          * max (runDyadicMult ctx) M
        ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
          * ((supportShell ctx.d ctx.X).card : ℝ)) :
    RunClass5LeafSupportMaxCoreResidual ctx :=
  runCoreOfClass5ProductBound ctx (by
    have hmaxle : runBaseMaxExcess ctx (fun _ => 0) ≤ max (runDyadicMult ctx) M := by
      refine runBaseMaxExcess_le_of_pointBound ctx (fun _ => 0)
        (le_trans (runDyadicMult_nonneg ctx) (le_max_left _ _)) ?_
      intro k hk
      rw [runBaseFibre_zeroStage] at hk
      have hwin := class5Fibre_mem_window ctx hk
      by_cases hint : k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card
      · exact le_trans (class5_windowExcess_le_runDyadicMult_of_interior ctx hint)
          (le_max_left _ _)
      · exact le_trans (hM k (by omega) hwin.2) (le_max_right _ _)
    have hN_nonneg : (0 : ℝ)
        ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ) :=
      Nat.cast_nonneg _
    calc erdos260Constants.c0
            * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
            * runBaseMaxExcess ctx (fun _ => 0)
        ≤ erdos260Constants.c0
            * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
            * max (runDyadicMult ctx) M :=
          mul_le_mul_of_nonneg_left hmaxle
            (mul_nonneg erdos260Constants.c0_pos.le hN_nonneg)
      _ ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
            * ((supportShell ctx.d ctx.X).card : ℝ) := hcount)

/-! ## 10.  Honest status -/

/-- The precise status of the Run / Class 5 atom after this module. -/
def runClass5RoutingStatus : List String :=
  [ "CLOSED (routing pin) - mem_class5Fibre_iff / class5Fibre_eq_pinnedFilter: the sharp " ++
      "class-5 membership characterization on the genuine first-obstruction route, mirroring " ++
      "the proved class-1 (canonGap = 4, mem_class1Fibre_iff) and class-4 (canonGap = 2, " ++
      "mem_class4Fibre_iff) analyses: k in fibre5 iff k is a carry-window start with " ++
      "129L+64 <= 64*gapWindow and (canonGap q K_k = 1, the run band, or canonGap q K_k = 4 " ++
      "with the heavy floor 130L+64 <= 64*gapWindow, the cnlTail local-spike branch " ++
      "runClsOfShell = 1). Supporting windows: canonGap_eq_one_iff (q < 2K), " ++
      "towerExitClassOfGap_eq_run_iff, two_Y_le_windowExcess_iff_gapWindow, " ++
      "runClsOfShell_eq_one_iff; orbit pins class5Fibre_orbit_band / class5Fibre_orbit_step; " ++
      "below modulus 9 only band 1 survives (class5Fibre_canonGap_eq_one_of_modulus_lt_nine).",
    "CLOSED (genuine small-modulus emptiness) - class5Fibre_empty_of_modulus_lt_five: at the " ++
      "smallest admissible modulus q = 3 the E.13 orbit is constant 1 from index 1 on " ++
      "(boundedSlopeStep_three, slopeOrbit_three_tail) with band canonGap 3 1 = 2 (returnPkg), " ++
      "and 0 is never a window start, so the class-5 fibre is provably EMPTY; the q = 3 mass " ++
      "routes to class 4 (no all-classes-empty degeneracy). runCoreOfModulusLtFive closes the " ++
      "whole Run atom UNCONDITIONALLY on that shell family.",
    "CLOSED (boundary confinement, gate regime) - class5Fibre_window_overrun / " ++
      "class5Fibre_card_le_of_gapCeiling: under the K.1 numeric gate 64(r+1)(L+B+1) < 129L+64 " ++
      "(automatic at r = 0, i.e. ALL L <= 15420: class5_gate_of_r_eq_zero, class5_gate_of_L_le) " ++
      "the class-5 fibre sits in the top r+1 boundary band; at r = 0 it is pinned to the single " ++
      "topmost window start (class5Fibre_top_of_r_eq_zero, class5Fibre_card_le_one_of_r_eq_zero, " ++
      "class5Fibre_card_le_one_of_L_le).",
    "CLOSED (zero-stage collapse + emptiness closure) - runStageLen_zeroStage / " ++
      "runBaseFibre_zeroStage: at the constant stage map the L.4.2 half-decrease is vacuous and " ++
      "the base-stage fibre is the whole fibre, so the max-core residual IS the single product " ++
      "bound (runCoreOfClass5ProductBound); an empty fibre closes it honestly with count 0 and " ++
      "max excess 0 (runCoreOfClass5FibreEmpty, family runCoreOfClass5FibreEmptyFamily, capstone " ++
      "erdos260_of_class5FibreEmpty_and_highExcess); class5Fibre_empty_iff_pinned is the " ++
      "necessary-and-sufficient arithmetic form of the emptiness residual.",
    "CLOSED (gate + interior => FULL closure) - class5Fibre_empty_of_gate_interior / " ++
      "runCoreOfGateInterior: on gated shells the shared K.1 active-window interior condition " ++
      "(the boundary residual every sibling class retains) alone forces fibre-emptiness, hence " ++
      "the entire Run atom.",
    "REDUCED (gate-side boundary entry) - runCoreOfGateBoundary: under the gate the residual " ++
      "shrinks to a fibre-free window-excess bound on the <= r+1 top boundary starts plus ONE " ++
      "scalar numeric at the PROVED count r+1.",
    "REDUCED (ungated split entry) - class5_windowExcess_le_runDyadicMult_of_interior / " ++
      "runCoreOfSplitBoundary: with NO gate hypothesis, every class-5 start is interior " ++
      "(window excess <= the PROVED canonical matched ceiling runDyadicMult) or in the top " ++
      "r+1 boundary band (bound M), so the residual reduces to the boundary-band bound plus " ++
      "ONE scalar numeric at the split multiplier max(runDyadicMult, M) - the only " ++
      "windowExcess quantity left in the interface is the boundary band.",
    "OPEN (honest obstruction, why not runCoreUnconditional) - unconditional class-5 emptiness " ++
      "is NOT provable from the routing arithmetic: the band-1 window q < 2K < 2q is realized " ++
      "along the recurrent orbit for q >= 5 (e.g. q = 5: orbit 1 -> 3 -> 1 alternates through " ++
      "the band-1 numerator 3), and on the surviving boundary band the window excess has no " ++
      "formalized ceiling (the dyadic gap estimate hitGap <= L+B+1 covers only j+1 < " ++
      "firstIndexAbove X + |supportShell|, which overrun starts escape by construction). As in " ++
      "the class-1/class-4 analyses, the hit-gap floor (actual hit sequence) and the band pin " ++
      "(recurrent slope orbit) are mutually unconstrained in the model; the Section 26 linear " ++
      "sparsity on the boundary band remains the manuscript's irreducible positive-density " ++
      "input." ]

theorem runClass5RoutingStatus_nonempty : runClass5RoutingStatus ≠ [] := by
  simp [runClass5RoutingStatus]

/-! ## 11.  Axiom-cleanliness audit -/

#print axioms towerExitClassOfGap_eq_run_iff
#print axioms canonGap_eq_one_iff
#print axioms two_Y_le_windowExcess_iff_gapWindow
#print axioms runClsOfShell_eq_one_iff
#print axioms class5Fibre_band_pin
#print axioms mem_class5Fibre_iff
#print axioms class5Fibre_eq_pinnedFilter
#print axioms class5Fibre_orbit_band
#print axioms class5Fibre_orbit_step
#print axioms class5Fibre_canonGap_eq_one_of_modulus_lt_nine
#print axioms canonGap_three_one
#print axioms canonGap_three_two
#print axioms boundedSlopeStep_three
#print axioms slopeOrbit_three_tail
#print axioms class5Fibre_empty_of_modulus_lt_five
#print axioms class5Fibre_mem_window
#print axioms class5Fibre_window_overrun
#print axioms class5Fibre_card_le_of_gapCeiling
#print axioms class5_gate_of_r_eq_zero
#print axioms class5_gate_of_L_le
#print axioms class5Fibre_top_of_r_eq_zero
#print axioms class5Fibre_card_le_one_of_r_eq_zero
#print axioms class5Fibre_card_le_one_of_L_le
#print axioms runStageLen_zeroStage
#print axioms runBaseFibre_zeroStage
#print axioms runCoreOfClass5ProductBound
#print axioms runCoreOfClass5FibreEmpty
#print axioms runCoreOfClass5FibreEmptyFamily
#print axioms erdos260_of_class5FibreEmpty_and_highExcess
#print axioms runCoreOfModulusLtFive
#print axioms class5Fibre_empty_iff_pinned
#print axioms class5Fibre_empty_of_gate_interior
#print axioms runCoreOfGateInterior
#print axioms runCoreOfGateBoundary
#print axioms class5_windowExcess_le_runDyadicMult_of_interior
#print axioms runCoreOfSplitBoundary

end

end Erdos260
