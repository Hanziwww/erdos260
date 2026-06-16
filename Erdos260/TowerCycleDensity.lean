import Erdos260.TowerDeepWindowClosure
import Erdos260.CNLClass1Closure

/-!
# Tower / Class 2, wave 3 — orbit cycle-density counting for the deep-shell count bound

This module (NEW; it edits no existing file) attacks the wave-2 capstone field

`towerCount : Class2DeepShellCountBound`
  `= ∀ ctx, 328965 < L → towerSparsityBlock ctx · #fibre₂ ≤ |supportShell|`

via **orbit cycle-density counting**: class-2 starts need `canonGap q K_k = 4`
(`mem_class2Fibre_iff`), the orbit `k ↦ K_k` is purely periodic from index `1` with period
`1 ≤ c ≤ q` (`slopeOrbit_exists_period`, imported from `CNLClass1Closure`), so class-2-eligible
indices are confined to the band-4 residues of the cycle.

## What is proved here (all unconditional theorems about the canonical routing)

1. **The class-2 parity pins** (the class-2 twins of the wave-2 class-1 pins): every class-2
   start has `k ≥ 1` (`class2Fibre_start_pos`), hence an ODD orbit numerator
   (`class2Fibre_orbit_odd`); the band-4 window `8K ≤ q < 16K` with odd `K` forces
   `q ∈ {9,…,15} ∪ {25, 27, …}` (`modulus_window_of_class2Fibre_nonempty`); the fibre is
   **provably empty on `q ∈ {17, 19, 21, 23}`** (`class2Fibre_empty_of_modulus_window`) — a
   brand-new closed modulus subfamily beyond the wave-2 `q < 9` closure; and on `q ≤ 15` every
   class-2 start has `K_k = 1` exactly (`class2Fibre_orbit_eq_one_of_modulus_le_15`).

2. **The per-cycle band-4 count** `towerBand4CycleCount q K₀ c` (a `Finset` card over one
   period `[1, c]`) and **the window counting theorem** (`towerBand4_window_card_le`,
   `class2Fibre_card_le_cycleDensity`):

   `#fibre₂ ≤ b4(q, K₀, c) · ⌈K/c⌉`   (`⌈K/c⌉ = (K + c − 1)/c`)

   for ANY period `c` of the orbit, by an explicit injection
   `k ↦ ((k−1) mod c + 1, (k−i₀)/c)` of the band-4 window positions into
   (band-4 cycle positions) × (blocks).

3. **The bridges to the exact capstone field**: the per-ctx finite cycle inequality
   `Class2CycleInequality ctx := ∃ c, period ∧ m₀·(b4·⌈K/c⌉) ≤ K` discharges the count bound
   at `ctx` (`class2CountBound_of_cycleInequality`), and the deep-shell residual
   `Class2CycleDensityResidual` discharges `Class2DeepShellCountBound` outright
   (`towerCountBound_ofCycleDensity`), hence the full capstone Tower surface
   (`towerDeepResidual_ofCycleDensity`, `p9V3TowerCount_ofCycleDensity`).  A split entry
   (`towerCountBound_of_modulus_split`) folds in the proved modulus closures.

4. **Clean sufficient forms of the cycle inequality**: a band-4-free period EMPTIES the fibre
   (`class2Fibre_empty_of_cycle_band_free` — the class-2 analogue of the class-1
   `class1Fibre_empty_of_cycle_band_free`), and the half-density check
   `2·(m₀·b4) ≤ c ≤ K` yields the count bound with the rounding worked exactly
   (`towerHalfDensity_rounding`, `class2CycleInequality_of_half_density`).

5. **The all-band-4 dichotomy** (the structured line): a period whose EVERY reading is band 4
   forces the exact `1/15` fixed point `15·K₁ = q` (`towerCycle_band4_full_forces_fixed`, via
   the wave-2 run rigidity `band4_run_forces_pow_lt`), hence `15 ∣ q`
   (`towerCycle_band4_full_fifteen_dvd`); at the fixed point the orbit is CONSTANT
   (`towerFixedPoint_orbit_const`).  Consequently `b4 < c` on every orbit off the fixed point
   (`towerBand4CycleCount_lt_of_not_fixed`) — the cycle density `b4/c = 1` happens ONLY on the
   `15 ∣ q` fixed-point family, exactly the wave-2 obstruction family.

6. **Explicit modulus families**:
   * `q = 9`: every admissible orbit has period `3` from index `1`
     (`towerNine_orbit_period`: the odd states split into the 3-cycle `1 → 7 → 5` and the
     fixed point `3`) with at most ONE band-4 reading per period
     (`towerNine_band4CycleCount_le_one`), so the count bound holds OUTRIGHT on every `q = 9`
     shell with `m₀ ≤ 2` (`class2CountBound_of_modulus_nine`) — in particular on ALL deep
     shells with `r ≤ 41` (`towerSparsityBlock_le_two_iff`).
   * `q = 15` (the `15 ∣ q` family at `t = 1`): off the fixed point (`K₁ ≠ 1`) the orbit NEVER
     visits `1`, the only band-4 state (`towerFifteen_orbit_ne_one`), so the fibre is
     **provably empty** (`class2Fibre_empty_of_modulus_fifteen_off_fixed`); ON the fixed point
     (`K₁ = 1`) every positive index is band 4
     (`class2_modulus_fifteen_fixed_family_band4`) — the honest open family, characterized
     exactly.

## Honesty — what is NOT closed

The count bound itself remains open exactly on the shells where the cycle inequality fails:
the `15 ∣ q` fixed-point orbits (`b4 = c`, density `1`) and any `(q, K₀, r)` with cycle
density `b4/c` above the demanded `1/m₀ ≈ 64/(3(r+1))`.  Cycle counting reads ONLY the orbit
side of the class-2 pin; the digit-side gap-window band (`129L+64 < 64·gW < 130L+64`) is not
consumed, because no unconditional bridge ties `hitGap` to `canonGap` along the orbit (the
wave-2 audit; the zero-run hypothesis of `carry_tracks_slopeOrbit` is not derivable from the
window pins).  No degenerate witness is fabricated.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The class-2 parity pins and the modulus-window closure

Every carry-window start has `k ≥ 1` (`n24_starts_pos`, wave 2), and the slope orbit is odd at
every index `k ≥ 1` (`slopeOrbit_odd`).  The class-2 band-4 window `8K ≤ q < 16K` therefore
carries an ODD numerator, which pins the modulus into `{9,…,15} ∪ {25, 27, …}` — the exact
class-2 twin of the wave-2 class-1 parity closure. -/

/-- Every class-2 routed start of the genuine route has `k ≥ 1` (it is a carry-window
start). -/
theorem class2Fibre_start_pos (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2) :
    1 ≤ k :=
  n24_starts_pos ctx (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1

/-- **The class-2 odd-numerator pin**: every class-2 routed start has an ODD slope-orbit
numerator `K_k` (it sits at index `k ≥ 1` of the orbit). -/
theorem class2Fibre_orbit_odd (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2) :
    Odd (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) :=
  slopeOrbit_odd (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k (class2Fibre_start_pos ctx hk)

/-- **The two-sided modulus window of a nonempty class-2 fibre** (sharpens the wave-2
`modulus_ge_nine_of_class2Fibre_nonempty`): a class-2 start forces the odd modulus into
`{9,…,15} ∪ {25, 27, …}` — the parity pin excludes the whole band `16 < q < 25`. -/
theorem modulus_window_of_class2Fibre_nonempty (ctx : ActualFailureContext)
    (h : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).Nonempty) :
    9 ≤ (class1SlopeDatum ctx).q
      ∧ ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨h8, h16⟩ := class2Fibre_orbit_band ctx hk
  exact band_four_odd_modulus_window (class1SlopeDatum ctx).hq_odd
    (class2Fibre_orbit_odd ctx hk) h8 h16

/-- **NEW modulus-window closure**: the class-2 routed fibre of the genuine route is PROVABLY
EMPTY on every shell whose closed AP-subfibre modulus lies in the band `16 < q < 25`
(`q ∈ {17, 19, 21, 23}`) — the only band-4 numerator there is the even `K = 2`, while every
window start carries an odd orbit numerator. -/
theorem class2Fibre_empty_of_modulus_window (ctx : ActualFailureContext)
    (h16 : 16 < (class1SlopeDatum ctx).q) (h25 : (class1SlopeDatum ctx).q < 25) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  obtain ⟨h9, hwin⟩ := modulus_window_of_class2Fibre_nonempty ctx ⟨k, hk⟩
  omega

/-- The count bound holds outright on the `16 < q < 25` modulus window (the fibre is
empty). -/
theorem class2CountBound_of_modulus_window (ctx : ActualFailureContext)
    (h16 : 16 < (class1SlopeDatum ctx).q) (h25 : (class1SlopeDatum ctx).q < 25) :
    towerSparsityBlock ctx
        * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card
      ≤ shellWidth ctx := by
  rw [class2Fibre_empty_of_modulus_window ctx h16 h25]
  simp

/-- The FULL deep window datum on the `16 < q < 25` modulus window. -/
def class2DeepShellWindowData_of_modulus_window (ctx : ActualFailureContext)
    (h16 : 16 < (class1SlopeDatum ctx).q) (h25 : (class1SlopeDatum ctx).q < 25) :
    Class2DeepShellWindowData ctx :=
  class2DeepShellWindowData_ofCountBound ctx
    (class2CountBound_of_modulus_window ctx h16 h25)

/-- **The low-modulus orbit pin**: on every shell with `q ≤ 15` each class-2 start has its
orbit numerator pinned to `K_k = 1` EXACTLY (the band `8K ≤ q ≤ 15` admits no other positive
value). -/
theorem class2Fibre_orbit_eq_one_of_modulus_le_15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 15) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2) :
    slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 1 := by
  obtain ⟨h8, h16⟩ := class2Fibre_orbit_band ctx hk
  have h1 := (slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k).1
  omega

/-! ## Part 2.  Periodic transport along the orbit

The orbit value at any index `k ≥ 1` equals its value at the canonical cycle position
`(k − 1) mod c + 1 ∈ [1, c]`, for any period `c` valid from index `1`. -/

/-- Period iteration: `K_{m + t·c} = K_m` for every `m ≥ 1` and every multiple `t·c`. -/
theorem towerCycle_orbit_add_mul {q K₀ c : ℕ}
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m) :
    ∀ t m, 1 ≤ m → slopeOrbit q K₀ (m + t * c) = slopeOrbit q K₀ m := by
  intro t
  induction t with
  | zero => intro m hm; simp
  | succ n ih =>
      intro m hm
      have h1 : m + (n + 1) * c = (m + n * c) + c := by ring
      rw [h1, hper (m + n * c) (by omega), ih m hm]

/-- **Cycle-position transport**: for any period `c ≥ 1` valid from index `1`, the orbit value
at `k ≥ 1` equals its value at the cycle position `(k − 1) mod c + 1 ∈ [1, c]`. -/
theorem towerCycle_orbit_mod {q K₀ c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    (k : ℕ) (hk : 1 ≤ k) :
    slopeOrbit q K₀ k = slopeOrbit q K₀ ((k - 1) % c + 1) := by
  have hd := Nat.div_add_mod (k - 1) c
  have hcomm : ((k - 1) / c) * c = c * ((k - 1) / c) := Nat.mul_comm _ _
  have hdecomp : k = ((k - 1) % c + 1) + ((k - 1) / c) * c := by omega
  conv_lhs => rw [hdecomp]
  exact towerCycle_orbit_add_mul hper ((k - 1) / c) ((k - 1) % c + 1) (by omega)

/-! ## Part 3.  The per-cycle band-4 count and the window counting theorem -/

/-- **The per-cycle band-4 count** `b4(q, K₀, c)`: the number of positions in one period
`[1, c]` of the slope orbit whose canonical-gap band index is exactly `4`.  A finite,
per-`(q, K₀, c)` checkable quantity (at most `c` canonical-gap evaluations). -/
def towerBand4CycleCount (q K₀ c : ℕ) : ℕ :=
  ((Finset.Icc 1 c).filter
    (fun j => canonGap q (slopeOrbit q K₀ j) = 4)).card

/-- The per-cycle band-4 count never exceeds the period. -/
theorem towerBand4CycleCount_le (q K₀ c : ℕ) : towerBand4CycleCount q K₀ c ≤ c := by
  have h := Finset.card_filter_le (Finset.Icc 1 c)
    (fun j => canonGap q (slopeOrbit q K₀ j) = 4)
  have hcard : (Finset.Icc 1 c).card = c := by rw [Nat.card_Icc]; omega
  unfold towerBand4CycleCount
  omega

/-- A band-4-free period has count `0`. -/
theorem towerBand4CycleCount_eq_zero_of_band_free {q K₀ c : ℕ}
    (hband : ∀ j, 1 ≤ j → j ≤ c → canonGap q (slopeOrbit q K₀ j) ≠ 4) :
    towerBand4CycleCount q K₀ c = 0 := by
  unfold towerBand4CycleCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  rw [Finset.mem_Icc] at hj
  exact hband j hj.1 hj.2

/-- **The window counting theorem**: in ANY index window `[i₀, i₀ + w)` with `i₀ ≥ 1`, the
number of band-4 orbit positions is at most `b4(q, K₀, c) · ⌈w/c⌉` — each one injects into
(its cycle position, its block index), the cycle position is band-4 by periodic transport, and
the block index ranges over `⌈w/c⌉ = (w + c − 1)/c` blocks. -/
theorem towerBand4_window_card_le {q K₀ c i₀ w : ℕ} (hc : 1 ≤ c) (hi₀ : 1 ≤ i₀)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m) :
    ((Finset.Ico i₀ (i₀ + w)).filter
        (fun k => canonGap q (slopeOrbit q K₀ k) = 4)).card
      ≤ towerBand4CycleCount q K₀ c * ((w + c - 1) / c) := by
  have hcard : (((Finset.Icc 1 c).filter
        (fun j => canonGap q (slopeOrbit q K₀ j) = 4))
          ×ˢ Finset.range ((w + c - 1) / c)).card
      = towerBand4CycleCount q K₀ c * ((w + c - 1) / c) := by
    rw [Finset.card_product, Finset.card_range]
    rfl
  rw [← hcard]
  apply Finset.card_le_card_of_injOn
    (fun k => ((k - 1) % c + 1, (k - i₀) / c))
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hk
    obtain ⟨⟨hklo, hkhi⟩, hband⟩ := hk
    have hk1 : 1 ≤ k := le_trans hi₀ hklo
    have hmodlt : (k - 1) % c < c := Nat.mod_lt _ (by omega)
    refine Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨?_, ?_⟩)
    · show (k - 1) % c + 1 ∈ (Finset.Icc 1 c).filter
        (fun j => canonGap q (slopeOrbit q K₀ j) = 4)
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [← towerCycle_orbit_mod hc hper k hk1]
      exact hband
    · show (k - i₀) / c ∈ Finset.range ((w + c - 1) / c)
      rw [Finset.mem_range]
      have hw1 : 1 ≤ w := by omega
      have hQ : (w + c - 1) / c = (w - 1) / c + 1 := by
        rw [show w + c - 1 = (w - 1) + c by omega]
        exact Nat.add_div_right _ (by omega)
      have hle : (k - i₀) / c ≤ (w - 1) / c :=
        Nat.div_le_div_right (by omega)
      omega
  · intro k hk k' hk' heq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hk hk'
    obtain ⟨⟨hklo, hkhi⟩, _⟩ := hk
    obtain ⟨⟨hklo', hkhi'⟩, _⟩ := hk'
    have hk1 : 1 ≤ k := le_trans hi₀ hklo
    have hk1' : 1 ≤ k' := le_trans hi₀ hklo'
    have hfst : (k - 1) % c + 1 = (k' - 1) % c + 1 := congrArg Prod.fst heq
    have hsnd : (k - i₀) / c = (k' - i₀) / c := congrArg Prod.snd heq
    have hmod1 : k - 1 ≡ k' - 1 [MOD c] := by
      have h : (k - 1) % c = (k' - 1) % c := by omega
      exact h
    have hmodk : k ≡ k' [MOD c] := by
      have h1 : (k - 1) + 1 ≡ (k' - 1) + 1 [MOD c] := Nat.ModEq.add_right 1 hmod1
      rwa [Nat.sub_add_cancel hk1, Nat.sub_add_cancel hk1'] at h1
    have hmodki : (k - i₀) % c = (k' - i₀) % c := by
      have h2 : (k - i₀) + i₀ ≡ (k' - i₀) + i₀ [MOD c] := by
        rwa [Nat.sub_add_cancel hklo, Nat.sub_add_cancel hklo']
      exact Nat.ModEq.add_right_cancel' i₀ h2
    have e1 := Nat.div_add_mod (k - i₀) c
    have e2 := Nat.div_add_mod (k' - i₀) c
    rw [hsnd, hmodki] at e1
    omega

/-- **The class-2 fibre sits inside the band-4 window filter** (the orbit half of the wave-2
routing pin `mem_class2Fibre_iff`; the digit half — the gap-window band — is discarded by this
projection, which is exactly why the cycle bound below cannot be beaten without a
hitGap↔canonGap bridge). -/
theorem class2Fibre_subset_band4Filter (ctx : ActualFailureContext) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2
      ⊆ (Finset.Ico (shellStart ctx) (shellStart ctx + shellWidth ctx)).filter
          (fun k => canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4) := by
  intro k hk
  obtain ⟨hstart, _, _, hband⟩ := (mem_class2Fibre_iff ctx k).mp hk
  rw [Finset.mem_filter]
  refine ⟨?_, hband⟩
  rw [← n24Starts_eq_window]
  exact hstart

/-- **The class-2 cycle-density count bound**: for ANY period `c ≥ 1` of the actual orbit
(valid from index `1`),

`#fibre₂ ≤ b4(q, K₀, c) · ⌈|supportShell|/c⌉`.

The fibre count is controlled by the per-cycle band-4 density alone. -/
theorem class2Fibre_card_le_cycleDensity (ctx : ActualFailureContext) {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card
      ≤ towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c
          * ((shellWidth ctx + c - 1) / c) :=
  le_trans (Finset.card_le_card (class2Fibre_subset_band4Filter ctx))
    (towerBand4_window_card_le hc (n24_firstIndexAbove_pos ctx) hper)

/-- The actual orbit ALWAYS has a period `1 ≤ c ≤ q` valid from index `1`
(restating the wave-2 `class1Fibre_orbit_period_exists` for the class-2 surface): the cycle
inequality below is a FINITE per-context check. -/
theorem class2_orbit_period_exists (ctx : ActualFailureContext) :
    ∃ c, 1 ≤ c ∧ c ≤ (class1SlopeDatum ctx).q ∧ ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m :=
  class1Fibre_orbit_period_exists ctx

/-! ## Part 4.  The cycle inequality, its bridges, and the clean sufficient forms -/

/-- **The per-context finite cycle inequality**: SOME period `c` of the actual orbit satisfies
`m₀ · (b4 · ⌈K/c⌉) ≤ K`.  By `class2_orbit_period_exists` a period `c ≤ q` always exists, so
this is decidable from `(q, K₀, r, K)` by at most `q` canonical-gap evaluations plus one `ℕ`
comparison. -/
def Class2CycleInequality (ctx : ActualFailureContext) : Prop :=
  ∃ c : ℕ, 1 ≤ c
    ∧ (∀ m, 1 ≤ m →
        slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
          = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    ∧ towerSparsityBlock ctx
        * (towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c
            * ((shellWidth ctx + c - 1) / c))
      ≤ shellWidth ctx

/-- **The cycle inequality discharges the count bound at `ctx`.** -/
theorem class2CountBound_of_cycleInequality (ctx : ActualFailureContext)
    (h : Class2CycleInequality ctx) :
    towerSparsityBlock ctx
        * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card
      ≤ shellWidth ctx := by
  obtain ⟨c, hc, hper, hineq⟩ := h
  exact le_trans
    (Nat.mul_le_mul_left _ (class2Fibre_card_le_cycleDensity ctx hc hper))
    hineq

/-- The FULL deep window datum from the cycle inequality at `ctx`. -/
def class2DeepShellWindowData_of_cycleInequality (ctx : ActualFailureContext)
    (h : Class2CycleInequality ctx) :
    Class2DeepShellWindowData ctx :=
  class2DeepShellWindowData_ofCountBound ctx
    (class2CountBound_of_cycleInequality ctx h)

/-- **The deep-shell cycle-density residual**: the cycle inequality on every genuinely deep
shell (`L ≥ 328966`).  Strictly orbit-side data: no window family, no Hall marginal, no digit
information. -/
def Class2CycleDensityResidual : Prop :=
  ∀ ctx : ActualFailureContext, towerShallowDepthBound < shellLadderDepth ctx →
    Class2CycleInequality ctx

/-- **The bridge to the exact capstone field**: the cycle-density residual discharges
`Class2DeepShellCountBound` (the `towerCount` field of `Erdos260SharpResidual`) outright. -/
theorem towerCountBound_ofCycleDensity (h : Class2CycleDensityResidual) :
    Class2DeepShellCountBound :=
  fun ctx hdeep => class2CountBound_of_cycleInequality ctx (h ctx hdeep)

/-- The full wave-1 deep-shell Tower residual from the cycle-density residual. -/
def towerDeepResidual_ofCycleDensity (h : Class2CycleDensityResidual) :
    Class2DeepShellResidual :=
  towerDeepResidual_ofCountBound (towerCountBound_ofCycleDensity h)

/-- The full V3/P9 Tower field from the cycle-density residual alone. -/
def p9V3TowerCount_ofCycleDensity (h : Class2CycleDensityResidual) :
    ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  p9V3TowerCount_ofCountBound (towerCountBound_ofCycleDensity h)

/-- **The split entry**: per deep shell it suffices to verify `q < 9` (closed, wave 2) OR
`16 < q < 25` (closed here, parity) OR the cycle inequality — the sharpest combined surface
for the capstone field. -/
theorem towerCountBound_of_modulus_split
    (h : ∀ ctx : ActualFailureContext, towerShallowDepthBound < shellLadderDepth ctx →
      (class1SlopeDatum ctx).q < 9
      ∨ (16 < (class1SlopeDatum ctx).q ∧ (class1SlopeDatum ctx).q < 25)
      ∨ Class2CycleInequality ctx) :
    Class2DeepShellCountBound := by
  intro ctx hdeep
  rcases h ctx hdeep with hq | ⟨h16, h25⟩ | hcyc
  · rw [class2Fibre_empty_of_modulus_lt_nine ctx hq]
    simp
  · exact class2CountBound_of_modulus_window ctx h16 h25
  · exact class2CountBound_of_cycleInequality ctx hcyc

/-- **Band-4-free cycle closure** (the class-2 analogue of the class-1
`class1Fibre_empty_of_cycle_band_free`): if one period of the orbit avoids band 4
entirely, the class-2 fibre is EMPTY. -/
theorem class2Fibre_empty_of_cycle_band_free (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c → canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ := by
  have h := class2Fibre_card_le_cycleDensity ctx hc hper
  rw [towerBand4CycleCount_eq_zero_of_band_free hband, Nat.zero_mul] at h
  exact Finset.card_eq_zero.mp (Nat.le_zero.mp h)

/-- A band-4-free cycle satisfies the cycle inequality trivially. -/
theorem class2CycleInequality_of_band_free (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c → canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 4) :
    Class2CycleInequality ctx :=
  ⟨c, hc, hper, by
    rw [towerBand4CycleCount_eq_zero_of_band_free hband]
    simp⟩

/-- **The exact rounding of the half-density check**: `2·(m·b) ≤ c ≤ K` forces
`m · (b · ⌈K/c⌉) ≤ K` — the ceiling loses at most one period, and the half-density slack
absorbs it whenever the window holds at least one full period. -/
theorem towerHalfDensity_rounding {m b c K : ℕ} (hc : 1 ≤ c) (hcK : c ≤ K)
    (hhalf : 2 * (m * b) ≤ c) : m * (b * ((K + c - 1) / c)) ≤ K := by
  have h2 : ((K + c - 1) / c) * c ≤ K + c - 1 := Nat.div_mul_le_self _ _
  have h1 : (2 * (m * b)) * ((K + c - 1) / c) ≤ c * ((K + c - 1) / c) :=
    Nat.mul_le_mul_right _ hhalf
  have hassoc : (2 * (m * b)) * ((K + c - 1) / c)
      = 2 * (m * (b * ((K + c - 1) / c))) := by ring
  have hcomm : c * ((K + c - 1) / c) = ((K + c - 1) / c) * c := Nat.mul_comm _ _
  omega

/-- **The half-density cycle closure**: `2·(m₀·b4) ≤ c` with the window at least one period
wide (`c ≤ K`) yields the cycle inequality, hence the count bound. -/
theorem class2CycleInequality_of_half_density (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hhalf : 2 * (towerSparsityBlock ctx
        * towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c) ≤ c)
    (hcK : c ≤ shellWidth ctx) :
    Class2CycleInequality ctx :=
  ⟨c, hc, hper, towerHalfDensity_rounding hc hcK hhalf⟩

/-! ## Part 5.  The all-band-4 dichotomy: full cycles are EXACTLY the `1/15` fixed point

The band-4 step `K ↦ 16K − q` has the unique fixed point `15K = q`.  The wave-2 run rigidity
(`band4_run_forces_pow_lt`) turns a band-4-full period into an infinite band-4 run, which
forces the fixed point.  Hence `b4 = c` happens ONLY at the fixed point (where the orbit is
constant), and `b4 ≤ c − 1` everywhere else. -/

/-- The canonical gap at the `1/15` fixed point is exactly `4`. -/
theorem towerFixedPoint_canonGap_four {q K : ℕ} (hK : 1 ≤ K) (hfix : 15 * K = q) :
    canonGap q K = 4 := by
  unfold canonGap
  have hdiv : q / K = 15 := by
    rw [← hfix, Nat.mul_div_cancel _ (by omega : 0 < K)]
  have hlog : Nat.log 2 15 = 3 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  rw [hdiv, hlog]

/-- **The fixed point is absorbing**: once `15·K₁ = q`, the orbit is CONSTANT from index `1`
(the band-4 step `16K − q` fixes `K = q/15`). -/
theorem towerFixedPoint_orbit_const {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀) (hKq : K₀ < q)
    (hfix : 15 * slopeOrbit q K₀ 1 = q) :
    ∀ j, 1 ≤ j → slopeOrbit q K₀ j = slopeOrbit q K₀ 1 := by
  have h1 : 1 ≤ slopeOrbit q K₀ 1 := (slopeOrbit_mem hq hK1 hKq 1).1
  have hgap : canonGap q (slopeOrbit q K₀ 1) = 4 := towerFixedPoint_canonGap_four h1 hfix
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  clear hj
  induction i with
  | zero => rfl
  | succ n ih =>
      have hstep : slopeOrbit q K₀ (n + 1 + 1)
          = boundedSlopeStep q (slopeOrbit q K₀ (n + 1)) := rfl
      rw [hstep, ih]
      unfold boundedSlopeStep
      rw [hgap]
      have h16 : (2 : ℕ) ^ 4 = 16 := by norm_num
      rw [h16]
      omega

/-- **A band-4-full period forces the exact `1/15` fixed point**: if EVERY position of one
period reads band 4, then `15·K₁ = q` (run rigidity along the periodically-extended run). -/
theorem towerCycle_band4_full_forces_fixed {q K₀ c : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀)
    (hKq : K₀ < q) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    (hall : ∀ j, 1 ≤ j → j ≤ c → canonGap q (slopeOrbit q K₀ j) = 4) :
    15 * slopeOrbit q K₀ 1 = q := by
  have hallj : ∀ j, 1 ≤ j → canonGap q (slopeOrbit q K₀ j) = 4 := by
    intro j hj
    rw [towerCycle_orbit_mod hc hper j hj]
    have hlt : (j - 1) % c < c := Nat.mod_lt _ (by omega)
    exact hall ((j - 1) % c + 1) (by omega) (by omega)
  have hrun := band4_run_forces_pow_lt hq hK1 hKq (k := 1) (s := q)
    (fun i _ => hallj (1 + i) (by omega))
  rcases hrun with h | h
  · exact h
  · exfalso
    have h2 : q < 16 ^ q :=
      lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left (by norm_num) q)
    omega

/-- A band-4-full period forces `15 ∣ q` — the wave-2 `15 ∣ q` obstruction family is the ONLY
family with cycle band-4 density `1`. -/
theorem towerCycle_band4_full_fifteen_dvd {q K₀ c : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀)
    (hKq : K₀ < q) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    (hall : ∀ j, 1 ≤ j → j ≤ c → canonGap q (slopeOrbit q K₀ j) = 4) :
    15 ∣ q :=
  ⟨slopeOrbit q K₀ 1,
    (towerCycle_band4_full_forces_fixed hq hK1 hKq hc hper hall).symm⟩

/-- **Off the fixed point the band-4 cycle count is strictly below the period**:
`15·K₁ ≠ q → b4(q, K₀, c) ≤ c − 1` for every period `c`. -/
theorem towerBand4CycleCount_lt_of_not_fixed {q K₀ c : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀)
    (hKq : K₀ < q) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    (hnf : 15 * slopeOrbit q K₀ 1 ≠ q) :
    towerBand4CycleCount q K₀ c < c := by
  rcases Nat.lt_or_ge (towerBand4CycleCount q K₀ c) c with h | h
  · exact h
  · exfalso
    have hcard : (Finset.Icc 1 c).card = c := by rw [Nat.card_Icc]; omega
    have heq : ((Finset.Icc 1 c).filter
        (fun j => canonGap q (slopeOrbit q K₀ j) = 4)) = Finset.Icc 1 c := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      rw [hcard]
      unfold towerBand4CycleCount at h
      exact h
    have hall : ∀ j, 1 ≤ j → j ≤ c → canonGap q (slopeOrbit q K₀ j) = 4 := by
      intro j h1 h2
      have hjmem : j ∈ (Finset.Icc 1 c).filter
          (fun j => canonGap q (slopeOrbit q K₀ j) = 4) := by
        rw [heq, Finset.mem_Icc]
        exact ⟨h1, h2⟩
      exact (Finset.mem_filter.mp hjmem).2
    exact hnf (towerCycle_band4_full_forces_fixed hq hK1 hKq hc hper hall)

/-! ## Part 6.  Numeric canonical-gap and step evaluations (shared helper) -/

/-- Numeric canonical-gap evaluation: `q/K = d` with `2^g ≤ d < 2^{g+1}` pins
`canonGap q K = g + 1`. -/
private theorem canonGap_num {q K d g : ℕ} (hd : q / K = d)
    (h1 : 2 ^ g ≤ d) (h2 : d < 2 ^ (g + 1)) : canonGap q K = g + 1 := by
  unfold canonGap
  rw [hd, Nat.log_eq_of_pow_le_of_lt_pow h1 h2]

/-! ## Part 7.  The `q = 9` modulus family: period `3`, band-4 count `≤ 1`

The odd states of `q = 9` split into the 3-cycle `1 → 7 → 5 → 1` (bands `4, 1, 1`) and the
fixed point `3 → 3` (band `2`).  EVERY admissible orbit therefore has period `3` from index
`1` with at most one band-4 reading per period — closing the count bound outright on every
`q = 9` shell with `m₀ ≤ 2` (all deep shells with `r ≤ 41`). -/

private theorem nine_gap_one : canonGap 9 1 = 4 :=
  canonGap_num (d := 9) (g := 3) (by norm_num) (by norm_num) (by norm_num)

private theorem nine_gap_three : canonGap 9 3 = 2 :=
  canonGap_num (d := 3) (g := 1) (by norm_num) (by norm_num) (by norm_num)

private theorem nine_gap_five : canonGap 9 5 = 1 :=
  canonGap_num (d := 1) (g := 0) (by norm_num) (by norm_num) (by norm_num)

private theorem nine_gap_seven : canonGap 9 7 = 1 :=
  canonGap_num (d := 1) (g := 0) (by norm_num) (by norm_num) (by norm_num)

private theorem nine_step_one : boundedSlopeStep 9 1 = 7 := by
  unfold boundedSlopeStep
  rw [nine_gap_one]
  norm_num

private theorem nine_step_three : boundedSlopeStep 9 3 = 3 := by
  unfold boundedSlopeStep
  rw [nine_gap_three]
  norm_num

private theorem nine_step_five : boundedSlopeStep 9 5 = 1 := by
  unfold boundedSlopeStep
  rw [nine_gap_five]
  norm_num

private theorem nine_step_seven : boundedSlopeStep 9 7 = 5 := by
  unfold boundedSlopeStep
  rw [nine_gap_seven]
  norm_num

/-- **Every admissible `q = 9` orbit has period `3` from index `1`** (the odd states are the
3-cycle `1 → 7 → 5` and the step fixed point `3`). -/
theorem towerNine_orbit_period {K₀ : ℕ} (hK1 : 1 ≤ K₀) (hKq : K₀ < 9) :
    ∀ m, 1 ≤ m → slopeOrbit 9 K₀ (m + 3) = slopeOrbit 9 K₀ m := by
  have hq : Odd 9 := Nat.odd_iff.mpr (by norm_num)
  intro m hm
  have hmem := slopeOrbit_mem hq hK1 hKq m
  obtain ⟨t, ht⟩ := slopeOrbit_odd hq hK1 hKq m hm
  have h1 : slopeOrbit 9 K₀ (m + 1) = boundedSlopeStep 9 (slopeOrbit 9 K₀ m) := rfl
  have h2 : slopeOrbit 9 K₀ (m + 1 + 1)
      = boundedSlopeStep 9 (slopeOrbit 9 K₀ (m + 1)) := rfl
  have h3 : slopeOrbit 9 K₀ (m + 1 + 1 + 1)
      = boundedSlopeStep 9 (slopeOrbit 9 K₀ (m + 1 + 1)) := rfl
  have hidx : m + 3 = m + 1 + 1 + 1 := by omega
  have hcases : slopeOrbit 9 K₀ m = 1 ∨ slopeOrbit 9 K₀ m = 3
      ∨ slopeOrbit 9 K₀ m = 5 ∨ slopeOrbit 9 K₀ m = 7 := by omega
  rw [hidx, h3, h2, h1]
  rcases hcases with hv | hv | hv | hv <;> rw [hv]
  · rw [nine_step_one, nine_step_seven, nine_step_five]
  · rw [nine_step_three, nine_step_three, nine_step_three]
  · rw [nine_step_five, nine_step_one, nine_step_seven]
  · rw [nine_step_seven, nine_step_five, nine_step_one]

/-- After a `q = 9` orbit visits `1`, the next two values are `7` and `5` — never `1`. -/
private theorem nine_after_one {K₀ : ℕ} {a : ℕ}
    (hKa : slopeOrbit 9 K₀ a = 1) :
    slopeOrbit 9 K₀ (a + 1) = 7 ∧ slopeOrbit 9 K₀ (a + 1 + 1) = 5 := by
  have h1 : slopeOrbit 9 K₀ (a + 1) = boundedSlopeStep 9 (slopeOrbit 9 K₀ a) := rfl
  have h2 : slopeOrbit 9 K₀ (a + 1 + 1)
      = boundedSlopeStep 9 (slopeOrbit 9 K₀ (a + 1)) := rfl
  have e1 : slopeOrbit 9 K₀ (a + 1) = 7 := by rw [h1, hKa, nine_step_one]
  have e2 : slopeOrbit 9 K₀ (a + 1 + 1) = 5 := by rw [h2, e1, nine_step_seven]
  exact ⟨e1, e2⟩

/-- **The `q = 9` per-cycle band-4 count is at most `1`**: band 4 at `q = 9` forces `K = 1`,
and `1` cannot recur within `3` consecutive orbit positions (its successors are `7, 5`). -/
theorem towerNine_band4CycleCount_le_one {K₀ : ℕ} (hK1 : 1 ≤ K₀) (hKq : K₀ < 9) :
    towerBand4CycleCount 9 K₀ 3 ≤ 1 := by
  have hq : Odd 9 := Nat.odd_iff.mpr (by norm_num)
  unfold towerBand4CycleCount
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter, Finset.mem_Icc] at ha hb
  obtain ⟨⟨ha1, ha3⟩, hband_a⟩ := ha
  obtain ⟨⟨hb1, hb3⟩, hband_b⟩ := hb
  have hKa : slopeOrbit 9 K₀ a = 1 := by
    have hmem := slopeOrbit_mem hq hK1 hKq a
    have h := (canonGap_eq_four_iff hmem.1).mp hband_a
    omega
  have hKb : slopeOrbit 9 K₀ b = 1 := by
    have hmem := slopeOrbit_mem hq hK1 hKq b
    have h := (canonGap_eq_four_iff hmem.1).mp hband_b
    omega
  by_contra hne
  rcases Nat.lt_or_ge a b with hab | hab
  · obtain ⟨e1, e2⟩ := nine_after_one (K₀ := K₀) hKa
    have hb_cases : b = a + 1 ∨ b = a + 1 + 1 := by omega
    rcases hb_cases with rfl | rfl
    · rw [e1] at hKb
      omega
    · rw [e2] at hKb
      omega
  · have hba : b < a := by omega
    obtain ⟨e1, e2⟩ := nine_after_one (K₀ := K₀) hKb
    have ha_cases : a = b + 1 ∨ a = b + 1 + 1 := by omega
    rcases ha_cases with rfl | rfl
    · rw [e1] at hKa
      omega
    · rw [e2] at hKa
      omega

/-- `m₀ ≤ 2` holds exactly on `r ≤ 41` shells (so it covers ALL deep shells with
`21 ≤ r ≤ 41`). -/
theorem towerSparsityBlock_le_two_iff (ctx : ActualFailureContext) :
    towerSparsityBlock ctx ≤ 2 ↔ ctx.n24CarryData.r ≤ 41 := by
  unfold towerSparsityBlock
  omega

/-- **The `q = 9` cycle inequality** holds on every shell with `m₀ ≤ 2`: period `3`, band-4
count `≤ 1`, and `2·⌈K/3⌉ ≤ K` once `K ≥ 4` (deep shells have `K ≥ 22`). -/
theorem class2CycleInequality_of_modulus_nine (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9)
    (hm : towerSparsityBlock ctx ≤ 2) :
    Class2CycleInequality ctx := by
  have hK1 := (class1SlopeDatum ctx).hK₀_pos
  have hKq := (class1SlopeDatum ctx).hK₀_lt
  rw [hq] at hKq
  refine ⟨3, by norm_num, ?_, ?_⟩
  · intro m hm'
    rw [hq]
    exact towerNine_orbit_period hK1 hKq m hm'
  · have hb4 : towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 3
        ≤ 1 := by
      rw [hq]
      exact towerNine_band4CycleCount_le_one hK1 hKq
    by_cases h1 : towerSparsityBlock ctx ≤ 1
    · have hQle : (shellWidth ctx + 3 - 1) / 3 ≤ shellWidth ctx := by omega
      calc towerSparsityBlock ctx
            * (towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 3
              * ((shellWidth ctx + 3 - 1) / 3))
          ≤ 1 * (1 * ((shellWidth ctx + 3 - 1) / 3)) :=
            Nat.mul_le_mul h1 (Nat.mul_le_mul_right _ hb4)
        _ = (shellWidth ctx + 3 - 1) / 3 := by ring
        _ ≤ shellWidth ctx := hQle
    · have hm0 : towerSparsityBlock ctx = 2 := by omega
      have hdef : towerSparsityBlock ctx
          = (3 * (ctx.n24CarryData.r + 1) + 63) / 64 := rfl
      have hr : 22 ≤ ctx.n24CarryData.r + 1 := by omega
      have hK : 22 ≤ shellWidth ctx := le_trans hr (r_add_one_le_width ctx)
      calc towerSparsityBlock ctx
            * (towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 3
              * ((shellWidth ctx + 3 - 1) / 3))
          ≤ 2 * (1 * ((shellWidth ctx + 3 - 1) / 3)) := by
            rw [hm0]
            exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hb4)
        _ = 2 * ((shellWidth ctx + 3 - 1) / 3) := by ring
        _ ≤ shellWidth ctx := by omega

/-- **The `q = 9` count-bound closure** on every `m₀ ≤ 2` shell (in particular all deep
shells with `21 ≤ r ≤ 41`). -/
theorem class2CountBound_of_modulus_nine (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9)
    (hm : towerSparsityBlock ctx ≤ 2) :
    towerSparsityBlock ctx
        * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card
      ≤ shellWidth ctx :=
  class2CountBound_of_cycleInequality ctx
    (class2CycleInequality_of_modulus_nine ctx hq hm)

/-- The FULL deep window datum on `q = 9`, `m₀ ≤ 2` shells. -/
def class2DeepShellWindowData_of_modulus_nine (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9)
    (hm : towerSparsityBlock ctx ≤ 2) :
    Class2DeepShellWindowData ctx :=
  class2DeepShellWindowData_ofCountBound ctx
    (class2CountBound_of_modulus_nine ctx hq hm)

/-! ## Part 8.  The `q = 15` modulus family: the `15 ∣ q` fixed point, characterized exactly

`q = 15` is the smallest member of the wave-2 `15 ∣ q` obstruction family (`t = 1`).  Its odd
states split into the band-4 fixed point `{1}` and the band-4-FREE cycles `{5}`, `{3, 9}`,
`{7, 13, 11}`.  Hence: off the fixed point (`K₁ ≠ 1`) the fibre is provably EMPTY; on the
fixed point every positive index reads band 4 — the open family is exactly `K₁ = 1`. -/

private theorem fifteen_gap_three : canonGap 15 3 = 3 :=
  canonGap_num (d := 5) (g := 2) (by norm_num) (by norm_num) (by norm_num)

private theorem fifteen_gap_five : canonGap 15 5 = 2 :=
  canonGap_num (d := 3) (g := 1) (by norm_num) (by norm_num) (by norm_num)

private theorem fifteen_gap_seven : canonGap 15 7 = 2 :=
  canonGap_num (d := 2) (g := 1) (by norm_num) (by norm_num) (by norm_num)

private theorem fifteen_gap_nine : canonGap 15 9 = 1 :=
  canonGap_num (d := 1) (g := 0) (by norm_num) (by norm_num) (by norm_num)

private theorem fifteen_gap_eleven : canonGap 15 11 = 1 :=
  canonGap_num (d := 1) (g := 0) (by norm_num) (by norm_num) (by norm_num)

private theorem fifteen_gap_thirteen : canonGap 15 13 = 1 :=
  canonGap_num (d := 1) (g := 0) (by norm_num) (by norm_num) (by norm_num)

private theorem fifteen_step_three : boundedSlopeStep 15 3 = 9 := by
  unfold boundedSlopeStep
  rw [fifteen_gap_three]
  norm_num

private theorem fifteen_step_five : boundedSlopeStep 15 5 = 5 := by
  unfold boundedSlopeStep
  rw [fifteen_gap_five]
  norm_num

private theorem fifteen_step_seven : boundedSlopeStep 15 7 = 13 := by
  unfold boundedSlopeStep
  rw [fifteen_gap_seven]
  norm_num

private theorem fifteen_step_nine : boundedSlopeStep 15 9 = 3 := by
  unfold boundedSlopeStep
  rw [fifteen_gap_nine]
  norm_num

private theorem fifteen_step_eleven : boundedSlopeStep 15 11 = 7 := by
  unfold boundedSlopeStep
  rw [fifteen_gap_eleven]
  norm_num

private theorem fifteen_step_thirteen : boundedSlopeStep 15 13 = 11 := by
  unfold boundedSlopeStep
  rw [fifteen_gap_thirteen]
  norm_num

/-- At `q = 15` the only odd state stepping to `1` is `1` itself. -/
private theorem fifteen_step_ne_one {K : ℕ} (hodd : Odd K) (h1 : 1 ≤ K) (hlt : K < 15)
    (hne : K ≠ 1) : boundedSlopeStep 15 K ≠ 1 := by
  obtain ⟨t, ht⟩ := hodd
  have hcases : K = 3 ∨ K = 5 ∨ K = 7 ∨ K = 9 ∨ K = 11 ∨ K = 13 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [fifteen_step_three]; norm_num
  · rw [fifteen_step_five]; norm_num
  · rw [fifteen_step_seven]; norm_num
  · rw [fifteen_step_nine]; norm_num
  · rw [fifteen_step_eleven]; norm_num
  · rw [fifteen_step_thirteen]; norm_num

/-- **Off the fixed point the `q = 15` orbit never visits `1`**: `K₁ ≠ 1` propagates to every
positive index (the only odd predecessor of `1` is `1`). -/
theorem towerFifteen_orbit_ne_one {K₀ : ℕ} (hK1 : 1 ≤ K₀) (hKq : K₀ < 15)
    (hne1 : slopeOrbit 15 K₀ 1 ≠ 1) :
    ∀ j, 1 ≤ j → slopeOrbit 15 K₀ j ≠ 1 := by
  have hq : Odd 15 := Nat.odd_iff.mpr (by norm_num)
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  clear hj
  induction i with
  | zero => exact hne1
  | succ n ih =>
      have hstep : slopeOrbit 15 K₀ (n + 1 + 1)
          = boundedSlopeStep 15 (slopeOrbit 15 K₀ (n + 1)) := rfl
      rw [hstep]
      exact fifteen_step_ne_one
        (slopeOrbit_odd hq hK1 hKq (n + 1) (by omega))
        (slopeOrbit_mem hq hK1 hKq (n + 1)).1
        (slopeOrbit_mem hq hK1 hKq (n + 1)).2
        ih

/-- **The `q = 15` off-fixed-point closure**: on every `q = 15` shell whose orbit is off the
fixed point at index `1` (`K₁ ≠ 1`), the class-2 fibre is PROVABLY EMPTY — band 4 at `q = 15`
forces `K_k = 1`, which the orbit never realizes. -/
theorem class2Fibre_empty_of_modulus_fifteen_off_fixed (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15)
    (hne : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1 ≠ 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have hKk := class2Fibre_orbit_eq_one_of_modulus_le_15 ctx (by omega) hk
  have hkpos := class2Fibre_start_pos ctx hk
  have hK1 := (class1SlopeDatum ctx).hK₀_pos
  have hKq := (class1SlopeDatum ctx).hK₀_lt
  rw [hq] at hKq hne hKk
  exact towerFifteen_orbit_ne_one hK1 hKq hne k hkpos hKk

/-- The count bound holds outright on `q = 15` off-fixed-point shells. -/
theorem class2CountBound_of_modulus_fifteen_off_fixed (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15)
    (hne : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1 ≠ 1) :
    towerSparsityBlock ctx
        * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card
      ≤ shellWidth ctx := by
  rw [class2Fibre_empty_of_modulus_fifteen_off_fixed ctx hq hne]
  simp

/-- **The honest open family at `q = 15`, characterized exactly**: ON the fixed point
(`K₁ = 1`) every positive orbit index reads band 4 — the cycle has `b4 = c = 1` and cycle
counting CANNOT bound the fibre (every window start is band-4-eligible).  This is the `t = 1`
member of the wave-2 `15 ∣ q` obstruction family; closing it needs the digit side. -/
theorem class2_modulus_fifteen_fixed_family_band4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15)
    (h1 : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1 = 1) :
    ∀ j, 1 ≤ j →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 4 := by
  intro j hj
  have hK1 := (class1SlopeDatum ctx).hK₀_pos
  have hKq := (class1SlopeDatum ctx).hK₀_lt
  rw [hq] at hKq h1 ⊢
  have hq15 : Odd 15 := Nat.odd_iff.mpr (by norm_num)
  have hfix : 15 * slopeOrbit 15 (class1SlopeDatum ctx).K₀ 1 = 15 := by rw [h1]
  have hconst := towerFixedPoint_orbit_const hq15 hK1 hKq hfix j hj
  rw [hconst, h1]
  exact towerFixedPoint_canonGap_four le_rfl (by norm_num)

/-! ## Part 9.  Honest machine-readable status -/

/-- The precise status of the Tower / Class 2 cycle-density closure after this module. -/
def towerCycleDensityStatus : List String :=
  [ "CLOSED (class-2 parity pins, NEW): every class-2 start has k >= 1 " ++
      "(class2Fibre_start_pos) hence an ODD orbit numerator (class2Fibre_orbit_odd); the " ++
      "band-4 window with odd K forces q in {9..15} or {25, 27, ...} " ++
      "(modulus_window_of_class2Fibre_nonempty); the class-2 fibre is PROVABLY EMPTY on " ++
      "every shell with modulus 16 < q < 25, i.e. q in {17,19,21,23} " ++
      "(class2Fibre_empty_of_modulus_window, class2CountBound_of_modulus_window, " ++
      "class2DeepShellWindowData_of_modulus_window) - a brand-new closed modulus subfamily " ++
      "beyond the wave-2 q < 9 closure; on q <= 15 every class-2 start has K_k = 1 EXACTLY " ++
      "(class2Fibre_orbit_eq_one_of_modulus_le_15).",
    "CLOSED (the cycle-density counting theorem, NEW - the main idea): for ANY period c of " ++
      "the orbit (valid from index 1, exists with c <= q by class2_orbit_period_exists), " ++
      "#fibre2 <= towerBand4CycleCount(q,K0,c) * ceil(K/c) " ++
      "(class2Fibre_card_le_cycleDensity, via the window injection " ++
      "towerBand4_window_card_le k |-> ((k-1) mod c + 1, (k-i0)/c) and the periodic " ++
      "transport towerCycle_orbit_mod / towerCycle_orbit_add_mul). The fibre count is " ++
      "controlled by the per-cycle band-4 density alone; b4 <= c always " ++
      "(towerBand4CycleCount_le).",
    "REDUCED (the strictly smaller cycle residual + proved bridges to the EXACT capstone " ++
      "field): Class2CycleInequality ctx := EXISTS c, period AND m0*(b4*ceil(K/c)) <= K - a " ++
      "single finite per-(q,K0,r,K) check (at most q canonical-gap evaluations + one Nat " ++
      "comparison). class2CountBound_of_cycleInequality discharges the count bound per ctx; " ++
      "Class2CycleDensityResidual (deep shells only) discharges Class2DeepShellCountBound " ++
      "outright (towerCountBound_ofCycleDensity), hence the full capstone Tower surface " ++
      "(towerDeepResidual_ofCycleDensity, p9V3TowerCount_ofCycleDensity, " ++
      "class2DeepShellWindowData_of_cycleInequality). Split entry folding in the proved " ++
      "modulus closures: towerCountBound_of_modulus_split (q < 9 OR 16 < q < 25 OR cycle " ++
      "inequality, per deep ctx).",
    "CLOSED (clean sufficient forms of the cycle inequality, NEW): a band-4-free period " ++
      "EMPTIES the fibre (class2Fibre_empty_of_cycle_band_free - the exact class-2 analogue " ++
      "of class1Fibre_empty_of_cycle_band_free; class2CycleInequality_of_band_free); the " ++
      "half-density check 2*(m0*b4) <= c <= K yields the count bound with the rounding " ++
      "worked exactly (towerHalfDensity_rounding: ceil loses at most one period, absorbed " ++
      "by the factor-2 slack; class2CycleInequality_of_half_density).",
    "CLOSED (the all-band-4 dichotomy, NEW - the structured line): a period whose EVERY " ++
      "reading is band 4 forces the exact 1/15 fixed point 15*K_1 = q " ++
      "(towerCycle_band4_full_forces_fixed, via the wave-2 run rigidity " ++
      "band4_run_forces_pow_lt extended along the cycle), hence 15 | q " ++
      "(towerCycle_band4_full_fifteen_dvd); at the fixed point the orbit is CONSTANT " ++
      "(towerFixedPoint_orbit_const, towerFixedPoint_canonGap_four). Off the fixed point " ++
      "b4 <= c - 1 for EVERY period (towerBand4CycleCount_lt_of_not_fixed): cycle band-4 " ++
      "density 1 happens ONLY on the 15 | q fixed-point family - the wave-2 obstruction " ++
      "family is exactly the full-cycle family.",
    "CLOSED (q = 9 modulus family, NEW): every admissible orbit has period 3 from index 1 " ++
      "(towerNine_orbit_period: odd states = the 3-cycle 1 -> 7 -> 5 plus the fixed point " ++
      "3) with at most ONE band-4 reading per period (towerNine_band4CycleCount_le_one: " ++
      "band 4 at q = 9 forces K = 1, whose successors 7, 5 exclude recurrence within 3). " ++
      "Hence the cycle inequality and the count bound hold OUTRIGHT on every q = 9 shell " ++
      "with m0 <= 2 (class2CycleInequality_of_modulus_nine, " ++
      "class2CountBound_of_modulus_nine, class2DeepShellWindowData_of_modulus_nine); " ++
      "m0 <= 2 iff r <= 41 (towerSparsityBlock_le_two_iff), so this covers ALL deep shells " ++
      "with 21 <= r <= 41 (roughly 328966 <= L <= 647529).",
    "CLOSED (q = 15 off the fixed point, NEW) + CHARACTERIZED (the open family): q = 15 is " ++
      "the t = 1 member of the 15 | q family; its odd states split into the band-4 fixed " ++
      "point {1} and the band-4-FREE cycles {5}, {3,9}, {7,13,11}. Off the fixed point " ++
      "(K_1 != 1) the orbit NEVER visits 1, the only band-4 state " ++
      "(towerFifteen_orbit_ne_one: the only odd predecessor of 1 is 1), so the fibre is " ++
      "PROVABLY EMPTY (class2Fibre_empty_of_modulus_fifteen_off_fixed, " ++
      "class2CountBound_of_modulus_fifteen_off_fixed). ON the fixed point (K_1 = 1) every " ++
      "positive index reads band 4 (class2_modulus_fifteen_fixed_family_band4): b4 = c = 1 " ++
      "and cycle counting CANNOT bound the fibre - the open family at q = 15 is EXACTLY " ++
      "K_1 = 1.",
    "HONESTLY NOT CLOSED (the count bound itself): open exactly where the cycle inequality " ++
      "fails - the 15 | q fixed-point orbits (b4 = c, density 1, every window start " ++
      "band-4-eligible) and any (q, K0, r) with cycle density b4/c above the demanded " ++
      "1/m0 ~ 64/(3(r+1)). Cycle counting reads ONLY the orbit side of the class-2 pin; " ++
      "the digit-side gap-window band 129L+64 < 64*gW < 130L+64 is NOT consumed, because " ++
      "no unconditional bridge ties hitGap to canonGap along the orbit (the wave-2 audit: " ++
      "the zero-run hypothesis of carry_tracks_slopeOrbit is not derivable from the window " ++
      "pins). No degenerate witness is fabricated.",
    "NON-DEGENERATE: every theorem is about the genuine routed class-2 fibre of " ++
      "genuineChargeRoute with the genuine carry data and the genuine closed AP-subfibre " ++
      "orbit datum (q = oddpart(Q(2|P|+1)), K0 = |P|); the counting injection maps real " ++
      "window starts to real cycle positions; the modulus closures are proved emptiness / " ++
      "cardinality facts, not fabricated data." ]

theorem towerCycleDensityStatus_nonempty : towerCycleDensityStatus ≠ [] := by
  simp [towerCycleDensityStatus]

/-! ## Part 10.  Axiom-cleanliness audit -/

#print axioms class2Fibre_start_pos
#print axioms class2Fibre_orbit_odd
#print axioms modulus_window_of_class2Fibre_nonempty
#print axioms class2Fibre_empty_of_modulus_window
#print axioms class2CountBound_of_modulus_window
#print axioms class2DeepShellWindowData_of_modulus_window
#print axioms class2Fibre_orbit_eq_one_of_modulus_le_15
#print axioms towerCycle_orbit_add_mul
#print axioms towerCycle_orbit_mod
#print axioms towerBand4CycleCount_le
#print axioms towerBand4CycleCount_eq_zero_of_band_free
#print axioms towerBand4_window_card_le
#print axioms class2Fibre_subset_band4Filter
#print axioms class2Fibre_card_le_cycleDensity
#print axioms class2_orbit_period_exists
#print axioms class2CountBound_of_cycleInequality
#print axioms class2DeepShellWindowData_of_cycleInequality
#print axioms towerCountBound_ofCycleDensity
#print axioms towerDeepResidual_ofCycleDensity
#print axioms p9V3TowerCount_ofCycleDensity
#print axioms towerCountBound_of_modulus_split
#print axioms class2Fibre_empty_of_cycle_band_free
#print axioms class2CycleInequality_of_band_free
#print axioms towerHalfDensity_rounding
#print axioms class2CycleInequality_of_half_density
#print axioms towerFixedPoint_canonGap_four
#print axioms towerFixedPoint_orbit_const
#print axioms towerCycle_band4_full_forces_fixed
#print axioms towerCycle_band4_full_fifteen_dvd
#print axioms towerBand4CycleCount_lt_of_not_fixed
#print axioms towerNine_orbit_period
#print axioms towerNine_band4CycleCount_le_one
#print axioms towerSparsityBlock_le_two_iff
#print axioms class2CycleInequality_of_modulus_nine
#print axioms class2CountBound_of_modulus_nine
#print axioms class2DeepShellWindowData_of_modulus_nine
#print axioms towerFifteen_orbit_ne_one
#print axioms class2Fibre_empty_of_modulus_fifteen_off_fixed
#print axioms class2CountBound_of_modulus_fifteen_off_fixed
#print axioms class2_modulus_fifteen_fixed_family_band4
#print axioms towerCycleDensityStatus_nonempty

end

end Erdos260
