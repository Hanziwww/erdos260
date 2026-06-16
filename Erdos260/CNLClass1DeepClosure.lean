import Erdos260.CNLClass1Closure

/-!
# Class-1 deep closure, wave 3: residue rigidity at `q ≤ 15` and the odd-modulus cycle tail

This module (NEW; it edits no existing file) attacks the wave-2 capstone field
`class1Pinned` (`Erdos260SharpCapstone`): refute `canonGap q K_k = 4` at the exact pin
`64·gapWindow = 129L + 64` on the surviving subfamily `64 ∣ L`, `9 ≤ q`,
`q ∈ {9,…,15} ∪ {25, 27, …}`, `Odd K_k`, window starts `k ≥ 1`.

## What is newly closed here (all unconditional)

* **The spacing-is-period rigidity**: two class-1 starts carrying EQUAL orbit numerators make
  their spacing a PERIOD of the recurrent orbit (`slopeOrbit_spacing_period`,
  `class1Fibre_spacing_period`); on `q ≤ 15` (where `K_k = 1` is forced) and on the new pin
  window `25 ≤ q ≤ 39` (where `K_k = 3` is forced — `class1Fibre_orbit_eq_three_of_modulus_window`)
  EVERY pair of class-1 starts is so spaced.
* **The residue pin**: periods are closed under difference and mod
  (`slopeOrbit_period_sub`, `slopeOrbit_period_mod`), so every period is a multiple of a
  minimal one (`slopeOrbit_minimalPeriod_dvd`); hence all class-1 starts with equal orbit
  numerators — in particular ALL of them when `q ≤ 15` — are congruent modulo the minimal
  orbit period (`class1Fibre_residue_pin`, `class1Fibre_residue_pin_of_modulus_le_15`).
* **The telescope rigidity**: all class-1 starts share the SAME exact window span
  `(129L+64)/64`, so for any two of them the hit increments repeat
  (`class1Fibre_span_rigidity`: `a(k+r+1) + a(k') = a(k'+r+1) + a(k)`;
  `class1Fibre_flank_sum_eq`: the `k'−k` gaps entering the window equal the `k'−k` gaps
  leaving it).
* **The adjacency obstruction**: two ADJACENT class-1 starts force the fixed-point modulus
  `q = 15·K_k` (`class1Fibre_adjacent_modulus_eq`); on `q ≤ 15` this forces `q = 15` exactly
  (`class1Fibre_adjacent_forces_q15_of_le15`), and on `25 ≤ q ≤ 39` it is IMPOSSIBLE
  (`class1Fibre_no_adjacent_of_modulus_window`, since `q = 45` would be forced).
* **The gated `|fibre₁| ≤ 1` extension**: under the numeric gate
  `64(r+1)(L+B+1) < 129L+64` (which forces `r ≤ 1`), every shell with modulus
  `q ≤ 13 ∨ 25 ≤ q ≤ 39` has AT MOST ONE class-1 start
  (`class1Fibre_card_le_one_of_gate_modulus`) — extending the wave-2 `r = 0` bound to the
  whole gated regime on those moduli.  The `r = 0` fibre is pinned INSIDE the singleton
  `{cnlWindowTopStart ctx}` (`class1Fibre_subset_top_of_r_eq_zero`), and `r ≥ 1` forces
  `L ≥ 15421` (`n24_L_ge_of_r_pos`).
* **The odd-modulus cycle tail closures**: explicit per-modulus emptiness for
  `q ∈ {27, 31, 33, 43, 45, 51, 65, 85, 91, 93}` (`class1Fibre_empty_of_modulus_eq_*`,
  dispatched by `class1Fibre_empty_of_mem_closedModuli` over `class1ClosedModuli`): for each
  admissible base numerator (`2K₀+1 ∣ q`, via the closed-datum pin `class1SlopeDatum_H_dvd`
  with `K₀ = |P|` from `class1SlopeDatum_K₀_eq`) one explicit period of the orbit is computed
  and verified band-4-free, feeding the wave-2 finite cycle-check closer
  `class1Fibre_empty_of_cycle_band_free`.  The family `(q, K₀) = (15, 7)` closes the same way
  (`class1Fibre_empty_of_q15_K₀7`).
* **The strictly smaller residual + bridge**: `Class1DeepResidual` (an `r = 0` SINGLE-START
  fact + a deep-shell emptiness restricted to the surviving moduli) discharges the capstone
  field exactly (`class1Pinned_of_deepResidual`), and plugs into the full wave-2 chain
  (`class1FibreEmpty_of_deepResidual`).

## Honest obstructions (documented, not fudged)

* `|fibre₁| ≤ 1` is NOT provable unconditionally for ungated `r ≥ 1` shells: the digit side
  is unconstrained there, and a hit sequence whose increments repeat along one residue class
  realizes many simultaneous exact pins.  The rigidity lemmas above are exactly what survives.
* The moduli `q ∈ {25, 29, 35, 37, 39, 41, 47, 49, …}` have band-4 elements with odd `K` ON
  the orbit cycle of some admissible `K₀` (e.g. `q = 25`: `K = 3` lies on the 10-cycle of
  both `K₀ = 2` and `K₀ = 12`; `q = 15`, `K₀ ∈ {1, 2}`: the orbit is the all-band-4 fixed
  point `K = 1`), so NO cycle-check closure exists for them; their refutation must come from
  the digit side and stays in the residual.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 0.  Evaluation helpers for explicit orbit cycles

`canonGap` evaluates through `Nat.log`; the two dyadic band inequalities pin it exactly.
These two lemmas let every concrete `(q, K₀)` orbit step be certified by `norm_num`. -/

/-- **Canonical-gap evaluator**: `2^g·K ≤ q < 2^{g+1}·K` pins `canonGap q K = g + 1`. -/
theorem canonGap_eval {q v g : ℕ} (hv : 1 ≤ v) (hlow : 2 ^ g * v ≤ q)
    (hhigh : q < 2 ^ (g + 1) * v) : canonGap q v = g + 1 := by
  unfold canonGap
  have h1 : 2 ^ g ≤ q / v := (Nat.le_div_iff_mul_le hv).mpr hlow
  have h2 : q / v < 2 ^ (g + 1) := (Nat.div_lt_iff_lt_mul hv).mpr hhigh
  rw [Nat.log_eq_of_pow_le_of_lt_pow h1 h2]

/-- **Orbit-step evaluator**: from `K_j = v` with the band data `2^g·v ≤ q < 2^{g+1}·v` and
the subtraction-free identity `2^{g+1}·v = q + w`, conclude `K_{j+1} = w`. -/
theorem slopeOrbit_step_eval {q K₀ : ℕ} (j g : ℕ) {v w : ℕ}
    (hv : slopeOrbit q K₀ j = v) (hv1 : 1 ≤ v)
    (hlow : 2 ^ g * v ≤ q) (hhigh : q < 2 ^ (g + 1) * v)
    (hw : 2 ^ (g + 1) * v = q + w) :
    slopeOrbit q K₀ (j + 1) = w := by
  have hstep : slopeOrbit q K₀ (j + 1) = boundedSlopeStep q (slopeOrbit q K₀ j) := rfl
  rw [hstep, hv]
  unfold boundedSlopeStep
  rw [canonGap_eval hv1 hlow hhigh, hw]
  omega

/-- A numerator outside the band-4 window `(q/16, q/8]` has `canonGap ≠ 4`. -/
theorem canonGap_ne_four_of_band {q K : ℕ} (h : q < 8 * K ∨ 16 * K ≤ q) :
    canonGap q K ≠ 4 := by
  intro h4
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · unfold canonGap at h4
    rw [Nat.div_zero, Nat.log_zero_right] at h4
    omega
  · obtain ⟨h8, h16⟩ := (canonGap_eq_four_iff hK).mp h4
    omega

/-! ## Part 1.  Spacing-is-period: the residue rigidity of equal orbit values

Backward determinism (`slopeOrbit_cancel`) peels a collision `K_k = K_{k'}` back to index `1`,
and forward determinism (`slopeOrbit_eq_shift`) pushes it over the whole orbit: the spacing
`k' − k` of any two equal-valued positive indices is a PERIOD valid from index `1`. -/

/-- **Spacing-is-period**: equal orbit values at positive indices `k < k'` make `k' − k` a
period of the orbit, valid from index `1` onward. -/
theorem slopeOrbit_spacing_period {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀) (hKq : K₀ < q)
    {k k' : ℕ} (hk : 1 ≤ k) (hlt : k < k')
    (heq : slopeOrbit q K₀ k = slopeOrbit q K₀ k') :
    ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + (k' - k)) = slopeOrbit q K₀ m := by
  have hpeel : slopeOrbit q K₀ (1 + (k' - k)) = slopeOrbit q K₀ 1 := by
    apply slopeOrbit_cancel hq hK1 hKq (k - 1) (by omega) le_rfl
    rw [show 1 + (k' - k) + (k - 1) = k' by omega, show 1 + (k - 1) = k by omega]
    exact heq.symm
  intro m hm
  have hshift := slopeOrbit_eq_shift hpeel (m - 1)
  rwa [show 1 + (k' - k) + (m - 1) = m + (k' - k) by omega,
    show 1 + (m - 1) = m by omega] at hshift

/-- Periods are closed under (positive) difference. -/
theorem slopeOrbit_period_sub {q K₀ c c' : ℕ} (hlt : c < c')
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    (hper' : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c') = slopeOrbit q K₀ m) :
    ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + (c' - c)) = slopeOrbit q K₀ m := by
  intro m hm
  have h1 := hper (m + (c' - c)) (by omega)
  rw [show m + (c' - c) + c = m + c' by omega] at h1
  exact h1.symm.trans (hper' m hm)

/-- Periods are closed under mod (Euclid): if `c, c'` are periods and `c' % c > 0`, then
`c' % c` is a period. -/
theorem slopeOrbit_period_mod {q K₀ c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m) :
    ∀ c', (∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c') = slopeOrbit q K₀ m) →
      0 < c' % c →
      ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c' % c) = slopeOrbit q K₀ m := by
  intro c'
  induction c' using Nat.strong_induction_on with
  | _ c' ih =>
    intro hper' hmod
    rcases Nat.lt_or_ge c' c with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hmod ⊢
      exact hper'
    · have hclt : c < c' := by
        rcases Nat.eq_or_lt_of_le hge with heq | hlt'
        · exfalso
          rw [← heq, Nat.mod_self] at hmod
          omega
        · exact hlt'
      have hsub := slopeOrbit_period_sub hclt hper hper'
      have hmodeq : (c' - c) % c = c' % c := (Nat.mod_eq_sub_mod hge).symm
      have hrec := ih (c' - c) (by omega) hsub (by rw [hmodeq]; exact hmod)
      rwa [hmodeq] at hrec

/-- **Every period is a multiple of a minimal period** (gcd structure of the period set). -/
theorem slopeOrbit_minimalPeriod_dvd {q K₀ c c' : ℕ} (hc : 1 ≤ c) (hc' : 1 ≤ c')
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    (hmin : ∀ c'', 1 ≤ c'' → c'' < c →
      ¬ ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c'') = slopeOrbit q K₀ m)
    (hper' : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c') = slopeOrbit q K₀ m) :
    c ∣ c' := by
  by_contra hndvd
  have hmod : 0 < c' % c := by
    rcases Nat.eq_zero_or_pos (c' % c) with h0 | hpos
    · exact absurd (Nat.dvd_of_mod_eq_zero h0) hndvd
    · exact hpos
  exact hmin (c' % c) hmod (Nat.mod_lt c' (by omega))
    (slopeOrbit_period_mod hc hper c' hper' hmod)

/-! ## Part 2.  The class-1 instantiations: equal-numerator starts and the pinned moduli -/

/-- **Class-1 spacing-is-period**: two class-1 starts with EQUAL orbit numerators make their
spacing a period of the recurrent orbit. -/
theorem class1Fibre_spacing_period (ctx : ActualFailureContext) {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k')
    (horb : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
      = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k') :
    ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m :=
  slopeOrbit_spacing_period (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt (class1Fibre_start_pos ctx hk) hlt horb

/-- **The `25 ≤ q ≤ 39` numerator pin** (the band-4 companion of the proved `q ≤ 15` pin
`K_k = 1`): on the window `25 ≤ q ≤ 39` every class-1 start has `K_k = 3` EXACTLY — the only
odd numerator in `(q/16, q/8]` there. -/
theorem class1Fibre_orbit_eq_three_of_modulus_window (ctx : ActualFailureContext)
    (h25 : 25 ≤ (class1SlopeDatum ctx).q) (h39 : (class1SlopeDatum ctx).q ≤ 39) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 3 := by
  obtain ⟨h8, h16⟩ := class1Fibre_orbit_band ctx hk
  obtain ⟨n, hn⟩ := class1Fibre_orbit_odd ctx hk
  omega

/-- On `q ≤ 15` the spacing of ANY two class-1 starts is an orbit period (both numerators
are pinned to `1`). -/
theorem class1Fibre_spacing_period_of_modulus_le_15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 15) {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m :=
  class1Fibre_spacing_period ctx hk hk' hlt (by
    rw [class1Fibre_orbit_eq_one_of_modulus_le_15 ctx hq hk,
      class1Fibre_orbit_eq_one_of_modulus_le_15 ctx hq hk'])

/-- **The residue pin**: two class-1 starts with equal orbit numerators are congruent modulo
any MINIMAL period of the orbit. -/
theorem class1Fibre_residue_pin (ctx : ActualFailureContext) {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hmin : ∀ c'', 1 ≤ c'' → c'' < c →
      ¬ ∀ m, 1 ≤ m →
        slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c'')
          = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (horb : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
      = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k') :
    k % c = k' % c := by
  have key : ∀ x y : ℕ,
      x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 →
      y ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 →
      x < y →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ x
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ y →
      x % c = y % c := by
    intro x y hx hy hxy ho
    have hper' := class1Fibre_spacing_period ctx hx hy hxy ho
    obtain ⟨t, ht⟩ :=
      slopeOrbit_minimalPeriod_dvd hc (by omega) hper hmin hper'
    have hy' : y = x + c * t := by omega
    rw [hy', Nat.add_mul_mod_self_left]
  rcases lt_trichotomy k k' with hlt | heq | hlt
  · exact key k k' hk hk' hlt horb
  · rw [heq]
  · exact (key k' k hk' hk hlt horb.symm).symm

/-- **The `q ≤ 15` residue pin**: ALL class-1 starts are congruent modulo any minimal orbit
period (their numerators are all pinned to `1`). -/
theorem class1Fibre_residue_pin_of_modulus_le_15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 15) {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hmin : ∀ c'', 1 ≤ c'' → c'' < c →
      ¬ ∀ m, 1 ≤ m →
        slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c'')
          = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % c = k' % c :=
  class1Fibre_residue_pin ctx hc hper hmin hk hk' (by
    rw [class1Fibre_orbit_eq_one_of_modulus_le_15 ctx hq hk,
      class1Fibre_orbit_eq_one_of_modulus_le_15 ctx hq hk'])

/-! ## Part 3.  The telescope rigidity across pinned starts

Every class-1 start realizes the SAME exact window span `(129L+64)/64`
(`class1Fibre_hitPosition_eq`), so the hit sequence repeats its increment totals across any
two class-1 starts: the `k' − k` gaps entering the window equal the `k' − k` gaps leaving it. -/

/-- **Span rigidity**: any two class-1 starts have equal window spans, in additive form
`a(k+r+1) + a(k') = a(k'+r+1) + a(k)`. -/
theorem class1Fibre_span_rigidity (ctx : ActualFailureContext) {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
      = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k := by
  have h1 := class1Fibre_hitPosition_eq ctx hk
  have h2 := class1Fibre_hitPosition_eq ctx hk'
  have m1 : ctx.n24CarryData.a k ≤ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) :=
    ctx.n24CarryData.carry.hits.strict.monotone (by omega)
  have m2 : ctx.n24CarryData.a k' ≤ ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) :=
    ctx.n24CarryData.carry.hits.strict.monotone (by omega)
  omega

/-- **Flank-sum rigidity** (the repeat-increment identity): for class-1 starts `k < k'`, the
`k' − k` hit gaps entering the window at `k` sum to EXACTLY the `k' − k` gaps leaving it. -/
theorem class1Fibre_flank_sum_eq (ctx : ActualFailureContext) {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    ∑ i ∈ Finset.Ico k k', hitGap ctx.n24CarryData.a i
      = ∑ i ∈ Finset.Ico (k + ctx.n24CarryData.r + 1) (k' + ctx.n24CarryData.r + 1),
          hitGap ctx.n24CarryData.a i := by
  have hs1 : ∑ i ∈ Finset.Ico k k', hitGap ctx.n24CarryData.a i
      = ctx.n24CarryData.a k' - ctx.n24CarryData.a k := by
    have h := ctx.n24CarryData.carry.hits.a_add_eq_sum_hitGap k (k' - k)
    rw [show k + (k' - k) = k' by omega] at h
    rw [Finset.sum_Ico_eq_sum_range]
    exact h.symm
  have hs2 : ∑ i ∈ Finset.Ico (k + ctx.n24CarryData.r + 1) (k' + ctx.n24CarryData.r + 1),
        hitGap ctx.n24CarryData.a i
      = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1)
        - ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) := by
    have h := ctx.n24CarryData.carry.hits.a_add_eq_sum_hitGap
      (k + ctx.n24CarryData.r + 1) (k' - k)
    rw [show k + ctx.n24CarryData.r + 1 + (k' - k) = k' + ctx.n24CarryData.r + 1
      by omega] at h
    rw [Finset.sum_Ico_eq_sum_range,
      show k' + ctx.n24CarryData.r + 1 - (k + ctx.n24CarryData.r + 1) = k' - k by omega]
    exact h.symm
  rw [hs1, hs2]
  have hspan := class1Fibre_span_rigidity ctx hk hk'
  have m1 : ctx.n24CarryData.a k ≤ ctx.n24CarryData.a k' :=
    ctx.n24CarryData.carry.hits.strict.monotone (by omega)
  have m2 : ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1)
      ≤ ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) :=
    ctx.n24CarryData.carry.hits.strict.monotone (by omega)
  omega

/-! ## Part 4.  The adjacency obstruction and the gated `|fibre₁| ≤ 1` extension -/

/-- **Adjacent class-1 starts force the fixed-point modulus**: if `k` and `k + 1` are both
class-1 starts with EQUAL orbit numerators, then `q = 15·K_k` (the E.13 band-4 step
`K_{k+1} = 16·K_k − q` collapses to a fixed point). -/
theorem class1Fibre_adjacent_modulus_eq (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (horb : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (k + 1)
      = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) :
    (class1SlopeDatum ctx).q
      = 15 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k := by
  have hstep := class1Fibre_orbit_step ctx hk
  obtain ⟨h8, h16⟩ := class1Fibre_orbit_band ctx hk
  omega

/-- On `q ≤ 15`, two ADJACENT class-1 starts force `q = 15` exactly. -/
theorem class1Fibre_adjacent_forces_q15_of_le15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 15) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk1 : k + 1 ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    (class1SlopeDatum ctx).q = 15 := by
  have h1 := class1Fibre_orbit_eq_one_of_modulus_le_15 ctx hq hk
  have h2 := class1Fibre_orbit_eq_one_of_modulus_le_15 ctx hq hk1
  have h := class1Fibre_adjacent_modulus_eq ctx hk (by rw [h2, h1])
  omega

/-- On the window `25 ≤ q ≤ 39`, ADJACENT class-1 starts are IMPOSSIBLE (the fixed point
would force `q = 45`). -/
theorem class1Fibre_no_adjacent_of_modulus_window (ctx : ActualFailureContext)
    (h25 : 25 ≤ (class1SlopeDatum ctx).q) (h39 : (class1SlopeDatum ctx).q ≤ 39) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk1 : k + 1 ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    False := by
  have h1 := class1Fibre_orbit_eq_three_of_modulus_window ctx h25 h39 hk
  have h2 := class1Fibre_orbit_eq_three_of_modulus_window ctx h25 h39 hk1
  have h := class1Fibre_adjacent_modulus_eq ctx hk (by rw [h2, h1])
  omega

/-- **The gated `|fibre₁| ≤ 1` extension**: under the numeric gate
`64(r+1)(L+B+1) < 129L+64` — which forces `r ≤ 1` — every shell with modulus
`q ≤ 13 ∨ 25 ≤ q ≤ 39` has at most ONE class-1 start.  (The gate confines the fibre to the
top `r + 1 ≤ 2` window starts; two survivors would be adjacent, which the modulus forbids.) -/
theorem class1Fibre_card_le_one_of_gate_modulus (ctx : ActualFailureContext)
    (hgate : 64 * ((ctx.n24CarryData.r + 1)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
      < 129 * shellLadderDepth ctx + 64)
    (hq : (class1SlopeDatum ctx).q ≤ 13
      ∨ (25 ≤ (class1SlopeDatum ctx).q ∧ (class1SlopeDatum ctx).q ≤ 39)) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card ≤ 1 := by
  have hr1 : ctx.n24CarryData.r ≤ 1 := by
    by_contra h
    have hL : 28 ≤ shellLadderDepth ctx := shellLadderDepth_ge ctx
    have h3 : 3 * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
        ≤ (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have key : ∀ x y : ℕ,
      x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 →
      y ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 →
      x < y → False := by
    intro x y hx hy hxy
    have hox := class1Fibre_window_overrun ctx hx hgate
    have hwx := class1Fibre_mem_window ctx hx
    have hwy := class1Fibre_mem_window ctx hy
    have hadj : y = x + 1 := by omega
    subst hadj
    rcases hq with hq13 | ⟨h25, h39⟩
    · have h15 := class1Fibre_adjacent_forces_q15_of_le15 ctx (by omega) hx hy
      omega
    · exact class1Fibre_no_adjacent_of_modulus_window ctx h25 h39 hx hy
  refine Finset.card_le_one.mpr ?_
  intro x hx y hy
  by_contra hne
  rcases lt_trichotomy x y with hlt | heq | hlt
  · exact key x y hx hy hlt
  · exact hne heq
  · exact key y x hy hx hlt

/-! ## Part 5.  The `r = 0` top-start pin and the deep-shell regime tie -/

/-- The topmost carry-window start `firstIndexAbove X + |supportShell| − 1` — the unique
possible class-1 start on `r = 0` shells. -/
def cnlWindowTopStart (ctx : ActualFailureContext) : ℕ :=
  ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
    + (supportShell ctx.shell.d ctx.shell.X).card - 1

/-- On `r = 0` shells the class-1 fibre is contained in the SINGLETON top start. -/
theorem class1Fibre_subset_top_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 ⊆ {cnlWindowTopStart ctx} := by
  intro k hk
  have htop := class1Fibre_top_of_r_eq_zero ctx hr hk
  rw [Finset.mem_singleton]
  unfold cnlWindowTopStart
  omega

/-- Deep shells are large: `r ≥ 1` forces `L ≥ 15421` (contrapositive of the proved
`n24_r_eq_zero_of_L_le`). -/
theorem n24_L_ge_of_r_pos (ctx : ActualFailureContext)
    (hr : 1 ≤ ctx.n24CarryData.r) : 15421 ≤ shellLadderDepth ctx := by
  by_contra h
  have h0 := n24_r_eq_zero_of_L_le ctx (by omega)
  omega

/-! ## Part 6.  The odd-modulus cycle tail: explicit per-modulus closures

For each admissible base numerator (`2K₀+1 ∣ q`, with `K₀ = |P|` by the closed-datum pins),
one explicit period of the recurrent orbit is computed and verified band-4-free; the wave-2
finite cycle-check closer `class1Fibre_empty_of_cycle_band_free` then empties the fibre.
The closable odd moduli below `100` are exactly `{27, 31, 33, 43, 45, 51, 65, 85, 91, 93}`
(every other surviving modulus has a band-4 odd numerator ON the cycle of some admissible
`K₀`). -/

/-- **The collision-form cycle closer**: a single orbit collision `K_{1+c} = K_1` plus `c`
band readings `≠ 4` empty the class-1 fibre (for the actual closed-datum `(q, K₀)`). -/
theorem class1Fibre_empty_of_orbit_collision (ctx : ActualFailureContext) {q K₀ c : ℕ}
    (hq : (class1SlopeDatum ctx).q = q) (hK₀ : (class1SlopeDatum ctx).K₀ = K₀)
    (hc : 1 ≤ c)
    (hcol : slopeOrbit q K₀ (1 + c) = slopeOrbit q K₀ 1)
    (hband : ∀ j, 1 ≤ j → j ≤ c → canonGap q (slopeOrbit q K₀ j) ≠ 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  subst hq
  subst hK₀
  refine class1Fibre_empty_of_cycle_band_free ctx hc ?_ hband
  intro m hm
  have hshift := slopeOrbit_eq_shift hcol (m - 1)
  rwa [show 1 + c + (m - 1) = m + c by omega, show 1 + (m - 1) = m by omega] at hshift


/-- Orbit cycle table for `(q, K₀) = (15, 7)`: period `3`,
cycle `13 → 11 → 7`, bands `1, 1, 2` · band-4-free. -/
private theorem cycle_15_7 :
    slopeOrbit 15 7 (1 + 3) = slopeOrbit 15 7 1
      ∧ ∀ j, 1 ≤ j → j ≤ 3 → canonGap 15 (slopeOrbit 15 7 j) ≠ 4 := by
  have e0 : slopeOrbit 15 7 0 = 7 := rfl
  have e1 : slopeOrbit 15 7 1 = 13 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 15 7 2 = 11 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 15 7 3 = 7 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 15 7 4 = 13 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 15 7 4 = slopeOrbit 15 7 1
    rw [e4, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (27, 1)`: period `9`,
cycle `5 → 13 → 25 → 23 → 19 → 11 → 17 → 7 → 1`, bands `3, 2, 1, 1, 1, 2, 1, 2, 5` · band-4-free. -/
private theorem cycle_27_1 :
    slopeOrbit 27 1 (1 + 9) = slopeOrbit 27 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 → canonGap 27 (slopeOrbit 27 1 j) ≠ 4 := by
  have e0 : slopeOrbit 27 1 0 = 1 := rfl
  have e1 : slopeOrbit 27 1 1 = 5 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 27 1 2 = 13 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 27 1 3 = 25 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 27 1 4 = 23 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 27 1 5 = 19 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 27 1 6 = 11 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 27 1 7 = 17 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 27 1 8 = 7 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 27 1 9 = 1 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 27 1 10 = 5 :=
    slopeOrbit_step_eval 9 4 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 27 1 10 = slopeOrbit 27 1 1
    rw [e10, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)
    · rw [e9]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (27, 4)`: period `9`,
cycle `5 → 13 → 25 → 23 → 19 → 11 → 17 → 7 → 1`, bands `3, 2, 1, 1, 1, 2, 1, 2, 5` · band-4-free. -/
private theorem cycle_27_4 :
    slopeOrbit 27 4 (1 + 9) = slopeOrbit 27 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 → canonGap 27 (slopeOrbit 27 4 j) ≠ 4 := by
  have e0 : slopeOrbit 27 4 0 = 4 := rfl
  have e1 : slopeOrbit 27 4 1 = 5 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 27 4 2 = 13 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 27 4 3 = 25 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 27 4 4 = 23 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 27 4 5 = 19 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 27 4 6 = 11 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 27 4 7 = 17 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 27 4 8 = 7 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 27 4 9 = 1 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 27 4 10 = 5 :=
    slopeOrbit_step_eval 9 4 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 27 4 10 = slopeOrbit 27 4 1
    rw [e10, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)
    · rw [e9]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (27, 13)`: period `9`,
cycle `25 → 23 → 19 → 11 → 17 → 7 → 1 → 5 → 13`, bands `1, 1, 1, 2, 1, 2, 5, 3, 2` · band-4-free. -/
private theorem cycle_27_13 :
    slopeOrbit 27 13 (1 + 9) = slopeOrbit 27 13 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 → canonGap 27 (slopeOrbit 27 13 j) ≠ 4 := by
  have e0 : slopeOrbit 27 13 0 = 13 := rfl
  have e1 : slopeOrbit 27 13 1 = 25 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 27 13 2 = 23 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 27 13 3 = 19 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 27 13 4 = 11 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 27 13 5 = 17 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 27 13 6 = 7 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 27 13 7 = 1 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 27 13 8 = 5 :=
    slopeOrbit_step_eval 7 4 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 27 13 9 = 13 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 27 13 10 = 25 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 27 13 10 = slopeOrbit 27 13 1
    rw [e10, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)
    · rw [e9]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (31, 15)`: period `4`,
cycle `29 → 27 → 23 → 15`, bands `1, 1, 1, 2` · band-4-free. -/
private theorem cycle_31_15 :
    slopeOrbit 31 15 (1 + 4) = slopeOrbit 31 15 1
      ∧ ∀ j, 1 ≤ j → j ≤ 4 → canonGap 31 (slopeOrbit 31 15 j) ≠ 4 := by
  have e0 : slopeOrbit 31 15 0 = 15 := rfl
  have e1 : slopeOrbit 31 15 1 = 29 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 31 15 2 = 27 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 31 15 3 = 23 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 31 15 4 = 15 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 31 15 5 = 29 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 31 15 5 = slopeOrbit 31 15 1
    rw [e5, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (33, 1)`: period `5`,
cycle `31 → 29 → 25 → 17 → 1`, bands `1, 1, 1, 1, 6` · band-4-free. -/
private theorem cycle_33_1 :
    slopeOrbit 33 1 (1 + 5) = slopeOrbit 33 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 33 (slopeOrbit 33 1 j) ≠ 4 := by
  have e0 : slopeOrbit 33 1 0 = 1 := rfl
  have e1 : slopeOrbit 33 1 1 = 31 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 33 1 2 = 29 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 33 1 3 = 25 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 33 1 4 = 17 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 33 1 5 = 1 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 33 1 6 = 31 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 33 1 6 = slopeOrbit 33 1 1
    rw [e6, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (33, 5)`: period `5`,
cycle `7 → 23 → 13 → 19 → 5`, bands `3, 1, 2, 1, 3` · band-4-free. -/
private theorem cycle_33_5 :
    slopeOrbit 33 5 (1 + 5) = slopeOrbit 33 5 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 33 (slopeOrbit 33 5 j) ≠ 4 := by
  have e0 : slopeOrbit 33 5 0 = 5 := rfl
  have e1 : slopeOrbit 33 5 1 = 7 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 33 5 2 = 23 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 33 5 3 = 13 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 33 5 4 = 19 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 33 5 5 = 5 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 33 5 6 = 7 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 33 5 6 = slopeOrbit 33 5 1
    rw [e6, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (33, 16)`: period `5`,
cycle `31 → 29 → 25 → 17 → 1`, bands `1, 1, 1, 1, 6` · band-4-free. -/
private theorem cycle_33_16 :
    slopeOrbit 33 16 (1 + 5) = slopeOrbit 33 16 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 33 (slopeOrbit 33 16 j) ≠ 4 := by
  have e0 : slopeOrbit 33 16 0 = 16 := rfl
  have e1 : slopeOrbit 33 16 1 = 31 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 33 16 2 = 29 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 33 16 3 = 25 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 33 16 4 = 17 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 33 16 5 = 1 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 33 16 6 = 31 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 33 16 6 = slopeOrbit 33 16 1
    rw [e6, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (43, 21)`: period `7`,
cycle `41 → 39 → 35 → 27 → 11 → 1 → 21`, bands `1, 1, 1, 1, 2, 6, 2` · band-4-free. -/
private theorem cycle_43_21 :
    slopeOrbit 43 21 (1 + 7) = slopeOrbit 43 21 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 → canonGap 43 (slopeOrbit 43 21 j) ≠ 4 := by
  have e0 : slopeOrbit 43 21 0 = 21 := rfl
  have e1 : slopeOrbit 43 21 1 = 41 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 43 21 2 = 39 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 43 21 3 = 35 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 43 21 4 = 27 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 43 21 5 = 11 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 43 21 6 = 1 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 43 21 7 = 21 :=
    slopeOrbit_step_eval 6 5 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 43 21 8 = 41 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 43 21 8 = slopeOrbit 43 21 1
    rw [e8, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (45, 1)`: period `5`,
cycle `19 → 31 → 17 → 23 → 1`, bands `2, 1, 2, 1, 6` · band-4-free. -/
private theorem cycle_45_1 :
    slopeOrbit 45 1 (1 + 5) = slopeOrbit 45 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 45 (slopeOrbit 45 1 j) ≠ 4 := by
  have e0 : slopeOrbit 45 1 0 = 1 := rfl
  have e1 : slopeOrbit 45 1 1 = 19 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 45 1 2 = 31 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 45 1 3 = 17 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 45 1 4 = 23 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 45 1 5 = 1 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 45 1 6 = 19 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 45 1 6 = slopeOrbit 45 1 1
    rw [e6, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (45, 2)`: period `5`,
cycle `19 → 31 → 17 → 23 → 1`, bands `2, 1, 2, 1, 6` · band-4-free. -/
private theorem cycle_45_2 :
    slopeOrbit 45 2 (1 + 5) = slopeOrbit 45 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 45 (slopeOrbit 45 2 j) ≠ 4 := by
  have e0 : slopeOrbit 45 2 0 = 2 := rfl
  have e1 : slopeOrbit 45 2 1 = 19 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 45 2 2 = 31 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 45 2 3 = 17 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 45 2 4 = 23 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 45 2 5 = 1 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 45 2 6 = 19 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 45 2 6 = slopeOrbit 45 2 1
    rw [e6, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (45, 4)`: period `5`,
cycle `19 → 31 → 17 → 23 → 1`, bands `2, 1, 2, 1, 6` · band-4-free. -/
private theorem cycle_45_4 :
    slopeOrbit 45 4 (1 + 5) = slopeOrbit 45 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 45 (slopeOrbit 45 4 j) ≠ 4 := by
  have e0 : slopeOrbit 45 4 0 = 4 := rfl
  have e1 : slopeOrbit 45 4 1 = 19 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 45 4 2 = 31 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 45 4 3 = 17 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 45 4 4 = 23 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 45 4 5 = 1 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 45 4 6 = 19 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 45 4 6 = slopeOrbit 45 4 1
    rw [e6, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (45, 7)`: period `7`,
cycle `11 → 43 → 41 → 37 → 29 → 13 → 7`, bands `3, 1, 1, 1, 1, 2, 3` · band-4-free. -/
private theorem cycle_45_7 :
    slopeOrbit 45 7 (1 + 7) = slopeOrbit 45 7 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 → canonGap 45 (slopeOrbit 45 7 j) ≠ 4 := by
  have e0 : slopeOrbit 45 7 0 = 7 := rfl
  have e1 : slopeOrbit 45 7 1 = 11 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 45 7 2 = 43 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 45 7 3 = 41 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 45 7 4 = 37 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 45 7 5 = 29 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 45 7 6 = 13 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 45 7 7 = 7 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 45 7 8 = 11 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 45 7 8 = slopeOrbit 45 7 1
    rw [e8, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (45, 22)`: period `7`,
cycle `43 → 41 → 37 → 29 → 13 → 7 → 11`, bands `1, 1, 1, 1, 2, 3, 3` · band-4-free. -/
private theorem cycle_45_22 :
    slopeOrbit 45 22 (1 + 7) = slopeOrbit 45 22 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 → canonGap 45 (slopeOrbit 45 22 j) ≠ 4 := by
  have e0 : slopeOrbit 45 22 0 = 22 := rfl
  have e1 : slopeOrbit 45 22 1 = 43 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 45 22 2 = 41 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 45 22 3 = 37 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 45 22 4 = 29 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 45 22 5 = 13 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 45 22 6 = 7 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 45 22 7 = 11 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 45 22 8 = 43 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 45 22 8 = slopeOrbit 45 22 1
    rw [e8, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (51, 1)`: period `2`,
cycle `13 → 1`, bands `2, 6` · band-4-free. -/
private theorem cycle_51_1 :
    slopeOrbit 51 1 (1 + 2) = slopeOrbit 51 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → canonGap 51 (slopeOrbit 51 1 j) ≠ 4 := by
  have e0 : slopeOrbit 51 1 0 = 1 := rfl
  have e1 : slopeOrbit 51 1 1 = 13 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 51 1 2 = 1 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 51 1 3 = 13 :=
    slopeOrbit_step_eval 2 5 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 51 1 3 = slopeOrbit 51 1 1
    rw [e3, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (51, 8)`: period `2`,
cycle `13 → 1`, bands `2, 6` · band-4-free. -/
private theorem cycle_51_8 :
    slopeOrbit 51 8 (1 + 2) = slopeOrbit 51 8 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → canonGap 51 (slopeOrbit 51 8 j) ≠ 4 := by
  have e0 : slopeOrbit 51 8 0 = 8 := rfl
  have e1 : slopeOrbit 51 8 1 = 13 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 51 8 2 = 1 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 51 8 3 = 13 :=
    slopeOrbit_step_eval 2 5 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 51 8 3 = slopeOrbit 51 8 1
    rw [e3, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (51, 25)`: period `6`,
cycle `49 → 47 → 43 → 35 → 19 → 25`, bands `1, 1, 1, 1, 2, 2` · band-4-free. -/
private theorem cycle_51_25 :
    slopeOrbit 51 25 (1 + 6) = slopeOrbit 51 25 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 51 (slopeOrbit 51 25 j) ≠ 4 := by
  have e0 : slopeOrbit 51 25 0 = 25 := rfl
  have e1 : slopeOrbit 51 25 1 = 49 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 51 25 2 = 47 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 51 25 3 = 43 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 51 25 4 = 35 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 51 25 5 = 19 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 51 25 6 = 25 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 51 25 7 = 49 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 51 25 7 = slopeOrbit 51 25 1
    rw [e7, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (65, 2)`: period `6`,
cycle `63 → 61 → 57 → 49 → 33 → 1`, bands `1, 1, 1, 1, 1, 7` · band-4-free. -/
private theorem cycle_65_2 :
    slopeOrbit 65 2 (1 + 6) = slopeOrbit 65 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 65 (slopeOrbit 65 2 j) ≠ 4 := by
  have e0 : slopeOrbit 65 2 0 = 2 := rfl
  have e1 : slopeOrbit 65 2 1 = 63 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 65 2 2 = 61 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 65 2 3 = 57 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 65 2 4 = 49 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 65 2 5 = 33 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 65 2 6 = 1 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 65 2 7 = 63 :=
    slopeOrbit_step_eval 6 6 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 65 2 7 = slopeOrbit 65 2 1
    rw [e7, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (65, 6)`: period `6`,
cycle `31 → 59 → 53 → 41 → 17 → 3`, bands `2, 1, 1, 1, 2, 5` · band-4-free. -/
private theorem cycle_65_6 :
    slopeOrbit 65 6 (1 + 6) = slopeOrbit 65 6 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 65 (slopeOrbit 65 6 j) ≠ 4 := by
  have e0 : slopeOrbit 65 6 0 = 6 := rfl
  have e1 : slopeOrbit 65 6 1 = 31 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 65 6 2 = 59 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 65 6 3 = 53 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 65 6 4 = 41 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 65 6 5 = 17 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 65 6 6 = 3 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 65 6 7 = 31 :=
    slopeOrbit_step_eval 6 4 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 65 6 7 = slopeOrbit 65 6 1
    rw [e7, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (65, 32)`: period `6`,
cycle `63 → 61 → 57 → 49 → 33 → 1`, bands `1, 1, 1, 1, 1, 7` · band-4-free. -/
private theorem cycle_65_32 :
    slopeOrbit 65 32 (1 + 6) = slopeOrbit 65 32 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 65 (slopeOrbit 65 32 j) ≠ 4 := by
  have e0 : slopeOrbit 65 32 0 = 32 := rfl
  have e1 : slopeOrbit 65 32 1 = 63 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 65 32 2 = 61 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 65 32 3 = 57 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 65 32 4 = 49 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 65 32 5 = 33 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 65 32 6 = 1 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 65 32 7 = 63 :=
    slopeOrbit_step_eval 6 6 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 65 32 7 = slopeOrbit 65 32 1
    rw [e7, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (85, 2)`: period `2`,
cycle `43 → 1`, bands `1, 7` · band-4-free. -/
private theorem cycle_85_2 :
    slopeOrbit 85 2 (1 + 2) = slopeOrbit 85 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → canonGap 85 (slopeOrbit 85 2 j) ≠ 4 := by
  have e0 : slopeOrbit 85 2 0 = 2 := rfl
  have e1 : slopeOrbit 85 2 1 = 43 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 85 2 2 = 1 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 85 2 3 = 43 :=
    slopeOrbit_step_eval 2 6 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 85 2 3 = slopeOrbit 85 2 1
    rw [e3, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (85, 8)`: period `2`,
cycle `43 → 1`, bands `1, 7` · band-4-free. -/
private theorem cycle_85_8 :
    slopeOrbit 85 8 (1 + 2) = slopeOrbit 85 8 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → canonGap 85 (slopeOrbit 85 8 j) ≠ 4 := by
  have e0 : slopeOrbit 85 8 0 = 8 := rfl
  have e1 : slopeOrbit 85 8 1 = 43 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 85 8 2 = 1 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 85 8 3 = 43 :=
    slopeOrbit_step_eval 2 6 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 85 8 3 = slopeOrbit 85 8 1
    rw [e3, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (85, 42)`: period `6`,
cycle `83 → 81 → 77 → 69 → 53 → 21`, bands `1, 1, 1, 1, 1, 3` · band-4-free. -/
private theorem cycle_85_42 :
    slopeOrbit 85 42 (1 + 6) = slopeOrbit 85 42 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 85 (slopeOrbit 85 42 j) ≠ 4 := by
  have e0 : slopeOrbit 85 42 0 = 42 := rfl
  have e1 : slopeOrbit 85 42 1 = 83 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 85 42 2 = 81 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 85 42 3 = 77 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 85 42 4 = 69 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 85 42 5 = 53 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 85 42 6 = 21 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 85 42 7 = 83 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 85 42 7 = slopeOrbit 85 42 1
    rw [e7, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (91, 3)`: period `4`,
cycle `5 → 69 → 47 → 3`, bands `5, 1, 1, 5` · band-4-free. -/
private theorem cycle_91_3 :
    slopeOrbit 91 3 (1 + 4) = slopeOrbit 91 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 4 → canonGap 91 (slopeOrbit 91 3 j) ≠ 4 := by
  have e0 : slopeOrbit 91 3 0 = 3 := rfl
  have e1 : slopeOrbit 91 3 1 = 5 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 91 3 2 = 69 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 91 3 3 = 47 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 91 3 4 = 3 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 91 3 5 = 5 :=
    slopeOrbit_step_eval 4 4 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 91 3 5 = slopeOrbit 91 3 1
    rw [e5, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (91, 6)`: period `4`,
cycle `5 → 69 → 47 → 3`, bands `5, 1, 1, 5` · band-4-free. -/
private theorem cycle_91_6 :
    slopeOrbit 91 6 (1 + 4) = slopeOrbit 91 6 1
      ∧ ∀ j, 1 ≤ j → j ≤ 4 → canonGap 91 (slopeOrbit 91 6 j) ≠ 4 := by
  have e0 : slopeOrbit 91 6 0 = 6 := rfl
  have e1 : slopeOrbit 91 6 1 = 5 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 91 6 2 = 69 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 91 6 3 = 47 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 91 6 4 = 3 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 91 6 5 = 5 :=
    slopeOrbit_step_eval 4 4 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 91 6 5 = slopeOrbit 91 6 1
    rw [e5, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (91, 45)`: period `8`,
cycle `89 → 87 → 83 → 75 → 59 → 27 → 17 → 45`, bands `1, 1, 1, 1, 1, 2, 3, 2` · band-4-free. -/
private theorem cycle_91_45 :
    slopeOrbit 91 45 (1 + 8) = slopeOrbit 91 45 1
      ∧ ∀ j, 1 ≤ j → j ≤ 8 → canonGap 91 (slopeOrbit 91 45 j) ≠ 4 := by
  have e0 : slopeOrbit 91 45 0 = 45 := rfl
  have e1 : slopeOrbit 91 45 1 = 89 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 91 45 2 = 87 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 91 45 3 = 83 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 91 45 4 = 75 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 91 45 5 = 59 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 91 45 6 = 27 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 91 45 7 = 17 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 91 45 8 = 45 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 91 45 9 = 89 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 91 45 9 = slopeOrbit 91 45 1
    rw [e9, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)
    · rw [e8]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (93, 1)`: period `3`,
cycle `35 → 47 → 1`, bands `2, 1, 7` · band-4-free. -/
private theorem cycle_93_1 :
    slopeOrbit 93 1 (1 + 3) = slopeOrbit 93 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 3 → canonGap 93 (slopeOrbit 93 1 j) ≠ 4 := by
  have e0 : slopeOrbit 93 1 0 = 1 := rfl
  have e1 : slopeOrbit 93 1 1 = 35 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 93 1 2 = 47 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 93 1 3 = 1 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 93 1 4 = 35 :=
    slopeOrbit_step_eval 3 6 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 93 1 4 = slopeOrbit 93 1 1
    rw [e4, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (93, 15)`: period `2`,
cycle `27 → 15`, bands `2, 3` · band-4-free. -/
private theorem cycle_93_15 :
    slopeOrbit 93 15 (1 + 2) = slopeOrbit 93 15 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → canonGap 93 (slopeOrbit 93 15 j) ≠ 4 := by
  have e0 : slopeOrbit 93 15 0 = 15 := rfl
  have e1 : slopeOrbit 93 15 1 = 27 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 93 15 2 = 15 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 93 15 3 = 27 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 93 15 3 = slopeOrbit 93 15 1
    rw [e3, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle table for `(q, K₀) = (93, 46)`: period `7`,
cycle `91 → 89 → 85 → 77 → 61 → 29 → 23`, bands `1, 1, 1, 1, 1, 2, 3` · band-4-free. -/
private theorem cycle_93_46 :
    slopeOrbit 93 46 (1 + 7) = slopeOrbit 93 46 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 → canonGap 93 (slopeOrbit 93 46 j) ≠ 4 := by
  have e0 : slopeOrbit 93 46 0 = 46 := rfl
  have e1 : slopeOrbit 93 46 1 = 91 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 93 46 2 = 89 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 93 46 3 = 85 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 93 46 4 = 77 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 93 46 5 = 61 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 93 46 6 = 29 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 93 46 7 = 23 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 93 46 8 = 91 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 93 46 8 = slopeOrbit 93 46 1
    rw [e8, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)
    · rw [e7]; exact canonGap_ne_four_of_band (by omega)

/-- **Modulus-27 closure**: the class-1 fibre is empty on every shell with orbit modulus
`q = 27` (every admissible `K₀` with `2K₀ + 1 ∣ 27` has a band-4-free cycle). -/
theorem class1Fibre_empty_of_modulus_eq_27 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  obtain ⟨v, hv⟩ : ∃ v, (class1SlopeDatum ctx).K₀ = v := ⟨_, rfl⟩
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq, hv] at hdvd
  have hpos : 1 ≤ v := by rw [← hv]; exact (class1SlopeDatum ctx).hK₀_pos
  have hub : v ≤ 13 := by
    have h := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases v
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_27_1.1 cycle_27_1.2
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_27_4.1 cycle_27_4.2
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_27_13.1 cycle_27_13.2

/-- **Modulus-31 closure**: the class-1 fibre is empty on every shell with orbit modulus
`q = 31` (every admissible `K₀` with `2K₀ + 1 ∣ 31` has a band-4-free cycle). -/
theorem class1Fibre_empty_of_modulus_eq_31 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 31) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  obtain ⟨v, hv⟩ : ∃ v, (class1SlopeDatum ctx).K₀ = v := ⟨_, rfl⟩
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq, hv] at hdvd
  have hpos : 1 ≤ v := by rw [← hv]; exact (class1SlopeDatum ctx).hK₀_pos
  have hub : v ≤ 15 := by
    have h := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases v
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_31_15.1 cycle_31_15.2

/-- **Modulus-33 closure**: the class-1 fibre is empty on every shell with orbit modulus
`q = 33` (every admissible `K₀` with `2K₀ + 1 ∣ 33` has a band-4-free cycle). -/
theorem class1Fibre_empty_of_modulus_eq_33 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  obtain ⟨v, hv⟩ : ∃ v, (class1SlopeDatum ctx).K₀ = v := ⟨_, rfl⟩
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq, hv] at hdvd
  have hpos : 1 ≤ v := by rw [← hv]; exact (class1SlopeDatum ctx).hK₀_pos
  have hub : v ≤ 16 := by
    have h := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases v
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_33_1.1 cycle_33_1.2
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_33_5.1 cycle_33_5.2
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_33_16.1 cycle_33_16.2

/-- **Modulus-43 closure**: the class-1 fibre is empty on every shell with orbit modulus
`q = 43` (every admissible `K₀` with `2K₀ + 1 ∣ 43` has a band-4-free cycle). -/
theorem class1Fibre_empty_of_modulus_eq_43 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 43) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  obtain ⟨v, hv⟩ : ∃ v, (class1SlopeDatum ctx).K₀ = v := ⟨_, rfl⟩
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq, hv] at hdvd
  have hpos : 1 ≤ v := by rw [← hv]; exact (class1SlopeDatum ctx).hK₀_pos
  have hub : v ≤ 21 := by
    have h := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases v
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_43_21.1 cycle_43_21.2

/-- **Modulus-45 closure**: the class-1 fibre is empty on every shell with orbit modulus
`q = 45` (every admissible `K₀` with `2K₀ + 1 ∣ 45` has a band-4-free cycle). -/
theorem class1Fibre_empty_of_modulus_eq_45 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  obtain ⟨v, hv⟩ : ∃ v, (class1SlopeDatum ctx).K₀ = v := ⟨_, rfl⟩
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq, hv] at hdvd
  have hpos : 1 ≤ v := by rw [← hv]; exact (class1SlopeDatum ctx).hK₀_pos
  have hub : v ≤ 22 := by
    have h := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases v
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_45_1.1 cycle_45_1.2
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_45_2.1 cycle_45_2.2
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_45_4.1 cycle_45_4.2
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_45_7.1 cycle_45_7.2
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_45_22.1 cycle_45_22.2

/-- **Modulus-51 closure**: the class-1 fibre is empty on every shell with orbit modulus
`q = 51` (every admissible `K₀` with `2K₀ + 1 ∣ 51` has a band-4-free cycle). -/
theorem class1Fibre_empty_of_modulus_eq_51 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 51) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  obtain ⟨v, hv⟩ : ∃ v, (class1SlopeDatum ctx).K₀ = v := ⟨_, rfl⟩
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq, hv] at hdvd
  have hpos : 1 ≤ v := by rw [← hv]; exact (class1SlopeDatum ctx).hK₀_pos
  have hub : v ≤ 25 := by
    have h := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases v
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_51_1.1 cycle_51_1.2
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_51_8.1 cycle_51_8.2
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_51_25.1 cycle_51_25.2

/-- **Modulus-65 closure**: the class-1 fibre is empty on every shell with orbit modulus
`q = 65` (every admissible `K₀` with `2K₀ + 1 ∣ 65` has a band-4-free cycle). -/
theorem class1Fibre_empty_of_modulus_eq_65 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 65) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  obtain ⟨v, hv⟩ : ∃ v, (class1SlopeDatum ctx).K₀ = v := ⟨_, rfl⟩
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq, hv] at hdvd
  have hpos : 1 ≤ v := by rw [← hv]; exact (class1SlopeDatum ctx).hK₀_pos
  have hub : v ≤ 32 := by
    have h := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases v
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_65_2.1 cycle_65_2.2
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_65_6.1 cycle_65_6.2
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_65_32.1 cycle_65_32.2

/-- **Modulus-85 closure**: the class-1 fibre is empty on every shell with orbit modulus
`q = 85` (every admissible `K₀` with `2K₀ + 1 ∣ 85` has a band-4-free cycle). -/
theorem class1Fibre_empty_of_modulus_eq_85 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 85) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  obtain ⟨v, hv⟩ : ∃ v, (class1SlopeDatum ctx).K₀ = v := ⟨_, rfl⟩
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq, hv] at hdvd
  have hpos : 1 ≤ v := by rw [← hv]; exact (class1SlopeDatum ctx).hK₀_pos
  have hub : v ≤ 42 := by
    have h := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases v
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_85_2.1 cycle_85_2.2
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_85_8.1 cycle_85_8.2
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_85_42.1 cycle_85_42.2

/-- **Modulus-91 closure**: the class-1 fibre is empty on every shell with orbit modulus
`q = 91` (every admissible `K₀` with `2K₀ + 1 ∣ 91` has a band-4-free cycle). -/
theorem class1Fibre_empty_of_modulus_eq_91 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 91) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  obtain ⟨v, hv⟩ : ∃ v, (class1SlopeDatum ctx).K₀ = v := ⟨_, rfl⟩
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq, hv] at hdvd
  have hpos : 1 ≤ v := by rw [← hv]; exact (class1SlopeDatum ctx).hK₀_pos
  have hub : v ≤ 45 := by
    have h := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases v
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_91_3.1 cycle_91_3.2
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_91_6.1 cycle_91_6.2
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_91_45.1 cycle_91_45.2

/-- **Modulus-93 closure**: the class-1 fibre is empty on every shell with orbit modulus
`q = 93` (every admissible `K₀` with `2K₀ + 1 ∣ 93` has a band-4-free cycle). -/
theorem class1Fibre_empty_of_modulus_eq_93 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 93) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  obtain ⟨v, hv⟩ : ∃ v, (class1SlopeDatum ctx).K₀ = v := ⟨_, rfl⟩
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq, hv] at hdvd
  have hpos : 1 ≤ v := by rw [← hv]; exact (class1SlopeDatum ctx).hK₀_pos
  have hub : v ≤ 46 := by
    have h := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases v
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_93_1.1 cycle_93_1.2
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_93_15.1 cycle_93_15.2
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact class1Fibre_empty_of_orbit_collision ctx hq hv (by norm_num)
      cycle_93_46.1 cycle_93_46.2


/-- **The `(q, K₀) = (15, 7)` family closure**: the only `q ≤ 15` datum whose orbit avoids
band 4 — odd cycle `13 → 11 → 7`, bands `2, 1, 1`.  (For `K₀ ∈ {1, 2}` at `q = 15` the
orbit is the all-band-4 fixed point `K = 1`, and for `q ∈ {9, 11, 13}` every admissible
cycle contains `K = 1` with `canonGap = 4`; those families are NOT cycle-closable.) -/
theorem class1Fibre_empty_of_q15_K₀7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 7) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) cycle_15_7.1 cycle_15_7.2

/-! ## Part 7.  The closed-moduli dispatch -/

/-- The odd moduli below `100` whose class-1 fibre is closed by the cycle checks of this
module (beyond the proved `q < 9` and `16 < q < 25` closures). -/
def class1ClosedModuli : Finset ℕ := {27, 31, 33, 43, 45, 51, 65, 85, 91, 93}

/-- **The closed-moduli dispatch**: the class-1 fibre is empty on every shell whose orbit
modulus lies in `class1ClosedModuli`. -/
theorem class1Fibre_empty_of_mem_closedModuli (ctx : ActualFailureContext)
    (h : (class1SlopeDatum ctx).q ∈ class1ClosedModuli) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  have h' : (class1SlopeDatum ctx).q = 27 ∨ (class1SlopeDatum ctx).q = 31
      ∨ (class1SlopeDatum ctx).q = 33 ∨ (class1SlopeDatum ctx).q = 43
      ∨ (class1SlopeDatum ctx).q = 45 ∨ (class1SlopeDatum ctx).q = 51
      ∨ (class1SlopeDatum ctx).q = 65 ∨ (class1SlopeDatum ctx).q = 85
      ∨ (class1SlopeDatum ctx).q = 91 ∨ (class1SlopeDatum ctx).q = 93 := by
    simpa [class1ClosedModuli] using h
  rcases h' with h' | h' | h' | h' | h' | h' | h' | h' | h' | h'
  · exact class1Fibre_empty_of_modulus_eq_27 ctx h'
  · exact class1Fibre_empty_of_modulus_eq_31 ctx h'
  · exact class1Fibre_empty_of_modulus_eq_33 ctx h'
  · exact class1Fibre_empty_of_modulus_eq_43 ctx h'
  · exact class1Fibre_empty_of_modulus_eq_45 ctx h'
  · exact class1Fibre_empty_of_modulus_eq_51 ctx h'
  · exact class1Fibre_empty_of_modulus_eq_65 ctx h'
  · exact class1Fibre_empty_of_modulus_eq_85 ctx h'
  · exact class1Fibre_empty_of_modulus_eq_91 ctx h'
  · exact class1Fibre_empty_of_modulus_eq_93 ctx h'

/-- The v3 seed budget routes through the genuine route, so the closed-moduli dispatch
applies to it verbatim. -/
theorem v3_class1Fibre_empty_of_mem_closedModuli
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (ctx : ActualFailureContext)
    (h : (class1SlopeDatum ctx).q ∈ class1ClosedModuli) :
    routedFibre ctx.n24CarryData
      ((v3Budget towerCount runChain returnCharge) ctx).route 1 = ∅ :=
  class1Fibre_empty_of_mem_closedModuli ctx h

/-! ## Part 8.  The strictly smaller wave-3 residual and the capstone bridge

`Class1DeepResidual` splits the surviving subfamily along the `r = ⌊κL⌋` regime: on `r = 0`
shells (ALL `L ≤ 15420`) the fibre is pinned inside the single top start, so only ONE
per-context start fact is needed; on deep shells (`r ≥ 1`, `L ≥ 15421`) the emptiness Prop
survives, but only on moduli outside `class1ClosedModuli`.  The bridge
`class1Pinned_of_deepResidual` produces EXACTLY the capstone field `class1Pinned`. -/

/-- **The wave-3 class-1 residual.**  Field 1: on `r = 0` shells the SINGLE top window start
is not class-1 (a one-start fact per context).  Field 2: on deep shells (`r ≥ 1`), the fibre
is empty on the moduli surviving every closure of waves 1–3. -/
structure Class1DeepResidual : Prop where
  /-- `r = 0` shells: the unique candidate (the top window start) is not class-1. -/
  topStart : ∀ ctx : ActualFailureContext,
    ctx.n24CarryData.r = 0 →
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  /-- Deep shells (`r ≥ 1`, hence `L ≥ 15421`): emptiness on the surviving moduli. -/
  deep : ∀ ctx : ActualFailureContext,
    1 ≤ ctx.n24CarryData.r →
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅

/-- The wave-2 emptiness field trivially provides the wave-3 residual (it is strictly
weaker). -/
theorem class1DeepResidual_of_fibreEmpty
    (h : ∀ ctx : ActualFailureContext,
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅) :
    Class1DeepResidual := by
  refine ⟨fun ctx _ _ _ _ _ => ?_, fun ctx _ _ _ _ _ => h ctx⟩
  rw [h ctx]
  exact Finset.notMem_empty _

/-- **The capstone bridge**: the wave-3 residual discharges the capstone field
`class1Pinned` EXACTLY (same statement, same hypotheses). -/
theorem class1Pinned_of_deepResidual (R : Class1DeepResidual) :
    ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      1 ≤ k →
      64 ∣ shellLadderDepth ctx →
      9 ≤ (class1SlopeDatum ctx).q →
      ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
      Odd (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) →
      64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          = 129 * shellLadderDepth ctx + 64 →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) ≠ 4 := by
  intro ctx k hk h1 hdvd h9 hwin hodd hgw hband
  have hmem : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
    (mem_class1Fibre_iff ctx k).mpr ⟨hk, hgw, hband⟩
  by_cases hclosed : (class1SlopeDatum ctx).q ∈ class1ClosedModuli
  · rw [class1Fibre_empty_of_mem_closedModuli ctx hclosed] at hmem
    exact Finset.notMem_empty k hmem
  · rcases Nat.eq_zero_or_pos ctx.n24CarryData.r with hr | hr
    · have htop := class1Fibre_top_of_r_eq_zero ctx hr hmem
      have hkeq : k = cnlWindowTopStart ctx := by
        unfold cnlWindowTopStart
        omega
      rw [hkeq] at hmem
      exact R.topStart ctx hr hdvd h9 hwin hclosed hmem
    · rw [R.deep ctx hr hdvd h9 hwin hclosed] at hmem
      exact Finset.notMem_empty k hmem

/-- **The full-chain entry**: the wave-3 residual closes the v3 clean-CNL atom through the
wave-2 sharp pinned-arithmetic bridge — nothing else is needed. -/
theorem class1FibreEmpty_of_deepResidual
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (R : Class1DeepResidual) :
    Class1FibreEmpty (v3Budget towerCount runChain returnCharge) :=
  class1FibreEmpty_of_pinned_arithmetic_sharp towerCount runChain returnCharge
    (class1Pinned_of_deepResidual R)

/-! ## Part 9.  Machine-readable status (brutally honest) -/

/-- Honest machine-readable status of the wave-3 class-1 deep-closure attempt.  This list
refines (and should be read after) `cnlClass1ClosureStatus`. -/
def cnlClass1DeepClosureStatus : List String :=
  [ "TARGET (capstone field): class1Pinned - refute canonGap q K_k = 4 at the exact pin " ++
      "64*gapWindow = 129L+64 given 1 <= k, 64 | L, 9 <= q, (q <= 15 or 25 <= q), Odd K_k.",
    "CLOSED (spacing-is-period rigidity, NEW): two class-1 starts with EQUAL orbit " ++
      "numerators make their spacing a PERIOD of the orbit valid from index 1 " ++
      "(slopeOrbit_spacing_period via slopeOrbit_cancel + slopeOrbit_eq_shift; fibre form " ++
      "class1Fibre_spacing_period; q <= 15 form class1Fibre_spacing_period_of_modulus_le_15 " ++
      "since K_k = 1 there).",
    "CLOSED (the 25 <= q <= 39 numerator pin, NEW): every class-1 start on that window has " ++
      "K_k = 3 EXACTLY (class1Fibre_orbit_eq_three_of_modulus_window) - the band-4 odd " ++
      "window (q/16, q/8] pins K uniquely, the companion of the q <= 15 pin K_k = 1.",
    "CLOSED (the residue pin, NEW): periods are closed under difference and mod " ++
      "(slopeOrbit_period_sub, slopeOrbit_period_mod), every period is a multiple of a " ++
      "minimal one (slopeOrbit_minimalPeriod_dvd), hence equal-numerator class-1 starts are " ++
      "congruent mod any minimal period (class1Fibre_residue_pin) - on q <= 15 ALL class-1 " ++
      "starts lie in ONE residue class mod c (class1Fibre_residue_pin_of_modulus_le_15).",
    "CLOSED (telescope rigidity, NEW): all class-1 starts share the exact span (129L+64)/64, " ++
      "so a(k+r+1) + a(k') = a(k'+r+1) + a(k) for any two (class1Fibre_span_rigidity) and " ++
      "the k'-k gaps entering the window equal the k'-k gaps leaving it " ++
      "(class1Fibre_flank_sum_eq) - the repeat-increment rigidity across c-spaced starts.",
    "CLOSED (adjacency obstruction, NEW): adjacent class-1 starts with equal numerators " ++
      "force q = 15*K_k (class1Fibre_adjacent_modulus_eq); on q <= 15 this forces q = 15 " ++
      "(class1Fibre_adjacent_forces_q15_of_le15), on 25 <= q <= 39 it is IMPOSSIBLE " ++
      "(class1Fibre_no_adjacent_of_modulus_window, would force q = 45).",
    "CLOSED (gated |fibre1| <= 1 extension, NEW): under the gate 64(r+1)(L+B+1) < 129L+64 " ++
      "(forcing r <= 1) every shell with q <= 13 or 25 <= q <= 39 has at most ONE class-1 " ++
      "start (class1Fibre_card_le_one_of_gate_modulus) - extends the wave-2 r = 0 bound; " ++
      "the q = 15 fixed point remains the lone gated multi-start candidate.",
    "CLOSED (r = 0 top-start pin, NEW): the r = 0 fibre is INSIDE the singleton " ++
      "{cnlWindowTopStart ctx} (class1Fibre_subset_top_of_r_eq_zero), and r >= 1 forces " ++
      "L >= 15421 (n24_L_ge_of_r_pos) - so the r = 0 residual is a SINGLE per-ctx start fact.",
    "CLOSED (odd-modulus cycle tail, NEW): per-modulus emptiness for q in {27, 31, 33, 43, " ++
      "45, 51, 65, 85, 91, 93} (class1Fibre_empty_of_modulus_eq_27 ... _93, dispatched by " ++
      "class1Fibre_empty_of_mem_closedModuli over class1ClosedModuli; v3 form " ++
      "v3_class1Fibre_empty_of_mem_closedModuli): every admissible K0 (2K0+1 | q) has an " ++
      "explicitly computed band-4-free cycle fed to class1Fibre_empty_of_cycle_band_free " ++
      "through the collision closer class1Fibre_empty_of_orbit_collision; plus the " ++
      "(q, K0) = (15, 7) family (class1Fibre_empty_of_q15_K07).",
    "AUDIT (honest negative, cycle side): the moduli 25, 29, 35, 37, 39, 41, 47, 49, 53, " ++
      "55, 57, 59, 61, 63, 67, 69, 71, 73, 75, 77, 79, 81, 83, 87, 89, 95, 97, 99 have a " ++
      "band-4 odd numerator ON the cycle of at least one admissible K0 (e.g. q = 25: K = 3 " ++
      "on the 10-cycle of K0 = 2 and 12; q = 15, K0 in {1, 2}: the all-band-4 fixed point " ++
      "K = 1), so NO cycle-check closure exists for them - their refutation must come from " ++
      "the digit side.",
    "AUDIT (honest negative, count side): |fibre1| <= 1 is NOT provable unconditionally on " ++
      "ungated r >= 1 shells - the digit side is unconstrained, and a hit sequence whose " ++
      "increments repeat along one residue class realizes many simultaneous exact pins; " ++
      "the rigidity lemmas above are exactly the surviving content.",
    "RESIDUAL (strictly smaller than wave 2): Class1DeepResidual - field topStart: on " ++
      "r = 0 shells (ALL L <= 15420) the SINGLE top window start is not class-1; field " ++
      "deep: on r >= 1 shells (L >= 15421) emptiness, only for moduli q in {9, 11, 13, 15, " ++
      "25, 29, 35, 37, 39, ...} \\ class1ClosedModuli with 64 | L.  Bridge " ++
      "class1Pinned_of_deepResidual produces the capstone field class1Pinned EXACTLY; " ++
      "full-chain entry class1FibreEmpty_of_deepResidual; weakness witness " ++
      "class1DeepResidual_of_fibreEmpty.",
    "NOT CLOSED (the honest wave-3 residual): shells with 64 | L whose modulus survives " ++
      "(q in {9, 11, 13, 15} union {25, 29, 35, 37, 39, 41, 47, ...} minus the closed " ++
      "lists), where on r = 0 the unique top start - and on r >= 1 some window start with " ++
      "odd K_k on a band-4 cycle index - realizes the exact pin 64*gapWindow = 129L+64.  " ++
      "The digit-side pin and the orbit-side pin remain coupled only through the shared " ++
      "index k; no formalized bridge ties them for the actual ctx.  We do NOT claim " ++
      "unconditional closure of the atom." ]

theorem cnlClass1DeepClosureStatus_nonempty : cnlClass1DeepClosureStatus ≠ [] := by
  simp [cnlClass1DeepClosureStatus]

/-! ## Part 10.  Axiom-cleanliness audit -/

#print axioms canonGap_eval
#print axioms slopeOrbit_step_eval
#print axioms canonGap_ne_four_of_band
#print axioms slopeOrbit_spacing_period
#print axioms slopeOrbit_period_sub
#print axioms slopeOrbit_period_mod
#print axioms slopeOrbit_minimalPeriod_dvd
#print axioms class1Fibre_spacing_period
#print axioms class1Fibre_orbit_eq_three_of_modulus_window
#print axioms class1Fibre_spacing_period_of_modulus_le_15
#print axioms class1Fibre_residue_pin
#print axioms class1Fibre_residue_pin_of_modulus_le_15
#print axioms class1Fibre_span_rigidity
#print axioms class1Fibre_flank_sum_eq
#print axioms class1Fibre_adjacent_modulus_eq
#print axioms class1Fibre_adjacent_forces_q15_of_le15
#print axioms class1Fibre_no_adjacent_of_modulus_window
#print axioms class1Fibre_card_le_one_of_gate_modulus
#print axioms class1Fibre_subset_top_of_r_eq_zero
#print axioms n24_L_ge_of_r_pos
#print axioms class1Fibre_empty_of_orbit_collision
#print axioms class1Fibre_empty_of_q15_K₀7
#print axioms class1Fibre_empty_of_modulus_eq_27
#print axioms class1Fibre_empty_of_modulus_eq_31
#print axioms class1Fibre_empty_of_modulus_eq_33
#print axioms class1Fibre_empty_of_modulus_eq_43
#print axioms class1Fibre_empty_of_modulus_eq_45
#print axioms class1Fibre_empty_of_modulus_eq_51
#print axioms class1Fibre_empty_of_modulus_eq_65
#print axioms class1Fibre_empty_of_modulus_eq_85
#print axioms class1Fibre_empty_of_modulus_eq_91
#print axioms class1Fibre_empty_of_modulus_eq_93
#print axioms class1Fibre_empty_of_mem_closedModuli
#print axioms v3_class1Fibre_empty_of_mem_closedModuli
#print axioms class1DeepResidual_of_fibreEmpty
#print axioms class1Pinned_of_deepResidual
#print axioms class1FibreEmpty_of_deepResidual
#print axioms cnlClass1DeepClosureStatus_nonempty

end

end Erdos260
