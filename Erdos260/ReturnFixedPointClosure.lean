import Erdos260.DensePackFixedPointClosure

/-!
# Return / class-4 band-2 fixed-point closure — the datum lever transplanted to band 2

This module (NEW; it edits no existing file) attacks the band-2 lane of the wave-3 capstone
`Erdos260CycleResidual` (`returnGates`, `returnZero`, `returnMaxClean`, `returnInterior`) with the
wave-4 central lever already used for band 3 in `DensePackFixedPointClosure.lean`: the orbit datum
`(q, K₀) = class1SlopeDatum ctx` carries the proved pins

* `class1SlopeDatum_q_eq`  : `q = oddpart(Q · (2|P| + 1))`,
* `class1SlopeDatum_K₀_eq` : `K₀ = |P|`,
* `class1SlopeDatum_H_dvd` : the divisor pin `(2K₀ + 1) ∣ q`,

so the band-2 fixed-point family collapses to ONE explicit `(q, K₀)` pair.  Everything below is
proved from the routing/orbit/datum arithmetic of the canonical objects — no fabricated witnesses,
no new axioms, no `sorry`/`admit`/`native_decide`.

A band-2 fixed point of the E.13 step is a numerator `K` with `q = 3K`: then `canonGap (3K) K = 2`
and `2²·K − 3K = K` (`canonGap_three_mul`, `boundedSlopeStep_three_mul`, `slopeOrbit_three_mul`,
already proved in `ReturnClass4Closure.lean`).  This is the exact band-2 analogue of band 3's
`7F = q` and band 4's `15·K₁ = q`.

## What is newly closed here (all unconditional)

* **The band-2 fixed-point datum confinement** (`band2_fixedHit_pins`,
  `returnClass4FixedHit_datum`, `returnClass4FixedHit_iff_datum`): if the actual datum's orbit hits
  a band-2 fixed point `3F = q` at ANY index `j ≥ 1` (a fixed base `3K₀ = q` propagates to index 1,
  `returnClass4FixedHit_of_base`), then backward determinism pins `K₁ = F`
  (`slopeOrbit_one_eq_of_hits_fixed`), the base step pins `3·2^{g₀}·K₀ = 4q`, and the divisor pin
  `(2K₀+1) ∣ q` forces `(2K₀+1) ∣ 3·2^{g₀}`, hence `2K₀+1 = 3`, `K₀ = 1`, and `3·2^{g₀} = 4q` with
  `q` odd gives `g₀ = 2`, `q = 3`: **`(q, K₀) = (3, 1)` exactly** — necessary AND sufficient
  (`canonGap 3 1 = 2`, `2²·1 − 3 = 1`, the orbit is constantly `1`).
* **The all-band-2 cycle rigidity** (`band2_full_orbit_forces_fixed`,
  `band2_full_cycle_forces_fixed`, `band2_full_cycle_three_dvd`): a period whose EVERY reading is
  band 2 forces the exact `1/3` fixed point `3·K₁ = q` (deviations `3K − q` QUADRUPLE along band-2
  steps and the run bound `2·4^{s−1} ≤ q` cannot hold for `s = q+1`), hence `3 ∣ q` — the band-2
  mirror of `band3_full_cycle_seven_dvd` / `towerCycle_band4_full_fifteen_dvd`.
* **`b₂ < c` off the fixed point** (`band2CycleCount_lt_of_not_fixed`, datum form
  `datum_band2CycleCount_lt_of_offFixed`): on every actual context with `(q, K₀) ≠ (3, 1)`, EVERY
  orbit period has band-2 count strictly below the period — band-2 cycle density `1` happens ONLY on
  the confined `(3, 1)` family.  Off the datum the cycle-count count carries the strict factor and
  feeds the fibre bound (`olcFibre_card_le_offFixed`).
* **The cycle-count route to the capstone count field** (`class4FibreSmall_of_cycleCount`): a per-ctx
  cycle-count witness `t·b₂ ≤ r + 1` (with `K ≤ t·c`) discharges `Class4FibreSmall` through the
  existing four-way gate bridge `class4FibreSmall_of_gates`.
* **The `(3, 1)` survivor characterized exactly**: the orbit is constantly `1`
  (`slopeOrbit_three_one_const`), every residue reads band 2 (`datum_canonGap_orbit_two_of_datum`),
  the shell denominator has odd part EXACTLY `1` (`return_datum_Q_oddPart`: `Q = 2^t`,
  `return_datum_Q_eq`), the chosen carry numerator is `P = 1`, and therefore **the Erdős weighted
  value is exactly a dyadic reciprocal** `Σ n·dₙ/2ⁿ = 1/2^t` (`return_datum_value_eq`,
  `returnClass4FixedHit_value_eq`).  This is the complete `Q`-arithmetic the model pins at this layer
  (the shell carries only `0 < Q`); the family is NOT refuted here — recorded honestly as THE unique
  surviving band-2 fixed pair, with its value forced dyadic, exactly mirroring band 3's `(21, 3)`.

## The honest residual after this module

Goal 2 (interior) and goal 3 (digit fields) DO NOT close on the `(3, 1)` family: there the orbit is
constantly band 2, so the interior top-band cycle check (`class4Interior_of_cycle_topBand_check`)
cannot fire — `datum_canonGap_orbit_two_of_datum` shows every top-band residue reads band 2 — and the
gap-floor lives on the model-unconstrained escape gap (the returnGates 4th disjunct is vacuous there,
`b₂ = c`).  For the digit fields, the M.2.1 self-referential congruence gives only SPACING: a
same-slice class-4 pair `x < z` forces `2^{carryVal2 x} < K`
(`returnSelfRef_sliceModulus_lt_width_of_pair`), so the `carryVal2 ≥ log₂ K` regime makes `returnZero`
a theorem (the existing `returnDigit_hzero_of_carryVal2_large`, re-contextualized) and shrinks
`returnMaxClean`, while the complementary `carryVal2 < log₂ K` regime genuinely resists — no
formalized bridge ties the digit-side gap floor to the orbit-side band beyond the shared index, and
we do NOT prove any context empty.

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The band-2 fixed point at the actual datum: generic arithmetic

A band-2 fixed point of the E.13 step is a numerator `F` with `3F = q`: then `canonGap q F = 2`,
`2²·F − q = F`, and the orbit is constant.  At `(q, F) = (3, 1)` this is the concrete surviving
family.  The base arithmetic (`canonGap_three_mul`, `boundedSlopeStep_three_mul`,
`slopeOrbit_three_mul`, `canonGap_orbit_three`) is already proved in `ReturnClass4Closure.lean`. -/

/-- A `1/3` numerator reads band 2: `3F = q` gives `canonGap q F = 2`. -/
theorem canonGap_of_three_mul {q F : ℕ} (hF : 1 ≤ F) (h3 : 3 * F = q) :
    canonGap q F = 2 := by
  rw [← h3]; exact canonGap_three_mul hF

/-- A `1/3` numerator is a FIXED POINT of the E.13 step: `2²·F − q = F`. -/
theorem boundedSlopeStep_of_three_mul {q F : ℕ} (hF : 1 ≤ F) (h3 : 3 * F = q) :
    boundedSlopeStep q F = F := by
  rw [← h3]; exact boundedSlopeStep_three_mul hF

/-- **The `(3, 1)` orbit is CONSTANT**: `K_j = 1` at every index (including the base).
(`canonGap 3 1 = 2` is the upstream `canonGap_three_one` of `RunClass5Routing`.) -/
theorem slopeOrbit_three_one_const : ∀ j, slopeOrbit 3 1 j = 1 := by
  intro j; simpa using slopeOrbit_three_mul (K := 1) le_rfl j

/-! ## Part 2.  The datum confinement: every band-2 fixed-point hit forces `(q, K₀) = (3, 1)`

The wave-4 lever, transplanted from band 3.  A hit at index `j ≥ 1` propagates back to `K₁ = F`
(`slopeOrbit_one_eq_of_hits_fixed`), the base step pins `2^{g₀}·K₀ = q + F`, so `3·2^{g₀}·K₀ = 4q`;
the divisor pin `(2K₀+1) ∣ q` then gives `(2K₀+1) ∣ 3·2^{g₀}·(2K₀+1) − 2·(3·2^{g₀}·K₀) = 3·2^{g₀}`,
and coprimality leaves `2K₀+1 = 3`.  Back-substituting, `3·2^{g₀} = 4q` with `q` odd forces `g₀ = 2`,
`q = 3`. -/

/-- **The generic band-2 fixed-point pin extraction** (pure orbit/datum arithmetic): an odd modulus
with the divisor pin `(2K₀+1) ∣ q` whose orbit hits a band-2 fixed point `3F = q` at any index
`j ≥ 1` must have `(q, K₀) = (3, 1)`. -/
theorem band2_fixedHit_pins {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀) (hKq : K₀ < q)
    (hdvd : 2 * K₀ + 1 ∣ q) {j : ℕ} (hj : 1 ≤ j)
    (h3 : 3 * slopeOrbit q K₀ j = q) :
    q = 3 ∧ K₀ = 1 := by
  -- the hit propagates back to index 1
  have hmemj := slopeOrbit_mem hq hK1 hKq j
  have hfixj : boundedSlopeStep q (slopeOrbit q K₀ j) = slopeOrbit q K₀ j :=
    boundedSlopeStep_of_three_mul hmemj.1 h3
  have h1 := slopeOrbit_one_eq_of_hits_fixed hq hK1 hKq hj hfixj
  have h31 : 3 * slopeOrbit q K₀ 1 = q := by rw [h1]; exact h3
  -- the base-step equation: 3·2^{g₀}·K₀ = 4q
  have hstep : slopeOrbit q K₀ 1 = boundedSlopeStep q K₀ := rfl
  have hbound := (canonGap_bounds hq hK1 hKq).1
  obtain ⟨g, hg⟩ : ∃ g, canonGap q K₀ = g := ⟨_, rfl⟩
  rw [hg] at hbound
  unfold boundedSlopeStep at hstep
  rw [hg] at hstep
  have hkey : 3 * (2 ^ g * K₀) = 4 * q := by omega
  -- the divisor pin forces 2K₀+1 = 3
  have hdvd8 : (2 * K₀ + 1) ∣ 8 * q := hdvd.mul_left 8
  have hexp : 3 * 2 ^ g * (2 * K₀ + 1) = 8 * q + 3 * 2 ^ g := by
    calc 3 * 2 ^ g * (2 * K₀ + 1) = 2 * (3 * (2 ^ g * K₀)) + 3 * 2 ^ g := by ring
      _ = 2 * (4 * q) + 3 * 2 ^ g := by rw [hkey]
      _ = 8 * q + 3 * 2 ^ g := by ring
  have hdvd3g : (2 * K₀ + 1) ∣ 3 * 2 ^ g := by
    have hL : (2 * K₀ + 1) ∣ 3 * 2 ^ g * (2 * K₀ + 1) := dvd_mul_left _ _
    rw [hexp] at hL
    have hsub := Nat.dvd_sub hL hdvd8
    rwa [Nat.add_sub_cancel_left] at hsub
  have hcop : Nat.Coprime (2 * K₀ + 1) (2 ^ g) :=
    Nat.Coprime.pow_right g (Nat.coprime_two_right.mpr ⟨K₀, by ring⟩)
  have hdvd3 : (2 * K₀ + 1) ∣ 3 := hcop.dvd_of_dvd_mul_right hdvd3g
  have hK1' : K₀ = 1 := by
    rcases (by norm_num : Nat.Prime 3).eq_one_or_self_of_dvd _ hdvd3 with h | h <;> omega
  refine ⟨?_, hK1'⟩
  -- 3·2^{g₀} = 4q with q odd forces q = 3
  rw [hK1', mul_one] at hkey
  obtain ⟨m, hm⟩ := hq
  rcases Nat.lt_or_ge g 2 with hg2 | hg2
  · have h2g : (2 : ℕ) ^ g = 1 ∨ (2 : ℕ) ^ g = 2 := by
      rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
      · left; rw [pow_zero]
      · right; rw [pow_one]
    rcases h2g with h | h <;> rw [h] at hkey <;> omega
  · obtain ⟨s, rfl⟩ : ∃ s, g = 2 + s := ⟨g - 2, by omega⟩
    have hpow : (2 : ℕ) ^ (2 + s) = 4 * 2 ^ s := by
      rw [pow_add]; norm_num
    rw [hpow] at hkey
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · rw [pow_zero] at hkey
      omega
    · obtain ⟨t, ht⟩ := (dvd_pow_self 2 (by omega : s ≠ 0) : (2 : ℕ) ∣ 2 ^ s)
      rw [ht] at hkey
      omega

/-- **The named per-ctx band-2 fixed-point hit**: the actual datum's orbit reads a band-2 fixed
point `3F = q` at some positive index. -/
def ReturnClass4FixedHit (ctx : ActualFailureContext) : Prop :=
  ∃ j, 1 ≤ j
    ∧ 3 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j
        = (class1SlopeDatum ctx).q

/-- **THE DATUM CONFINEMENT**: a band-2 fixed-point hit at the actual datum forces
`(q, K₀) = (3, 1)` exactly — the divisor pin `(2K₀+1) ∣ q` (from `class1SlopeDatum_H_dvd` and
`class1SlopeDatum_K₀_eq`) admits no other solution. -/
theorem returnClass4FixedHit_datum (ctx : ActualFailureContext) (h : ReturnClass4FixedHit ctx) :
    (class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1 := by
  obtain ⟨j, hj, h3⟩ := h
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    have hH := class1SlopeDatum_H_dvd ctx
    rwa [← class1SlopeDatum_K₀_eq ctx] at hH
  exact band2_fixedHit_pins (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt hdvd hj h3

/-- The converse: at `(q, K₀) = (3, 1)` the hit is immediate (`K₁ = 1`, `3·1 = 3`). -/
theorem returnClass4FixedHit_of_datum (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 3) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ReturnClass4FixedHit ctx := by
  refine ⟨1, le_rfl, ?_⟩
  rw [hq, hK, slopeOrbit_three_one_const 1]

/-- **The exact fixed-point characterization at the actual datum**: the orbit hits a band-2 fixed
point IFF `(q, K₀) = (3, 1)`. -/
theorem returnClass4FixedHit_iff_datum (ctx : ActualFailureContext) :
    ReturnClass4FixedHit ctx
      ↔ (class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1 :=
  ⟨returnClass4FixedHit_datum ctx, fun ⟨hq, hK⟩ => returnClass4FixedHit_of_datum ctx hq hK⟩

/-- **The tail is captured**: a fixed BASE numerator (`3·K₀ = q` at index `0`) propagates to index
`1`, so it is a `ReturnClass4FixedHit` and the confinement applies to it as well. -/
theorem returnClass4FixedHit_of_base (ctx : ActualFailureContext)
    (h : 3 * (class1SlopeDatum ctx).K₀ = (class1SlopeDatum ctx).q) :
    ReturnClass4FixedHit ctx := by
  refine ⟨1, le_rfl, ?_⟩
  have hfix : boundedSlopeStep (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
      = (class1SlopeDatum ctx).K₀ :=
    boundedSlopeStep_of_three_mul (class1SlopeDatum ctx).hK₀_pos h
  have h1 : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1
      = boundedSlopeStep (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ := rfl
  rw [h1, hfix]; exact h

/-! ## Part 3.  The all-band-2 cycle rigidity and `b₂ < c` off the fixed point

Along a band-2 step the deviation `3K − q` multiplies by `4`; on a band-2-full orbit the run bound
`2·4^{s−1} ≤ q` of `band2_run_forces_three_mul_or_pow_le` cannot hold for `s = q+1`
(`q < 2^q ≤ 4^q`), so the orbit sits on the `1/3` fixed point `3K₁ = q`. -/

/-- **A band-2-full orbit forces the exact `1/3` fixed point**: if EVERY positive index reads band
2, then `3·K₁ = q`. -/
theorem band2_full_orbit_forces_fixed {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀) (hKq : K₀ < q)
    (hall : ∀ j, 1 ≤ j → canonGap q (slopeOrbit q K₀ j) = 2) :
    3 * slopeOrbit q K₀ 1 = q := by
  rcases band2_run_forces_three_mul_or_pow_le hq hK1 hKq 1 (q + 1) (by omega)
    (fun t ht => hall (1 + t) (by omega)) with h | h
  · exact h
  · exfalso
    have h1 : q < 2 ^ q := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ q ≤ 4 ^ q := Nat.pow_le_pow_left (by norm_num) q
    simp only [Nat.add_sub_cancel] at h
    omega

/-- **A band-2-full period forces the fixed point** (mod-period reduction): `3·K₁ = q`. -/
theorem band2_full_cycle_forces_fixed {q K₀ c : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀)
    (hKq : K₀ < q) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    (hall : ∀ j, 1 ≤ j → j ≤ c → canonGap q (slopeOrbit q K₀ j) = 2) :
    3 * slopeOrbit q K₀ 1 = q := by
  apply band2_full_orbit_forces_fixed hq hK1 hKq
  intro j hj
  rw [slopeOrbit_eq_mod_period hc hper hj]
  refine hall (1 + (j - 1) % c) (by omega) ?_
  have := Nat.mod_lt (j - 1) (show 0 < c by omega)
  omega

/-- A band-2-full period forces `3 ∣ q` — band-2 cycle density `1` lives ONLY on the `3 ∣ q`
fixed-point family (the band-2 mirror of `band3_full_cycle_seven_dvd`). -/
theorem band2_full_cycle_three_dvd {q K₀ c : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀)
    (hKq : K₀ < q) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    (hall : ∀ j, 1 ≤ j → j ≤ c → canonGap q (slopeOrbit q K₀ j) = 2) :
    3 ∣ q :=
  ⟨slopeOrbit q K₀ 1, (band2_full_cycle_forces_fixed hq hK1 hKq hc hper hall).symm⟩

/-- **The per-period band-2 count** (the `Icc`-form mirror of `band3CycleCount`). -/
def band2CycleCount (q K₀ c : ℕ) : ℕ :=
  ((Finset.Icc 1 c).filter (fun j => canonGap q (slopeOrbit q K₀ j) = 2)).card

/-- The band-2 count never exceeds the period. -/
theorem band2CycleCount_le (q K₀ c : ℕ) : band2CycleCount q K₀ c ≤ c := by
  unfold band2CycleCount
  calc ((Finset.Icc 1 c).filter (fun j => canonGap q (slopeOrbit q K₀ j) = 2)).card
      ≤ (Finset.Icc 1 c).card := Finset.card_filter_le _ _
    _ = c := by rw [Nat.card_Icc]; omega

/-- **Off the fixed point the band-2 cycle count is strictly below the period**:
`3·K₁ ≠ q → b₂(q, K₀, c) < c` for every period `c` — the band-2 mirror of
`band3CycleCount_lt_of_not_fixed` / `towerBand4CycleCount_lt_of_not_fixed`. -/
theorem band2CycleCount_lt_of_not_fixed {q K₀ c : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀)
    (hKq : K₀ < q) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    (hnf : 3 * slopeOrbit q K₀ 1 ≠ q) :
    band2CycleCount q K₀ c < c := by
  rcases Nat.lt_or_ge (band2CycleCount q K₀ c) c with h | h
  · exact h
  · exfalso
    have hcard : (Finset.Icc 1 c).card = c := by rw [Nat.card_Icc]; omega
    have heq : ((Finset.Icc 1 c).filter (fun j => canonGap q (slopeOrbit q K₀ j) = 2))
        = Finset.Icc 1 c := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      rw [hcard]
      exact h
    have hall : ∀ j, 1 ≤ j → j ≤ c → canonGap q (slopeOrbit q K₀ j) = 2 := by
      intro j h1 h2
      have hjmem : j ∈ (Finset.Icc 1 c).filter
          (fun j => canonGap q (slopeOrbit q K₀ j) = 2) := by
        rw [heq, Finset.mem_Icc]
        exact ⟨h1, h2⟩
      exact (Finset.mem_filter.mp hjmem).2
    exact hnf (band2_full_cycle_forces_fixed hq hK1 hKq hc hper hall)

/-! ## Part 4.  Datum forms: the off-`(3, 1)` strict count and the fixed-point block -/

/-- **An all-band-2 period at the actual datum forces `(q, K₀) = (3, 1)`** — the band-2 constant
cycle reachable from the actual datum, confined via the cycle rigidity and the divisor pin. -/
theorem returnClass4CycleBand2Full_datum (ctx : ActualFailureContext) {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hall : ∀ j, 1 ≤ j → j ≤ c → canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2) :
    (class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1 :=
  returnClass4FixedHit_datum ctx
    ⟨1, le_rfl, band2_full_cycle_forces_fixed (class1SlopeDatum ctx).hq_odd
      (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum ctx).hK₀_lt hc hper hall⟩

/-- **Off the confined pair the band-2 residue count is strictly below EVERY period**: on an
actual context with `(q, K₀) ≠ (3, 1)`, band-2 cycle density `1` is impossible. -/
theorem datum_band2CycleCount_lt_of_offFixed (ctx : ActualFailureContext)
    (hoff : ¬((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1))
    {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) :
    band2CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c < c := by
  apply band2CycleCount_lt_of_not_fixed (class1SlopeDatum ctx).hq_odd
    (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum ctx).hK₀_lt hc hper
  intro hfix
  exact hoff (returnClass4FixedHit_datum ctx ⟨1, le_rfl, hfix⟩)

/-- **The off-fixed fibre bound**: away from `(3, 1)`, with any period `c` and `K ≤ t·c`, the
class-4 fibre population is `≤ t·b₂` AND the cycle band-2 count is strictly deficient — the
quantitative "class-4 starts occupy at most `⌈K/c⌉·b₂` window positions" statement off the family. -/
theorem olcFibre_card_le_offFixed (ctx : ActualFailureContext)
    (hoff : ¬((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1))
    {c t : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hcover : (supportShell ctx.shell.d ctx.shell.X).card ≤ t * c) :
    (olcFibre ctx).card
        ≤ t * band2CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c
      ∧ band2CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c < c :=
  ⟨class4Fibre_card_le_cycle_count ctx hc hper hcover,
    datum_band2CycleCount_lt_of_offFixed ctx hoff hc hper⟩

/-! ## Part 5.  The cycle-count route to the capstone count field -/

/-- **The cycle-count route to `Class4FibreSmall`**: a per-ctx band-2 cycle-count witness
`t·b₂ ≤ r + 1` (with a period `c` and `K ≤ t·c`) discharges the capstone count field through the
existing four-way gate bridge `class4FibreSmall_of_gates` (it lands in its 4th disjunct).  This is
the additive bridge from the datum analysis above into the `returnGates` slot of
`Erdos260CycleResidual`. -/
theorem class4FibreSmall_of_cycleCount
    (H : ∀ ctx : ActualFailureContext, ∃ c t : ℕ, 1 ≤ c
        ∧ (∀ m, 1 ≤ m →
            slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
              = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
        ∧ (supportShell ctx.shell.d ctx.shell.X).card ≤ t * c
        ∧ t * band2CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c
            ≤ ctx.n24CarryData.r + 1) :
    Class4FibreSmall :=
  class4FibreSmall_of_gates (fun ctx => Or.inr (Or.inr (Or.inr (H ctx))))

/-! ## Part 6.  The `(3, 1)` survivor characterized — orbit, the fixed-point block, and the forced
dyadic value

`(q, K₀) = (3, 1)` is THE unique band-2 fixed pair compatible with the datum.  There the orbit is
constantly `1`, every residue reads band 2, and the datum arithmetic pins the shell:
`oddpart(Q) = 1` (`Q = 2^t`) and the Erdős weighted value is EXACTLY `1/2^t`. -/

/-- At the `(3, 1)` datum every orbit residue reads band 2 — so the interior top-band cycle check
(`class4Interior_of_cycle_topBand_check`) cannot fire there: the honest obstruction, relocated from
band 3's `(21, 3)`. -/
theorem datum_canonGap_orbit_two_of_datum (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 3) (hK : (class1SlopeDatum ctx).K₀ = 1) (j : ℕ) :
    canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 := by
  rw [hq, hK]; exact canonGap_orbit_three j

/-- **The survivor's denominator pin**: on the `(3, 1)` family the shell denominator has odd part
EXACTLY `1` (`3 = oddpart(Q · 3)` with `K₀ = |P| = 1`), i.e. `Q` is a power of two. -/
theorem return_datum_Q_oddPart (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 3) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ordCompl[2] ctx.shell.Q = 1 := by
  have habs : ctx.shell.hrational.choose.natAbs = 1 := by
    rw [← class1SlopeDatum_K₀_eq ctx]
    exact hK
  have hqe := class1SlopeDatum_q_eq ctx
  rw [habs] at hqe
  rw [hq] at hqe
  have h3 : (2 * 1 + 1 : ℕ) = 3 := by norm_num
  rw [h3] at hqe
  have hcompl : apOddModulus ctx.shell.Q 3 = ordCompl[2] ctx.shell.Q * 3 := by
    show ordCompl[2] (ctx.shell.Q * 3) = _
    exact ordCompl_two_mul_odd ctx.shell.hQ.ne' ⟨1, by norm_num⟩
  rw [hcompl] at hqe
  omega

/-- **The survivor's denominator shape**: `Q = 2^t`. -/
theorem return_datum_Q_eq (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 3) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ∃ t : ℕ, ctx.shell.Q = 2 ^ t := by
  refine ⟨ctx.shell.Q.factorization 2, ?_⟩
  have h1 := return_datum_Q_oddPart ctx hq hK
  have hself := Nat.ordProj_mul_ordCompl_eq_self ctx.shell.Q 2
  rw [h1] at hself
  omega

/-- **THE VALUE PIN OF THE SURVIVING FAMILY**: on the `(3, 1)` family the chosen carry numerator is
`P = 1` and `Q = 2^t`, so the Erdős weighted value is EXACTLY the dyadic reciprocal
`Σ n·dₙ/2ⁿ = 1/2^t` — the complete datum arithmetic of the unique surviving band-2 fixed pair
(recorded honestly; the model pins nothing more on `Q` at this layer). -/
theorem return_datum_value_eq (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 3) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ∃ t : ℕ, ctx.shell.Q = 2 ^ t
      ∧ realWeightedValue (natBinaryAsReal ctx.shell.d) = 1 / 2 ^ t := by
  obtain ⟨t, hQ⟩ := return_datum_Q_eq ctx hq hK
  refine ⟨t, hQ, ?_⟩
  have hspec := ctx.shell.hrational.choose_spec
  have hP1 : ctx.shell.hrational.choose = 1 := by
    have hpos : 0 < ctx.shell.hrational.choose :=
      failingShell_carry_pos ctx.shell _ hspec
    have habs : ctx.shell.hrational.choose.natAbs = 1 := by
      rw [← class1SlopeDatum_K₀_eq ctx]
      exact hK
    omega
  rw [hspec, hP1, hQ]
  push_cast
  ring

/-- The fixed-hit form of the survivor value pin (composed through the confinement). -/
theorem returnClass4FixedHit_value_eq (ctx : ActualFailureContext)
    (h : ReturnClass4FixedHit ctx) :
    ∃ t : ℕ, ctx.shell.Q = 2 ^ t
      ∧ realWeightedValue (natBinaryAsReal ctx.shell.d) = 1 / 2 ^ t := by
  obtain ⟨hq, hK⟩ := returnClass4FixedHit_datum ctx h
  exact return_datum_value_eq ctx hq hK

/-! ## Part 7.  The digit fields — the spacing boundary and its honest outcome

The M.2.1 self-referential congruence (`returnSelfRefKey_gapDiv`) yields SPACING `2^{v₂} ∣ z − x`,
and the window pins confine same-slice pairs to `z − x < K`.  Hence a same-slice class-4 pair forces
`2^{carryVal2 x} < K`: the EXACT boundary of the obstruction.  In the `carryVal2 ≥ log₂ K` regime
the slices are singletons and `returnZero` holds vacuously (the existing
`returnDigit_hzero_of_carryVal2_large`); the complementary `carryVal2 < log₂ K` regime resists. -/

/-- **The spacing boundary**: a same-key class-4 pair `x < z` forces `2^{carryVal2 x} < K` — the
slice modulus is strictly below the window width.  Contrapositive of
`returnSelfRef_pair_false_of_carryVal2_large`: the `carryVal2 ≥ log₂ K` regime cannot host a
same-slice pair, so there the `(Z)` zero-run field holds vacuously. -/
theorem returnSelfRef_sliceModulus_lt_width_of_pair (ctx : ActualFailureContext) {x z : ℕ}
    (hx : x ∈ olcFibre ctx) (hz : z ∈ olcFibre ctx)
    (hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z) (hlt : x < z) :
    2 ^ carryVal2 ctx x < (supportShell ctx.shell.d ctx.shell.X).card := by
  by_contra hge
  exact returnSelfRef_pair_false_of_carryVal2_large ctx hx hz hkey hlt (not_lt.mp hge)

/-- **`returnZero` is a theorem in the large-valuation regime** (re-contextualized for the datum
lane): if every fibre member has `K ≤ 2^{carryVal2 k}`, the self-referential slices are singletons
and the `(Z)` all-pairs zero-run field holds vacuously.  This is exactly the capstone `returnZero`
body, discharged by spacing arithmetic. -/
theorem returnZero_of_carryVal2_large (ctx : ActualFailureContext)
    (hval : ∀ k ∈ olcFibre ctx,
      (supportShell ctx.shell.d ctx.shell.X).card ≤ 2 ^ carryVal2 ctx k) :
    ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
      ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y,
        ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
          x < z → ∀ j, x < j → j ≤ z → ctx.d j = 0 :=
  returnDigit_hzero_of_carryVal2_large ctx hval

/-! ## Part 8.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the band-2 fixed-point closure for the Return / class-4
lane. -/
def returnFixedPointClosureStatus : List String :=
  [ "CLOSED (the band-2 fixed-point datum confinement, NEW - the wave-4 lever transplanted " ++
      "from band 3): band2_fixedHit_pins / returnClass4FixedHit_datum / " ++
      "returnClass4FixedHit_iff_datum - the actual datum's orbit hits a band-2 fixed point " ++
      "3F = q at some index j >= 1 IFF (q, K0) = (3, 1). Proof: backward determinism pins " ++
      "K1 = F (slopeOrbit_one_eq_of_hits_fixed, reused from DensePackFixedPointClosure), the " ++
      "base step pins 3*2^g0*K0 = 4q, and the divisor pin (2K0+1) | q (class1SlopeDatum_H_dvd + " ++
      "class1SlopeDatum_K0_eq) forces (2K0+1) | 3*2^g0, hence 2K0+1 = 3, K0 = 1, and " ++
      "3*2^g0 = 4q with odd q gives g0 = 2, q = 3. A fixed base 3*K0 = q propagates to index 1 " ++
      "(returnClass4FixedHit_of_base); the orbit indices the class-4 starts read are all >= 1.",
    "DECIDED (the (3,1) pair survives, NEW): the divisor pin admits the UNIQUE survivor " ++
      "(q, K0) = (3, 1) - verified formally in band2_fixedHit_pins (2K0+1 | 3*2^g0 with 3 prime " ++
      "and coprimality leaves 2K0+1 = 3; 3*2^g0 = 4q odd forces g0 = 2, q = 3). Then q = 3 = " ++
      "oddpart(Q*3) = 3*oddpart(Q) forces oddpart(Q) = 1 (return_datum_Q_oddPart), i.e. Q a " ++
      "power of two Q = 2^t (return_datum_Q_eq). The arithmetic does NOT refute it: the shell " ++
      "carries only 0 < Q, exactly as band 3's (21,3); recorded as THE surviving family.",
    "CHARACTERIZED (the (3,1) survivor, NEW): canonGap 3 1 = 2, 2^2*1 - 3 = 1 " ++
      "(canonGap_three_one, via canonGap_three_mul / boundedSlopeStep_three_mul upstream), the " ++
      "orbit is CONSTANT 1 (slopeOrbit_three_one_const), every residue reads band 2 " ++
      "(datum_canonGap_orbit_two_of_datum), and P = 1 with Q = 2^t so THE ERDOS WEIGHTED VALUE " ++
      "IS EXACTLY THE DYADIC RECIPROCAL sum n*d_n/2^n = 1/2^t (return_datum_value_eq, " ++
      "returnClass4FixedHit_value_eq) - the complete Q-arithmetic at this layer, value forced " ++
      "dyadic (any future digit-side fact contradicting a dyadic weighted value on a failing " ++
      "shell would void it), mirroring band 3's (21,3) verbatim.",
    "CLOSED (all-band-2 cycle rigidity, NEW - the band-2 mirror of the tower/densepack line): a " ++
      "period whose EVERY reading is band 2 forces the exact 1/3 fixed point 3*K1 = q " ++
      "(band2_full_orbit_forces_fixed: the run bound 2*4^{s-1} <= q of " ++
      "band2_run_forces_three_mul_or_pow_le fails at s = q+1 since q < 2^q <= 4^q; cycle form " ++
      "band2_full_cycle_forces_fixed; 3 | q form band2_full_cycle_three_dvd). At the actual " ++
      "datum an all-band-2 period forces (q, K0) = (3, 1) (returnClass4CycleBand2Full_datum).",
    "CLOSED (b2 < c off the fixed point, NEW): band2CycleCount_lt_of_not_fixed (generic, Icc " ++
      "form, mirror of band3CycleCount_lt_of_not_fixed / " ++
      "towerBand4CycleCount_lt_of_not_fixed) and datum_band2CycleCount_lt_of_offFixed (datum " ++
      "form): on every actual context with (q, K0) != (3, 1), EVERY orbit period has band-2 " ++
      "residue count strictly below the period - cycle band-2 density 1 happens ONLY on the " ++
      "confined (3, 1) family. Quantitative off-fixed fibre bound: olcFibre_card_le_offFixed " ++
      "(|fibre4| <= t*b2 AND b2 < c with t*c >= K).",
    "BRIDGED (the count field, additive) - class4FibreSmall_of_cycleCount: a per-ctx band-2 " ++
      "cycle-count witness t*b2 <= r+1 (period c, K <= t*c) discharges Class4FibreSmall through " ++
      "the existing four-way gate bridge class4FibreSmall_of_gates (its 4th disjunct), i.e. " ++
      "feeds the returnGates slot of Erdos260CycleResidual. NOT claimed unconditionally: at the " ++
      "(3,1) fixed point b2 = c (every residue is band 2), so the cycle-count disjunct is " ++
      "vacuous and only the sliding-window / span gates can bite - exactly the wave-3 honest " ++
      "obstruction, relocated to (3,1).",
    "RESIDUAL (honest, what resists) - returnInterior: at (3,1) every orbit residue reads " ++
      "band 2 (datum_canonGap_orbit_two_of_datum), so the interior top-band cycle check " ++
      "class4Interior_of_cycle_topBand_check (which needs the >= r+1 top-band residues to AVOID " ++
      "band 2) cannot fire; the K.1 interior stays genuine window content there. " ++
      "returnInterior is discharged off (3,1) ONLY when the top-band residues avoid band 2 - no " ++
      "unconditional closure is claimed.",
    "RESIDUAL (honest, what resists) - digit fields returnZero / returnMaxClean: the M.2.1 " ++
      "self-referential congruence (returnSelfRefKey_gapDiv) gives SPACING only. A same-slice " ++
      "class-4 pair x < z forces 2^{carryVal2 x} < K (returnSelfRef_sliceModulus_lt_width_of_pair, " ++
      "the contrapositive of returnSelfRef_pair_false_of_carryVal2_large). So the " ++
      "carryVal2 >= log2 K regime makes returnZero a theorem (returnZero_of_carryVal2_large, the " ++
      "existing returnDigit_hzero_of_carryVal2_large re-contextualized) and shrinks returnMaxClean " ++
      "to the per-slice maxima (returnDigit_cleanStep_of_hzero_max upstream); the complementary " ++
      "carryVal2 < log2 K regime genuinely resists - no formalized bridge ties the digit-side gap " ++
      "floor to the orbit-side band beyond the shared index, and we do NOT prove any context empty." ]

theorem returnFixedPointClosureStatus_nonempty :
    returnFixedPointClosureStatus ≠ [] := by
  simp [returnFixedPointClosureStatus]

/-! ## Part 9.  Axiom-cleanliness audit -/

#print axioms canonGap_of_three_mul
#print axioms boundedSlopeStep_of_three_mul
#print axioms slopeOrbit_three_one_const
#print axioms band2_fixedHit_pins
#print axioms returnClass4FixedHit_datum
#print axioms returnClass4FixedHit_of_datum
#print axioms returnClass4FixedHit_iff_datum
#print axioms returnClass4FixedHit_of_base
#print axioms band2_full_orbit_forces_fixed
#print axioms band2_full_cycle_forces_fixed
#print axioms band2_full_cycle_three_dvd
#print axioms band2CycleCount_le
#print axioms band2CycleCount_lt_of_not_fixed
#print axioms returnClass4CycleBand2Full_datum
#print axioms datum_band2CycleCount_lt_of_offFixed
#print axioms olcFibre_card_le_offFixed
#print axioms class4FibreSmall_of_cycleCount
#print axioms datum_canonGap_orbit_two_of_datum
#print axioms return_datum_Q_oddPart
#print axioms return_datum_Q_eq
#print axioms return_datum_value_eq
#print axioms returnClass4FixedHit_value_eq
#print axioms returnSelfRef_sliceModulus_lt_width_of_pair
#print axioms returnZero_of_carryVal2_large
#print axioms returnFixedPointClosureStatus_nonempty

end

end Erdos260
