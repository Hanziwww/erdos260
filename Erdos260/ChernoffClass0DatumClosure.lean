import Erdos260.ChernoffClass0CycleClosure

/-!
# Class-0 (Chernoff) datum-driven deep-band closure, wave 4

This module (NEW; it edits no existing file) attacks the wave-3 capstone field

  `class0Cycle : ∀ ctx, Class0WindowCycleCheck ctx`

of `Erdos260CycleResidual` (`Erdos260CycleCapstone.lean`) with the wave-4 datum lever: the
orbit datum `(q, K₀)` of the actual context is NOT arbitrary — it satisfies the proved
divisor pin `(2·K₀ + 1) ∣ q` (from `class1SlopeDatum_H_dvd` + `class1SlopeDatum_K₀_eq`:
`H = 2|P| + 1` divides `q` and `K₀ = |P|`).  Intersecting this pin with the deep-band
arithmetic `16·K ≤ q` collapses each modulus window to an EXPLICIT finite list of
`(q, K₀)` pairs, each of which is then either CLOSED by a finite cycle/divisor check or
PROVED to be a genuine obstruction to the window-free check.

## What IS newly closed here (all unconditional theorems)

* **The class-0 datum divisor pin** (`class0_datum_dvd`): `(2·K₀ + 1) ∣ q` at every ctx.
* **Canonical-gap evaluation** (`canonGap_eq_of_bounds`, `boundedSlopeStep_eq_of_bounds`,
  `slopeOrbit_period_of_return`): the E.13 band bounds determine `canonGap` uniquely, so
  explicit orbits are verified by pure numeral arithmetic (no `Nat.log` computation).
* **The exact boundary of the window-free check**
  (`class0CycleDeepBandFree_iff_orbit_deepBand_free`): `Class0CycleDeepBandFree ctx` holds
  IFF the orbit misses the deep band at EVERY positive index — so each datum pair is
  decidably closed or decidably obstructed.
* **The `q < 48` bottleneck sharpening**
  (`deepBand_odd_eq_one_of_modulus_lt_48`,
  `class0CycleDeepBandFree_of_cycle_avoids_one_of_modulus_lt_48`,
  `class0Pinned_of_cycle_avoids_one_of_modulus_lt_48`): window starts read the orbit at
  indices `k ≥ 1` where it is ODD, and an odd deep value below modulus `48` must be `1` —
  extending the wave-3 avoid-`1` window `17 ≤ q < 32` by a full band to `17 ≤ q < 48`.
* **The datum enumerations** (`datum_mid_window_pairs`, `datum_upper_window_pairs`): on
  `17 ≤ q < 32` the divisor pin admits EXACTLY thirteen pairs, on `32 ≤ q < 48` exactly
  eighteen — pure `(q, K₀)` arithmetic from the pin, oddness, and `2·K₀ < q`.
* **Twelve per-pair cycle/divisor closures**
  (`class0CycleDeepBandFree_of_datum_21_3/21_10/23_11/31_15/33_5/35_3/35_17/39_6/39_19/`
  `45_7/45_22/47_23`): explicit periods avoid the deep band, deciding the pair.
* **The gcd/divisor datum criteria** (`datum_gcd_floor_forces_K_le_seven`,
  `class0CycleDeepBandFree_of_datum_product`, `class0Pinned_of_datum_55_5`,
  `class0Pinned_of_datum_105_7`): under the pin `gcd(q, K₀)·(2·K₀+1) ∣ q`, so the proved
  gcd-floor closure can fire ONLY for `K₀ ≤ 7`; the product family `q = K₀·(2·K₀+1)`,
  `K₀ ≤ 7` closes outright — in particular `(55, 5)` and `(105, 7)` BEYOND the enumerated
  windows (the latter is the tower fixed-point datum pair).
* **The deep-base datum confinement** (`datum_deep_base_q_ge`,
  `datum_odd_deep_base_pairs`): a deep base `16·K₀ ≤ q` under the pin forces
  `q ≥ 7·(2·K₀+1)`, and in the boundary band `q < 9·(2·K₀+1)` exactly the two pairs
  `(21, 1)` and `(49, 3)` survive — the datum confinement of the wave-3 odd-small-base
  obstruction family.
* **The survivor resolution** (`Class0DatumSurvivor`, `class0_datum_window_resolved`,
  `class0_datum_survivor_defeats_cycleCheck`, `class0CycleDeepBandFree_iff_not_survivor`):
  on every shell with `q < 48` the window-free check is DECIDED — it holds IFF the datum
  pair is NOT one of the nineteen explicit survivors, each of which provably reaches the
  deep band on its cycle (orbit hits `1`).
* **The window-residue exploits** (`class0Pinned_of_datum_17_8_window`,
  `class0Pinned_of_datum_21_1_window`): for the flagship survivors the deep cycle residues
  are explicit (`4 ∣ k`, resp. `2 ∣ k`), so a start-congruence hypothesis closes the ctx —
  the brief's window-position-vs-cycle-residue lever in concrete form.
* **The field/capstone bridges** (`class0Pinned_of_datum_not_survivor`,
  `class0Pinned_field_of_datum_split`, `class0Cycle_of_datum_split`,
  `class0FibreEmpty_of_datum_split`): the capstone field (verbatim type
  `∀ ctx, Class0WindowCycleCheck ctx`) follows from windowed checks ONLY on the nineteen
  surviving datum pairs plus the `48 ≤ q` regime — a strictly smaller residual than the
  wave-3 surface (which needed the windowed check on every `q ≥ 17` shell).

## Honest obstruction boundary (proved, not conjectured)

The nineteen surviving pairs defeat every window-free cycle check
(`class0_datum_survivor_defeats_cycleCheck`): their cycles provably contain the deep value
`1`.  On those shells only the WINDOWED check (gap-floor coupling at the shared index `k` +
cycle-residue miss) can close the atom, and no formalized `hitGap ↔ canonGap` bridge exists
at the actual ctx.  We do NOT claim unconditional closure of the atom.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The class-0 datum divisor pin

`class1SlopeDatum_H_dvd` gives `H = 2|P| + 1 ∣ q` and `class1SlopeDatum_K₀_eq` gives
`K₀ = |P|`, so the orbit datum satisfies `(2·K₀ + 1) ∣ q` — the wave-4 lever. -/

/-- **The datum divisor pin**: the actual orbit datum satisfies `(2·K₀ + 1) ∣ q`. -/
theorem class0_datum_dvd (ctx : ActualFailureContext) :
    2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
  have h := class1SlopeDatum_H_dvd ctx
  rwa [← class1SlopeDatum_K₀_eq ctx] at h

/-! ## Part 2.  Canonical-gap evaluation by band bounds

`canonGap q K` is the UNIQUE `g` with `q < 2^g·K < 2q` (for odd `q`), so explicit orbit
steps are verified by numeral arithmetic alone — no `Nat.log` evaluation anywhere. -/

/-- **The canonical gap is determined by the band bounds**: for odd `q` and admissible `K`,
any `g` with `q < 2^g·K < 2q` equals `canonGap q K`. -/
theorem canonGap_eq_of_bounds {q K g : ℕ} (hq : Odd q) (hK1 : 1 ≤ K) (hKq : K < q)
    (hlow : q < 2 ^ g * K) (hhigh : 2 ^ g * K < 2 * q) : canonGap q K = g := by
  obtain ⟨hlow₀, hhigh₀⟩ := canonGap_bounds hq hK1 hKq
  rcases Nat.lt_trichotomy (canonGap q K) g with h | h | h
  · exfalso
    have hle : 2 ^ (canonGap q K + 1) ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (canonGap q K + 1) * K ≤ 2 ^ g * K := Nat.mul_le_mul hle (le_refl K)
    have h3 : 2 ^ (canonGap q K + 1) * K = 2 * (2 ^ canonGap q K * K) := by ring
    omega
  · exact h
  · exfalso
    have hle : 2 ^ (g + 1) ≤ 2 ^ canonGap q K := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (g + 1) * K ≤ 2 ^ canonGap q K * K := Nat.mul_le_mul hle (le_refl K)
    have h3 : 2 ^ (g + 1) * K = 2 * (2 ^ g * K) := by ring
    omega

/-- The E.13 step evaluated through the band bounds: `boundedSlopeStep q K = 2^g·K − q`
whenever `q < 2^g·K < 2q`. -/
theorem boundedSlopeStep_eq_of_bounds {q K g : ℕ} (hq : Odd q) (hK1 : 1 ≤ K) (hKq : K < q)
    (hlow : q < 2 ^ g * K) (hhigh : 2 ^ g * K < 2 * q) :
    boundedSlopeStep q K = 2 ^ g * K - q := by
  unfold boundedSlopeStep
  rw [canonGap_eq_of_bounds hq hK1 hKq hlow hhigh]

/-- One explicit orbit step: from `K_j = K` and band bounds for `g`, read off
`K_{j+1} = 2^g·K − q`. -/
private theorem orbit_step {q K₀ j K g K' : ℕ} (hq : Odd q)
    (h : slopeOrbit q K₀ j = K) (hK1 : 1 ≤ K) (hKq : K < q)
    (hlow : q < 2 ^ g * K) (hhigh : 2 ^ g * K < 2 * q) (hval : 2 ^ g * K - q = K') :
    slopeOrbit q K₀ (j + 1) = K' := by
  have hstep : slopeOrbit q K₀ (j + 1) = boundedSlopeStep q (slopeOrbit q K₀ j) := rfl
  rw [hstep, h, boundedSlopeStep_eq_of_bounds hq hK1 hKq hlow hhigh, hval]

/-- A first-return collision `K_{1+c} = K_1` iterates to a full period valid from
index `1` (forward determinism). -/
theorem slopeOrbit_period_of_return {q K₀ c : ℕ}
    (h : slopeOrbit q K₀ (1 + c) = slopeOrbit q K₀ 1) :
    ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m := by
  intro m hm
  obtain ⟨t, rfl⟩ : ∃ t, m = 1 + t := ⟨m - 1, by omega⟩
  have hshift := slopeOrbit_eq_shift h t
  have e1 : 1 + c + t = 1 + t + c := by omega
  rw [e1] at hshift
  exact hshift

/-! ## Part 3.  The exact boundary of the window-free check

`Class0CycleDeepBandFree ctx` holds IFF the orbit misses the deep band at every positive
index — by the residue reduction any single deep hit lands inside EVERY period block. -/

/-- **The window-free check is exactly orbit deep-band-freeness**: some deep-band-free
period exists iff the orbit misses the deep band at every positive index. -/
theorem class0CycleDeepBandFree_iff_orbit_deepBand_free (ctx : ActualFailureContext) :
    Class0CycleDeepBandFree ctx
      ↔ ∀ j, 1 ≤ j →
          (class1SlopeDatum ctx).q
            < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j := by
  constructor
  · rintro ⟨c, hc1, hcq, hper, hband⟩
    exact slopeOrbit_pred_of_cycle
      (P := fun K => (class1SlopeDatum ctx).q < 16 * K) hc1 hper hband
  · intro h
    obtain ⟨c, hc1, hcq, hper⟩ := class1Fibre_orbit_period_exists ctx
    exact ⟨c, hc1, hcq, hper, fun j hj1 _ => h j hj1⟩

/-- **Datum obstruction builder**: a single explicit deep orbit value at a positive index
refutes the window-free check at every ctx carrying that datum pair. -/
theorem not_class0CycleDeepBandFree_of_datum_orbit_deep (ctx : ActualFailureContext)
    {qv Kv : ℕ} (hq : (class1SlopeDatum ctx).q = qv) (hK : (class1SlopeDatum ctx).K₀ = Kv)
    (j₀ : ℕ) (hj₀ : 1 ≤ j₀) (hdeep : 16 * slopeOrbit qv Kv j₀ ≤ qv) :
    ¬ Class0CycleDeepBandFree ctx := by
  subst hq; subst hK
  intro hfree
  have h := (class0CycleDeepBandFree_iff_orbit_deepBand_free ctx).mp hfree j₀ hj₀
  omega

/-- On `q < 17` the window-free check holds outright (deep needs `16·K ≤ q`, `K ≥ 1`,
`q` odd). -/
theorem class0CycleDeepBandFree_of_modulus_lt_seventeen (ctx : ActualFailureContext)
    (hq17 : (class1SlopeDatum ctx).q < 17) : Class0CycleDeepBandFree ctx := by
  obtain ⟨c, hc1, hcq, hper⟩ := class1Fibre_orbit_period_exists ctx
  refine ⟨c, hc1, hcq, hper, fun j hj1 hjc => ?_⟩
  have hmem := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt j
  obtain ⟨t, ht⟩ := (class1SlopeDatum ctx).hq_odd
  omega

/-! ## Part 4.  Divisor-floor closures at the check level

The divisor persistence of `ChernoffClass0CycleClosure` upgraded to conclude the
window-free check itself (with the canonical period), plus the datum product family. -/

/-- **Divisor-floor check closure**: a common divisor `d` of `q` and `K₀` with `q < 16·d`
yields the window-free check (every orbit value is a positive multiple of `d`). -/
theorem class0CycleDeepBandFree_of_dvd_floor (ctx : ActualFailureContext) {d : ℕ}
    (hdq : d ∣ (class1SlopeDatum ctx).q) (hdK : d ∣ (class1SlopeDatum ctx).K₀)
    (hfl : (class1SlopeDatum ctx).q < 16 * d) : Class0CycleDeepBandFree ctx := by
  obtain ⟨c, hc1, hcq, hper⟩ := class1Fibre_orbit_period_exists ctx
  refine ⟨c, hc1, hcq, hper, fun j hj1 hjc => ?_⟩
  have hdvd := slopeOrbit_dvd_of_dvd hdq hdK j
  have hmem := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt j
  have hle : d ≤ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j :=
    Nat.le_of_dvd hmem.1 hdvd
  omega

/-- Datum-pair form of the divisor-floor check closure. -/
theorem class0CycleDeepBandFree_of_datum_dvd_floor (ctx : ActualFailureContext)
    {qv Kv : ℕ} (hq : (class1SlopeDatum ctx).q = qv) (hK : (class1SlopeDatum ctx).K₀ = Kv)
    (d : ℕ) (hdq : d ∣ qv) (hdK : d ∣ Kv) (hfl : qv < 16 * d) :
    Class0CycleDeepBandFree ctx := by
  subst hq; subst hK
  exact class0CycleDeepBandFree_of_dvd_floor ctx hdq hdK hfl

/-- **The datum product family closes** (pure `(q, K₀)` arithmetic): `q = K₀·(2·K₀+1)` with
`K₀ ≤ 7` yields the window-free check — the pin-compatible family `(3,1), (21,3), (55,5),
(105,7)`. -/
theorem class0CycleDeepBandFree_of_datum_product (ctx : ActualFailureContext)
    (hprod : (class1SlopeDatum ctx).q
      = (class1SlopeDatum ctx).K₀ * (2 * (class1SlopeDatum ctx).K₀ + 1))
    (h7 : (class1SlopeDatum ctx).K₀ ≤ 7) : Class0CycleDeepBandFree ctx := by
  have hK1 : 1 ≤ (class1SlopeDatum ctx).K₀ := (class1SlopeDatum ctx).hK₀_pos
  refine class0CycleDeepBandFree_of_dvd_floor ctx (d := (class1SlopeDatum ctx).K₀) ?_ dvd_rfl ?_
  · rw [hprod]; exact dvd_mul_right _ _
  · rw [hprod]
    have h15 : (class1SlopeDatum ctx).K₀ * (2 * (class1SlopeDatum ctx).K₀ + 1)
        ≤ (class1SlopeDatum ctx).K₀ * 15 := Nat.mul_le_mul (le_refl _) (by omega)
    omega

/-- Product family, pinned-arithmetic form (the capstone field body per ctx). -/
theorem class0Pinned_of_datum_product (ctx : ActualFailureContext)
    (hprod : (class1SlopeDatum ctx).q
      = (class1SlopeDatum ctx).K₀ * (2 * (class1SlopeDatum ctx).K₀ + 1))
    (h7 : (class1SlopeDatum ctx).K₀ ≤ 7) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_cycleCheck ctx (class0CycleDeepBandFree_of_datum_product ctx hprod h7)

/-- The `(55, 5)` datum pair is class-0 closed (beyond the enumerated windows). -/
theorem class0Pinned_of_datum_55_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 55) (hK : (class1SlopeDatum ctx).K₀ = 5) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_cycleCheck ctx
    (class0CycleDeepBandFree_of_datum_dvd_floor ctx hq hK 5 (by norm_num) (by norm_num)
      (by norm_num))

/-- The `(105, 7)` datum pair — the tower fixed-point pair — is class-0 closed. -/
theorem class0Pinned_of_datum_105_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 7) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_cycleCheck ctx
    (class0CycleDeepBandFree_of_datum_dvd_floor ctx hq hK 7 (by norm_num) (by norm_num)
      (by norm_num))

/-! ## Part 5.  K₀-only datum criteria from the divisor pin

`gcd(q, K₀)` is coprime to `2·K₀ + 1`, so under the pin `gcd·(2K₀+1) ∣ q`: the gcd-floor
closure can fire only for `K₀ ≤ 7`, and a deep base forces `q ≥ 7·(2K₀+1)`. -/

/-- A divisor of `K₀` is coprime to `2·K₀ + 1`. -/
private theorem coprime_of_dvd_base {d K : ℕ} (hdK : d ∣ K) : Nat.Coprime d (2 * K + 1) := by
  have he1 : Nat.gcd d (2 * K + 1) ∣ 2 * K := ((Nat.gcd_dvd_left _ _).trans hdK).mul_left 2
  have he2 : Nat.gcd d (2 * K + 1) ∣ 2 * K + 1 := Nat.gcd_dvd_right _ _
  have h1 : Nat.gcd d (2 * K + 1) ∣ 1 := by
    have := Nat.dvd_sub he2 he1
    have e : 2 * K + 1 - 2 * K = 1 := by omega
    rwa [e] at this
  exact Nat.dvd_one.mp h1

/-- **The gcd-floor limitation under the pin**: `(2·K+1) ∣ q` and `q < 16·gcd(q, K)` force
`K ≤ 7` — under the actual datum the no-cycle gcd closure is confined to small bases. -/
theorem datum_gcd_floor_forces_K_le_seven {q K : ℕ} (hq2 : 2 ≤ q) (hK1 : 1 ≤ K)
    (hdvd : 2 * K + 1 ∣ q) (hfl : q < 16 * Nat.gcd q K) : K ≤ 7 := by
  set d := Nat.gcd q K with hd
  have hdq : d ∣ q := Nat.gcd_dvd_left q K
  have hdK : d ∣ K := Nat.gcd_dvd_right q K
  have hmul : d * (2 * K + 1) ∣ q := (coprime_of_dvd_base hdK).mul_dvd_of_dvd_of_dvd hdq hdvd
  have hle : d * (2 * K + 1) ≤ q := Nat.le_of_dvd (by omega) hmul
  by_contra hcon
  have h16 : 16 ≤ 2 * K + 1 := by omega
  have hge : d * 16 ≤ d * (2 * K + 1) := Nat.mul_le_mul (le_refl d) h16
  omega

/-- Ctx form of the gcd-floor limitation. -/
theorem class0_datum_gcd_floor_K₀_le_seven (ctx : ActualFailureContext)
    (hfl : (class1SlopeDatum ctx).q
      < 16 * Nat.gcd (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀) :
    (class1SlopeDatum ctx).K₀ ≤ 7 :=
  datum_gcd_floor_forces_K_le_seven (class1SlopeDatum ctx).hq2
    (class1SlopeDatum ctx).hK₀_pos (class0_datum_dvd ctx) hfl

/-- **The deep-base datum bound**: `(2·K+1) ∣ q`, `q` odd, `K ≥ 1`, `16·K ≤ q` force
`q ≥ 7·(2·K+1)` — the divisor pin pushes every deep-base shell seven `H`-multiples up. -/
theorem datum_deep_base_q_ge {q K : ℕ} (hq_odd : Odd q) (hdvd : 2 * K + 1 ∣ q)
    (hK1 : 1 ≤ K) (hdeep : 16 * K ≤ q) : 7 * (2 * K + 1) ≤ q := by
  obtain ⟨s, hs⟩ := hdvd
  have hs_odd : Odd s := (Nat.odd_mul.mp (hs ▸ hq_odd)).2
  rcases Nat.lt_or_ge s 7 with h7 | h7
  · exfalso
    have hs135 : s = 1 ∨ s = 3 ∨ s = 5 := by
      obtain ⟨u, hu⟩ := hs_odd
      omega
    rcases hs135 with rfl | rfl | rfl <;> omega
  · calc 7 * (2 * K + 1) = (2 * K + 1) * 7 := by ring
      _ ≤ (2 * K + 1) * s := Nat.mul_le_mul (le_refl _) h7
      _ = q := hs.symm

/-- Ctx form of the deep-base bound. -/
theorem class0_datum_deep_base_q_ge (ctx : ActualFailureContext)
    (hdeep : 16 * (class1SlopeDatum ctx).K₀ ≤ (class1SlopeDatum ctx).q) :
    7 * (2 * (class1SlopeDatum ctx).K₀ + 1) ≤ (class1SlopeDatum ctx).q :=
  datum_deep_base_q_ge (class1SlopeDatum ctx).hq_odd (class0_datum_dvd ctx)
    (class1SlopeDatum ctx).hK₀_pos hdeep

/-- **The boundary deep-base pairs**: an ODD deep base under the pin with
`q < 9·(2·K+1)` (the quotient-`7` boundary band) is EXACTLY `(21, 1)` or `(49, 3)` — the
datum confinement of the odd-small-base obstruction family at its minimal quotient. -/
theorem datum_odd_deep_base_pairs {q K : ℕ} (hq_odd : Odd q) (hdvd : 2 * K + 1 ∣ q)
    (hK1 : 1 ≤ K) (hodd : Odd K) (hdeep : 16 * K ≤ q) (hlt : q < 9 * (2 * K + 1)) :
    (q = 21 ∧ K = 1) ∨ (q = 49 ∧ K = 3) := by
  have h7 := datum_deep_base_q_ge hq_odd hdvd hK1 hdeep
  obtain ⟨s, hs⟩ := hdvd
  have hs_odd : Odd s := (Nat.odd_mul.mp (hs ▸ hq_odd)).2
  have h7s : 7 ≤ s := by
    by_contra hcon
    have hle : (2 * K + 1) * s ≤ (2 * K + 1) * 6 := Nat.mul_le_mul (le_refl _) (by omega)
    omega
  have hs9 : s < 9 := by
    by_contra hcon
    have hge : (2 * K + 1) * 9 ≤ (2 * K + 1) * s := Nat.mul_le_mul (le_refl _) (by omega)
    omega
  obtain ⟨u, hu⟩ := hs_odd
  have hs7 : s = 7 := by omega
  subst hs7
  obtain ⟨v, hv⟩ := hodd
  omega

/-- Ctx form of the boundary deep-base pairs. -/
theorem class0_datum_odd_deep_base_pairs (ctx : ActualFailureContext)
    (hodd : Odd (class1SlopeDatum ctx).K₀)
    (hdeep : 16 * (class1SlopeDatum ctx).K₀ ≤ (class1SlopeDatum ctx).q)
    (hlt : (class1SlopeDatum ctx).q < 9 * (2 * (class1SlopeDatum ctx).K₀ + 1)) :
    ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 1)
      ∨ ((class1SlopeDatum ctx).q = 49 ∧ (class1SlopeDatum ctx).K₀ = 3) :=
  datum_odd_deep_base_pairs (class1SlopeDatum ctx).hq_odd (class0_datum_dvd ctx)
    (class1SlopeDatum ctx).hK₀_pos hodd hdeep hlt

/-! ## Part 6.  The `q < 48` bottleneck sharpening

Window starts have `k ≥ 1`, where the orbit is ODD; an odd deep value below modulus `48`
must be `1`.  This extends the wave-3 avoid-`1` reduction from `q < 32` to `q < 48`. -/

/-- **The odd deep band below `48` is `{1}`**: `Odd K`, `16·K ≤ q < 48` force `K = 1`. -/
theorem deepBand_odd_eq_one_of_modulus_lt_48 {q K : ℕ} (hq48 : q < 48) (hodd : Odd K)
    (h16 : 16 * K ≤ q) : K = 1 := by
  obtain ⟨t, ht⟩ := hodd
  omega

/-- **Avoid-`1` check closure on `q < 48`**: a period block avoiding the value `1` yields
the window-free check on every modulus `q < 48` (the orbit is odd at positive indices). -/
theorem class0CycleDeepBandFree_of_cycle_avoids_one_of_modulus_lt_48
    (ctx : ActualFailureContext) (hq48 : (class1SlopeDatum ctx).q < 48) {c : ℕ}
    (hc1 : 1 ≤ c) (hcq : c ≤ (class1SlopeDatum ctx).q)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (h1 : ∀ j, 1 ≤ j → j ≤ c →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j ≠ 1) :
    Class0CycleDeepBandFree ctx := by
  refine ⟨c, hc1, hcq, hper, fun j hj1 hjc => ?_⟩
  have hodd := slopeOrbit_odd (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt j hj1
  have hne := h1 j hj1 hjc
  obtain ⟨t, ht⟩ := hodd
  omega

/-- **Avoid-`1` pinned closure on `q < 48`** — the strict extension of the wave-3
`class0Pinned_of_cycle_avoids_one_of_modulus_lt_32` by a full dyadic band. -/
theorem class0Pinned_of_cycle_avoids_one_of_modulus_lt_48 (ctx : ActualFailureContext)
    (hq48 : (class1SlopeDatum ctx).q < 48) {c : ℕ}
    (hc1 : 1 ≤ c) (hcq : c ≤ (class1SlopeDatum ctx).q)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (h1 : ∀ j, 1 ≤ j → j ≤ c →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j ≠ 1) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_cycleCheck ctx
    (class0CycleDeepBandFree_of_cycle_avoids_one_of_modulus_lt_48 ctx hq48 hc1 hcq hper h1)

/-- Datum-pair form of the avoid-`1` check closure on `q < 48`. -/
theorem class0CycleDeepBandFree_of_datum_avoids_one (ctx : ActualFailureContext)
    {qv Kv : ℕ} (hq : (class1SlopeDatum ctx).q = qv) (hK : (class1SlopeDatum ctx).K₀ = Kv)
    (c : ℕ) (hq48 : qv < 48) (hc1 : 1 ≤ c) (hcq : c ≤ qv)
    (hper : ∀ m, 1 ≤ m → slopeOrbit qv Kv (m + c) = slopeOrbit qv Kv m)
    (h1 : ∀ j, 1 ≤ j → j ≤ c → slopeOrbit qv Kv j ≠ 1) :
    Class0CycleDeepBandFree ctx := by
  subst hq; subst hK
  exact class0CycleDeepBandFree_of_cycle_avoids_one_of_modulus_lt_48 ctx hq48 hc1 hcq hper h1

/-! ## Part 7.  The datum enumerations: `17 ≤ q < 32` and `32 ≤ q < 48`

Pure `(q, K)` arithmetic: `q` odd, `1 ≤ K`, `2·K < q`, `(2·K+1) ∣ q` confine the datum to
EXPLICIT pair lists on each window. -/

/-- **The mid-window datum enumeration**: on `17 ≤ q < 32` the divisor pin admits exactly
thirteen pairs. -/
theorem datum_mid_window_pairs {q K : ℕ} (hq_odd : Odd q) (hK1 : 1 ≤ K)
    (h2K : 2 * K < q) (hdvd : 2 * K + 1 ∣ q) (h17 : 17 ≤ q) (h32 : q < 32) :
    (q = 17 ∧ K = 8) ∨ (q = 19 ∧ K = 9) ∨ (q = 21 ∧ K = 1) ∨ (q = 21 ∧ K = 3)
    ∨ (q = 21 ∧ K = 10) ∨ (q = 23 ∧ K = 11) ∨ (q = 25 ∧ K = 2) ∨ (q = 25 ∧ K = 12)
    ∨ (q = 27 ∧ K = 1) ∨ (q = 27 ∧ K = 4) ∨ (q = 27 ∧ K = 13) ∨ (q = 29 ∧ K = 14)
    ∨ (q = 31 ∧ K = 15) := by
  obtain ⟨s, hs⟩ := hdvd
  obtain ⟨t, ht⟩ := hq_odd
  have hK15 : K ≤ 15 := by omega
  have hq8 : q = 17 ∨ q = 19 ∨ q = 21 ∨ q = 23 ∨ q = 25 ∨ q = 27 ∨ q = 29 ∨ q = 31 := by
    omega
  rcases hq8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases K <;> ((try ring_nf at hs); first | (norm_num; done) | (exfalso; omega))

/-- **The upper-window datum enumeration**: on `32 ≤ q < 48` the divisor pin admits exactly
eighteen pairs. -/
theorem datum_upper_window_pairs {q K : ℕ} (hq_odd : Odd q) (hK1 : 1 ≤ K)
    (h2K : 2 * K < q) (hdvd : 2 * K + 1 ∣ q) (h32 : 32 ≤ q) (h48 : q < 48) :
    (q = 33 ∧ K = 1) ∨ (q = 33 ∧ K = 5) ∨ (q = 33 ∧ K = 16) ∨ (q = 35 ∧ K = 2)
    ∨ (q = 35 ∧ K = 3) ∨ (q = 35 ∧ K = 17) ∨ (q = 37 ∧ K = 18) ∨ (q = 39 ∧ K = 1)
    ∨ (q = 39 ∧ K = 6) ∨ (q = 39 ∧ K = 19) ∨ (q = 41 ∧ K = 20) ∨ (q = 43 ∧ K = 21)
    ∨ (q = 45 ∧ K = 1) ∨ (q = 45 ∧ K = 2) ∨ (q = 45 ∧ K = 4) ∨ (q = 45 ∧ K = 7)
    ∨ (q = 45 ∧ K = 22) ∨ (q = 47 ∧ K = 23) := by
  obtain ⟨s, hs⟩ := hdvd
  obtain ⟨t, ht⟩ := hq_odd
  have hK23 : K ≤ 23 := by omega
  have hq8 : q = 33 ∨ q = 35 ∨ q = 37 ∨ q = 39 ∨ q = 41 ∨ q = 43 ∨ q = 45 ∨ q = 47 := by
    omega
  rcases hq8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases K <;> ((try ring_nf at hs); first | (norm_num; done) | (exfalso; omega))

/-! ## Part 8.  The twelve per-pair cycle/divisor closures

Each explicit cycle is verified step by step through the band bounds; the period is the
first return to the index-`1` value; avoidance of `1` is read off the period block. -/

private theorem orbit_21_10_check :
    (∀ m, 1 ≤ m → slopeOrbit 21 10 (m + 4) = slopeOrbit 21 10 m)
    ∧ ∀ j, 1 ≤ j → j ≤ 4 → slopeOrbit 21 10 j ≠ 1 := by
  have hq : Odd 21 := ⟨10, by norm_num⟩
  have h0 : slopeOrbit 21 10 0 = 10 := rfl
  have h1 : slopeOrbit 21 10 1 = 19 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 21 10 2 = 17 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 21 10 3 = 13 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 21 10 4 = 5 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 21 10 5 = 19 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, ?_⟩
  · show slopeOrbit 21 10 5 = slopeOrbit 21 10 1
    rw [h5, h1]
  · intro j hj1 hj4
    interval_cases j <;> simp_all

private theorem orbit_23_11_check :
    (∀ m, 1 ≤ m → slopeOrbit 23 11 (m + 7) = slopeOrbit 23 11 m)
    ∧ ∀ j, 1 ≤ j → j ≤ 7 → slopeOrbit 23 11 j ≠ 1 := by
  have hq : Odd 23 := ⟨11, by norm_num⟩
  have h0 : slopeOrbit 23 11 0 = 11 := rfl
  have h1 : slopeOrbit 23 11 1 = 21 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 23 11 2 = 19 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 23 11 3 = 15 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 23 11 4 = 7 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 23 11 5 = 5 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 23 11 6 = 17 :=
    orbit_step hq h5 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 23 11 7 = 11 :=
    orbit_step hq h6 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 23 11 8 = 21 :=
    orbit_step hq h7 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, ?_⟩
  · show slopeOrbit 23 11 8 = slopeOrbit 23 11 1
    rw [h8, h1]
  · intro j hj1 hj7
    interval_cases j <;> simp_all

private theorem orbit_31_15_check :
    (∀ m, 1 ≤ m → slopeOrbit 31 15 (m + 4) = slopeOrbit 31 15 m)
    ∧ ∀ j, 1 ≤ j → j ≤ 4 → slopeOrbit 31 15 j ≠ 1 := by
  have hq : Odd 31 := ⟨15, by norm_num⟩
  have h0 : slopeOrbit 31 15 0 = 15 := rfl
  have h1 : slopeOrbit 31 15 1 = 29 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 31 15 2 = 27 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 31 15 3 = 23 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 31 15 4 = 15 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 31 15 5 = 29 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, ?_⟩
  · show slopeOrbit 31 15 5 = slopeOrbit 31 15 1
    rw [h5, h1]
  · intro j hj1 hj4
    interval_cases j <;> simp_all

private theorem orbit_33_5_check :
    (∀ m, 1 ≤ m → slopeOrbit 33 5 (m + 5) = slopeOrbit 33 5 m)
    ∧ ∀ j, 1 ≤ j → j ≤ 5 → slopeOrbit 33 5 j ≠ 1 := by
  have hq : Odd 33 := ⟨16, by norm_num⟩
  have h0 : slopeOrbit 33 5 0 = 5 := rfl
  have h1 : slopeOrbit 33 5 1 = 7 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 33 5 2 = 23 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 33 5 3 = 13 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 33 5 4 = 19 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 33 5 5 = 5 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 33 5 6 = 7 :=
    orbit_step hq h5 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, ?_⟩
  · show slopeOrbit 33 5 6 = slopeOrbit 33 5 1
    rw [h6, h1]
  · intro j hj1 hj5
    interval_cases j <;> simp_all

private theorem orbit_35_3_check :
    (∀ m, 1 ≤ m → slopeOrbit 35 3 (m + 7) = slopeOrbit 35 3 m)
    ∧ ∀ j, 1 ≤ j → j ≤ 7 → slopeOrbit 35 3 j ≠ 1 := by
  have hq : Odd 35 := ⟨17, by norm_num⟩
  have h0 : slopeOrbit 35 3 0 = 3 := rfl
  have h1 : slopeOrbit 35 3 1 = 13 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 35 3 2 = 17 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 35 3 3 = 33 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 35 3 4 = 31 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 35 3 5 = 27 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 35 3 6 = 19 :=
    orbit_step hq h5 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 35 3 7 = 3 :=
    orbit_step hq h6 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 35 3 8 = 13 :=
    orbit_step hq h7 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, ?_⟩
  · show slopeOrbit 35 3 8 = slopeOrbit 35 3 1
    rw [h8, h1]
  · intro j hj1 hj7
    interval_cases j <;> simp_all

private theorem orbit_35_17_check :
    (∀ m, 1 ≤ m → slopeOrbit 35 17 (m + 7) = slopeOrbit 35 17 m)
    ∧ ∀ j, 1 ≤ j → j ≤ 7 → slopeOrbit 35 17 j ≠ 1 := by
  have hq : Odd 35 := ⟨17, by norm_num⟩
  have h0 : slopeOrbit 35 17 0 = 17 := rfl
  have h1 : slopeOrbit 35 17 1 = 33 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 35 17 2 = 31 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 35 17 3 = 27 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 35 17 4 = 19 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 35 17 5 = 3 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 35 17 6 = 13 :=
    orbit_step hq h5 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 35 17 7 = 17 :=
    orbit_step hq h6 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 35 17 8 = 33 :=
    orbit_step hq h7 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, ?_⟩
  · show slopeOrbit 35 17 8 = slopeOrbit 35 17 1
    rw [h8, h1]
  · intro j hj1 hj7
    interval_cases j <;> simp_all

private theorem orbit_39_19_check :
    (∀ m, 1 ≤ m → slopeOrbit 39 19 (m + 8) = slopeOrbit 39 19 m)
    ∧ ∀ j, 1 ≤ j → j ≤ 8 → slopeOrbit 39 19 j ≠ 1 := by
  have hq : Odd 39 := ⟨19, by norm_num⟩
  have h0 : slopeOrbit 39 19 0 = 19 := rfl
  have h1 : slopeOrbit 39 19 1 = 37 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 39 19 2 = 35 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 39 19 3 = 31 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 39 19 4 = 23 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 39 19 5 = 7 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 39 19 6 = 17 :=
    orbit_step hq h5 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 39 19 7 = 29 :=
    orbit_step hq h6 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 39 19 8 = 19 :=
    orbit_step hq h7 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h9 : slopeOrbit 39 19 9 = 37 :=
    orbit_step hq h8 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, ?_⟩
  · show slopeOrbit 39 19 9 = slopeOrbit 39 19 1
    rw [h9, h1]
  · intro j hj1 hj8
    interval_cases j <;> simp_all

private theorem orbit_45_7_check :
    (∀ m, 1 ≤ m → slopeOrbit 45 7 (m + 7) = slopeOrbit 45 7 m)
    ∧ ∀ j, 1 ≤ j → j ≤ 7 → slopeOrbit 45 7 j ≠ 1 := by
  have hq : Odd 45 := ⟨22, by norm_num⟩
  have h0 : slopeOrbit 45 7 0 = 7 := rfl
  have h1 : slopeOrbit 45 7 1 = 11 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 45 7 2 = 43 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 45 7 3 = 41 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 45 7 4 = 37 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 45 7 5 = 29 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 45 7 6 = 13 :=
    orbit_step hq h5 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 45 7 7 = 7 :=
    orbit_step hq h6 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 45 7 8 = 11 :=
    orbit_step hq h7 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, ?_⟩
  · show slopeOrbit 45 7 8 = slopeOrbit 45 7 1
    rw [h8, h1]
  · intro j hj1 hj7
    interval_cases j <;> simp_all

private theorem orbit_45_22_check :
    (∀ m, 1 ≤ m → slopeOrbit 45 22 (m + 7) = slopeOrbit 45 22 m)
    ∧ ∀ j, 1 ≤ j → j ≤ 7 → slopeOrbit 45 22 j ≠ 1 := by
  have hq : Odd 45 := ⟨22, by norm_num⟩
  have h0 : slopeOrbit 45 22 0 = 22 := rfl
  have h1 : slopeOrbit 45 22 1 = 43 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 45 22 2 = 41 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 45 22 3 = 37 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 45 22 4 = 29 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 45 22 5 = 13 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 45 22 6 = 7 :=
    orbit_step hq h5 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 45 22 7 = 11 :=
    orbit_step hq h6 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 45 22 8 = 43 :=
    orbit_step hq h7 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, ?_⟩
  · show slopeOrbit 45 22 8 = slopeOrbit 45 22 1
    rw [h8, h1]
  · intro j hj1 hj7
    interval_cases j <;> simp_all

private theorem orbit_47_23_check :
    (∀ m, 1 ≤ m → slopeOrbit 47 23 (m + 14) = slopeOrbit 47 23 m)
    ∧ ∀ j, 1 ≤ j → j ≤ 14 → slopeOrbit 47 23 j ≠ 1 := by
  have hq : Odd 47 := ⟨23, by norm_num⟩
  have h0 : slopeOrbit 47 23 0 = 23 := rfl
  have h1 : slopeOrbit 47 23 1 = 45 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 47 23 2 = 43 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 47 23 3 = 39 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 47 23 4 = 31 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 47 23 5 = 15 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 47 23 6 = 13 :=
    orbit_step hq h5 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 47 23 7 = 5 :=
    orbit_step hq h6 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 47 23 8 = 33 :=
    orbit_step hq h7 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num) (by norm_num)
  have h9 : slopeOrbit 47 23 9 = 19 :=
    orbit_step hq h8 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h10 : slopeOrbit 47 23 10 = 29 :=
    orbit_step hq h9 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h11 : slopeOrbit 47 23 11 = 11 :=
    orbit_step hq h10 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h12 : slopeOrbit 47 23 12 = 41 :=
    orbit_step hq h11 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h13 : slopeOrbit 47 23 13 = 35 :=
    orbit_step hq h12 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h14 : slopeOrbit 47 23 14 = 23 :=
    orbit_step hq h13 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h15 : slopeOrbit 47 23 15 = 45 :=
    orbit_step hq h14 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, ?_⟩
  · show slopeOrbit 47 23 15 = slopeOrbit 47 23 1
    rw [h15, h1]
  · intro j hj1 hj14
    interval_cases j <;> simp_all

/-- `(21, 3)` closes by the divisor floor `d = 3` (no cycle computation). -/
theorem class0CycleDeepBandFree_of_datum_21_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    Class0CycleDeepBandFree ctx :=
  class0CycleDeepBandFree_of_datum_dvd_floor ctx hq hK 3 (by norm_num) (by norm_num)
    (by norm_num)

/-- `(21, 10)` closes by the period-`4` cycle `19, 17, 13, 5`. -/
theorem class0CycleDeepBandFree_of_datum_21_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    Class0CycleDeepBandFree ctx :=
  class0CycleDeepBandFree_of_datum_avoids_one ctx hq hK 4 (by norm_num) (by norm_num)
    (by norm_num) orbit_21_10_check.1 orbit_21_10_check.2

/-- `(23, 11)` closes by the period-`7` cycle `21, 19, 15, 7, 5, 17, 11`. -/
theorem class0CycleDeepBandFree_of_datum_23_11 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 23) (hK : (class1SlopeDatum ctx).K₀ = 11) :
    Class0CycleDeepBandFree ctx :=
  class0CycleDeepBandFree_of_datum_avoids_one ctx hq hK 7 (by norm_num) (by norm_num)
    (by norm_num) orbit_23_11_check.1 orbit_23_11_check.2

/-- `(31, 15)` closes by the period-`4` cycle `29, 27, 23, 15`. -/
theorem class0CycleDeepBandFree_of_datum_31_15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 31) (hK : (class1SlopeDatum ctx).K₀ = 15) :
    Class0CycleDeepBandFree ctx :=
  class0CycleDeepBandFree_of_datum_avoids_one ctx hq hK 4 (by norm_num) (by norm_num)
    (by norm_num) orbit_31_15_check.1 orbit_31_15_check.2

/-- `(33, 5)` closes by the period-`5` cycle `7, 23, 13, 19, 5`. -/
theorem class0CycleDeepBandFree_of_datum_33_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 5) :
    Class0CycleDeepBandFree ctx :=
  class0CycleDeepBandFree_of_datum_avoids_one ctx hq hK 5 (by norm_num) (by norm_num)
    (by norm_num) orbit_33_5_check.1 orbit_33_5_check.2

/-- `(35, 3)` closes by the period-`7` cycle `13, 17, 33, 31, 27, 19, 3`. -/
theorem class0CycleDeepBandFree_of_datum_35_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    Class0CycleDeepBandFree ctx :=
  class0CycleDeepBandFree_of_datum_avoids_one ctx hq hK 7 (by norm_num) (by norm_num)
    (by norm_num) orbit_35_3_check.1 orbit_35_3_check.2

/-- `(35, 17)` closes by the period-`7` cycle `33, 31, 27, 19, 3, 13, 17`. -/
theorem class0CycleDeepBandFree_of_datum_35_17 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 17) :
    Class0CycleDeepBandFree ctx :=
  class0CycleDeepBandFree_of_datum_avoids_one ctx hq hK 7 (by norm_num) (by norm_num)
    (by norm_num) orbit_35_17_check.1 orbit_35_17_check.2

/-- `(39, 6)` closes by the divisor floor `d = 3` (no cycle computation). -/
theorem class0CycleDeepBandFree_of_datum_39_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 6) :
    Class0CycleDeepBandFree ctx :=
  class0CycleDeepBandFree_of_datum_dvd_floor ctx hq hK 3 (by norm_num) (by norm_num)
    (by norm_num)

/-- `(39, 19)` closes by the period-`8` cycle `37, 35, 31, 23, 7, 17, 29, 19`. -/
theorem class0CycleDeepBandFree_of_datum_39_19 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 19) :
    Class0CycleDeepBandFree ctx :=
  class0CycleDeepBandFree_of_datum_avoids_one ctx hq hK 8 (by norm_num) (by norm_num)
    (by norm_num) orbit_39_19_check.1 orbit_39_19_check.2

/-- `(45, 7)` closes by the period-`7` cycle `11, 43, 41, 37, 29, 13, 7`. -/
theorem class0CycleDeepBandFree_of_datum_45_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 7) :
    Class0CycleDeepBandFree ctx :=
  class0CycleDeepBandFree_of_datum_avoids_one ctx hq hK 7 (by norm_num) (by norm_num)
    (by norm_num) orbit_45_7_check.1 orbit_45_7_check.2

/-- `(45, 22)` closes by the period-`7` cycle `43, 41, 37, 29, 13, 7, 11`. -/
theorem class0CycleDeepBandFree_of_datum_45_22 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 22) :
    Class0CycleDeepBandFree ctx :=
  class0CycleDeepBandFree_of_datum_avoids_one ctx hq hK 7 (by norm_num) (by norm_num)
    (by norm_num) orbit_45_22_check.1 orbit_45_22_check.2

/-- `(47, 23)` closes by the period-`14` cycle
`45, 43, 39, 31, 15, 13, 5, 33, 19, 29, 11, 41, 35, 23`. -/
theorem class0CycleDeepBandFree_of_datum_47_23 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 47) (hK : (class1SlopeDatum ctx).K₀ = 23) :
    Class0CycleDeepBandFree ctx :=
  class0CycleDeepBandFree_of_datum_avoids_one ctx hq hK 14 (by norm_num) (by norm_num)
    (by norm_num) orbit_47_23_check.1 orbit_47_23_check.2

/-! ## Part 9.  The nineteen surviving pairs: resolution and proved obstruction

Every pair of the two enumerations is either closed above or proved to put the deep value
`1` ON its cycle — so the survivor list is the EXACT obstruction boundary of the
window-free check below modulus `48`. -/

/-- **The wave-4 class-0 survivor list**: the nineteen datum pairs on `17 ≤ q < 48` whose
cycles provably contain the deep value `1`. -/
def Class0DatumSurvivor (ctx : ActualFailureContext) : Prop :=
  ((class1SlopeDatum ctx).q = 17 ∧ (class1SlopeDatum ctx).K₀ = 8)
  ∨ ((class1SlopeDatum ctx).q = 19 ∧ (class1SlopeDatum ctx).K₀ = 9)
  ∨ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 25 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 25 ∧ (class1SlopeDatum ctx).K₀ = 12)
  ∨ ((class1SlopeDatum ctx).q = 27 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 27 ∧ (class1SlopeDatum ctx).K₀ = 4)
  ∨ ((class1SlopeDatum ctx).q = 27 ∧ (class1SlopeDatum ctx).K₀ = 13)
  ∨ ((class1SlopeDatum ctx).q = 29 ∧ (class1SlopeDatum ctx).K₀ = 14)
  ∨ ((class1SlopeDatum ctx).q = 33 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 33 ∧ (class1SlopeDatum ctx).K₀ = 16)
  ∨ ((class1SlopeDatum ctx).q = 35 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 37 ∧ (class1SlopeDatum ctx).K₀ = 18)
  ∨ ((class1SlopeDatum ctx).q = 39 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 41 ∧ (class1SlopeDatum ctx).K₀ = 20)
  ∨ ((class1SlopeDatum ctx).q = 43 ∧ (class1SlopeDatum ctx).K₀ = 21)
  ∨ ((class1SlopeDatum ctx).q = 45 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 45 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 45 ∧ (class1SlopeDatum ctx).K₀ = 4)

/-- **The window resolution**: on `17 ≤ q < 48` every actual ctx is a survivor pair or its
window-free check HOLDS (twelve pairs closed, nineteen recorded). -/
theorem class0_datum_window_resolved (ctx : ActualFailureContext)
    (h17 : 17 ≤ (class1SlopeDatum ctx).q) (h48 : (class1SlopeDatum ctx).q < 48) :
    Class0DatumSurvivor ctx ∨ Class0CycleDeepBandFree ctx := by
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 32 with h32 | h32
  · rcases datum_mid_window_pairs (class1SlopeDatum ctx).hq_odd
      (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum_two_K₀_lt ctx)
      (class0_datum_dvd ctx) h17 h32 with
      h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inr (class0CycleDeepBandFree_of_datum_21_3 ctx h.1 h.2)
    · exact Or.inr (class0CycleDeepBandFree_of_datum_21_10 ctx h.1 h.2)
    · exact Or.inr (class0CycleDeepBandFree_of_datum_23_11 ctx h.1 h.2)
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inr (class0CycleDeepBandFree_of_datum_31_15 ctx h.1 h.2)
  · rcases datum_upper_window_pairs (class1SlopeDatum ctx).hq_odd
      (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum_two_K₀_lt ctx)
      (class0_datum_dvd ctx) h32 h48 with
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inr (class0CycleDeepBandFree_of_datum_33_5 ctx h.1 h.2)
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inr (class0CycleDeepBandFree_of_datum_35_3 ctx h.1 h.2)
    · exact Or.inr (class0CycleDeepBandFree_of_datum_35_17 ctx h.1 h.2)
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inr (class0CycleDeepBandFree_of_datum_39_6 ctx h.1 h.2)
    · exact Or.inr (class0CycleDeepBandFree_of_datum_39_19 ctx h.1 h.2)
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inl (by simp [Class0DatumSurvivor, h.1, h.2])
    · exact Or.inr (class0CycleDeepBandFree_of_datum_45_7 ctx h.1 h.2)
    · exact Or.inr (class0CycleDeepBandFree_of_datum_45_22 ctx h.1 h.2)
    · exact Or.inr (class0CycleDeepBandFree_of_datum_47_23 ctx h.1 h.2)

/-! ### The orbit-hits-one certificates for the surviving pairs -/

private theorem orbit_17_8_vals :
    slopeOrbit 17 8 1 = 15 ∧ slopeOrbit 17 8 2 = 13 ∧ slopeOrbit 17 8 3 = 9
    ∧ slopeOrbit 17 8 4 = 1 ∧ slopeOrbit 17 8 5 = 15 := by
  have hq : Odd 17 := ⟨8, by norm_num⟩
  have h0 : slopeOrbit 17 8 0 = 8 := rfl
  have h1 : slopeOrbit 17 8 1 = 15 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 17 8 2 = 13 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 17 8 3 = 9 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 17 8 4 = 1 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 17 8 5 = 15 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h1, h2, h3, h4, h5⟩

private theorem orbit_19_9_hits_one : slopeOrbit 19 9 6 = 1 := by
  have hq : Odd 19 := ⟨9, by norm_num⟩
  have h0 : slopeOrbit 19 9 0 = 9 := rfl
  have h1 : slopeOrbit 19 9 1 = 17 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 19 9 2 = 15 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 19 9 3 = 11 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 19 9 4 = 3 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 19 9 5 = 5 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  exact orbit_step hq h5 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
    (by norm_num)

private theorem orbit_21_1_vals :
    slopeOrbit 21 1 1 = 11 ∧ slopeOrbit 21 1 2 = 1 ∧ slopeOrbit 21 1 3 = 11 := by
  have hq : Odd 21 := ⟨10, by norm_num⟩
  have h0 : slopeOrbit 21 1 0 = 1 := rfl
  have h1 : slopeOrbit 21 1 1 = 11 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 21 1 2 = 1 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 21 1 3 = 11 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h1, h2, h3⟩

private theorem orbit_25_2_hits_one : slopeOrbit 25 2 10 = 1 := by
  have hq : Odd 25 := ⟨12, by norm_num⟩
  have h0 : slopeOrbit 25 2 0 = 2 := rfl
  have h1 : slopeOrbit 25 2 1 = 7 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 25 2 2 = 3 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 25 2 3 = 23 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 25 2 4 = 21 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 25 2 5 = 17 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 25 2 6 = 9 :=
    orbit_step hq h5 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 25 2 7 = 11 :=
    orbit_step hq h6 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 25 2 8 = 19 :=
    orbit_step hq h7 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h9 : slopeOrbit 25 2 9 = 13 :=
    orbit_step hq h8 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  exact orbit_step hq h9 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
    (by norm_num)

private theorem orbit_25_12_hits_one : slopeOrbit 25 12 8 = 1 := by
  have hq : Odd 25 := ⟨12, by norm_num⟩
  have h0 : slopeOrbit 25 12 0 = 12 := rfl
  have h1 : slopeOrbit 25 12 1 = 23 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 25 12 2 = 21 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 25 12 3 = 17 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 25 12 4 = 9 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 25 12 5 = 11 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 25 12 6 = 19 :=
    orbit_step hq h5 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 25 12 7 = 13 :=
    orbit_step hq h6 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  exact orbit_step hq h7 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
    (by norm_num)

private theorem orbit_27_4_hits_one : slopeOrbit 27 4 9 = 1 := by
  have hq : Odd 27 := ⟨13, by norm_num⟩
  have h0 : slopeOrbit 27 4 0 = 4 := rfl
  have h1 : slopeOrbit 27 4 1 = 5 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 27 4 2 = 13 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 27 4 3 = 25 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 27 4 4 = 23 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 27 4 5 = 19 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 27 4 6 = 11 :=
    orbit_step hq h5 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 27 4 7 = 17 :=
    orbit_step hq h6 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 27 4 8 = 7 :=
    orbit_step hq h7 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  exact orbit_step hq h8 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
    (by norm_num)

private theorem orbit_27_13_hits_one : slopeOrbit 27 13 7 = 1 := by
  have hq : Odd 27 := ⟨13, by norm_num⟩
  have h0 : slopeOrbit 27 13 0 = 13 := rfl
  have h1 : slopeOrbit 27 13 1 = 25 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 27 13 2 = 23 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 27 13 3 = 19 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 27 13 4 = 11 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 27 13 5 = 17 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 27 13 6 = 7 :=
    orbit_step hq h5 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  exact orbit_step hq h6 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
    (by norm_num)

private theorem orbit_29_14_hits_one : slopeOrbit 29 14 10 = 1 := by
  have hq : Odd 29 := ⟨14, by norm_num⟩
  have h0 : slopeOrbit 29 14 0 = 14 := rfl
  have h1 : slopeOrbit 29 14 1 = 27 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 29 14 2 = 25 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 29 14 3 = 21 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 29 14 4 = 13 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 29 14 5 = 23 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 29 14 6 = 17 :=
    orbit_step hq h5 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 29 14 7 = 5 :=
    orbit_step hq h6 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 29 14 8 = 11 :=
    orbit_step hq h7 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h9 : slopeOrbit 29 14 9 = 15 :=
    orbit_step hq h8 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  exact orbit_step hq h9 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
    (by norm_num)

private theorem orbit_33_16_hits_one : slopeOrbit 33 16 5 = 1 := by
  have hq : Odd 33 := ⟨16, by norm_num⟩
  have h0 : slopeOrbit 33 16 0 = 16 := rfl
  have h1 : slopeOrbit 33 16 1 = 31 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 33 16 2 = 29 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 33 16 3 = 25 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 33 16 4 = 17 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  exact orbit_step hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
    (by norm_num)

private theorem orbit_35_2_hits_one : slopeOrbit 35 2 5 = 1 := by
  have hq : Odd 35 := ⟨17, by norm_num⟩
  have h0 : slopeOrbit 35 2 0 = 2 := rfl
  have h1 : slopeOrbit 35 2 1 = 29 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 35 2 2 = 23 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 35 2 3 = 11 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 35 2 4 = 9 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  exact orbit_step hq h4 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
    (by norm_num)

private theorem orbit_37_18_hits_one : slopeOrbit 37 18 10 = 1 := by
  have hq : Odd 37 := ⟨18, by norm_num⟩
  have h0 : slopeOrbit 37 18 0 = 18 := rfl
  have h1 : slopeOrbit 37 18 1 = 35 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 37 18 2 = 33 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 37 18 3 = 29 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 37 18 4 = 21 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 37 18 5 = 5 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 37 18 6 = 3 :=
    orbit_step hq h5 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 37 18 7 = 11 :=
    orbit_step hq h6 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 37 18 8 = 7 :=
    orbit_step hq h7 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h9 : slopeOrbit 37 18 9 = 19 :=
    orbit_step hq h8 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  exact orbit_step hq h9 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
    (by norm_num)

private theorem orbit_41_20_hits_one : slopeOrbit 41 20 8 = 1 := by
  have hq : Odd 41 := ⟨20, by norm_num⟩
  have h0 : slopeOrbit 41 20 0 = 20 := rfl
  have h1 : slopeOrbit 41 20 1 = 39 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 41 20 2 = 37 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 41 20 3 = 33 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 41 20 4 = 25 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 41 20 5 = 9 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 41 20 6 = 31 :=
    orbit_step hq h5 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 41 20 7 = 21 :=
    orbit_step hq h6 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  exact orbit_step hq h7 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
    (by norm_num)

private theorem orbit_43_21_hits_one : slopeOrbit 43 21 6 = 1 := by
  have hq : Odd 43 := ⟨21, by norm_num⟩
  have h0 : slopeOrbit 43 21 0 = 21 := rfl
  have h1 : slopeOrbit 43 21 1 = 41 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 43 21 2 = 39 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 43 21 3 = 35 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 43 21 4 = 27 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 43 21 5 = 11 :=
    orbit_step hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  exact orbit_step hq h5 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
    (by norm_num)

private theorem orbit_45_2_hits_one : slopeOrbit 45 2 5 = 1 := by
  have hq : Odd 45 := ⟨22, by norm_num⟩
  have h0 : slopeOrbit 45 2 0 = 2 := rfl
  have h1 : slopeOrbit 45 2 1 = 19 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 45 2 2 = 31 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 45 2 3 = 17 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 45 2 4 = 23 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  exact orbit_step hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
    (by norm_num)

private theorem orbit_45_4_hits_one : slopeOrbit 45 4 5 = 1 := by
  have hq : Odd 45 := ⟨22, by norm_num⟩
  have h0 : slopeOrbit 45 4 0 = 4 := rfl
  have h1 : slopeOrbit 45 4 1 = 19 :=
    orbit_step hq h0 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 45 4 2 = 31 :=
    orbit_step hq h1 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 45 4 3 = 17 :=
    orbit_step hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 45 4 4 = 23 :=
    orbit_step hq h3 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  exact orbit_step hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
    (by norm_num)

/-- **Every surviving pair PROVABLY defeats the window-free check**: each of the nineteen
cycles contains the deep value `1` (odd-base closure at the base or an explicit orbit
certificate).  The survivor list is therefore the EXACT obstruction boundary of
`Class0CycleDeepBandFree` below modulus `48`. -/
theorem class0_datum_survivor_defeats_cycleCheck (ctx : ActualFailureContext)
    (h : Class0DatumSurvivor ctx) : ¬ Class0CycleDeepBandFree ctx := by
  simp only [Class0DatumSurvivor] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact not_class0CycleDeepBandFree_of_datum_orbit_deep ctx h.1 h.2 4 (by norm_num)
      (by rw [orbit_17_8_vals.2.2.2.1]; norm_num)
  · exact not_class0CycleDeepBandFree_of_datum_orbit_deep ctx h.1 h.2 6 (by norm_num)
      (by rw [orbit_19_9_hits_one]; norm_num)
  · exact not_class0CycleDeepBandFree_of_odd_small_base ctx
      (by rw [h.2]; exact ⟨0, by norm_num⟩) (by rw [h.1, h.2]; norm_num)
  · exact not_class0CycleDeepBandFree_of_datum_orbit_deep ctx h.1 h.2 10 (by norm_num)
      (by rw [orbit_25_2_hits_one]; norm_num)
  · exact not_class0CycleDeepBandFree_of_datum_orbit_deep ctx h.1 h.2 8 (by norm_num)
      (by rw [orbit_25_12_hits_one]; norm_num)
  · exact not_class0CycleDeepBandFree_of_odd_small_base ctx
      (by rw [h.2]; exact ⟨0, by norm_num⟩) (by rw [h.1, h.2]; norm_num)
  · exact not_class0CycleDeepBandFree_of_datum_orbit_deep ctx h.1 h.2 9 (by norm_num)
      (by rw [orbit_27_4_hits_one]; norm_num)
  · exact not_class0CycleDeepBandFree_of_datum_orbit_deep ctx h.1 h.2 7 (by norm_num)
      (by rw [orbit_27_13_hits_one]; norm_num)
  · exact not_class0CycleDeepBandFree_of_datum_orbit_deep ctx h.1 h.2 10 (by norm_num)
      (by rw [orbit_29_14_hits_one]; norm_num)
  · exact not_class0CycleDeepBandFree_of_odd_small_base ctx
      (by rw [h.2]; exact ⟨0, by norm_num⟩) (by rw [h.1, h.2]; norm_num)
  · exact not_class0CycleDeepBandFree_of_datum_orbit_deep ctx h.1 h.2 5 (by norm_num)
      (by rw [orbit_33_16_hits_one]; norm_num)
  · exact not_class0CycleDeepBandFree_of_datum_orbit_deep ctx h.1 h.2 5 (by norm_num)
      (by rw [orbit_35_2_hits_one]; norm_num)
  · exact not_class0CycleDeepBandFree_of_datum_orbit_deep ctx h.1 h.2 10 (by norm_num)
      (by rw [orbit_37_18_hits_one]; norm_num)
  · exact not_class0CycleDeepBandFree_of_odd_small_base ctx
      (by rw [h.2]; exact ⟨0, by norm_num⟩) (by rw [h.1, h.2]; norm_num)
  · exact not_class0CycleDeepBandFree_of_datum_orbit_deep ctx h.1 h.2 8 (by norm_num)
      (by rw [orbit_41_20_hits_one]; norm_num)
  · exact not_class0CycleDeepBandFree_of_datum_orbit_deep ctx h.1 h.2 6 (by norm_num)
      (by rw [orbit_43_21_hits_one]; norm_num)
  · exact not_class0CycleDeepBandFree_of_odd_small_base ctx
      (by rw [h.2]; exact ⟨0, by norm_num⟩) (by rw [h.1, h.2]; norm_num)
  · exact not_class0CycleDeepBandFree_of_datum_orbit_deep ctx h.1 h.2 5 (by norm_num)
      (by rw [orbit_45_2_hits_one]; norm_num)
  · exact not_class0CycleDeepBandFree_of_datum_orbit_deep ctx h.1 h.2 5 (by norm_num)
      (by rw [orbit_45_4_hits_one]; norm_num)

/-- **The window-free check is DECIDED below modulus `48`**: it holds IFF the actual datum
pair is not one of the nineteen survivors. -/
theorem class0CycleDeepBandFree_iff_not_survivor (ctx : ActualFailureContext)
    (h48 : (class1SlopeDatum ctx).q < 48) :
    Class0CycleDeepBandFree ctx ↔ ¬ Class0DatumSurvivor ctx := by
  constructor
  · intro hfree hsurv
    exact class0_datum_survivor_defeats_cycleCheck ctx hsurv hfree
  · intro hns
    rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 17 with h17 | h17
    · exact class0CycleDeepBandFree_of_modulus_lt_seventeen ctx h17
    · rcases class0_datum_window_resolved ctx h17 h48 with hs | hc
      · exact absurd hs hns
      · exact hc

/-- Non-survivor pinned closure on `q < 48` (the capstone field body per ctx). -/
theorem class0Pinned_of_datum_not_survivor (ctx : ActualFailureContext)
    (h48 : (class1SlopeDatum ctx).q < 48) (hns : ¬ Class0DatumSurvivor ctx) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_cycleCheck ctx
    ((class0CycleDeepBandFree_iff_not_survivor ctx h48).mpr hns)

/-! ## Part 10.  The window-residue exploits for the flagship survivors

For a surviving pair the deep cycle residues are EXPLICIT, so the windowed check reduces to
a start-congruence condition — the brief's window-position-vs-cycle-residue lever. -/

/-- **The `(17, 8)` window exploit**: the deep residues of the period-`4` cycle
`15, 13, 9, 1` are exactly the indices `4 ∣ k`, so if no floor-realizing window start is
divisible by `4`, the ctx closes. -/
theorem class0Pinned_of_datum_17_8_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 17) (hK : (class1SlopeDatum ctx).K₀ = 8)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      ¬ (4 ∣ k)) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) := by
  intro k hk hpins
  rw [hq, hK] at hpins
  have hfl := hpins.1
  have hdeep := hpins.2
  have hndvd := h k hk hfl
  have h0 : k % 4 ≠ 0 := fun hc => hndvd (Nat.dvd_of_mod_eq_zero hc)
  have hper : ∀ m, 1 ≤ m → slopeOrbit 17 8 (m + 4) = slopeOrbit 17 8 m := by
    apply slopeOrbit_period_of_return
    show slopeOrbit 17 8 5 = slopeOrbit 17 8 1
    rw [orbit_17_8_vals.2.2.2.2, orbit_17_8_vals.1]
  have hk1 : 1 ≤ k := n24_starts_pos ctx hk
  have hrep := slopeOrbit_cycleRep (by norm_num : (1:ℕ) ≤ 4) hper hk1
  have hcr : cycleRep 4 k = k % 4 := by
    unfold cycleRep
    rw [if_neg h0]
  rw [hrep, hcr] at hdeep
  have hmod : k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hmod with hm | hm | hm <;> rw [hm] at hdeep
  · rw [orbit_17_8_vals.1] at hdeep; omega
  · rw [orbit_17_8_vals.2.1] at hdeep; omega
  · rw [orbit_17_8_vals.2.2.1] at hdeep; omega

/-- **The `(21, 1)` window exploit**: the deep residues of the period-`2` cycle `11, 1` are
exactly the EVEN indices, so if no floor-realizing window start is even, the ctx closes. -/
theorem class0Pinned_of_datum_21_1_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      ¬ (2 ∣ k)) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) := by
  intro k hk hpins
  rw [hq, hK] at hpins
  have hfl := hpins.1
  have hdeep := hpins.2
  have hndvd := h k hk hfl
  have h0 : k % 2 ≠ 0 := fun hc => hndvd (Nat.dvd_of_mod_eq_zero hc)
  have hper : ∀ m, 1 ≤ m → slopeOrbit 21 1 (m + 2) = slopeOrbit 21 1 m := by
    apply slopeOrbit_period_of_return
    show slopeOrbit 21 1 3 = slopeOrbit 21 1 1
    rw [orbit_21_1_vals.2.2, orbit_21_1_vals.1]
  have hk1 : 1 ≤ k := n24_starts_pos ctx hk
  have hrep := slopeOrbit_cycleRep (by norm_num : (1:ℕ) ≤ 2) hper hk1
  have hcr : cycleRep 2 k = k % 2 := by
    unfold cycleRep
    rw [if_neg h0]
  rw [hrep, hcr] at hdeep
  have hm : k % 2 = 1 := by omega
  rw [hm, orbit_21_1_vals.1] at hdeep
  omega

/-! ## Part 11.  The field-level and capstone bridges

The capstone field follows from windowed checks ONLY on the nineteen surviving pairs plus
the `48 ≤ q` regime — strictly smaller than the wave-3 surface (`q ≥ 17` everywhere). -/

/-- **The field-level datum split**: windowed checks on the nineteen surviving pairs and on
`48 ≤ q` yield the capstone `class0Pinned` field verbatim. -/
theorem class0Pinned_field_of_datum_split
    (hsurv : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      Class0WindowCycleCheck ctx)
    (hbig : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
      Class0WindowCycleCheck ctx) :
    ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) := by
  intro ctx
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 48 with h48 | h48
  · by_cases hs : Class0DatumSurvivor ctx
    · exact class0Pinned_of_windowCycleCheck ctx (hsurv ctx hs)
    · exact class0Pinned_of_datum_not_survivor ctx h48 hs
  · exact class0Pinned_of_windowCycleCheck ctx (hbig ctx h48)

/-- **The capstone field from the datum split** (EXACTLY the `class0Cycle` field type of
`Erdos260CycleResidual`): windowed checks on the nineteen surviving pairs and on `48 ≤ q`
deliver `∀ ctx, Class0WindowCycleCheck ctx`. -/
theorem class0Cycle_of_datum_split
    (hsurv : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      Class0WindowCycleCheck ctx)
    (hbig : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
      Class0WindowCycleCheck ctx) :
    ∀ ctx : ActualFailureContext, Class0WindowCycleCheck ctx := fun ctx =>
  (class0Pinned_iff_windowCycleCheck ctx).mp
    (class0Pinned_field_of_datum_split hsurv hbig ctx)

/-- **The wave-2 residual from the datum split**: `Class0FibreEmpty` for every budget
routing through the genuine route, from the same two reduced hypotheses. -/
theorem class0FibreEmpty_of_datum_split
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hroute : ∀ ctx : ActualFailureContext, (budget ctx).route = genuineChargeRoute ctx)
    (hsurv : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      Class0WindowCycleCheck ctx)
    (hbig : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
      Class0WindowCycleCheck ctx) :
    Class0FibreEmpty budget :=
  class0FibreEmpty_of_genuineRoute_pinned budget hroute
    (class0Pinned_field_of_datum_split hsurv hbig)

/-! ## Part 12.  Machine-readable status (brutally honest) -/

/-- Honest machine-readable status of the wave-4 class-0 datum closure. -/
def chernoffClass0DatumClosureStatus : List String :=
  [ "TARGET (capstone field): Erdos260CycleResidual.class0Cycle - forall ctx, " ++
      "Class0WindowCycleCheck ctx (lossless for the wave-2 pinned field via the proved " ++
      "iff class0Pinned_field_iff_windowCycleCheck).",
    "NEW LEVER (proved): the datum divisor pin class0_datum_dvd - (2*K0+1) | q at every " ++
      "actual ctx, from class1SlopeDatum_H_dvd (H = 2|P|+1 divides q) and " ++
      "class1SlopeDatum_K0_eq (K0 = |P|).",
    "CLOSED (evaluation kit, NEW): canonGap_eq_of_bounds / boundedSlopeStep_eq_of_bounds " ++
      "- the band bounds q < 2^g*K < 2q determine the canonical gap, so explicit orbits " ++
      "are verified by numeral arithmetic; slopeOrbit_period_of_return iterates a first " ++
      "return into a full period.",
    "CLOSED (exact boundary, NEW): class0CycleDeepBandFree_iff_orbit_deepBand_free - the " ++
      "window-free check holds IFF the orbit misses the deep band at every positive " ++
      "index; hence every datum pair is decidably closed or decidably obstructed.",
    "CLOSED (q < 48 sharpening, NEW): window starts read the orbit at k >= 1 where it is " ++
      "ODD, and an odd deep value below 48 is 1 (deepBand_odd_eq_one_of_modulus_lt_48), " ++
      "so the avoid-1 reduction extends from the wave-3 window 17 <= q < 32 to " ++
      "17 <= q < 48 (class0CycleDeepBandFree_of_cycle_avoids_one_of_modulus_lt_48, " ++
      "class0Pinned_of_cycle_avoids_one_of_modulus_lt_48).",
    "CLOSED (datum enumerations, NEW): datum_mid_window_pairs - on 17 <= q < 32 the pin " ++
      "admits EXACTLY thirteen pairs (17,8),(19,9),(21,1),(21,3),(21,10),(23,11),(25,2)," ++
      "(25,12),(27,1),(27,4),(27,13),(29,14),(31,15); datum_upper_window_pairs - on " ++
      "32 <= q < 48 exactly eighteen: (33,1),(33,5),(33,16),(35,2),(35,3),(35,17),(37,18)," ++
      "(39,1),(39,6),(39,19),(41,20),(43,21),(45,1),(45,2),(45,4),(45,7),(45,22),(47,23).",
    "CLOSED (twelve per-pair checks, NEW): (21,3) and (39,6) by divisor floor d = 3; " ++
      "(21,10),(23,11),(31,15),(33,5),(35,3),(35,17),(39,19),(45,7),(45,22),(47,23) by " ++
      "explicit deep-band-free cycles (periods 4,7,4,5,7,7,8,7,7,14) - " ++
      "class0CycleDeepBandFree_of_datum_<q>_<K0>.",
    "CLOSED (K0-only datum criteria, NEW): datum_gcd_floor_forces_K_le_seven - under the " ++
      "pin gcd(q,K0)*(2K0+1) | q, so the no-cycle gcd-floor closure fires ONLY for " ++
      "K0 <= 7; class0CycleDeepBandFree_of_datum_product - the family q = K0*(2K0+1), " ++
      "K0 <= 7 closes outright, including (55,5) (class0Pinned_of_datum_55_5) and the " ++
      "tower fixed-point pair (105,7) (class0Pinned_of_datum_105_7) BEYOND q < 48.",
    "CLOSED (deep-base confinement, NEW): datum_deep_base_q_ge - any deep base " ++
      "16*K0 <= q under the pin forces q >= 7*(2K0+1) (quotient s >= 7); " ++
      "datum_odd_deep_base_pairs - in the boundary band q < 9*(2K0+1) exactly (21,1) and " ++
      "(49,3) survive: the datum confinement of the wave-3 odd-small-base obstruction.",
    "OBSTRUCTIONS PROVED (the honest boundary): class0_datum_survivor_defeats_cycleCheck " ++
      "- all NINETEEN surviving pairs put the deep value 1 ON their cycles (explicit " ++
      "orbit certificates; odd bases close at the base), so " ++
      "class0CycleDeepBandFree_iff_not_survivor DECIDES the window-free check below " ++
      "modulus 48: it holds iff the datum pair is not a survivor.  Survivors: (17,8) " ++
      "[1 at j=4], (19,9) [j=6], (21,1) [odd base], (25,2) [j=10], (25,12) [j=8], (27,1) " ++
      "[odd base], (27,4) [j=9], (27,13) [j=7], (29,14) [j=10], (33,1) [odd base], " ++
      "(33,16) [j=5], (35,2) [j=5], (37,18) [j=10], (39,1) [odd base], (41,20) [j=8], " ++
      "(43,21) [j=6], (45,1) [odd base], (45,2) [j=5], (45,4) [j=5].",
    "CLOSED (window-residue exploits, NEW - the brief's window lever): " ++
      "class0Pinned_of_datum_17_8_window - the deep residues of (17,8) are EXACTLY " ++
      "4 | k, so no floor-realizing start divisible by 4 closes the ctx; " ++
      "class0Pinned_of_datum_21_1_window - for (21,1) the deep residues are the even " ++
      "starts.  The surviving content on a survivor shell is exactly such a congruence " ++
      "miss at floor-realizing starts.",
    "BRIDGES (NEW, strictly smaller residual): class0Pinned_of_datum_not_survivor " ++
      "(q < 48 non-survivors closed outright), class0Pinned_field_of_datum_split " ++
      "(capstone pinned field from windowed checks ONLY on survivors + 48 <= q), " ++
      "class0Cycle_of_datum_split (EXACTLY the capstone field type forall ctx, " ++
      "Class0WindowCycleCheck ctx), class0FibreEmpty_of_datum_split (wave-2 residual for " ++
      "every genuine-route budget).  The wave-3 surface needed the windowed check on " ++
      "EVERY q >= 17 shell; wave 4 needs it only on the nineteen survivor pairs and " ++
      "q >= 48.",
    "NOT CLOSED (the honest wave-4 residual): the atom itself.  On the nineteen " ++
      "survivor pairs the deep band sits ON the cycle, and for q >= 48 deep odd values " ++
      "3, 5, ... become admissible (the enumeration is not extended past 48 here); no " ++
      "formalized hitGap <-> canonGap bridge exists at the actual ctx, and the pressure " ++
      "floor forbids proving all classes empty.  The exact remaining surface is: the " ++
      "windowed check Class0WindowCycleCheck on survivor shells (a start-congruence miss " ++
      "as in the flagship exploits) and on 48 <= q shells.  We do NOT claim " ++
      "unconditional closure of the atom." ]

theorem chernoffClass0DatumClosureStatus_nonempty :
    chernoffClass0DatumClosureStatus ≠ [] := by
  simp [chernoffClass0DatumClosureStatus]

/-! ## Part 13.  Axiom-cleanliness audit -/

#print axioms class0_datum_dvd
#print axioms canonGap_eq_of_bounds
#print axioms boundedSlopeStep_eq_of_bounds
#print axioms slopeOrbit_period_of_return
#print axioms class0CycleDeepBandFree_iff_orbit_deepBand_free
#print axioms not_class0CycleDeepBandFree_of_datum_orbit_deep
#print axioms class0CycleDeepBandFree_of_modulus_lt_seventeen
#print axioms class0CycleDeepBandFree_of_dvd_floor
#print axioms class0CycleDeepBandFree_of_datum_dvd_floor
#print axioms class0CycleDeepBandFree_of_datum_product
#print axioms class0Pinned_of_datum_product
#print axioms class0Pinned_of_datum_55_5
#print axioms class0Pinned_of_datum_105_7
#print axioms datum_gcd_floor_forces_K_le_seven
#print axioms class0_datum_gcd_floor_K₀_le_seven
#print axioms datum_deep_base_q_ge
#print axioms class0_datum_deep_base_q_ge
#print axioms datum_odd_deep_base_pairs
#print axioms class0_datum_odd_deep_base_pairs
#print axioms deepBand_odd_eq_one_of_modulus_lt_48
#print axioms class0CycleDeepBandFree_of_cycle_avoids_one_of_modulus_lt_48
#print axioms class0Pinned_of_cycle_avoids_one_of_modulus_lt_48
#print axioms class0CycleDeepBandFree_of_datum_avoids_one
#print axioms datum_mid_window_pairs
#print axioms datum_upper_window_pairs
#print axioms class0CycleDeepBandFree_of_datum_21_3
#print axioms class0CycleDeepBandFree_of_datum_21_10
#print axioms class0CycleDeepBandFree_of_datum_23_11
#print axioms class0CycleDeepBandFree_of_datum_31_15
#print axioms class0CycleDeepBandFree_of_datum_33_5
#print axioms class0CycleDeepBandFree_of_datum_35_3
#print axioms class0CycleDeepBandFree_of_datum_35_17
#print axioms class0CycleDeepBandFree_of_datum_39_6
#print axioms class0CycleDeepBandFree_of_datum_39_19
#print axioms class0CycleDeepBandFree_of_datum_45_7
#print axioms class0CycleDeepBandFree_of_datum_45_22
#print axioms class0CycleDeepBandFree_of_datum_47_23
#print axioms class0_datum_window_resolved
#print axioms class0_datum_survivor_defeats_cycleCheck
#print axioms class0CycleDeepBandFree_iff_not_survivor
#print axioms class0Pinned_of_datum_not_survivor
#print axioms class0Pinned_of_datum_17_8_window
#print axioms class0Pinned_of_datum_21_1_window
#print axioms class0Pinned_field_of_datum_split
#print axioms class0Cycle_of_datum_split
#print axioms class0FibreEmpty_of_datum_split
#print axioms chernoffClass0DatumClosureStatus_nonempty

end

end Erdos260
