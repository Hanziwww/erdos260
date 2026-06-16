import Erdos260.TowerCycleDensity
import Erdos260.CNLClass1DeepClosure

/-!
# Tower / Class 2, wave 4 — the datum-confined band-4 fixed point

This module (NEW; it edits no existing file) attacks the wave-3 capstone field

`towerSplit : ∀ ctx, towerShallowDepthBound < shellLadderDepth ctx →
    (class1SlopeDatum ctx).q < 9 ∨ (16 < q ∧ q < 25) ∨ Class2CycleInequality ctx`

with the wave-4 central lever: the orbit datum `(q, K₀)` is NOT arbitrary — it carries the
proved divisor pin `2·K₀ + 1 ∣ q` (`class1SlopeDatum_H_dvd` + `class1SlopeDatum_K₀_eq`,
named here `class1SlopeDatum_pin`).

## What is proved here (all unconditional theorems about the actual datum)

1. **The all-band-4 fixed point is datum-confined to THREE explicit pairs**
   (`towerFixedPoint_pairs_core`, `towerFixedPoint_pairs_of_step`,
   `towerFixedPoint_datum_confined`, `towerCycle_band4_full_datum_confined`): the wave-3
   dichotomy says a band-4-full period forces `15·K₁ = q` (`towerCycle_band4_full_forces_fixed`).
   Writing `K₁ = 2^g·K₀ − q` (one E.13 step, `g = canonGap q K₀`, so `2^g·K₀ = 16·K₁` with `K₁`
   odd) and intersecting with the divisor pin `2·K₀ + 1 ∣ q = 15·K₁` leaves EXACTLY

   `(q, K₀) ∈ {(15, 1), (15, 2), (105, 7)}`

   — the parent's sketch `{(15,1), (105,7)}` (odd `K₀`, step exponent `g = 4`) PLUS the
   even-`K₀` one-step tail `(15, 2)` (`g = 3`; the orbit is odd from index `1`, so the
   pre-period tail has length at most one and the exponent analysis `g + ord₂(K₀) = 4`
   covers it).  The exponents `g ∈ {1, 2}` (tails `K₀ = 4·K₁, 8·K₁`) are killed by the pin:
   `8·K₁ + 1 ∣ 15` and `16·K₁ + 1 ∣ 15` have no admissible solution.
2. **Off `q ∈ {15, 105}` the band-4 cycle density is strictly below 1 at the actual datum**
   (`towerBand4CycleCount_lt_of_datum_off`): `b4 < c` for EVERY period of the actual orbit.
3. **The surviving pairs are genuinely the fixed family, characterized exactly**:
   * `(15, 1), (15, 2)`: `K₁ = 1` and every positive index reads band 4
     (`towerFP15_fixed_band4`); `(105, 7)`: the orbit is constant `= 7 = 105/15`, every
     positive index reads band 4 (`towerFP105_fixed_band4`).
   * The datum arithmetic pins the target denominator: at `(15, 1)` the odd part of the
     actual `Q` is EXACTLY `5`; at `(15, 2)` it is `3`; at `(105, 7)` it is `7`
     (`towerFP15_1_oddpartQ`, `towerFP15_2_oddpartQ`, `towerFP105_7_oddpartQ`, via
     `q = ordCompl[2] (Q·(2K₀+1)) = ordCompl[2] Q · (2K₀+1)`).  These pairs CANNOT be refuted
     by further datum arithmetic alone: `Q` (hence its odd part) is a free model parameter
     (`η = P/Q` with `P = K₀`), so the three shapes remain the honest open fixed family.
4. **New datum-driven modulus closures of the towerSplit surface** (the divisor pin makes
   each odd modulus carry a FINITE explicit list of admissible `K₀`):
   * `q = 11` forces `K₀ = 5` (`towerFP11_K₀_eq`); the orbit cycle is `9 → 7 → 3 → 1 → 5`
     (period 5, band-4 count 1), closing the cycle inequality for every `m₀ ≤ 4`, i.e. all
     shells with `r ≤ 84` (`class2CycleInequality_of_modulus_eleven`).
   * `q = 13` forces `K₀ = 6`; cycle `11 → 9 → 5 → 7 → 1 → 3` (period 6, band-4 count 1),
     closing every `m₀ ≤ 5`, i.e. `r ≤ 106` (`class2CycleInequality_of_modulus_thirteen`).
   * `q = 15` forces `K₀ ∈ {1, 2, 7}` (`towerFP15_K₀_cases`); `K₀ = 7` rides the band-4-free
     cycle `13 → 11 → 7` — the fibre is EMPTY and the cycle inequality holds at every `m₀`
     (`class2CycleInequality_of_q15_K₀7`, `towerFP15_fibre_empty_of_K₀_ge_three`); the
     surviving `q = 15` family is EXACTLY `K₀ ≤ 2`, the fixed point.
   * `q = 105` forces `K₀ ∈ {1, 2, 3, 7, 10, 17, 52}` (`towerFP105_K₀_cases`); the five
     values `{1, 2, 3, 10, 17}` ride band-4-free cycles (`23 → 79 → 53 → 1` for `1, 2`;
     `87 → 69 → 33 → 27 → 3`; `55 → 5`; `31 → 19 → 47 → 83 → 61 → 17`) — fibre EMPTY, cycle
     inequality at every `m₀` (`towerFP105_fibre_empty_offFixed`); `K₀ = 52` rides the
     period-8 cycle `103 → 101 → 97 → 89 → 73 → 41 → 59 → 13` with band-4 count 1, closing
     every `m₀ ≤ 7`, i.e. `r ≤ 148` (`class2CycleInequality_of_q105_K₀52`); `K₀ = 7` is the
     fixed point.
5. **The general cycle-inequality criteria** (the wave-3 rounding, sharpened):
   `towerCycleRounding` — `m·b·(K + c − 1) ≤ K·c` discharges the exact ceiling inequality
   `m·(b·⌈K/c⌉) ≤ K` (no half-density slack lost); the collision-form builders
   `class2CycleInequality_of_collision_count` / `class2CycleInequality_of_collision_free` /
   `class2Fibre_empty_of_collision_free` turn one explicit orbit collision plus a per-cycle
   band count into the capstone-facing inequality.
6. **The ord₂ cycle-sum relation** (criteria infrastructure for later waves):
   `towerCycle_gapSum_relation` — telescoping one period gives `2^G·K₁ = K₁ + q·S`, hence
   `q ∣ (2^G − 1)·K₁` (`towerCycle_modulus_dvd_gapSum`) with `G = Σ canonGap` over the cycle
   and `G ≥ c + 3·b4` (`towerCycle_gapSum_ge`).
7. **The strictly smaller residual + the exact capstone bridge**: `TowerFixedPointResidual`
   demands the cycle inequality ONLY on the escape surface `TowerEscape` (q = 9 with m₀ ≥ 3;
   q = 11 with m₀ ≥ 5; q = 13 with m₀ ≥ 6; q = 15 on the fixed pair K₀ ≤ 2; q = 105 on
   K₀ = 7 or m₀ ≥ 8; and the un-enumerated moduli 25 ≤ q ≠ 105).
   `towerSplit_of_fixedPointResidual` rebuilds VERBATIM the capstone `towerSplit` field;
   `towerCountBound_of_fixedPointResidual` discharges `Class2DeepShellCountBound` through the
   existing wave-3 bridge; `towerFixedPointResidual_of_cycleDensity` witnesses that the new
   residual is no stronger than the wave-3 `Class2CycleDensityResidual`.

## Honesty — what is NOT closed

* The fixed pairs `(15, 1), (15, 2), (105, 7)` (equivalently: odd part of `Q` in `{5, 3, 7}`
  with `P = K₀`) keep `b4 = c` on every period; cycle counting cannot bound their fibres, and
  no formalized digit-orbit bridge (hitGap ↔ canonGap beyond the shared index) exists to
  refute them.  They are isolated and characterized, not closed.
* The counted families keep escape regimes: `q = 9` with `m₀ ≥ 3` (`r ≥ 42`), `q = 11` with
  `m₀ ≥ 5` (`r ≥ 85`), `q = 13` with `m₀ ≥ 6` (`r ≥ 107`), `(105, 52)` with `m₀ ≥ 8`
  (`r ≥ 149`) — there the demanded density `1/m₀` falls below the cycle density `b4/c` and
  the count bound needs new (digit-side or window-side) input.
* Odd moduli `25 ≤ q ∉ {105}` are not enumerated here (each carries its own finite
  pin-admissible `K₀` list and explicit orbit tables; the method extends mechanically).

No `sorry`, `admit`, `axiom`, or `native_decide`.  No degenerate witnesses: every theorem is
about the genuine `class1SlopeDatum` of the actual failing-shell context, with the genuine
routed class-2 fibre.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The divisor pin at the actual datum -/

/-- **The closed-datum divisor pin**: `2·K₀ + 1 ∣ q` at the actual orbit datum — the odd AP
modulus `H = 2|P| + 1` divides the slope modulus and the base numerator is `K₀ = |P|`. -/
theorem class1SlopeDatum_pin (ctx : ActualFailureContext) :
    2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
  rw [class1SlopeDatum_K₀_eq ctx]
  exact class1SlopeDatum_H_dvd ctx

/-! ## Part 2.  Collision-form cycle-inequality builders and the exact rounding -/

/-- A single orbit collision `K_{1+c} = K₁` is a period valid from index `1`. -/
theorem slopeOrbit_collision_period {q K₀ c : ℕ}
    (hcol : slopeOrbit q K₀ (1 + c) = slopeOrbit q K₀ 1) :
    ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m := by
  intro m hm
  have hshift := slopeOrbit_eq_shift hcol (m - 1)
  rwa [show 1 + c + (m - 1) = m + c by omega, show 1 + (m - 1) = m by omega] at hshift

/-- **The exact rounding of the ceiling inequality**: `m·b·(K + c − 1) ≤ K·c` discharges
`m·(b·⌈K/c⌉) ≤ K` (`⌈K/c⌉ = (K + c − 1)/c` in ℕ) — no half-density slack is lost. -/
theorem towerCycleRounding {m b c K : ℕ} (hc : 1 ≤ c)
    (h : m * b * (K + c - 1) ≤ K * c) :
    m * (b * ((K + c - 1) / c)) ≤ K := by
  have ht : (K + c - 1) / c * c ≤ K + c - 1 := Nat.div_mul_le_self _ _
  have h1 : m * (b * ((K + c - 1) / c)) * c ≤ K * c := by
    have h2 : m * (b * ((K + c - 1) / c)) * c = m * b * ((K + c - 1) / c * c) := by ring
    have h3 : m * b * ((K + c - 1) / c * c) ≤ m * b * (K + c - 1) :=
      Nat.mul_le_mul_left _ ht
    omega
  exact Nat.le_of_mul_le_mul_right h1 (by omega)

/-- **The collision-and-count builder**: one explicit orbit collision at the actual datum,
a per-cycle band-4 count bound `b4 ≤ b`, and the linear numeric `m₀·b·(K + c − 1) ≤ K·c`
yield the capstone cycle inequality. -/
theorem class2CycleInequality_of_collision_count (ctx : ActualFailureContext) {q K₀ c b : ℕ}
    (hq : (class1SlopeDatum ctx).q = q) (hK₀ : (class1SlopeDatum ctx).K₀ = K₀)
    (hc : 1 ≤ c)
    (hcol : slopeOrbit q K₀ (1 + c) = slopeOrbit q K₀ 1)
    (hcount : towerBand4CycleCount q K₀ c ≤ b)
    (hnum : towerSparsityBlock ctx * b * (shellWidth ctx + c - 1) ≤ shellWidth ctx * c) :
    Class2CycleInequality ctx := by
  subst hq
  subst hK₀
  refine ⟨c, hc, slopeOrbit_collision_period hcol, ?_⟩
  have hceil : towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c
        * ((shellWidth ctx + c - 1) / c)
      ≤ b * ((shellWidth ctx + c - 1) / c) := Nat.mul_le_mul_right _ hcount
  have hround : towerSparsityBlock ctx * (b * ((shellWidth ctx + c - 1) / c))
      ≤ shellWidth ctx := towerCycleRounding hc hnum
  exact le_trans (Nat.mul_le_mul_left _ hceil) hround

/-- **The collision-and-band-free builder**: one explicit orbit collision whose period avoids
band 4 yields the cycle inequality at EVERY sparsity block (count `0`). -/
theorem class2CycleInequality_of_collision_free (ctx : ActualFailureContext) {q K₀ c : ℕ}
    (hq : (class1SlopeDatum ctx).q = q) (hK₀ : (class1SlopeDatum ctx).K₀ = K₀)
    (hc : 1 ≤ c)
    (hcol : slopeOrbit q K₀ (1 + c) = slopeOrbit q K₀ 1)
    (hband : ∀ j, 1 ≤ j → j ≤ c → canonGap q (slopeOrbit q K₀ j) ≠ 4) :
    Class2CycleInequality ctx := by
  subst hq
  subst hK₀
  exact class2CycleInequality_of_band_free ctx hc (slopeOrbit_collision_period hcol) hband

/-- **The collision-and-band-free fibre emptiness**: the same data EMPTIES the class-2 routed
fibre outright. -/
theorem class2Fibre_empty_of_collision_free (ctx : ActualFailureContext) {q K₀ c : ℕ}
    (hq : (class1SlopeDatum ctx).q = q) (hK₀ : (class1SlopeDatum ctx).K₀ = K₀)
    (hc : 1 ≤ c)
    (hcol : slopeOrbit q K₀ (1 + c) = slopeOrbit q K₀ 1)
    (hband : ∀ j, 1 ≤ j → j ≤ c → canonGap q (slopeOrbit q K₀ j) ≠ 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ := by
  subst hq
  subst hK₀
  exact class2Fibre_empty_of_cycle_band_free ctx hc (slopeOrbit_collision_period hcol) hband

/-! ## Part 3.  The all-band-4 fixed point is datum-confined to three explicit pairs

The wave-3 dichotomy (`towerCycle_band4_full_forces_fixed`) turns a band-4-full period into
the fixed point `15·K₁ = q` at index `1`.  One E.13 step `K₁ = 2^g·K₀ − q` plus the canonical
band bounds give `2^g·K₀ = 16·K₁` with `K₁` odd, and the divisor pin `2·K₀ + 1 ∣ q = 15·K₁`
forces `(q, K₀) ∈ {(15, 1), (15, 2), (105, 7)}` — the odd-`K₀` pairs of the parent's sketch
PLUS the even-`K₀` one-step tail `(15, 2)`. -/

/-- A pin of the shape `c·K + 1 ∣ 15·K` divides `15` (the `+1` makes it coprime to `K`). -/
theorem pin_dvd_fifteen {c K : ℕ} (h : c * K + 1 ∣ 15 * K) : c * K + 1 ∣ 15 := by
  have h1 : c * K + 1 ∣ 15 * (c * K + 1) := dvd_mul_left (c * K + 1) 15
  have h2 : c * K + 1 ∣ c * (15 * K) := h.mul_left c
  have hee : 15 * (c * K + 1) = c * (15 * K) + 15 := by ring
  have hsub := Nat.dvd_sub h1 h2
  rwa [hee, Nat.add_sub_cancel_left] at hsub

/-- **The fixed-point pair arithmetic**: `2^g·K₀ = 16·K₁` (one E.13 step into the fixed
point) with `K₁` odd, `g ≥ 1`, and the divisor pin `2·K₀ + 1 ∣ 15·K₁` leaves exactly
`(K₁, K₀) ∈ {(1, 1), (1, 2), (7, 7)}`. -/
theorem towerFixedPoint_pairs_core {K₀ K₁ g : ℕ} (hK0 : 1 ≤ K₀) (hodd : Odd K₁)
    (hg : 1 ≤ g) (hpow : 2 ^ g * K₀ = 16 * K₁)
    (hdvd : 2 * K₀ + 1 ∣ 15 * K₁) :
    (K₁ = 1 ∧ K₀ = 1) ∨ (K₁ = 1 ∧ K₀ = 2) ∨ (K₁ = 7 ∧ K₀ = 7) := by
  have hK₁2 : K₁ % 2 = 1 := Nat.odd_iff.mp hodd
  have hK₁pos : 1 ≤ K₁ := by omega
  rcases Nat.lt_or_ge g 5 with hg5 | hg5
  · interval_cases g
    · -- g = 1: K₀ = 8·K₁, pin 16·K₁ + 1 ∣ 15 — impossible
      exfalso
      have hK : K₀ = 8 * K₁ := by norm_num at hpow; omega
      subst hK
      have hdvd' : 16 * K₁ + 1 ∣ 15 * K₁ := by
        have he : 2 * (8 * K₁) + 1 = 16 * K₁ + 1 := by ring
        rwa [he] at hdvd
      have h15 := pin_dvd_fifteen hdvd'
      have hle := Nat.le_of_dvd (by norm_num) h15
      omega
    · -- g = 2: K₀ = 4·K₁, pin 8·K₁ + 1 ∣ 15 — impossible
      exfalso
      have hK : K₀ = 4 * K₁ := by norm_num at hpow; omega
      subst hK
      have hdvd' : 8 * K₁ + 1 ∣ 15 * K₁ := by
        have he : 2 * (4 * K₁) + 1 = 8 * K₁ + 1 := by ring
        rwa [he] at hdvd
      have h15 := pin_dvd_fifteen hdvd'
      have hle := Nat.le_of_dvd (by norm_num) h15
      have hK1eq : K₁ = 1 := by omega
      subst hK1eq
      exact absurd h15 (by norm_num)
    · -- g = 3: K₀ = 2·K₁, pin 4·K₁ + 1 ∣ 15 — only K₁ = 1, the even tail (15, 2)
      have hK : K₀ = 2 * K₁ := by norm_num at hpow; omega
      subst hK
      have hdvd' : 4 * K₁ + 1 ∣ 15 * K₁ := by
        have he : 2 * (2 * K₁) + 1 = 4 * K₁ + 1 := by ring
        rwa [he] at hdvd
      have h15 := pin_dvd_fifteen hdvd'
      have hle := Nat.le_of_dvd (by norm_num) h15
      have hK1le : K₁ ≤ 3 := by omega
      interval_cases K₁
      · exact Or.inr (Or.inl ⟨rfl, by norm_num⟩)
      · omega
      · exact absurd h15 (by norm_num)
    · -- g = 4: K₀ = K₁ odd, pin 2·K₁ + 1 ∣ 15 — exactly K₁ ∈ {1, 7}
      have hK : K₀ = K₁ := by norm_num at hpow; omega
      have hdvd' : 2 * K₁ + 1 ∣ 15 * K₁ := by rwa [hK] at hdvd
      have h15 := pin_dvd_fifteen hdvd'
      have hle := Nat.le_of_dvd (by norm_num) h15
      have hK1le : K₁ ≤ 7 := by omega
      interval_cases K₁
      · exact Or.inl ⟨rfl, by omega⟩
      · omega
      · exact absurd h15 (by norm_num)
      · omega
      · exact absurd h15 (by norm_num)
      · omega
      · exact Or.inr (Or.inr ⟨rfl, by omega⟩)
  · -- g ≥ 5: the step value 2^{g-4}·K₀ = K₁ would be even — impossible
    exfalso
    obtain ⟨t, rfl⟩ : ∃ t, g = 5 + t := ⟨g - 5, by omega⟩
    rw [pow_add] at hpow
    have h32 : (2 : ℕ) ^ 5 = 32 := by norm_num
    rw [h32, Nat.mul_assoc] at hpow
    omega

/-- **The fixed-point datum confinement (one-step form)**: an odd modulus, the divisor pin,
and the fixed point at index `1` (`15·K₁ = q`) force `(q, K₀) ∈ {(15,1), (15,2), (105,7)}`. -/
theorem towerFixedPoint_pairs_of_step {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀) (hKq : K₀ < q)
    (hdvd : 2 * K₀ + 1 ∣ q)
    (hfix : 15 * slopeOrbit q K₀ 1 = q) :
    (q = 15 ∧ K₀ = 1) ∨ (q = 15 ∧ K₀ = 2) ∨ (q = 105 ∧ K₀ = 7) := by
  have hodd1 : Odd (slopeOrbit q K₀ 1) := slopeOrbit_odd hq hK1 hKq 1 le_rfl
  have hbounds := canonGap_bounds hq hK1 hKq
  have hKval : slopeOrbit q K₀ 1 = 2 ^ canonGap q K₀ * K₀ - q := rfl
  have hpow : 2 ^ canonGap q K₀ * K₀ = 16 * slopeOrbit q K₀ 1 := by omega
  have hg : 1 ≤ canonGap q K₀ := canonGap_pos q K₀
  have hdvd15 : 2 * K₀ + 1 ∣ 15 * slopeOrbit q K₀ 1 := by rwa [hfix]
  rcases towerFixedPoint_pairs_core hK1 hodd1 hg hpow hdvd15 with h | h | h
  · exact Or.inl ⟨by omega, h.2⟩
  · exact Or.inr (Or.inl ⟨by omega, h.2⟩)
  · exact Or.inr (Or.inr ⟨by omega, h.2⟩)

/-- **The fixed-point datum confinement at the ACTUAL datum**: if the actual orbit sits on
the `1/15` fixed point at index `1`, then `(q, K₀) ∈ {(15,1), (15,2), (105,7)}`. -/
theorem towerFixedPoint_datum_confined (ctx : ActualFailureContext)
    (hfix : 15 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1
        = (class1SlopeDatum ctx).q) :
    ((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 1)
    ∨ ((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 2)
    ∨ ((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 7) :=
  towerFixedPoint_pairs_of_step (class1SlopeDatum ctx).hq_odd
    (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum ctx).hK₀_lt
    (class1SlopeDatum_pin ctx) hfix

/-- **The all-band-4 cycle is datum-confined**: a band-4-full period of the ACTUAL orbit
forces `(q, K₀) ∈ {(15,1), (15,2), (105,7)}` — the wave-3 obstruction family collapses to
three explicit datum pairs. -/
theorem towerCycle_band4_full_datum_confined (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hall : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 4) :
    ((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 1)
    ∨ ((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 2)
    ∨ ((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 7) :=
  towerFixedPoint_datum_confined ctx
    (towerCycle_band4_full_forces_fixed (class1SlopeDatum ctx).hq_odd
      (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum ctx).hK₀_lt hc hper hall)

/-- **Off `q ∈ {15, 105}` the band-4 cycle count is strictly below the period at the actual
datum**: cycle density `1` needs a confined pair, and every confined pair has
`q ∈ {15, 105}`. -/
theorem towerBand4CycleCount_lt_of_datum_off (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (h15 : (class1SlopeDatum ctx).q ≠ 15) (h105 : (class1SlopeDatum ctx).q ≠ 105) :
    towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c < c := by
  refine towerBand4CycleCount_lt_of_not_fixed (class1SlopeDatum ctx).hq_odd
    (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum ctx).hK₀_lt hc hper ?_
  intro hfix
  rcases towerFixedPoint_datum_confined ctx hfix with h | h | h
  · exact h15 h.1
  · exact h15 h.1
  · exact h105 h.1

/-! ## Part 4.  The ord₂ cycle-sum relation (criteria infrastructure)

Telescoping the E.13 step `K_{j+1} = 2^{g_j}·K_j − q` over one period gives
`2^G·K₁ = K₁ + q·S` with `G = Σ canonGap` over the cycle, hence `q ∣ (2^G − 1)·K₁`;
and `G ≥ c + 3·b4` (band-4 positions contribute `4`, all others at least `1`). -/

/-- **The gap-sum telescoping**: for every `j`,
`2^{Σ_{i∈[1,j]} g_i}·K₁ = K_{j+1} + q·S` for some `S : ℕ`. -/
theorem towerCycle_gapSum_relation {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀) (hKq : K₀ < q) :
    ∀ j : ℕ, ∃ S : ℕ,
      2 ^ (∑ i ∈ Finset.Icc 1 j, canonGap q (slopeOrbit q K₀ i)) * slopeOrbit q K₀ 1
        = slopeOrbit q K₀ (j + 1) + q * S := by
  intro j
  induction j with
  | zero =>
      refine ⟨0, ?_⟩
      have h0 : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
      rw [h0, Finset.sum_empty, pow_zero, one_mul, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
      obtain ⟨S, hS⟩ := ih
      refine ⟨2 ^ canonGap q (slopeOrbit q K₀ (n + 1)) * S + 1, ?_⟩
      have hsum : (∑ i ∈ Finset.Icc 1 (n + 1), canonGap q (slopeOrbit q K₀ i))
          = (∑ i ∈ Finset.Icc 1 n, canonGap q (slopeOrbit q K₀ i))
            + canonGap q (slopeOrbit q K₀ (n + 1)) :=
        Finset.sum_Icc_succ_top (by omega) _
      have hmem := slopeOrbit_mem hq hK1 hKq (n + 1)
      have hlow := (canonGap_bounds hq hmem.1 hmem.2).1
      have hstep2 : 2 ^ canonGap q (slopeOrbit q K₀ (n + 1)) * slopeOrbit q K₀ (n + 1)
          = slopeOrbit q K₀ (n + 1 + 1) + q := by
        have hKval : slopeOrbit q K₀ (n + 1 + 1)
            = 2 ^ canonGap q (slopeOrbit q K₀ (n + 1)) * slopeOrbit q K₀ (n + 1) - q := rfl
        omega
      calc 2 ^ (∑ i ∈ Finset.Icc 1 (n + 1), canonGap q (slopeOrbit q K₀ i))
            * slopeOrbit q K₀ 1
          = 2 ^ canonGap q (slopeOrbit q K₀ (n + 1))
              * (2 ^ (∑ i ∈ Finset.Icc 1 n, canonGap q (slopeOrbit q K₀ i))
                * slopeOrbit q K₀ 1) := by
            rw [hsum, pow_add]
            ring
        _ = 2 ^ canonGap q (slopeOrbit q K₀ (n + 1))
              * (slopeOrbit q K₀ (n + 1) + q * S) := by rw [hS]
        _ = 2 ^ canonGap q (slopeOrbit q K₀ (n + 1)) * slopeOrbit q K₀ (n + 1)
              + q * (2 ^ canonGap q (slopeOrbit q K₀ (n + 1)) * S) := by ring
        _ = slopeOrbit q K₀ (n + 1 + 1) + q
              + q * (2 ^ canonGap q (slopeOrbit q K₀ (n + 1)) * S) := by rw [hstep2]
        _ = slopeOrbit q K₀ (n + 1 + 1)
              + q * (2 ^ canonGap q (slopeOrbit q K₀ (n + 1)) * S + 1) := by ring

/-- **The modulus divides `(2^G − 1)·K₁`** over any period `c` valid from index `1`, where
`G` is the canonical-gap sum over the cycle — the ord₂ obstruction to short periods. -/
theorem towerCycle_modulus_dvd_gapSum {q K₀ c : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀)
    (hKq : K₀ < q) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m) :
    q ∣ (2 ^ (∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i)) - 1)
        * slopeOrbit q K₀ 1 := by
  obtain ⟨S, hS⟩ := towerCycle_gapSum_relation hq hK1 hKq c
  have hcl : slopeOrbit q K₀ (c + 1) = slopeOrbit q K₀ 1 := by
    have h := hper 1 le_rfl
    rwa [Nat.add_comm 1 c] at h
  rw [hcl] at hS
  refine ⟨S, ?_⟩
  have hpow1 : 1 ≤ 2 ^ (∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i)) :=
    Nat.one_le_two_pow
  have hmul : (2 ^ (∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i)) - 1)
        * slopeOrbit q K₀ 1
      = 2 ^ (∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i)) * slopeOrbit q K₀ 1
        - slopeOrbit q K₀ 1 := by
    rw [Nat.sub_mul, Nat.one_mul]
  omega

/-- **The gap-sum floor**: `G ≥ c + 3·b4` — each band-4 cycle position contributes `4` to the
gap sum and every other position contributes at least `1`. -/
theorem towerCycle_gapSum_ge (q K₀ c : ℕ) :
    c + 3 * towerBand4CycleCount q K₀ c
      ≤ ∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i) := by
  have hpt : ∀ i ∈ Finset.Icc 1 c,
      1 + 3 * (if canonGap q (slopeOrbit q K₀ i) = 4 then 1 else 0)
        ≤ canonGap q (slopeOrbit q K₀ i) := by
    intro i _
    have h1 : 1 ≤ canonGap q (slopeOrbit q K₀ i) := canonGap_pos _ _
    by_cases h : canonGap q (slopeOrbit q K₀ i) = 4
    · norm_num [h]
    · rw [if_neg h]
      omega
  have hsum := Finset.sum_le_sum hpt
  have hsplit : (∑ i ∈ Finset.Icc 1 c,
        (1 + 3 * (if canonGap q (slopeOrbit q K₀ i) = 4 then 1 else 0)))
      = c + 3 * towerBand4CycleCount q K₀ c := by
    rw [Finset.sum_add_distrib]
    have hconst : (∑ _i ∈ Finset.Icc 1 c, 1) = c := by
      rw [Finset.sum_const, smul_eq_mul, Nat.card_Icc]
      omega
    have hcount : (∑ i ∈ Finset.Icc 1 c,
          3 * (if canonGap q (slopeOrbit q K₀ i) = 4 then 1 else 0))
        = 3 * towerBand4CycleCount q K₀ c := by
      rw [← Finset.mul_sum]
      unfold towerBand4CycleCount
      rw [Finset.card_filter]
    rw [hconst, hcount]
  omega

/-! ## Part 5.  The pin-admissible base numerators of the explicit moduli -/

/-- `q = 11` pins the base numerator COMPLETELY: `K₀ = 5` (the only `2K₀+1 ∣ 11`). -/
theorem towerFP11_K₀_eq (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 11) : (class1SlopeDatum ctx).K₀ = 5 := by
  obtain ⟨v, hv⟩ : ∃ v, (class1SlopeDatum ctx).K₀ = v := ⟨_, rfl⟩
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq, hv] at hdvd
  have hpos : 1 ≤ v := by rw [← hv]; exact (class1SlopeDatum ctx).hK₀_pos
  have hub : v ≤ 5 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases v
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact hv

/-- `q = 13` pins the base numerator COMPLETELY: `K₀ = 6`. -/
theorem towerFP13_K₀_eq (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 13) : (class1SlopeDatum ctx).K₀ = 6 := by
  obtain ⟨v, hv⟩ : ∃ v, (class1SlopeDatum ctx).K₀ = v := ⟨_, rfl⟩
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq, hv] at hdvd
  have hpos : 1 ≤ v := by rw [← hv]; exact (class1SlopeDatum ctx).hK₀_pos
  have hub : v ≤ 6 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases v
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact hv

/-- `q = 15` pins the base numerator into `{1, 2, 7}` (the divisors `3, 5, 15` of `15`). -/
theorem towerFP15_K₀_cases (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) :
    (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 2
      ∨ (class1SlopeDatum ctx).K₀ = 7 := by
  obtain ⟨v, hv⟩ : ∃ v, (class1SlopeDatum ctx).K₀ = v := ⟨_, rfl⟩
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq, hv] at hdvd
  have hpos : 1 ≤ v := by rw [← hv]; exact (class1SlopeDatum ctx).hK₀_pos
  have hub : v ≤ 7 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases v
  · exact Or.inl hv
  · exact Or.inr (Or.inl hv)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact Or.inr (Or.inr hv)

/-- `q = 105` pins the base numerator into `{1, 2, 3, 7, 10, 17, 52}` (the divisors
`3, 5, 7, 15, 21, 35, 105` of `105`). -/
theorem towerFP105_K₀_cases (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) :
    (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 2
      ∨ (class1SlopeDatum ctx).K₀ = 3 ∨ (class1SlopeDatum ctx).K₀ = 7
      ∨ (class1SlopeDatum ctx).K₀ = 10 ∨ (class1SlopeDatum ctx).K₀ = 17
      ∨ (class1SlopeDatum ctx).K₀ = 52 := by
  obtain ⟨v, hv⟩ : ∃ v, (class1SlopeDatum ctx).K₀ = v := ⟨_, rfl⟩
  have hdvd := class1SlopeDatum_pin ctx
  rw [hq, hv] at hdvd
  have hpos : 1 ≤ v := by rw [← hv]; exact (class1SlopeDatum ctx).hK₀_pos
  have hub : v ≤ 52 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases v
  · exact Or.inl hv
  · exact Or.inr (Or.inl hv)
  · exact Or.inr (Or.inr (Or.inl hv))
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact Or.inr (Or.inr (Or.inr (Or.inl hv)))
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hv))))
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact absurd hdvd (by norm_num)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hv)))))
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
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hv)))))

/-! ## Part 6.  Explicit orbit tables for the pin-admissible pairs -/

/-- Orbit cycle for `(11, 5)`: `9 → 7 → 3 → 1 → 5`, bands `1, 1, 2, 4, 3`. -/
private theorem towerFP11_orbit :
    slopeOrbit 11 5 1 = 9 ∧ slopeOrbit 11 5 2 = 7 ∧ slopeOrbit 11 5 3 = 3
      ∧ slopeOrbit 11 5 4 = 1 ∧ slopeOrbit 11 5 5 = 5 ∧ slopeOrbit 11 5 6 = 9 := by
  have e0 : slopeOrbit 11 5 0 = 5 := rfl
  have e1 : slopeOrbit 11 5 1 = 9 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 11 5 2 = 7 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 11 5 3 = 3 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 11 5 4 = 1 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 11 5 5 = 5 :=
    slopeOrbit_step_eval 4 3 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 11 5 6 = 9 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨e1, e2, e3, e4, e5, e6⟩

private theorem towerFP11_collision : slopeOrbit 11 5 (1 + 5) = slopeOrbit 11 5 1 := by
  obtain ⟨e1, _, _, _, _, e6⟩ := towerFP11_orbit
  show slopeOrbit 11 5 6 = slopeOrbit 11 5 1
  rw [e6, e1]

private theorem towerFP11_count : towerBand4CycleCount 11 5 5 ≤ 1 := by
  obtain ⟨e1, e2, e3, e4, e5, _⟩ := towerFP11_orbit
  unfold towerBand4CycleCount
  have hsub : (Finset.Icc 1 5).filter
      (fun j => canonGap 11 (slopeOrbit 11 5 j) = 4) ⊆ {4} := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    obtain ⟨⟨hj1, hj5⟩, hband⟩ := hj
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (by omega))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (by omega))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (by omega))
    · exact Finset.mem_singleton_self 4
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (by omega))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_singleton] at hcard
  exact hcard

/-- Orbit cycle for `(13, 6)`: `11 → 9 → 5 → 7 → 1 → 3`, bands `1, 1, 2, 1, 4, 3`. -/
private theorem towerFP13_orbit :
    slopeOrbit 13 6 1 = 11 ∧ slopeOrbit 13 6 2 = 9 ∧ slopeOrbit 13 6 3 = 5
      ∧ slopeOrbit 13 6 4 = 7 ∧ slopeOrbit 13 6 5 = 1 ∧ slopeOrbit 13 6 6 = 3
      ∧ slopeOrbit 13 6 7 = 11 := by
  have e0 : slopeOrbit 13 6 0 = 6 := rfl
  have e1 : slopeOrbit 13 6 1 = 11 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 13 6 2 = 9 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 13 6 3 = 5 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 13 6 4 = 7 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 13 6 5 = 1 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 13 6 6 = 3 :=
    slopeOrbit_step_eval 5 3 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 13 6 7 = 11 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨e1, e2, e3, e4, e5, e6, e7⟩

private theorem towerFP13_collision : slopeOrbit 13 6 (1 + 6) = slopeOrbit 13 6 1 := by
  obtain ⟨e1, _, _, _, _, _, e7⟩ := towerFP13_orbit
  show slopeOrbit 13 6 7 = slopeOrbit 13 6 1
  rw [e7, e1]

private theorem towerFP13_count : towerBand4CycleCount 13 6 6 ≤ 1 := by
  obtain ⟨e1, e2, e3, e4, e5, e6, _⟩ := towerFP13_orbit
  unfold towerBand4CycleCount
  have hsub : (Finset.Icc 1 6).filter
      (fun j => canonGap 13 (slopeOrbit 13 6 j) = 4) ⊆ {5} := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    obtain ⟨⟨hj1, hj6⟩, hband⟩ := hj
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (by omega))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (by omega))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (by omega))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (by omega))
    · exact Finset.mem_singleton_self 5
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (by omega))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_singleton] at hcard
  exact hcard

/-- Orbit cycle for `(15, 7)`: `13 → 11 → 7`, bands `1, 1, 2` — band-4-free. -/
private theorem towerFP_cycle_15_7 :
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

/-- Orbit cycle for `(105, 1)`: `23 → 79 → 53 → 1`, bands `3, 1, 1, 7` — band-4-free. -/
private theorem towerFP_cycle_105_1 :
    slopeOrbit 105 1 (1 + 4) = slopeOrbit 105 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 4 → canonGap 105 (slopeOrbit 105 1 j) ≠ 4 := by
  have e0 : slopeOrbit 105 1 0 = 1 := rfl
  have e1 : slopeOrbit 105 1 1 = 23 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 105 1 2 = 79 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 105 1 3 = 53 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 105 1 4 = 1 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 105 1 5 = 23 :=
    slopeOrbit_step_eval 4 6 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 105 1 5 = slopeOrbit 105 1 1
    rw [e5, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(105, 2)`: same band-4-free cycle `23 → 79 → 53 → 1`. -/
private theorem towerFP_cycle_105_2 :
    slopeOrbit 105 2 (1 + 4) = slopeOrbit 105 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 4 → canonGap 105 (slopeOrbit 105 2 j) ≠ 4 := by
  have e0 : slopeOrbit 105 2 0 = 2 := rfl
  have e1 : slopeOrbit 105 2 1 = 23 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 105 2 2 = 79 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 105 2 3 = 53 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 105 2 4 = 1 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 105 2 5 = 23 :=
    slopeOrbit_step_eval 4 6 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 105 2 5 = slopeOrbit 105 2 1
    rw [e5, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(105, 3)`: `87 → 69 → 33 → 27 → 3`, bands `1, 1, 2, 2, 6` —
band-4-free. -/
private theorem towerFP_cycle_105_3 :
    slopeOrbit 105 3 (1 + 5) = slopeOrbit 105 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 105 (slopeOrbit 105 3 j) ≠ 4 := by
  have e0 : slopeOrbit 105 3 0 = 3 := rfl
  have e1 : slopeOrbit 105 3 1 = 87 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 105 3 2 = 69 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 105 3 3 = 33 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 105 3 4 = 27 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 105 3 5 = 3 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 105 3 6 = 87 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 105 3 6 = slopeOrbit 105 3 1
    rw [e6, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(105, 10)`: `55 → 5`, bands `1, 5` — band-4-free. -/
private theorem towerFP_cycle_105_10 :
    slopeOrbit 105 10 (1 + 2) = slopeOrbit 105 10 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → canonGap 105 (slopeOrbit 105 10 j) ≠ 4 := by
  have e0 : slopeOrbit 105 10 0 = 10 := rfl
  have e1 : slopeOrbit 105 10 1 = 55 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 105 10 2 = 5 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 105 10 3 = 55 :=
    slopeOrbit_step_eval 2 4 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 105 10 3 = slopeOrbit 105 10 1
    rw [e3, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(105, 17)`: `31 → 19 → 47 → 83 → 61 → 17`, bands `2, 3, 2, 1, 1, 3` —
band-4-free. -/
private theorem towerFP_cycle_105_17 :
    slopeOrbit 105 17 (1 + 6) = slopeOrbit 105 17 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 105 (slopeOrbit 105 17 j) ≠ 4 := by
  have e0 : slopeOrbit 105 17 0 = 17 := rfl
  have e1 : slopeOrbit 105 17 1 = 31 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 105 17 2 = 19 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 105 17 3 = 47 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 105 17 4 = 83 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 105 17 5 = 61 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 105 17 6 = 17 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 105 17 7 = 31 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 105 17 7 = slopeOrbit 105 17 1
    rw [e7, e1]
  · intro j h1 hc
    interval_cases j
    · rw [e1]; exact canonGap_ne_four_of_band (by omega)
    · rw [e2]; exact canonGap_ne_four_of_band (by omega)
    · rw [e3]; exact canonGap_ne_four_of_band (by omega)
    · rw [e4]; exact canonGap_ne_four_of_band (by omega)
    · rw [e5]; exact canonGap_ne_four_of_band (by omega)
    · rw [e6]; exact canonGap_ne_four_of_band (by omega)

/-- Orbit cycle for `(105, 52)`: `103 → 101 → 97 → 89 → 73 → 41 → 59 → 13`,
bands `1, 1, 1, 1, 1, 2, 1, 4` — band-4 count `1` (only the state `13`). -/
private theorem towerFP105_52_orbit :
    slopeOrbit 105 52 1 = 103 ∧ slopeOrbit 105 52 2 = 101 ∧ slopeOrbit 105 52 3 = 97
      ∧ slopeOrbit 105 52 4 = 89 ∧ slopeOrbit 105 52 5 = 73 ∧ slopeOrbit 105 52 6 = 41
      ∧ slopeOrbit 105 52 7 = 59 ∧ slopeOrbit 105 52 8 = 13
      ∧ slopeOrbit 105 52 9 = 103 := by
  have e0 : slopeOrbit 105 52 0 = 52 := rfl
  have e1 : slopeOrbit 105 52 1 = 103 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 105 52 2 = 101 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 105 52 3 = 97 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 105 52 4 = 89 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 105 52 5 = 73 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 105 52 6 = 41 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 105 52 7 = 59 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 105 52 8 = 13 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 105 52 9 = 103 :=
    slopeOrbit_step_eval 8 3 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩

private theorem towerFP105_52_collision :
    slopeOrbit 105 52 (1 + 8) = slopeOrbit 105 52 1 := by
  obtain ⟨e1, _, _, _, _, _, _, _, e9⟩ := towerFP105_52_orbit
  show slopeOrbit 105 52 9 = slopeOrbit 105 52 1
  rw [e9, e1]

private theorem towerFP105_52_count : towerBand4CycleCount 105 52 8 ≤ 1 := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, _⟩ := towerFP105_52_orbit
  unfold towerBand4CycleCount
  have hsub : (Finset.Icc 1 8).filter
      (fun j => canonGap 105 (slopeOrbit 105 52 j) = 4) ⊆ {8} := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    obtain ⟨⟨hj1, hj8⟩, hband⟩ := hj
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (by omega))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (by omega))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (by omega))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (by omega))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (by omega))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (by omega))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (by omega))
    · exact Finset.mem_singleton_self 8
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_singleton] at hcard
  exact hcard

/-! ## Part 7.  The per-modulus towerSplit closures -/

/-- `m₀ ≥ 5` forces `r ≥ 85`, hence shell width `K ≥ 86`. -/
theorem towerFP_width_of_block_ge_five (ctx : ActualFailureContext)
    (hm : 5 ≤ towerSparsityBlock ctx) : 86 ≤ shellWidth ctx := by
  have hdef : towerSparsityBlock ctx = (3 * (ctx.n24CarryData.r + 1) + 63) / 64 := rfl
  have hKr := r_add_one_le_width ctx
  omega

/-- **The `q = 11` datum closure**: `K₀ = 5` is forced, the cycle has period `5` with band-4
count `1`, and the cycle inequality holds on every shell with `m₀ ≤ 4` (i.e. `r ≤ 84`) and
window at least `16` wide. -/
theorem class2CycleInequality_of_modulus_eleven (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 11) (hm : towerSparsityBlock ctx ≤ 4)
    (hK : 16 ≤ shellWidth ctx) :
    Class2CycleInequality ctx := by
  have hK₀ := towerFP11_K₀_eq ctx hq
  refine class2CycleInequality_of_collision_count ctx hq hK₀ (by norm_num)
    towerFP11_collision towerFP11_count ?_
  calc towerSparsityBlock ctx * 1 * (shellWidth ctx + 5 - 1)
      ≤ 4 * 1 * (shellWidth ctx + 5 - 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hm)
    _ ≤ shellWidth ctx * 5 := by omega

/-- **The `q = 13` datum closure**: `K₀ = 6` is forced, the cycle has period `6` with band-4
count `1`, and the cycle inequality holds on every shell with `m₀ ≤ 5` (i.e. `r ≤ 106`) and
window at least `22` wide (`m₀ = 5` forces `K ≥ 86` through the order pin). -/
theorem class2CycleInequality_of_modulus_thirteen (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 13) (hm : towerSparsityBlock ctx ≤ 5)
    (hK : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx := by
  have hK₀ := towerFP13_K₀_eq ctx hq
  refine class2CycleInequality_of_collision_count ctx hq hK₀ (by norm_num)
    towerFP13_collision towerFP13_count ?_
  rcases Nat.lt_or_ge (towerSparsityBlock ctx) 5 with h4 | h5
  · calc towerSparsityBlock ctx * 1 * (shellWidth ctx + 6 - 1)
        ≤ 4 * 1 * (shellWidth ctx + 6 - 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      _ ≤ shellWidth ctx * 6 := by omega
  · have h86 := towerFP_width_of_block_ge_five ctx h5
    calc towerSparsityBlock ctx * 1 * (shellWidth ctx + 6 - 1)
        ≤ 5 * 1 * (shellWidth ctx + 6 - 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hm)
      _ ≤ shellWidth ctx * 6 := by omega

/-- **The `q = 15`, `K₀ = 7` closure**: the band-4-free cycle `13 → 11 → 7` gives the cycle
inequality at EVERY sparsity block. -/
theorem class2CycleInequality_of_q15_K₀7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK₀ : (class1SlopeDatum ctx).K₀ = 7) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_collision_free ctx hq hK₀ (by norm_num)
    towerFP_cycle_15_7.1 towerFP_cycle_15_7.2

/-- **The `q = 15` datum emptiness off the fixed pair**: the divisor pin leaves
`K₀ ∈ {1, 2, 7}`, and `K₀ ≥ 3` forces `K₀ = 7`, whose cycle is band-4-free — the class-2
fibre is EMPTY. -/
theorem towerFP15_fibre_empty_of_K₀_ge_three (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (h3 : 3 ≤ (class1SlopeDatum ctx).K₀) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ := by
  rcases towerFP15_K₀_cases ctx hq with hv | hv | hv
  · omega
  · omega
  · exact class2Fibre_empty_of_collision_free ctx hq hv (by norm_num)
      towerFP_cycle_15_7.1 towerFP_cycle_15_7.2

/-- **The `q = 105`, `K₀ = 52` closure**: the period-8 cycle with band-4 count `1` gives the
cycle inequality on every shell with `m₀ ≤ 7` (i.e. `r ≤ 148`) and window at least `22`
wide. -/
theorem class2CycleInequality_of_q105_K₀52 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK₀ : (class1SlopeDatum ctx).K₀ = 52)
    (hm : towerSparsityBlock ctx ≤ 7) (hK : 22 ≤ shellWidth ctx) :
    Class2CycleInequality ctx := by
  refine class2CycleInequality_of_collision_count ctx hq hK₀ (by norm_num)
    towerFP105_52_collision towerFP105_52_count ?_
  rcases Nat.lt_or_ge (towerSparsityBlock ctx) 5 with h4 | h5
  · calc towerSparsityBlock ctx * 1 * (shellWidth ctx + 8 - 1)
        ≤ 4 * 1 * (shellWidth ctx + 8 - 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      _ ≤ shellWidth ctx * 8 := by omega
  · have h86 := towerFP_width_of_block_ge_five ctx h5
    calc towerSparsityBlock ctx * 1 * (shellWidth ctx + 8 - 1)
        ≤ 7 * 1 * (shellWidth ctx + 8 - 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hm)
      _ ≤ shellWidth ctx * 8 := by omega

/-- **The `q = 105` datum emptiness off the fixed point and the counted pair**: every
pin-admissible `K₀ ∉ {7, 52}` rides a band-4-free cycle — the class-2 fibre is EMPTY. -/
theorem towerFP105_fibre_empty_offFixed (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105)
    (h7 : (class1SlopeDatum ctx).K₀ ≠ 7) (h52 : (class1SlopeDatum ctx).K₀ ≠ 52) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ := by
  rcases towerFP105_K₀_cases ctx hq with hv | hv | hv | hv | hv | hv | hv
  · exact class2Fibre_empty_of_collision_free ctx hq hv (by norm_num)
      towerFP_cycle_105_1.1 towerFP_cycle_105_1.2
  · exact class2Fibre_empty_of_collision_free ctx hq hv (by norm_num)
      towerFP_cycle_105_2.1 towerFP_cycle_105_2.2
  · exact class2Fibre_empty_of_collision_free ctx hq hv (by norm_num)
      towerFP_cycle_105_3.1 towerFP_cycle_105_3.2
  · exact absurd hv h7
  · exact class2Fibre_empty_of_collision_free ctx hq hv (by norm_num)
      towerFP_cycle_105_10.1 towerFP_cycle_105_10.2
  · exact class2Fibre_empty_of_collision_free ctx hq hv (by norm_num)
      towerFP_cycle_105_17.1 towerFP_cycle_105_17.2
  · exact absurd hv h52

/-! ## Part 8.  The surviving fixed family, characterized exactly -/

private theorem towerFP15_step_one : slopeOrbit 15 1 1 = 1 := by
  have e0 : slopeOrbit 15 1 0 = 1 := rfl
  exact slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem towerFP15_step_two : slopeOrbit 15 2 1 = 1 := by
  have e0 : slopeOrbit 15 2 0 = 2 := rfl
  exact slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem towerFP105_step_seven : slopeOrbit 105 7 1 = 7 := by
  have e0 : slopeOrbit 105 7 0 = 7 := rfl
  exact slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The `q = 15` fixed pair is genuinely all-band-4**: `K₀ ≤ 2` (with the pin, exactly
`K₀ ∈ {1, 2}`) steps onto the fixed point `K₁ = 1` and every positive index reads band 4 —
cycle counting cannot bound this family. -/
theorem towerFP15_fixed_band4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK₀ : (class1SlopeDatum ctx).K₀ ≤ 2) :
    ∀ j, 1 ≤ j →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 4 := by
  have h1 : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1 = 1 := by
    have hpos := (class1SlopeDatum ctx).hK₀_pos
    have hcases : (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 2 := by omega
    rcases hcases with hv | hv
    · rw [hq, hv]
      exact towerFP15_step_one
    · rw [hq, hv]
      exact towerFP15_step_two
  exact class2_modulus_fifteen_fixed_family_band4 ctx hq h1

/-- **The `(105, 7)` fixed pair is genuinely all-band-4**: the orbit is constant at
`7 = 105/15` and every positive index reads band 4. -/
theorem towerFP105_fixed_band4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK₀ : (class1SlopeDatum ctx).K₀ = 7) :
    ∀ j, 1 ≤ j →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 4 := by
  intro j hj
  rw [hq, hK₀]
  have hodd105 : Odd 105 := Nat.odd_iff.mpr (by norm_num)
  have hfix : 15 * slopeOrbit 105 7 1 = 105 := by rw [towerFP105_step_seven]
  have hconst := towerFixedPoint_orbit_const hodd105 (by norm_num) (by norm_num) hfix j hj
  rw [hconst, towerFP105_step_seven]
  exact canonGap_eval (g := 3) (by norm_num) (by norm_num) (by norm_num)

/-- At the fixed pair `(15, 1)` the actual target denominator has odd part EXACTLY `5`:
`15 = ordCompl[2] (Q·3) = ordCompl[2] Q · 3`. -/
theorem towerFP15_1_oddpartQ (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK₀ : (class1SlopeDatum ctx).K₀ = 1) :
    ordCompl[2] ctx.shell.Q = 5 := by
  have hQne : ctx.shell.Q ≠ 0 := ctx.shell.hQ.ne'
  have habs : 2 * ctx.shell.hrational.choose.natAbs + 1 = 3 := by
    have h := class1SlopeDatum_K₀_eq ctx
    omega
  have hqe := class1SlopeDatum_q_eq ctx
  rw [habs, hq] at hqe
  have hsplit : apOddModulus ctx.shell.Q 3 = ordCompl[2] ctx.shell.Q * 3 :=
    ordCompl_two_mul_odd hQne (Nat.odd_iff.mpr (by norm_num))
  rw [hsplit] at hqe
  omega

/-- At the even-tail fixed pair `(15, 2)` the actual target denominator has odd part
EXACTLY `3`: `15 = ordCompl[2] (Q·5) = ordCompl[2] Q · 5`. -/
theorem towerFP15_2_oddpartQ (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK₀ : (class1SlopeDatum ctx).K₀ = 2) :
    ordCompl[2] ctx.shell.Q = 3 := by
  have hQne : ctx.shell.Q ≠ 0 := ctx.shell.hQ.ne'
  have habs : 2 * ctx.shell.hrational.choose.natAbs + 1 = 5 := by
    have h := class1SlopeDatum_K₀_eq ctx
    omega
  have hqe := class1SlopeDatum_q_eq ctx
  rw [habs, hq] at hqe
  have hsplit : apOddModulus ctx.shell.Q 5 = ordCompl[2] ctx.shell.Q * 5 :=
    ordCompl_two_mul_odd hQne (Nat.odd_iff.mpr (by norm_num))
  rw [hsplit] at hqe
  omega

/-- At the fixed pair `(105, 7)` the actual target denominator has odd part EXACTLY `7`:
`105 = ordCompl[2] (Q·15) = ordCompl[2] Q · 15`. -/
theorem towerFP105_7_oddpartQ (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK₀ : (class1SlopeDatum ctx).K₀ = 7) :
    ordCompl[2] ctx.shell.Q = 7 := by
  have hQne : ctx.shell.Q ≠ 0 := ctx.shell.hQ.ne'
  have habs : 2 * ctx.shell.hrational.choose.natAbs + 1 = 15 := by
    have h := class1SlopeDatum_K₀_eq ctx
    omega
  have hqe := class1SlopeDatum_q_eq ctx
  rw [habs, hq] at hqe
  have hsplit : apOddModulus ctx.shell.Q 15 = ordCompl[2] ctx.shell.Q * 15 :=
    ordCompl_two_mul_odd hQne (Nat.odd_iff.mpr (by norm_num))
  rw [hsplit] at hqe
  omega

/-! ## Part 9.  The strictly smaller residual and the exact capstone bridge -/

/-- **The wave-4 escape surface**: the per-ctx configurations on which the cycle inequality
is still demanded after every closure of this module — the `q = 9` family above `m₀ ≥ 3`,
the pinned `q = 11` / `q = 13` families above their density thresholds, the two fixed
families `q = 15, K₀ ≤ 2` and `q = 105, K₀ = 7` (plus the counted `(105, 52)` pair above
`m₀ ≥ 8`), and the un-enumerated odd moduli `25 ≤ q ≠ 105`. -/
def TowerEscape (ctx : ActualFailureContext) : Prop :=
  ((class1SlopeDatum ctx).q = 9 ∧ 3 ≤ towerSparsityBlock ctx)
  ∨ ((class1SlopeDatum ctx).q = 11 ∧ 5 ≤ towerSparsityBlock ctx)
  ∨ ((class1SlopeDatum ctx).q = 13 ∧ 6 ≤ towerSparsityBlock ctx)
  ∨ ((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ ≤ 2)
  ∨ ((class1SlopeDatum ctx).q = 105
      ∧ ((class1SlopeDatum ctx).K₀ = 7 ∨ 8 ≤ towerSparsityBlock ctx))
  ∨ (25 ≤ (class1SlopeDatum ctx).q ∧ (class1SlopeDatum ctx).q ≠ 105)

/-- **The wave-4 Tower residual**: the cycle inequality demanded ONLY on deep shells whose
datum configuration escapes every closure of this module — strictly smaller than the wave-3
`Class2CycleDensityResidual` (which demands it on EVERY deep shell). -/
def TowerFixedPointResidual : Prop :=
  ∀ ctx : ActualFailureContext, towerShallowDepthBound < shellLadderDepth ctx →
    TowerEscape ctx → Class2CycleInequality ctx

/-- The wave-3 cycle-density residual discharges the wave-4 residual (weakening witness:
the new surface is no stronger). -/
theorem towerFixedPointResidual_of_cycleDensity (h : Class2CycleDensityResidual) :
    TowerFixedPointResidual :=
  fun ctx hdeep _ => h ctx hdeep

/-- **The exact capstone bridge**: the wave-4 residual rebuilds VERBATIM the `towerSplit`
field of `Erdos260CycleResidual` — per deep ctx, `q < 9` OR `16 < q < 25` OR the cycle
inequality, with every closed configuration discharged by this module's theorems. -/
theorem towerSplit_of_fixedPointResidual (hres : TowerFixedPointResidual) :
    ∀ ctx : ActualFailureContext,
      towerShallowDepthBound < shellLadderDepth ctx →
      (class1SlopeDatum ctx).q < 9
      ∨ (16 < (class1SlopeDatum ctx).q ∧ (class1SlopeDatum ctx).q < 25)
      ∨ Class2CycleInequality ctx := by
  intro ctx hdeep
  have hodd : (class1SlopeDatum ctx).q % 2 = 1 :=
    Nat.odd_iff.mp (class1SlopeDatum ctx).hq_odd
  have hr21 := r_ge_21_of_deep ctx hdeep
  have hKr := r_add_one_le_width ctx
  have hK22 : 22 ≤ shellWidth ctx := by omega
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 9 with h9 | h9
  · exact Or.inl h9
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 17 with h17 | h17
  · -- the odd moduli 9 ≤ q < 17: q ∈ {9, 11, 13, 15}
    refine Or.inr (Or.inr ?_)
    have hq4 : (class1SlopeDatum ctx).q = 9 ∨ (class1SlopeDatum ctx).q = 11
        ∨ (class1SlopeDatum ctx).q = 13 ∨ (class1SlopeDatum ctx).q = 15 := by omega
    rcases hq4 with hq | hq | hq | hq
    · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 3 with hm | hm
      · exact class2CycleInequality_of_modulus_nine ctx hq (by omega)
      · exact hres ctx hdeep (Or.inl ⟨hq, hm⟩)
    · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 5 with hm | hm
      · exact class2CycleInequality_of_modulus_eleven ctx hq (by omega) (by omega)
      · exact hres ctx hdeep (Or.inr (Or.inl ⟨hq, hm⟩))
    · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 6 with hm | hm
      · exact class2CycleInequality_of_modulus_thirteen ctx hq (by omega) hK22
      · exact hres ctx hdeep (Or.inr (Or.inr (Or.inl ⟨hq, hm⟩)))
    · rcases towerFP15_K₀_cases ctx hq with hv | hv | hv
      · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, by omega⟩))))
      · exact hres ctx hdeep (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, by omega⟩))))
      · exact class2CycleInequality_of_q15_K₀7 ctx hq hv
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 25 with h25 | h25
  · -- the parity window 16 < q < 25
    exact Or.inr (Or.inl ⟨by omega, h25⟩)
  refine Or.inr (Or.inr ?_)
  by_cases h105 : (class1SlopeDatum ctx).q = 105
  · rcases towerFP105_K₀_cases ctx h105 with hv | hv | hv | hv | hv | hv | hv
    · exact class2CycleInequality_of_collision_free ctx h105 hv (by norm_num)
        towerFP_cycle_105_1.1 towerFP_cycle_105_1.2
    · exact class2CycleInequality_of_collision_free ctx h105 hv (by norm_num)
        towerFP_cycle_105_2.1 towerFP_cycle_105_2.2
    · exact class2CycleInequality_of_collision_free ctx h105 hv (by norm_num)
        towerFP_cycle_105_3.1 towerFP_cycle_105_3.2
    · exact hres ctx hdeep
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h105, Or.inl hv⟩)))))
    · exact class2CycleInequality_of_collision_free ctx h105 hv (by norm_num)
        towerFP_cycle_105_10.1 towerFP_cycle_105_10.2
    · exact class2CycleInequality_of_collision_free ctx h105 hv (by norm_num)
        towerFP_cycle_105_17.1 towerFP_cycle_105_17.2
    · rcases Nat.lt_or_ge (towerSparsityBlock ctx) 8 with hm | hm
      · exact class2CycleInequality_of_q105_K₀52 ctx h105 hv (by omega) hK22
      · exact hres ctx hdeep
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h105, Or.inr hm⟩)))))
  · exact hres ctx hdeep
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h25, h105⟩)))))

/-- **The full capstone count bound from the wave-4 residual**, through the existing wave-3
split-entry bridge: `Class2DeepShellCountBound` (the `towerCount` field of
`Erdos260SharpResidual`) outright. -/
theorem towerCountBound_of_fixedPointResidual (h : TowerFixedPointResidual) :
    Class2DeepShellCountBound :=
  towerCountBound_of_modulus_split (towerSplit_of_fixedPointResidual h)

/-! ## Part 10.  Honest machine-readable status -/

/-- The precise status of the Tower / Class 2 fixed-point closure after this module. -/
def towerFixedPointClosureStatus : List String :=
  [ "CLOSED (the datum divisor pin, named): 2*K0 + 1 | q at the actual orbit datum " ++
      "(class1SlopeDatum_pin, from class1SlopeDatum_H_dvd + class1SlopeDatum_K0_eq: the " ++
      "odd AP modulus H = 2|P|+1 divides q and K0 = |P|).",
    "CLOSED (the all-band-4 datum confinement, NEW - the wave-4 centerpiece): a " ++
      "band-4-full period of the ACTUAL orbit forces (q, K0) in {(15,1), (15,2), (105,7)} " ++
      "(towerCycle_band4_full_datum_confined; one-step forms " ++
      "towerFixedPoint_pairs_of_step / towerFixedPoint_datum_confined; arithmetic core " ++
      "towerFixedPoint_pairs_core: 2^g*K0 = 16*K1 with K1 odd and (2K0+1) | 15*K1 leaves " ++
      "exactly g=4, K0=K1 in {1,7} and the even one-step tail g=3, K0=2K1, K1=1; the " ++
      "exponents g in {1,2} die on the pin 8K1+1 | 15 / 16K1+1 | 15, g >= 5 dies on " ++
      "parity). The parent's sketch {(15,1),(105,7)} is verified and EXTENDED by the " ++
      "even-K0 tail (15,2) - the orbit is odd from index 1, so the pre-period tail has " ++
      "length at most one and the analysis is complete.",
    "CLOSED (off the confined moduli the cycle density is strictly below 1, NEW): " ++
      "q not in {15, 105} forces b4 < c for EVERY period of the actual orbit " ++
      "(towerBand4CycleCount_lt_of_datum_off, via towerBand4CycleCount_lt_of_not_fixed " ++
      "+ the confinement).",
    "CLOSED (datum-driven modulus closures of the towerSplit surface, NEW): q = 11 " ++
      "forces K0 = 5 (towerFP11_K0_eq; cycle 9->7->3->1->5, period 5, b4 = 1) closing " ++
      "every m0 <= 4 shell, r <= 84 (class2CycleInequality_of_modulus_eleven); q = 13 " ++
      "forces K0 = 6 (cycle 11->9->5->7->1->3, period 6, b4 = 1) closing every m0 <= 5 " ++
      "shell, r <= 106 (class2CycleInequality_of_modulus_thirteen); q = 15 forces " ++
      "K0 in {1,2,7} (towerFP15_K0_cases) with K0 = 7 on the band-4-free cycle " ++
      "13->11->7 - fibre EMPTY and cycle inequality at every m0 " ++
      "(class2CycleInequality_of_q15_K07, towerFP15_fibre_empty_of_K0_ge_three); " ++
      "q = 105 forces K0 in {1,2,3,7,10,17,52} (towerFP105_K0_cases) with " ++
      "{1,2,3,10,17} on band-4-free cycles (fibre EMPTY, " ++
      "towerFP105_fibre_empty_offFixed) and (105,52) on the period-8 cycle " ++
      "103->101->97->89->73->41->59->13 with b4 = 1, closing every m0 <= 7 shell, " ++
      "r <= 148 (class2CycleInequality_of_q105_K052).",
    "CLOSED (general criteria, NEW): the exact ceiling rounding m*b*(K+c-1) <= K*c => " ++
      "m*(b*ceil(K/c)) <= K (towerCycleRounding - no half-density slack); the " ++
      "collision-form builders class2CycleInequality_of_collision_count / _free and " ++
      "class2Fibre_empty_of_collision_free (one explicit orbit collision + band data " ++
      "=> capstone-facing facts); m0 >= 5 forces K >= 86 through the order pin " ++
      "(towerFP_width_of_block_ge_five).",
    "CLOSED (ord2 cycle-sum infrastructure, NEW): telescoping one period gives " ++
      "2^G * K1 = K1 + q*S (towerCycle_gapSum_relation), hence q | (2^G - 1)*K1 " ++
      "(towerCycle_modulus_dvd_gapSum) with G = sum of canonGaps over the cycle and " ++
      "G >= c + 3*b4 (towerCycle_gapSum_ge) - the ord-of-2 lower-bound tool for " ++
      "future per-modulus period floors.",
    "CHARACTERIZED (the honest surviving fixed family): (15,1), (15,2), (105,7) " ++
      "genuinely realize the all-band-4 fixed point (towerFP15_fixed_band4, " ++
      "towerFP105_fixed_band4: every positive index reads band 4, b4 = c on every " ++
      "period); their target denominators are pinned - oddpart(Q) = 5 at (15,1), " ++
      "3 at (15,2), 7 at (105,7) (towerFP15_1_oddpartQ, towerFP15_2_oddpartQ, " ++
      "towerFP105_7_oddpartQ via q = oddpart(Q)*(2K0+1)). These pairs CANNOT be " ++
      "refuted by datum arithmetic alone: Q's odd part is a free model parameter " ++
      "(eta = P/Q, P = K0), so the three shapes are isolated, not closed.",
    "REDUCED (the strictly smaller wave-4 residual + the EXACT capstone bridge): " ++
      "TowerFixedPointResidual = cycle inequality demanded only on the escape surface " ++
      "TowerEscape (q = 9 with m0 >= 3 i.e. r >= 42; q = 11 with m0 >= 5 i.e. " ++
      "r >= 85; q = 13 with m0 >= 6 i.e. r >= 107; q = 15 on the fixed pair K0 <= 2; " ++
      "q = 105 on K0 = 7 or m0 >= 8 i.e. r >= 149; un-enumerated odd moduli " ++
      "25 <= q != 105). towerSplit_of_fixedPointResidual rebuilds VERBATIM the " ++
      "towerSplit field of Erdos260CycleResidual; towerCountBound_of_fixedPointResidual " ++
      "discharges Class2DeepShellCountBound through the wave-3 split entry; " ++
      "towerFixedPointResidual_of_cycleDensity witnesses the new residual is no " ++
      "stronger than the wave-3 Class2CycleDensityResidual.",
    "HONESTLY NOT CLOSED: the three fixed pairs (b4 = c, cycle counting cannot bound " ++
      "their fibres; no formalized hitGap <-> canonGap bridge beyond the shared index " ++
      "exists to refute them); the counted families above their density thresholds " ++
      "(q = 9, m0 >= 3; q = 11, m0 >= 5; q = 13, m0 >= 6; (105,52), m0 >= 8) where " ++
      "the demanded density 1/m0 falls below the cycle density b4/c; and the " ++
      "un-enumerated moduli 25 <= q != 105 (each carries its own finite " ++
      "pin-admissible K0 list and explicit orbit tables; the method extends " ++
      "mechanically). We do NOT claim unconditional closure of the towerSplit field.",
    "NON-DEGENERATE: every theorem is about the genuine class1SlopeDatum of the " ++
      "actual failing-shell context (q = oddpart(Q*(2|P|+1)), K0 = |P|) and the " ++
      "genuine routed class-2 fibre of genuineChargeRoute; the orbit tables are " ++
      "explicit E.13 step evaluations; the emptiness and confinement results are " ++
      "proved impossibility theorems about the routing/orbit/datum arithmetic, not " ++
      "fabricated witnesses." ]

theorem towerFixedPointClosureStatus_nonempty : towerFixedPointClosureStatus ≠ [] := by
  simp [towerFixedPointClosureStatus]

/-! ## Part 11.  Axiom-cleanliness audit -/

#print axioms class1SlopeDatum_pin
#print axioms slopeOrbit_collision_period
#print axioms towerCycleRounding
#print axioms class2CycleInequality_of_collision_count
#print axioms class2CycleInequality_of_collision_free
#print axioms class2Fibre_empty_of_collision_free
#print axioms pin_dvd_fifteen
#print axioms towerFixedPoint_pairs_core
#print axioms towerFixedPoint_pairs_of_step
#print axioms towerFixedPoint_datum_confined
#print axioms towerCycle_band4_full_datum_confined
#print axioms towerBand4CycleCount_lt_of_datum_off
#print axioms towerCycle_gapSum_relation
#print axioms towerCycle_modulus_dvd_gapSum
#print axioms towerCycle_gapSum_ge
#print axioms towerFP11_K₀_eq
#print axioms towerFP13_K₀_eq
#print axioms towerFP15_K₀_cases
#print axioms towerFP105_K₀_cases
#print axioms towerFP_width_of_block_ge_five
#print axioms class2CycleInequality_of_modulus_eleven
#print axioms class2CycleInequality_of_modulus_thirteen
#print axioms class2CycleInequality_of_q15_K₀7
#print axioms towerFP15_fibre_empty_of_K₀_ge_three
#print axioms class2CycleInequality_of_q105_K₀52
#print axioms towerFP105_fibre_empty_offFixed
#print axioms towerFP15_fixed_band4
#print axioms towerFP105_fixed_band4
#print axioms towerFP15_1_oddpartQ
#print axioms towerFP15_2_oddpartQ
#print axioms towerFP105_7_oddpartQ
#print axioms towerFixedPointResidual_of_cycleDensity
#print axioms towerSplit_of_fixedPointResidual
#print axioms towerCountBound_of_fixedPointResidual
#print axioms towerFixedPointClosureStatus_nonempty

end

end Erdos260
