import Erdos260.Erdos260EnumCapstone

/-!
# Modulus-tail criteria from the period-closure relation

Every lane's wave-5 residual carries an un-enumerated modulus tail (tower `q ≥ 107`,
class 0 `q ≥ 96`, class 1 `q ≥ 101`, run/densepack `q ≥ 64`).  Per-modulus enumeration
cannot finish them.  This module (NEW; it edits no existing file) extracts the
consequences of the PROVED period-closure relation

  `q ∣ (2^G − 1) · K₁`    (`towerCycle_modulus_dvd_gapSum`)

where `G = Σ_{i=1}^{c} canonGap q (slopeOrbit q K₀ i)` is the gap sum over one period
and `K₁ = slopeOrbit q K₀ 1`.

## What is proved here

1. **The order floor** (`towerCycle_gapSum_ge_orderOf`): with
   `q' = orbitOrderModulus q K₀ = q / gcd(q, K₁)` (an odd cofactor `≥ 2`), the closure
   relation cancels to `q' ∣ 2^G − 1`, hence `(2 : ZMod q')^G = 1`, hence
   `orderOf (2 : ZMod q') ∣ G` and `orderOf (2 : ZMod q') ≤ G`.
2. **The gap-sum ceiling** (`towerCycle_gapSum_le`): `canonGap q K ≤ log₂ q + 1`, so
   `G ≤ c·(log₂ q + 1)`.  Combined: the **period floor**
   `orderOf (2 : ZMod q') ≤ c·(log₂ q + 1)` (`towerCycle_period_floor`), and the
   threshold form `(log₂ q + 1)·C < ord ⟹ C < c` (`towerCycle_period_gt_of_order_gt`).
   Since a period `c ≤ q` always exists, the UNCONDITIONAL ceiling
   `orderOf (2 : ZMod q') ≤ q·(log₂ q + 1)` (`orbit_orderOf_le_q_mul`) also holds —
   so "order > q·(log₂ q + 1)" criteria would be vacuous and are NOT claimed.
3. **Band-count ceilings**: `4·b4 ≤ G` (`towerCycle_band4_quadruple_le`); deep steps
   (`16·K ≤ q`) carry `canonGap ≥ 5` (`deep_canonGap_ge_five`), so
   `c + 4·d ≤ G` (`towerCycle_gapSum_ge_deep`) and `4·d ≤ c·log₂ q`
   (`towerCycle_deepCount_le`).  HONEST: these are densities (`b4/c ≤ 1` is trivial);
   alone they close nothing.
4. **Where order-largeness genuinely wins** — the `⌈K/c⌉` kill: if
   `(log₂ q + 1)·K < orderOf (2 : ZMod q')` then EVERY period has `c > K`, so the
   ceiling factor `⌈K/c⌉` collapses to `1` and the tower demand
   `m₀·(b4·⌈K/c⌉) ≤ K` reduces to the pure band-4 budget `m₀·b4 ≤ K`
   (`towerTail_of_order_gt`); the same kill reduces the run cycle-density numeric to
   its ceil-free form (`runTail_of_order_gt`).
5. **Period pruning** for the window/band checks of classes 0/1/3: under
   `(log₂ q + 1)·C < ord`, the finite checks need only be searched over periods
   `c > C` (the iffs `class0WindowCheck_iff_long_of_order_gt`,
   `class1BandFreePeriod_iff_long_of_order_gt`, `class3Band3Free_iff_long_of_order_gt`).
6. **Exceptional families**: the odd moduli `q' > 1` with `orderOf (2 : ZMod q') ≤ 6`
   are EXACTLY the Mersenne divisors `{3, 5, 7, 9, 15, 21, 31, 63}`
   (`mem_mersenneSmallOrderModuli_of_orderOf_le_six` / `orderOf_two_le_six_of_mem`)
   — the honest remaining hard cofactors where even the period floor is weak
   (`towerCycle_exceptional_or_gapSum_gt_six`).
7. **Additive bridges** into the lanes' residual surfaces (capstone field shapes):
   `towerEnumResidual_of_tail_order_criterion` (rebuilds
   `TowerModulusEnumerationResidual` verbatim), `class0Big_of_order_pruned`
   (the `class0Big` field shape), `class1PairDeep_split_at_tail` (the
   `Class1PairResidual.deep` field shape), `runSettlement_split_at_tail`
   (`RunCycleNumericSettlementHyp` verbatim), `densePackStartsEmpty_split_at_tail`
   (`Class3StartsEmpty` verbatim).

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The gap-sum ceiling `G ≤ c·(log₂ q + 1)` -/

/-- Every canonical gap is at most `log₂ q + 1` (monotonicity of `Nat.log` along
`q / K ≤ q`). -/
theorem canonGap_le_logFloor (q K : ℕ) : canonGap q K ≤ Nat.log 2 q + 1 := by
  unfold canonGap
  have h : Nat.log 2 (q / K) ≤ Nat.log 2 q := Nat.log_mono_right (Nat.div_le_self q K)
  omega

/-- **The gap-sum ceiling**: over any period block `[1, c]` the gap sum is at most
`c·(log₂ q + 1)`. -/
theorem towerCycle_gapSum_le (q K₀ c : ℕ) :
    (∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i)) ≤ c * (Nat.log 2 q + 1) := by
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.Icc 1 c) =>
    canonGap_le_logFloor q (slopeOrbit q K₀ i))
  have hconst : (∑ _i ∈ Finset.Icc 1 c, (Nat.log 2 q + 1)) = c * (Nat.log 2 q + 1) := by
    rw [Finset.sum_const, smul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
  omega

/-! ## Part 2.  The odd cofactor and the order floor

From `q ∣ (2^G − 1)·K₁` the gcd `g = gcd(q, K₁)` cancels: with `q' = q/g` coprime to
`K₁/g` we get `q' ∣ 2^G − 1`, i.e. `2^G ≡ 1 (mod q')` — the multiplicative order of `2`
modulo `q'` divides the gap sum.  This is the HONEST exact form: the order constraint
lives on the cofactor `q' = q / gcd(q, K₁)`, not on `q` itself (when `gcd = 1`, which is
the generic case, `q' = q`). -/

/-- The odd cofactor `q / gcd(q, K₁)` carrying the order constraint of the period
closure (`K₁ = slopeOrbit q K₀ 1` is the first orbit value). -/
def orbitOrderModulus (q K₀ : ℕ) : ℕ := q / Nat.gcd q (slopeOrbit q K₀ 1)

/-- The order cofactor is at least `2`: `gcd(q, K₁) ≤ K₁ < q` forces `q / gcd ≥ 2`. -/
theorem orbitOrderModulus_two_le {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀) (hKq : K₀ < q) :
    2 ≤ orbitOrderModulus q K₀ := by
  have hmem := slopeOrbit_mem hq hK1 hKq 1
  unfold orbitOrderModulus
  set K₁ := slopeOrbit q K₀ 1 with hK₁def
  have hqpos : 0 < q := by omega
  have hgpos : 0 < Nat.gcd q K₁ := Nat.gcd_pos_of_pos_left K₁ hqpos
  have hgle : Nat.gcd q K₁ ≤ K₁ := Nat.le_of_dvd hmem.1 (Nat.gcd_dvd_right q K₁)
  have hmul : Nat.gcd q K₁ * (q / Nat.gcd q K₁) = q :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left q K₁)
  rcases Nat.lt_or_ge (q / Nat.gcd q K₁) 2 with hlt | hge
  · exfalso
    have hcase : q / Nat.gcd q K₁ = 0 ∨ q / Nat.gcd q K₁ = 1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hlt)
    rcases hcase with h0 | h1
    · rw [h0, Nat.mul_zero] at hmul; omega
    · rw [h1, Nat.mul_one] at hmul; omega
  · exact hge

/-- The order cofactor is odd (a divisor of the odd modulus `q`). -/
theorem orbitOrderModulus_odd {q K₀ : ℕ} (hq : Odd q) : Odd (orbitOrderModulus q K₀) := by
  have hdvd : orbitOrderModulus q K₀ ∣ q :=
    Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q (slopeOrbit q K₀ 1))
  obtain ⟨m, hm⟩ := hdvd
  rcases Nat.even_or_odd (orbitOrderModulus q K₀) with he | ho
  · exfalso
    have heq : Even q := by rw [hm]; exact he.mul_right m
    rcases heq with ⟨t, ht⟩
    rcases hq with ⟨s, hs⟩
    omega
  · exact ho

/-- **The cancelled closure relation**: the order cofactor divides `2^G − 1` — the gcd
structure of `q ∣ (2^G − 1)·K₁` cancels to a pure Mersenne-divisibility. -/
theorem orbitOrderModulus_dvd_two_pow_gapSum_sub_one {q K₀ c : ℕ} (hq : Odd q)
    (hK1 : 1 ≤ K₀) (hKq : K₀ < q) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m) :
    orbitOrderModulus q K₀
      ∣ 2 ^ (∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i)) - 1 := by
  have hmain := towerCycle_modulus_dvd_gapSum hq hK1 hKq hc hper
  unfold orbitOrderModulus
  set K₁ := slopeOrbit q K₀ 1 with hK₁def
  set G := ∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i) with hGdef
  set g := Nat.gcd q K₁ with hgdef
  have hqpos : 0 < q := by omega
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left K₁ hqpos
  have hgq : g ∣ q := Nat.gcd_dvd_left q K₁
  have hgK : g ∣ K₁ := Nat.gcd_dvd_right q K₁
  have hq' : g * (q / g) = q := Nat.mul_div_cancel' hgq
  have hK' : g * (K₁ / g) = K₁ := Nat.mul_div_cancel' hgK
  have hco : Nat.Coprime (q / g) (K₁ / g) := Nat.coprime_div_gcd_div_gcd hgpos
  have hstep : q / g ∣ (2 ^ G - 1) * (K₁ / g) := by
    have h1 : g * (q / g) ∣ (2 ^ G - 1) * (g * (K₁ / g)) := by
      rw [hq', hK']
      exact hmain
    have h2 : (2 ^ G - 1) * (g * (K₁ / g)) = g * ((2 ^ G - 1) * (K₁ / g)) := by ring
    rw [h2] at h1
    exact (Nat.mul_dvd_mul_iff_left hgpos).mp h1
  exact hco.dvd_of_dvd_mul_right hstep

/-- **The closure relation in `ZMod`**: `2^G = 1` in `ZMod (orbitOrderModulus q K₀)`. -/
theorem orbit_two_pow_gapSum_eq_one {q K₀ c : ℕ} (hq : Odd q)
    (hK1 : 1 ≤ K₀) (hKq : K₀ < q) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m) :
    (2 : ZMod (orbitOrderModulus q K₀))
        ^ (∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i)) = 1 := by
  have hdvd := orbitOrderModulus_dvd_two_pow_gapSum_sub_one hq hK1 hKq hc hper
  have h1 : (1 : ℕ) ≤ 2 ^ (∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i)) :=
    Nat.one_le_two_pow
  have hmodeq : (1 : ℕ)
      ≡ 2 ^ (∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i))
        [MOD orbitOrderModulus q K₀] :=
    (Nat.modEq_iff_dvd' h1).mpr hdvd
  have hcast : ((2 ^ (∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i)) : ℕ)
        : ZMod (orbitOrderModulus q K₀))
      = ((1 : ℕ) : ZMod (orbitOrderModulus q K₀)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmodeq.symm
  push_cast at hcast
  exact hcast

/-- **The order divides the gap sum**: `ord_2(q') ∣ G` for `q' = orbitOrderModulus`. -/
theorem orbit_orderOf_dvd_gapSum {q K₀ c : ℕ} (hq : Odd q)
    (hK1 : 1 ≤ K₀) (hKq : K₀ < q) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m) :
    orderOf (2 : ZMod (orbitOrderModulus q K₀))
      ∣ ∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i) :=
  orderOf_dvd_of_pow_eq_one (orbit_two_pow_gapSum_eq_one hq hK1 hKq hc hper)

/-- **The order floor**: `ord_2(q') ≤ G` — the multiplicative order of `2` modulo the
odd cofactor `q' = q / gcd(q, K₁)` is a LOWER bound on the gap sum of any cycle. -/
theorem towerCycle_gapSum_ge_orderOf {q K₀ c : ℕ} (hq : Odd q)
    (hK1 : 1 ≤ K₀) (hKq : K₀ < q) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m) :
    orderOf (2 : ZMod (orbitOrderModulus q K₀))
      ≤ ∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i) := by
  have hdvd := orbit_orderOf_dvd_gapSum hq hK1 hKq hc hper
  have hge := towerCycle_gapSum_ge q K₀ c
  have hpos : 0 < ∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i) := by omega
  exact Nat.le_of_dvd hpos hdvd

/-- **The period floor**: `ord_2(q') ≤ c·(log₂ q + 1)` — every period of the bounded
slope orbit is at least `ord / (log₂ q + 1)`. -/
theorem towerCycle_period_floor {q K₀ c : ℕ} (hq : Odd q)
    (hK1 : 1 ≤ K₀) (hKq : K₀ < q) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m) :
    orderOf (2 : ZMod (orbitOrderModulus q K₀)) ≤ c * (Nat.log 2 q + 1) :=
  le_trans (towerCycle_gapSum_ge_orderOf hq hK1 hKq hc hper)
    (towerCycle_gapSum_le q K₀ c)

/-- **The period floor in threshold form**: if `(log₂ q + 1)·C < ord_2(q')` then EVERY
period exceeds `C` — order-largeness forces long cycles. -/
theorem towerCycle_period_gt_of_order_gt {q K₀ c : ℕ} (hq : Odd q)
    (hK1 : 1 ≤ K₀) (hKq : K₀ < q) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m) (C : ℕ)
    (horder : (Nat.log 2 q + 1) * C < orderOf (2 : ZMod (orbitOrderModulus q K₀))) :
    C < c := by
  have hfloor := towerCycle_period_floor hq hK1 hKq hc hper
  have h1 : (Nat.log 2 q + 1) * C < c * (Nat.log 2 q + 1) := lt_of_lt_of_le horder hfloor
  rw [Nat.mul_comm c] at h1
  exact lt_of_mul_lt_mul_left h1 (Nat.zero_le _)

/-- **The unconditional order ceiling**: since a period `c ≤ q` ALWAYS exists, the order
of `2` modulo the cofactor can never exceed `q·(log₂ q + 1)`.  HONEST consequence: any
"tail closes whenever `ord > q·(log₂ q + 1)`" criterion would be vacuously true; the
non-vacuous criteria below use thresholds strictly inside this ceiling. -/
theorem orbit_orderOf_le_q_mul {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀) (hKq : K₀ < q) :
    orderOf (2 : ZMod (orbitOrderModulus q K₀)) ≤ q * (Nat.log 2 q + 1) := by
  obtain ⟨c, hc1, hcq, hper⟩ := slopeOrbit_exists_period hq hK1 hKq
  exact le_trans (towerCycle_period_floor hq hK1 hKq hc1 hper)
    (Nat.mul_le_mul hcq (Nat.le_refl _))

/-! ## Part 3.  Band-count ceilings from the gap sum

Each band-`b` step contributes `b` to `G`; band-4 steps contribute `4`, deep steps
(`16·K ≤ q`, the class-0 deep band) contribute `≥ 5`.  HONEST assessment: combined with
the ceiling `G ≤ c·(log₂ q + 1)` these give only DENSITY bounds (`4·b4 ≤ G`,
`4·d ≤ c·log₂ q`), never `b4/c < 1` — alone they close no tail. -/

/-- **The band-4 count ceiling**: `4·b4 ≤ G` (each band-4 step gives `4`, and
`b4 ≤ c` absorbs the remaining `c − b4` unit floors). -/
theorem towerCycle_band4_quadruple_le (q K₀ c : ℕ) :
    4 * towerBand4CycleCount q K₀ c
      ≤ ∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i) := by
  have h1 := towerCycle_gapSum_ge q K₀ c
  have h2 := towerBand4CycleCount_le q K₀ c
  omega

/-- The number of deep-band cycle positions (`16·K_j ≤ q`, the class-0 window). -/
def towerDeepCycleCount (q K₀ c : ℕ) : ℕ :=
  ((Finset.Icc 1 c).filter (fun j => 16 * slopeOrbit q K₀ j ≤ q)).card

/-- **Deep steps carry gap `≥ 5`**: `16·K ≤ q` forces `q/K ≥ 16`, so
`canonGap q K = log₂(q/K) + 1 ≥ 5` — each deep step has `2^g·K − q` produced by a
five-plus-bit jump. -/
theorem deep_canonGap_ge_five {q K : ℕ} (hK1 : 1 ≤ K) (hdeep : 16 * K ≤ q) :
    5 ≤ canonGap q K := by
  unfold canonGap
  have h16 : 16 ≤ q / K := (Nat.le_div_iff_mul_le hK1).mpr (by omega)
  have hpow : 2 ^ 4 ≤ q / K := by
    have h24 : (2 : ℕ) ^ 4 = 16 := by norm_num
    omega
  have hlog : 4 ≤ Nat.log 2 (q / K) := Nat.le_log_of_pow_le Nat.one_lt_two hpow
  omega

/-- **The deep-count floor**: `c + 4·d ≤ G` — a cycle carrying `d` deep steps has gap
sum at least `c + 4·d`. -/
theorem towerCycle_gapSum_ge_deep {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀) (hKq : K₀ < q)
    (c : ℕ) :
    c + 4 * towerDeepCycleCount q K₀ c
      ≤ ∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i) := by
  have hpt : ∀ i ∈ Finset.Icc 1 c,
      1 + 4 * (if 16 * slopeOrbit q K₀ i ≤ q then 1 else 0)
        ≤ canonGap q (slopeOrbit q K₀ i) := by
    intro i _
    by_cases h : 16 * slopeOrbit q K₀ i ≤ q
    · rw [if_pos h]
      have h5 := deep_canonGap_ge_five (slopeOrbit_mem hq hK1 hKq i).1 h
      omega
    · rw [if_neg h]
      have h1 := canonGap_pos q (slopeOrbit q K₀ i)
      omega
  have hsum := Finset.sum_le_sum hpt
  have hsplit : (∑ i ∈ Finset.Icc 1 c,
        (1 + 4 * (if 16 * slopeOrbit q K₀ i ≤ q then 1 else 0)))
      = c + 4 * towerDeepCycleCount q K₀ c := by
    rw [Finset.sum_add_distrib]
    have hconst : (∑ _i ∈ Finset.Icc 1 c, 1) = c := by
      rw [Finset.sum_const, smul_eq_mul, Nat.card_Icc]
      omega
    have hcount : (∑ i ∈ Finset.Icc 1 c,
          4 * (if 16 * slopeOrbit q K₀ i ≤ q then 1 else 0))
        = 4 * towerDeepCycleCount q K₀ c := by
      rw [← Finset.mul_sum]
      unfold towerDeepCycleCount
      rw [Finset.card_filter]
    omega
  omega

/-- **The deep-density ceiling**: `4·d ≤ c·log₂ q` — a cycle of period `c` carries at
most `c·log₂(q)/4` deep steps.  HONEST: this is a density `≤ log₂(q)/4` per step, NOT a
closure; it quantifies how many class-0 deep windows one cycle can serve. -/
theorem towerCycle_deepCount_le {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀) (hKq : K₀ < q)
    (c : ℕ) :
    4 * towerDeepCycleCount q K₀ c ≤ c * Nat.log 2 q := by
  have h1 := towerCycle_gapSum_ge_deep hq hK1 hKq c
  have h2 := towerCycle_gapSum_le q K₀ c
  have h3 : c * (Nat.log 2 q + 1) = c * Nat.log 2 q + c := by ring
  omega

/-! ## Part 4.  The tower tail criterion — order-largeness kills `⌈K/c⌉`

The genuine win: the tower demand is `m₀·(b4·⌈K/c⌉) ≤ K` with `K = shellWidth`.  If
`(log₂ q + 1)·K < ord_2(q')` then every period has `c > K`, so `⌈K/c⌉ = 1` and the
demand REDUCES to the pure band-4 budget `m₀·b4 ≤ K`. -/

/-- The pure band-4 budget: some period whose band-4 count satisfies `m₀·b4 ≤ K`
WITHOUT the `⌈K/c⌉` ceiling factor. -/
def TowerBand4Budget (ctx : ActualFailureContext) : Prop :=
  ∃ c : ℕ, 1 ≤ c
    ∧ (∀ m, 1 ≤ m →
        slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
          = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    ∧ towerSparsityBlock ctx
        * towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c
      ≤ shellWidth ctx

/-- **The tower tail criterion**: if the order of `2` modulo the cofactor exceeds
`(log₂ q + 1)·shellWidth`, every period is longer than the shell width, the ceiling
factor collapses to `1`, and the pure band-4 budget delivers the full cycle
inequality `Class2CycleInequality` (the wave-5 tower residual surface). -/
theorem towerTail_of_order_gt (ctx : ActualFailureContext)
    (horder : (Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
    (hbudget : TowerBand4Budget ctx) :
    Class2CycleInequality ctx := by
  obtain ⟨c, hc1, hper, hbud⟩ := hbudget
  have hKc : shellWidth ctx < c :=
    towerCycle_period_gt_of_order_gt (class1SlopeDatum ctx).hq_odd
      (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum ctx).hK₀_lt hc1 hper
      (shellWidth ctx) horder
  refine ⟨c, hc1, hper, ?_⟩
  have hceil : (shellWidth ctx + c - 1) / c < 2 :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < c)).mpr (by omega)
  have hmul : towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c
        * ((shellWidth ctx + c - 1) / c)
      ≤ towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c := by
    have h1 : (shellWidth ctx + c - 1) / c ≤ 1 := by omega
    calc towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c
          * ((shellWidth ctx + c - 1) / c)
        ≤ towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c
          * 1 := Nat.mul_le_mul (Nat.le_refl _) h1
      _ = towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c :=
        Nat.mul_one _
  calc towerSparsityBlock ctx
      * (towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c
          * ((shellWidth ctx + c - 1) / c))
      ≤ towerSparsityBlock ctx
        * towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c :=
        Nat.mul_le_mul (Nat.le_refl _) hmul
    _ ≤ shellWidth ctx := hbud

/-- **The tower bridge (additive)**: the enumerated part (`q < 107`) plus the
order-gt/band-4-budget criterion on the un-enumerated tail (`107 ≤ q`) rebuild
`TowerModulusEnumerationResidual` — VERBATIM the wave-5 tower surface consumed by
`towerSplit_of_modulusEnumeration` in the capstone. -/
theorem towerEnumResidual_of_tail_order_criterion
    (hlow : ∀ ctx : ActualFailureContext, towerShallowDepthBound < shellLadderDepth ctx →
      TowerModulusEnumEscape ctx → (class1SlopeDatum ctx).q < 107 →
      Class2CycleInequality ctx)
    (htail : ∀ ctx : ActualFailureContext, towerShallowDepthBound < shellLadderDepth ctx →
      107 ≤ (class1SlopeDatum ctx).q →
      ((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
          < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
              (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx) :
    TowerModulusEnumerationResidual := by
  intro ctx hdeep hesc
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 107 with hlt | hge
  · exact hlow ctx hdeep hesc hlt
  · obtain ⟨ho, hb⟩ := htail ctx hdeep hge
    exact towerTail_of_order_gt ctx ho hb

/-! ## Part 5.  Period pruning for the class-0 window check (`96 ≤ q` tail)

The class-0 windowed check searches periods `1 ≤ c ≤ q`.  Order-largeness prunes:
under `(log₂ q + 1)·C < ord` NO period `≤ C` exists, so the check is EQUIVALENT to its
restriction to long periods `C < c ≤ q`.  HONEST: pruning shrinks the certified search
but does not by itself produce the window condition. -/

/-- Per-ctx wrapper of the threshold period floor on the actual slope datum. -/
theorem class0_period_gt_of_order_gt (ctx : ActualFailureContext) (C : ℕ)
    (horder : (Nat.log 2 (class1SlopeDatum ctx).q + 1) * C
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
    {c : ℕ} (hc1 : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) :
    C < c :=
  towerCycle_period_gt_of_order_gt (class1SlopeDatum ctx).hq_odd
    (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum ctx).hK₀_lt hc1 hper C horder

/-- **The class-0 pruning iff**: under the order threshold, the windowed cycle check is
EQUIVALENT to its long-period restriction — the finite search may skip all `c ≤ C`. -/
theorem class0WindowCheck_iff_long_of_order_gt (ctx : ActualFailureContext) (C : ℕ)
    (horder : (Nat.log 2 (class1SlopeDatum ctx).q + 1) * C
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀))) :
    Class0WindowCycleCheck ctx
      ↔ ∃ c, C < c ∧ c ≤ (class1SlopeDatum ctx).q
          ∧ (∀ m, 1 ≤ m →
              slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
                = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
          ∧ ∀ k ∈ ctx.n24CarryData.starts,
              129 * shellLadderDepth ctx + 64
                  ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
              (class1SlopeDatum ctx).q
                < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
                    (cycleRep c k) := by
  constructor
  · rintro ⟨c, hc1, hcq, hper, hwin⟩
    exact ⟨c, class0_period_gt_of_order_gt ctx C horder hc1 hper, hcq, hper, hwin⟩
  · rintro ⟨c, hCc, hcq, hper, hwin⟩
    exact ⟨c, by omega, hcq, hper, hwin⟩

/-- **The class-0 tail criterion**: under the order threshold, a long-period windowed
certificate delivers `Class0WindowCycleCheck` — the exact `class0Big` surface (`96 ≤ q`)
of the wave-5 capstone. -/
theorem class0Tail_of_order_gt (ctx : ActualFailureContext) (C : ℕ)
    (horder : (Nat.log 2 (class1SlopeDatum ctx).q + 1) * C
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
    (hcheck : ∃ c, C < c ∧ c ≤ (class1SlopeDatum ctx).q
        ∧ (∀ m, 1 ≤ m →
            slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
              = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
        ∧ ∀ k ∈ ctx.n24CarryData.starts,
            129 * shellLadderDepth ctx + 64
                ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
            (class1SlopeDatum ctx).q
              < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
                  (cycleRep c k)) :
    Class0WindowCycleCheck ctx :=
  (class0WindowCheck_iff_long_of_order_gt ctx C horder).mpr hcheck

/-- **The class-0 bridge (additive)**: the per-ctx order threshold plus the pruned
long-period certificate rebuild the `class0Big` field of `Erdos260EnumResidual`
VERBATIM. -/
theorem class0Big_of_order_pruned
    (h : ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
      ∃ C, ((Nat.log 2 (class1SlopeDatum ctx).q + 1) * C
          < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
              (class1SlopeDatum ctx).K₀)))
        ∧ ∃ c, C < c ∧ c ≤ (class1SlopeDatum ctx).q
            ∧ (∀ m, 1 ≤ m →
                slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
                  = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
            ∧ ∀ k ∈ ctx.n24CarryData.starts,
                129 * shellLadderDepth ctx + 64
                    ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
                (class1SlopeDatum ctx).q
                  < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
                      (cycleRep c k)) :
    ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
      Class0WindowCycleCheck ctx := by
  intro ctx h96
  obtain ⟨C, horder, hcheck⟩ := h ctx h96
  exact class0Tail_of_order_gt ctx C horder hcheck

/-! ## Part 6.  The class-1 tail (`101 ≤ q`): band-4-free periods, order-pruned -/

/-- Some period of the actual orbit is band-4-free over its whole block — a finite
check (`≤ q` canonical-gap evaluations once a period is found). -/
def Class1Band4FreePeriod (ctx : ActualFailureContext) : Prop :=
  ∃ c, 1 ≤ c
    ∧ (∀ m, 1 ≤ m →
        slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
          = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    ∧ ∀ j, 1 ≤ j → j ≤ c →
        canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 4

/-- A band-4-free period empties the class-1 routed fibre (the cycle-representative
reduction feeds `class1Fibre_empty_of_orbit_band_free`). -/
theorem class1Fibre_empty_of_period_band4_free (ctx : ActualFailureContext)
    {c : ℕ} (hc1 : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hfree : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  apply class1Fibre_empty_of_orbit_band_free ctx
  intro j hj
  rw [slopeOrbit_cycleRep hc1 hper hj]
  exact hfree _ (cycleRep_pos hc1 j) (cycleRep_le hc1 j)

/-- The band-4-free-period check empties the class-1 fibre. -/
theorem class1Tail_of_band4FreePeriod (ctx : ActualFailureContext)
    (h : Class1Band4FreePeriod ctx) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  obtain ⟨c, hc1, hper, hfree⟩ := h
  exact class1Fibre_empty_of_period_band4_free ctx hc1 hper hfree

/-- **The class-1 pruning iff**: under the order threshold the band-4-free-period check
is EQUIVALENT to its long-period restriction. -/
theorem class1BandFreePeriod_iff_long_of_order_gt (ctx : ActualFailureContext) (C : ℕ)
    (horder : (Nat.log 2 (class1SlopeDatum ctx).q + 1) * C
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀))) :
    Class1Band4FreePeriod ctx
      ↔ ∃ c, C < c
          ∧ (∀ m, 1 ≤ m →
              slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
                = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
          ∧ ∀ j, 1 ≤ j → j ≤ c →
              canonGap (class1SlopeDatum ctx).q
                (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j)
                ≠ 4 := by
  constructor
  · rintro ⟨c, hc1, hper, hfree⟩
    exact ⟨c, class0_period_gt_of_order_gt ctx C horder hc1 hper, hper, hfree⟩
  · rintro ⟨c, hCc, hper, hfree⟩
    exact ⟨c, by omega, hper, hfree⟩

/-- **The class-1 tail criterion**: under the order threshold, a long band-4-free
period empties the class-1 fibre. -/
theorem class1Tail_of_order_gt (ctx : ActualFailureContext) (C : ℕ)
    (horder : (Nat.log 2 (class1SlopeDatum ctx).q + 1) * C
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
    (hcheck : ∃ c, C < c
        ∧ (∀ m, 1 ≤ m →
            slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
              = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
        ∧ ∀ j, 1 ≤ j → j ≤ c →
            canonGap (class1SlopeDatum ctx).q
              (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Tail_of_band4FreePeriod ctx
    ((class1BandFreePeriod_iff_long_of_order_gt ctx C horder).mpr hcheck)

/-- **The class-1 bridge (additive)**: the enumerated part (`q < 101`) plus
band-4-free periods on the tail (`101 ≤ q`) rebuild the `deep` field of
`Class1PairResidual` VERBATIM. -/
theorem class1PairDeep_split_at_tail
    (hlow : ∀ ctx : ActualFailureContext,
      1 ≤ ctx.n24CarryData.r →
      64 ∣ shellLadderDepth ctx →
      9 ≤ (class1SlopeDatum ctx).q →
      ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
      (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
      ¬ Class1DatumClosed ctx →
      ¬ Class1GcdWindowMiss ctx →
      (class1SlopeDatum ctx).q < 101 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅)
    (htail : ∀ ctx : ActualFailureContext,
      1 ≤ ctx.n24CarryData.r →
      101 ≤ (class1SlopeDatum ctx).q →
      Class1Band4FreePeriod ctx) :
    ∀ ctx : ActualFailureContext,
      1 ≤ ctx.n24CarryData.r →
      64 ∣ shellLadderDepth ctx →
      9 ≤ (class1SlopeDatum ctx).q →
      ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
      (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
      ¬ Class1DatumClosed ctx →
      ¬ Class1GcdWindowMiss ctx →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  intro ctx hr hdvd h9 hwin hcl hdc hgcd
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 101 with hlt | hge
  · exact hlow ctx hr hdvd h9 hwin hcl hdc hgcd hlt
  · exact class1Tail_of_band4FreePeriod ctx (htail ctx hr hge)

/-! ## Part 7.  The run tail (`64 ≤ q`): the same `⌈K/c⌉` kill on the cycle numeric -/

/-- The ceil-free run band budget: some period whose band-`{1,4}` count satisfies the
cycle-density numeric WITHOUT the `⌈W/c⌉` ceiling factor. -/
def RunBandBudget (ctx : ActualFailureContext) : Prop :=
  ∃ c : ℕ, 1 ≤ c
    ∧ (∀ m, 1 ≤ m →
        slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
          = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    ∧ erdos260Constants.c0 * (((class5CycleBand ctx c).card : ℕ) : ℝ)
        * runDyadicMult ctx
      ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
        * ((supportShell ctx.d ctx.X).card : ℝ)

/-- **The run tail criterion**: if the order of `2` modulo the cofactor exceeds
`(log₂ q + 1)·|supportShell|`, every period is longer than the support width, the
`⌈W/c⌉` factor collapses to `1`, and the ceil-free band budget delivers
`Class5CycleNumericCloses` — the second disjunct of the wave-5 run residual. -/
theorem runTail_of_order_gt (ctx : ActualFailureContext)
    (horder : (Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
    (hbudget : RunBandBudget ctx) :
    Class5CycleNumericCloses ctx := by
  obtain ⟨c, hc1, hper, hbud⟩ := hbudget
  have hWc : (supportShell ctx.shell.d ctx.shell.X).card < c :=
    towerCycle_period_gt_of_order_gt (class1SlopeDatum ctx).hq_odd
      (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum ctx).hK₀_lt hc1 hper
      (supportShell ctx.shell.d ctx.shell.X).card horder
  refine ⟨c, hc1, hper, ?_⟩
  have hceil : ((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c < 2 :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < c)).mpr (by omega)
  have hcard : (class5CycleBand ctx c).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c)
      ≤ (class5CycleBand ctx c).card := by
    have h1 : ((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c ≤ 1 := by omega
    calc (class5CycleBand ctx c).card
          * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c)
        ≤ (class5CycleBand ctx c).card * 1 := Nat.mul_le_mul (Nat.le_refl _) h1
      _ = (class5CycleBand ctx c).card := Nat.mul_one _
  have hcast : (((class5CycleBand ctx c).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) : ℕ) : ℝ)
      ≤ (((class5CycleBand ctx c).card : ℕ) : ℝ) := Nat.cast_le.mpr hcard
  calc erdos260Constants.c0
      * (((class5CycleBand ctx c).card
          * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) : ℕ) : ℝ)
      * runDyadicMult ctx
      ≤ erdos260Constants.c0 * (((class5CycleBand ctx c).card : ℕ) : ℝ)
        * runDyadicMult ctx :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcast erdos260Constants.c0_pos.le)
          (runDyadicMult_nonneg ctx)
    _ ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
        * ((supportShell ctx.d ctx.X).card : ℝ) := hbud

/-- **The run bridge (additive)**: the enumerated part (`q < 64`) plus the
order-gt/ceil-free-budget criterion on the tail (`64 ≤ q`) rebuild
`RunCycleNumericSettlementHyp` VERBATIM (the wave-5 `runNumeric` consumer). -/
theorem runSettlement_split_at_tail
    (hlow : ∀ ctx : ActualFailureContext, 1 ≤ ctx.n24CarryData.r →
      (class1SlopeDatum ctx).q < 64 →
      Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx)
    (htail : ∀ ctx : ActualFailureContext, 1 ≤ ctx.n24CarryData.r →
      64 ≤ (class1SlopeDatum ctx).q →
      ((Nat.log 2 (class1SlopeDatum ctx).q + 1)
          * (supportShell ctx.shell.d ctx.shell.X).card
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ RunBandBudget ctx) :
    RunCycleNumericSettlementHyp := by
  intro ctx hr
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 64 with hlt | hge
  · exact hlow ctx hr hlt
  · obtain ⟨ho, hb⟩ := htail ctx hr hge
    exact Or.inr (runTail_of_order_gt ctx ho hb)

/-! ## Part 8.  The densepack tail (`64 ≤ q`): band-3-free periods, order-pruned -/

/-- **The class-3 pruning iff**: under the order threshold the band-3-free-period check
`Class3CycleBand3Free` is EQUIVALENT to its long-period restriction. -/
theorem class3Band3Free_iff_long_of_order_gt (ctx : ActualFailureContext) (C : ℕ)
    (horder : (Nat.log 2 (class1SlopeDatum ctx).q + 1) * C
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀))) :
    Class3CycleBand3Free ctx
      ↔ ∃ c, C < c
          ∧ (∀ m, 1 ≤ m →
              slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
                = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
          ∧ ∀ j, 1 ≤ j → j ≤ c →
              canonGap (class1SlopeDatum ctx).q
                (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j)
                ≠ 3 := by
  constructor
  · rintro ⟨c, hc1, hper, hfree⟩
    exact ⟨c, class0_period_gt_of_order_gt ctx C horder hc1 hper, hper, hfree⟩
  · rintro ⟨c, hCc, hper, hfree⟩
    exact ⟨c, by omega, hper, hfree⟩

/-- **The densepack tail criterion**: under the order threshold, a long band-3-free
period empties the genuine dense start set. -/
theorem densePackTail_of_order_gt (ctx : ActualFailureContext) (C : ℕ)
    (horder : (Nat.log 2 (class1SlopeDatum ctx).q + 1) * C
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
    (hcheck : ∃ c, C < c
        ∧ (∀ m, 1 ≤ m →
            slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
              = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
        ∧ ∀ j, 1 ≤ j → j ≤ c →
            canonGap (class1SlopeDatum ctx).q
              (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 3) :
    genuineDensePackStarts ctx = ∅ :=
  densePackStarts_empty_of_cycleBand3Free ctx
    ((class3Band3Free_iff_long_of_order_gt ctx C horder).mpr hcheck)

/-- **The densepack bridge (additive)**: the enumerated window (`q < 64`) plus
band-3-free periods on the tail (`64 ≤ q`) rebuild `Class3StartsEmpty` VERBATIM. -/
theorem densePackStartsEmpty_split_at_tail
    (hlow : ∀ ctx : ActualFailureContext, (class1SlopeDatum ctx).q < 64 →
      genuineDensePackStarts ctx = ∅)
    (htail : ∀ ctx : ActualFailureContext, 64 ≤ (class1SlopeDatum ctx).q →
      Class3CycleBand3Free ctx) :
    Class3StartsEmpty := by
  intro ctx
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 64 with hlt | hge
  · exact hlow ctx hlt
  · exact densePackStarts_empty_of_cycleBand3Free ctx (htail ctx hge)

/-! ## Part 9.  The exceptional modulus families (small order = Mersenne divisors)

Order-conditional criteria reduce each tail to the moduli whose cofactor has SMALL
order — exactly the divisors of small Mersenne numbers `2^G₀ − 1`.  For `ord ≤ 6` the
complete list of odd exceptional cofactors `> 1` is the divisor union of
`{3, 7, 15, 31, 63}`: `{3, 5, 7, 9, 15, 21, 31, 63}`. -/

/-- Every modulus divides `2^ord − 1` (cast `pow_orderOf_eq_one` back to `ℕ`). -/
theorem zmod_dvd_two_pow_orderOf_sub_one (n : ℕ) :
    n ∣ 2 ^ orderOf (2 : ZMod n) - 1 := by
  have hpow := pow_orderOf_eq_one (2 : ZMod n)
  have hcast : ((2 ^ orderOf (2 : ZMod n) : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
    push_cast
    exact hpow
  have hmodeq := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmodeq.symm

/-- For odd `n > 1` the order of `2` in `ZMod n` is positive (Euler: `ord ∣ φ(n) > 0`). -/
theorem orderOf_two_pos_of_odd {n : ℕ} (hodd : Odd n) (h1 : 1 < n) :
    0 < orderOf (2 : ZMod n) := by
  have hco : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hodd
  have heuler : (2 : ℕ) ^ Nat.totient n ≡ 1 [MOD n] := Nat.ModEq.pow_totient hco
  have hcast : (((2 : ℕ) ^ Nat.totient n : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr heuler
  push_cast at hcast
  have hdvd : orderOf (2 : ZMod n) ∣ Nat.totient n := orderOf_dvd_of_pow_eq_one hcast
  have htot : 0 < Nat.totient n := Nat.totient_pos.mpr (by omega)
  rcases Nat.eq_zero_or_pos (orderOf (2 : ZMod n)) with h0 | hpos
  · exfalso
    rw [h0] at hdvd
    have := Nat.eq_zero_of_zero_dvd hdvd
    omega
  · exact hpos

/-- The exceptional odd cofactors with `ord_2 ≤ 6`: the odd divisors `> 1` of the
Mersenne numbers `2^k − 1`, `k ≤ 6`. -/
def mersenneSmallOrderModuli : List ℕ := [3, 5, 7, 9, 15, 21, 31, 63]

/-- **The exceptional family is complete**: every odd `n > 1` with
`orderOf (2 : ZMod n) ≤ 6` is one of `{3, 5, 7, 9, 15, 21, 31, 63}`. -/
theorem mem_mersenneSmallOrderModuli_of_orderOf_le_six {n : ℕ} (hodd : Odd n)
    (h1 : 1 < n) (hord : orderOf (2 : ZMod n) ≤ 6) :
    n ∈ mersenneSmallOrderModuli := by
  have hpos := orderOf_two_pos_of_odd hodd h1
  have hdvd := zmod_dvd_two_pow_orderOf_sub_one n
  have hcases : orderOf (2 : ZMod n) = 1 ∨ orderOf (2 : ZMod n) = 2
      ∨ orderOf (2 : ZMod n) = 3 ∨ orderOf (2 : ZMod n) = 4
      ∨ orderOf (2 : ZMod n) = 5 ∨ orderOf (2 : ZMod n) = 6 := by omega
  rcases hcases with h | h | h | h | h | h <;> rw [h] at hdvd <;> norm_num at hdvd
  · -- ord = 1 : n ∣ 1
    omega
  · -- ord = 2 : n ∣ 3
    have hmem := Nat.mem_divisors.mpr ⟨hdvd, (by norm_num : (3 : ℕ) ≠ 0)⟩
    rw [show Nat.divisors 3 = {1, 3} from by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' <;> subst h'
    · omega
    · decide
  · -- ord = 3 : n ∣ 7
    have hmem := Nat.mem_divisors.mpr ⟨hdvd, (by norm_num : (7 : ℕ) ≠ 0)⟩
    rw [show Nat.divisors 7 = {1, 7} from by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' <;> subst h'
    · omega
    · decide
  · -- ord = 4 : n ∣ 15
    have hmem := Nat.mem_divisors.mpr ⟨hdvd, (by norm_num : (15 : ℕ) ≠ 0)⟩
    rw [show Nat.divisors 15 = {1, 3, 5, 15} from by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' | h' | h' <;> subst h'
    · omega
    · decide
    · decide
    · decide
  · -- ord = 5 : n ∣ 31
    have hmem := Nat.mem_divisors.mpr ⟨hdvd, (by norm_num : (31 : ℕ) ≠ 0)⟩
    rw [show Nat.divisors 31 = {1, 31} from by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' <;> subst h'
    · omega
    · decide
  · -- ord = 6 : n ∣ 63
    have hmem := Nat.mem_divisors.mpr ⟨hdvd, (by norm_num : (63 : ℕ) ≠ 0)⟩
    rw [show Nat.divisors 63 = {1, 3, 7, 9, 21, 63} from by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h' | h' | h' | h' | h' | h' <;> subst h'
    · omega
    · decide
    · decide
    · decide
    · decide
    · decide

/-- **The exceptional family is exact**: each listed modulus genuinely has
`orderOf (2 : ZMod n) ≤ 6`. -/
theorem orderOf_two_le_six_of_mem {n : ℕ} (h : n ∈ mersenneSmallOrderModuli) :
    orderOf (2 : ZMod n) ≤ 6 := by
  have hcases : n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 9 ∨ n = 15 ∨ n = 21 ∨ n = 31 ∨ n = 63 := by
    simpa [mersenneSmallOrderModuli] using h
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h2 : (2 : ZMod 3) ^ 2 = 1 := by decide
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
    omega
  · have h2 : (2 : ZMod 5) ^ 4 = 1 := by decide
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
    omega
  · have h2 : (2 : ZMod 7) ^ 3 = 1 := by decide
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
    omega
  · have h2 : (2 : ZMod 9) ^ 6 = 1 := by decide
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
    omega
  · have h2 : (2 : ZMod 15) ^ 4 = 1 := by decide
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
    omega
  · have h2 : (2 : ZMod 21) ^ 6 = 1 := by decide
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
    omega
  · have h2 : (2 : ZMod 31) ^ 5 = 1 := by decide
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
    omega
  · have h2 : (2 : ZMod 63) ^ 6 = 1 := by decide
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
    omega

/-- **The dichotomy at threshold `6`**: for any cycle, EITHER the order cofactor is one
of the eight exceptional Mersenne-divisor moduli, OR the gap sum exceeds `6` (and the
order floor is active).  This is the honest shape of the order lever: it splits every
tail modulus into the generic (long-gap-sum) regime and the finite exceptional list. -/
theorem towerCycle_exceptional_or_gapSum_gt_six {q K₀ c : ℕ} (hq : Odd q)
    (hK1 : 1 ≤ K₀) (hKq : K₀ < q) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m) :
    orbitOrderModulus q K₀ ∈ mersenneSmallOrderModuli
      ∨ 6 < ∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i) := by
  rcases Nat.lt_or_ge 6 (∑ i ∈ Finset.Icc 1 c, canonGap q (slopeOrbit q K₀ i)) with
    hgt | hle
  · exact Or.inr hgt
  · left
    have hord := towerCycle_gapSum_ge_orderOf hq hK1 hKq hc hper
    have h2le := orbitOrderModulus_two_le hq hK1 hKq
    exact mem_mersenneSmallOrderModuli_of_orderOf_le_six (orbitOrderModulus_odd hq)
      (by omega) (by omega)

/-! ## Part 10.  Honest machine-readable status -/

/-- The precise status of the modulus-tail criteria after this module. -/
def modulusTailCriteriaStatus : List String :=
  [ "PROVED (the order floor, generic): from the period closure q | (2^G - 1)*K1 " ++
      "(towerCycle_modulus_dvd_gapSum), the gcd cancels to q' | 2^G - 1 on the odd " ++
      "cofactor q' = orbitOrderModulus q K0 = q / gcd(q, K1) >= 2 " ++
      "(orbitOrderModulus_dvd_two_pow_gapSum_sub_one), so (2 : ZMod q')^G = 1 " ++
      "(orbit_two_pow_gapSum_eq_one), orderOf (2 : ZMod q') | G " ++
      "(orbit_orderOf_dvd_gapSum) and orderOf (2 : ZMod q') <= G " ++
      "(towerCycle_gapSum_ge_orderOf).  HONEST exact form: the constraint lives on " ++
      "the COFACTOR q' (generically q' = q when gcd(q, K1) = 1), not always on q.",
    "PROVED (the period floor): canonGap <= log2 q + 1 (canonGap_le_logFloor) gives " ++
      "G <= c*(log2 q + 1) (towerCycle_gapSum_le), hence orderOf (2 : ZMod q') <= " ++
      "c*(log2 q + 1) (towerCycle_period_floor) and the threshold form (log2 q + 1)*C " ++
      "< ord => C < c for EVERY period (towerCycle_period_gt_of_order_gt).  " ++
      "UNCONDITIONAL ceiling: a period c <= q always exists, so ord <= q*(log2 q + 1) " ++
      "(orbit_orderOf_le_q_mul) - criteria demanding ord beyond this are vacuous and " ++
      "are NOT claimed.",
    "PROVED (band ceilings, honest densities only): 4*b4 <= G " ++
      "(towerCycle_band4_quadruple_le); deep steps (16K <= q) carry gap >= 5 " ++
      "(deep_canonGap_ge_five), so c + 4*d <= G (towerCycle_gapSum_ge_deep) and " ++
      "4*d <= c*log2 q (towerCycle_deepCount_le).  HONEST: these bound DENSITIES " ++
      "(b4 <= c is trivial); alone they close no tail.",
    "TOWER TAIL (q >= 107) CRITERION - where order-largeness genuinely wins: if " ++
      "(log2 q + 1)*shellWidth < orderOf (2 : ZMod q') then every period c > K, the " ++
      "ceiling factor ceil(K/c) collapses to 1, and the pure band-4 budget m0*b4 <= K " ++
      "(TowerBand4Budget) delivers Class2CycleInequality (towerTail_of_order_gt); " ++
      "bridge towerEnumResidual_of_tail_order_criterion rebuilds " ++
      "TowerModulusEnumerationResidual VERBATIM from the enumerated part (q < 107) " ++
      "plus the tail criterion.",
    "RUN TAIL (q >= 64) CRITERION - the same ceil-kill: (log2 q + 1)*|supportShell| < " ++
      "ord forces every period past the support width, ceil(W/c) = 1, and the " ++
      "ceil-free band budget (RunBandBudget) delivers Class5CycleNumericCloses " ++
      "(runTail_of_order_gt); bridge runSettlement_split_at_tail rebuilds " ++
      "RunCycleNumericSettlementHyp VERBATIM.",
    "CLASS-0 TAIL (q >= 96) PRUNING - honest: order-largeness does NOT produce the " ++
      "window condition; it PRUNES the finite search: under (log2 q + 1)*C < ord the " ++
      "windowed check is EQUIVALENT to its restriction to periods c > C " ++
      "(class0WindowCheck_iff_long_of_order_gt); sufficient form " ++
      "class0Tail_of_order_gt, bridge class0Big_of_order_pruned (the class0Big field " ++
      "shape VERBATIM).",
    "CLASS-1 TAIL (q >= 101) and DENSEPACK TAIL (q >= 64) PRUNING - band-4-free " ++
      "(Class1Band4FreePeriod, class1Fibre_empty_of_period_band4_free, " ++
      "class1Tail_of_band4FreePeriod) resp. band-3-free (Class3CycleBand3Free) " ++
      "periods close per-ctx; the order threshold prunes both searches to long " ++
      "periods (class1BandFreePeriod_iff_long_of_order_gt, class1Tail_of_order_gt, " ++
      "class3Band3Free_iff_long_of_order_gt, densePackTail_of_order_gt); bridges " ++
      "class1PairDeep_split_at_tail (the Class1PairResidual.deep field shape) and " ++
      "densePackStartsEmpty_split_at_tail (Class3StartsEmpty VERBATIM).",
    "EXCEPTIONAL FAMILIES (proved exactly): the odd cofactors q' > 1 with " ++
      "orderOf (2 : ZMod q') <= 6 are EXACTLY the Mersenne divisors " ++
      "{3, 5, 7, 9, 15, 21, 31, 63} (mem_mersenneSmallOrderModuli_of_orderOf_le_six " ++
      "complete via n | 2^ord - 1, orderOf_two_le_six_of_mem exact via per-element " ++
      "power certificates; positivity orderOf_two_pos_of_odd by Euler).  Dichotomy " ++
      "towerCycle_exceptional_or_gapSum_gt_six: every cycle either has its cofactor " ++
      "in the list or gap sum > 6.",
    "NOT CLOSED (the honest residual): the tails themselves remain open.  The " ++
      "criteria are CONDITIONAL on order-largeness plus per-ctx band budgets/window " ++
      "certificates; no unconditional emptiness is claimed.  What the order lever " ++
      "genuinely buys: (i) the tower/run ceil factors die under explicit order " ++
      "thresholds, reducing those tails to pure band-count budgets; (ii) the " ++
      "class-0/1/3 finite searches shrink to long periods; (iii) the remaining hard " ++
      "moduli are characterized - those whose cofactor lies in the small-order " ++
      "Mersenne-divisor families (enumerated exactly up to order 6 here; larger " ++
      "thresholds give larger finite lists of divisors of 2^k - 1, k <= threshold)." ]

theorem modulusTailCriteriaStatus_nonempty : modulusTailCriteriaStatus ≠ [] := by
  simp [modulusTailCriteriaStatus]

/-! ## Part 11.  Axiom-cleanliness audit -/

#print axioms canonGap_le_logFloor
#print axioms towerCycle_gapSum_le
#print axioms orbitOrderModulus_two_le
#print axioms orbitOrderModulus_odd
#print axioms orbitOrderModulus_dvd_two_pow_gapSum_sub_one
#print axioms orbit_two_pow_gapSum_eq_one
#print axioms orbit_orderOf_dvd_gapSum
#print axioms towerCycle_gapSum_ge_orderOf
#print axioms towerCycle_period_floor
#print axioms towerCycle_period_gt_of_order_gt
#print axioms orbit_orderOf_le_q_mul
#print axioms towerCycle_band4_quadruple_le
#print axioms deep_canonGap_ge_five
#print axioms towerCycle_gapSum_ge_deep
#print axioms towerCycle_deepCount_le
#print axioms towerTail_of_order_gt
#print axioms towerEnumResidual_of_tail_order_criterion
#print axioms class0_period_gt_of_order_gt
#print axioms class0WindowCheck_iff_long_of_order_gt
#print axioms class0Tail_of_order_gt
#print axioms class0Big_of_order_pruned
#print axioms class1Fibre_empty_of_period_band4_free
#print axioms class1Tail_of_band4FreePeriod
#print axioms class1BandFreePeriod_iff_long_of_order_gt
#print axioms class1Tail_of_order_gt
#print axioms class1PairDeep_split_at_tail
#print axioms runTail_of_order_gt
#print axioms runSettlement_split_at_tail
#print axioms class3Band3Free_iff_long_of_order_gt
#print axioms densePackTail_of_order_gt
#print axioms densePackStartsEmpty_split_at_tail
#print axioms zmod_dvd_two_pow_orderOf_sub_one
#print axioms orderOf_two_pos_of_odd
#print axioms mem_mersenneSmallOrderModuli_of_orderOf_le_six
#print axioms orderOf_two_le_six_of_mem
#print axioms towerCycle_exceptional_or_gapSum_gt_six
#print axioms modulusTailCriteriaStatus_nonempty

end

end Erdos260
