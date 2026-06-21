import Erdos260.Erdos260CycleCapstone

/-!
# DensePack class-3 fixed-point closure — wave 4: the datum lever

This module (NEW; it edits no existing file) attacks the wave-3 capstone field
`densePackCycle : DensePackCycleSplitResidual` with the wave-4 central lever: the orbit
datum `(q, K₀)` is `class1SlopeDatum ctx`, with the proved pins

* `class1SlopeDatum_q_eq`   : `q = oddpart(Q · (2|P| + 1))`,
* `class1SlopeDatum_K₀_eq`  : `K₀ = |P|`,
* `class1SlopeDatum_H_dvd`  : the divisor pin `(2K₀ + 1) ∣ q`,

so every per-class fixed-point family collapses to explicit finite `(q, K₀)` Diophantine
solutions.  Everything below is proved from the routing/orbit/datum arithmetic of the
canonical objects — no fabricated witnesses, no new axioms.

## What is newly closed here (all unconditional)

* **The band-3 fixed-point datum confinement** (`band3_fixedHit_pins`,
  `class3FixedHit_datum`, `class3FixedHit_iff_datum`): if the actual datum's orbit hits a
  band-3 fixed point `7F = q` at ANY index `j ≥ 1` (even base numerators have exactly the
  one-step tail at index `0`, and a fixed base `7K₀ = q` propagates to index `1`,
  `class3FixedHit_of_base` — so this notion captures every reachability route), then
  backward determinism pins `K₁ = F`, the base step pins `7·2^{g₀}·K₀ = 8q`, and the
  divisor pin `(2K₀+1) ∣ q` forces `(2K₀+1) ∣ 7·2^{g₀}`, hence `2K₀+1 = 7`:
  **`(q, K₀) = (21, 3)` exactly** — necessary AND sufficient (`canonGap 21 3 = 3`,
  `2³·3 − 21 = 3`, the orbit is constant).
* **The `q = 7` fixed family is VOID at the actual datum** (`class3_q7_orbit_ne_one`): the
  all-ones fixed point at `q = 7` would force `q = 21` through the confinement —
  contradiction.  The wave-3 honest hard family `densePackStarts_q7_dichotomy`(fixed
  branch) is vacuous in the model; hence the **NEW modulus closure**
  `densePackStarts_empty_of_modulus_seven` / `class3CycleBand3Free_of_modulus_seven`:
  `q = 7` joins the closed moduli.  Combined window
  (`modulus_eq_five_or_ge_thirteen_of_densePackStarts_nonempty`): a nonempty dense start
  set now forces `q = 5` or `q ≥ 13` — every odd modulus `< 13` except `5` is closed.
* **The all-band-3 cycle rigidity** (`band3_full_orbit_forces_fixed`,
  `band3_full_cycle_forces_fixed`, `band3_full_cycle_seven_dvd`): a period whose EVERY
  reading is band 3 forces the exact `1/7` fixed point `7·K₁ = q` (the deviation
  `7K − q` multiplies by `8` along band-3 steps and is bounded on the orbit), hence
  `7 ∣ q` — the band-3 mirror of `towerCycle_band4_full_forces_fixed`.
* **`b₃ < c` off the fixed point** (`band3CycleCount_lt_of_not_fixed` — the band-3 mirror
  of `towerBand4CycleCount_lt_of_not_fixed`; datum form
  `cycleBand3Residues_card_lt_of_offDatum`): on every actual context with
  `(q, K₀) ≠ (21, 3)`, EVERY orbit period has band-3 count strictly below the period —
  cycle band-3 density `1` happens ONLY on the confined `(21, 3)` family.  Off the datum
  the cycle-density count carries the strict factor
  (`densePackStarts_card_le_offDatum_density`), and the K.1.2 Nat cover follows from the
  per-ctx cycle-density check (`densePackCoverNat_of_cycle_density`).
* **The `(21, 3)` survivor characterized exactly**: the orbit is constantly `3`
  (`slopeOrbit_twentyone_three_const`), both cycle checks genuinely FAIL
  (`not_class3CycleBand3Free_of_datum`, `not_class3TopBandCycleFree_of_datum`), the dense
  start set IS the bare gap-floor filter (`densePackStarts_eq_floorFilter_of_datum`), and
  gated emptiness is EXACTLY the `≤ r + 1 ≤ 2` top-band gap-floor refutations
  (`densePackStarts_empty_iff_topBand_floor_of_gate_datum`) — the wave-3 `q = 7` hard
  family relocates verbatim to `(21, 3)`.
* **The survivor's datum arithmetic** (`densePack_datum_Q_oddPart`,
  `densePack_datum_Q_eq`, `densePack_datum_value_eq`): on the `(21, 3)` family the shell
  denominator has odd part exactly `3` (`Q = 3·2^t`), the chosen carry numerator is
  `P = 3`, and therefore **the Erdős weighted value is exactly a dyadic reciprocal**:
  `Σ n·dₙ/2ⁿ = 1/2^t`.  This is the complete `Q`-arithmetic the model pins at this layer
  (the shell carries only `0 < Q`); the family is NOT refuted here — recorded honestly as
  THE unique surviving band-3 fixed pair, now with its value forced dyadic.

## The wave-4 surface: `DensePackDatumSplitResidual`

The wave-3 `DensePackCycleSplitResidual` with every field ADDITIONALLY guarded by the
surviving-modulus window `q = 5 ∨ 13 ≤ q` — providers owe NOTHING on `q = 7` (and on the
other closed moduli) any more.  Bridges:

* `DensePackDatumSplitResidual.toCycleSplit` — lands EXACTLY in the capstone field type
  `DensePackCycleSplitResidual` (the complement moduli discharge through the proved cycle
  checks `q < 5` / `q = 7` / `q ∈ {9, 11}`);
* `DensePackCycleSplitResidual.toDatumSplit` — the converse weakening, so
  `nonempty_datumSplit_iff_cycleSplit`: the surfaces are EQUIVALENT — nothing is hidden;
* `erdos260_of_datumSplit` — the drop-in final endpoint with the class-3 slot carried by
  the wave-4 surface.

## The honest residual after this module

(a) Gated shells with `q = 5` or `q ≥ 13` whose top-band cycle residues meet band 3
(notably the `(21, 3)` fixed family): the `≤ r + 1 ≤ 2` gap-floor refutations — the floor
lives on the model-unconstrained escape gap, exactly as wave 2/3 proved.  (b) Ungated such
shells: the K.1.1 endpoint density, the K.1 interior, the K.1.2 Nat cover (with the
off-datum strict cycle-density count now available).  No formalized bridge ties the
digit-side gap floor to the orbit-side band beyond the shared index; we do NOT claim
unconditional closure of the atom, and we do NOT prove any context empty — the `(21, 3)`
family (with its forced dyadic value) genuinely survives at this layer.

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The band-3 fixed point: generic arithmetic

A band-3 fixed point of the E.13 step is a numerator `F` with `7F = q`: then `q/F = 7`
exactly, `canonGap q F = 3`, and `2³·F − q = F`.  At `(q, F) = (21, 3)` this is the
concrete surviving family. -/

/-- A `1/7` numerator reads band 3: `7F = q` gives `q/F = 7` and `canonGap q F = 3`. -/
theorem canonGap_of_seven_mul {q F : ℕ} (hF : 1 ≤ F) (h7 : 7 * F = q) :
    canonGap q F = 3 := by
  unfold canonGap
  have hdiv : q / F = 7 := Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [hdiv]
  have hlog : Nat.log 2 7 = 2 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  omega

/-- A `1/7` numerator is a FIXED POINT of the E.13 step: `2³·F − q = F`. -/
theorem boundedSlopeStep_of_seven_mul {q F : ℕ} (hF : 1 ≤ F) (h7 : 7 * F = q) :
    boundedSlopeStep q F = F := by
  unfold boundedSlopeStep
  rw [canonGap_of_seven_mul hF h7]
  have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
  rw [h8]
  omega

/-- `canonGap 21 3 = 3` (the surviving fixed pair reads band 3). -/
theorem canonGap_twentyone_three : canonGap 21 3 = 3 :=
  canonGap_of_seven_mul (by norm_num) (by norm_num)

/-- The E.13 step at `q = 21` fixes `K = 3`: `2³·3 − 21 = 3`. -/
theorem boundedSlopeStep_twentyone_three : boundedSlopeStep 21 3 = 3 :=
  boundedSlopeStep_of_seven_mul (by norm_num) (by norm_num)

/-- **The `(21, 3)` orbit is CONSTANT**: `K_j = 3` at every index (including the base). -/
theorem slopeOrbit_twentyone_three_const : ∀ j, slopeOrbit 21 3 j = 3 := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      show boundedSlopeStep 21 (slopeOrbit 21 3 j) = 3
      rw [ih]
      exact boundedSlopeStep_twentyone_three

/-- **Forward absorption**: once the orbit sits on a fixed point of the step, it stays
there at every later offset. -/
theorem slopeOrbit_const_of_fixed {q K₀ j : ℕ}
    (hfix : boundedSlopeStep q (slopeOrbit q K₀ j) = slopeOrbit q K₀ j) :
    ∀ s, slopeOrbit q K₀ (j + s) = slopeOrbit q K₀ j := by
  intro s
  induction s with
  | zero => rfl
  | succ s ih =>
      show boundedSlopeStep q (slopeOrbit q K₀ (j + s)) = slopeOrbit q K₀ j
      rw [ih]
      exact hfix

/-- **Backward determinism to index `1`**: if the orbit hits a fixed point of the step at
ANY index `j ≥ 1`, then already `K₁` is that fixed point (`slopeOrbit_cancel` on the odd
recurrent range — even base numerators have exactly the one-step tail at index `0`, which
this statement never reads). -/
theorem slopeOrbit_one_eq_of_hits_fixed {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀)
    (hKq : K₀ < q) {j : ℕ} (hj : 1 ≤ j)
    (hfix : boundedSlopeStep q (slopeOrbit q K₀ j) = slopeOrbit q K₀ j) :
    slopeOrbit q K₀ 1 = slopeOrbit q K₀ j := by
  have hconst := slopeOrbit_const_of_fixed hfix
  apply slopeOrbit_cancel hq hK1 hKq j le_rfl hj
  have h1 : slopeOrbit q K₀ (1 + j) = slopeOrbit q K₀ j := by
    rw [Nat.add_comm 1 j]
    exact hconst 1
  have h2 : slopeOrbit q K₀ (j + j) = slopeOrbit q K₀ j := hconst j
  rw [h1, h2]

/-! ## Part 2.  The all-band-3 cycle rigidity and `b₃ < c` off the fixed point

Along a band-3 step the integer deviation `7K − q` multiplies by `8`
(`K' = 8K − q ⇒ 7K' − q = 8(7K − q)`).  On a band-3-full orbit the deviation is both
`8ⁿ`-growing and bounded by `8q`, so it vanishes: `7K₁ = q` — the exact band-3 mirror of
`towerCycle_band4_full_forces_fixed`. -/

private theorem band3_dev_pow {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀) (hKq : K₀ < q)
    (hall : ∀ j, 1 ≤ j → canonGap q (slopeOrbit q K₀ j) = 3) :
    ∀ n, 7 * (slopeOrbit q K₀ (1 + n) : ℤ) - (q : ℤ)
      = 8 ^ n * (7 * (slopeOrbit q K₀ 1 : ℤ) - (q : ℤ)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hmem := slopeOrbit_mem hq hK1 hKq (1 + n)
      have hgap := hall (1 + n) (by omega)
      have hlow := (canonGap_bounds hq hmem.1 hmem.2).1
      rw [hgap] at hlow
      have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
      rw [h8] at hlow
      have hstepv : slopeOrbit q K₀ (1 + (n + 1))
          = 8 * slopeOrbit q K₀ (1 + n) - q := by
        show boundedSlopeStep q (slopeOrbit q K₀ (1 + n)) = _
        unfold boundedSlopeStep
        rw [hgap, h8]
      have hcast : (slopeOrbit q K₀ (1 + (n + 1)) : ℤ)
          = 8 * (slopeOrbit q K₀ (1 + n) : ℤ) - (q : ℤ) := by
        rw [hstepv, Nat.cast_sub hlow.le]
        push_cast
        ring
      have hlin : 7 * (slopeOrbit q K₀ (1 + (n + 1)) : ℤ) - (q : ℤ)
          = 8 * (7 * (slopeOrbit q K₀ (1 + n) : ℤ) - (q : ℤ)) := by
        rw [hcast]
        ring
      rw [hlin, ih, pow_succ]
      ring

/-- **A band-3-full orbit forces the exact `1/7` fixed point**: if EVERY positive index
reads band 3, then `7·K₁ = q`. -/
theorem band3_full_orbit_forces_fixed {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀)
    (hKq : K₀ < q)
    (hall : ∀ j, 1 ≤ j → canonGap q (slopeOrbit q K₀ j) = 3) :
    7 * slopeOrbit q K₀ 1 = q := by
  by_contra hne
  have hdev := band3_dev_pow hq hK1 hKq hall (q + 1)
  have hmem := slopeOrbit_mem hq hK1 hKq (1 + (q + 1))
  have hene : 7 * (slopeOrbit q K₀ 1 : ℤ) - (q : ℤ) ≠ 0 := by
    intro h0
    apply hne
    omega
  have habs1 : 1 ≤ |7 * (slopeOrbit q K₀ 1 : ℤ) - (q : ℤ)| := Int.one_le_abs hene
  have habs2 : |7 * (slopeOrbit q K₀ (1 + (q + 1)) : ℤ) - (q : ℤ)| < 8 * (q : ℤ) := by
    obtain ⟨hm1, hm2⟩ := hmem
    rw [abs_lt]
    constructor <;> omega
  rw [hdev, abs_mul, abs_pow] at habs2
  have h8abs : |(8 : ℤ)| = 8 := by norm_num
  rw [h8abs] at habs2
  have hge : (8 : ℤ) ^ (q + 1)
      ≤ 8 ^ (q + 1) * |7 * (slopeOrbit q K₀ 1 : ℤ) - (q : ℤ)| :=
    le_mul_of_one_le_right (by positivity) habs1
  have hgrow : 8 * (q : ℤ) < 8 ^ (q + 1) := by
    have h1 : q < 2 ^ q := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ q ≤ 8 ^ q := Nat.pow_le_pow_left (by norm_num) q
    have h3 : (8 : ℕ) ^ (q + 1) = 8 ^ q * 8 := pow_succ 8 q
    have hN : 8 * q < 8 ^ (q + 1) := by omega
    exact_mod_cast hN
  linarith

/-- **A band-3-full period forces the fixed point** (mod-period reduction to the full
orbit): `7·K₁ = q`. -/
theorem band3_full_cycle_forces_fixed {q K₀ c : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀)
    (hKq : K₀ < q) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    (hall : ∀ j, 1 ≤ j → j ≤ c → canonGap q (slopeOrbit q K₀ j) = 3) :
    7 * slopeOrbit q K₀ 1 = q := by
  apply band3_full_orbit_forces_fixed hq hK1 hKq
  intro j hj
  rw [slopeOrbit_eq_mod_period hc hper hj]
  refine hall (1 + (j - 1) % c) (by omega) ?_
  have := Nat.mod_lt (j - 1) (show 0 < c by omega)
  omega

/-- A band-3-full period forces `7 ∣ q` — band-3 cycle density `1` lives ONLY on the
`7 ∣ q` fixed-point family (the band-3 mirror of `towerCycle_band4_full_fifteen_dvd`). -/
theorem band3_full_cycle_seven_dvd {q K₀ c : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀)
    (hKq : K₀ < q) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    (hall : ∀ j, 1 ≤ j → j ≤ c → canonGap q (slopeOrbit q K₀ j) = 3) :
    7 ∣ q :=
  ⟨slopeOrbit q K₀ 1, (band3_full_cycle_forces_fixed hq hK1 hKq hc hper hall).symm⟩

/-- **The per-period band-3 count** (the `Icc`-form mirror of `towerBand4CycleCount`). -/
def band3CycleCount (q K₀ c : ℕ) : ℕ :=
  ((Finset.Icc 1 c).filter (fun j => canonGap q (slopeOrbit q K₀ j) = 3)).card

/-- The band-3 count never exceeds the period. -/
theorem band3CycleCount_le (q K₀ c : ℕ) : band3CycleCount q K₀ c ≤ c := by
  unfold band3CycleCount
  calc ((Finset.Icc 1 c).filter (fun j => canonGap q (slopeOrbit q K₀ j) = 3)).card
      ≤ (Finset.Icc 1 c).card := Finset.card_filter_le _ _
    _ = c := by rw [Nat.card_Icc]; omega

/-- **Off the fixed point the band-3 cycle count is strictly below the period**:
`7·K₁ ≠ q → b₃(q, K₀, c) ≤ c − 1` for every period `c` — the exact band-3 mirror of
`towerBand4CycleCount_lt_of_not_fixed`. -/
theorem band3CycleCount_lt_of_not_fixed {q K₀ c : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀)
    (hKq : K₀ < q) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    (hnf : 7 * slopeOrbit q K₀ 1 ≠ q) :
    band3CycleCount q K₀ c < c := by
  rcases Nat.lt_or_ge (band3CycleCount q K₀ c) c with h | h
  · exact h
  · exfalso
    have hcard : (Finset.Icc 1 c).card = c := by rw [Nat.card_Icc]; omega
    have heq : ((Finset.Icc 1 c).filter (fun j => canonGap q (slopeOrbit q K₀ j) = 3))
        = Finset.Icc 1 c := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      rw [hcard]
      exact h
    have hall : ∀ j, 1 ≤ j → j ≤ c → canonGap q (slopeOrbit q K₀ j) = 3 := by
      intro j h1 h2
      have hjmem : j ∈ (Finset.Icc 1 c).filter
          (fun j => canonGap q (slopeOrbit q K₀ j) = 3) := by
        rw [heq, Finset.mem_Icc]
        exact ⟨h1, h2⟩
      exact (Finset.mem_filter.mp hjmem).2
    exact hnf (band3_full_cycle_forces_fixed hq hK1 hKq hc hper hall)

/-! ## Part 3.  The datum confinement: every band-3 fixed-point hit forces `(q, K₀) = (21, 3)`

The wave-4 lever.  A hit at index `j ≥ 1` propagates back to `K₁ = F` (Part 1), the base
step pins `2^{g₀}·K₀ = q + F`, so `7·2^{g₀}·K₀ = 8q`; the divisor pin `(2K₀+1) ∣ q` then
gives `(2K₀+1) ∣ 7·2^{g₀}·(2K₀+1) − 2·(7·2^{g₀}·K₀) = 7·2^{g₀}`, and oddness leaves
`2K₀+1 = 7`.  Back-substituting, `21·2^{g₀} = 8q` with `q` odd forces `g₀ = 3`, `q = 21`. -/

/-- **The generic band-3 fixed-point pin extraction** (pure orbit/datum arithmetic): an
odd modulus with the divisor pin `(2K₀+1) ∣ q` whose orbit hits a band-3 fixed point
`7F = q` at any index `j ≥ 1` must have `(q, K₀) = (21, 3)`. -/
theorem band3_fixedHit_pins {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀) (hKq : K₀ < q)
    (hdvd : 2 * K₀ + 1 ∣ q) {j : ℕ} (hj : 1 ≤ j)
    (h7 : 7 * slopeOrbit q K₀ j = q) :
    q = 21 ∧ K₀ = 3 := by
  -- the hit propagates back to index 1
  have hmemj := slopeOrbit_mem hq hK1 hKq j
  have hfixj : boundedSlopeStep q (slopeOrbit q K₀ j) = slopeOrbit q K₀ j :=
    boundedSlopeStep_of_seven_mul hmemj.1 h7
  have h1 := slopeOrbit_one_eq_of_hits_fixed hq hK1 hKq hj hfixj
  have h71 : 7 * slopeOrbit q K₀ 1 = q := by rw [h1]; exact h7
  -- the base-step equation: 7·2^{g₀}·K₀ = 8q
  have hstep : slopeOrbit q K₀ 1 = boundedSlopeStep q K₀ := rfl
  have hbound := (canonGap_bounds hq hK1 hKq).1
  obtain ⟨g, hg⟩ : ∃ g, canonGap q K₀ = g := ⟨_, rfl⟩
  rw [hg] at hbound
  unfold boundedSlopeStep at hstep
  rw [hg] at hstep
  have hkey : 7 * (2 ^ g * K₀) = 8 * q := by omega
  -- the divisor pin forces 2K₀+1 = 7
  have hdvd16 : (2 * K₀ + 1) ∣ 16 * q := hdvd.mul_left 16
  have hexp : 7 * 2 ^ g * (2 * K₀ + 1) = 16 * q + 7 * 2 ^ g := by
    calc 7 * 2 ^ g * (2 * K₀ + 1) = 2 * (7 * (2 ^ g * K₀)) + 7 * 2 ^ g := by ring
      _ = 2 * (8 * q) + 7 * 2 ^ g := by rw [hkey]
      _ = 16 * q + 7 * 2 ^ g := by ring
  have hdvd7g : (2 * K₀ + 1) ∣ 7 * 2 ^ g := by
    have hL : (2 * K₀ + 1) ∣ 7 * 2 ^ g * (2 * K₀ + 1) := dvd_mul_left _ _
    rw [hexp] at hL
    have hsub := Nat.dvd_sub hL hdvd16
    rwa [Nat.add_sub_cancel_left] at hsub
  have hcop : Nat.Coprime (2 * K₀ + 1) (2 ^ g) :=
    Nat.Coprime.pow_right g (Nat.coprime_two_right.mpr ⟨K₀, by ring⟩)
  have hdvd7 : (2 * K₀ + 1) ∣ 7 := hcop.dvd_of_dvd_mul_right hdvd7g
  have hK3 : K₀ = 3 := by
    rcases (by norm_num : Nat.Prime 7).eq_one_or_self_of_dvd _ hdvd7 with h | h <;> omega
  refine ⟨?_, hK3⟩
  -- 21·2^{g₀} = 8q with q odd forces q = 21
  rw [hK3] at hkey
  obtain ⟨m, hm⟩ := hq
  rcases Nat.lt_or_ge g 3 with hg3 | hg3
  · have h2g : (2 : ℕ) ^ g = 1 ∨ (2 : ℕ) ^ g = 2 ∨ (2 : ℕ) ^ g = 4 := by
      rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2) with rfl | rfl | rfl
      · left; rw [pow_zero]
      · right; left; rw [pow_one]
      · right; right; norm_num
    rcases h2g with h | h | h <;> rw [h] at hkey <;> omega
  · obtain ⟨s, rfl⟩ : ∃ s, g = 3 + s := ⟨g - 3, by omega⟩
    have hpow : (2 : ℕ) ^ (3 + s) = 8 * 2 ^ s := by
      rw [pow_add]
      norm_num
    rw [hpow] at hkey
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · rw [pow_zero] at hkey
      omega
    · obtain ⟨t, ht⟩ := (dvd_pow_self 2 (by omega : s ≠ 0) : (2 : ℕ) ∣ 2 ^ s)
      rw [ht] at hkey
      omega

/-- **The named per-ctx band-3 fixed-point hit**: the actual datum's orbit reads a band-3
fixed point `7F = q` at some positive index. -/
def Class3FixedHit (ctx : ActualFailureContext) : Prop :=
  ∃ j, 1 ≤ j
    ∧ 7 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j
        = (class1SlopeDatum ctx).q

/-- **THE DATUM CONFINEMENT**: a band-3 fixed-point hit at the actual datum forces
`(q, K₀) = (21, 3)` exactly — the divisor pin `(2K₀+1) ∣ q` (from
`class1SlopeDatum_H_dvd` and `class1SlopeDatum_K₀_eq`) admits no other solution. -/
theorem class3FixedHit_datum (ctx : ActualFailureContext) (h : Class3FixedHit ctx) :
    (class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3 := by
  obtain ⟨j, hj, h7⟩ := h
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    have hH := class1SlopeDatum_H_dvd ctx
    rwa [← class1SlopeDatum_K₀_eq ctx] at hH
  exact band3_fixedHit_pins (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt hdvd hj h7

/-- The converse: at `(q, K₀) = (21, 3)` the hit is immediate (`K₁ = 3`, `7·3 = 21`). -/
theorem class3FixedHit_of_datum (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    Class3FixedHit ctx := by
  refine ⟨1, le_rfl, ?_⟩
  rw [hq, hK, slopeOrbit_twentyone_three_const 1]

/-- **The exact fixed-point characterization at the actual datum**: the orbit hits a
band-3 fixed point IFF `(q, K₀) = (21, 3)`. -/
theorem class3FixedHit_iff_datum (ctx : ActualFailureContext) :
    Class3FixedHit ctx
      ↔ (class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3 :=
  ⟨class3FixedHit_datum ctx, fun ⟨hq, hK⟩ => class3FixedHit_of_datum ctx hq hK⟩

/-- **The tail is captured**: a fixed BASE numerator (`7·K₀ = q` at index `0` — the only
possible pre-period state, even bases included) propagates to index `1`, so it is a
`Class3FixedHit` and the confinement applies to it as well. -/
theorem class3FixedHit_of_base (ctx : ActualFailureContext)
    (h : 7 * (class1SlopeDatum ctx).K₀ = (class1SlopeDatum ctx).q) :
    Class3FixedHit ctx := by
  refine ⟨1, le_rfl, ?_⟩
  have hfix : boundedSlopeStep (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
      = (class1SlopeDatum ctx).K₀ :=
    boundedSlopeStep_of_seven_mul (class1SlopeDatum ctx).hK₀_pos h
  have h1 : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1
      = boundedSlopeStep (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ := rfl
  rw [h1, hfix]
  exact h

/-- **An all-band-3 period at the actual datum forces `(q, K₀) = (21, 3)`** — the brief's
"all-band-3 constant cycle reachable from the actual datum" confinement, via the cycle
rigidity and the divisor pin. -/
theorem class3CycleBand3Full_datum (ctx : ActualFailureContext) {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hall : ∀ j, 1 ≤ j → j ≤ c → canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 3) :
    (class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3 :=
  class3FixedHit_datum ctx
    ⟨1, le_rfl, band3_full_cycle_forces_fixed (class1SlopeDatum ctx).hq_odd
      (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum ctx).hK₀_lt hc hper hall⟩

/-! ## Part 4.  The `q = 7` fixed family is VOID — the modulus joins the closed list

The wave-3 honest hard family was `q = 7` with `K₁ = 1` (the all-ones fixed point, which
genuinely defeats every cycle check).  At the actual datum that hit would force `q = 21`
through the confinement — contradiction.  So on every actual `q = 7` shell the orbit is
unfixed, the swap-cycle closure applies, and the dense start set is EMPTY. -/

/-- **The `q = 7` voiding**: at the actual datum the all-ones fixed point is impossible —
`K₁ = 1` with `q = 7` is a band-3 fixed hit (`7·1 = 7`), which the confinement sends to
`q = 21`. -/
theorem class3_q7_orbit_ne_one (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 7) :
    slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1 ≠ 1 := by
  intro h1
  have hhit : Class3FixedHit ctx := ⟨1, le_rfl, by rw [h1, hq]⟩
  have h21 := (class3FixedHit_datum ctx hhit).1
  omega

/-- **NEW closed cycle family `q = 7`**: the band-3 cycle check holds on EVERY actual
`q = 7` shell (the fixed branch is void, so the wave-3 unfixed closure is unconditional). -/
theorem class3CycleBand3Free_of_modulus_seven (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 7) :
    Class3CycleBand3Free ctx :=
  class3CycleBand3Free_of_q7_unfixed ctx hq (class3_q7_orbit_ne_one ctx hq)

/-- **NEW modulus closure `q = 7`**: the dense start set is PROVABLY EMPTY on every actual
shell with `q = 7` — the wave-3 dichotomy collapses to its empty branch. -/
theorem densePackStarts_empty_of_modulus_seven (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 7) :
    genuineDensePackStarts ctx = ∅ :=
  densePackStarts_empty_of_cycleBand3Free ctx (class3CycleBand3Free_of_modulus_seven ctx hq)

/-- **The sharpened modulus window**: a nonempty dense start set forces `q = 5` or
`q ≥ 13` — every odd modulus below `13` except `5` is now closed (`q < 5` wave 2; `q = 7`
HERE; `q ∈ {9, 11}` wave 3; even `q` impossible). -/
theorem modulus_eq_five_or_ge_thirteen_of_densePackStarts_nonempty
    (ctx : ActualFailureContext) (h : (genuineDensePackStarts ctx).Nonempty) :
    (class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q := by
  obtain ⟨h5, hwin⟩ := modulus_window_of_densePackStarts_nonempty ctx h
  rcases hwin with h7 | h13
  · left
    obtain ⟨m, hm⟩ := (class1SlopeDatum ctx).hq_odd
    have hcase : (class1SlopeDatum ctx).q = 5 ∨ (class1SlopeDatum ctx).q = 7 := by omega
    rcases hcase with hc | hc
    · exact hc
    · exfalso
      obtain ⟨k, hk⟩ := h
      rw [densePackStarts_empty_of_modulus_seven ctx hc] at hk
      exact Finset.notMem_empty k hk
  · right
    exact h13

/-- **The closed-moduli discharge**: outside the surviving window `q = 5 ∨ 13 ≤ q`, the
band-3 cycle check holds outright (`q < 5` / `q = 7` / `q ∈ {9, 11}`; even `q` is
impossible by the datum parity). -/
theorem class3CycleBand3Free_of_modulus_complement (ctx : ActualFailureContext)
    (hq : ¬((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q)) :
    Class3CycleBand3Free ctx := by
  obtain ⟨m, hm⟩ := (class1SlopeDatum ctx).hq_odd
  have hcase : (class1SlopeDatum ctx).q < 5 ∨ (class1SlopeDatum ctx).q = 7
      ∨ (8 ≤ (class1SlopeDatum ctx).q ∧ (class1SlopeDatum ctx).q < 13) := by omega
  rcases hcase with h | h | ⟨h8, h13⟩
  · exact class3CycleBand3Free_of_modulus_lt_five ctx h
  · exact class3CycleBand3Free_of_modulus_seven ctx h
  · exact class3CycleBand3Free_of_modulus_window ctx h8 h13

/-! ## Part 5.  `b₃ < c` at the datum off `(21, 3)`, and the sharpened counts -/

/-- **Off the confined pair the band-3 residue count is strictly below EVERY period**: on
an actual context with `(q, K₀) ≠ (21, 3)`, cycle band-3 density `1` is impossible. -/
theorem cycleBand3Residues_card_lt_of_offDatum (ctx : ActualFailureContext)
    (hoff : ¬((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3))
    {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) :
    (cycleBand3Residues ctx c).card < c := by
  rcases Nat.lt_or_ge (cycleBand3Residues ctx c).card c with h | h
  · exact h
  · exfalso
    apply hoff
    apply class3CycleBand3Full_datum ctx hc hper
    intro j h1 h2
    have hsub : cycleBand3Residues ctx c ⊆ Finset.range c := Finset.filter_subset _ _
    have heq : cycleBand3Residues ctx c = Finset.range c :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range]; exact h)
    have hmem : j - 1 ∈ cycleBand3Residues ctx c := by
      rw [heq, Finset.mem_range]
      omega
    rw [mem_cycleBand3Residues] at hmem
    have hidx : 1 + (j - 1) = j := by omega
    rw [hidx] at hmem
    exact hmem.2

/-- **The off-datum strict cycle-density count**: away from `(21, 3)` SOME period
`1 ≤ c ≤ q` carries BOTH the count bound and the strict residue deficit `b₃ < c`. -/
theorem densePackStarts_card_le_offDatum_density (ctx : ActualFailureContext)
    (hoff : ¬((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3)) :
    ∃ c, 1 ≤ c ∧ c ≤ (class1SlopeDatum ctx).q
      ∧ (cycleBand3Residues ctx c).card < c
      ∧ (genuineDensePackStarts ctx).card
        ≤ (cycleBand3Residues ctx c).card
          * (((supportShell ctx.shell.d ctx.shell.X).card - 1) / c + 2) := by
  obtain ⟨c, hc1, hcq, hper⟩ := class1Fibre_orbit_period_exists ctx
  exact ⟨c, hc1, hcq, cycleBand3Residues_card_lt_of_offDatum ctx hoff hc1 hper,
    densePackStarts_card_le_cycle_density ctx hc1 hper⟩

/-- **The K.1.2 Nat cover from the per-ctx cycle-density check** (the exact-`ℕ` mirror of
`amortizedCover_of_cycle_density`, landing in the capstone's `ungatedCoverNat` form):
`b₃ · (⌊(K−1)/c⌋ + 2) · mult ≤ markers` discharges the cover field. -/
theorem densePackCoverNat_of_cycle_density (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (h : (cycleBand3Residues ctx c).card
          * (((supportShell ctx.shell.d ctx.shell.X).card - 1) / c + 2)
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card) :
    (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  le_trans
    (Nat.mul_le_mul_right _ (densePackStarts_card_le_cycle_density ctx hc hper)) h

/-! ## Part 6.  The `(21, 3)` survivor characterized — orbit, checks, floor filter, and
the forced dyadic value

`(q, K₀) = (21, 3)` is THE unique band-3 fixed pair compatible with the datum.  There the
orbit is constantly `3`, every window start carries the band pin automatically, and both
cycle checks genuinely fail — the wave-3 `q = 7` hard-family analysis relocates verbatim.
The datum arithmetic additionally pins the shell: `oddpart(Q) = 3` and the Erdős weighted
value is EXACTLY `1/2^t`. -/

/-- At the `(21, 3)` datum every period fails the band-3 cycle check (the first index
already reads band 3) — the honest obstruction, relocated from `q = 7`. -/
theorem not_class3CycleBand3Free_of_datum (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    ¬ Class3CycleBand3Free ctx := by
  rintro ⟨c, hc1, hper, hband⟩
  refine hband 1 le_rfl hc1 ?_
  rw [hq, hK, slopeOrbit_twentyone_three_const 1]
  exact canonGap_twentyone_three

/-- At the `(21, 3)` datum the TOP-BAND cycle check fails as well: the top window
position `i + K − 1` exists (`i ≥ 1`, `K ≥ 1`) and reads the constant band-3 residue. -/
theorem not_class3TopBandCycleFree_of_datum (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    ¬ Class3TopBandCycleFree ctx := by
  rintro ⟨c, hc1, hper, hfree⟩
  have hi := n24_firstIndexAbove_pos ctx
  have hwidth := cnlMulti_r_add_one_le_width ctx
  refine hfree (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
      + (supportShell ctx.shell.d ctx.shell.X).card - 1)
    (by omega) (by omega) (by omega) ?_
  rw [hq, hK, slopeOrbit_twentyone_three_const]
  exact canonGap_twentyone_three

/-- **`(21, 3)`: the dense start set IS the bare gap-floor filter** (the band pin holds at
EVERY window start on the constant orbit — the mirror of
`densePackStarts_eq_floorFilter_of_q7_fixed`). -/
theorem densePackStarts_eq_floorFilter_of_datum (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    genuineDensePackStarts ctx
      = ctx.n24CarryData.starts.filter (fun k =>
          129 * shellLadderDepth ctx + 64
            ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r) := by
  ext k
  rw [mem_densePackStarts_iff, Finset.mem_filter]
  constructor
  · rintro ⟨hstart, hgw, _⟩
    exact ⟨hstart, hgw⟩
  · rintro ⟨hstart, hgw⟩
    refine ⟨hstart, hgw, ?_⟩
    rw [hq, hK, slopeOrbit_twentyone_three_const k]
    exact canonGap_twentyone_three

/-- **The gated `(21, 3)` family characterized**: emptiness is EXACTLY the gap-floor
refutation at the `≤ r + 1 ≤ 2` top-band window starts (the band pin is automatic on the
constant orbit) — the minimal honest residual of the surviving hard family. -/
theorem densePackStarts_empty_iff_topBand_floor_of_gate_datum (ctx : ActualFailureContext)
    (hg : class3Gate ctx)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    genuineDensePackStarts ctx = ∅
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card ≤ k + ctx.n24CarryData.r + 1 →
          ¬(129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r) := by
  rw [densePackStarts_empty_iff_topBand_of_gate ctx hg]
  constructor
  · intro h k hstart htop hfloor
    refine h k hstart htop ⟨hfloor, ?_⟩
    rw [hq, hK, slopeOrbit_twentyone_three_const k]
    exact canonGap_twentyone_three
  · intro h k hstart htop hpins
    exact h k hstart htop hpins.1

/-- **The survivor's denominator pin**: on the `(21, 3)` family the shell denominator has
odd part EXACTLY `3` (`21 = oddpart(Q · 7)` with `K₀ = |P| = 3`). -/
theorem densePack_datum_Q_oddPart (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    ordCompl[2] ctx.shell.Q = 3 := by
  have habs : ctx.shell.hrational.choose.natAbs = 3 := by
    rw [← class1SlopeDatum_K₀_eq ctx]
    exact hK
  have hqe := class1SlopeDatum_q_eq ctx
  rw [habs] at hqe
  rw [hq] at hqe
  have h7 : (2 * 3 + 1 : ℕ) = 7 := by norm_num
  rw [h7] at hqe
  have hcompl : apOddModulus ctx.shell.Q 7 = ordCompl[2] ctx.shell.Q * 7 := by
    show ordCompl[2] (ctx.shell.Q * 7) = _
    exact ordCompl_two_mul_odd ctx.shell.hQ.ne' ⟨3, by norm_num⟩
  rw [hcompl] at hqe
  omega

/-- **The survivor's denominator shape**: `Q = 3 · 2^t`. -/
theorem densePack_datum_Q_eq (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    ∃ t : ℕ, ctx.shell.Q = 3 * 2 ^ t := by
  refine ⟨ctx.shell.Q.factorization 2, ?_⟩
  have h3 := densePack_datum_Q_oddPart ctx hq hK
  have hself := Nat.ordProj_mul_ordCompl_eq_self ctx.shell.Q 2
  rw [h3] at hself
  omega

/-- **THE VALUE PIN OF THE SURVIVING FAMILY**: on the `(21, 3)` family the chosen carry
numerator is `P = 3` and `Q = 3·2^t`, so the Erdős weighted value is EXACTLY the dyadic
reciprocal `Σ n·dₙ/2ⁿ = 1/2^t` — the complete datum arithmetic of the unique surviving
band-3 fixed pair (recorded honestly; the model pins nothing more on `Q` at this layer). -/
theorem densePack_datum_value_eq (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    ∃ t : ℕ, ctx.shell.Q = 3 * 2 ^ t
      ∧ realWeightedValue (natBinaryAsReal ctx.shell.d) = 1 / 2 ^ t := by
  obtain ⟨t, hQ⟩ := densePack_datum_Q_eq ctx hq hK
  refine ⟨t, hQ, ?_⟩
  have hspec := ctx.shell.hrational.choose_spec
  have hP3 : ctx.shell.hrational.choose = 3 := by
    have hpos : 0 < ctx.shell.hrational.choose :=
      failingShell_carry_pos ctx.shell _ hspec
    have habs : ctx.shell.hrational.choose.natAbs = 3 := by
      rw [← class1SlopeDatum_K₀_eq ctx]
      exact hK
    omega
  rw [hspec, hP3, hQ]
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- The fixed-hit forms of the survivor pins (composed through the confinement). -/
theorem class3FixedHit_value_eq (ctx : ActualFailureContext) (h : Class3FixedHit ctx) :
    ∃ t : ℕ, ctx.shell.Q = 3 * 2 ^ t
      ∧ realWeightedValue (natBinaryAsReal ctx.shell.d) = 1 / 2 ^ t := by
  obtain ⟨hq, hK⟩ := class3FixedHit_datum ctx h
  exact densePack_datum_value_eq ctx hq hK

/-! ## Part 7.  The wave-4 surface: the datum-guarded cycle-split residual

The wave-3 `DensePackCycleSplitResidual` with every field additionally guarded by the
surviving-modulus window `q = 5 ∨ 13 ≤ q`.  Strictly less is demanded (nothing on `q = 7`
any more); the bridge back is lossless through the proved closed-moduli cycle checks. -/

/-- **The wave-4 datum-split residual** — the wave-3 cycle-split fields, each demanded
ONLY on the surviving moduli `q = 5 ∨ 13 ≤ q` (every other modulus is closed by a proved
cycle check, including the NEW `q = 7`). -/
structure DensePackDatumSplitResidual where
  /-- Gated surviving-modulus shells whose top-band cycle residues meet band 3 (e.g. the
  `(21, 3)` fixed family): the dense start set is empty — equivalently the
  `≤ r + 1 ≤ 2` top-band gap-floor refutations. -/
  gatedEmpty : ∀ ctx : ActualFailureContext, class3Gate ctx →
    ¬ Class3TopBandCycleFree ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    genuineDensePackStarts ctx = ∅
  /-- Ungated surviving-modulus shells whose cycle meets band 3: the K.1.1 coarea
  hit-density at the descent endpoints. -/
  ungatedDensity : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    densePackEndpointDensity ctx
  /-- Ungated surviving-modulus shells whose top-band cycle residues meet band 3: the K.1
  active-window interior containment. -/
  ungatedInterior : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
    ¬ Class3TopBandCycleFree ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card
  /-- Ungated surviving-modulus shells whose cycle meets band 3: the corrected K.1.2
  cover in exact `ℕ` form (dischargeable from the per-ctx cycle-density check,
  `densePackCoverNat_of_cycle_density`; off `(21, 3)` the count carries `b₃ < c`). -/
  ungatedCoverNat : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card

namespace DensePackDatumSplitResidual

/-- **The lossless bridge into the EXACT capstone field type**: outside the surviving
window every field's cycle-check guard is contradicted by the proved closed-moduli checks
(`q < 5`, the NEW `q = 7`, `q ∈ {9, 11}`), so nothing is lost. -/
def toCycleSplit (R : DensePackDatumSplitResidual) : DensePackCycleSplitResidual where
  gatedEmpty := fun ctx hg hfree => by
    by_cases hmod : (class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q
    · exact R.gatedEmpty ctx hg hfree hmod
    · exact absurd (class3TopBandCycleFree_of_cycleBand3Free ctx
        (class3CycleBand3Free_of_modulus_complement ctx hmod)) hfree
  ungatedDensity := fun ctx hg hfree => by
    by_cases hmod : (class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q
    · exact R.ungatedDensity ctx hg hfree hmod
    · exact absurd (class3CycleBand3Free_of_modulus_complement ctx hmod) hfree
  ungatedInterior := fun ctx hg hfree => by
    by_cases hmod : (class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q
    · exact R.ungatedInterior ctx hg hfree hmod
    · exact absurd (class3TopBandCycleFree_of_cycleBand3Free ctx
        (class3CycleBand3Free_of_modulus_complement ctx hmod)) hfree
  ungatedCoverNat := fun ctx hg hfree => by
    by_cases hmod : (class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q
    · exact R.ungatedCoverNat ctx hg hfree hmod
    · exact absurd (class3CycleBand3Free_of_modulus_complement ctx hmod) hfree

/-- Direct gated-shell emptiness projection from the datum-split surface. -/
theorem densePackStarts_empty_of_gate (R : DensePackDatumSplitResidual)
    (ctx : ActualFailureContext) (hg : class3Gate ctx) :
    genuineDensePackStarts ctx = ∅ := by
  by_cases hfree : Class3TopBandCycleFree ctx
  · exact densePackStarts_empty_of_gate_topBandCycleFree ctx hg hfree
  · by_cases hmod : (class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q
    · exact R.gatedEmpty ctx hg hfree hmod
    · exact absurd (class3TopBandCycleFree_of_cycleBand3Free ctx
        (class3CycleBand3Free_of_modulus_complement ctx hmod)) hfree

/-- Direct `r = 0` emptiness projection from the datum-split surface. -/
theorem densePackStarts_empty_of_r_eq_zero (R : DensePackDatumSplitResidual)
    (ctx : ActualFailureContext) (hr : ctx.n24CarryData.r = 0) :
    genuineDensePackStarts ctx = ∅ :=
  R.densePackStarts_empty_of_gate ctx (class3Gate_of_r_eq_zero ctx hr)

/-- Direct shallow-depth emptiness projection from the datum-split surface. -/
theorem densePackStarts_empty_of_L_le (R : DensePackDatumSplitResidual)
    (ctx : ActualFailureContext) (hL : shellLadderDepth ctx ≤ 15420) :
    genuineDensePackStarts ctx = ∅ :=
  R.densePackStarts_empty_of_gate ctx (class3Gate_of_L_le ctx hL)

/-- Direct class-3 ledger bridge from the datum-split surface, at any budget. -/
theorem hDensePackField (R : DensePackDatumSplitResidual)
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hroute : ∀ ctx : ActualFailureContext, (budget ctx).route = genuineChargeRoute ctx) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 3
        ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  ((R.toCycleSplit).toRegimeSplit budget).toCorrected.hDensePackField hroute

end DensePackDatumSplitResidual

/-- **The converse weakening**: any wave-3 cycle-split provider restricts to the wave-4
surface — the new presentation hides no strength. -/
def DensePackCycleSplitResidual.toDatumSplit (R : DensePackCycleSplitResidual) :
    DensePackDatumSplitResidual where
  gatedEmpty := fun ctx hg hfree _ => R.gatedEmpty ctx hg hfree
  ungatedDensity := fun ctx hg hfree _ => R.ungatedDensity ctx hg hfree
  ungatedInterior := fun ctx hg hfree _ => R.ungatedInterior ctx hg hfree
  ungatedCoverNat := fun ctx hg hfree _ => R.ungatedCoverNat ctx hg hfree

/-- **The two surfaces are EQUIVALENT** — the wave-4 residual is exactly the wave-3 one
with the proved modulus closures (including the new `q = 7` voiding) folded in. -/
theorem nonempty_datumSplit_iff_cycleSplit :
    Nonempty DensePackDatumSplitResidual ↔ Nonempty DensePackCycleSplitResidual :=
  ⟨fun ⟨R⟩ => ⟨R.toCycleSplit⟩, fun ⟨S⟩ => ⟨S.toDatumSplit⟩⟩

/-- **The final endpoint with the class-3 slot at the wave-4 datum-split surface**:
`Erdos260Statement` from the six other sharp fields plus the datum-guarded residual,
through the existing wave-3 drop-in `erdos260_of_cycleSplit`. -/
theorem erdos260_of_datumSplit
    (towerCount : Class2DeepShellCountBound)
    (runSplit : ∀ ctx : ActualFailureContext, RunClass5SplitBoundary ctx)
    (returnSmall : Class4FibreSmall)
    (returnDigit : ∀ ctx : ActualFailureContext, ReturnClass4DigitResidual ctx)
    (class0Pinned : ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q))
    (class1Pinned : ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      1 ≤ k →
      64 ∣ shellLadderDepth ctx →
      9 ≤ (class1SlopeDatum ctx).q →
      ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
      Odd (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) →
      64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          = 129 * shellLadderDepth ctx + 64 →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) ≠ 4)
    (datum : DensePackDatumSplitResidual) :
    Erdos260Statement :=
  erdos260_of_cycleSplit towerCount runSplit returnSmall returnDigit class0Pinned
    class1Pinned datum.toCycleSplit

/-! ## Part 8.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the wave-4 class-3 fixed-point closure. -/
def densePackFixedPointClosureStatus : List String :=
  [ "CLOSED (the band-3 fixed-point datum confinement, NEW - the wave-4 lever): " ++
      "band3_fixedHit_pins / class3FixedHit_datum / class3FixedHit_iff_datum - the " ++
      "actual datum's orbit hits a band-3 fixed point 7F = q at some index j >= 1 IFF " ++
      "(q, K0) = (21, 3). Proof: backward determinism pins K1 = F " ++
      "(slopeOrbit_one_eq_of_hits_fixed via slopeOrbit_cancel), the base step pins " ++
      "7*2^g0*K0 = 8q, and the divisor pin (2K0+1) | q (class1SlopeDatum_H_dvd + " ++
      "class1SlopeDatum_K0_eq) forces (2K0+1) | 7*2^g0, hence 2K0+1 = 7, K0 = 3, and " ++
      "21*2^g0 = 8q with odd q gives g0 = 3, q = 21. Even-K0 tails are captured: the " ++
      "only pre-period state is index 0, and a fixed base propagates to index 1 " ++
      "(class3FixedHit_of_base); the orbit indices the dense starts read are all >= 1.",
    "VOIDED (the q = 7 fixed family, NEW): class3_q7_orbit_ne_one - at EVERY actual " ++
      "q = 7 shell the all-ones fixed point K1 = 1 is IMPOSSIBLE (it is a band-3 fixed " ++
      "hit, which the confinement sends to q = 21). The wave-3 honest hard family " ++
      "(densePackStarts_q7_dichotomy fixed branch, not_class3CycleBand3Free_of_q7_fixed) " ++
      "is VACUOUS in the model; q = 7 joins the closed moduli: " ++
      "class3CycleBand3Free_of_modulus_seven, densePackStarts_empty_of_modulus_seven.",
    "CLOSED (sharpened modulus window, NEW): " ++
      "modulus_eq_five_or_ge_thirteen_of_densePackStarts_nonempty - a nonempty dense " ++
      "start set forces q = 5 or q >= 13; every odd modulus < 13 except 5 is closed " ++
      "(q < 5 wave 2; q = 7 HERE; q in {9,11} wave 3). Complement discharge: " ++
      "class3CycleBand3Free_of_modulus_complement.",
    "CLOSED (all-band-3 cycle rigidity, NEW - the band-3 mirror of the tower line): " ++
      "a period whose EVERY reading is band 3 forces the exact 1/7 fixed point " ++
      "7*K1 = q (band3_full_orbit_forces_fixed: the deviation 7K - q multiplies by 8 " ++
      "along band-3 steps and is bounded by 8q on the orbit; cycle form " ++
      "band3_full_cycle_forces_fixed; 7 | q form band3_full_cycle_seven_dvd). At the " ++
      "actual datum an all-band-3 period forces (q, K0) = (21, 3) " ++
      "(class3CycleBand3Full_datum).",
    "CLOSED (b3 < c off the fixed point, NEW): band3CycleCount_lt_of_not_fixed " ++
      "(generic, Icc form, mirror of towerBand4CycleCount_lt_of_not_fixed) and " ++
      "cycleBand3Residues_card_lt_of_offDatum (datum form): on every actual context " ++
      "with (q, K0) != (21, 3), EVERY orbit period has band-3 residue count strictly " ++
      "below the period - cycle band-3 density 1 happens ONLY on the confined (21, 3) " ++
      "family. Off-datum strict density count: densePackStarts_card_le_offDatum_density " ++
      "(some period 1 <= c <= q with b3 < c AND |starts3| <= b3*((K-1)/c + 2)). The " ++
      "K.1.2 Nat cover discharges from the per-ctx cycle-density check: " ++
      "densePackCoverNat_of_cycle_density.",
    "CHARACTERIZED (the (21, 3) survivor, NEW): canonGap 21 3 = 3, 2^3*3 - 21 = 3 " ++
      "(canonGap_twentyone_three, boundedSlopeStep_twentyone_three), the orbit is " ++
      "CONSTANT 3 (slopeOrbit_twentyone_three_const), both cycle checks genuinely FAIL " ++
      "(not_class3CycleBand3Free_of_datum, not_class3TopBandCycleFree_of_datum), the " ++
      "dense start set IS the bare gap-floor filter " ++
      "(densePackStarts_eq_floorFilter_of_datum), and gated emptiness is EXACTLY the " ++
      "<= r+1 <= 2 top-band gap-floor refutations " ++
      "(densePackStarts_empty_iff_topBand_floor_of_gate_datum) - the wave-3 q = 7 " ++
      "hard-family analysis relocates verbatim to (21, 3).",
    "DATUM ARITHMETIC OF THE SURVIVOR (NEW): densePack_datum_Q_oddPart - on the " ++
      "(21, 3) family oddpart(Q) = 3 exactly (21 = oddpart(Q*7) with K0 = |P| = 3); " ++
      "densePack_datum_Q_eq - Q = 3*2^t; densePack_datum_value_eq / " ++
      "class3FixedHit_value_eq - P = 3 and THE ERDOS WEIGHTED VALUE IS EXACTLY THE " ++
      "DYADIC RECIPROCAL sum n*d_n/2^n = 1/2^t. The model pins nothing more on Q at " ++
      "this layer (the shell carries only 0 < Q), so the family is NOT refuted - " ++
      "recorded honestly as THE unique surviving band-3 fixed pair, with its value " ++
      "forced dyadic (any future digit-side fact contradicting a dyadic weighted value " ++
      "on a failing shell would void it).",
    "SURFACE (the wave-4 residual): DensePackDatumSplitResidual - the wave-3 " ++
      "cycle-split fields, each ADDITIONALLY guarded by the surviving-modulus window " ++
      "q = 5 or 13 <= q (providers owe NOTHING on q = 7 and the other closed moduli " ++
      "any more). Bridges: DensePackDatumSplitResidual.toCycleSplit (lands EXACTLY in " ++
      "the capstone field type DensePackCycleSplitResidual - the densePackCycle slot " ++
      "of Erdos260CycleResidual consumes it as-is), " ++
      "DensePackCycleSplitResidual.toDatumSplit (converse weakening), " ++
      "nonempty_datumSplit_iff_cycleSplit (EQUIVALENT surfaces). Endpoint: " ++
      "erdos260_of_datumSplit (the drop-in final assembly through " ++
      "erdos260_of_cycleSplit).",
    "RESIDUAL (honest, what remains open): (a) gated shells with q = 5 or q >= 13 " ++
      "whose top-band cycle residues meet band 3 (notably the (21, 3) fixed family): " ++
      "the <= r+1 <= 2 per-shell gap-floor refutations - the floor lives on the " ++
      "model-unconstrained escape gap (wave-3 escape-gap blow-up), so it is not " ++
      "refutable at this layer; (b) ungated such shells: the K.1.1 endpoint density, " ++
      "the K.1 interior, the corrected K.1.2 Nat cover (with the off-datum strict " ++
      "cycle-density count and the q = 5 halving available against it). No formalized " ++
      "bridge ties the digit-side gap floor to the orbit-side band beyond the shared " ++
      "index k; we do NOT claim unconditional closure of the atom, and we do NOT prove " ++
      "any context empty - the (21, 3) family genuinely survives at this layer." ]

theorem densePackFixedPointClosureStatus_nonempty :
    densePackFixedPointClosureStatus ≠ [] := by
  simp [densePackFixedPointClosureStatus]

/-! ## Part 9.  Axiom-cleanliness audit -/

#print axioms canonGap_of_seven_mul
#print axioms boundedSlopeStep_of_seven_mul
#print axioms canonGap_twentyone_three
#print axioms boundedSlopeStep_twentyone_three
#print axioms slopeOrbit_twentyone_three_const
#print axioms slopeOrbit_const_of_fixed
#print axioms slopeOrbit_one_eq_of_hits_fixed
#print axioms band3_full_orbit_forces_fixed
#print axioms band3_full_cycle_forces_fixed
#print axioms band3_full_cycle_seven_dvd
#print axioms band3CycleCount_le
#print axioms band3CycleCount_lt_of_not_fixed
#print axioms band3_fixedHit_pins
#print axioms class3FixedHit_datum
#print axioms class3FixedHit_of_datum
#print axioms class3FixedHit_iff_datum
#print axioms class3FixedHit_of_base
#print axioms class3CycleBand3Full_datum
#print axioms class3_q7_orbit_ne_one
#print axioms class3CycleBand3Free_of_modulus_seven
#print axioms densePackStarts_empty_of_modulus_seven
#print axioms modulus_eq_five_or_ge_thirteen_of_densePackStarts_nonempty
#print axioms class3CycleBand3Free_of_modulus_complement
#print axioms cycleBand3Residues_card_lt_of_offDatum
#print axioms densePackStarts_card_le_offDatum_density
#print axioms densePackCoverNat_of_cycle_density
#print axioms not_class3CycleBand3Free_of_datum
#print axioms not_class3TopBandCycleFree_of_datum
#print axioms densePackStarts_eq_floorFilter_of_datum
#print axioms densePackStarts_empty_iff_topBand_floor_of_gate_datum
#print axioms densePack_datum_Q_oddPart
#print axioms densePack_datum_Q_eq
#print axioms densePack_datum_value_eq
#print axioms class3FixedHit_value_eq
#print axioms DensePackDatumSplitResidual.toCycleSplit
#print axioms DensePackDatumSplitResidual.densePackStarts_empty_of_gate
#print axioms DensePackDatumSplitResidual.densePackStarts_empty_of_r_eq_zero
#print axioms DensePackDatumSplitResidual.densePackStarts_empty_of_L_le
#print axioms DensePackDatumSplitResidual.hDensePackField
#print axioms DensePackCycleSplitResidual.toDatumSplit
#print axioms nonempty_datumSplit_iff_cycleSplit
#print axioms erdos260_of_datumSplit
#print axioms densePackFixedPointClosureStatus_nonempty

end

end Erdos260
