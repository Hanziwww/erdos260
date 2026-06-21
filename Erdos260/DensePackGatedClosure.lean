import Erdos260.Erdos260DatumCapstone
import Erdos260.RunCycleNumericClosure

/-!
# DensePack class-3 gated closure — wave 5: the band-3 datum enumeration

This module (NEW; it edits no existing file) attacks the wave-4 capstone field
`densePackDatum : DensePackDatumSplitResidual` (`DensePackFixedPointClosure`, consumed by
`Erdos260DatumCapstone` via `toCycleSplit`) by the finite datum enumeration the divisor
pin makes available: on the surviving window `q = 5 ∨ 13 ≤ q` with `q < 64` the pinned
datum `(q, K₀)` (`K₀ = |P|`, `(2K₀+1) ∣ q` — `class1SlopeDatum_H_dvd` /
`class1SlopeDatum_K₀_eq`) admits EXACTLY `55` pairs (`band3_datum_enum`), and each pair's
recurrent orbit cycle is a finite computation.

## What is newly closed here (all unconditional)

* **The 55-pair datum enumeration** (`band3_datum_enum`): on the surviving window the
  divisor pin admits exactly `55` pairs — assembled from the four proved window
  enumerations (`datum_low/mid/upper/top_window_pairs`), no fresh enumeration sweep.
* **The generic refutation/count kit**: `canonGap_ne_three_of_band`,
  `not_class3CycleBand3Free_of_orbit_band3` (a single band-3 orbit reading defeats EVERY
  cycle check), `densePackHalfDensity_rounding` (`2b ≤ c` collapses the cycle-density
  count to the half-width form `⌊(K−1)/2⌋ + 2b`), the per-datum counts
  (`densePackStarts_card_le_of_period_count`,
  `densePackStarts_card_le_half_width_of_period_count`), and the per-datum K.1.2
  Nat-cover threshold (`densePackCoverNat_of_period_count`).
* **The gated residual is packaged as the ≤ `r+1 ≤ 2` hit-gap floor inequalities**
  (`densePackStarts_empty_of_gate_floor_refuted`,
  `densePackStarts_empty_of_gate_band3_floor_refuted`): on gated shells, refuting the
  gap floor at the top-band starts (at the band-3 orbit residues only) empties the set —
  the quantified form of the per-shell finite check that remains.
* **The modulus `q = 15` is closed and the `(21, 1)` datum is closed** (NEW cycle
  certificates): all three `q = 15` data `(15,1)`, `(15,2)`, `(15,7)` and the `(21,1)`
  datum are band-3-free (`class3CycleBand3Free_of_datum_15_1/15_2/15_7/21_1`, periods
  `1/1/3/2`, cycles `1` / `1` / `13 → 11 → 7` / `11 → 1`); modulus closure
  `class3CycleBand3Free_of_modulus_fifteen` / `densePackStarts_empty_of_modulus_fifteen`
  via the divisor pin (`band3_datum_K₀_of_modulus_fifteen`); aggregate
  `DensePackDatumClosed` (`q = 15 ∨ (q, K₀) = (21, 1)`) with
  `class3CycleBand3Free_of_datumClosed` / `densePackStarts_empty_of_datumClosed`.
* **Three more band-3 data are certified as genuine cycle-check defeats**: `(5,2)`
  (cycle `3 → 1`, band 3 at index `2`), `(13,6)` (cycle `11 → 9 → 5 → 7 → 1 → 3`, band 3
  at index `6`), `(21,10)` (cycle `19 → 17 → 13 → 5`, band 3 at index `4`) —
  `not_class3CycleBand3Free_of_datum_5_2/13_6/21_10`; together with the wave-4 `(21,3)`
  defeat (`not_class3CycleBand3Free_of_datum`) this settles every enumerated pair with
  `q ∈ {5, 13, 15, 21}`.
* **The successor residual** `DensePackGatedClosureResidual`: the wave-4 fields, each
  ADDITIONALLY guarded by `¬ DensePackDatumClosed ctx` — providers owe NOTHING on the
  closed data any more.  Bridges: `DensePackGatedClosureResidual.toDatumSplit` (lands
  exactly in the wave-4 capstone field type), `DensePackDatumSplitResidual.toGatedClosure`
  (converse weakening), `nonempty_gatedClosure_iff_datumSplit` (equivalent surfaces),
  `erdos260_of_gatedClosure` (the drop-in final endpoint).

## The honest residual after this module

(a) The remaining `47` enumerated pairs' cycles are not yet machine-tabulated here (only
`q ∈ {5, 13, 15, 21}` is settled: `4` pairs closed, `4` certified band-3); extending
`DensePackDatumClosed` pair by pair through the Part-2 certificate format is the
mechanical continuation.  (b) On the surviving band-3 data — notably the `(21, 3)` fixed
family (NOT refuted here; its Q-parity voiding is out of scope for this module) — the
untabulated pairs, and all un-enumerated `q ≥ 64`: gated shells owe the `≤ r + 1 ≤ 2`
per-shell gap-floor refutations; ungated shells owe the K.1.1 endpoint density, the K.1
interior, and the corrected K.1.2 Nat cover — with the per-pair thresholds and the
half-width counts available against them.  No context is proved empty on the surviving
band-3 data; nothing is claimed beyond the proved cycle facts.

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 0.  Generic helpers: band-3 refutation, per-datum counts, rounding

(The collision-to-period lemma `slopeOrbit_collision_period` is already provided by
`TowerFixedPointClosure` — hypothesis-free beyond the collision itself — and is reused
as-is below.) -/

/-- A numerator outside the band-3 window `(q/8, q/4]` has `canonGap ≠ 3` (the band-3
mirror of `canonGap_ne_four_of_band`). -/
theorem canonGap_ne_three_of_band {q K : ℕ} (h : q < 4 * K ∨ 8 * K ≤ q) :
    canonGap q K ≠ 3 := by
  intro h3
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · unfold canonGap at h3
    rw [Nat.div_zero, Nat.log_zero_right] at h3
    omega
  · obtain ⟨h4, h8⟩ := (canonGap_eq_three_iff hK).mp h3
    omega

/-- **A single band-3 orbit reading defeats EVERY cycle check** (mod-period reduction):
if `canonGap q K_{j₀} = 3` at some `j₀ ≥ 1`, no period of the actual orbit can be
band-3-free. -/
theorem not_class3CycleBand3Free_of_orbit_band3 (ctx : ActualFailureContext) {j₀ : ℕ}
    (hj₀ : 1 ≤ j₀)
    (hband : canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j₀) = 3) :
    ¬ Class3CycleBand3Free ctx := by
  rintro ⟨c, hc, hper, hfree⟩
  have hmod := Nat.mod_lt (j₀ - 1) (show 0 < c by omega)
  apply hfree (1 + (j₀ - 1) % c) (by omega) (by omega)
  rw [← slopeOrbit_eq_mod_period hc hper hj₀]
  exact hband

/-- **The half-density rounding** (the class-3 mirror of `towerHalfDensity_rounding`):
`2b ≤ c` turns the cycle-density count `b·(⌊(K−1)/c⌋ + 2)` into the half-width form
`⌊(K−1)/2⌋ + 2b`. -/
theorem densePackHalfDensity_rounding {b c K : ℕ} (hhalf : 2 * b ≤ c) :
    b * ((K - 1) / c + 2) ≤ (K - 1) / 2 + 2 * b := by
  have hD : b * ((K - 1) / c) ≤ (K - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    calc b * ((K - 1) / c) * 2 = (K - 1) / c * (2 * b) := by ring
      _ ≤ (K - 1) / c * c := Nat.mul_le_mul_left _ hhalf
      _ ≤ K - 1 := Nat.div_mul_le_self _ _
  have hexp : b * ((K - 1) / c + 2) = b * ((K - 1) / c) + 2 * b := by ring
  omega

/-- **The per-datum cycle-density count**: a period `c` and a residue-count bound
`b₃ ≤ b` give `|starts₃| ≤ b·(⌊(K−1)/c⌋ + 2)`. -/
theorem densePackStarts_card_le_of_period_count (ctx : ActualFailureContext) {c b : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hcount : (cycleBand3Residues ctx c).card ≤ b) :
    (genuineDensePackStarts ctx).card
      ≤ b * (((supportShell ctx.shell.d ctx.shell.X).card - 1) / c + 2) :=
  le_trans (densePackStarts_card_le_cycle_density ctx hc hper)
    (Nat.mul_le_mul_right _ hcount)

/-- **The half-width count**: with the half-density check `2b ≤ c` the per-datum count
collapses to `⌊(K−1)/2⌋ + 2b` — the generalized `q = 5` halving. -/
theorem densePackStarts_card_le_half_width_of_period_count (ctx : ActualFailureContext)
    {c b : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hcount : (cycleBand3Residues ctx c).card ≤ b) (hhalf : 2 * b ≤ c) :
    (genuineDensePackStarts ctx).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card - 1) / 2 + 2 * b :=
  le_trans (densePackStarts_card_le_of_period_count ctx hc hper hcount)
    (densePackHalfDensity_rounding hhalf)

/-- **The per-datum K.1.2 Nat-cover threshold**: a period `c`, a residue-count bound `b`,
and the numeric check `b·(⌊(K−1)/c⌋+2)·mult ≤ markers` discharge the capstone's exact
`ℕ` cover field (through `densePackCoverNat_of_cycle_density`). -/
theorem densePackCoverNat_of_period_count (ctx : ActualFailureContext) {c b : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hcount : (cycleBand3Residues ctx c).card ≤ b)
    (h : b * (((supportShell ctx.shell.d ctx.shell.X).card - 1) / c + 2)
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card) :
    (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  densePackCoverNat_of_cycle_density ctx hc hper
    (le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcount)) h)

/-- **Gated emptiness from PURE gap-floor refutations** at the ≤ `r + 1 ≤ 2` top-band
starts: the band conjunct of `densePackStarts_empty_iff_topBand_of_gate` is dropped —
refuting the hit-gap floor alone suffices. -/
theorem densePackStarts_empty_of_gate_floor_refuted (ctx : ActualFailureContext)
    (hg : class3Gate ctx)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card ≤ k + ctx.n24CarryData.r + 1 →
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r)) :
    genuineDensePackStarts ctx = ∅ :=
  (densePackStarts_empty_iff_topBand_of_gate ctx hg).mpr
    (fun k hk htop hpins => h k hk htop hpins.1)

/-- **Gated emptiness from band-3-refined gap-floor refutations**: the floor needs
refuting ONLY at top-band starts whose orbit residue actually reads band 3 — on the
surviving pairs these residues are the computed per-pair sets. -/
theorem densePackStarts_empty_of_gate_band3_floor_refuted (ctx : ActualFailureContext)
    (hg : class3Gate ctx)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card ≤ k + ctx.n24CarryData.r + 1 →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 3 →
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r)) :
    genuineDensePackStarts ctx = ∅ :=
  (densePackStarts_empty_iff_topBand_of_gate ctx hg).mpr
    (fun k hk htop hpins => h k hk htop hpins.2 hpins.1)

/-! ## Part 1.  The divisor-pin datum enumeration on the surviving window

`(2K₀+1) ∣ q` with `K₀ ≥ 1`, `q` odd, `q < 64` and `q = 5 ∨ 13 ≤ q`: exactly `55`
pairs.  The proof assembles the four proved window enumerations
(`datum_low_window_pairs`, `datum_mid_window_pairs`, `datum_upper_window_pairs`,
`datum_top_window_pairs`) and filters the low window through the surviving-modulus
hypothesis. -/

set_option maxHeartbeats 4000000 in
/-- **The band-3 window datum enumeration**: the divisor pin confines `(q, K₀)` to the
55 explicit pairs (the `q ∈ {5, 13, 15, 21}` cycle statuses are certified in Part 2). -/
theorem band3_datum_enum {q K₀ : ℕ} (hodd : Odd q) (hK1 : 1 ≤ K₀)
    (hdvd : 2 * K₀ + 1 ∣ q) (hq64 : q < 64) (hwin : q = 5 ∨ 13 ≤ q) :
    (q = 5 ∧ K₀ = 2) ∨ (q = 13 ∧ K₀ = 6)
      ∨ (q = 15 ∧ K₀ = 1) ∨ (q = 15 ∧ K₀ = 2) ∨ (q = 15 ∧ K₀ = 7)
      ∨ (q = 17 ∧ K₀ = 8) ∨ (q = 19 ∧ K₀ = 9)
      ∨ (q = 21 ∧ K₀ = 1) ∨ (q = 21 ∧ K₀ = 3) ∨ (q = 21 ∧ K₀ = 10)
      ∨ (q = 23 ∧ K₀ = 11) ∨ (q = 25 ∧ K₀ = 2) ∨ (q = 25 ∧ K₀ = 12)
      ∨ (q = 27 ∧ K₀ = 1) ∨ (q = 27 ∧ K₀ = 4) ∨ (q = 27 ∧ K₀ = 13)
      ∨ (q = 29 ∧ K₀ = 14) ∨ (q = 31 ∧ K₀ = 15)
      ∨ (q = 33 ∧ K₀ = 1) ∨ (q = 33 ∧ K₀ = 5) ∨ (q = 33 ∧ K₀ = 16)
      ∨ (q = 35 ∧ K₀ = 2) ∨ (q = 35 ∧ K₀ = 3) ∨ (q = 35 ∧ K₀ = 17)
      ∨ (q = 37 ∧ K₀ = 18)
      ∨ (q = 39 ∧ K₀ = 1) ∨ (q = 39 ∧ K₀ = 6) ∨ (q = 39 ∧ K₀ = 19)
      ∨ (q = 41 ∧ K₀ = 20) ∨ (q = 43 ∧ K₀ = 21)
      ∨ (q = 45 ∧ K₀ = 1) ∨ (q = 45 ∧ K₀ = 2) ∨ (q = 45 ∧ K₀ = 4)
      ∨ (q = 45 ∧ K₀ = 7) ∨ (q = 45 ∧ K₀ = 22)
      ∨ (q = 47 ∧ K₀ = 23) ∨ (q = 49 ∧ K₀ = 3) ∨ (q = 49 ∧ K₀ = 24)
      ∨ (q = 51 ∧ K₀ = 1) ∨ (q = 51 ∧ K₀ = 8) ∨ (q = 51 ∧ K₀ = 25)
      ∨ (q = 53 ∧ K₀ = 26)
      ∨ (q = 55 ∧ K₀ = 2) ∨ (q = 55 ∧ K₀ = 5) ∨ (q = 55 ∧ K₀ = 27)
      ∨ (q = 57 ∧ K₀ = 1) ∨ (q = 57 ∧ K₀ = 9) ∨ (q = 57 ∧ K₀ = 28)
      ∨ (q = 59 ∧ K₀ = 29) ∨ (q = 61 ∧ K₀ = 30)
      ∨ (q = 63 ∧ K₀ = 1) ∨ (q = 63 ∧ K₀ = 3) ∨ (q = 63 ∧ K₀ = 4)
      ∨ (q = 63 ∧ K₀ = 10) ∨ (q = 63 ∧ K₀ = 31) := by
  obtain ⟨t, ht⟩ := hodd
  have hq0 : 0 < q := by omega
  have hle : 2 * K₀ + 1 ≤ q := Nat.le_of_dvd hq0 hdvd
  have h2K : 2 * K₀ < q := by omega
  rcases Nat.lt_or_ge q 16 with h16 | h16
  · have h := datum_low_window_pairs ⟨t, ht⟩ hK1 h2K hdvd (by omega) h16
    rcases h with h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl, rfl⟩ := h <;> first | (norm_num; done) | exact absurd hwin (by norm_num)
  · rcases Nat.lt_or_ge q 32 with h32 | h32
    · have h := datum_mid_window_pairs ⟨t, ht⟩ hK1 h2K hdvd (by omega) h32
      rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl, rfl⟩ := h <;> norm_num
    · rcases Nat.lt_or_ge q 48 with h48 | h48
      · have h := datum_upper_window_pairs ⟨t, ht⟩ hK1 h2K hdvd h32 h48
        rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl, rfl⟩ := h <;> norm_num
      · have h := datum_top_window_pairs ⟨t, ht⟩ hK1 h2K hdvd h48 hq64
        rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl, rfl⟩ := h <;> norm_num

/-! ## Part 2.  Cycle certificates: `q = 15` closed, `(21, 1)` closed, and the band-3
defeats at `(5, 2)`, `(13, 6)`, `(21, 10)`

Each cycle is verified step by step through the band bounds (`slopeOrbit_step_eval` —
no `Nat.log` evaluation anywhere); the period is the first return to the index-`1`
value, promoted by `slopeOrbit_collision_period`; band-3-freeness is read off by
`canonGap_ne_three_of_band`, band-3 hits by `canonGap_eval`. -/

/-- `(15, 1)`: period `1`, cycle `1` (gap `4`) — band-3-free. -/
private theorem densePackCycle_15_1 :
    slopeOrbit 15 1 (1 + 1) = slopeOrbit 15 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → canonGap 15 (slopeOrbit 15 1 j) ≠ 3 := by
  have e0 : slopeOrbit 15 1 0 = 1 := rfl
  have e1 : slopeOrbit 15 1 1 = 1 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 15 1 2 = 1 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 15 1 2 = slopeOrbit 15 1 1
    rw [e2, e1]
  · intro j hj1 hjc
    interval_cases j
    rw [e1]
    exact canonGap_ne_three_of_band (Or.inr (by norm_num))

/-- `(15, 2)`: period `1` from index `1`, cycle `1` — band-3-free. -/
private theorem densePackCycle_15_2 :
    slopeOrbit 15 2 (1 + 1) = slopeOrbit 15 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → canonGap 15 (slopeOrbit 15 2 j) ≠ 3 := by
  have e0 : slopeOrbit 15 2 0 = 2 := rfl
  have e1 : slopeOrbit 15 2 1 = 1 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 15 2 2 = 1 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 15 2 2 = slopeOrbit 15 2 1
    rw [e2, e1]
  · intro j hj1 hjc
    interval_cases j
    rw [e1]
    exact canonGap_ne_three_of_band (Or.inr (by norm_num))

/-- `(15, 7)`: period `3`, cycle `13 → 11 → 7` — band-3-free. -/
private theorem densePackCycle_15_7 :
    slopeOrbit 15 7 (1 + 3) = slopeOrbit 15 7 1
      ∧ ∀ j, 1 ≤ j → j ≤ 3 → canonGap 15 (slopeOrbit 15 7 j) ≠ 3 := by
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
  · intro j hj1 hjc
    interval_cases j
    · rw [e1]
      exact canonGap_ne_three_of_band (Or.inl (by norm_num))
    · rw [e2]
      exact canonGap_ne_three_of_band (Or.inl (by norm_num))
    · rw [e3]
      exact canonGap_ne_three_of_band (Or.inl (by norm_num))

/-- `(21, 1)`: period `2`, cycle `11 → 1` — band-3-free. -/
private theorem densePackCycle_21_1 :
    slopeOrbit 21 1 (1 + 2) = slopeOrbit 21 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → canonGap 21 (slopeOrbit 21 1 j) ≠ 3 := by
  have e0 : slopeOrbit 21 1 0 = 1 := rfl
  have e1 : slopeOrbit 21 1 1 = 11 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 21 1 2 = 1 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 21 1 3 = 11 :=
    slopeOrbit_step_eval 2 4 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 21 1 3 = slopeOrbit 21 1 1
    rw [e3, e1]
  · intro j hj1 hjc
    interval_cases j
    · rw [e1]
      exact canonGap_ne_three_of_band (Or.inl (by norm_num))
    · rw [e2]
      exact canonGap_ne_three_of_band (Or.inr (by norm_num))

/-- The `(15, 1)` datum satisfies the band-3 cycle check on every actual shell. -/
theorem class3CycleBand3Free_of_datum_15_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    Class3CycleBand3Free ctx := by
  refine ⟨1, le_rfl, ?_, ?_⟩
  · intro m hm
    rw [hq, hK]
    exact slopeOrbit_collision_period densePackCycle_15_1.1 m hm
  · intro j hj1 hjc
    rw [hq, hK]
    exact densePackCycle_15_1.2 j hj1 hjc

/-- The `(15, 2)` datum satisfies the band-3 cycle check on every actual shell. -/
theorem class3CycleBand3Free_of_datum_15_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    Class3CycleBand3Free ctx := by
  refine ⟨1, le_rfl, ?_, ?_⟩
  · intro m hm
    rw [hq, hK]
    exact slopeOrbit_collision_period densePackCycle_15_2.1 m hm
  · intro j hj1 hjc
    rw [hq, hK]
    exact densePackCycle_15_2.2 j hj1 hjc

/-- The `(15, 7)` datum satisfies the band-3 cycle check on every actual shell. -/
theorem class3CycleBand3Free_of_datum_15_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 7) :
    Class3CycleBand3Free ctx := by
  refine ⟨3, by norm_num, ?_, ?_⟩
  · intro m hm
    rw [hq, hK]
    exact slopeOrbit_collision_period densePackCycle_15_7.1 m hm
  · intro j hj1 hjc
    rw [hq, hK]
    exact densePackCycle_15_7.2 j hj1 hjc

/-- The `(21, 1)` datum satisfies the band-3 cycle check on every actual shell. -/
theorem class3CycleBand3Free_of_datum_21_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    Class3CycleBand3Free ctx := by
  refine ⟨2, by norm_num, ?_, ?_⟩
  · intro m hm
    rw [hq, hK]
    exact slopeOrbit_collision_period densePackCycle_21_1.1 m hm
  · intro j hj1 hjc
    rw [hq, hK]
    exact densePackCycle_21_1.2 j hj1 hjc

/-- The divisor pin at `q = 15`: the admissible base numerators are exactly `{1, 2, 7}`. -/
theorem band3_datum_K₀_of_dvd_fifteen {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 15) :
    K = 1 ∨ K = 2 ∨ K = 7 := by
  have hle : 2 * K + 1 ≤ 15 := Nat.le_of_dvd (by norm_num) hdvd
  have hK7 : K ≤ 7 := by omega
  obtain ⟨s, hs⟩ := hdvd
  interval_cases K <;> omega

/-- The divisor pin at every actual `q = 15` shell: `K₀ ∈ {1, 2, 7}`. -/
theorem band3_datum_K₀_of_modulus_fifteen (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) :
    (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 2
      ∨ (class1SlopeDatum ctx).K₀ = 7 := by
  have hd := class0_datum_dvd ctx
  rw [hq] at hd
  exact band3_datum_K₀_of_dvd_fifteen (class1SlopeDatum ctx).hK₀_pos hd

/-- **NEW closed cycle family `q = 15`**: all three pinned data are band-3-free, so the
band-3 cycle check holds on EVERY actual `q = 15` shell. -/
theorem class3CycleBand3Free_of_modulus_fifteen (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) : Class3CycleBand3Free ctx := by
  rcases band3_datum_K₀_of_modulus_fifteen ctx hq with hK | hK | hK
  · exact class3CycleBand3Free_of_datum_15_1 ctx hq hK
  · exact class3CycleBand3Free_of_datum_15_2 ctx hq hK
  · exact class3CycleBand3Free_of_datum_15_7 ctx hq hK

/-- **NEW modulus closure `q = 15`**: the dense start set is PROVABLY EMPTY on every
actual shell with `q = 15`. -/
theorem densePackStarts_empty_of_modulus_fifteen (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) :
    genuineDensePackStarts ctx = ∅ :=
  densePackStarts_empty_of_cycleBand3Free ctx
    (class3CycleBand3Free_of_modulus_fifteen ctx hq)

/-- `(5, 2)`: the orbit reads `3 → 1` — the index-`2` value. -/
private theorem densePackOrbit_5_2 : slopeOrbit 5 2 2 = 1 := by
  have e0 : slopeOrbit 5 2 0 = 2 := rfl
  have e1 : slopeOrbit 5 2 1 = 3 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- At the `(5, 2)` datum every period fails the band-3 cycle check (the cycle `3 → 1`
reads band 3 at index `2`, `canonGap 5 1 = 3`). -/
theorem not_class3CycleBand3Free_of_datum_5_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 5) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    ¬ Class3CycleBand3Free ctx := by
  apply not_class3CycleBand3Free_of_orbit_band3 ctx (j₀ := 2) (by norm_num)
  rw [hq, hK, densePackOrbit_5_2]
  exact canonGap_eval (by norm_num) (by norm_num) (by norm_num)

/-- `(13, 6)`: the orbit reads `11 → 9 → 5 → 7 → 1 → 3` — the index-`6` value. -/
private theorem densePackOrbit_13_6 : slopeOrbit 13 6 6 = 3 := by
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
  exact slopeOrbit_step_eval 5 3 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- At the `(13, 6)` datum every period fails the band-3 cycle check (the cycle
`11 → 9 → 5 → 7 → 1 → 3` reads band 3 at index `6`, `canonGap 13 3 = 3`). -/
theorem not_class3CycleBand3Free_of_datum_13_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 13) (hK : (class1SlopeDatum ctx).K₀ = 6) :
    ¬ Class3CycleBand3Free ctx := by
  apply not_class3CycleBand3Free_of_orbit_band3 ctx (j₀ := 6) (by norm_num)
  rw [hq, hK, densePackOrbit_13_6]
  exact canonGap_eval (by norm_num) (by norm_num) (by norm_num)

/-- `(21, 10)`: the orbit reads `19 → 17 → 13 → 5` — the index-`4` value. -/
private theorem densePackOrbit_21_10 : slopeOrbit 21 10 4 = 5 := by
  have e0 : slopeOrbit 21 10 0 = 10 := rfl
  have e1 : slopeOrbit 21 10 1 = 19 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 21 10 2 = 17 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 21 10 3 = 13 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- At the `(21, 10)` datum every period fails the band-3 cycle check (the cycle
`19 → 17 → 13 → 5` reads band 3 at index `4`, `canonGap 21 5 = 3`); together with the
wave-4 `(21, 3)` defeat and the `(21, 1)` closure this settles the `q = 21` data. -/
theorem not_class3CycleBand3Free_of_datum_21_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    ¬ Class3CycleBand3Free ctx := by
  apply not_class3CycleBand3Free_of_orbit_band3 ctx (j₀ := 4) (by norm_num)
  rw [hq, hK, densePackOrbit_21_10]
  exact canonGap_eval (by norm_num) (by norm_num) (by norm_num)

/-! ## Part 3.  The closed-datum aggregate -/

/-- **The closed-datum aggregate**: the data whose band-3 cycle check is PROVED here —
the whole modulus `q = 15` (all three pinned data) and the `(21, 1)` datum. -/
def DensePackDatumClosed (ctx : ActualFailureContext) : Prop :=
  (class1SlopeDatum ctx).q = 15
    ∨ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 1)

/-- On every closed datum the band-3 cycle check holds. -/
theorem class3CycleBand3Free_of_datumClosed (ctx : ActualFailureContext)
    (h : DensePackDatumClosed ctx) : Class3CycleBand3Free ctx := by
  rcases h with hq | ⟨hq, hK⟩
  · exact class3CycleBand3Free_of_modulus_fifteen ctx hq
  · exact class3CycleBand3Free_of_datum_21_1 ctx hq hK

/-- On every closed datum the dense start set is PROVABLY EMPTY. -/
theorem densePackStarts_empty_of_datumClosed (ctx : ActualFailureContext)
    (h : DensePackDatumClosed ctx) :
    genuineDensePackStarts ctx = ∅ :=
  densePackStarts_empty_of_cycleBand3Free ctx
    (class3CycleBand3Free_of_datumClosed ctx h)

/-! ## Part 4.  The gated-closure residual surface and the bridges -/

/-- **The wave-5 residual**: the four wave-4 datum-split fields, each ADDITIONALLY
guarded by `¬ DensePackDatumClosed ctx` — providers owe NOTHING on the proved-closed
data (`q = 15`, `(21, 1)`) any more. -/
structure DensePackGatedClosureResidual where
  /-- Gated surviving-window shells with an unclosed datum whose top-band cycle residues
  meet band 3: the dense start set is empty — equivalently the `≤ r + 1 ≤ 2` top-band
  gap-floor refutations. -/
  gatedEmpty : ∀ ctx : ActualFailureContext, class3Gate ctx →
    ¬ Class3TopBandCycleFree ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    genuineDensePackStarts ctx = ∅
  /-- Ungated surviving-window shells with an unclosed datum whose cycle meets band 3:
  the K.1.1 coarea hit-density at the descent endpoints. -/
  ungatedDensity : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    densePackEndpointDensity ctx
  /-- Ungated surviving-window shells with an unclosed datum whose top-band cycle
  residues meet band 3: the K.1 active-window interior containment. -/
  ungatedInterior : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
    ¬ Class3TopBandCycleFree ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card
  /-- Ungated surviving-window shells with an unclosed datum whose cycle meets band 3:
  the corrected K.1.2 cover in exact `ℕ` form (dischargeable from the per-datum
  threshold `densePackCoverNat_of_period_count`). -/
  ungatedCoverNat : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card

/-- **The lossless bridge into the EXACT wave-4 capstone field type**: on the closed
data every field is discharged by the proved cycle certificates (`gatedEmpty` directly
by the proved emptiness; the other three by contradicting their cycle-check guards
through `class3CycleBand3Free_of_datumClosed`). -/
def DensePackGatedClosureResidual.toDatumSplit (R : DensePackGatedClosureResidual) :
    DensePackDatumSplitResidual where
  gatedEmpty := fun ctx hg hfree hwin => by
    by_cases hcl : DensePackDatumClosed ctx
    · exact densePackStarts_empty_of_datumClosed ctx hcl
    · exact R.gatedEmpty ctx hg hfree hwin hcl
  ungatedDensity := fun ctx hg hfree hwin => by
    by_cases hcl : DensePackDatumClosed ctx
    · exact absurd (class3CycleBand3Free_of_datumClosed ctx hcl) hfree
    · exact R.ungatedDensity ctx hg hfree hwin hcl
  ungatedInterior := fun ctx hg hfree hwin => by
    by_cases hcl : DensePackDatumClosed ctx
    · exact absurd (class3TopBandCycleFree_of_cycleBand3Free ctx
        (class3CycleBand3Free_of_datumClosed ctx hcl)) hfree
    · exact R.ungatedInterior ctx hg hfree hwin hcl
  ungatedCoverNat := fun ctx hg hfree hwin => by
    by_cases hcl : DensePackDatumClosed ctx
    · exact absurd (class3CycleBand3Free_of_datumClosed ctx hcl) hfree
    · exact R.ungatedCoverNat ctx hg hfree hwin hcl

/-- Direct gated-shell emptiness projection from the gated-closure surface. -/
theorem DensePackGatedClosureResidual.densePackStarts_empty_of_gate
    (R : DensePackGatedClosureResidual)
    (ctx : ActualFailureContext) (hg : class3Gate ctx) :
    genuineDensePackStarts ctx = ∅ := by
  by_cases hfree : Class3TopBandCycleFree ctx
  · exact densePackStarts_empty_of_gate_topBandCycleFree ctx hg hfree
  · by_cases hwin : (class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q
    · by_cases hcl : DensePackDatumClosed ctx
      · exact densePackStarts_empty_of_datumClosed ctx hcl
      · exact R.gatedEmpty ctx hg hfree hwin hcl
    · exact absurd (class3TopBandCycleFree_of_cycleBand3Free ctx
        (class3CycleBand3Free_of_modulus_complement ctx hwin)) hfree

/-- Direct `r = 0` emptiness projection from the gated-closure surface. -/
theorem DensePackGatedClosureResidual.densePackStarts_empty_of_r_eq_zero
    (R : DensePackGatedClosureResidual)
    (ctx : ActualFailureContext) (hr : ctx.n24CarryData.r = 0) :
    genuineDensePackStarts ctx = ∅ :=
  R.densePackStarts_empty_of_gate ctx (class3Gate_of_r_eq_zero ctx hr)

/-- Direct shallow-depth emptiness projection from the gated-closure surface. -/
theorem DensePackGatedClosureResidual.densePackStarts_empty_of_L_le
    (R : DensePackGatedClosureResidual)
    (ctx : ActualFailureContext) (hL : shellLadderDepth ctx ≤ 15420) :
    genuineDensePackStarts ctx = ∅ :=
  R.densePackStarts_empty_of_gate ctx (class3Gate_of_L_le ctx hL)

/-- Direct class-3 ledger bridge from the gated-closure surface, at any budget. -/
theorem DensePackGatedClosureResidual.hDensePackField
    (R : DensePackGatedClosureResidual)
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hroute : ∀ ctx : ActualFailureContext, (budget ctx).route = genuineChargeRoute ctx) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 3
        ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  (((R.toDatumSplit).toCycleSplit).toRegimeSplit budget).toCorrected.hDensePackField hroute

/-- **The converse weakening**: any wave-4 datum-split provider restricts to the wave-5
surface — the new presentation hides no strength. -/
def DensePackDatumSplitResidual.toGatedClosure (R : DensePackDatumSplitResidual) :
    DensePackGatedClosureResidual where
  gatedEmpty := fun ctx hg hfree hwin _ => R.gatedEmpty ctx hg hfree hwin
  ungatedDensity := fun ctx hg hfree hwin _ => R.ungatedDensity ctx hg hfree hwin
  ungatedInterior := fun ctx hg hfree hwin _ => R.ungatedInterior ctx hg hfree hwin
  ungatedCoverNat := fun ctx hg hfree hwin _ => R.ungatedCoverNat ctx hg hfree hwin

/-- **The two surfaces are EQUIVALENT** — the wave-5 residual is exactly the wave-4 one
with the proved datum closures (`q = 15`, `(21, 1)`) folded in. -/
theorem nonempty_gatedClosure_iff_datumSplit :
    Nonempty DensePackGatedClosureResidual ↔ Nonempty DensePackDatumSplitResidual :=
  ⟨fun ⟨R⟩ => ⟨R.toDatumSplit⟩, fun ⟨S⟩ => ⟨S.toGatedClosure⟩⟩

/-- **The final endpoint with the class-3 slot at the wave-5 gated-closure surface**:
`Erdos260Statement` from the six other sharp fields plus the datum-guarded residual,
through the wave-4 drop-in `erdos260_of_datumSplit`. -/
theorem erdos260_of_gatedClosure
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
    (gated : DensePackGatedClosureResidual) :
    Erdos260Statement :=
  erdos260_of_datumSplit towerCount runSplit returnSmall returnDigit class0Pinned
    class1Pinned gated.toDatumSplit

/-! ## Part 5.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the wave-5 class-3 gated closure. -/
def densePackGatedClosureStatus : List String :=
  [ "CLOSED (the band-3 window datum enumeration, NEW): band3_datum_enum - on the " ++
      "wave-4 surviving window (q = 5 or 13 <= q) with odd q < 64, the divisor pin " ++
      "(2K0+1) | q (class0_datum_dvd from class1SlopeDatum_H_dvd + " ++
      "class1SlopeDatum_K0_eq) admits EXACTLY 55 pairs; assembled from the four " ++
      "proved window enumerations datum_low/mid/upper/top_window_pairs.",
    "CLOSED (generic refutation/count kit, NEW): canonGap_ne_three_of_band (band 3 " ++
      "needs 4K <= q < 8K), not_class3CycleBand3Free_of_orbit_band3 (ONE band-3 " ++
      "orbit reading defeats EVERY cycle check, via slopeOrbit_eq_mod_period), " ++
      "densePackHalfDensity_rounding (2b <= c collapses the cycle-density count to " ++
      "floor((K-1)/2) + 2b), densePackStarts_card_le_of_period_count / " ++
      "densePackStarts_card_le_half_width_of_period_count (per-datum counts), " ++
      "densePackCoverNat_of_period_count (per-datum K.1.2 Nat-cover threshold).",
    "CLOSED (gated floor-refutation closers, NEW): " ++
      "densePackStarts_empty_of_gate_floor_refuted / " ++
      "densePackStarts_empty_of_gate_band3_floor_refuted - on gated shells, refuting " ++
      "the <= r+1 <= 2 top-band hit-gap floors (at the band-3 orbit residues only, " ++
      "in the refined form) EMPTIES the dense start set.",
    "CLOSED (NEW modulus q = 15 and datum (21,1), unconditional, every shell/every " ++
      "r): all three q = 15 data (15,1),(15,2),(15,7) and the (21,1) datum are " ++
      "band-3-free - class3CycleBand3Free_of_datum_15_1/15_2/15_7/21_1, periods " ++
      "1/1/3/2, cycles 1 / 1 / 13->11->7 / 11->1, verified by slopeOrbit_step_eval " ++
      "band bounds (no Nat.log evaluation); divisor pin " ++
      "band3_datum_K0_of_modulus_fifteen confines q = 15 to K0 in {1,2,7}; modulus " ++
      "closure class3CycleBand3Free_of_modulus_fifteen + " ++
      "densePackStarts_empty_of_modulus_fifteen; aggregate DensePackDatumClosed " ++
      "(q = 15 or (q,K0) = (21,1)) with class3CycleBand3Free_of_datumClosed / " ++
      "densePackStarts_empty_of_datumClosed.",
    "DECIDED (band-3 data certified as genuine cycle-check defeats, NEW): (5,2) " ++
      "cycle 3->1 reads band 3 at index 2; (13,6) cycle 11->9->5->7->1->3 reads " ++
      "band 3 at index 6; (21,10) cycle 19->17->13->5 reads band 3 at index 4 - " ++
      "not_class3CycleBand3Free_of_datum_5_2/13_6/21_10 via " ++
      "not_class3CycleBand3Free_of_orbit_band3; the (21,3) defeat is the wave-4 " ++
      "not_class3CycleBand3Free_of_datum. Every enumerated pair with q in " ++
      "{5,13,15,21} is now settled; q = 21 is narrowed to (21,3) and (21,10).",
    "PACKAGED (the successor residual, NEW): DensePackGatedClosureResidual - the " ++
      "four wave-4 datum-split fields, each ADDITIONALLY guarded by " ++
      "not DensePackDatumClosed (providers owe NOTHING on q = 15 or (21,1) any " ++
      "more). Bridges: DensePackGatedClosureResidual.toDatumSplit (lands EXACTLY in " ++
      "the wave-4 capstone field type, via the proved closures), " ++
      "DensePackDatumSplitResidual.toGatedClosure (converse weakening), " ++
      "nonempty_gatedClosure_iff_datumSplit (EQUIVALENT surfaces). Endpoint: " ++
      "erdos260_of_gatedClosure (the drop-in final assembly through " ++
      "erdos260_of_datumSplit).",
    "RESIDUAL (honest, what remains open): (a) the remaining 47 enumerated pairs' " ++
      "cycles are not yet machine-tabulated here (only q in {5,13,15,21} is " ++
      "settled: 4 pairs closed, 4 certified band-3); extending DensePackDatumClosed " ++
      "pair by pair through the Part-2 certificate format is the mechanical " ++
      "continuation. (b) On the surviving band-3 data ((5,2),(13,6),(21,3),(21,10) " ++
      "and the untabulated pairs) and all q >= 64: gated shells owe the " ++
      "<= r+1 <= 2 per-shell gap-floor refutations (the floor lives on the " ++
      "model-unconstrained escape gap); ungated shells owe the K.1.1 endpoint " ++
      "density, the K.1 interior, and the corrected K.1.2 Nat cover (per-datum " ++
      "thresholds and half-width counts available against them). No context is " ++
      "proved empty on the surviving band-3 data; nothing is claimed beyond the " ++
      "proved cycle facts." ]

theorem densePackGatedClosureStatus_nonempty :
    densePackGatedClosureStatus ≠ [] := by
  simp [densePackGatedClosureStatus]

/-! ## Part 6.  Axiom-cleanliness audit -/

#print axioms canonGap_ne_three_of_band
#print axioms not_class3CycleBand3Free_of_orbit_band3
#print axioms densePackHalfDensity_rounding
#print axioms densePackStarts_card_le_of_period_count
#print axioms densePackStarts_card_le_half_width_of_period_count
#print axioms densePackCoverNat_of_period_count
#print axioms densePackStarts_empty_of_gate_floor_refuted
#print axioms densePackStarts_empty_of_gate_band3_floor_refuted
#print axioms band3_datum_enum
#print axioms class3CycleBand3Free_of_datum_15_1
#print axioms class3CycleBand3Free_of_datum_15_2
#print axioms class3CycleBand3Free_of_datum_15_7
#print axioms class3CycleBand3Free_of_datum_21_1
#print axioms band3_datum_K₀_of_dvd_fifteen
#print axioms band3_datum_K₀_of_modulus_fifteen
#print axioms class3CycleBand3Free_of_modulus_fifteen
#print axioms densePackStarts_empty_of_modulus_fifteen
#print axioms not_class3CycleBand3Free_of_datum_5_2
#print axioms not_class3CycleBand3Free_of_datum_13_6
#print axioms not_class3CycleBand3Free_of_datum_21_10
#print axioms class3CycleBand3Free_of_datumClosed
#print axioms densePackStarts_empty_of_datumClosed
#print axioms DensePackGatedClosureResidual.toDatumSplit
#print axioms DensePackGatedClosureResidual.densePackStarts_empty_of_gate
#print axioms DensePackGatedClosureResidual.densePackStarts_empty_of_r_eq_zero
#print axioms DensePackGatedClosureResidual.densePackStarts_empty_of_L_le
#print axioms DensePackGatedClosureResidual.hDensePackField
#print axioms DensePackDatumSplitResidual.toGatedClosure
#print axioms nonempty_gatedClosure_iff_datumSplit
#print axioms erdos260_of_gatedClosure
#print axioms densePackGatedClosureStatus_nonempty

end

end Erdos260
