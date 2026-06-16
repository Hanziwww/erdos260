import Erdos260.ChernoffClass0DatumClosure
import Erdos260.RunClass5BoundaryClosure

/-!
# Class-0 (Chernoff) survivor residue closure, wave 5

This module (NEW; it edits no existing file) attacks the wave-4 residual of
`ChernoffClass0DatumClosure`: the capstone field `class0Cycle : ∀ ctx, Class0WindowCycleCheck ctx`
reduced by `class0Cycle_of_datum_split` to (i) the windowed check on the NINETEEN survivor
datum pairs (`Class0DatumSurvivor`, all with the deep value `1` on-cycle below modulus `48`)
and (ii) the windowed check on every `48 ≤ q` shell.

## What IS newly closed here (all unconditional theorems)

* **The generic residue-window levers** (`class0WindowCycleCheck_of_residue_avoid`,
  `class0WindowCycleCheck_residue_necessary`): for ANY datum pair with `q < 48`, an explicit
  period `c` and a single deep residue `ρ`, the windowed check holds IFF every floor-realizing
  window start misses the congruence `k ≡ ρ [MOD c]` — sufficiency reads the orbit at
  `cycleRep c k` (odd, `≠ 1`, hence `≥ 3` and `16·K ≥ 48 > q`), necessity transports the deep
  representative through any period of the check.
* **All seventeen remaining survivor pairs get window-residue exploits** (mirroring the wave-4
  flagships `(17,8)`/`(21,1)`): explicit cycles, the per-pair pinned exploits
  `class0Pinned_of_datum_<q>_<K₀>_window`, and the per-pair EXACT characterizations
  `class0WindowCycleCheck_iff_datum_<q>_<K₀>` — the windowed check on a survivor shell IS the
  single-congruence miss.  Deep residue table (period `c`, residue `ρ`, `ρ = 0` meaning
  `c ∣ k`): (17,8):(4,0); (19,9):(9,6); (21,1):(2,0); (25,2):(10,0); (25,12):(10,8);
  (27,1):(9,0); (27,4):(9,0); (27,13):(9,7); (29,14):(14,10); (33,1):(5,0); (33,16):(5,0);
  (35,2):(5,0); (37,18):(18,10); (39,1):(4,0); (41,20):(10,8); (43,21):(7,6); (45,1):(5,0);
  (45,2):(5,0); (45,4):(5,0).
* **The conflict probe outcome** (honest): NO survivor pair closes outright.  The only
  unconditional facts about floor-realizing starts (positivity `k ≥ 1`, shell-window
  membership, the gate violation `129L+64 ≤ 64(r+1)(L+B+1)` — which the proved pressure floor
  makes automatic) exclude no residue class mod `c`; the `r = 0` top-start pin
  (`n24_r_eq_zero_of_L_le` + the single-start structure) fires only VACUOUSLY because
  `n24_r_pos` / `shellLadderDepth_ge_15421` prove `r ≥ 1` and `L ≥ 15421` at every actual ctx
  (`class0WindowCycleCheck_of_r_eq_zero`, `class0WindowCycleCheck_of_depth_le`).
* **The `48 ≤ q < 96` band criterion** (`deepBand_odd_shallow_of_modulus_lt_96`,
  `class0CycleDeepBandFree_of_cycle_avoids_shallow_of_modulus_lt_96`,
  `class0Pinned_of_cycle_avoids_shallow_of_modulus_lt_96`,
  `class0CycleDeepBandFree_of_datum_avoids_shallow`,
  `class0CycleMeetsShallow_of_not_deepBandFree`): window starts read the orbit at `k ≥ 1`
  where it is ODD, and an odd deep value below modulus `96` is `1`, `3` or `5`; hence a cycle
  avoiding `{1, 3, 5}` passes the window-free check on every `q < 96` shell, and conversely a
  failing check puts one of `1, 3, 5` ON the cycle (`Class0CycleMeetsShallow`).
* **The band-5 datum enumerations** (`datum_band5_lower_window_pairs`,
  `datum_band5_upper_window_pairs`): under the divisor pin `(2·K₀+1) ∣ q` the window
  `48 ≤ q < 72` admits EXACTLY twenty-seven pairs and `72 ≤ q < 96` exactly thirty-one —
  pure `(q, K₀)` arithmetic (cofactor case split), mirroring the wave-4 enumerations.
  Combined resolution `class0_datum_band5_window_resolved`: every `48 ≤ q < 96` ctx either
  passes the window-free check or carries one of the 58 listed pairs with a shallow value
  `{1,3,5}` provably on its cycle.
* **The strictly smaller successor split** (`Class0SurvivorResidueMiss`,
  `class0WindowCycleCheck_of_survivor_residueMiss`,
  `class0_survivor_residueMiss_of_windowCycleCheck`, `class0WindowCycleCheck_of_band5_split`,
  `class0Cycle_of_survivor_residue_split`, `class0Pinned_field_of_survivor_residue_split`,
  `class0FibreEmpty_of_survivor_residue_split`): the capstone field (verbatim type
  `∀ ctx, Class0WindowCycleCheck ctx`) follows from (a) the per-pair congruence misses on the
  nineteen survivors (a single residue per pair — equivalent to the wave-4 survivor windowed
  checks by the iffs, and strictly more explicit), (b) the windowed check on `48 ≤ q < 96`
  shells ONLY where the cycle provably meets `{1,3,5}`, and (c) the windowed check on
  `96 ≤ q`.  The comparison theorems (`class0_survivorResidueMiss_hypothesis_of_datum_split`,
  `class0_band5_hypotheses_of_datum_split`) derive every successor hypothesis from the wave-4
  pair, so the new surface is never harder and is strictly smaller on the mid band.

## Honest obstruction boundary (proved, not conjectured)

The nineteen survivor cycles contain the deep value `1`
(`class0_datum_survivor_defeats_cycleCheck`), so on those shells only the congruence miss at
floor-realizing starts can close the atom, and the proved pressure floor
(`chernoffClass0_highExcessStarts_nonempty`) guarantees floor-realizing starts EXIST.  No
formalized `hitGap ↔ canonGap` bridge exists at the actual ctx; we do NOT claim unconditional
closure of the atom.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The generic residue-window levers

For a datum pair `(qv, Kv)` with `qv < 48`, an explicit period `c` valid from index `1`, and
a SINGLE deep residue `ρ < c` (the position of the value `1` on the cycle, mod `c`), the
windowed check is decided by one congruence per floor-realizing start. -/

/-- One explicit orbit step through the band bounds (local copy of the wave-4 evaluator):
from `K_j = K` and `q < 2^g·K < 2q`, read off `K_{j+1} = 2^g·K − q`. -/
private theorem srvStep {q K₀ j K g K' : ℕ} (hq : Odd q)
    (h : slopeOrbit q K₀ j = K) (hK1 : 1 ≤ K) (hKq : K < q)
    (hlow : q < 2 ^ g * K) (hhigh : 2 ^ g * K < 2 * q) (hval : 2 ^ g * K - q = K') :
    slopeOrbit q K₀ (j + 1) = K' := by
  have hstep : slopeOrbit q K₀ (j + 1) = boundedSlopeStep q (slopeOrbit q K₀ j) := rfl
  rw [hstep, h, boundedSlopeStep_eq_of_bounds hq hK1 hKq hlow hhigh, hval]

/-- **The generic residue-avoid sufficiency**: on a `q < 48` shell with period `c ≤ q` whose
cycle reads `1` ONLY at indices `≡ ρ [MOD c]`, the windowed check holds as soon as every
floor-realizing window start misses that congruence (off-residue representatives are odd and
`≠ 1`, hence `≥ 3`, hence outside the deep band `16·K ≤ q < 48`). -/
theorem class0WindowCycleCheck_of_residue_avoid (ctx : ActualFailureContext)
    {qv Kv c ρ : ℕ} (hq : (class1SlopeDatum ctx).q = qv)
    (hK : (class1SlopeDatum ctx).K₀ = Kv) (hq48 : qv < 48) (hc1 : 1 ≤ c) (hcq : c ≤ qv)
    (hper : ∀ m, 1 ≤ m → slopeOrbit qv Kv (m + c) = slopeOrbit qv Kv m)
    (hone : ∀ j, 1 ≤ j → j ≤ c → j % c ≠ ρ → slopeOrbit qv Kv j ≠ 1)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % c ≠ ρ) :
    Class0WindowCycleCheck ctx := by
  subst hq; subst hK
  refine ⟨c, hc1, hcq, hper, fun k hk hfl => ?_⟩
  have hcrpos := cycleRep_pos hc1 k
  have hcrle := cycleRep_le hc1 k
  have hmod : cycleRep c k % c = k % c := by
    unfold cycleRep
    by_cases h0 : k % c = 0
    · rw [if_pos h0, Nat.mod_self, h0]
    · rw [if_neg h0]
      exact Nat.mod_mod_of_dvd k (dvd_refl c)
  have hone' : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
      (cycleRep c k) ≠ 1 := hone _ hcrpos hcrle (by rw [hmod]; exact h k hk hfl)
  have hodd := slopeOrbit_odd (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt (cycleRep c k) hcrpos
  obtain ⟨t, ht⟩ := hodd
  omega

/-- **The generic residue necessity**: if the cycle is DEEP at the residue `ρ` (its
representative `cycleRep c ρ` reads a deep value), then the windowed check FORCES every
floor-realizing window start to miss the congruence `k ≡ ρ [MOD c]` — the windowed check on
the pair is never weaker than the congruence miss. -/
theorem class0WindowCycleCheck_residue_necessary (ctx : ActualFailureContext)
    {qv Kv c ρ : ℕ} (hq : (class1SlopeDatum ctx).q = qv)
    (hK : (class1SlopeDatum ctx).K₀ = Kv) (hc1 : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit qv Kv (m + c) = slopeOrbit qv Kv m)
    (hρ : ρ % c = ρ) (hdeep : 16 * slopeOrbit qv Kv (cycleRep c ρ) ≤ qv)
    (hcheck : Class0WindowCycleCheck ctx) :
    ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % c ≠ ρ := by
  subst hq; subst hK
  intro k hk hfl hkρ
  have hk1 : 1 ≤ k := n24_starts_pos ctx hk
  obtain ⟨c', hc'1, hc'q, hper', hbody⟩ := hcheck
  have hlt := hbody k hk hfl
  rw [← slopeOrbit_cycleRep hc'1 hper' hk1] at hlt
  have hcrk : cycleRep c k = cycleRep c ρ := by
    unfold cycleRep
    rw [hkρ, hρ]
  rw [slopeOrbit_cycleRep hc1 hper hk1, hcrk] at hlt
  omega

/-! ## Part 2.  The nineteen survivor cycle certificates

Each certificate carries: the period (first return to the index-`1` value), the deep value
`1` at its unique cycle position, and the avoidance of `1` at every OFF-residue position. -/

private theorem orbit_17_8_cert :
    (∀ m, 1 ≤ m → slopeOrbit 17 8 (m + 4) = slopeOrbit 17 8 m)
    ∧ slopeOrbit 17 8 4 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 4 → j % 4 ≠ 0 → slopeOrbit 17 8 j ≠ 1 := by
  have hq : Odd 17 := ⟨8, by norm_num⟩
  have h0 : slopeOrbit 17 8 0 = 8 := rfl
  have h1 : slopeOrbit 17 8 1 = 15 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 17 8 2 = 13 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 17 8 3 = 9 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 17 8 4 = 1 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 17 8 5 = 15 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h4, ?_⟩
  · show slopeOrbit 17 8 5 = slopeOrbit 17 8 1
    rw [h5, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_19_9_cert :
    (∀ m, 1 ≤ m → slopeOrbit 19 9 (m + 9) = slopeOrbit 19 9 m)
    ∧ slopeOrbit 19 9 6 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 9 → j % 9 ≠ 6 → slopeOrbit 19 9 j ≠ 1 := by
  have hq : Odd 19 := ⟨9, by norm_num⟩
  have h0 : slopeOrbit 19 9 0 = 9 := rfl
  have h1 : slopeOrbit 19 9 1 = 17 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 19 9 2 = 15 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 19 9 3 = 11 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 19 9 4 = 3 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 19 9 5 = 5 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 19 9 6 = 1 :=
    srvStep hq h5 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 19 9 7 = 13 :=
    srvStep hq h6 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 19 9 8 = 7 :=
    srvStep hq h7 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h9 : slopeOrbit 19 9 9 = 9 :=
    srvStep hq h8 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h10 : slopeOrbit 19 9 10 = 17 :=
    srvStep hq h9 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h6, ?_⟩
  · show slopeOrbit 19 9 10 = slopeOrbit 19 9 1
    rw [h10, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_21_1_cert :
    (∀ m, 1 ≤ m → slopeOrbit 21 1 (m + 2) = slopeOrbit 21 1 m)
    ∧ slopeOrbit 21 1 2 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 2 → j % 2 ≠ 0 → slopeOrbit 21 1 j ≠ 1 := by
  have hq : Odd 21 := ⟨10, by norm_num⟩
  have h0 : slopeOrbit 21 1 0 = 1 := rfl
  have h1 : slopeOrbit 21 1 1 = 11 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 21 1 2 = 1 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 21 1 3 = 11 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h2, ?_⟩
  · show slopeOrbit 21 1 3 = slopeOrbit 21 1 1
    rw [h3, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_25_2_cert :
    (∀ m, 1 ≤ m → slopeOrbit 25 2 (m + 10) = slopeOrbit 25 2 m)
    ∧ slopeOrbit 25 2 10 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 10 → j % 10 ≠ 0 → slopeOrbit 25 2 j ≠ 1 := by
  have hq : Odd 25 := ⟨12, by norm_num⟩
  have h0 : slopeOrbit 25 2 0 = 2 := rfl
  have h1 : slopeOrbit 25 2 1 = 7 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 25 2 2 = 3 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 25 2 3 = 23 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 25 2 4 = 21 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 25 2 5 = 17 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 25 2 6 = 9 :=
    srvStep hq h5 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 25 2 7 = 11 :=
    srvStep hq h6 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 25 2 8 = 19 :=
    srvStep hq h7 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h9 : slopeOrbit 25 2 9 = 13 :=
    srvStep hq h8 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h10 : slopeOrbit 25 2 10 = 1 :=
    srvStep hq h9 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h11 : slopeOrbit 25 2 11 = 7 :=
    srvStep hq h10 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h10, ?_⟩
  · show slopeOrbit 25 2 11 = slopeOrbit 25 2 1
    rw [h11, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_25_12_cert :
    (∀ m, 1 ≤ m → slopeOrbit 25 12 (m + 10) = slopeOrbit 25 12 m)
    ∧ slopeOrbit 25 12 8 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 10 → j % 10 ≠ 8 → slopeOrbit 25 12 j ≠ 1 := by
  have hq : Odd 25 := ⟨12, by norm_num⟩
  have h0 : slopeOrbit 25 12 0 = 12 := rfl
  have h1 : slopeOrbit 25 12 1 = 23 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 25 12 2 = 21 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 25 12 3 = 17 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 25 12 4 = 9 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 25 12 5 = 11 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 25 12 6 = 19 :=
    srvStep hq h5 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 25 12 7 = 13 :=
    srvStep hq h6 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 25 12 8 = 1 :=
    srvStep hq h7 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h9 : slopeOrbit 25 12 9 = 7 :=
    srvStep hq h8 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  have h10 : slopeOrbit 25 12 10 = 3 :=
    srvStep hq h9 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h11 : slopeOrbit 25 12 11 = 23 :=
    srvStep hq h10 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h8, ?_⟩
  · show slopeOrbit 25 12 11 = slopeOrbit 25 12 1
    rw [h11, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_27_1_cert :
    (∀ m, 1 ≤ m → slopeOrbit 27 1 (m + 9) = slopeOrbit 27 1 m)
    ∧ slopeOrbit 27 1 9 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 9 → j % 9 ≠ 0 → slopeOrbit 27 1 j ≠ 1 := by
  have hq : Odd 27 := ⟨13, by norm_num⟩
  have h0 : slopeOrbit 27 1 0 = 1 := rfl
  have h1 : slopeOrbit 27 1 1 = 5 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 27 1 2 = 13 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 27 1 3 = 25 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 27 1 4 = 23 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 27 1 5 = 19 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 27 1 6 = 11 :=
    srvStep hq h5 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 27 1 7 = 17 :=
    srvStep hq h6 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 27 1 8 = 7 :=
    srvStep hq h7 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h9 : slopeOrbit 27 1 9 = 1 :=
    srvStep hq h8 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h10 : slopeOrbit 27 1 10 = 5 :=
    srvStep hq h9 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h9, ?_⟩
  · show slopeOrbit 27 1 10 = slopeOrbit 27 1 1
    rw [h10, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_27_4_cert :
    (∀ m, 1 ≤ m → slopeOrbit 27 4 (m + 9) = slopeOrbit 27 4 m)
    ∧ slopeOrbit 27 4 9 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 9 → j % 9 ≠ 0 → slopeOrbit 27 4 j ≠ 1 := by
  have hq : Odd 27 := ⟨13, by norm_num⟩
  have h0 : slopeOrbit 27 4 0 = 4 := rfl
  have h1 : slopeOrbit 27 4 1 = 5 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 27 4 2 = 13 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 27 4 3 = 25 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 27 4 4 = 23 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 27 4 5 = 19 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 27 4 6 = 11 :=
    srvStep hq h5 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 27 4 7 = 17 :=
    srvStep hq h6 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 27 4 8 = 7 :=
    srvStep hq h7 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h9 : slopeOrbit 27 4 9 = 1 :=
    srvStep hq h8 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h10 : slopeOrbit 27 4 10 = 5 :=
    srvStep hq h9 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h9, ?_⟩
  · show slopeOrbit 27 4 10 = slopeOrbit 27 4 1
    rw [h10, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_27_13_cert :
    (∀ m, 1 ≤ m → slopeOrbit 27 13 (m + 9) = slopeOrbit 27 13 m)
    ∧ slopeOrbit 27 13 7 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 9 → j % 9 ≠ 7 → slopeOrbit 27 13 j ≠ 1 := by
  have hq : Odd 27 := ⟨13, by norm_num⟩
  have h0 : slopeOrbit 27 13 0 = 13 := rfl
  have h1 : slopeOrbit 27 13 1 = 25 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 27 13 2 = 23 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 27 13 3 = 19 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 27 13 4 = 11 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 27 13 5 = 17 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 27 13 6 = 7 :=
    srvStep hq h5 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 27 13 7 = 1 :=
    srvStep hq h6 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 27 13 8 = 5 :=
    srvStep hq h7 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  have h9 : slopeOrbit 27 13 9 = 13 :=
    srvStep hq h8 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h10 : slopeOrbit 27 13 10 = 25 :=
    srvStep hq h9 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h7, ?_⟩
  · show slopeOrbit 27 13 10 = slopeOrbit 27 13 1
    rw [h10, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_29_14_cert :
    (∀ m, 1 ≤ m → slopeOrbit 29 14 (m + 14) = slopeOrbit 29 14 m)
    ∧ slopeOrbit 29 14 10 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 14 → j % 14 ≠ 10 → slopeOrbit 29 14 j ≠ 1 := by
  have hq : Odd 29 := ⟨14, by norm_num⟩
  have h0 : slopeOrbit 29 14 0 = 14 := rfl
  have h1 : slopeOrbit 29 14 1 = 27 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 29 14 2 = 25 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 29 14 3 = 21 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 29 14 4 = 13 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 29 14 5 = 23 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 29 14 6 = 17 :=
    srvStep hq h5 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 29 14 7 = 5 :=
    srvStep hq h6 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 29 14 8 = 11 :=
    srvStep hq h7 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h9 : slopeOrbit 29 14 9 = 15 :=
    srvStep hq h8 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h10 : slopeOrbit 29 14 10 = 1 :=
    srvStep hq h9 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h11 : slopeOrbit 29 14 11 = 3 :=
    srvStep hq h10 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  have h12 : slopeOrbit 29 14 12 = 19 :=
    srvStep hq h11 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num) (by norm_num)
  have h13 : slopeOrbit 29 14 13 = 9 :=
    srvStep hq h12 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h14 : slopeOrbit 29 14 14 = 7 :=
    srvStep hq h13 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h15 : slopeOrbit 29 14 15 = 27 :=
    srvStep hq h14 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h10, ?_⟩
  · show slopeOrbit 29 14 15 = slopeOrbit 29 14 1
    rw [h15, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_33_1_cert :
    (∀ m, 1 ≤ m → slopeOrbit 33 1 (m + 5) = slopeOrbit 33 1 m)
    ∧ slopeOrbit 33 1 5 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 5 → j % 5 ≠ 0 → slopeOrbit 33 1 j ≠ 1 := by
  have hq : Odd 33 := ⟨16, by norm_num⟩
  have h0 : slopeOrbit 33 1 0 = 1 := rfl
  have h1 : slopeOrbit 33 1 1 = 31 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 33 1 2 = 29 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 33 1 3 = 25 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 33 1 4 = 17 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 33 1 5 = 1 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 33 1 6 = 31 :=
    srvStep hq h5 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h5, ?_⟩
  · show slopeOrbit 33 1 6 = slopeOrbit 33 1 1
    rw [h6, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_33_16_cert :
    (∀ m, 1 ≤ m → slopeOrbit 33 16 (m + 5) = slopeOrbit 33 16 m)
    ∧ slopeOrbit 33 16 5 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 5 → j % 5 ≠ 0 → slopeOrbit 33 16 j ≠ 1 := by
  have hq : Odd 33 := ⟨16, by norm_num⟩
  have h0 : slopeOrbit 33 16 0 = 16 := rfl
  have h1 : slopeOrbit 33 16 1 = 31 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 33 16 2 = 29 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 33 16 3 = 25 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 33 16 4 = 17 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 33 16 5 = 1 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 33 16 6 = 31 :=
    srvStep hq h5 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h5, ?_⟩
  · show slopeOrbit 33 16 6 = slopeOrbit 33 16 1
    rw [h6, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_35_2_cert :
    (∀ m, 1 ≤ m → slopeOrbit 35 2 (m + 5) = slopeOrbit 35 2 m)
    ∧ slopeOrbit 35 2 5 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 5 → j % 5 ≠ 0 → slopeOrbit 35 2 j ≠ 1 := by
  have hq : Odd 35 := ⟨17, by norm_num⟩
  have h0 : slopeOrbit 35 2 0 = 2 := rfl
  have h1 : slopeOrbit 35 2 1 = 29 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 35 2 2 = 23 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 35 2 3 = 11 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 35 2 4 = 9 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 35 2 5 = 1 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 35 2 6 = 29 :=
    srvStep hq h5 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h5, ?_⟩
  · show slopeOrbit 35 2 6 = slopeOrbit 35 2 1
    rw [h6, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_37_18_cert :
    (∀ m, 1 ≤ m → slopeOrbit 37 18 (m + 18) = slopeOrbit 37 18 m)
    ∧ slopeOrbit 37 18 10 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 18 → j % 18 ≠ 10 → slopeOrbit 37 18 j ≠ 1 := by
  have hq : Odd 37 := ⟨18, by norm_num⟩
  have h0 : slopeOrbit 37 18 0 = 18 := rfl
  have h1 : slopeOrbit 37 18 1 = 35 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 37 18 2 = 33 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 37 18 3 = 29 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 37 18 4 = 21 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 37 18 5 = 5 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 37 18 6 = 3 :=
    srvStep hq h5 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 37 18 7 = 11 :=
    srvStep hq h6 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 37 18 8 = 7 :=
    srvStep hq h7 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h9 : slopeOrbit 37 18 9 = 19 :=
    srvStep hq h8 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h10 : slopeOrbit 37 18 10 = 1 :=
    srvStep hq h9 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h11 : slopeOrbit 37 18 11 = 27 :=
    srvStep hq h10 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num) (by norm_num)
  have h12 : slopeOrbit 37 18 12 = 17 :=
    srvStep hq h11 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h13 : slopeOrbit 37 18 13 = 31 :=
    srvStep hq h12 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h14 : slopeOrbit 37 18 14 = 25 :=
    srvStep hq h13 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h15 : slopeOrbit 37 18 15 = 13 :=
    srvStep hq h14 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h16 : slopeOrbit 37 18 16 = 15 :=
    srvStep hq h15 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h17 : slopeOrbit 37 18 17 = 23 :=
    srvStep hq h16 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h18 : slopeOrbit 37 18 18 = 9 :=
    srvStep hq h17 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h19 : slopeOrbit 37 18 19 = 35 :=
    srvStep hq h18 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h10, ?_⟩
  · show slopeOrbit 37 18 19 = slopeOrbit 37 18 1
    rw [h19, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_39_1_cert :
    (∀ m, 1 ≤ m → slopeOrbit 39 1 (m + 4) = slopeOrbit 39 1 m)
    ∧ slopeOrbit 39 1 4 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 4 → j % 4 ≠ 0 → slopeOrbit 39 1 j ≠ 1 := by
  have hq : Odd 39 := ⟨19, by norm_num⟩
  have h0 : slopeOrbit 39 1 0 = 1 := rfl
  have h1 : slopeOrbit 39 1 1 = 25 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 39 1 2 = 11 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 39 1 3 = 5 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 39 1 4 = 1 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 39 1 5 = 25 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h4, ?_⟩
  · show slopeOrbit 39 1 5 = slopeOrbit 39 1 1
    rw [h5, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_41_20_cert :
    (∀ m, 1 ≤ m → slopeOrbit 41 20 (m + 10) = slopeOrbit 41 20 m)
    ∧ slopeOrbit 41 20 8 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 10 → j % 10 ≠ 8 → slopeOrbit 41 20 j ≠ 1 := by
  have hq : Odd 41 := ⟨20, by norm_num⟩
  have h0 : slopeOrbit 41 20 0 = 20 := rfl
  have h1 : slopeOrbit 41 20 1 = 39 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 41 20 2 = 37 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 41 20 3 = 33 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 41 20 4 = 25 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 41 20 5 = 9 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 41 20 6 = 31 :=
    srvStep hq h5 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 41 20 7 = 21 :=
    srvStep hq h6 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 41 20 8 = 1 :=
    srvStep hq h7 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h9 : slopeOrbit 41 20 9 = 23 :=
    srvStep hq h8 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num) (by norm_num)
  have h10 : slopeOrbit 41 20 10 = 5 :=
    srvStep hq h9 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h11 : slopeOrbit 41 20 11 = 39 :=
    srvStep hq h10 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h8, ?_⟩
  · show slopeOrbit 41 20 11 = slopeOrbit 41 20 1
    rw [h11, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_43_21_cert :
    (∀ m, 1 ≤ m → slopeOrbit 43 21 (m + 7) = slopeOrbit 43 21 m)
    ∧ slopeOrbit 43 21 6 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 7 → j % 7 ≠ 6 → slopeOrbit 43 21 j ≠ 1 := by
  have hq : Odd 43 := ⟨21, by norm_num⟩
  have h0 : slopeOrbit 43 21 0 = 21 := rfl
  have h1 : slopeOrbit 43 21 1 = 41 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 43 21 2 = 39 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 43 21 3 = 35 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 43 21 4 = 27 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 43 21 5 = 11 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 43 21 6 = 1 :=
    srvStep hq h5 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h7 : slopeOrbit 43 21 7 = 21 :=
    srvStep hq h6 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num) (by norm_num)
  have h8 : slopeOrbit 43 21 8 = 41 :=
    srvStep hq h7 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h6, ?_⟩
  · show slopeOrbit 43 21 8 = slopeOrbit 43 21 1
    rw [h8, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_45_1_cert :
    (∀ m, 1 ≤ m → slopeOrbit 45 1 (m + 5) = slopeOrbit 45 1 m)
    ∧ slopeOrbit 45 1 5 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 5 → j % 5 ≠ 0 → slopeOrbit 45 1 j ≠ 1 := by
  have hq : Odd 45 := ⟨22, by norm_num⟩
  have h0 : slopeOrbit 45 1 0 = 1 := rfl
  have h1 : slopeOrbit 45 1 1 = 19 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 45 1 2 = 31 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 45 1 3 = 17 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 45 1 4 = 23 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 45 1 5 = 1 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 45 1 6 = 19 :=
    srvStep hq h5 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h5, ?_⟩
  · show slopeOrbit 45 1 6 = slopeOrbit 45 1 1
    rw [h6, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_45_2_cert :
    (∀ m, 1 ≤ m → slopeOrbit 45 2 (m + 5) = slopeOrbit 45 2 m)
    ∧ slopeOrbit 45 2 5 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 5 → j % 5 ≠ 0 → slopeOrbit 45 2 j ≠ 1 := by
  have hq : Odd 45 := ⟨22, by norm_num⟩
  have h0 : slopeOrbit 45 2 0 = 2 := rfl
  have h1 : slopeOrbit 45 2 1 = 19 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 45 2 2 = 31 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 45 2 3 = 17 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 45 2 4 = 23 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 45 2 5 = 1 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 45 2 6 = 19 :=
    srvStep hq h5 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h5, ?_⟩
  · show slopeOrbit 45 2 6 = slopeOrbit 45 2 1
    rw [h6, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

private theorem orbit_45_4_cert :
    (∀ m, 1 ≤ m → slopeOrbit 45 4 (m + 5) = slopeOrbit 45 4 m)
    ∧ slopeOrbit 45 4 5 = 1
    ∧ ∀ j, 1 ≤ j → j ≤ 5 → j % 5 ≠ 0 → slopeOrbit 45 4 j ≠ 1 := by
  have hq : Odd 45 := ⟨22, by norm_num⟩
  have h0 : slopeOrbit 45 4 0 = 4 := rfl
  have h1 : slopeOrbit 45 4 1 = 19 :=
    srvStep hq h0 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num) (by norm_num)
  have h2 : slopeOrbit 45 4 2 = 31 :=
    srvStep hq h1 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h3 : slopeOrbit 45 4 3 = 17 :=
    srvStep hq h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h4 : slopeOrbit 45 4 4 = 23 :=
    srvStep hq h3 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num) (by norm_num)
  have h5 : slopeOrbit 45 4 5 = 1 :=
    srvStep hq h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num) (by norm_num)
  have h6 : slopeOrbit 45 4 6 = 19 :=
    srvStep hq h5 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨slopeOrbit_period_of_return ?_, h5, ?_⟩
  · show slopeOrbit 45 4 6 = slopeOrbit 45 4 1
    rw [h6, h1]
  · intro j hj1 hjc hjr
    interval_cases j <;> omega

/-! ## Part 3.  The per-pair residue exploits

For every survivor pair: the EXACT characterization (the windowed check IS the congruence
miss at floor-realizing starts) and — for the seventeen pairs beyond the wave-4 flagships —
the pinned window exploit mirroring `class0Pinned_of_datum_17_8_window`. -/

/-- **`(17, 8)` exact residue characterization**: the windowed check holds IFF no
floor-realizing start has `4 ∣ k` (deep residue table entry `(c, ρ) = (4, 0)`). -/
theorem class0WindowCycleCheck_iff_datum_17_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 17) (hK : (class1SlopeDatum ctx).K₀ = 8) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 4 ≠ 0 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_17_8_cert.1
      (by norm_num)
      (by rw [show cycleRep 4 0 = 4 by norm_num [cycleRep], orbit_17_8_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_17_8_cert.1 orbit_17_8_cert.2.2⟩

/-- **`(19, 9)` exact residue characterization**: deep residues exactly `k ≡ 6 [MOD 9]`
(period-`9` cycle `17, 15, 11, 3, 5, 1, 13, 7, 9`). -/
theorem class0WindowCycleCheck_iff_datum_19_9 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 19) (hK : (class1SlopeDatum ctx).K₀ = 9) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 9 ≠ 6 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_19_9_cert.1
      (by norm_num)
      (by rw [show cycleRep 9 6 = 6 by norm_num [cycleRep], orbit_19_9_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_19_9_cert.1 orbit_19_9_cert.2.2⟩

/-- **`(19, 9)` window exploit** (mirror of `class0Pinned_of_datum_17_8_window`): if no
floor-realizing window start has `k ≡ 6 [MOD 9]`, the ctx closes. -/
theorem class0Pinned_of_datum_19_9_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 19) (hK : (class1SlopeDatum ctx).K₀ = 9)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % 9 ≠ 6) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_windowCycleCheck ctx
    ((class0WindowCycleCheck_iff_datum_19_9 ctx hq hK).mpr h)

/-- **`(21, 1)` exact residue characterization**: deep residues exactly the even starts
(period-`2` cycle `11, 1`). -/
theorem class0WindowCycleCheck_iff_datum_21_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 2 ≠ 0 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_21_1_cert.1
      (by norm_num)
      (by rw [show cycleRep 2 0 = 2 by norm_num [cycleRep], orbit_21_1_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_21_1_cert.1 orbit_21_1_cert.2.2⟩

/-- **`(25, 2)` exact residue characterization**: deep residues exactly `10 ∣ k`
(period-`10` cycle `7, 3, 23, 21, 17, 9, 11, 19, 13, 1`). -/
theorem class0WindowCycleCheck_iff_datum_25_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 10 ≠ 0 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_25_2_cert.1
      (by norm_num)
      (by rw [show cycleRep 10 0 = 10 by norm_num [cycleRep], orbit_25_2_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_25_2_cert.1 orbit_25_2_cert.2.2⟩

/-- **`(25, 2)` window exploit**: no floor-realizing start with `10 ∣ k` closes the ctx. -/
theorem class0Pinned_of_datum_25_2_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % 10 ≠ 0) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_windowCycleCheck ctx
    ((class0WindowCycleCheck_iff_datum_25_2 ctx hq hK).mpr h)

/-- **`(25, 12)` exact residue characterization**: deep residues exactly `k ≡ 8 [MOD 10]`
(period-`10` cycle `23, 21, 17, 9, 11, 19, 13, 1, 7, 3`). -/
theorem class0WindowCycleCheck_iff_datum_25_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 12) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 10 ≠ 8 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_25_12_cert.1
      (by norm_num)
      (by rw [show cycleRep 10 8 = 8 by norm_num [cycleRep], orbit_25_12_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_25_12_cert.1 orbit_25_12_cert.2.2⟩

/-- **`(25, 12)` window exploit**: no floor-realizing start `≡ 8 [MOD 10]` closes the ctx. -/
theorem class0Pinned_of_datum_25_12_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 12)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % 10 ≠ 8) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_windowCycleCheck ctx
    ((class0WindowCycleCheck_iff_datum_25_12 ctx hq hK).mpr h)

/-- **`(27, 1)` exact residue characterization**: deep residues exactly `9 ∣ k`
(period-`9` cycle `5, 13, 25, 23, 19, 11, 17, 7, 1`). -/
theorem class0WindowCycleCheck_iff_datum_27_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 9 ≠ 0 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_27_1_cert.1
      (by norm_num)
      (by rw [show cycleRep 9 0 = 9 by norm_num [cycleRep], orbit_27_1_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_27_1_cert.1 orbit_27_1_cert.2.2⟩

/-- **`(27, 1)` window exploit**: no floor-realizing start with `9 ∣ k` closes the ctx. -/
theorem class0Pinned_of_datum_27_1_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % 9 ≠ 0) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_windowCycleCheck ctx
    ((class0WindowCycleCheck_iff_datum_27_1 ctx hq hK).mpr h)

/-- **`(27, 4)` exact residue characterization**: deep residues exactly `9 ∣ k`
(period-`9` cycle `5, 13, 25, 23, 19, 11, 17, 7, 1`). -/
theorem class0WindowCycleCheck_iff_datum_27_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 9 ≠ 0 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_27_4_cert.1
      (by norm_num)
      (by rw [show cycleRep 9 0 = 9 by norm_num [cycleRep], orbit_27_4_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_27_4_cert.1 orbit_27_4_cert.2.2⟩

/-- **`(27, 4)` window exploit**: no floor-realizing start with `9 ∣ k` closes the ctx. -/
theorem class0Pinned_of_datum_27_4_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 4)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % 9 ≠ 0) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_windowCycleCheck ctx
    ((class0WindowCycleCheck_iff_datum_27_4 ctx hq hK).mpr h)

/-- **`(27, 13)` exact residue characterization**: deep residues exactly `k ≡ 7 [MOD 9]`
(period-`9` cycle `25, 23, 19, 11, 17, 7, 1, 5, 13`). -/
theorem class0WindowCycleCheck_iff_datum_27_13 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 13) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 9 ≠ 7 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_27_13_cert.1
      (by norm_num)
      (by rw [show cycleRep 9 7 = 7 by norm_num [cycleRep], orbit_27_13_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_27_13_cert.1 orbit_27_13_cert.2.2⟩

/-- **`(27, 13)` window exploit**: no floor-realizing start `≡ 7 [MOD 9]` closes the ctx. -/
theorem class0Pinned_of_datum_27_13_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 13)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % 9 ≠ 7) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_windowCycleCheck ctx
    ((class0WindowCycleCheck_iff_datum_27_13 ctx hq hK).mpr h)

/-- **`(29, 14)` exact residue characterization**: deep residues exactly `k ≡ 10 [MOD 14]`
(period-`14` cycle `27, 25, 21, 13, 23, 17, 5, 11, 15, 1, 3, 19, 9, 7`). -/
theorem class0WindowCycleCheck_iff_datum_29_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 29) (hK : (class1SlopeDatum ctx).K₀ = 14) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 14 ≠ 10 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_29_14_cert.1
      (by norm_num)
      (by rw [show cycleRep 14 10 = 10 by norm_num [cycleRep], orbit_29_14_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_29_14_cert.1 orbit_29_14_cert.2.2⟩

/-- **`(29, 14)` window exploit**: no floor-realizing start `≡ 10 [MOD 14]` closes the ctx. -/
theorem class0Pinned_of_datum_29_14_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 29) (hK : (class1SlopeDatum ctx).K₀ = 14)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % 14 ≠ 10) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_windowCycleCheck ctx
    ((class0WindowCycleCheck_iff_datum_29_14 ctx hq hK).mpr h)

/-- **`(33, 1)` exact residue characterization**: deep residues exactly `5 ∣ k`
(period-`5` cycle `31, 29, 25, 17, 1`). -/
theorem class0WindowCycleCheck_iff_datum_33_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 5 ≠ 0 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_33_1_cert.1
      (by norm_num)
      (by rw [show cycleRep 5 0 = 5 by norm_num [cycleRep], orbit_33_1_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_33_1_cert.1 orbit_33_1_cert.2.2⟩

/-- **`(33, 1)` window exploit**: no floor-realizing start with `5 ∣ k` closes the ctx. -/
theorem class0Pinned_of_datum_33_1_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % 5 ≠ 0) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_windowCycleCheck ctx
    ((class0WindowCycleCheck_iff_datum_33_1 ctx hq hK).mpr h)

/-- **`(33, 16)` exact residue characterization**: deep residues exactly `5 ∣ k`
(period-`5` cycle `31, 29, 25, 17, 1`). -/
theorem class0WindowCycleCheck_iff_datum_33_16 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 16) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 5 ≠ 0 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_33_16_cert.1
      (by norm_num)
      (by rw [show cycleRep 5 0 = 5 by norm_num [cycleRep], orbit_33_16_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_33_16_cert.1 orbit_33_16_cert.2.2⟩

/-- **`(33, 16)` window exploit**: no floor-realizing start with `5 ∣ k` closes the ctx. -/
theorem class0Pinned_of_datum_33_16_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 16)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % 5 ≠ 0) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_windowCycleCheck ctx
    ((class0WindowCycleCheck_iff_datum_33_16 ctx hq hK).mpr h)

/-- **`(35, 2)` exact residue characterization**: deep residues exactly `5 ∣ k`
(period-`5` cycle `29, 23, 11, 9, 1`). -/
theorem class0WindowCycleCheck_iff_datum_35_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 5 ≠ 0 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_35_2_cert.1
      (by norm_num)
      (by rw [show cycleRep 5 0 = 5 by norm_num [cycleRep], orbit_35_2_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_35_2_cert.1 orbit_35_2_cert.2.2⟩

/-- **`(35, 2)` window exploit**: no floor-realizing start with `5 ∣ k` closes the ctx. -/
theorem class0Pinned_of_datum_35_2_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % 5 ≠ 0) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_windowCycleCheck ctx
    ((class0WindowCycleCheck_iff_datum_35_2 ctx hq hK).mpr h)

/-- **`(37, 18)` exact residue characterization**: deep residues exactly `k ≡ 10 [MOD 18]`
(period-`18` cycle `35, 33, 29, 21, 5, 3, 11, 7, 19, 1, 27, 17, 31, 25, 13, 15, 23, 9`). -/
theorem class0WindowCycleCheck_iff_datum_37_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 37) (hK : (class1SlopeDatum ctx).K₀ = 18) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 18 ≠ 10 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_37_18_cert.1
      (by norm_num)
      (by rw [show cycleRep 18 10 = 10 by norm_num [cycleRep], orbit_37_18_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_37_18_cert.1 orbit_37_18_cert.2.2⟩

/-- **`(37, 18)` window exploit**: no floor-realizing start `≡ 10 [MOD 18]` closes the ctx. -/
theorem class0Pinned_of_datum_37_18_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 37) (hK : (class1SlopeDatum ctx).K₀ = 18)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % 18 ≠ 10) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_windowCycleCheck ctx
    ((class0WindowCycleCheck_iff_datum_37_18 ctx hq hK).mpr h)

/-- **`(39, 1)` exact residue characterization**: deep residues exactly `4 ∣ k`
(period-`4` cycle `25, 11, 5, 1`). -/
theorem class0WindowCycleCheck_iff_datum_39_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 4 ≠ 0 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_39_1_cert.1
      (by norm_num)
      (by rw [show cycleRep 4 0 = 4 by norm_num [cycleRep], orbit_39_1_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_39_1_cert.1 orbit_39_1_cert.2.2⟩

/-- **`(39, 1)` window exploit**: no floor-realizing start with `4 ∣ k` closes the ctx. -/
theorem class0Pinned_of_datum_39_1_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % 4 ≠ 0) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_windowCycleCheck ctx
    ((class0WindowCycleCheck_iff_datum_39_1 ctx hq hK).mpr h)

/-- **`(41, 20)` exact residue characterization**: deep residues exactly `k ≡ 8 [MOD 10]`
(period-`10` cycle `39, 37, 33, 25, 9, 31, 21, 1, 23, 5`). -/
theorem class0WindowCycleCheck_iff_datum_41_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 41) (hK : (class1SlopeDatum ctx).K₀ = 20) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 10 ≠ 8 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_41_20_cert.1
      (by norm_num)
      (by rw [show cycleRep 10 8 = 8 by norm_num [cycleRep], orbit_41_20_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_41_20_cert.1 orbit_41_20_cert.2.2⟩

/-- **`(41, 20)` window exploit**: no floor-realizing start `≡ 8 [MOD 10]` closes the ctx. -/
theorem class0Pinned_of_datum_41_20_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 41) (hK : (class1SlopeDatum ctx).K₀ = 20)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % 10 ≠ 8) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_windowCycleCheck ctx
    ((class0WindowCycleCheck_iff_datum_41_20 ctx hq hK).mpr h)

/-- **`(43, 21)` exact residue characterization**: deep residues exactly `k ≡ 6 [MOD 7]`
(period-`7` cycle `41, 39, 35, 27, 11, 1, 21`). -/
theorem class0WindowCycleCheck_iff_datum_43_21 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 43) (hK : (class1SlopeDatum ctx).K₀ = 21) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 7 ≠ 6 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_43_21_cert.1
      (by norm_num)
      (by rw [show cycleRep 7 6 = 6 by norm_num [cycleRep], orbit_43_21_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_43_21_cert.1 orbit_43_21_cert.2.2⟩

/-- **`(43, 21)` window exploit**: no floor-realizing start `≡ 6 [MOD 7]` closes the ctx. -/
theorem class0Pinned_of_datum_43_21_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 43) (hK : (class1SlopeDatum ctx).K₀ = 21)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % 7 ≠ 6) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_windowCycleCheck ctx
    ((class0WindowCycleCheck_iff_datum_43_21 ctx hq hK).mpr h)

/-- **`(45, 1)` exact residue characterization**: deep residues exactly `5 ∣ k`
(period-`5` cycle `19, 31, 17, 23, 1`). -/
theorem class0WindowCycleCheck_iff_datum_45_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 5 ≠ 0 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_45_1_cert.1
      (by norm_num)
      (by rw [show cycleRep 5 0 = 5 by norm_num [cycleRep], orbit_45_1_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_45_1_cert.1 orbit_45_1_cert.2.2⟩

/-- **`(45, 1)` window exploit**: no floor-realizing start with `5 ∣ k` closes the ctx. -/
theorem class0Pinned_of_datum_45_1_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % 5 ≠ 0) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_windowCycleCheck ctx
    ((class0WindowCycleCheck_iff_datum_45_1 ctx hq hK).mpr h)

/-- **`(45, 2)` exact residue characterization**: deep residues exactly `5 ∣ k`
(period-`5` cycle `19, 31, 17, 23, 1`). -/
theorem class0WindowCycleCheck_iff_datum_45_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 5 ≠ 0 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_45_2_cert.1
      (by norm_num)
      (by rw [show cycleRep 5 0 = 5 by norm_num [cycleRep], orbit_45_2_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_45_2_cert.1 orbit_45_2_cert.2.2⟩

/-- **`(45, 2)` window exploit**: no floor-realizing start with `5 ∣ k` closes the ctx. -/
theorem class0Pinned_of_datum_45_2_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % 5 ≠ 0) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_windowCycleCheck ctx
    ((class0WindowCycleCheck_iff_datum_45_2 ctx hq hK).mpr h)

/-- **`(45, 4)` exact residue characterization**: deep residues exactly `5 ∣ k`
(period-`5` cycle `19, 31, 17, 23, 1`). -/
theorem class0WindowCycleCheck_iff_datum_45_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    Class0WindowCycleCheck ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k % 5 ≠ 0 :=
  ⟨class0WindowCycleCheck_residue_necessary ctx hq hK (by norm_num) orbit_45_4_cert.1
      (by norm_num)
      (by rw [show cycleRep 5 0 = 5 by norm_num [cycleRep], orbit_45_4_cert.2.1]; norm_num),
    class0WindowCycleCheck_of_residue_avoid ctx hq hK (by norm_num) (by norm_num)
      (by norm_num) orbit_45_4_cert.1 orbit_45_4_cert.2.2⟩

/-- **`(45, 4)` window exploit**: no floor-realizing start with `5 ∣ k` closes the ctx. -/
theorem class0Pinned_of_datum_45_4_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 4)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k % 5 ≠ 0) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_windowCycleCheck ctx
    ((class0WindowCycleCheck_iff_datum_45_4 ctx hq hK).mpr h)

/-! ## Part 4.  The conflict probe: the `r = 0` top-start route is vacuous

The brief's conflict levers for closing a survivor pair outright are the window facts: start
positivity (`n24_starts_pos`), the gap-floor coupling, and the `r = 0` top-start pin
(`n24_r_eq_zero_of_L_le` + the single-start structure).  The wave-4 Run results
`n24_r_pos` / `shellLadderDepth_ge_15421` prove `r ≥ 1` and `L ≥ 15421` at EVERY actual ctx,
so the whole `r = 0` (equivalently `L ≤ 15420`) regime fires only vacuously — packaged here
at the exact windowed-check type.  No unconditional fact excludes any start residue class
mod `c`, so no survivor pair closes outright; the residue exploits of Part 3 are the honest
per-pair surface. -/

/-- On an `r = 0` shell the windowed check holds VACUOUSLY: no actual failure context has
`r = 0` (`n24_r_pos`). -/
theorem class0WindowCycleCheck_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) : Class0WindowCycleCheck ctx :=
  absurd hr (by have := n24_r_pos ctx; omega)

/-- On an `L ≤ 15420` shell (the entire `r = ⌊κL⌋ = 0` range of `n24_r_eq_zero_of_L_le`)
the windowed check holds VACUOUSLY: every actual ctx has `L ≥ 15421`
(`shellLadderDepth_ge_15421`). -/
theorem class0WindowCycleCheck_of_depth_le (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 15420) : Class0WindowCycleCheck ctx :=
  absurd hL (by have := shellLadderDepth_ge_15421 ctx; omega)

/-! ## Part 5.  The `48 ≤ q < 96` band: the avoid-`{1, 3, 5}` criterion

Window starts read the orbit at `k ≥ 1` where it is ODD, and an odd deep value below
modulus `96` is `1`, `3` or `5` — extending the wave-4 avoid-`1` technique
(`deepBand_odd_eq_one_of_modulus_lt_48`) by a full dyadic band. -/

/-- **The odd deep band below `96` is `{1, 3, 5}`**: `Odd K`, `16·K ≤ q < 96` force
`K ∈ {1, 3, 5}` (the brief's `K ≤ q/16` bound, verified). -/
theorem deepBand_odd_shallow_of_modulus_lt_96 {q K : ℕ} (hq96 : q < 96) (hodd : Odd K)
    (h16 : 16 * K ≤ q) : K = 1 ∨ K = 3 ∨ K = 5 := by
  obtain ⟨t, ht⟩ := hodd
  omega

/-- **The avoid-`{1,3,5}` check closure on `q < 96`**: a period block avoiding the values
`1`, `3`, `5` yields the window-free check on every modulus `q < 96` (the orbit is odd at
positive indices). -/
theorem class0CycleDeepBandFree_of_cycle_avoids_shallow_of_modulus_lt_96
    (ctx : ActualFailureContext) (hq96 : (class1SlopeDatum ctx).q < 96) {c : ℕ}
    (hc1 : 1 ≤ c) (hcq : c ≤ (class1SlopeDatum ctx).q)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (h135 : ∀ j, 1 ≤ j → j ≤ c →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j ≠ 1
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j ≠ 3
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j ≠ 5) :
    Class0CycleDeepBandFree ctx := by
  refine ⟨c, hc1, hcq, hper, fun j hj1 hjc => ?_⟩
  have hodd := slopeOrbit_odd (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt j hj1
  obtain ⟨hn1, hn3, hn5⟩ := h135 j hj1 hjc
  obtain ⟨t, ht⟩ := hodd
  omega

/-- **Avoid-`{1,3,5}` pinned closure on `q < 96`** — the wave-5 extension of the wave-4
`class0Pinned_of_cycle_avoids_one_of_modulus_lt_48` by a full dyadic band. -/
theorem class0Pinned_of_cycle_avoids_shallow_of_modulus_lt_96 (ctx : ActualFailureContext)
    (hq96 : (class1SlopeDatum ctx).q < 96) {c : ℕ}
    (hc1 : 1 ≤ c) (hcq : c ≤ (class1SlopeDatum ctx).q)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (h135 : ∀ j, 1 ≤ j → j ≤ c →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j ≠ 1
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j ≠ 3
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j ≠ 5) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_cycleCheck ctx
    (class0CycleDeepBandFree_of_cycle_avoids_shallow_of_modulus_lt_96 ctx hq96 hc1 hcq
      hper h135)

/-- Datum-pair form of the avoid-`{1,3,5}` check closure on `q < 96`. -/
theorem class0CycleDeepBandFree_of_datum_avoids_shallow (ctx : ActualFailureContext)
    {qv Kv : ℕ} (hq : (class1SlopeDatum ctx).q = qv) (hK : (class1SlopeDatum ctx).K₀ = Kv)
    (c : ℕ) (hq96 : qv < 96) (hc1 : 1 ≤ c) (hcq : c ≤ qv)
    (hper : ∀ m, 1 ≤ m → slopeOrbit qv Kv (m + c) = slopeOrbit qv Kv m)
    (h135 : ∀ j, 1 ≤ j → j ≤ c →
      slopeOrbit qv Kv j ≠ 1 ∧ slopeOrbit qv Kv j ≠ 3 ∧ slopeOrbit qv Kv j ≠ 5) :
    Class0CycleDeepBandFree ctx := by
  subst hq; subst hK
  exact class0CycleDeepBandFree_of_cycle_avoids_shallow_of_modulus_lt_96 ctx hq96 hc1 hcq
    hper h135

/-- **The wave-5 shallow-cycle predicate**: some positive orbit index reads `1`, `3`, or
`5` — the EXACT content of a window-free check failure below modulus `96`. -/
def Class0CycleMeetsShallow (ctx : ActualFailureContext) : Prop :=
  ∃ j, 1 ≤ j
    ∧ (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j = 1
      ∨ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j = 3
      ∨ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j = 5)

/-- **The converse direction below `96`**: a failing window-free check puts one of
`1, 3, 5` on the cycle (deep value at a positive index, odd, below `96/16 = 6`). -/
theorem class0CycleMeetsShallow_of_not_deepBandFree (ctx : ActualFailureContext)
    (hq96 : (class1SlopeDatum ctx).q < 96) (h : ¬ Class0CycleDeepBandFree ctx) :
    Class0CycleMeetsShallow ctx := by
  rw [class0CycleDeepBandFree_iff_orbit_deepBand_free ctx] at h
  by_contra hcon
  apply h
  intro j hj1
  by_contra hle
  have hodd := slopeOrbit_odd (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt j hj1
  obtain ⟨t, ht⟩ := hodd
  exact hcon ⟨j, hj1, by omega⟩

/-! ## Part 6.  The band-5 datum enumerations: `48 ≤ q < 72` and `72 ≤ q < 96`

Pure `(q, K)` arithmetic from the divisor pin `(2·K+1) ∣ q`: casing on the cofactor
`s = q / (2·K+1) ≤ q/3` keeps every branch linear. -/

/-- The pin cofactor is bounded: `q = (2·K+1)·s` with `1 ≤ K` forces `3·s ≤ q`. -/
private theorem band5_cofactor_le {q K s : ℕ} (hK1 : 1 ≤ K) (hs : q = (2 * K + 1) * s) :
    3 * s ≤ q := by
  have h3 : 3 ≤ 2 * K + 1 := by omega
  calc 3 * s ≤ (2 * K + 1) * s := Nat.mul_le_mul h3 (le_refl s)
    _ = q := hs.symm

private theorem band5_K_of_q_49 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 49) :
    K = 3 ∨ K = 24 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> omega

private theorem band5_K_of_q_51 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 51) :
    K = 1 ∨ K = 8 ∨ K = 25 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16
      ∨ s = 17 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem band5_K_of_q_53 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 53) :
    K = 26 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16
      ∨ s = 17 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem band5_K_of_q_55 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 55) :
    K = 2 ∨ K = 5 ∨ K = 27 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem band5_K_of_q_57 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 57) :
    K = 1 ∨ K = 9 ∨ K = 28 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem band5_K_of_q_59 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 59) :
    K = 29 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem band5_K_of_q_61 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 61) :
    K = 30 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem band5_K_of_q_63 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 63) :
    K = 1 ∨ K = 3 ∨ K = 4 ∨ K = 10 ∨ K = 31 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem band5_K_of_q_65 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 65) :
    K = 2 ∨ K = 6 ∨ K = 32 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem band5_K_of_q_67 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 67) :
    K = 33 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem band5_K_of_q_69 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 69) :
    K = 1 ∨ K = 11 ∨ K = 34 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨ s = 23 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem band5_K_of_q_71 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 71) :
    K = 35 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨ s = 23 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

set_option maxHeartbeats 1000000 in
/-- **The band-5 lower-window datum enumeration**: on `48 ≤ q < 72` the divisor pin admits
exactly twenty-seven pairs. -/
theorem datum_band5_lower_window_pairs {q K : ℕ} (hq_odd : Odd q) (hK1 : 1 ≤ K)
    (h2K : 2 * K < q) (hdvd : 2 * K + 1 ∣ q) (h48 : 48 ≤ q) (h72 : q < 72) :
    (q = 49 ∧ K = 3) ∨ (q = 49 ∧ K = 24) ∨ (q = 51 ∧ K = 1) ∨ (q = 51 ∧ K = 8)
    ∨ (q = 51 ∧ K = 25) ∨ (q = 53 ∧ K = 26) ∨ (q = 55 ∧ K = 2) ∨ (q = 55 ∧ K = 5)
    ∨ (q = 55 ∧ K = 27) ∨ (q = 57 ∧ K = 1) ∨ (q = 57 ∧ K = 9) ∨ (q = 57 ∧ K = 28)
    ∨ (q = 59 ∧ K = 29) ∨ (q = 61 ∧ K = 30) ∨ (q = 63 ∧ K = 1) ∨ (q = 63 ∧ K = 3)
    ∨ (q = 63 ∧ K = 4) ∨ (q = 63 ∧ K = 10) ∨ (q = 63 ∧ K = 31) ∨ (q = 65 ∧ K = 2)
    ∨ (q = 65 ∧ K = 6) ∨ (q = 65 ∧ K = 32) ∨ (q = 67 ∧ K = 33) ∨ (q = 69 ∧ K = 1)
    ∨ (q = 69 ∧ K = 11) ∨ (q = 69 ∧ K = 34) ∨ (q = 71 ∧ K = 35) := by
  obtain ⟨t, ht⟩ := hq_odd
  have hq12 : q = 49 ∨ q = 51 ∨ q = 53 ∨ q = 55 ∨ q = 57 ∨ q = 59 ∨ q = 61 ∨ q = 63
      ∨ q = 65 ∨ q = 67 ∨ q = 69 ∨ q = 71 := by omega
  rcases hq12 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases band5_K_of_q_49 hK1 hdvd with rfl | rfl <;> norm_num
  · rcases band5_K_of_q_51 hK1 hdvd with rfl | rfl | rfl <;> norm_num
  · rcases band5_K_of_q_53 hK1 hdvd with rfl; norm_num
  · rcases band5_K_of_q_55 hK1 hdvd with rfl | rfl | rfl <;> norm_num
  · rcases band5_K_of_q_57 hK1 hdvd with rfl | rfl | rfl <;> norm_num
  · rcases band5_K_of_q_59 hK1 hdvd with rfl; norm_num
  · rcases band5_K_of_q_61 hK1 hdvd with rfl; norm_num
  · rcases band5_K_of_q_63 hK1 hdvd with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · rcases band5_K_of_q_65 hK1 hdvd with rfl | rfl | rfl <;> norm_num
  · rcases band5_K_of_q_67 hK1 hdvd with rfl; norm_num
  · rcases band5_K_of_q_69 hK1 hdvd with rfl | rfl | rfl <;> norm_num
  · rcases band5_K_of_q_71 hK1 hdvd with rfl; norm_num

private theorem band5_K_of_q_73 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 73) :
    K = 36 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨ s = 23 ∨ s = 24 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem band5_K_of_q_75 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 75) :
    K = 1 ∨ K = 2 ∨ K = 7 ∨ K = 12 ∨ K = 37 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨ s = 23 ∨ s = 24 ∨ s = 25 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> omega

private theorem band5_K_of_q_77 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 77) :
    K = 3 ∨ K = 5 ∨ K = 38 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨ s = 23 ∨ s = 24 ∨ s = 25 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> omega

private theorem band5_K_of_q_79 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 79) :
    K = 39 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨ s = 23 ∨ s = 24 ∨ s = 25
      ∨ s = 26 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> omega

private theorem band5_K_of_q_81 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 81) :
    K = 1 ∨ K = 4 ∨ K = 13 ∨ K = 40 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨ s = 23 ∨ s = 24 ∨ s = 25 ∨ s = 26
      ∨ s = 27 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> omega

private theorem band5_K_of_q_83 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 83) :
    K = 41 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨ s = 23 ∨ s = 24 ∨ s = 25 ∨ s = 26
      ∨ s = 27 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> omega

private theorem band5_K_of_q_85 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 85) :
    K = 2 ∨ K = 8 ∨ K = 42 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨ s = 23 ∨ s = 24 ∨ s = 25 ∨ s = 26
      ∨ s = 27 ∨ s = 28 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> omega

private theorem band5_K_of_q_87 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 87) :
    K = 1 ∨ K = 14 ∨ K = 43 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨ s = 23 ∨ s = 24 ∨ s = 25 ∨ s = 26
      ∨ s = 27 ∨ s = 28 ∨ s = 29 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> omega

private theorem band5_K_of_q_89 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 89) :
    K = 44 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨ s = 23 ∨ s = 24 ∨ s = 25 ∨ s = 26
      ∨ s = 27 ∨ s = 28 ∨ s = 29 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> omega

private theorem band5_K_of_q_91 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 91) :
    K = 3 ∨ K = 6 ∨ K = 45 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨ s = 23 ∨ s = 24 ∨ s = 25 ∨ s = 26
      ∨ s = 27 ∨ s = 28 ∨ s = 29 ∨ s = 30 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> omega

private theorem band5_K_of_q_93 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 93) :
    K = 1 ∨ K = 15 ∨ K = 46 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨ s = 23 ∨ s = 24 ∨ s = 25 ∨ s = 26
      ∨ s = 27 ∨ s = 28 ∨ s = 29 ∨ s = 30 ∨ s = 31 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem band5_K_of_q_95 {K : ℕ} (hK1 : 1 ≤ K) (hdvd : 2 * K + 1 ∣ 95) :
    K = 2 ∨ K = 9 ∨ K = 47 := by
  obtain ⟨s, hs⟩ := hdvd
  have h3s := band5_cofactor_le hK1 hs
  have hsd : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8
      ∨ s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17
      ∨ s = 18 ∨ s = 19 ∨ s = 20 ∨ s = 21 ∨ s = 22 ∨ s = 23 ∨ s = 24 ∨ s = 25 ∨ s = 26
      ∨ s = 27 ∨ s = 28 ∨ s = 29 ∨ s = 30 ∨ s = 31 := by omega
  rcases hsd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;> omega

set_option maxHeartbeats 1000000 in
/-- **The band-5 upper-window datum enumeration**: on `72 ≤ q < 96` the divisor pin admits
exactly thirty-one pairs. -/
theorem datum_band5_upper_window_pairs {q K : ℕ} (hq_odd : Odd q) (hK1 : 1 ≤ K)
    (h2K : 2 * K < q) (hdvd : 2 * K + 1 ∣ q) (h72 : 72 ≤ q) (h96 : q < 96) :
    (q = 73 ∧ K = 36) ∨ (q = 75 ∧ K = 1) ∨ (q = 75 ∧ K = 2) ∨ (q = 75 ∧ K = 7)
    ∨ (q = 75 ∧ K = 12) ∨ (q = 75 ∧ K = 37) ∨ (q = 77 ∧ K = 3) ∨ (q = 77 ∧ K = 5)
    ∨ (q = 77 ∧ K = 38) ∨ (q = 79 ∧ K = 39) ∨ (q = 81 ∧ K = 1) ∨ (q = 81 ∧ K = 4)
    ∨ (q = 81 ∧ K = 13) ∨ (q = 81 ∧ K = 40) ∨ (q = 83 ∧ K = 41) ∨ (q = 85 ∧ K = 2)
    ∨ (q = 85 ∧ K = 8) ∨ (q = 85 ∧ K = 42) ∨ (q = 87 ∧ K = 1) ∨ (q = 87 ∧ K = 14)
    ∨ (q = 87 ∧ K = 43) ∨ (q = 89 ∧ K = 44) ∨ (q = 91 ∧ K = 3) ∨ (q = 91 ∧ K = 6)
    ∨ (q = 91 ∧ K = 45) ∨ (q = 93 ∧ K = 1) ∨ (q = 93 ∧ K = 15) ∨ (q = 93 ∧ K = 46)
    ∨ (q = 95 ∧ K = 2) ∨ (q = 95 ∧ K = 9) ∨ (q = 95 ∧ K = 47) := by
  obtain ⟨t, ht⟩ := hq_odd
  have hq12 : q = 73 ∨ q = 75 ∨ q = 77 ∨ q = 79 ∨ q = 81 ∨ q = 83 ∨ q = 85 ∨ q = 87
      ∨ q = 89 ∨ q = 91 ∨ q = 93 ∨ q = 95 := by omega
  rcases hq12 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases band5_K_of_q_73 hK1 hdvd with rfl; norm_num
  · rcases band5_K_of_q_75 hK1 hdvd with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · rcases band5_K_of_q_77 hK1 hdvd with rfl | rfl | rfl <;> norm_num
  · rcases band5_K_of_q_79 hK1 hdvd with rfl; norm_num
  · rcases band5_K_of_q_81 hK1 hdvd with rfl | rfl | rfl | rfl <;> norm_num
  · rcases band5_K_of_q_83 hK1 hdvd with rfl; norm_num
  · rcases band5_K_of_q_85 hK1 hdvd with rfl | rfl | rfl <;> norm_num
  · rcases band5_K_of_q_87 hK1 hdvd with rfl | rfl | rfl <;> norm_num
  · rcases band5_K_of_q_89 hK1 hdvd with rfl; norm_num
  · rcases band5_K_of_q_91 hK1 hdvd with rfl | rfl | rfl <;> norm_num
  · rcases band5_K_of_q_93 hK1 hdvd with rfl | rfl | rfl <;> norm_num
  · rcases band5_K_of_q_95 hK1 hdvd with rfl | rfl | rfl <;> norm_num

/-- **The band-5 datum pair list** (all fifty-eight pin-admissible pairs on
`48 ≤ q < 96`). -/
def Class0Band5DatumPair (ctx : ActualFailureContext) : Prop :=
  ((class1SlopeDatum ctx).q = 49 ∧ (class1SlopeDatum ctx).K₀ = 3)
  ∨ ((class1SlopeDatum ctx).q = 49 ∧ (class1SlopeDatum ctx).K₀ = 24)
  ∨ ((class1SlopeDatum ctx).q = 51 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 51 ∧ (class1SlopeDatum ctx).K₀ = 8)
  ∨ ((class1SlopeDatum ctx).q = 51 ∧ (class1SlopeDatum ctx).K₀ = 25)
  ∨ ((class1SlopeDatum ctx).q = 53 ∧ (class1SlopeDatum ctx).K₀ = 26)
  ∨ ((class1SlopeDatum ctx).q = 55 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 55 ∧ (class1SlopeDatum ctx).K₀ = 5)
  ∨ ((class1SlopeDatum ctx).q = 55 ∧ (class1SlopeDatum ctx).K₀ = 27)
  ∨ ((class1SlopeDatum ctx).q = 57 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 57 ∧ (class1SlopeDatum ctx).K₀ = 9)
  ∨ ((class1SlopeDatum ctx).q = 57 ∧ (class1SlopeDatum ctx).K₀ = 28)
  ∨ ((class1SlopeDatum ctx).q = 59 ∧ (class1SlopeDatum ctx).K₀ = 29)
  ∨ ((class1SlopeDatum ctx).q = 61 ∧ (class1SlopeDatum ctx).K₀ = 30)
  ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 3)
  ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 4)
  ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 10)
  ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 31)
  ∨ ((class1SlopeDatum ctx).q = 65 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 65 ∧ (class1SlopeDatum ctx).K₀ = 6)
  ∨ ((class1SlopeDatum ctx).q = 65 ∧ (class1SlopeDatum ctx).K₀ = 32)
  ∨ ((class1SlopeDatum ctx).q = 67 ∧ (class1SlopeDatum ctx).K₀ = 33)
  ∨ ((class1SlopeDatum ctx).q = 69 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 69 ∧ (class1SlopeDatum ctx).K₀ = 11)
  ∨ ((class1SlopeDatum ctx).q = 69 ∧ (class1SlopeDatum ctx).K₀ = 34)
  ∨ ((class1SlopeDatum ctx).q = 71 ∧ (class1SlopeDatum ctx).K₀ = 35)
  ∨ ((class1SlopeDatum ctx).q = 73 ∧ (class1SlopeDatum ctx).K₀ = 36)
  ∨ ((class1SlopeDatum ctx).q = 75 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 75 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 75 ∧ (class1SlopeDatum ctx).K₀ = 7)
  ∨ ((class1SlopeDatum ctx).q = 75 ∧ (class1SlopeDatum ctx).K₀ = 12)
  ∨ ((class1SlopeDatum ctx).q = 75 ∧ (class1SlopeDatum ctx).K₀ = 37)
  ∨ ((class1SlopeDatum ctx).q = 77 ∧ (class1SlopeDatum ctx).K₀ = 3)
  ∨ ((class1SlopeDatum ctx).q = 77 ∧ (class1SlopeDatum ctx).K₀ = 5)
  ∨ ((class1SlopeDatum ctx).q = 77 ∧ (class1SlopeDatum ctx).K₀ = 38)
  ∨ ((class1SlopeDatum ctx).q = 79 ∧ (class1SlopeDatum ctx).K₀ = 39)
  ∨ ((class1SlopeDatum ctx).q = 81 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 81 ∧ (class1SlopeDatum ctx).K₀ = 4)
  ∨ ((class1SlopeDatum ctx).q = 81 ∧ (class1SlopeDatum ctx).K₀ = 13)
  ∨ ((class1SlopeDatum ctx).q = 81 ∧ (class1SlopeDatum ctx).K₀ = 40)
  ∨ ((class1SlopeDatum ctx).q = 83 ∧ (class1SlopeDatum ctx).K₀ = 41)
  ∨ ((class1SlopeDatum ctx).q = 85 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 85 ∧ (class1SlopeDatum ctx).K₀ = 8)
  ∨ ((class1SlopeDatum ctx).q = 85 ∧ (class1SlopeDatum ctx).K₀ = 42)
  ∨ ((class1SlopeDatum ctx).q = 87 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 87 ∧ (class1SlopeDatum ctx).K₀ = 14)
  ∨ ((class1SlopeDatum ctx).q = 87 ∧ (class1SlopeDatum ctx).K₀ = 43)
  ∨ ((class1SlopeDatum ctx).q = 89 ∧ (class1SlopeDatum ctx).K₀ = 44)
  ∨ ((class1SlopeDatum ctx).q = 91 ∧ (class1SlopeDatum ctx).K₀ = 3)
  ∨ ((class1SlopeDatum ctx).q = 91 ∧ (class1SlopeDatum ctx).K₀ = 6)
  ∨ ((class1SlopeDatum ctx).q = 91 ∧ (class1SlopeDatum ctx).K₀ = 45)
  ∨ ((class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 15)
  ∨ ((class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 46)
  ∨ ((class1SlopeDatum ctx).q = 95 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 95 ∧ (class1SlopeDatum ctx).K₀ = 9)
  ∨ ((class1SlopeDatum ctx).q = 95 ∧ (class1SlopeDatum ctx).K₀ = 47)

set_option maxHeartbeats 1000000 in
/-- **The band-5 window resolution**: every actual ctx on `48 ≤ q < 96` either passes the
window-free check or carries one of the fifty-eight pin-admissible pairs AND has a shallow
value `{1, 3, 5}` provably on its cycle — the wave-5 mirror of the wave-4
`class0_datum_window_resolved`. -/
theorem class0_datum_band5_window_resolved (ctx : ActualFailureContext)
    (h48 : 48 ≤ (class1SlopeDatum ctx).q) (h96 : (class1SlopeDatum ctx).q < 96) :
    Class0CycleDeepBandFree ctx
      ∨ (Class0CycleMeetsShallow ctx ∧ Class0Band5DatumPair ctx) := by
  by_cases hfree : Class0CycleDeepBandFree ctx
  · exact Or.inl hfree
  · refine Or.inr ⟨class0CycleMeetsShallow_of_not_deepBandFree ctx h96 hfree, ?_⟩
    rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 72 with h72 | h72
    · rcases datum_band5_lower_window_pairs (class1SlopeDatum ctx).hq_odd
        (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum_two_K₀_lt ctx)
        (class0_datum_dvd ctx) h48 h72 with
        h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h <;>
      simp [Class0Band5DatumPair, h.1, h.2]
    · rcases datum_band5_upper_window_pairs (class1SlopeDatum ctx).hq_odd
        (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum_two_K₀_lt ctx)
        (class0_datum_dvd ctx) h72 h96 with
        h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h | h | h | h <;>
      simp [Class0Band5DatumPair, h.1, h.2]

/-! ## Part 7.  The successor residual: the survivor residue split

The wave-4 hypothesis pair (`class0Cycle_of_datum_split`) demanded the FULL windowed check
on every survivor pair and on every `48 ≤ q` shell.  The successor demands strictly less:
one congruence miss per survivor pair, the windowed check on `48 ≤ q < 96` only where the
cycle provably meets `{1, 3, 5}`, and the windowed check on `96 ≤ q`. -/

/-- The canonical survivor period, selected by the modulus (the survivor list determines
the period by `q` alone). -/
def class0SurvivorPeriod (q : ℕ) : ℕ :=
  if q = 17 then 4
  else if q = 19 then 9
  else if q = 21 then 2
  else if q = 25 then 10
  else if q = 27 then 9
  else if q = 29 then 14
  else if q = 33 then 5
  else if q = 35 then 5
  else if q = 37 then 18
  else if q = 39 then 4
  else if q = 41 then 10
  else if q = 43 then 7
  else if q = 45 then 5
  else 1

/-- The survivor deep residue (mod the period) of the unique deep cycle position. -/
def class0SurvivorDeepResidue (q K : ℕ) : ℕ :=
  if q = 19 then 6
  else if q = 25 ∧ K = 12 then 8
  else if q = 27 ∧ K = 13 then 7
  else if q = 29 then 10
  else if q = 37 then 10
  else if q = 41 then 8
  else if q = 43 then 6
  else 0

/-- **The wave-5 successor hypothesis on a survivor shell**: every floor-realizing window
start misses the pair's deep cycle residue — one congruence per start, nothing else. -/
def Class0SurvivorResidueMiss (ctx : ActualFailureContext) : Prop :=
  ∀ k ∈ ctx.n24CarryData.starts,
    129 * shellLadderDepth ctx + 64
        ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
    k % class0SurvivorPeriod (class1SlopeDatum ctx).q
      ≠ class0SurvivorDeepResidue (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀

set_option maxHeartbeats 1000000 in
/-- **The survivor residue miss DELIVERS the windowed check** on every survivor pair (the
aggregation of the nineteen per-pair sufficiency directions). -/
theorem class0WindowCycleCheck_of_survivor_residueMiss (ctx : ActualFailureContext)
    (hs : Class0DatumSurvivor ctx) (hmiss : Class0SurvivorResidueMiss ctx) :
    Class0WindowCycleCheck ctx := by
  unfold Class0SurvivorResidueMiss at hmiss
  simp only [Class0DatumSurvivor] at hs
  rcases hs with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact (class0WindowCycleCheck_iff_datum_17_8 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 17 = 4 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 17 8 = 0 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_19_9 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 19 = 9 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 19 9 = 6 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_21_1 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 21 = 2 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 21 1 = 0 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_25_2 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 25 = 10 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 25 2 = 0 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_25_12 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 25 = 10 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 25 12 = 8 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_27_1 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 27 = 9 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 27 1 = 0 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_27_4 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 27 = 9 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 27 4 = 0 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_27_13 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 27 = 9 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 27 13 = 7 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_29_14 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 29 = 14 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 29 14 = 10 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_33_1 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 33 = 5 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 33 1 = 0 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_33_16 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 33 = 5 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 33 16 = 0 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_35_2 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 35 = 5 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 35 2 = 0 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_37_18 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 37 = 18 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 37 18 = 10 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_39_1 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 39 = 4 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 39 1 = 0 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_41_20 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 41 = 10 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 41 20 = 8 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_43_21 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 43 = 7 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 43 21 = 6 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_45_1 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 45 = 5 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 45 1 = 0 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_45_2 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 45 = 5 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 45 2 = 0 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)
  · exact (class0WindowCycleCheck_iff_datum_45_4 ctx h.1 h.2).mpr (fun k hk hfl => by
      have hx := hmiss k hk hfl
      rw [h.1, h.2, show class0SurvivorPeriod 45 = 5 by norm_num [class0SurvivorPeriod],
        show class0SurvivorDeepResidue 45 4 = 0 by norm_num [class0SurvivorDeepResidue]] at hx
      exact hx)

set_option maxHeartbeats 1000000 in
/-- **The windowed check FORCES the survivor residue miss** (the aggregation of the
nineteen per-pair necessity directions): the successor survivor hypothesis is implied by
the wave-4 one — it loses nothing. -/
theorem class0_survivor_residueMiss_of_windowCycleCheck (ctx : ActualFailureContext)
    (hs : Class0DatumSurvivor ctx) (hcheck : Class0WindowCycleCheck ctx) :
    Class0SurvivorResidueMiss ctx := by
  unfold Class0SurvivorResidueMiss
  simp only [Class0DatumSurvivor] at hs
  rcases hs with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 17 = 4 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 17 8 = 0 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_17_8 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 19 = 9 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 19 9 = 6 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_19_9 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 21 = 2 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 21 1 = 0 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_21_1 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 25 = 10 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 25 2 = 0 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_25_2 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 25 = 10 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 25 12 = 8 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_25_12 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 27 = 9 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 27 1 = 0 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_27_1 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 27 = 9 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 27 4 = 0 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_27_4 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 27 = 9 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 27 13 = 7 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_27_13 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 29 = 14 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 29 14 = 10 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_29_14 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 33 = 5 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 33 1 = 0 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_33_1 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 33 = 5 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 33 16 = 0 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_33_16 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 35 = 5 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 35 2 = 0 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_35_2 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 37 = 18 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 37 18 = 10 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_37_18 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 39 = 4 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 39 1 = 0 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_39_1 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 41 = 10 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 41 20 = 8 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_41_20 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 43 = 7 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 43 21 = 6 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_43_21 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 45 = 5 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 45 1 = 0 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_45_1 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 45 = 5 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 45 2 = 0 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_45_2 ctx h.1 h.2).mp hcheck k hk hfl
  · intro k hk hfl
    rw [h.1, h.2, show class0SurvivorPeriod 45 = 5 by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 45 4 = 0 by norm_num [class0SurvivorDeepResidue]]
    exact (class0WindowCycleCheck_iff_datum_45_4 ctx h.1 h.2).mp hcheck k hk hfl

/-- **The per-ctx band-5 split**: on `48 ≤ q`, the windowed check follows from the mid-band
hypothesis (needed only when the cycle meets `{1,3,5}` below `96`) and the `96 ≤ q`
hypothesis — mid-band shells whose cycles avoid `{1,3,5}` close FREE. -/
theorem class0WindowCycleCheck_of_band5_split (ctx : ActualFailureContext)
    (hmid : 48 ≤ (class1SlopeDatum ctx).q → (class1SlopeDatum ctx).q < 96 →
      Class0CycleMeetsShallow ctx → Class0WindowCycleCheck ctx)
    (hbig : 96 ≤ (class1SlopeDatum ctx).q → Class0WindowCycleCheck ctx)
    (h48 : 48 ≤ (class1SlopeDatum ctx).q) :
    Class0WindowCycleCheck ctx := by
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 96 with h96 | h96
  · by_cases hfree : Class0CycleDeepBandFree ctx
    · exact hfree.toWindowCheck
    · exact hmid h48 h96 (class0CycleMeetsShallow_of_not_deepBandFree ctx h96 hfree)
  · exact hbig h96

/-- **The capstone field from the wave-5 survivor residue split** (EXACTLY the
`class0Cycle` field type of `Erdos260CycleResidual`): one congruence miss per survivor
pair, the windowed check on shallow-meeting `48 ≤ q < 96` shells, and the windowed check
on `96 ≤ q` deliver `∀ ctx, Class0WindowCycleCheck ctx`. -/
theorem class0Cycle_of_survivor_residue_split
    (hsurv : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      Class0SurvivorResidueMiss ctx)
    (hmid : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
      (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
      Class0WindowCycleCheck ctx)
    (hbig : ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
      Class0WindowCycleCheck ctx) :
    ∀ ctx : ActualFailureContext, Class0WindowCycleCheck ctx :=
  class0Cycle_of_datum_split
    (fun ctx hsv => class0WindowCycleCheck_of_survivor_residueMiss ctx hsv (hsurv ctx hsv))
    (fun ctx h48 => class0WindowCycleCheck_of_band5_split ctx (hmid ctx) (hbig ctx) h48)

/-- The capstone pinned field from the wave-5 survivor residue split (the wave-2 surface,
verbatim). -/
theorem class0Pinned_field_of_survivor_residue_split
    (hsurv : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      Class0SurvivorResidueMiss ctx)
    (hmid : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
      (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
      Class0WindowCycleCheck ctx)
    (hbig : ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
      Class0WindowCycleCheck ctx) :
    ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_field_of_datum_split
    (fun ctx hsv => class0WindowCycleCheck_of_survivor_residueMiss ctx hsv (hsurv ctx hsv))
    (fun ctx h48 => class0WindowCycleCheck_of_band5_split ctx (hmid ctx) (hbig ctx) h48)

/-- The wave-2 residual from the wave-5 survivor residue split: `Class0FibreEmpty` for
every genuine-route budget. -/
theorem class0FibreEmpty_of_survivor_residue_split
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hroute : ∀ ctx : ActualFailureContext, (budget ctx).route = genuineChargeRoute ctx)
    (hsurv : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      Class0SurvivorResidueMiss ctx)
    (hmid : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
      (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
      Class0WindowCycleCheck ctx)
    (hbig : ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
      Class0WindowCycleCheck ctx) :
    Class0FibreEmpty budget :=
  class0FibreEmpty_of_datum_split budget hroute
    (fun ctx hsv => class0WindowCycleCheck_of_survivor_residueMiss ctx hsv (hsurv ctx hsv))
    (fun ctx h48 => class0WindowCycleCheck_of_band5_split ctx (hmid ctx) (hbig ctx) h48)

/-- **Successor comparison (survivor side)**: the wave-4 survivor hypothesis delivers the
wave-5 one — the successor never demands more. -/
theorem class0_survivorResidueMiss_hypothesis_of_datum_split
    (hold : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      Class0WindowCycleCheck ctx) :
    ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      Class0SurvivorResidueMiss ctx :=
  fun ctx hs => class0_survivor_residueMiss_of_windowCycleCheck ctx hs (hold ctx hs)

/-- **Successor comparison (`48 ≤ q` side)**: the wave-4 big-modulus hypothesis delivers
BOTH wave-5 hypotheses — and the wave-5 pair demands strictly less (mid-band shells with
`{1,3,5}`-free cycles need nothing at all). -/
theorem class0_band5_hypotheses_of_datum_split
    (hold : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
      Class0WindowCycleCheck ctx) :
    (∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
      (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
      Class0WindowCycleCheck ctx)
    ∧ ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
      Class0WindowCycleCheck ctx :=
  ⟨fun ctx h48 _ _ => hold ctx h48, fun ctx h96 => hold ctx (by omega)⟩

/-! ## Part 8.  Machine-readable status (brutally honest) -/

/-- Honest machine-readable status of the wave-5 class-0 survivor residue closure. -/
def chernoffClass0SurvivorClosureStatus : List String :=
  [ "TARGET (wave-4 residual): the class0Cycle_of_datum_split hypothesis pair of " ++
      "ChernoffClass0DatumClosure - the windowed check Class0WindowCycleCheck on the " ++
      "nineteen survivor pairs (Class0DatumSurvivor, all with deep value 1 on-cycle " ++
      "below modulus 48) plus all 48 <= q shells.",
    "CLOSED (generic residue-window levers, NEW): " ++
      "class0WindowCycleCheck_of_residue_avoid - for q < 48, period c <= q, single deep " ++
      "residue rho, the congruence miss k % c != rho at floor-realizing starts yields the " ++
      "windowed check (off-residue representatives are odd, != 1, hence >= 3 and " ++
      "16K >= 48 > q); class0WindowCycleCheck_residue_necessary - the windowed check " ++
      "FORCES the congruence miss whenever the residue representative is deep.",
    "CLOSED (seventeen NEW per-pair residue exploits + exactness, the brief's goal 1): " ++
      "class0Pinned_of_datum_<q>_<K0>_window mirrors of the wave-4 flagships, plus " ++
      "class0WindowCycleCheck_iff_datum_<q>_<K0> for ALL nineteen survivors: the " ++
      "windowed check IS the single congruence miss.  Deep residue table (c, rho; " ++
      "rho = 0 means c | k): (17,8):(4,0) (19,9):(9,6) (21,1):(2,0) (25,2):(10,0) " ++
      "(25,12):(10,8) (27,1):(9,0) (27,4):(9,0) (27,13):(9,7) (29,14):(14,10) " ++
      "(33,1):(5,0) (33,16):(5,0) (35,2):(5,0) (37,18):(18,10) (39,1):(4,0) " ++
      "(41,20):(10,8) (43,21):(7,6) (45,1):(5,0) (45,2):(5,0) (45,4):(5,0).",
    "CONFLICT PROBE OUTCOME (honest, goal 1): NO survivor pair closes outright.  The " ++
      "unconditional window facts - start positivity k >= 1 (n24_starts_pos), shell " ++
      "window membership (cnlMulti_starts_eq_window), the gap ceiling " ++
      "(n24_gapWindow_le_of_start) - exclude no residue class mod c, and the proved " ++
      "pressure floor (chernoffClass0_highExcessStarts_nonempty, via n24_gate_violated) " ++
      "makes floor-realizing starts EXIST at every actual ctx.  The r = 0 top-start pin " ++
      "route (n24_r_eq_zero_of_L_le + single-start structure) fires only vacuously: " ++
      "n24_r_pos / shellLadderDepth_ge_15421 prove r >= 1 and L >= 15421 everywhere - " ++
      "packaged at check type as class0WindowCycleCheck_of_r_eq_zero / " ++
      "class0WindowCycleCheck_of_depth_le.  Every pair is therefore RESIDUE-SHRUNK, " ++
      "none CLOSED.",
    "CLOSED (q in [48, 96) criterion, the brief's goal 2): " ++
      "deepBand_odd_shallow_of_modulus_lt_96 - an odd deep value below 96 is 1, 3 or 5 " ++
      "(K <= q/16 < 6, verified); " ++
      "class0CycleDeepBandFree_of_cycle_avoids_shallow_of_modulus_lt_96 / " ++
      "class0Pinned_of_cycle_avoids_shallow_of_modulus_lt_96 / " ++
      "class0CycleDeepBandFree_of_datum_avoids_shallow - a period avoiding {1,3,5} " ++
      "passes the window-free check on every q < 96 shell; " ++
      "class0CycleMeetsShallow_of_not_deepBandFree - conversely a failing check puts " ++
      "one of 1, 3, 5 ON the cycle (Class0CycleMeetsShallow).",
    "CLOSED (band-5 datum enumerations, goal 2): datum_band5_lower_window_pairs - on " ++
      "48 <= q < 72 the divisor pin (2K0+1) | q admits EXACTLY twenty-seven pairs " ++
      "(49,3),(49,24),(51,1),(51,8),(51,25),(53,26),(55,2),(55,5),(55,27),(57,1)," ++
      "(57,9),(57,28),(59,29),(61,30),(63,1),(63,3),(63,4),(63,10),(63,31),(65,2)," ++
      "(65,6),(65,32),(67,33),(69,1),(69,11),(69,34),(71,35); " ++
      "datum_band5_upper_window_pairs - on 72 <= q < 96 exactly thirty-one: " ++
      "(73,36),(75,1),(75,2),(75,7),(75,12),(75,37),(77,3),(77,5),(77,38),(79,39)," ++
      "(81,1),(81,4),(81,13),(81,40),(83,41),(85,2),(85,8),(85,42),(87,1),(87,14)," ++
      "(87,43),(89,44),(91,3),(91,6),(91,45),(93,1),(93,15),(93,46),(95,2),(95,9)," ++
      "(95,47).  Resolution class0_datum_band5_window_resolved: every 48 <= q < 96 ctx " ++
      "passes the window-free check or carries one of the fifty-eight pairs WITH a " ++
      "shallow value {1,3,5} provably on its cycle.",
    "BRIDGES (the strictly smaller successor, goal 3): " ++
      "class0Cycle_of_survivor_residue_split - the capstone field (verbatim type " ++
      "forall ctx, Class0WindowCycleCheck ctx) from (a) Class0SurvivorResidueMiss on " ++
      "survivors (ONE congruence per floor-realizing start, selectors " ++
      "class0SurvivorPeriod / class0SurvivorDeepResidue), (b) the windowed check on " ++
      "48 <= q < 96 ONLY at shallow-meeting cycles (Class0CycleMeetsShallow), (c) the " ++
      "windowed check on 96 <= q; pinned-field and fibre forms " ++
      "class0Pinned_field_of_survivor_residue_split / " ++
      "class0FibreEmpty_of_survivor_residue_split; per-ctx dichotomy " ++
      "class0WindowCycleCheck_of_band5_split.  Comparisons: " ++
      "class0_survivorResidueMiss_hypothesis_of_datum_split and " ++
      "class0_band5_hypotheses_of_datum_split derive every successor hypothesis from " ++
      "the wave-4 pair (never harder), while mid-band shells with {1,3,5}-free cycles " ++
      "and the explicit residue reductions make the successor strictly smaller; " ++
      "class0WindowCycleCheck_of_survivor_residueMiss / " ++
      "class0_survivor_residueMiss_of_windowCycleCheck prove the survivor leg is " ++
      "EXACTLY equivalent, so the reduction is lossless.",
    "NOT CLOSED (the honest wave-5 residual): the atom itself.  On the nineteen " ++
      "survivor shells the closure now needs exactly one congruence miss per " ++
      "floor-realizing start (k % c != rho per the table) - the pressure floor " ++
      "guarantees such starts exist, and no formalized fact pins their residues; on " ++
      "48 <= q < 96 the windowed check is needed exactly on the (<= 58 pair) shells " ++
      "whose cycles meet {1,3,5}; on 96 <= q the full windowed check remains.  No " ++
      "hitGap <-> canonGap bridge exists at the actual ctx.  We do NOT claim " ++
      "unconditional closure of the atom." ]

theorem chernoffClass0SurvivorClosureStatus_nonempty :
    chernoffClass0SurvivorClosureStatus ≠ [] := by
  simp [chernoffClass0SurvivorClosureStatus]

/-! ## Part 9.  Axiom-cleanliness audit -/

#print axioms class0WindowCycleCheck_of_residue_avoid
#print axioms class0WindowCycleCheck_residue_necessary
#print axioms class0WindowCycleCheck_iff_datum_17_8
#print axioms class0WindowCycleCheck_iff_datum_19_9
#print axioms class0Pinned_of_datum_19_9_window
#print axioms class0WindowCycleCheck_iff_datum_21_1
#print axioms class0WindowCycleCheck_iff_datum_25_2
#print axioms class0Pinned_of_datum_25_2_window
#print axioms class0WindowCycleCheck_iff_datum_25_12
#print axioms class0Pinned_of_datum_25_12_window
#print axioms class0WindowCycleCheck_iff_datum_27_1
#print axioms class0Pinned_of_datum_27_1_window
#print axioms class0WindowCycleCheck_iff_datum_27_4
#print axioms class0Pinned_of_datum_27_4_window
#print axioms class0WindowCycleCheck_iff_datum_27_13
#print axioms class0Pinned_of_datum_27_13_window
#print axioms class0WindowCycleCheck_iff_datum_29_14
#print axioms class0Pinned_of_datum_29_14_window
#print axioms class0WindowCycleCheck_iff_datum_33_1
#print axioms class0Pinned_of_datum_33_1_window
#print axioms class0WindowCycleCheck_iff_datum_33_16
#print axioms class0Pinned_of_datum_33_16_window
#print axioms class0WindowCycleCheck_iff_datum_35_2
#print axioms class0Pinned_of_datum_35_2_window
#print axioms class0WindowCycleCheck_iff_datum_37_18
#print axioms class0Pinned_of_datum_37_18_window
#print axioms class0WindowCycleCheck_iff_datum_39_1
#print axioms class0Pinned_of_datum_39_1_window
#print axioms class0WindowCycleCheck_iff_datum_41_20
#print axioms class0Pinned_of_datum_41_20_window
#print axioms class0WindowCycleCheck_iff_datum_43_21
#print axioms class0Pinned_of_datum_43_21_window
#print axioms class0WindowCycleCheck_iff_datum_45_1
#print axioms class0Pinned_of_datum_45_1_window
#print axioms class0WindowCycleCheck_iff_datum_45_2
#print axioms class0Pinned_of_datum_45_2_window
#print axioms class0WindowCycleCheck_iff_datum_45_4
#print axioms class0Pinned_of_datum_45_4_window
#print axioms class0WindowCycleCheck_of_r_eq_zero
#print axioms class0WindowCycleCheck_of_depth_le
#print axioms deepBand_odd_shallow_of_modulus_lt_96
#print axioms class0CycleDeepBandFree_of_cycle_avoids_shallow_of_modulus_lt_96
#print axioms class0Pinned_of_cycle_avoids_shallow_of_modulus_lt_96
#print axioms class0CycleDeepBandFree_of_datum_avoids_shallow
#print axioms class0CycleMeetsShallow_of_not_deepBandFree
#print axioms datum_band5_lower_window_pairs
#print axioms datum_band5_upper_window_pairs
#print axioms class0_datum_band5_window_resolved
#print axioms class0WindowCycleCheck_of_survivor_residueMiss
#print axioms class0_survivor_residueMiss_of_windowCycleCheck
#print axioms class0WindowCycleCheck_of_band5_split
#print axioms class0Cycle_of_survivor_residue_split
#print axioms class0Pinned_field_of_survivor_residue_split
#print axioms class0FibreEmpty_of_survivor_residue_split
#print axioms class0_survivorResidueMiss_hypothesis_of_datum_split
#print axioms class0_band5_hypotheses_of_datum_split
#print axioms chernoffClass0SurvivorClosureStatus_nonempty

end

end Erdos260
