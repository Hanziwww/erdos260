import Erdos260.ModulusTailCriteria
import Erdos260.SurvivorKeyCount

/-!
# The mechanical finite tails: the b2-heavy joint congruences, the class-1
# divisor-pin sweep to `q < 200`, and the run/densepack band sweeps on `64 <= q < 128`
# (`FiniteTailsSweep`)

This module (NEW; it edits no existing file) sweeps the mechanical finite instances
left open after wave 14 (item 4 of the post-wave-14 open set).

## Part 1 - the fourteen b2-heavy class-0 survivors (`Class0SurvivorB2HeavyRest`)

Per pair the dossier is: the certified orbit period `c` from index `1` (which EQUALS
the wave-5 class-0 survivor period `class0SurvivorPeriod q` at all fourteen pairs),
the band-2 residue set of the cycle, and the class-0 deep residue
`(c, rho) = (class0SurvivorPeriod q, class0SurvivorDeepResidue q K0)`.  THE VERDICT:
at ALL FOURTEEN pairs the two congruences CONFLICT - the deep slot of the cycle
(the class-0 residue the windowed check must miss) reads band `>= 5`, never band `2`,
so no class-4 fibre member can sit in the class-0 bad residue class
(`ftHeavyConflict_<q>_<K0>`, dispatcher `ftHeavyConflict_dispatch`).  Consequence:
the joint demand DECOMPOSES - `Class0SurvivorResidueMiss` is equivalent to its
restriction to starts OFF the class-4 fibre (`ftClass0ResidueMiss_iff_offFibre`).
Honest: this closes the cross-demand only; the residue miss off the fibre and the
window-ones content remain open.  `(39,1)` is the unique b2-heavy pair with a UNIQUE
band-2 residue: the lcm spacing closes the `W <= 4` regime outright
(`ftKeyInj_of_datum_39_1`), and the member-EVEN parity pin empties the val-0 fibre
part at `Q` odd (`ftVal0Empty_of_datum_39_1`).

## Part 2 - the class-1 deep tail pushed from `q < 100` to `q < 200`

For every divisor-pin pair (`2*K0 + 1 | q`, odd `101 <= q < 200`; 136 pairs) the
orbit cycle is computed.  49 pairs have BAND-4-FREE cycles - each closes the class-1
routed fibre outright (`ftClass1Fibre_empty_of_datum_<q>_<K0>`).  EIGHT new moduli
have ALL pins band-4-free: `{109, 113, 123, 127, 129, 151, 157, 171}` - the
extension of the wave-3 `class1ClosedModuli` (`ftClass1ClosedModuli200`,
per-modulus closures, dispatcher `ftClass1Fibre_empty_of_mem_extended`).  STRUCTURAL
FINDING (honest): every on-cycle numerator is ODD (the step `2^g*K - q` is odd for
odd `q`), so the wave-5 'band 4 with odd numerator' refinement is vacuous on-cycle -
there are NO even-only-band-4 pairs; the 87 remaining pairs genuinely read band 4
and survive.  THE EXCEPTIONAL-COFACTOR CROSS of the wave-6 order criteria: among the
87 survivors EXACTLY TWO have their order cofactor `orbitOrderModulus` in the
Mersenne small-order family - `(105,7)` (cofactor 15) and `(155,15)` (cofactor 31)
(`ftSurvivor_105_7_exceptional`, `ftSurvivor_155_15_exceptional`); all other
survivors have cofactor order `>= 12`, where the order-floor pruning of
`ModulusTailCriteria` is live.  Bridge: `ftClass1Deep_split_at_200` rebuilds the
`Class1PairResidual.deep` field shape VERBATIM from the swept part.

## Part 3 - the run/densepack tails on `64 <= q < 128`

Same treatment for the 80 divisor-pin pairs of odd `64 <= q < 128`.  RUN lane
(band-`{1,4}`-free cycles): EXACTLY ONE pair closes - `(93,15)` (cycle `[27,15]`,
bands `2,3`); band 1 is on-cycle everywhere else (`ftRunCloses_of_datum_93_15`,
generic closer `ftClass5CycleNumeric_of_cycle_band_free`).  DENSEPACK lane
(band-3-free cycles): NINETEEN pairs close (`ftClass3Band3Free_of_datum_<q>_<K0>`,
aggregate `FtDensePackBand3FreeDatum`).  Dispatchers `ftRunSettlement_split_at_128`
/ `ftDensePackStartsEmpty_split_at_128` rebuild `RunCycleNumericSettlementHyp` and
`Class3StartsEmpty` VERBATIM with the mid-band demand relieved of the closed pairs.

## Part 4 - the per-lane sweep record

Machine-readable closed/surviving lists per lane and the honest status
`finiteTailsSweepStatus`.

No `sorry`, no `admit`, no new `axiom`, no `native_decide` (`decide` only on small
closed numeric/list/divisor goals); additive only - no existing module is edited.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Part 0.  Helpers -/

/-- lcm of positives is positive (local copy of the wave-14 helper). -/
private theorem ftLcmPos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : 0 < Nat.lcm a b := by
  rcases Nat.eq_zero_or_pos (Nat.lcm a b) with h0 | hp
  · exfalso
    have hdvd : Nat.lcm a b ∣ a * b :=
      Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a)
    rw [h0] at hdvd
    have hab : a * b = 0 := zero_dvd_iff.mp hdvd
    have hpos : 0 < a * b := Nat.mul_pos ha hb
    omega
  · exact hp

/-! ## Part 1.  The fourteen b2-heavy class-0 survivor pairs: per-pair dossiers and
the joint-congruence conflict -/

/-- `(19,9)`: cycle `[17, 15, 11, 3, 5, 1, 13, 7, 9]` (period `9` = `class0SurvivorPeriod 19`), band-2
residues `[5, 8, 9]`, deep slot `6` (value `1`, band `5`) - not band-2. -/
private theorem ftHC_19_9 :
    slopeOrbit 19 9 (1 + 9) = slopeOrbit 19 9 1
      ∧ canonGap 19 (slopeOrbit 19 9 6) ≠ 2 := by
  have e0 : slopeOrbit 19 9 0 = 9 := rfl
  have e1 : slopeOrbit 19 9 1 = 17 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 19 9 2 = 15 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 19 9 3 = 11 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 19 9 4 = 3 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 19 9 5 = 5 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 19 9 6 = 1 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 19 9 7 = 13 :=
    slopeOrbit_step_eval 6 4 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 19 9 8 = 7 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 19 9 9 = 9 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 19 9 10 = 17 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 19 9 10 = slopeOrbit 19 9 1
    rw [e10, e1]
  · rw [e6, canonGap_eval (q := 19) (v := 1) (g := 4) (by norm_num) (by norm_num) (by norm_num)]
    decide

/-- **Joint-congruence conflict at `(19,9)`**: every class-4 fibre member misses the
class-0 deep residue `6` mod `9` - the band-2 congruence and the class-0 bad
residue are jointly unsatisfiable. -/
theorem ftHeavyConflict_19_9 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 19) (hK : (class1SlopeDatum ctx).K₀ = 9) :
    ∀ k ∈ olcFibre ctx, k % 9 ≠ 6 := by
  intro k hk hmod
  have hk1 : 1 ≤ k := olcFibre_mem_pos ctx hk
  have hband2 : canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
    rw [olcFibre_def] at hk
    exact class4Fibre_canonGap_eq ctx hk
  rw [hq, hK] at hband2
  have hres : slopeOrbit 19 9 k = slopeOrbit 19 9 ((k - 1) % 9 + 1) :=
    slopeOrbit_eq_residue (c := 9) (by norm_num)
      (slopeOrbit_period_of_return ftHC_19_9.1) hk1
  have hpos : (k - 1) % 9 + 1 = 6 := by omega
  rw [hres, hpos] at hband2
  exact ftHC_19_9.2 hband2

/-- `(25,2)`: cycle `[7, 3, 23, 21, 17, 9, 11, 19, 13, 1]` (period `10` = `class0SurvivorPeriod 25`), band-2
residues `[1, 6, 7]`, deep slot `10` (value `1`, band `5`) - not band-2. -/
private theorem ftHC_25_2 :
    slopeOrbit 25 2 (1 + 10) = slopeOrbit 25 2 1
      ∧ canonGap 25 (slopeOrbit 25 2 10) ≠ 2 := by
  have e0 : slopeOrbit 25 2 0 = 2 := rfl
  have e1 : slopeOrbit 25 2 1 = 7 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 25 2 2 = 3 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 25 2 3 = 23 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 25 2 4 = 21 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 25 2 5 = 17 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 25 2 6 = 9 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 25 2 7 = 11 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 25 2 8 = 19 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 25 2 9 = 13 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 25 2 10 = 1 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 25 2 11 = 7 :=
    slopeOrbit_step_eval 10 4 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 25 2 11 = slopeOrbit 25 2 1
    rw [e11, e1]
  · rw [e10, canonGap_eval (q := 25) (v := 1) (g := 4) (by norm_num) (by norm_num) (by norm_num)]
    decide

/-- **Joint-congruence conflict at `(25,2)`**: every class-4 fibre member misses the
class-0 deep residue `0` mod `10` - the band-2 congruence and the class-0 bad
residue are jointly unsatisfiable. -/
theorem ftHeavyConflict_25_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    ∀ k ∈ olcFibre ctx, k % 10 ≠ 0 := by
  intro k hk hmod
  have hk1 : 1 ≤ k := olcFibre_mem_pos ctx hk
  have hband2 : canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
    rw [olcFibre_def] at hk
    exact class4Fibre_canonGap_eq ctx hk
  rw [hq, hK] at hband2
  have hres : slopeOrbit 25 2 k = slopeOrbit 25 2 ((k - 1) % 10 + 1) :=
    slopeOrbit_eq_residue (c := 10) (by norm_num)
      (slopeOrbit_period_of_return ftHC_25_2.1) hk1
  have hpos : (k - 1) % 10 + 1 = 10 := by omega
  rw [hres, hpos] at hband2
  exact ftHC_25_2.2 hband2

/-- `(25,12)`: cycle `[23, 21, 17, 9, 11, 19, 13, 1, 7, 3]` (period `10` = `class0SurvivorPeriod 25`), band-2
residues `[4, 5, 9]`, deep slot `8` (value `1`, band `5`) - not band-2. -/
private theorem ftHC_25_12 :
    slopeOrbit 25 12 (1 + 10) = slopeOrbit 25 12 1
      ∧ canonGap 25 (slopeOrbit 25 12 8) ≠ 2 := by
  have e0 : slopeOrbit 25 12 0 = 12 := rfl
  have e1 : slopeOrbit 25 12 1 = 23 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 25 12 2 = 21 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 25 12 3 = 17 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 25 12 4 = 9 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 25 12 5 = 11 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 25 12 6 = 19 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 25 12 7 = 13 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 25 12 8 = 1 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 25 12 9 = 7 :=
    slopeOrbit_step_eval 8 4 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 25 12 10 = 3 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 25 12 11 = 23 :=
    slopeOrbit_step_eval 10 3 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 25 12 11 = slopeOrbit 25 12 1
    rw [e11, e1]
  · rw [e8, canonGap_eval (q := 25) (v := 1) (g := 4) (by norm_num) (by norm_num) (by norm_num)]
    decide

/-- **Joint-congruence conflict at `(25,12)`**: every class-4 fibre member misses the
class-0 deep residue `8` mod `10` - the band-2 congruence and the class-0 bad
residue are jointly unsatisfiable. -/
theorem ftHeavyConflict_25_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 12) :
    ∀ k ∈ olcFibre ctx, k % 10 ≠ 8 := by
  intro k hk hmod
  have hk1 : 1 ≤ k := olcFibre_mem_pos ctx hk
  have hband2 : canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
    rw [olcFibre_def] at hk
    exact class4Fibre_canonGap_eq ctx hk
  rw [hq, hK] at hband2
  have hres : slopeOrbit 25 12 k = slopeOrbit 25 12 ((k - 1) % 10 + 1) :=
    slopeOrbit_eq_residue (c := 10) (by norm_num)
      (slopeOrbit_period_of_return ftHC_25_12.1) hk1
  have hpos : (k - 1) % 10 + 1 = 8 := by omega
  rw [hres, hpos] at hband2
  exact ftHC_25_12.2 hband2

/-- `(27,1)`: cycle `[5, 13, 25, 23, 19, 11, 17, 7, 1]` (period `9` = `class0SurvivorPeriod 27`), band-2
residues `[2, 6, 8]`, deep slot `9` (value `1`, band `5`) - not band-2. -/
private theorem ftHC_27_1 :
    slopeOrbit 27 1 (1 + 9) = slopeOrbit 27 1 1
      ∧ canonGap 27 (slopeOrbit 27 1 9) ≠ 2 := by
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
  · rw [e9, canonGap_eval (q := 27) (v := 1) (g := 4) (by norm_num) (by norm_num) (by norm_num)]
    decide

/-- **Joint-congruence conflict at `(27,1)`**: every class-4 fibre member misses the
class-0 deep residue `0` mod `9` - the band-2 congruence and the class-0 bad
residue are jointly unsatisfiable. -/
theorem ftHeavyConflict_27_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ∀ k ∈ olcFibre ctx, k % 9 ≠ 0 := by
  intro k hk hmod
  have hk1 : 1 ≤ k := olcFibre_mem_pos ctx hk
  have hband2 : canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
    rw [olcFibre_def] at hk
    exact class4Fibre_canonGap_eq ctx hk
  rw [hq, hK] at hband2
  have hres : slopeOrbit 27 1 k = slopeOrbit 27 1 ((k - 1) % 9 + 1) :=
    slopeOrbit_eq_residue (c := 9) (by norm_num)
      (slopeOrbit_period_of_return ftHC_27_1.1) hk1
  have hpos : (k - 1) % 9 + 1 = 9 := by omega
  rw [hres, hpos] at hband2
  exact ftHC_27_1.2 hband2

/-- `(27,4)`: cycle `[5, 13, 25, 23, 19, 11, 17, 7, 1]` (period `9` = `class0SurvivorPeriod 27`), band-2
residues `[2, 6, 8]`, deep slot `9` (value `1`, band `5`) - not band-2. -/
private theorem ftHC_27_4 :
    slopeOrbit 27 4 (1 + 9) = slopeOrbit 27 4 1
      ∧ canonGap 27 (slopeOrbit 27 4 9) ≠ 2 := by
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
  · rw [e9, canonGap_eval (q := 27) (v := 1) (g := 4) (by norm_num) (by norm_num) (by norm_num)]
    decide

/-- **Joint-congruence conflict at `(27,4)`**: every class-4 fibre member misses the
class-0 deep residue `0` mod `9` - the band-2 congruence and the class-0 bad
residue are jointly unsatisfiable. -/
theorem ftHeavyConflict_27_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    ∀ k ∈ olcFibre ctx, k % 9 ≠ 0 := by
  intro k hk hmod
  have hk1 : 1 ≤ k := olcFibre_mem_pos ctx hk
  have hband2 : canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
    rw [olcFibre_def] at hk
    exact class4Fibre_canonGap_eq ctx hk
  rw [hq, hK] at hband2
  have hres : slopeOrbit 27 4 k = slopeOrbit 27 4 ((k - 1) % 9 + 1) :=
    slopeOrbit_eq_residue (c := 9) (by norm_num)
      (slopeOrbit_period_of_return ftHC_27_4.1) hk1
  have hpos : (k - 1) % 9 + 1 = 9 := by omega
  rw [hres, hpos] at hband2
  exact ftHC_27_4.2 hband2

/-- `(27,13)`: cycle `[25, 23, 19, 11, 17, 7, 1, 5, 13]` (period `9` = `class0SurvivorPeriod 27`), band-2
residues `[4, 6, 9]`, deep slot `7` (value `1`, band `5`) - not band-2. -/
private theorem ftHC_27_13 :
    slopeOrbit 27 13 (1 + 9) = slopeOrbit 27 13 1
      ∧ canonGap 27 (slopeOrbit 27 13 7) ≠ 2 := by
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
  · rw [e7, canonGap_eval (q := 27) (v := 1) (g := 4) (by norm_num) (by norm_num) (by norm_num)]
    decide

/-- **Joint-congruence conflict at `(27,13)`**: every class-4 fibre member misses the
class-0 deep residue `7` mod `9` - the band-2 congruence and the class-0 bad
residue are jointly unsatisfiable. -/
theorem ftHeavyConflict_27_13 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 13) :
    ∀ k ∈ olcFibre ctx, k % 9 ≠ 7 := by
  intro k hk hmod
  have hk1 : 1 ≤ k := olcFibre_mem_pos ctx hk
  have hband2 : canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
    rw [olcFibre_def] at hk
    exact class4Fibre_canonGap_eq ctx hk
  rw [hq, hK] at hband2
  have hres : slopeOrbit 27 13 k = slopeOrbit 27 13 ((k - 1) % 9 + 1) :=
    slopeOrbit_eq_residue (c := 9) (by norm_num)
      (slopeOrbit_period_of_return ftHC_27_13.1) hk1
  have hpos : (k - 1) % 9 + 1 = 7 := by omega
  rw [hres, hpos] at hband2
  exact ftHC_27_13.2 hband2

/-- `(29,14)`: cycle `[27, 25, 21, 13, 23, 17, 5, 11, 15, 1, 3, 19, 9, 7]` (period `14` = `class0SurvivorPeriod 29`), band-2
residues `[4, 8, 13]`, deep slot `10` (value `1`, band `5`) - not band-2. -/
private theorem ftHC_29_14 :
    slopeOrbit 29 14 (1 + 14) = slopeOrbit 29 14 1
      ∧ canonGap 29 (slopeOrbit 29 14 10) ≠ 2 := by
  have e0 : slopeOrbit 29 14 0 = 14 := rfl
  have e1 : slopeOrbit 29 14 1 = 27 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 29 14 2 = 25 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 29 14 3 = 21 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 29 14 4 = 13 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 29 14 5 = 23 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 29 14 6 = 17 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 29 14 7 = 5 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 29 14 8 = 11 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 29 14 9 = 15 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 29 14 10 = 1 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 29 14 11 = 3 :=
    slopeOrbit_step_eval 10 4 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 29 14 12 = 19 :=
    slopeOrbit_step_eval 11 3 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 29 14 13 = 9 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 29 14 14 = 7 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 29 14 15 = 27 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 29 14 15 = slopeOrbit 29 14 1
    rw [e15, e1]
  · rw [e10, canonGap_eval (q := 29) (v := 1) (g := 4) (by norm_num) (by norm_num) (by norm_num)]
    decide

/-- **Joint-congruence conflict at `(29,14)`**: every class-4 fibre member misses the
class-0 deep residue `10` mod `14` - the band-2 congruence and the class-0 bad
residue are jointly unsatisfiable. -/
theorem ftHeavyConflict_29_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 29) (hK : (class1SlopeDatum ctx).K₀ = 14) :
    ∀ k ∈ olcFibre ctx, k % 14 ≠ 10 := by
  intro k hk hmod
  have hk1 : 1 ≤ k := olcFibre_mem_pos ctx hk
  have hband2 : canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
    rw [olcFibre_def] at hk
    exact class4Fibre_canonGap_eq ctx hk
  rw [hq, hK] at hband2
  have hres : slopeOrbit 29 14 k = slopeOrbit 29 14 ((k - 1) % 14 + 1) :=
    slopeOrbit_eq_residue (c := 14) (by norm_num)
      (slopeOrbit_period_of_return ftHC_29_14.1) hk1
  have hpos : (k - 1) % 14 + 1 = 10 := by omega
  rw [hres, hpos] at hband2
  exact ftHC_29_14.2 hband2

/-- `(35,2)`: cycle `[29, 23, 11, 9, 1]` (period `5` = `class0SurvivorPeriod 35`), band-2
residues `[3, 4]`, deep slot `5` (value `1`, band `6`) - not band-2. -/
private theorem ftHC_35_2 :
    slopeOrbit 35 2 (1 + 5) = slopeOrbit 35 2 1
      ∧ canonGap 35 (slopeOrbit 35 2 5) ≠ 2 := by
  have e0 : slopeOrbit 35 2 0 = 2 := rfl
  have e1 : slopeOrbit 35 2 1 = 29 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 35 2 2 = 23 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 35 2 3 = 11 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 35 2 4 = 9 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 35 2 5 = 1 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 35 2 6 = 29 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 35 2 6 = slopeOrbit 35 2 1
    rw [e6, e1]
  · rw [e5, canonGap_eval (q := 35) (v := 1) (g := 5) (by norm_num) (by norm_num) (by norm_num)]
    decide

/-- **Joint-congruence conflict at `(35,2)`**: every class-4 fibre member misses the
class-0 deep residue `0` mod `5` - the band-2 congruence and the class-0 bad
residue are jointly unsatisfiable. -/
theorem ftHeavyConflict_35_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    ∀ k ∈ olcFibre ctx, k % 5 ≠ 0 := by
  intro k hk hmod
  have hk1 : 1 ≤ k := olcFibre_mem_pos ctx hk
  have hband2 : canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
    rw [olcFibre_def] at hk
    exact class4Fibre_canonGap_eq ctx hk
  rw [hq, hK] at hband2
  have hres : slopeOrbit 35 2 k = slopeOrbit 35 2 ((k - 1) % 5 + 1) :=
    slopeOrbit_eq_residue (c := 5) (by norm_num)
      (slopeOrbit_period_of_return ftHC_35_2.1) hk1
  have hpos : (k - 1) % 5 + 1 = 5 := by omega
  rw [hres, hpos] at hband2
  exact ftHC_35_2.2 hband2

/-- `(37,18)`: cycle `[35, 33, 29, 21, 5, 3, 11, 7, 19, 1, 27, 17, 31, 25, 13, 15, 23, 9]` (period `18` = `class0SurvivorPeriod 37`), band-2
residues `[7, 12, 15, 16]`, deep slot `10` (value `1`, band `6`) - not band-2. -/
private theorem ftHC_37_18 :
    slopeOrbit 37 18 (1 + 18) = slopeOrbit 37 18 1
      ∧ canonGap 37 (slopeOrbit 37 18 10) ≠ 2 := by
  have e0 : slopeOrbit 37 18 0 = 18 := rfl
  have e1 : slopeOrbit 37 18 1 = 35 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 37 18 2 = 33 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 37 18 3 = 29 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 37 18 4 = 21 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 37 18 5 = 5 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 37 18 6 = 3 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 37 18 7 = 11 :=
    slopeOrbit_step_eval 6 3 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 37 18 8 = 7 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 37 18 9 = 19 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 37 18 10 = 1 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 37 18 11 = 27 :=
    slopeOrbit_step_eval 10 5 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 37 18 12 = 17 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 37 18 13 = 31 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 37 18 14 = 25 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 37 18 15 = 13 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 37 18 16 = 15 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 37 18 17 = 23 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 37 18 18 = 9 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 37 18 19 = 35 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 37 18 19 = slopeOrbit 37 18 1
    rw [e19, e1]
  · rw [e10, canonGap_eval (q := 37) (v := 1) (g := 5) (by norm_num) (by norm_num) (by norm_num)]
    decide

/-- **Joint-congruence conflict at `(37,18)`**: every class-4 fibre member misses the
class-0 deep residue `10` mod `18` - the band-2 congruence and the class-0 bad
residue are jointly unsatisfiable. -/
theorem ftHeavyConflict_37_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 37) (hK : (class1SlopeDatum ctx).K₀ = 18) :
    ∀ k ∈ olcFibre ctx, k % 18 ≠ 10 := by
  intro k hk hmod
  have hk1 : 1 ≤ k := olcFibre_mem_pos ctx hk
  have hband2 : canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
    rw [olcFibre_def] at hk
    exact class4Fibre_canonGap_eq ctx hk
  rw [hq, hK] at hband2
  have hres : slopeOrbit 37 18 k = slopeOrbit 37 18 ((k - 1) % 18 + 1) :=
    slopeOrbit_eq_residue (c := 18) (by norm_num)
      (slopeOrbit_period_of_return ftHC_37_18.1) hk1
  have hpos : (k - 1) % 18 + 1 = 10 := by omega
  rw [hres, hpos] at hband2
  exact ftHC_37_18.2 hband2

/-- `(39,1)`: cycle `[25, 11, 5, 1]` (period `4` = `class0SurvivorPeriod 39`), band-2
residues `[2]`, deep slot `4` (value `1`, band `6`) - not band-2.  Unique band-2 residue. -/
private theorem ftHC_39_1 :
    slopeOrbit 39 1 (1 + 4) = slopeOrbit 39 1 1
      ∧ canonGap 39 (slopeOrbit 39 1 4) ≠ 2
      ∧ (∀ j, 1 ≤ j → j ≤ 4 → canonGap 39 (slopeOrbit 39 1 j) = 2 → j = 2) := by
  have e0 : slopeOrbit 39 1 0 = 1 := rfl
  have e1 : slopeOrbit 39 1 1 = 25 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 39 1 2 = 11 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 39 1 3 = 5 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 39 1 4 = 1 :=
    slopeOrbit_step_eval 3 2 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 39 1 5 = 25 :=
    slopeOrbit_step_eval 4 5 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · show slopeOrbit 39 1 5 = slopeOrbit 39 1 1
    rw [e5, e1]
  · rw [e4, canonGap_eval (q := 39) (v := 1) (g := 5) (by norm_num) (by norm_num) (by norm_num)]
    decide
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 39) (v := 25) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 39) (v := 11) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 39) (v := 5) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 39) (v := 1) (g := 5) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- **Joint-congruence conflict at `(39,1)`**: every class-4 fibre member misses the
class-0 deep residue `0` mod `4` - the band-2 congruence and the class-0 bad
residue are jointly unsatisfiable. -/
theorem ftHeavyConflict_39_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ∀ k ∈ olcFibre ctx, k % 4 ≠ 0 := by
  intro k hk hmod
  have hk1 : 1 ≤ k := olcFibre_mem_pos ctx hk
  have hband2 : canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
    rw [olcFibre_def] at hk
    exact class4Fibre_canonGap_eq ctx hk
  rw [hq, hK] at hband2
  have hres : slopeOrbit 39 1 k = slopeOrbit 39 1 ((k - 1) % 4 + 1) :=
    slopeOrbit_eq_residue (c := 4) (by norm_num)
      (slopeOrbit_period_of_return ftHC_39_1.1) hk1
  have hpos : (k - 1) % 4 + 1 = 4 := by omega
  rw [hres, hpos] at hband2
  exact ftHC_39_1.2.1 hband2

/-- `(43,21)`: cycle `[41, 39, 35, 27, 11, 1, 21]` (period `7` = `class0SurvivorPeriod 43`), band-2
residues `[5, 7]`, deep slot `6` (value `1`, band `6`) - not band-2. -/
private theorem ftHC_43_21 :
    slopeOrbit 43 21 (1 + 7) = slopeOrbit 43 21 1
      ∧ canonGap 43 (slopeOrbit 43 21 6) ≠ 2 := by
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
  · rw [e6, canonGap_eval (q := 43) (v := 1) (g := 5) (by norm_num) (by norm_num) (by norm_num)]
    decide

/-- **Joint-congruence conflict at `(43,21)`**: every class-4 fibre member misses the
class-0 deep residue `6` mod `7` - the band-2 congruence and the class-0 bad
residue are jointly unsatisfiable. -/
theorem ftHeavyConflict_43_21 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 43) (hK : (class1SlopeDatum ctx).K₀ = 21) :
    ∀ k ∈ olcFibre ctx, k % 7 ≠ 6 := by
  intro k hk hmod
  have hk1 : 1 ≤ k := olcFibre_mem_pos ctx hk
  have hband2 : canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
    rw [olcFibre_def] at hk
    exact class4Fibre_canonGap_eq ctx hk
  rw [hq, hK] at hband2
  have hres : slopeOrbit 43 21 k = slopeOrbit 43 21 ((k - 1) % 7 + 1) :=
    slopeOrbit_eq_residue (c := 7) (by norm_num)
      (slopeOrbit_period_of_return ftHC_43_21.1) hk1
  have hpos : (k - 1) % 7 + 1 = 6 := by omega
  rw [hres, hpos] at hband2
  exact ftHC_43_21.2 hband2

/-- `(45,1)`: cycle `[19, 31, 17, 23, 1]` (period `5` = `class0SurvivorPeriod 45`), band-2
residues `[1, 3]`, deep slot `5` (value `1`, band `6`) - not band-2. -/
private theorem ftHC_45_1 :
    slopeOrbit 45 1 (1 + 5) = slopeOrbit 45 1 1
      ∧ canonGap 45 (slopeOrbit 45 1 5) ≠ 2 := by
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
  · rw [e5, canonGap_eval (q := 45) (v := 1) (g := 5) (by norm_num) (by norm_num) (by norm_num)]
    decide

/-- **Joint-congruence conflict at `(45,1)`**: every class-4 fibre member misses the
class-0 deep residue `0` mod `5` - the band-2 congruence and the class-0 bad
residue are jointly unsatisfiable. -/
theorem ftHeavyConflict_45_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ∀ k ∈ olcFibre ctx, k % 5 ≠ 0 := by
  intro k hk hmod
  have hk1 : 1 ≤ k := olcFibre_mem_pos ctx hk
  have hband2 : canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
    rw [olcFibre_def] at hk
    exact class4Fibre_canonGap_eq ctx hk
  rw [hq, hK] at hband2
  have hres : slopeOrbit 45 1 k = slopeOrbit 45 1 ((k - 1) % 5 + 1) :=
    slopeOrbit_eq_residue (c := 5) (by norm_num)
      (slopeOrbit_period_of_return ftHC_45_1.1) hk1
  have hpos : (k - 1) % 5 + 1 = 5 := by omega
  rw [hres, hpos] at hband2
  exact ftHC_45_1.2 hband2

/-- `(45,2)`: cycle `[19, 31, 17, 23, 1]` (period `5` = `class0SurvivorPeriod 45`), band-2
residues `[1, 3]`, deep slot `5` (value `1`, band `6`) - not band-2. -/
private theorem ftHC_45_2 :
    slopeOrbit 45 2 (1 + 5) = slopeOrbit 45 2 1
      ∧ canonGap 45 (slopeOrbit 45 2 5) ≠ 2 := by
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
  · rw [e5, canonGap_eval (q := 45) (v := 1) (g := 5) (by norm_num) (by norm_num) (by norm_num)]
    decide

/-- **Joint-congruence conflict at `(45,2)`**: every class-4 fibre member misses the
class-0 deep residue `0` mod `5` - the band-2 congruence and the class-0 bad
residue are jointly unsatisfiable. -/
theorem ftHeavyConflict_45_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    ∀ k ∈ olcFibre ctx, k % 5 ≠ 0 := by
  intro k hk hmod
  have hk1 : 1 ≤ k := olcFibre_mem_pos ctx hk
  have hband2 : canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
    rw [olcFibre_def] at hk
    exact class4Fibre_canonGap_eq ctx hk
  rw [hq, hK] at hband2
  have hres : slopeOrbit 45 2 k = slopeOrbit 45 2 ((k - 1) % 5 + 1) :=
    slopeOrbit_eq_residue (c := 5) (by norm_num)
      (slopeOrbit_period_of_return ftHC_45_2.1) hk1
  have hpos : (k - 1) % 5 + 1 = 5 := by omega
  rw [hres, hpos] at hband2
  exact ftHC_45_2.2 hband2

/-- `(45,4)`: cycle `[19, 31, 17, 23, 1]` (period `5` = `class0SurvivorPeriod 45`), band-2
residues `[1, 3]`, deep slot `5` (value `1`, band `6`) - not band-2. -/
private theorem ftHC_45_4 :
    slopeOrbit 45 4 (1 + 5) = slopeOrbit 45 4 1
      ∧ canonGap 45 (slopeOrbit 45 4 5) ≠ 2 := by
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
  · rw [e5, canonGap_eval (q := 45) (v := 1) (g := 5) (by norm_num) (by norm_num) (by norm_num)]
    decide

/-- **Joint-congruence conflict at `(45,4)`**: every class-4 fibre member misses the
class-0 deep residue `0` mod `5` - the band-2 congruence and the class-0 bad
residue are jointly unsatisfiable. -/
theorem ftHeavyConflict_45_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    ∀ k ∈ olcFibre ctx, k % 5 ≠ 0 := by
  intro k hk hmod
  have hk1 : 1 ≤ k := olcFibre_mem_pos ctx hk
  have hband2 : canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
    rw [olcFibre_def] at hk
    exact class4Fibre_canonGap_eq ctx hk
  rw [hq, hK] at hband2
  have hres : slopeOrbit 45 4 k = slopeOrbit 45 4 ((k - 1) % 5 + 1) :=
    slopeOrbit_eq_residue (c := 5) (by norm_num)
      (slopeOrbit_period_of_return ftHC_45_4.1) hk1
  have hpos : (k - 1) % 5 + 1 = 5 := by omega
  rw [hres, hpos] at hband2
  exact ftHC_45_4.2 hband2

/-- **THE FOURTEEN-PAIR CONFLICT DISPATCHER**: at every b2-heavy class-0 survivor pair,
every class-4 fibre member automatically satisfies the class-0 survivor residue miss -
the class-0 windowed congruence and the class-4 band-2 congruence are jointly
unsatisfiable at ALL fourteen pairs. -/
theorem ftHeavyConflict_dispatch (ctx : ActualFailureContext)
    (h : Class0SurvivorB2HeavyRest ctx) :
    ∀ k ∈ olcFibre ctx,
      k % class0SurvivorPeriod (class1SlopeDatum ctx).q
        ≠ class0SurvivorDeepResidue (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ := by
  rcases h with ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩
  · rw [hq, hK,
      show class0SurvivorPeriod 19 = 9 from by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 19 9 = 6 from by
        norm_num [class0SurvivorDeepResidue]]
    exact ftHeavyConflict_19_9 ctx hq hK
  · rw [hq, hK,
      show class0SurvivorPeriod 25 = 10 from by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 25 2 = 0 from by
        norm_num [class0SurvivorDeepResidue]]
    exact ftHeavyConflict_25_2 ctx hq hK
  · rw [hq, hK,
      show class0SurvivorPeriod 25 = 10 from by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 25 12 = 8 from by
        norm_num [class0SurvivorDeepResidue]]
    exact ftHeavyConflict_25_12 ctx hq hK
  · rw [hq, hK,
      show class0SurvivorPeriod 27 = 9 from by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 27 1 = 0 from by
        norm_num [class0SurvivorDeepResidue]]
    exact ftHeavyConflict_27_1 ctx hq hK
  · rw [hq, hK,
      show class0SurvivorPeriod 27 = 9 from by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 27 4 = 0 from by
        norm_num [class0SurvivorDeepResidue]]
    exact ftHeavyConflict_27_4 ctx hq hK
  · rw [hq, hK,
      show class0SurvivorPeriod 27 = 9 from by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 27 13 = 7 from by
        norm_num [class0SurvivorDeepResidue]]
    exact ftHeavyConflict_27_13 ctx hq hK
  · rw [hq, hK,
      show class0SurvivorPeriod 29 = 14 from by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 29 14 = 10 from by
        norm_num [class0SurvivorDeepResidue]]
    exact ftHeavyConflict_29_14 ctx hq hK
  · rw [hq, hK,
      show class0SurvivorPeriod 35 = 5 from by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 35 2 = 0 from by
        norm_num [class0SurvivorDeepResidue]]
    exact ftHeavyConflict_35_2 ctx hq hK
  · rw [hq, hK,
      show class0SurvivorPeriod 37 = 18 from by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 37 18 = 10 from by
        norm_num [class0SurvivorDeepResidue]]
    exact ftHeavyConflict_37_18 ctx hq hK
  · rw [hq, hK,
      show class0SurvivorPeriod 39 = 4 from by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 39 1 = 0 from by
        norm_num [class0SurvivorDeepResidue]]
    exact ftHeavyConflict_39_1 ctx hq hK
  · rw [hq, hK,
      show class0SurvivorPeriod 43 = 7 from by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 43 21 = 6 from by
        norm_num [class0SurvivorDeepResidue]]
    exact ftHeavyConflict_43_21 ctx hq hK
  · rw [hq, hK,
      show class0SurvivorPeriod 45 = 5 from by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 45 1 = 0 from by
        norm_num [class0SurvivorDeepResidue]]
    exact ftHeavyConflict_45_1 ctx hq hK
  · rw [hq, hK,
      show class0SurvivorPeriod 45 = 5 from by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 45 2 = 0 from by
        norm_num [class0SurvivorDeepResidue]]
    exact ftHeavyConflict_45_2 ctx hq hK
  · rw [hq, hK,
      show class0SurvivorPeriod 45 = 5 from by norm_num [class0SurvivorPeriod],
      show class0SurvivorDeepResidue 45 4 = 0 from by
        norm_num [class0SurvivorDeepResidue]]
    exact ftHeavyConflict_45_4 ctx hq hK

/-- **The joint-demand decomposition (sufficiency)**: on a b2-heavy survivor pair the
class-0 survivor residue miss follows from its restriction to floor-realizing starts
OFF the class-4 fibre - the on-fibre part is free by the fourteen conflicts. -/
theorem ftClass0ResidueMiss_of_offFibre (ctx : ActualFailureContext)
    (h : Class0SurvivorB2HeavyRest ctx)
    (hoff : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      k ∉ olcFibre ctx →
      k % class0SurvivorPeriod (class1SlopeDatum ctx).q
        ≠ class0SurvivorDeepResidue (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀) :
    Class0SurvivorResidueMiss ctx := by
  intro k hk hfl
  by_cases hmem : k ∈ olcFibre ctx
  · exact ftHeavyConflict_dispatch ctx h k hmem
  · exact hoff k hk hfl hmem

/-- **The joint-demand decomposition (exact)**: on a b2-heavy survivor pair the class-0
survivor residue miss IS its off-fibre restriction. -/
theorem ftClass0ResidueMiss_iff_offFibre (ctx : ActualFailureContext)
    (h : Class0SurvivorB2HeavyRest ctx) :
    Class0SurvivorResidueMiss ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k ∉ olcFibre ctx →
          k % class0SurvivorPeriod (class1SlopeDatum ctx).q
            ≠ class0SurvivorDeepResidue (class1SlopeDatum ctx).q
                (class1SlopeDatum ctx).K₀ :=
  ⟨fun hmiss k hk hfl _ => hmiss k hk hfl, ftClass0ResidueMiss_of_offFibre ctx h⟩

/-! ### The `(39,1)` regime closures: the unique-band-2 lcm spacing and the parity pin -/

/-- **The `(39,1)` window-regime closure**: on shells with window width `W <= 4` the
lcm spacing (`lcm(2^v, 4) >= 4`) forces every slice of the self-referential key to a
singleton, hence the FULL key injectivity `ReturnKeyInjOn` - the per-regime closure of
the unique b2-heavy unique-band-2 pair. -/
theorem ftKeyInj_of_datum_39_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hW : (supportShell ctx.shell.d ctx.shell.X).card ≤ 4) :
    ReturnKeyInjOn ctx := by
  apply keyInjOn_of_slices_le_one
  intro y
  rcases Finset.eq_empty_or_nonempty (olcSlice ctx (returnSelfRefKey ctx) y) with
    hy | ⟨x, hx⟩
  · rw [hy, Finset.card_empty]
    norm_num
  · have hb := sliceCard_le_of_band2_unique ctx (c := 4) (j₀ := 2) (by norm_num)
      (by rw [hq, hK]; exact slopeOrbit_period_of_return ftHC_39_1.1)
      (by rw [hq, hK]; exact ftHC_39_1.2.2) hx
    have hpos : 0 < Nat.lcm (2 ^ carryVal2 ctx x) 4 :=
      ftLcmPos (pow_pos (by norm_num) _) (by norm_num)
    have hge : 4 ≤ Nat.lcm (2 ^ carryVal2 ctx x) 4 :=
      Nat.le_of_dvd hpos (Nat.dvd_lcm_right _ _)
    have hdiv : ((supportShell ctx.shell.d ctx.shell.X).card
        + Nat.lcm (2 ^ carryVal2 ctx x) 4 - 1) / Nat.lcm (2 ^ carryVal2 ctx x) 4 < 2 :=
      (Nat.div_lt_iff_lt_mul hpos).mpr (by omega)
    omega

/-- **The `(39,1)` parity pin**: at `Q` odd the val-0 part of the class-4 fibre is EMPTY
(member-EVEN parity, re-exported from the wave-12/14 machinery at this pair). -/
theorem ftVal0Empty_of_datum_39_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hQodd : ctx.Q % 2 = 1) :
    (olcFibre ctx).filter (fun k => carryVal2 ctx k = 0) = ∅ :=
  olcFibre_val0_empty_of_parityEvenDatum ctx hQodd (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩)))

/-- **The `(39,1)` slice valuation floor**: at `Q` odd every slice member has
`carryVal2 >= 1`, so the slice spacing modulus is `lcm(2^v, 4) >= 4` with `v >= 1`. -/
theorem ftSliceValPos_of_datum_39_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hQodd : ctx.Q % 2 = 1) {y k : ℕ}
    (hk : k ∈ olcSlice ctx (returnSelfRefKey ctx) y) :
    1 ≤ carryVal2 ctx k :=
  slice_member_val_pos_of_parityEvenDatum ctx hQodd
    (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩))) hk

/-! ## Part 2.  The class-1 divisor-pin sweep: odd `101 <= q < 200`

49 of the 136 divisor-pin pairs have band-4-free cycles and close the class-1 routed
fibre outright; eight moduli close completely. -/

/-- `(105,1)`: cycle `[23, 79, 53, 1]` (period `4`, bands `3, 1, 1, 7`) - band-4-free. -/
private theorem ftC1_105_1 :
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
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 105) (v := 23) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 105) (v := 79) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 105) (v := 53) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 105) (v := 1) (g := 6) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(105,1)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_105_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_105_1.1 ftC1_105_1.2

/-- `(105,2)`: cycle `[23, 79, 53, 1]` (period `4`, bands `3, 1, 1, 7`) - band-4-free. -/
private theorem ftC1_105_2 :
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
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 105) (v := 23) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 105) (v := 79) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 105) (v := 53) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 105) (v := 1) (g := 6) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(105,2)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_105_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_105_2.1 ftC1_105_2.2

/-- `(105,3)`: cycle `[87, 69, 33, 27, 3]` (period `5`, bands `1, 1, 2, 2, 6`) - band-4-free. -/
private theorem ftC1_105_3 :
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
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 105) (v := 87) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 105) (v := 69) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 105) (v := 33) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 105) (v := 27) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 105) (v := 3) (g := 5) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(105,3)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_105_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_105_3.1 ftC1_105_3.2

/-- `(105,10)`: cycle `[55, 5]` (period `2`, bands `1, 5`) - band-4-free. -/
private theorem ftC1_105_10 :
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
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 105) (v := 55) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 105) (v := 5) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(105,10)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_105_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_105_10.1 ftC1_105_10.2

/-- `(105,17)`: cycle `[31, 19, 47, 83, 61, 17]` (period `6`, bands `2, 3, 2, 1, 1, 3`) - band-4-free. -/
private theorem ftC1_105_17 :
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
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 105) (v := 31) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 105) (v := 19) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 105) (v := 47) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 105) (v := 83) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 105) (v := 61) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 105) (v := 17) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(105,17)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_105_17 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 17) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_105_17.1 ftC1_105_17.2

/-- `(109,54)`: cycle `[107, 105, 101, 93, 77, 45, 71, 33, 23, 75, 41, 55, 1, 19, 43, 63, 17, 27]` (period `18`, bands `1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 7, 3, 2, 1, 3, 3`) - band-4-free. -/
private theorem ftC1_109_54 :
    slopeOrbit 109 54 (1 + 18) = slopeOrbit 109 54 1
      ∧ ∀ j, 1 ≤ j → j ≤ 18 → canonGap 109 (slopeOrbit 109 54 j) ≠ 4 := by
  have e0 : slopeOrbit 109 54 0 = 54 := rfl
  have e1 : slopeOrbit 109 54 1 = 107 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 109 54 2 = 105 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 109 54 3 = 101 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 109 54 4 = 93 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 109 54 5 = 77 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 109 54 6 = 45 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 109 54 7 = 71 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 109 54 8 = 33 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 109 54 9 = 23 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 109 54 10 = 75 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 109 54 11 = 41 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 109 54 12 = 55 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 109 54 13 = 1 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 109 54 14 = 19 :=
    slopeOrbit_step_eval 13 6 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 109 54 15 = 43 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 109 54 16 = 63 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 109 54 17 = 17 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 109 54 18 = 27 :=
    slopeOrbit_step_eval 17 2 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 109 54 19 = 107 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 109 54 19 = slopeOrbit 109 54 1
    rw [e19, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 109) (v := 107) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 109) (v := 105) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 109) (v := 101) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 109) (v := 93) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 109) (v := 77) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 109) (v := 45) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 109) (v := 71) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 109) (v := 33) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 109) (v := 23) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 109) (v := 75) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e11, canonGap_eval (q := 109) (v := 41) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e12, canonGap_eval (q := 109) (v := 55) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e13, canonGap_eval (q := 109) (v := 1) (g := 6) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e14, canonGap_eval (q := 109) (v := 19) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e15, canonGap_eval (q := 109) (v := 43) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e16, canonGap_eval (q := 109) (v := 63) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e17, canonGap_eval (q := 109) (v := 17) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e18, canonGap_eval (q := 109) (v := 27) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(109,54)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_109_54 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 109) (hK : (class1SlopeDatum ctx).K₀ = 54) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_109_54.1 ftC1_109_54.2

/-- `(113,56)`: cycle `[111, 109, 105, 97, 81, 49, 83, 53, 99, 85, 57, 1, 15, 7]` (period `14`, bands `1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 5`) - band-4-free. -/
private theorem ftC1_113_56 :
    slopeOrbit 113 56 (1 + 14) = slopeOrbit 113 56 1
      ∧ ∀ j, 1 ≤ j → j ≤ 14 → canonGap 113 (slopeOrbit 113 56 j) ≠ 4 := by
  have e0 : slopeOrbit 113 56 0 = 56 := rfl
  have e1 : slopeOrbit 113 56 1 = 111 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 113 56 2 = 109 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 113 56 3 = 105 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 113 56 4 = 97 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 113 56 5 = 81 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 113 56 6 = 49 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 113 56 7 = 83 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 113 56 8 = 53 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 113 56 9 = 99 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 113 56 10 = 85 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 113 56 11 = 57 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 113 56 12 = 1 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 113 56 13 = 15 :=
    slopeOrbit_step_eval 12 6 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 113 56 14 = 7 :=
    slopeOrbit_step_eval 13 2 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 113 56 15 = 111 :=
    slopeOrbit_step_eval 14 4 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 113 56 15 = slopeOrbit 113 56 1
    rw [e15, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 113) (v := 111) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 113) (v := 109) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 113) (v := 105) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 113) (v := 97) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 113) (v := 81) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 113) (v := 49) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 113) (v := 83) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 113) (v := 53) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 113) (v := 99) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 113) (v := 85) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e11, canonGap_eval (q := 113) (v := 57) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e12, canonGap_eval (q := 113) (v := 1) (g := 6) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e13, canonGap_eval (q := 113) (v := 15) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e14, canonGap_eval (q := 113) (v := 7) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(113,56)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_113_56 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 113) (hK : (class1SlopeDatum ctx).K₀ = 56) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_113_56.1 ftC1_113_56.2

/-- `(117,6)`: cycle `[75, 33, 15, 3]` (period `4`, bands `1, 2, 3, 6`) - band-4-free. -/
private theorem ftC1_117_6 :
    slopeOrbit 117 6 (1 + 4) = slopeOrbit 117 6 1
      ∧ ∀ j, 1 ≤ j → j ≤ 4 → canonGap 117 (slopeOrbit 117 6 j) ≠ 4 := by
  have e0 : slopeOrbit 117 6 0 = 6 := rfl
  have e1 : slopeOrbit 117 6 1 = 75 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 117 6 2 = 33 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 117 6 3 = 15 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 117 6 4 = 3 :=
    slopeOrbit_step_eval 3 2 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 117 6 5 = 75 :=
    slopeOrbit_step_eval 4 5 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 117 6 5 = slopeOrbit 117 6 1
    rw [e5, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 117) (v := 75) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 117) (v := 33) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 117) (v := 15) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 117) (v := 3) (g := 5) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(117,6)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_117_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 117) (hK : (class1SlopeDatum ctx).K₀ = 6) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_117_6.1 ftC1_117_6.2

/-- `(117,19)`: cycle `[35, 23, 67, 17, 19]` (period `5`, bands `2, 3, 1, 3, 3`) - band-4-free. -/
private theorem ftC1_117_19 :
    slopeOrbit 117 19 (1 + 5) = slopeOrbit 117 19 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 117 (slopeOrbit 117 19 j) ≠ 4 := by
  have e0 : slopeOrbit 117 19 0 = 19 := rfl
  have e1 : slopeOrbit 117 19 1 = 35 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 117 19 2 = 23 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 117 19 3 = 67 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 117 19 4 = 17 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 117 19 5 = 19 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 117 19 6 = 35 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 117 19 6 = slopeOrbit 117 19 1
    rw [e6, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 117) (v := 35) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 117) (v := 23) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 117) (v := 67) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 117) (v := 17) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 117) (v := 19) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(117,19)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_117_19 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 117) (hK : (class1SlopeDatum ctx).K₀ = 19) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_117_19.1 ftC1_117_19.2

/-- `(117,58)`: cycle `[115, 113, 109, 101, 85, 53, 95, 73, 29]` (period `9`, bands `1, 1, 1, 1, 1, 2, 1, 1, 3`) - band-4-free. -/
private theorem ftC1_117_58 :
    slopeOrbit 117 58 (1 + 9) = slopeOrbit 117 58 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 → canonGap 117 (slopeOrbit 117 58 j) ≠ 4 := by
  have e0 : slopeOrbit 117 58 0 = 58 := rfl
  have e1 : slopeOrbit 117 58 1 = 115 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 117 58 2 = 113 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 117 58 3 = 109 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 117 58 4 = 101 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 117 58 5 = 85 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 117 58 6 = 53 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 117 58 7 = 95 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 117 58 8 = 73 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 117 58 9 = 29 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 117 58 10 = 115 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 117 58 10 = slopeOrbit 117 58 1
    rw [e10, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 117) (v := 115) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 117) (v := 113) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 117) (v := 109) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 117) (v := 101) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 117) (v := 85) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 117) (v := 53) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 117) (v := 95) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 117) (v := 73) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 117) (v := 29) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(117,58)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_117_58 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 117) (hK : (class1SlopeDatum ctx).K₀ = 58) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_117_58.1 ftC1_117_58.2

/-- `(119,3)`: cycle `[73, 27, 97, 75, 31, 5, 41, 45, 61, 3]` (period `10`, bands `1, 3, 1, 1, 2, 5, 2, 2, 1, 6`) - band-4-free. -/
private theorem ftC1_119_3 :
    slopeOrbit 119 3 (1 + 10) = slopeOrbit 119 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 10 → canonGap 119 (slopeOrbit 119 3 j) ≠ 4 := by
  have e0 : slopeOrbit 119 3 0 = 3 := rfl
  have e1 : slopeOrbit 119 3 1 = 73 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 119 3 2 = 27 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 119 3 3 = 97 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 119 3 4 = 75 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 119 3 5 = 31 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 119 3 6 = 5 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 119 3 7 = 41 :=
    slopeOrbit_step_eval 6 4 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 119 3 8 = 45 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 119 3 9 = 61 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 119 3 10 = 3 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 119 3 11 = 73 :=
    slopeOrbit_step_eval 10 5 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 119 3 11 = slopeOrbit 119 3 1
    rw [e11, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 119) (v := 73) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 119) (v := 27) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 119) (v := 97) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 119) (v := 75) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 119) (v := 31) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 119) (v := 5) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 119) (v := 41) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 119) (v := 45) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 119) (v := 61) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 119) (v := 3) (g := 5) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(119,3)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_119_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 119) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_119_3.1 ftC1_119_3.2

/-- `(123,1)`: cycle `[5, 37, 25, 77, 31, 1]` (period `6`, bands `5, 2, 3, 1, 2, 7`) - band-4-free. -/
private theorem ftC1_123_1 :
    slopeOrbit 123 1 (1 + 6) = slopeOrbit 123 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 123 (slopeOrbit 123 1 j) ≠ 4 := by
  have e0 : slopeOrbit 123 1 0 = 1 := rfl
  have e1 : slopeOrbit 123 1 1 = 5 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 123 1 2 = 37 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 123 1 3 = 25 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 123 1 4 = 77 :=
    slopeOrbit_step_eval 3 2 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 123 1 5 = 31 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 123 1 6 = 1 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 123 1 7 = 5 :=
    slopeOrbit_step_eval 6 6 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 123 1 7 = slopeOrbit 123 1 1
    rw [e7, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 123) (v := 5) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 123) (v := 37) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 123) (v := 25) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 123) (v := 77) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 123) (v := 31) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 123) (v := 1) (g := 6) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(123,1)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_123_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 123) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_123_1.1 ftC1_123_1.2

/-- `(123,20)`: cycle `[37, 25, 77, 31, 1, 5]` (period `6`, bands `2, 3, 1, 2, 7, 5`) - band-4-free. -/
private theorem ftC1_123_20 :
    slopeOrbit 123 20 (1 + 6) = slopeOrbit 123 20 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 123 (slopeOrbit 123 20 j) ≠ 4 := by
  have e0 : slopeOrbit 123 20 0 = 20 := rfl
  have e1 : slopeOrbit 123 20 1 = 37 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 123 20 2 = 25 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 123 20 3 = 77 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 123 20 4 = 31 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 123 20 5 = 1 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 123 20 6 = 5 :=
    slopeOrbit_step_eval 5 6 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 123 20 7 = 37 :=
    slopeOrbit_step_eval 6 4 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 123 20 7 = slopeOrbit 123 20 1
    rw [e7, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 123) (v := 37) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 123) (v := 25) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 123) (v := 77) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 123) (v := 31) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 123) (v := 1) (g := 6) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 123) (v := 5) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(123,20)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_123_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 123) (hK : (class1SlopeDatum ctx).K₀ = 20) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_123_20.1 ftC1_123_20.2

/-- `(123,61)`: cycle `[121, 119, 115, 107, 91, 59, 113, 103, 83, 43, 49, 73, 23, 61]` (period `14`, bands `1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 2`) - band-4-free. -/
private theorem ftC1_123_61 :
    slopeOrbit 123 61 (1 + 14) = slopeOrbit 123 61 1
      ∧ ∀ j, 1 ≤ j → j ≤ 14 → canonGap 123 (slopeOrbit 123 61 j) ≠ 4 := by
  have e0 : slopeOrbit 123 61 0 = 61 := rfl
  have e1 : slopeOrbit 123 61 1 = 121 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 123 61 2 = 119 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 123 61 3 = 115 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 123 61 4 = 107 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 123 61 5 = 91 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 123 61 6 = 59 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 123 61 7 = 113 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 123 61 8 = 103 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 123 61 9 = 83 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 123 61 10 = 43 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 123 61 11 = 49 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 123 61 12 = 73 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 123 61 13 = 23 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 123 61 14 = 61 :=
    slopeOrbit_step_eval 13 2 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 123 61 15 = 121 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 123 61 15 = slopeOrbit 123 61 1
    rw [e15, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 123) (v := 121) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 123) (v := 119) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 123) (v := 115) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 123) (v := 107) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 123) (v := 91) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 123) (v := 59) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 123) (v := 113) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 123) (v := 103) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 123) (v := 83) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 123) (v := 43) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e11, canonGap_eval (q := 123) (v := 49) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e12, canonGap_eval (q := 123) (v := 73) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e13, canonGap_eval (q := 123) (v := 23) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e14, canonGap_eval (q := 123) (v := 61) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(123,61)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_123_61 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 123) (hK : (class1SlopeDatum ctx).K₀ = 61) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_123_61.1 ftC1_123_61.2

/-- `(127,63)`: cycle `[125, 123, 119, 111, 95, 63]` (period `6`, bands `1, 1, 1, 1, 1, 2`) - band-4-free. -/
private theorem ftC1_127_63 :
    slopeOrbit 127 63 (1 + 6) = slopeOrbit 127 63 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 127 (slopeOrbit 127 63 j) ≠ 4 := by
  have e0 : slopeOrbit 127 63 0 = 63 := rfl
  have e1 : slopeOrbit 127 63 1 = 125 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 127 63 2 = 123 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 127 63 3 = 119 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 127 63 4 = 111 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 127 63 5 = 95 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 127 63 6 = 63 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 127 63 7 = 125 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 127 63 7 = slopeOrbit 127 63 1
    rw [e7, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 127) (v := 125) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 127) (v := 123) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 127) (v := 119) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 127) (v := 111) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 127) (v := 95) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 127) (v := 63) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(127,63)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_127_63 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 127) (hK : (class1SlopeDatum ctx).K₀ = 63) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_127_63.1 ftC1_127_63.2

/-- `(129,1)`: cycle `[127, 125, 121, 113, 97, 65, 1]` (period `7`, bands `1, 1, 1, 1, 1, 1, 8`) - band-4-free. -/
private theorem ftC1_129_1 :
    slopeOrbit 129 1 (1 + 7) = slopeOrbit 129 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 → canonGap 129 (slopeOrbit 129 1 j) ≠ 4 := by
  have e0 : slopeOrbit 129 1 0 = 1 := rfl
  have e1 : slopeOrbit 129 1 1 = 127 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 129 1 2 = 125 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 129 1 3 = 121 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 129 1 4 = 113 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 129 1 5 = 97 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 129 1 6 = 65 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 129 1 7 = 1 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 129 1 8 = 127 :=
    slopeOrbit_step_eval 7 7 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 129 1 8 = slopeOrbit 129 1 1
    rw [e8, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 129) (v := 127) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 129) (v := 125) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 129) (v := 121) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 129) (v := 113) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 129) (v := 97) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 129) (v := 65) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 129) (v := 1) (g := 7) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(129,1)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_129_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 129) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_129_1.1 ftC1_129_1.2

/-- `(129,21)`: cycle `[39, 27, 87, 45, 51, 75, 21]` (period `7`, bands `2, 3, 1, 2, 2, 1, 3`) - band-4-free. -/
private theorem ftC1_129_21 :
    slopeOrbit 129 21 (1 + 7) = slopeOrbit 129 21 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 → canonGap 129 (slopeOrbit 129 21 j) ≠ 4 := by
  have e0 : slopeOrbit 129 21 0 = 21 := rfl
  have e1 : slopeOrbit 129 21 1 = 39 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 129 21 2 = 27 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 129 21 3 = 87 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 129 21 4 = 45 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 129 21 5 = 51 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 129 21 6 = 75 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 129 21 7 = 21 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 129 21 8 = 39 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 129 21 8 = slopeOrbit 129 21 1
    rw [e8, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 129) (v := 39) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 129) (v := 27) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 129) (v := 87) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 129) (v := 45) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 129) (v := 51) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 129) (v := 75) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 129) (v := 21) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(129,21)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_129_21 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 129) (hK : (class1SlopeDatum ctx).K₀ = 21) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_129_21.1 ftC1_129_21.2

/-- `(129,64)`: cycle `[127, 125, 121, 113, 97, 65, 1]` (period `7`, bands `1, 1, 1, 1, 1, 1, 8`) - band-4-free. -/
private theorem ftC1_129_64 :
    slopeOrbit 129 64 (1 + 7) = slopeOrbit 129 64 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 → canonGap 129 (slopeOrbit 129 64 j) ≠ 4 := by
  have e0 : slopeOrbit 129 64 0 = 64 := rfl
  have e1 : slopeOrbit 129 64 1 = 127 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 129 64 2 = 125 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 129 64 3 = 121 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 129 64 4 = 113 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 129 64 5 = 97 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 129 64 6 = 65 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 129 64 7 = 1 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 129 64 8 = 127 :=
    slopeOrbit_step_eval 7 7 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 129 64 8 = slopeOrbit 129 64 1
    rw [e8, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 129) (v := 127) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 129) (v := 125) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 129) (v := 121) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 129) (v := 113) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 129) (v := 97) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 129) (v := 65) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 129) (v := 1) (g := 7) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(129,64)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_129_64 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 129) (hK : (class1SlopeDatum ctx).K₀ = 64) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_129_64.1 ftC1_129_64.2

/-- `(133,66)`: cycle `[131, 129, 125, 117, 101, 69, 5, 27, 83, 33]` (period `10`, bands `1, 1, 1, 1, 1, 1, 5, 3, 1, 3`) - band-4-free. -/
private theorem ftC1_133_66 :
    slopeOrbit 133 66 (1 + 10) = slopeOrbit 133 66 1
      ∧ ∀ j, 1 ≤ j → j ≤ 10 → canonGap 133 (slopeOrbit 133 66 j) ≠ 4 := by
  have e0 : slopeOrbit 133 66 0 = 66 := rfl
  have e1 : slopeOrbit 133 66 1 = 131 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 133 66 2 = 129 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 133 66 3 = 125 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 133 66 4 = 117 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 133 66 5 = 101 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 133 66 6 = 69 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 133 66 7 = 5 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 133 66 8 = 27 :=
    slopeOrbit_step_eval 7 4 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 133 66 9 = 83 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 133 66 10 = 33 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 133 66 11 = 131 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 133 66 11 = slopeOrbit 133 66 1
    rw [e11, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 133) (v := 131) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 133) (v := 129) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 133) (v := 125) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 133) (v := 117) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 133) (v := 101) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 133) (v := 69) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 133) (v := 5) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 133) (v := 27) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 133) (v := 83) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 133) (v := 33) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(133,66)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_133_66 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 133) (hK : (class1SlopeDatum ctx).K₀ = 66) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_133_66.1 ftC1_133_66.2

/-- `(135,1)`: cycle `[121, 107, 79, 23, 49, 61, 109, 83, 31, 113, 91, 47, 53, 77, 19, 17, 1]` (period `17`, bands `1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 8`) - band-4-free. -/
private theorem ftC1_135_1 :
    slopeOrbit 135 1 (1 + 17) = slopeOrbit 135 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 17 → canonGap 135 (slopeOrbit 135 1 j) ≠ 4 := by
  have e0 : slopeOrbit 135 1 0 = 1 := rfl
  have e1 : slopeOrbit 135 1 1 = 121 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 135 1 2 = 107 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 135 1 3 = 79 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 135 1 4 = 23 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 135 1 5 = 49 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 135 1 6 = 61 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 135 1 7 = 109 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 135 1 8 = 83 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 135 1 9 = 31 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 135 1 10 = 113 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 135 1 11 = 91 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 135 1 12 = 47 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 135 1 13 = 53 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 135 1 14 = 77 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 135 1 15 = 19 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 135 1 16 = 17 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 135 1 17 = 1 :=
    slopeOrbit_step_eval 16 2 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 135 1 18 = 121 :=
    slopeOrbit_step_eval 17 7 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 135 1 18 = slopeOrbit 135 1 1
    rw [e18, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 135) (v := 121) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 135) (v := 107) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 135) (v := 79) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 135) (v := 23) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 135) (v := 49) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 135) (v := 61) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 135) (v := 109) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 135) (v := 83) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 135) (v := 31) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 135) (v := 113) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e11, canonGap_eval (q := 135) (v := 91) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e12, canonGap_eval (q := 135) (v := 47) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e13, canonGap_eval (q := 135) (v := 53) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e14, canonGap_eval (q := 135) (v := 77) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e15, canonGap_eval (q := 135) (v := 19) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e16, canonGap_eval (q := 135) (v := 17) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e17, canonGap_eval (q := 135) (v := 1) (g := 7) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(135,1)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_135_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 135) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_135_1.1 ftC1_135_1.2

/-- `(135,2)`: cycle `[121, 107, 79, 23, 49, 61, 109, 83, 31, 113, 91, 47, 53, 77, 19, 17, 1]` (period `17`, bands `1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 8`) - band-4-free. -/
private theorem ftC1_135_2 :
    slopeOrbit 135 2 (1 + 17) = slopeOrbit 135 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 17 → canonGap 135 (slopeOrbit 135 2 j) ≠ 4 := by
  have e0 : slopeOrbit 135 2 0 = 2 := rfl
  have e1 : slopeOrbit 135 2 1 = 121 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 135 2 2 = 107 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 135 2 3 = 79 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 135 2 4 = 23 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 135 2 5 = 49 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 135 2 6 = 61 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 135 2 7 = 109 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 135 2 8 = 83 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 135 2 9 = 31 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 135 2 10 = 113 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 135 2 11 = 91 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 135 2 12 = 47 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 135 2 13 = 53 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 135 2 14 = 77 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 135 2 15 = 19 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 135 2 16 = 17 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 135 2 17 = 1 :=
    slopeOrbit_step_eval 16 2 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 135 2 18 = 121 :=
    slopeOrbit_step_eval 17 7 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 135 2 18 = slopeOrbit 135 2 1
    rw [e18, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 135) (v := 121) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 135) (v := 107) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 135) (v := 79) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 135) (v := 23) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 135) (v := 49) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 135) (v := 61) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 135) (v := 109) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 135) (v := 83) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 135) (v := 31) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 135) (v := 113) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e11, canonGap_eval (q := 135) (v := 91) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e12, canonGap_eval (q := 135) (v := 47) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e13, canonGap_eval (q := 135) (v := 53) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e14, canonGap_eval (q := 135) (v := 77) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e15, canonGap_eval (q := 135) (v := 19) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e16, canonGap_eval (q := 135) (v := 17) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e17, canonGap_eval (q := 135) (v := 1) (g := 7) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(135,2)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_135_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 135) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_135_2.1 ftC1_135_2.2

/-- `(135,4)`: cycle `[121, 107, 79, 23, 49, 61, 109, 83, 31, 113, 91, 47, 53, 77, 19, 17, 1]` (period `17`, bands `1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 8`) - band-4-free. -/
private theorem ftC1_135_4 :
    slopeOrbit 135 4 (1 + 17) = slopeOrbit 135 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 17 → canonGap 135 (slopeOrbit 135 4 j) ≠ 4 := by
  have e0 : slopeOrbit 135 4 0 = 4 := rfl
  have e1 : slopeOrbit 135 4 1 = 121 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 135 4 2 = 107 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 135 4 3 = 79 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 135 4 4 = 23 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 135 4 5 = 49 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 135 4 6 = 61 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 135 4 7 = 109 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 135 4 8 = 83 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 135 4 9 = 31 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 135 4 10 = 113 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 135 4 11 = 91 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 135 4 12 = 47 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 135 4 13 = 53 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 135 4 14 = 77 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 135 4 15 = 19 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 135 4 16 = 17 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 135 4 17 = 1 :=
    slopeOrbit_step_eval 16 2 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 135 4 18 = 121 :=
    slopeOrbit_step_eval 17 7 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 135 4 18 = slopeOrbit 135 4 1
    rw [e18, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 135) (v := 121) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 135) (v := 107) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 135) (v := 79) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 135) (v := 23) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 135) (v := 49) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 135) (v := 61) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 135) (v := 109) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 135) (v := 83) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 135) (v := 31) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 135) (v := 113) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e11, canonGap_eval (q := 135) (v := 91) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e12, canonGap_eval (q := 135) (v := 47) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e13, canonGap_eval (q := 135) (v := 53) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e14, canonGap_eval (q := 135) (v := 77) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e15, canonGap_eval (q := 135) (v := 19) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e16, canonGap_eval (q := 135) (v := 17) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e17, canonGap_eval (q := 135) (v := 1) (g := 7) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(135,4)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_135_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 135) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_135_4.1 ftC1_135_4.2

/-- `(147,3)`: cycle `[45, 33, 117, 87, 27, 69, 129, 111, 75, 3]` (period `10`, bands `2, 3, 1, 1, 3, 2, 1, 1, 1, 6`) - band-4-free. -/
private theorem ftC1_147_3 :
    slopeOrbit 147 3 (1 + 10) = slopeOrbit 147 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 10 → canonGap 147 (slopeOrbit 147 3 j) ≠ 4 := by
  have e0 : slopeOrbit 147 3 0 = 3 := rfl
  have e1 : slopeOrbit 147 3 1 = 45 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 147 3 2 = 33 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 147 3 3 = 117 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 147 3 4 = 87 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 147 3 5 = 27 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 147 3 6 = 69 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 147 3 7 = 129 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 147 3 8 = 111 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 147 3 9 = 75 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 147 3 10 = 3 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 147 3 11 = 45 :=
    slopeOrbit_step_eval 10 5 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 147 3 11 = slopeOrbit 147 3 1
    rw [e11, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 147) (v := 45) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 147) (v := 33) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 147) (v := 117) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 147) (v := 87) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 147) (v := 27) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 147) (v := 69) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 147) (v := 129) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 147) (v := 111) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 147) (v := 75) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 147) (v := 3) (g := 5) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(147,3)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_147_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 147) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_147_3.1 ftC1_147_3.2

/-- `(147,24)`: cycle `[45, 33, 117, 87, 27, 69, 129, 111, 75, 3]` (period `10`, bands `2, 3, 1, 1, 3, 2, 1, 1, 1, 6`) - band-4-free. -/
private theorem ftC1_147_24 :
    slopeOrbit 147 24 (1 + 10) = slopeOrbit 147 24 1
      ∧ ∀ j, 1 ≤ j → j ≤ 10 → canonGap 147 (slopeOrbit 147 24 j) ≠ 4 := by
  have e0 : slopeOrbit 147 24 0 = 24 := rfl
  have e1 : slopeOrbit 147 24 1 = 45 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 147 24 2 = 33 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 147 24 3 = 117 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 147 24 4 = 87 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 147 24 5 = 27 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 147 24 6 = 69 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 147 24 7 = 129 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 147 24 8 = 111 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 147 24 9 = 75 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 147 24 10 = 3 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 147 24 11 = 45 :=
    slopeOrbit_step_eval 10 5 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 147 24 11 = slopeOrbit 147 24 1
    rw [e11, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 147) (v := 45) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 147) (v := 33) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 147) (v := 117) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 147) (v := 87) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 147) (v := 27) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 147) (v := 69) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 147) (v := 129) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 147) (v := 111) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 147) (v := 75) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 147) (v := 3) (g := 5) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(147,24)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_147_24 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 147) (hK : (class1SlopeDatum ctx).K₀ = 24) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_147_24.1 ftC1_147_24.2

/-- `(151,75)`: cycle `[149, 147, 143, 135, 119, 87, 23, 33, 113, 75]` (period `10`, bands `1, 1, 1, 1, 1, 1, 3, 3, 1, 2`) - band-4-free. -/
private theorem ftC1_151_75 :
    slopeOrbit 151 75 (1 + 10) = slopeOrbit 151 75 1
      ∧ ∀ j, 1 ≤ j → j ≤ 10 → canonGap 151 (slopeOrbit 151 75 j) ≠ 4 := by
  have e0 : slopeOrbit 151 75 0 = 75 := rfl
  have e1 : slopeOrbit 151 75 1 = 149 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 151 75 2 = 147 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 151 75 3 = 143 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 151 75 4 = 135 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 151 75 5 = 119 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 151 75 6 = 87 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 151 75 7 = 23 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 151 75 8 = 33 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 151 75 9 = 113 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 151 75 10 = 75 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 151 75 11 = 149 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 151 75 11 = slopeOrbit 151 75 1
    rw [e11, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 151) (v := 149) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 151) (v := 147) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 151) (v := 143) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 151) (v := 135) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 151) (v := 119) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 151) (v := 87) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 151) (v := 23) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 151) (v := 33) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 151) (v := 113) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 151) (v := 75) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(151,75)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_151_75 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 151) (hK : (class1SlopeDatum ctx).K₀ = 75) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_151_75.1 ftC1_151_75.2

/-- `(155,2)`: cycle `[101, 47, 33, 109, 63, 97, 39, 1]` (period `8`, bands `1, 2, 3, 1, 2, 1, 2, 8`) - band-4-free. -/
private theorem ftC1_155_2 :
    slopeOrbit 155 2 (1 + 8) = slopeOrbit 155 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 8 → canonGap 155 (slopeOrbit 155 2 j) ≠ 4 := by
  have e0 : slopeOrbit 155 2 0 = 2 := rfl
  have e1 : slopeOrbit 155 2 1 = 101 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 155 2 2 = 47 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 155 2 3 = 33 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 155 2 4 = 109 :=
    slopeOrbit_step_eval 3 2 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 155 2 5 = 63 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 155 2 6 = 97 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 155 2 7 = 39 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 155 2 8 = 1 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 155 2 9 = 101 :=
    slopeOrbit_step_eval 8 7 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 155 2 9 = slopeOrbit 155 2 1
    rw [e9, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 155) (v := 101) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 155) (v := 47) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 155) (v := 33) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 155) (v := 109) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 155) (v := 63) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 155) (v := 97) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 155) (v := 39) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 155) (v := 1) (g := 7) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(155,2)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_155_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 155) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_155_2.1 ftC1_155_2.2

/-- `(155,77)`: cycle `[153, 151, 147, 139, 123, 91, 27, 61, 89, 23, 29, 77]` (period `12`, bands `1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2`) - band-4-free. -/
private theorem ftC1_155_77 :
    slopeOrbit 155 77 (1 + 12) = slopeOrbit 155 77 1
      ∧ ∀ j, 1 ≤ j → j ≤ 12 → canonGap 155 (slopeOrbit 155 77 j) ≠ 4 := by
  have e0 : slopeOrbit 155 77 0 = 77 := rfl
  have e1 : slopeOrbit 155 77 1 = 153 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 155 77 2 = 151 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 155 77 3 = 147 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 155 77 4 = 139 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 155 77 5 = 123 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 155 77 6 = 91 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 155 77 7 = 27 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 155 77 8 = 61 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 155 77 9 = 89 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 155 77 10 = 23 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 155 77 11 = 29 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 155 77 12 = 77 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 155 77 13 = 153 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 155 77 13 = slopeOrbit 155 77 1
    rw [e13, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 155) (v := 153) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 155) (v := 151) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 155) (v := 147) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 155) (v := 139) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 155) (v := 123) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 155) (v := 91) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 155) (v := 27) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 155) (v := 61) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 155) (v := 89) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 155) (v := 23) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e11, canonGap_eval (q := 155) (v := 29) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e12, canonGap_eval (q := 155) (v := 77) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(155,77)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_155_77 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 155) (hK : (class1SlopeDatum ctx).K₀ = 77) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_155_77.1 ftC1_155_77.2

/-- `(157,78)`: cycle `[155, 153, 149, 141, 125, 93, 29, 75, 143, 129, 101, 45, 23, 27, 59, 79, 1, 99, 41, 7, 67, 111, 65, 103, 49, 39]` (period `26`, bands `1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 2, 1, 8, 1, 2, 5, 2, 1, 2, 1, 2, 3`) - band-4-free. -/
private theorem ftC1_157_78 :
    slopeOrbit 157 78 (1 + 26) = slopeOrbit 157 78 1
      ∧ ∀ j, 1 ≤ j → j ≤ 26 → canonGap 157 (slopeOrbit 157 78 j) ≠ 4 := by
  have e0 : slopeOrbit 157 78 0 = 78 := rfl
  have e1 : slopeOrbit 157 78 1 = 155 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 157 78 2 = 153 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 157 78 3 = 149 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 157 78 4 = 141 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 157 78 5 = 125 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 157 78 6 = 93 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 157 78 7 = 29 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 157 78 8 = 75 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 157 78 9 = 143 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 157 78 10 = 129 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 157 78 11 = 101 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 157 78 12 = 45 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 157 78 13 = 23 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 157 78 14 = 27 :=
    slopeOrbit_step_eval 13 2 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 157 78 15 = 59 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 157 78 16 = 79 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 157 78 17 = 1 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 157 78 18 = 99 :=
    slopeOrbit_step_eval 17 7 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 157 78 19 = 41 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 157 78 20 = 7 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 157 78 21 = 67 :=
    slopeOrbit_step_eval 20 4 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 157 78 22 = 111 :=
    slopeOrbit_step_eval 21 1 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 157 78 23 = 65 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 157 78 24 = 103 :=
    slopeOrbit_step_eval 23 1 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 157 78 25 = 49 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 157 78 26 = 39 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 157 78 27 = 155 :=
    slopeOrbit_step_eval 26 2 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 157 78 27 = slopeOrbit 157 78 1
    rw [e27, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 157) (v := 155) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 157) (v := 153) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 157) (v := 149) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 157) (v := 141) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 157) (v := 125) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 157) (v := 93) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 157) (v := 29) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 157) (v := 75) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 157) (v := 143) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 157) (v := 129) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e11, canonGap_eval (q := 157) (v := 101) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e12, canonGap_eval (q := 157) (v := 45) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e13, canonGap_eval (q := 157) (v := 23) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e14, canonGap_eval (q := 157) (v := 27) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e15, canonGap_eval (q := 157) (v := 59) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e16, canonGap_eval (q := 157) (v := 79) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e17, canonGap_eval (q := 157) (v := 1) (g := 7) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e18, canonGap_eval (q := 157) (v := 99) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e19, canonGap_eval (q := 157) (v := 41) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e20, canonGap_eval (q := 157) (v := 7) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e21, canonGap_eval (q := 157) (v := 67) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e22, canonGap_eval (q := 157) (v := 111) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e23, canonGap_eval (q := 157) (v := 65) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e24, canonGap_eval (q := 157) (v := 103) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e25, canonGap_eval (q := 157) (v := 49) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e26, canonGap_eval (q := 157) (v := 39) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(157,78)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_157_78 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 157) (hK : (class1SlopeDatum ctx).K₀ = 78) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_157_78.1 ftC1_157_78.2

/-- `(165,5)`: cycle `[155, 145, 125, 85, 5]` (period `5`, bands `1, 1, 1, 1, 6`) - band-4-free. -/
private theorem ftC1_165_5 :
    slopeOrbit 165 5 (1 + 5) = slopeOrbit 165 5 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 165 (slopeOrbit 165 5 j) ≠ 4 := by
  have e0 : slopeOrbit 165 5 0 = 5 := rfl
  have e1 : slopeOrbit 165 5 1 = 155 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 165 5 2 = 145 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 165 5 3 = 125 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 165 5 4 = 85 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 165 5 5 = 5 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 165 5 6 = 155 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 165 5 6 = slopeOrbit 165 5 1
    rw [e6, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 165) (v := 155) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 165) (v := 145) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 165) (v := 125) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 165) (v := 85) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 165) (v := 5) (g := 5) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(165,5)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_165_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 165) (hK : (class1SlopeDatum ctx).K₀ = 5) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_165_5.1 ftC1_165_5.2

/-- `(165,27)`: cycle `[51, 39, 147, 129, 93, 21, 3, 27]` (period `8`, bands `2, 3, 1, 1, 1, 3, 6, 3`) - band-4-free. -/
private theorem ftC1_165_27 :
    slopeOrbit 165 27 (1 + 8) = slopeOrbit 165 27 1
      ∧ ∀ j, 1 ≤ j → j ≤ 8 → canonGap 165 (slopeOrbit 165 27 j) ≠ 4 := by
  have e0 : slopeOrbit 165 27 0 = 27 := rfl
  have e1 : slopeOrbit 165 27 1 = 51 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 165 27 2 = 39 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 165 27 3 = 147 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 165 27 4 = 129 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 165 27 5 = 93 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 165 27 6 = 21 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 165 27 7 = 3 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 165 27 8 = 27 :=
    slopeOrbit_step_eval 7 5 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 165 27 9 = 51 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 165 27 9 = slopeOrbit 165 27 1
    rw [e9, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 165) (v := 51) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 165) (v := 39) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 165) (v := 147) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 165) (v := 129) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 165) (v := 93) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 165) (v := 21) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 165) (v := 3) (g := 5) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 165) (v := 27) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(165,27)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_165_27 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 165) (hK : (class1SlopeDatum ctx).K₀ = 27) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_165_27.1 ftC1_165_27.2

/-- `(165,82)`: cycle `[163, 161, 157, 149, 133, 101, 37, 131, 97, 29, 67, 103, 41]` (period `13`, bands `1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3`) - band-4-free. -/
private theorem ftC1_165_82 :
    slopeOrbit 165 82 (1 + 13) = slopeOrbit 165 82 1
      ∧ ∀ j, 1 ≤ j → j ≤ 13 → canonGap 165 (slopeOrbit 165 82 j) ≠ 4 := by
  have e0 : slopeOrbit 165 82 0 = 82 := rfl
  have e1 : slopeOrbit 165 82 1 = 163 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 165 82 2 = 161 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 165 82 3 = 157 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 165 82 4 = 149 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 165 82 5 = 133 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 165 82 6 = 101 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 165 82 7 = 37 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 165 82 8 = 131 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 165 82 9 = 97 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 165 82 10 = 29 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 165 82 11 = 67 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 165 82 12 = 103 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 165 82 13 = 41 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 165 82 14 = 163 :=
    slopeOrbit_step_eval 13 2 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 165 82 14 = slopeOrbit 165 82 1
    rw [e14, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 165) (v := 163) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 165) (v := 161) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 165) (v := 157) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 165) (v := 149) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 165) (v := 133) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 165) (v := 101) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 165) (v := 37) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 165) (v := 131) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 165) (v := 97) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 165) (v := 29) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e11, canonGap_eval (q := 165) (v := 67) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e12, canonGap_eval (q := 165) (v := 103) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e13, canonGap_eval (q := 165) (v := 41) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(165,82)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_165_82 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 165) (hK : (class1SlopeDatum ctx).K₀ = 82) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_165_82.1 ftC1_165_82.2

/-- `(171,1)`: cycle `[85, 169, 167, 163, 155, 139, 107, 43, 1]` (period `9`, bands `2, 1, 1, 1, 1, 1, 1, 2, 8`) - band-4-free. -/
private theorem ftC1_171_1 :
    slopeOrbit 171 1 (1 + 9) = slopeOrbit 171 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 → canonGap 171 (slopeOrbit 171 1 j) ≠ 4 := by
  have e0 : slopeOrbit 171 1 0 = 1 := rfl
  have e1 : slopeOrbit 171 1 1 = 85 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 171 1 2 = 169 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 171 1 3 = 167 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 171 1 4 = 163 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 171 1 5 = 155 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 171 1 6 = 139 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 171 1 7 = 107 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 171 1 8 = 43 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 171 1 9 = 1 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 171 1 10 = 85 :=
    slopeOrbit_step_eval 9 7 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 171 1 10 = slopeOrbit 171 1 1
    rw [e10, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 171) (v := 85) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 171) (v := 169) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 171) (v := 167) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 171) (v := 163) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 171) (v := 155) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 171) (v := 139) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 171) (v := 107) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 171) (v := 43) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 171) (v := 1) (g := 7) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(171,1)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_171_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 171) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_171_1.1 ftC1_171_1.2

/-- `(171,4)`: cycle `[85, 169, 167, 163, 155, 139, 107, 43, 1]` (period `9`, bands `2, 1, 1, 1, 1, 1, 1, 2, 8`) - band-4-free. -/
private theorem ftC1_171_4 :
    slopeOrbit 171 4 (1 + 9) = slopeOrbit 171 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 → canonGap 171 (slopeOrbit 171 4 j) ≠ 4 := by
  have e0 : slopeOrbit 171 4 0 = 4 := rfl
  have e1 : slopeOrbit 171 4 1 = 85 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 171 4 2 = 169 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 171 4 3 = 167 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 171 4 4 = 163 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 171 4 5 = 155 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 171 4 6 = 139 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 171 4 7 = 107 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 171 4 8 = 43 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 171 4 9 = 1 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 171 4 10 = 85 :=
    slopeOrbit_step_eval 9 7 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 171 4 10 = slopeOrbit 171 4 1
    rw [e10, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 171) (v := 85) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 171) (v := 169) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 171) (v := 167) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 171) (v := 163) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 171) (v := 155) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 171) (v := 139) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 171) (v := 107) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 171) (v := 43) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 171) (v := 1) (g := 7) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(171,4)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_171_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 171) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_171_4.1 ftC1_171_4.2

/-- `(171,9)`: cycle `[117, 63, 81, 153, 135, 99, 27, 45, 9]` (period `9`, bands `1, 2, 2, 1, 1, 1, 3, 2, 5`) - band-4-free. -/
private theorem ftC1_171_9 :
    slopeOrbit 171 9 (1 + 9) = slopeOrbit 171 9 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 → canonGap 171 (slopeOrbit 171 9 j) ≠ 4 := by
  have e0 : slopeOrbit 171 9 0 = 9 := rfl
  have e1 : slopeOrbit 171 9 1 = 117 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 171 9 2 = 63 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 171 9 3 = 81 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 171 9 4 = 153 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 171 9 5 = 135 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 171 9 6 = 99 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 171 9 7 = 27 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 171 9 8 = 45 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 171 9 9 = 9 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 171 9 10 = 117 :=
    slopeOrbit_step_eval 9 4 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 171 9 10 = slopeOrbit 171 9 1
    rw [e10, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 171) (v := 117) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 171) (v := 63) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 171) (v := 81) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 171) (v := 153) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 171) (v := 135) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 171) (v := 99) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 171) (v := 27) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 171) (v := 45) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 171) (v := 9) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(171,9)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_171_9 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 171) (hK : (class1SlopeDatum ctx).K₀ = 9) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_171_9.1 ftC1_171_9.2

/-- `(171,28)`: cycle `[53, 41, 157, 143, 115, 59, 65, 89, 7]` (period `9`, bands `2, 3, 1, 1, 1, 2, 2, 1, 5`) - band-4-free. -/
private theorem ftC1_171_28 :
    slopeOrbit 171 28 (1 + 9) = slopeOrbit 171 28 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 → canonGap 171 (slopeOrbit 171 28 j) ≠ 4 := by
  have e0 : slopeOrbit 171 28 0 = 28 := rfl
  have e1 : slopeOrbit 171 28 1 = 53 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 171 28 2 = 41 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 171 28 3 = 157 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 171 28 4 = 143 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 171 28 5 = 115 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 171 28 6 = 59 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 171 28 7 = 65 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 171 28 8 = 89 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 171 28 9 = 7 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 171 28 10 = 53 :=
    slopeOrbit_step_eval 9 4 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 171 28 10 = slopeOrbit 171 28 1
    rw [e10, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 171) (v := 53) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 171) (v := 41) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 171) (v := 157) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 171) (v := 143) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 171) (v := 115) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 171) (v := 59) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 171) (v := 65) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 171) (v := 89) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 171) (v := 7) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(171,28)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_171_28 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 171) (hK : (class1SlopeDatum ctx).K₀ = 28) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_171_28.1 ftC1_171_28.2

/-- `(171,85)`: cycle `[169, 167, 163, 155, 139, 107, 43, 1, 85]` (period `9`, bands `1, 1, 1, 1, 1, 1, 2, 8, 2`) - band-4-free. -/
private theorem ftC1_171_85 :
    slopeOrbit 171 85 (1 + 9) = slopeOrbit 171 85 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 → canonGap 171 (slopeOrbit 171 85 j) ≠ 4 := by
  have e0 : slopeOrbit 171 85 0 = 85 := rfl
  have e1 : slopeOrbit 171 85 1 = 169 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 171 85 2 = 167 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 171 85 3 = 163 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 171 85 4 = 155 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 171 85 5 = 139 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 171 85 6 = 107 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 171 85 7 = 43 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 171 85 8 = 1 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 171 85 9 = 85 :=
    slopeOrbit_step_eval 8 7 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 171 85 10 = 169 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 171 85 10 = slopeOrbit 171 85 1
    rw [e10, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 171) (v := 169) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 171) (v := 167) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 171) (v := 163) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 171) (v := 155) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 171) (v := 139) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 171) (v := 107) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 171) (v := 43) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 171) (v := 1) (g := 7) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 171) (v := 85) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(171,85)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_171_85 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 171) (hK : (class1SlopeDatum ctx).K₀ = 85) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_171_85.1 ftC1_171_85.2

/-- `(183,91)`: cycle `[181, 179, 175, 167, 151, 119, 55, 37, 113, 43, 161, 139, 95, 7, 41, 145, 107, 31, 65, 77, 125, 67, 85, 157, 131, 79, 133, 83, 149, 115, 47, 5, 137, 91]` (period `34`, bands `1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 2`) - band-4-free. -/
private theorem ftC1_183_91 :
    slopeOrbit 183 91 (1 + 34) = slopeOrbit 183 91 1
      ∧ ∀ j, 1 ≤ j → j ≤ 34 → canonGap 183 (slopeOrbit 183 91 j) ≠ 4 := by
  have e0 : slopeOrbit 183 91 0 = 91 := rfl
  have e1 : slopeOrbit 183 91 1 = 181 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 183 91 2 = 179 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 183 91 3 = 175 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 183 91 4 = 167 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 183 91 5 = 151 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 183 91 6 = 119 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 183 91 7 = 55 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 183 91 8 = 37 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 183 91 9 = 113 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 183 91 10 = 43 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 183 91 11 = 161 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 183 91 12 = 139 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 183 91 13 = 95 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 183 91 14 = 7 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 183 91 15 = 41 :=
    slopeOrbit_step_eval 14 4 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 183 91 16 = 145 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 183 91 17 = 107 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 183 91 18 = 31 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 183 91 19 = 65 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 183 91 20 = 77 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 183 91 21 = 125 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 183 91 22 = 67 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 183 91 23 = 85 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 183 91 24 = 157 :=
    slopeOrbit_step_eval 23 1 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 183 91 25 = 131 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 183 91 26 = 79 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 183 91 27 = 133 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 183 91 28 = 83 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 183 91 29 = 149 :=
    slopeOrbit_step_eval 28 1 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 183 91 30 = 115 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 183 91 31 = 47 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 183 91 32 = 5 :=
    slopeOrbit_step_eval 31 1 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 183 91 33 = 137 :=
    slopeOrbit_step_eval 32 5 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 183 91 34 = 91 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 183 91 35 = 181 :=
    slopeOrbit_step_eval 34 1 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 183 91 35 = slopeOrbit 183 91 1
    rw [e35, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 183) (v := 181) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 183) (v := 179) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 183) (v := 175) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 183) (v := 167) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 183) (v := 151) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 183) (v := 119) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 183) (v := 55) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 183) (v := 37) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 183) (v := 113) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 183) (v := 43) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e11, canonGap_eval (q := 183) (v := 161) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e12, canonGap_eval (q := 183) (v := 139) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e13, canonGap_eval (q := 183) (v := 95) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e14, canonGap_eval (q := 183) (v := 7) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e15, canonGap_eval (q := 183) (v := 41) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e16, canonGap_eval (q := 183) (v := 145) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e17, canonGap_eval (q := 183) (v := 107) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e18, canonGap_eval (q := 183) (v := 31) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e19, canonGap_eval (q := 183) (v := 65) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e20, canonGap_eval (q := 183) (v := 77) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e21, canonGap_eval (q := 183) (v := 125) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e22, canonGap_eval (q := 183) (v := 67) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e23, canonGap_eval (q := 183) (v := 85) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e24, canonGap_eval (q := 183) (v := 157) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e25, canonGap_eval (q := 183) (v := 131) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e26, canonGap_eval (q := 183) (v := 79) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e27, canonGap_eval (q := 183) (v := 133) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e28, canonGap_eval (q := 183) (v := 83) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e29, canonGap_eval (q := 183) (v := 149) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e30, canonGap_eval (q := 183) (v := 115) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e31, canonGap_eval (q := 183) (v := 47) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e32, canonGap_eval (q := 183) (v := 5) (g := 5) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e33, canonGap_eval (q := 183) (v := 137) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e34, canonGap_eval (q := 183) (v := 91) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(183,91)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_183_91 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 183) (hK : (class1SlopeDatum ctx).K₀ = 91) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_183_91.1 ftC1_183_91.2

/-- `(187,5)`: cycle `[133, 79, 129, 71, 97, 7, 37, 109, 31, 61, 57, 41, 141, 95, 3, 5]` (period `16`, bands `1, 2, 1, 2, 1, 5, 3, 1, 3, 2, 2, 3, 1, 1, 6, 6`) - band-4-free. -/
private theorem ftC1_187_5 :
    slopeOrbit 187 5 (1 + 16) = slopeOrbit 187 5 1
      ∧ ∀ j, 1 ≤ j → j ≤ 16 → canonGap 187 (slopeOrbit 187 5 j) ≠ 4 := by
  have e0 : slopeOrbit 187 5 0 = 5 := rfl
  have e1 : slopeOrbit 187 5 1 = 133 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 187 5 2 = 79 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 187 5 3 = 129 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 187 5 4 = 71 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 187 5 5 = 97 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 187 5 6 = 7 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 187 5 7 = 37 :=
    slopeOrbit_step_eval 6 4 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 187 5 8 = 109 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 187 5 9 = 31 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 187 5 10 = 61 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 187 5 11 = 57 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 187 5 12 = 41 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 187 5 13 = 141 :=
    slopeOrbit_step_eval 12 2 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 187 5 14 = 95 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 187 5 15 = 3 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 187 5 16 = 5 :=
    slopeOrbit_step_eval 15 5 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 187 5 17 = 133 :=
    slopeOrbit_step_eval 16 5 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 187 5 17 = slopeOrbit 187 5 1
    rw [e17, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 187) (v := 133) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 187) (v := 79) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 187) (v := 129) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 187) (v := 71) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 187) (v := 97) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 187) (v := 7) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 187) (v := 37) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 187) (v := 109) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 187) (v := 31) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 187) (v := 61) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e11, canonGap_eval (q := 187) (v := 57) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e12, canonGap_eval (q := 187) (v := 41) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e13, canonGap_eval (q := 187) (v := 141) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e14, canonGap_eval (q := 187) (v := 95) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e15, canonGap_eval (q := 187) (v := 3) (g := 5) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e16, canonGap_eval (q := 187) (v := 5) (g := 5) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(187,5)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_187_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 187) (hK : (class1SlopeDatum ctx).K₀ = 5) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_187_5.1 ftC1_187_5.2

/-- `(189,1)`: cycle `[67, 79, 127, 65, 71, 95, 1]` (period `7`, bands `2, 2, 1, 2, 2, 1, 8`) - band-4-free. -/
private theorem ftC1_189_1 :
    slopeOrbit 189 1 (1 + 7) = slopeOrbit 189 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 → canonGap 189 (slopeOrbit 189 1 j) ≠ 4 := by
  have e0 : slopeOrbit 189 1 0 = 1 := rfl
  have e1 : slopeOrbit 189 1 1 = 67 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 189 1 2 = 79 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 189 1 3 = 127 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 189 1 4 = 65 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 189 1 5 = 71 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 189 1 6 = 95 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 189 1 7 = 1 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 189 1 8 = 67 :=
    slopeOrbit_step_eval 7 7 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 189 1 8 = slopeOrbit 189 1 1
    rw [e8, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 189) (v := 67) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 189) (v := 79) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 189) (v := 127) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 189) (v := 65) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 189) (v := 71) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 189) (v := 95) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 189) (v := 1) (g := 7) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(189,1)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_189_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 189) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_189_1.1 ftC1_189_1.2

/-- `(189,3)`: cycle `[3]` (period `1`, bands `6`) - band-4-free. -/
private theorem ftC1_189_3 :
    slopeOrbit 189 3 (1 + 1) = slopeOrbit 189 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → canonGap 189 (slopeOrbit 189 3 j) ≠ 4 := by
  have e0 : slopeOrbit 189 3 0 = 3 := rfl
  have e1 : slopeOrbit 189 3 1 = 3 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 189 3 2 = 3 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 189 3 2 = slopeOrbit 189 3 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 189) (v := 3) (g := 5) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(189,3)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_189_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 189) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_189_3.1 ftC1_189_3.2

/-- `(189,4)`: cycle `[67, 79, 127, 65, 71, 95, 1]` (period `7`, bands `2, 2, 1, 2, 2, 1, 8`) - band-4-free. -/
private theorem ftC1_189_4 :
    slopeOrbit 189 4 (1 + 7) = slopeOrbit 189 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 → canonGap 189 (slopeOrbit 189 4 j) ≠ 4 := by
  have e0 : slopeOrbit 189 4 0 = 4 := rfl
  have e1 : slopeOrbit 189 4 1 = 67 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 189 4 2 = 79 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 189 4 3 = 127 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 189 4 4 = 65 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 189 4 5 = 71 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 189 4 6 = 95 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 189 4 7 = 1 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 189 4 8 = 67 :=
    slopeOrbit_step_eval 7 7 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 189 4 8 = slopeOrbit 189 4 1
    rw [e8, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 189) (v := 67) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 189) (v := 79) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 189) (v := 127) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 189) (v := 65) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 189) (v := 71) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 189) (v := 95) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 189) (v := 1) (g := 7) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(189,4)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_189_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 189) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_189_4.1 ftC1_189_4.2

/-- `(189,31)`: cycle `[59, 47, 187, 185, 181, 173, 157, 125, 61, 55, 31]` (period `11`, bands `2, 3, 1, 1, 1, 1, 1, 1, 2, 2, 3`) - band-4-free. -/
private theorem ftC1_189_31 :
    slopeOrbit 189 31 (1 + 11) = slopeOrbit 189 31 1
      ∧ ∀ j, 1 ≤ j → j ≤ 11 → canonGap 189 (slopeOrbit 189 31 j) ≠ 4 := by
  have e0 : slopeOrbit 189 31 0 = 31 := rfl
  have e1 : slopeOrbit 189 31 1 = 59 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 189 31 2 = 47 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 189 31 3 = 187 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 189 31 4 = 185 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 189 31 5 = 181 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 189 31 6 = 173 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 189 31 7 = 157 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 189 31 8 = 125 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 189 31 9 = 61 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 189 31 10 = 55 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 189 31 11 = 31 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 189 31 12 = 59 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 189 31 12 = slopeOrbit 189 31 1
    rw [e12, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 189) (v := 59) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 189) (v := 47) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 189) (v := 187) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 189) (v := 185) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 189) (v := 181) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 189) (v := 173) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 189) (v := 157) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 189) (v := 125) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 189) (v := 61) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 189) (v := 55) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e11, canonGap_eval (q := 189) (v := 31) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(189,31)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_189_31 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 189) (hK : (class1SlopeDatum ctx).K₀ = 31) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_189_31.1 ftC1_189_31.2

/-- `(189,94)`: cycle `[187, 185, 181, 173, 157, 125, 61, 55, 31, 59, 47]` (period `11`, bands `1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3`) - band-4-free. -/
private theorem ftC1_189_94 :
    slopeOrbit 189 94 (1 + 11) = slopeOrbit 189 94 1
      ∧ ∀ j, 1 ≤ j → j ≤ 11 → canonGap 189 (slopeOrbit 189 94 j) ≠ 4 := by
  have e0 : slopeOrbit 189 94 0 = 94 := rfl
  have e1 : slopeOrbit 189 94 1 = 187 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 189 94 2 = 185 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 189 94 3 = 181 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 189 94 4 = 173 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 189 94 5 = 157 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 189 94 6 = 125 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 189 94 7 = 61 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 189 94 8 = 55 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 189 94 9 = 31 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 189 94 10 = 59 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 189 94 11 = 47 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 189 94 12 = 187 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 189 94 12 = slopeOrbit 189 94 1
    rw [e12, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 189) (v := 187) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 189) (v := 185) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 189) (v := 181) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 189) (v := 173) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 189) (v := 157) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 189) (v := 125) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 189) (v := 61) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 189) (v := 55) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 189) (v := 31) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 189) (v := 59) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e11, canonGap_eval (q := 189) (v := 47) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(189,94)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_189_94 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 189) (hK : (class1SlopeDatum ctx).K₀ = 94) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_189_94.1 ftC1_189_94.2

/-- `(195,1)`: cycle `[61, 49, 1]` (period `3`, bands `2, 2, 8`) - band-4-free. -/
private theorem ftC1_195_1 :
    slopeOrbit 195 1 (1 + 3) = slopeOrbit 195 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 3 → canonGap 195 (slopeOrbit 195 1 j) ≠ 4 := by
  have e0 : slopeOrbit 195 1 0 = 1 := rfl
  have e1 : slopeOrbit 195 1 1 = 61 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 195 1 2 = 49 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 195 1 3 = 1 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 195 1 4 = 61 :=
    slopeOrbit_step_eval 3 7 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 195 1 4 = slopeOrbit 195 1 1
    rw [e4, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 195) (v := 61) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 195) (v := 49) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 195) (v := 1) (g := 7) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(195,1)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_195_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 195) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_195_1.1 ftC1_195_1.2

/-- `(195,2)`: cycle `[61, 49, 1]` (period `3`, bands `2, 2, 8`) - band-4-free. -/
private theorem ftC1_195_2 :
    slopeOrbit 195 2 (1 + 3) = slopeOrbit 195 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 3 → canonGap 195 (slopeOrbit 195 2 j) ≠ 4 := by
  have e0 : slopeOrbit 195 2 0 = 2 := rfl
  have e1 : slopeOrbit 195 2 1 = 61 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 195 2 2 = 49 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 195 2 3 = 1 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 195 2 4 = 61 :=
    slopeOrbit_step_eval 3 7 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 195 2 4 = slopeOrbit 195 2 1
    rw [e4, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 195) (v := 61) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 195) (v := 49) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 195) (v := 1) (g := 7) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(195,2)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_195_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 195) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_195_2.1 ftC1_195_2.2

/-- `(195,6)`: cycle `[189, 183, 171, 147, 99, 3]` (period `6`, bands `1, 1, 1, 1, 1, 7`) - band-4-free. -/
private theorem ftC1_195_6 :
    slopeOrbit 195 6 (1 + 6) = slopeOrbit 195 6 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 195 (slopeOrbit 195 6 j) ≠ 4 := by
  have e0 : slopeOrbit 195 6 0 = 6 := rfl
  have e1 : slopeOrbit 195 6 1 = 189 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 195 6 2 = 183 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 195 6 3 = 171 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 195 6 4 = 147 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 195 6 5 = 99 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 195 6 6 = 3 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 195 6 7 = 189 :=
    slopeOrbit_step_eval 6 6 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 195 6 7 = slopeOrbit 195 6 1
    rw [e7, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 195) (v := 189) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 195) (v := 183) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 195) (v := 171) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 195) (v := 147) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 195) (v := 99) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 195) (v := 3) (g := 6) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(195,6)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_195_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 195) (hK : (class1SlopeDatum ctx).K₀ = 6) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_195_6.1 ftC1_195_6.2

/-- `(195,7)`: cycle `[29, 37, 101, 7]` (period `4`, bands `3, 3, 1, 5`) - band-4-free. -/
private theorem ftC1_195_7 :
    slopeOrbit 195 7 (1 + 4) = slopeOrbit 195 7 1
      ∧ ∀ j, 1 ≤ j → j ≤ 4 → canonGap 195 (slopeOrbit 195 7 j) ≠ 4 := by
  have e0 : slopeOrbit 195 7 0 = 7 := rfl
  have e1 : slopeOrbit 195 7 1 = 29 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 195 7 2 = 37 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 195 7 3 = 101 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 195 7 4 = 7 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 195 7 5 = 29 :=
    slopeOrbit_step_eval 4 4 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 195 7 5 = slopeOrbit 195 7 1
    rw [e5, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 195) (v := 29) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 195) (v := 37) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 195) (v := 101) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 195) (v := 7) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(195,7)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_195_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 195) (hK : (class1SlopeDatum ctx).K₀ = 7) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_195_7.1 ftC1_195_7.2

/-- `(195,32)`: cycle `[61, 49, 1]` (period `3`, bands `2, 2, 8`) - band-4-free. -/
private theorem ftC1_195_32 :
    slopeOrbit 195 32 (1 + 3) = slopeOrbit 195 32 1
      ∧ ∀ j, 1 ≤ j → j ≤ 3 → canonGap 195 (slopeOrbit 195 32 j) ≠ 4 := by
  have e0 : slopeOrbit 195 32 0 = 32 := rfl
  have e1 : slopeOrbit 195 32 1 = 61 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 195 32 2 = 49 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 195 32 3 = 1 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 195 32 4 = 61 :=
    slopeOrbit_step_eval 3 7 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 195 32 4 = slopeOrbit 195 32 1
    rw [e4, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 195) (v := 61) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 195) (v := 49) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 195) (v := 1) (g := 7) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(195,32)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_195_32 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 195) (hK : (class1SlopeDatum ctx).K₀ = 32) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_195_32.1 ftC1_195_32.2

/-- `(195,97)`: cycle `[193, 191, 187, 179, 163, 131, 67, 73, 97]` (period `9`, bands `1, 1, 1, 1, 1, 1, 2, 2, 2`) - band-4-free. -/
private theorem ftC1_195_97 :
    slopeOrbit 195 97 (1 + 9) = slopeOrbit 195 97 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 → canonGap 195 (slopeOrbit 195 97 j) ≠ 4 := by
  have e0 : slopeOrbit 195 97 0 = 97 := rfl
  have e1 : slopeOrbit 195 97 1 = 193 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 195 97 2 = 191 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 195 97 3 = 187 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 195 97 4 = 179 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 195 97 5 = 163 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 195 97 6 = 131 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 195 97 7 = 67 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 195 97 8 = 73 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 195 97 9 = 97 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 195 97 10 = 193 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 195 97 10 = slopeOrbit 195 97 1
    rw [e10, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 195) (v := 193) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 195) (v := 191) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 195) (v := 187) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 195) (v := 179) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 195) (v := 163) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 195) (v := 131) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 195) (v := 67) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 195) (v := 73) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 195) (v := 97) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(195,97)` empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_datum_195_97 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 195) (hK : (class1SlopeDatum ctx).K₀ = 97) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  class1Fibre_empty_of_orbit_collision ctx hq hK (by norm_num) ftC1_195_97.1 ftC1_195_97.2

/-! ### The eight fully closed new moduli -/

/-- **Modulus-109 closure**: every admissible pin (`2K₀+1 ∣ 109`) has a band-4-free
cycle - the class-1 fibre is empty on every `q = 109` shell. -/
theorem ftClass1Fibre_empty_of_modulus_eq_109 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 109) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq] at hdvd
  have hpos := (class1SlopeDatum ctx).hK₀_pos
  have hmem : 2 * (class1SlopeDatum ctx).K₀ + 1 ∈ Nat.divisors 109 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 109 = {1, 109} from by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hK : (class1SlopeDatum ctx).K₀ = 54 := by omega
  exact ftClass1Fibre_empty_of_datum_109_54 ctx hq hK

/-- **Modulus-113 closure**: every admissible pin (`2K₀+1 ∣ 113`) has a band-4-free
cycle - the class-1 fibre is empty on every `q = 113` shell. -/
theorem ftClass1Fibre_empty_of_modulus_eq_113 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 113) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq] at hdvd
  have hpos := (class1SlopeDatum ctx).hK₀_pos
  have hmem : 2 * (class1SlopeDatum ctx).K₀ + 1 ∈ Nat.divisors 113 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 113 = {1, 113} from by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hK : (class1SlopeDatum ctx).K₀ = 56 := by omega
  exact ftClass1Fibre_empty_of_datum_113_56 ctx hq hK

/-- **Modulus-123 closure**: every admissible pin (`2K₀+1 ∣ 123`) has a band-4-free
cycle - the class-1 fibre is empty on every `q = 123` shell. -/
theorem ftClass1Fibre_empty_of_modulus_eq_123 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 123) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq] at hdvd
  have hpos := (class1SlopeDatum ctx).hK₀_pos
  have hmem : 2 * (class1SlopeDatum ctx).K₀ + 1 ∈ Nat.divisors 123 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 123 = {1, 3, 41, 123} from by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hK : (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 20 ∨ (class1SlopeDatum ctx).K₀ = 61 := by omega
  rcases hK with hK | hK | hK
  · exact ftClass1Fibre_empty_of_datum_123_1 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_123_20 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_123_61 ctx hq hK

/-- **Modulus-127 closure**: every admissible pin (`2K₀+1 ∣ 127`) has a band-4-free
cycle - the class-1 fibre is empty on every `q = 127` shell. -/
theorem ftClass1Fibre_empty_of_modulus_eq_127 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 127) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq] at hdvd
  have hpos := (class1SlopeDatum ctx).hK₀_pos
  have hmem : 2 * (class1SlopeDatum ctx).K₀ + 1 ∈ Nat.divisors 127 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 127 = {1, 127} from by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hK : (class1SlopeDatum ctx).K₀ = 63 := by omega
  exact ftClass1Fibre_empty_of_datum_127_63 ctx hq hK

/-- **Modulus-129 closure**: every admissible pin (`2K₀+1 ∣ 129`) has a band-4-free
cycle - the class-1 fibre is empty on every `q = 129` shell. -/
theorem ftClass1Fibre_empty_of_modulus_eq_129 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 129) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq] at hdvd
  have hpos := (class1SlopeDatum ctx).hK₀_pos
  have hmem : 2 * (class1SlopeDatum ctx).K₀ + 1 ∈ Nat.divisors 129 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 129 = {1, 3, 43, 129} from by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hK : (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 21 ∨ (class1SlopeDatum ctx).K₀ = 64 := by omega
  rcases hK with hK | hK | hK
  · exact ftClass1Fibre_empty_of_datum_129_1 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_129_21 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_129_64 ctx hq hK

/-- **Modulus-151 closure**: every admissible pin (`2K₀+1 ∣ 151`) has a band-4-free
cycle - the class-1 fibre is empty on every `q = 151` shell. -/
theorem ftClass1Fibre_empty_of_modulus_eq_151 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 151) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq] at hdvd
  have hpos := (class1SlopeDatum ctx).hK₀_pos
  have hmem : 2 * (class1SlopeDatum ctx).K₀ + 1 ∈ Nat.divisors 151 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 151 = {1, 151} from by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hK : (class1SlopeDatum ctx).K₀ = 75 := by omega
  exact ftClass1Fibre_empty_of_datum_151_75 ctx hq hK

/-- **Modulus-157 closure**: every admissible pin (`2K₀+1 ∣ 157`) has a band-4-free
cycle - the class-1 fibre is empty on every `q = 157` shell. -/
theorem ftClass1Fibre_empty_of_modulus_eq_157 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 157) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq] at hdvd
  have hpos := (class1SlopeDatum ctx).hK₀_pos
  have hmem : 2 * (class1SlopeDatum ctx).K₀ + 1 ∈ Nat.divisors 157 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 157 = {1, 157} from by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hK : (class1SlopeDatum ctx).K₀ = 78 := by omega
  exact ftClass1Fibre_empty_of_datum_157_78 ctx hq hK

/-- **Modulus-171 closure**: every admissible pin (`2K₀+1 ∣ 171`) has a band-4-free
cycle - the class-1 fibre is empty on every `q = 171` shell. -/
theorem ftClass1Fibre_empty_of_modulus_eq_171 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 171) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  have hdvd : 2 * (class1SlopeDatum ctx).K₀ + 1 ∣ (class1SlopeDatum ctx).q := by
    rw [class1SlopeDatum_K₀_eq ctx]
    exact class1SlopeDatum_H_dvd ctx
  rw [hq] at hdvd
  have hpos := (class1SlopeDatum ctx).hK₀_pos
  have hmem : 2 * (class1SlopeDatum ctx).K₀ + 1 ∈ Nat.divisors 171 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 171 = {1, 3, 9, 19, 57, 171} from by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hK : (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 4 ∨ (class1SlopeDatum ctx).K₀ = 9 ∨ (class1SlopeDatum ctx).K₀ = 28 ∨ (class1SlopeDatum ctx).K₀ = 85 := by omega
  rcases hK with hK | hK | hK | hK | hK
  · exact ftClass1Fibre_empty_of_datum_171_1 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_171_4 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_171_9 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_171_28 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_171_85 ctx hq hK

/-- **The extended closed-moduli list**: the odd moduli in `(100, 200)` whose class-1
fibre is closed by the cycle checks of this module - the `q < 200` extension of the
wave-3 `class1ClosedModuli`. -/
def ftClass1ClosedModuli200 : Finset ℕ := {109, 113, 123, 127, 129, 151, 157, 171}

/-- **The extended closed-moduli dispatch**: the class-1 fibre is empty on every shell
whose orbit modulus lies in `ftClass1ClosedModuli200`. -/
theorem ftClass1Fibre_empty_of_mem_extended (ctx : ActualFailureContext)
    (h : (class1SlopeDatum ctx).q ∈ ftClass1ClosedModuli200) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  have h' : (class1SlopeDatum ctx).q = 109 ∨ (class1SlopeDatum ctx).q = 113 ∨ (class1SlopeDatum ctx).q = 123 ∨ (class1SlopeDatum ctx).q = 127 ∨ (class1SlopeDatum ctx).q = 129 ∨ (class1SlopeDatum ctx).q = 151 ∨ (class1SlopeDatum ctx).q = 157 ∨ (class1SlopeDatum ctx).q = 171 := by
    simpa [ftClass1ClosedModuli200] using h
  rcases h' with h' | h' | h' | h' | h' | h' | h' | h'
  · exact ftClass1Fibre_empty_of_modulus_eq_109 ctx h'
  · exact ftClass1Fibre_empty_of_modulus_eq_113 ctx h'
  · exact ftClass1Fibre_empty_of_modulus_eq_123 ctx h'
  · exact ftClass1Fibre_empty_of_modulus_eq_127 ctx h'
  · exact ftClass1Fibre_empty_of_modulus_eq_129 ctx h'
  · exact ftClass1Fibre_empty_of_modulus_eq_151 ctx h'
  · exact ftClass1Fibre_empty_of_modulus_eq_157 ctx h'
  · exact ftClass1Fibre_empty_of_modulus_eq_171 ctx h'

/-- **The 49 band-4-free pairs of the sweep** (including those inside partially closed
moduli) - at each the class-1 routed fibre is empty. -/
def FtClass1Band4FreeDatum (ctx : ActualFailureContext) : Prop :=
  ((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 3)
  ∨ ((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 10)
  ∨ ((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 17)
  ∨ ((class1SlopeDatum ctx).q = 109 ∧ (class1SlopeDatum ctx).K₀ = 54)
  ∨ ((class1SlopeDatum ctx).q = 113 ∧ (class1SlopeDatum ctx).K₀ = 56)
  ∨ ((class1SlopeDatum ctx).q = 117 ∧ (class1SlopeDatum ctx).K₀ = 6)
  ∨ ((class1SlopeDatum ctx).q = 117 ∧ (class1SlopeDatum ctx).K₀ = 19)
  ∨ ((class1SlopeDatum ctx).q = 117 ∧ (class1SlopeDatum ctx).K₀ = 58)
  ∨ ((class1SlopeDatum ctx).q = 119 ∧ (class1SlopeDatum ctx).K₀ = 3)
  ∨ ((class1SlopeDatum ctx).q = 123 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 123 ∧ (class1SlopeDatum ctx).K₀ = 20)
  ∨ ((class1SlopeDatum ctx).q = 123 ∧ (class1SlopeDatum ctx).K₀ = 61)
  ∨ ((class1SlopeDatum ctx).q = 127 ∧ (class1SlopeDatum ctx).K₀ = 63)
  ∨ ((class1SlopeDatum ctx).q = 129 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 129 ∧ (class1SlopeDatum ctx).K₀ = 21)
  ∨ ((class1SlopeDatum ctx).q = 129 ∧ (class1SlopeDatum ctx).K₀ = 64)
  ∨ ((class1SlopeDatum ctx).q = 133 ∧ (class1SlopeDatum ctx).K₀ = 66)
  ∨ ((class1SlopeDatum ctx).q = 135 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 135 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 135 ∧ (class1SlopeDatum ctx).K₀ = 4)
  ∨ ((class1SlopeDatum ctx).q = 147 ∧ (class1SlopeDatum ctx).K₀ = 3)
  ∨ ((class1SlopeDatum ctx).q = 147 ∧ (class1SlopeDatum ctx).K₀ = 24)
  ∨ ((class1SlopeDatum ctx).q = 151 ∧ (class1SlopeDatum ctx).K₀ = 75)
  ∨ ((class1SlopeDatum ctx).q = 155 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 155 ∧ (class1SlopeDatum ctx).K₀ = 77)
  ∨ ((class1SlopeDatum ctx).q = 157 ∧ (class1SlopeDatum ctx).K₀ = 78)
  ∨ ((class1SlopeDatum ctx).q = 165 ∧ (class1SlopeDatum ctx).K₀ = 5)
  ∨ ((class1SlopeDatum ctx).q = 165 ∧ (class1SlopeDatum ctx).K₀ = 27)
  ∨ ((class1SlopeDatum ctx).q = 165 ∧ (class1SlopeDatum ctx).K₀ = 82)
  ∨ ((class1SlopeDatum ctx).q = 171 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 171 ∧ (class1SlopeDatum ctx).K₀ = 4)
  ∨ ((class1SlopeDatum ctx).q = 171 ∧ (class1SlopeDatum ctx).K₀ = 9)
  ∨ ((class1SlopeDatum ctx).q = 171 ∧ (class1SlopeDatum ctx).K₀ = 28)
  ∨ ((class1SlopeDatum ctx).q = 171 ∧ (class1SlopeDatum ctx).K₀ = 85)
  ∨ ((class1SlopeDatum ctx).q = 183 ∧ (class1SlopeDatum ctx).K₀ = 91)
  ∨ ((class1SlopeDatum ctx).q = 187 ∧ (class1SlopeDatum ctx).K₀ = 5)
  ∨ ((class1SlopeDatum ctx).q = 189 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 189 ∧ (class1SlopeDatum ctx).K₀ = 3)
  ∨ ((class1SlopeDatum ctx).q = 189 ∧ (class1SlopeDatum ctx).K₀ = 4)
  ∨ ((class1SlopeDatum ctx).q = 189 ∧ (class1SlopeDatum ctx).K₀ = 31)
  ∨ ((class1SlopeDatum ctx).q = 189 ∧ (class1SlopeDatum ctx).K₀ = 94)
  ∨ ((class1SlopeDatum ctx).q = 195 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 195 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 195 ∧ (class1SlopeDatum ctx).K₀ = 6)
  ∨ ((class1SlopeDatum ctx).q = 195 ∧ (class1SlopeDatum ctx).K₀ = 7)
  ∨ ((class1SlopeDatum ctx).q = 195 ∧ (class1SlopeDatum ctx).K₀ = 32)
  ∨ ((class1SlopeDatum ctx).q = 195 ∧ (class1SlopeDatum ctx).K₀ = 97)

/-- Every swept band-4-free pair empties the class-1 routed fibre. -/
theorem ftClass1Fibre_empty_of_band4FreeDatum (ctx : ActualFailureContext)
    (h : FtClass1Band4FreeDatum ctx) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  rcases h with ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩
  · exact ftClass1Fibre_empty_of_datum_105_1 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_105_2 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_105_3 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_105_10 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_105_17 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_109_54 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_113_56 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_117_6 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_117_19 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_117_58 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_119_3 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_123_1 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_123_20 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_123_61 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_127_63 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_129_1 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_129_21 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_129_64 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_133_66 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_135_1 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_135_2 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_135_4 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_147_3 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_147_24 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_151_75 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_155_2 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_155_77 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_157_78 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_165_5 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_165_27 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_165_82 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_171_1 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_171_4 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_171_9 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_171_28 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_171_85 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_183_91 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_187_5 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_189_1 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_189_3 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_189_4 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_189_31 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_189_94 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_195_1 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_195_2 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_195_6 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_195_7 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_195_32 ctx hq hK
  · exact ftClass1Fibre_empty_of_datum_195_97 ctx hq hK

/-- **The class-1 bridge at `200` (additive)**: the swept part (closed moduli + the 49
band-4-free pairs) plus the per-ctx demand on the RELIEVED `q < 200` remainder plus
band-4-free periods on `200 <= q` rebuild the `Class1PairResidual.deep` field shape
VERBATIM (the `class1PairDeep_split_at_tail` consumer of `ModulusTailCriteria`, pushed
from `101` to `200`). -/
theorem ftClass1Deep_split_at_200
    (hlow : ∀ ctx : ActualFailureContext,
      1 ≤ ctx.n24CarryData.r →
      64 ∣ shellLadderDepth ctx →
      9 ≤ (class1SlopeDatum ctx).q →
      ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
      (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
      ¬ Class1DatumClosed ctx →
      ¬ Class1GcdWindowMiss ctx →
      (class1SlopeDatum ctx).q ∉ ftClass1ClosedModuli200 →
      ¬ FtClass1Band4FreeDatum ctx →
      (class1SlopeDatum ctx).q < 200 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅)
    (htail : ∀ ctx : ActualFailureContext,
      1 ≤ ctx.n24CarryData.r →
      200 ≤ (class1SlopeDatum ctx).q →
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
  by_cases hext : (class1SlopeDatum ctx).q ∈ ftClass1ClosedModuli200
  · exact ftClass1Fibre_empty_of_mem_extended ctx hext
  by_cases hA : FtClass1Band4FreeDatum ctx
  · exact ftClass1Fibre_empty_of_band4FreeDatum ctx hA
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 200 with hlt | hge
  · exact hlow ctx hr hdvd h9 hwin hcl hdc hgcd hext hA hlt
  · exact class1Tail_of_band4FreePeriod ctx (htail ctx hr hge)

/-! ### The exceptional-cofactor cross (the wave-6 order criteria applied) -/

/-- The order cofactor of the survivor `(105,7)` (the band-4 fixed point `K = 7`)
is `15`. -/
theorem ftCofactor_105_7 : orbitOrderModulus 105 7 = 15 := by
  have e0 : slopeOrbit 105 7 0 = 7 := rfl
  have e1 : slopeOrbit 105 7 1 = 7 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold orbitOrderModulus
  rw [e1]
  decide

/-- The order cofactor of the survivor `(155,15)` is `31`. -/
theorem ftCofactor_155_15 : orbitOrderModulus 155 15 = 31 := by
  have e0 : slopeOrbit 155 15 0 = 15 := rfl
  have e1 : slopeOrbit 155 15 1 = 85 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold orbitOrderModulus
  rw [e1]
  decide

/-- **`(105,7)` is order-exceptional**: its cofactor `15` lies in the Mersenne
small-order family, with `ord_2 <= 6` - the order-floor pruning of the wave-6
criteria is NOT live there. -/
theorem ftSurvivor_105_7_exceptional :
    orbitOrderModulus 105 7 ∈ mersenneSmallOrderModuli
      ∧ orderOf (2 : ZMod (orbitOrderModulus 105 7)) ≤ 6 := by
  rw [ftCofactor_105_7]
  exact ⟨by decide, orderOf_two_le_six_of_mem (by decide)⟩

/-- **`(155,15)` is order-exceptional**: its cofactor `31` lies in the Mersenne
small-order family, with `ord_2 <= 6`. -/
theorem ftSurvivor_155_15_exceptional :
    orbitOrderModulus 155 15 ∈ mersenneSmallOrderModuli
      ∧ orderOf (2 : ZMod (orbitOrderModulus 155 15)) ≤ 6 := by
  rw [ftCofactor_155_15]
  exact ⟨by decide, orderOf_two_le_six_of_mem (by decide)⟩

/-! ## Part 3.  The run/densepack sweeps: odd `64 <= q < 128` -/

/-- **Generic run closer**: a band-`{1,4}`-free period makes the class-5 cycle band
empty, so `Class5CycleNumericCloses` holds with a zero count. -/
theorem ftClass5CycleNumeric_of_cycle_band_free (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 1
        ∧ canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 4) :
    Class5CycleNumericCloses ctx := by
  refine ⟨c, hc, hper, ?_⟩
  have hempty : class5CycleBand ctx c = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro j hj
    rw [mem_class5CycleBand] at hj
    have h := hband j hj.1.1 hj.1.2
    rcases hj.2 with h1 | h4
    · exact h.1 h1
    · exact h.2 h4
  rw [hempty, Finset.card_empty, Nat.zero_mul]
  have hrhs : (0 : ℝ) ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
      * ((supportShell ctx.d ctx.X).card : ℝ) :=
    mul_nonneg
      (div_nonneg
        (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
        (by norm_num))
      (Nat.cast_nonneg _)
  simpa using hrhs

/-- `(93,15)`: cycle `[27, 15]` (period `2`, bands `2, 3`) - band-`{1,4}`-free, the ONLY
such divisor-pin pair on odd `64 <= q < 128`. -/
private theorem ftR_93_15 :
    slopeOrbit 93 15 (1 + 2) = slopeOrbit 93 15 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 →
          canonGap 93 (slopeOrbit 93 15 j) ≠ 1 ∧ canonGap 93 (slopeOrbit 93 15 j) ≠ 4 := by
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
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 93) (v := 27) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 93) (v := 15) (g := 2) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- **`(93,15)` closes the run cycle numeric outright** - the unique mid-band run
closure of the sweep. -/
theorem ftRunCloses_of_datum_93_15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 93) (hK : (class1SlopeDatum ctx).K₀ = 15) :
    Class5CycleNumericCloses ctx := by
  refine ftClass5CycleNumeric_of_cycle_band_free ctx (c := 2) (by norm_num) ?_ ?_
  · rw [hq, hK]
    exact slopeOrbit_period_of_return ftR_93_15.1
  · rw [hq, hK]
    exact ftR_93_15.2

/-- **The run bridge at `128` (additive)**: the enumerated part (`q < 64`) plus the
swept mid band (`64 <= q < 128`, relieved of the closed pair `(93,15)`) plus the tail
(`128 <= q`) rebuild `RunCycleNumericSettlementHyp` VERBATIM. -/
theorem ftRunSettlement_split_at_128
    (hlow : ∀ ctx : ActualFailureContext, 1 ≤ ctx.n24CarryData.r →
      (class1SlopeDatum ctx).q < 64 →
      Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx)
    (hmid : ∀ ctx : ActualFailureContext, 1 ≤ ctx.n24CarryData.r →
      64 ≤ (class1SlopeDatum ctx).q → (class1SlopeDatum ctx).q < 128 →
      ¬ ((class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 15) →
      Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx)
    (htail : ∀ ctx : ActualFailureContext, 1 ≤ ctx.n24CarryData.r →
      128 ≤ (class1SlopeDatum ctx).q →
      Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx) :
    RunCycleNumericSettlementHyp := by
  intro ctx hr
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 64 with h64 | h64
  · exact hlow ctx hr h64
  · rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 128 with h128 | h128
    · by_cases h93 : (class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 15
      · exact Or.inr (ftRunCloses_of_datum_93_15 ctx h93.1 h93.2)
      · exact hmid ctx hr h64 h128 h93
    · exact htail ctx hr h128

/-! ### The nineteen densepack band-3-free closures -/

/-- `(65,2)`: cycle `[63, 61, 57, 49, 33, 1]` (period `6`, bands `1, 1, 1, 1, 1, 7`) - band-3-free. -/
private theorem ftC3_65_2 :
    slopeOrbit 65 2 (1 + 6) = slopeOrbit 65 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 65 (slopeOrbit 65 2 j) ≠ 3 := by
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
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 65) (v := 63) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 65) (v := 61) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 65) (v := 57) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 65) (v := 49) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 65) (v := 33) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 65) (v := 1) (g := 6) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(65,2)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_65_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 65) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    Class3CycleBand3Free ctx :=
  ⟨6, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_65_2.1,
    by rw [hq, hK]; exact ftC3_65_2.2⟩

/-- `(65,6)`: cycle `[31, 59, 53, 41, 17, 3]` (period `6`, bands `2, 1, 1, 1, 2, 5`) - band-3-free. -/
private theorem ftC3_65_6 :
    slopeOrbit 65 6 (1 + 6) = slopeOrbit 65 6 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 65 (slopeOrbit 65 6 j) ≠ 3 := by
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
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 65) (v := 31) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 65) (v := 59) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 65) (v := 53) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 65) (v := 41) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 65) (v := 17) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 65) (v := 3) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(65,6)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_65_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 65) (hK : (class1SlopeDatum ctx).K₀ = 6) :
    Class3CycleBand3Free ctx :=
  ⟨6, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_65_6.1,
    by rw [hq, hK]; exact ftC3_65_6.2⟩

/-- `(65,32)`: cycle `[63, 61, 57, 49, 33, 1]` (period `6`, bands `1, 1, 1, 1, 1, 7`) - band-3-free. -/
private theorem ftC3_65_32 :
    slopeOrbit 65 32 (1 + 6) = slopeOrbit 65 32 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 65 (slopeOrbit 65 32 j) ≠ 3 := by
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
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 65) (v := 63) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 65) (v := 61) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 65) (v := 57) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 65) (v := 49) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 65) (v := 33) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 65) (v := 1) (g := 6) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(65,32)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_65_32 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 65) (hK : (class1SlopeDatum ctx).K₀ = 32) :
    Class3CycleBand3Free ctx :=
  ⟨6, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_65_32.1,
    by rw [hq, hK]; exact ftC3_65_32.2⟩

/-- `(73,36)`: cycle `[71, 69, 65, 57, 41, 9]` (period `6`, bands `1, 1, 1, 1, 1, 4`) - band-3-free. -/
private theorem ftC3_73_36 :
    slopeOrbit 73 36 (1 + 6) = slopeOrbit 73 36 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 73 (slopeOrbit 73 36 j) ≠ 3 := by
  have e0 : slopeOrbit 73 36 0 = 36 := rfl
  have e1 : slopeOrbit 73 36 1 = 71 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 73 36 2 = 69 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 73 36 3 = 65 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 73 36 4 = 57 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 73 36 5 = 41 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 73 36 6 = 9 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 73 36 7 = 71 :=
    slopeOrbit_step_eval 6 3 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 73 36 7 = slopeOrbit 73 36 1
    rw [e7, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 73) (v := 71) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 73) (v := 69) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 73) (v := 65) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 73) (v := 57) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 73) (v := 41) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 73) (v := 9) (g := 3) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(73,36)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_73_36 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 73) (hK : (class1SlopeDatum ctx).K₀ = 36) :
    Class3CycleBand3Free ctx :=
  ⟨6, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_73_36.1,
    by rw [hq, hK]; exact ftC3_73_36.2⟩

/-- `(75,12)`: cycle `[21, 9, 69, 63, 51, 27, 33, 57, 39, 3]` (period `10`, bands `2, 4, 1, 1, 1, 2, 2, 1, 1, 5`) - band-3-free. -/
private theorem ftC3_75_12 :
    slopeOrbit 75 12 (1 + 10) = slopeOrbit 75 12 1
      ∧ ∀ j, 1 ≤ j → j ≤ 10 → canonGap 75 (slopeOrbit 75 12 j) ≠ 3 := by
  have e0 : slopeOrbit 75 12 0 = 12 := rfl
  have e1 : slopeOrbit 75 12 1 = 21 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 75 12 2 = 9 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 75 12 3 = 69 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 75 12 4 = 63 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 75 12 5 = 51 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 75 12 6 = 27 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 75 12 7 = 33 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 75 12 8 = 57 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 75 12 9 = 39 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 75 12 10 = 3 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 75 12 11 = 21 :=
    slopeOrbit_step_eval 10 4 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 75 12 11 = slopeOrbit 75 12 1
    rw [e11, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 75) (v := 21) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 75) (v := 9) (g := 3) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 75) (v := 69) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 75) (v := 63) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 75) (v := 51) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 75) (v := 27) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 75) (v := 33) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 75) (v := 57) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 75) (v := 39) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 75) (v := 3) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(75,12)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_75_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 12) :
    Class3CycleBand3Free ctx :=
  ⟨10, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_75_12.1,
    by rw [hq, hK]; exact ftC3_75_12.2⟩

/-- `(85,2)`: cycle `[43, 1]` (period `2`, bands `1, 7`) - band-3-free. -/
private theorem ftC3_85_2 :
    slopeOrbit 85 2 (1 + 2) = slopeOrbit 85 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → canonGap 85 (slopeOrbit 85 2 j) ≠ 3 := by
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
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 85) (v := 43) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 85) (v := 1) (g := 6) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(85,2)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_85_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 85) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    Class3CycleBand3Free ctx :=
  ⟨2, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_85_2.1,
    by rw [hq, hK]; exact ftC3_85_2.2⟩

/-- `(85,8)`: cycle `[43, 1]` (period `2`, bands `1, 7`) - band-3-free. -/
private theorem ftC3_85_8 :
    slopeOrbit 85 8 (1 + 2) = slopeOrbit 85 8 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → canonGap 85 (slopeOrbit 85 8 j) ≠ 3 := by
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
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 85) (v := 43) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 85) (v := 1) (g := 6) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(85,8)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_85_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 85) (hK : (class1SlopeDatum ctx).K₀ = 8) :
    Class3CycleBand3Free ctx :=
  ⟨2, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_85_8.1,
    by rw [hq, hK]; exact ftC3_85_8.2⟩

/-- `(89,44)`: cycle `[87, 85, 81, 73, 57, 25, 11]` (period `7`, bands `1, 1, 1, 1, 1, 2, 4`) - band-3-free. -/
private theorem ftC3_89_44 :
    slopeOrbit 89 44 (1 + 7) = slopeOrbit 89 44 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 → canonGap 89 (slopeOrbit 89 44 j) ≠ 3 := by
  have e0 : slopeOrbit 89 44 0 = 44 := rfl
  have e1 : slopeOrbit 89 44 1 = 87 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 89 44 2 = 85 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 89 44 3 = 81 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 89 44 4 = 73 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 89 44 5 = 57 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 89 44 6 = 25 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 89 44 7 = 11 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 89 44 8 = 87 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 89 44 8 = slopeOrbit 89 44 1
    rw [e8, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 89) (v := 87) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 89) (v := 85) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 89) (v := 81) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 89) (v := 73) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 89) (v := 57) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 89) (v := 25) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 89) (v := 11) (g := 3) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(89,44)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_89_44 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 89) (hK : (class1SlopeDatum ctx).K₀ = 44) :
    Class3CycleBand3Free ctx :=
  ⟨7, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_89_44.1,
    by rw [hq, hK]; exact ftC3_89_44.2⟩

/-- `(91,3)`: cycle `[5, 69, 47, 3]` (period `4`, bands `5, 1, 1, 5`) - band-3-free. -/
private theorem ftC3_91_3 :
    slopeOrbit 91 3 (1 + 4) = slopeOrbit 91 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 4 → canonGap 91 (slopeOrbit 91 3 j) ≠ 3 := by
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
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 91) (v := 5) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 91) (v := 69) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 91) (v := 47) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 91) (v := 3) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(91,3)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_91_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 91) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    Class3CycleBand3Free ctx :=
  ⟨4, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_91_3.1,
    by rw [hq, hK]; exact ftC3_91_3.2⟩

/-- `(91,6)`: cycle `[5, 69, 47, 3]` (period `4`, bands `5, 1, 1, 5`) - band-3-free. -/
private theorem ftC3_91_6 :
    slopeOrbit 91 6 (1 + 4) = slopeOrbit 91 6 1
      ∧ ∀ j, 1 ≤ j → j ≤ 4 → canonGap 91 (slopeOrbit 91 6 j) ≠ 3 := by
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
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 91) (v := 5) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 91) (v := 69) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 91) (v := 47) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 91) (v := 3) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(91,6)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_91_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 91) (hK : (class1SlopeDatum ctx).K₀ = 6) :
    Class3CycleBand3Free ctx :=
  ⟨4, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_91_6.1,
    by rw [hq, hK]; exact ftC3_91_6.2⟩

/-- `(93,1)`: cycle `[35, 47, 1]` (period `3`, bands `2, 1, 7`) - band-3-free. -/
private theorem ftC3_93_1 :
    slopeOrbit 93 1 (1 + 3) = slopeOrbit 93 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 3 → canonGap 93 (slopeOrbit 93 1 j) ≠ 3 := by
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
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 93) (v := 35) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 93) (v := 47) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 93) (v := 1) (g := 6) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(93,1)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_93_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 93) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    Class3CycleBand3Free ctx :=
  ⟨3, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_93_1.1,
    by rw [hq, hK]; exact ftC3_93_1.2⟩

/-- `(97,48)`: cycle `[95, 93, 89, 81, 65, 33, 35, 43, 75, 53, 9, 47, 91, 85, 73, 49, 1, 31, 27, 11, 79, 61, 25, 3]` (period `24`, bands `1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 7, 2, 2, 4, 1, 1, 2, 6`) - band-3-free. -/
private theorem ftC3_97_48 :
    slopeOrbit 97 48 (1 + 24) = slopeOrbit 97 48 1
      ∧ ∀ j, 1 ≤ j → j ≤ 24 → canonGap 97 (slopeOrbit 97 48 j) ≠ 3 := by
  have e0 : slopeOrbit 97 48 0 = 48 := rfl
  have e1 : slopeOrbit 97 48 1 = 95 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 97 48 2 = 93 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 97 48 3 = 89 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 97 48 4 = 81 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 97 48 5 = 65 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 97 48 6 = 33 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 97 48 7 = 35 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 97 48 8 = 43 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 97 48 9 = 75 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 97 48 10 = 53 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 97 48 11 = 9 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 97 48 12 = 47 :=
    slopeOrbit_step_eval 11 3 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 97 48 13 = 91 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 97 48 14 = 85 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 97 48 15 = 73 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 97 48 16 = 49 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 97 48 17 = 1 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 97 48 18 = 31 :=
    slopeOrbit_step_eval 17 6 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 97 48 19 = 27 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 97 48 20 = 11 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 97 48 21 = 79 :=
    slopeOrbit_step_eval 20 3 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 97 48 22 = 61 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 97 48 23 = 25 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 97 48 24 = 3 :=
    slopeOrbit_step_eval 23 1 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 97 48 25 = 95 :=
    slopeOrbit_step_eval 24 5 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 97 48 25 = slopeOrbit 97 48 1
    rw [e25, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 97) (v := 95) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 97) (v := 93) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 97) (v := 89) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 97) (v := 81) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 97) (v := 65) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 97) (v := 33) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 97) (v := 35) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 97) (v := 43) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e9, canonGap_eval (q := 97) (v := 75) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e10, canonGap_eval (q := 97) (v := 53) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e11, canonGap_eval (q := 97) (v := 9) (g := 3) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e12, canonGap_eval (q := 97) (v := 47) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e13, canonGap_eval (q := 97) (v := 91) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e14, canonGap_eval (q := 97) (v := 85) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e15, canonGap_eval (q := 97) (v := 73) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e16, canonGap_eval (q := 97) (v := 49) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e17, canonGap_eval (q := 97) (v := 1) (g := 6) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e18, canonGap_eval (q := 97) (v := 31) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e19, canonGap_eval (q := 97) (v := 27) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e20, canonGap_eval (q := 97) (v := 11) (g := 3) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e21, canonGap_eval (q := 97) (v := 79) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e22, canonGap_eval (q := 97) (v := 61) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e23, canonGap_eval (q := 97) (v := 25) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e24, canonGap_eval (q := 97) (v := 3) (g := 5) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(97,48)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_97_48 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 97) (hK : (class1SlopeDatum ctx).K₀ = 48) :
    Class3CycleBand3Free ctx :=
  ⟨24, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_97_48.1,
    by rw [hq, hK]; exact ftC3_97_48.2⟩

/-- `(105,3)`: cycle `[87, 69, 33, 27, 3]` (period `5`, bands `1, 1, 2, 2, 6`) - band-3-free. -/
private theorem ftC3_105_3 :
    slopeOrbit 105 3 (1 + 5) = slopeOrbit 105 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 5 → canonGap 105 (slopeOrbit 105 3 j) ≠ 3 := by
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
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 105) (v := 87) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 105) (v := 69) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 105) (v := 33) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 105) (v := 27) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 105) (v := 3) (g := 5) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(105,3)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_105_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    Class3CycleBand3Free ctx :=
  ⟨5, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_105_3.1,
    by rw [hq, hK]; exact ftC3_105_3.2⟩

/-- `(105,7)`: cycle `[7]` (period `1`, bands `4`) - band-3-free. -/
private theorem ftC3_105_7 :
    slopeOrbit 105 7 (1 + 1) = slopeOrbit 105 7 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → canonGap 105 (slopeOrbit 105 7 j) ≠ 3 := by
  have e0 : slopeOrbit 105 7 0 = 7 := rfl
  have e1 : slopeOrbit 105 7 1 = 7 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 105 7 2 = 7 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 105 7 2 = slopeOrbit 105 7 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 105) (v := 7) (g := 3) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(105,7)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_105_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 7) :
    Class3CycleBand3Free ctx :=
  ⟨1, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_105_7.1,
    by rw [hq, hK]; exact ftC3_105_7.2⟩

/-- `(105,10)`: cycle `[55, 5]` (period `2`, bands `1, 5`) - band-3-free. -/
private theorem ftC3_105_10 :
    slopeOrbit 105 10 (1 + 2) = slopeOrbit 105 10 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → canonGap 105 (slopeOrbit 105 10 j) ≠ 3 := by
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
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 105) (v := 55) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 105) (v := 5) (g := 4) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(105,10)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_105_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    Class3CycleBand3Free ctx :=
  ⟨2, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_105_10.1,
    by rw [hq, hK]; exact ftC3_105_10.2⟩

/-- `(105,52)`: cycle `[103, 101, 97, 89, 73, 41, 59, 13]` (period `8`, bands `1, 1, 1, 1, 1, 2, 1, 4`) - band-3-free. -/
private theorem ftC3_105_52 :
    slopeOrbit 105 52 (1 + 8) = slopeOrbit 105 52 1
      ∧ ∀ j, 1 ≤ j → j ≤ 8 → canonGap 105 (slopeOrbit 105 52 j) ≠ 3 := by
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
  refine ⟨?_, ?_⟩
  · show slopeOrbit 105 52 9 = slopeOrbit 105 52 1
    rw [e9, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 105) (v := 103) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 105) (v := 101) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 105) (v := 97) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 105) (v := 89) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 105) (v := 73) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 105) (v := 41) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e7, canonGap_eval (q := 105) (v := 59) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e8, canonGap_eval (q := 105) (v := 13) (g := 3) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(105,52)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_105_52 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 52) :
    Class3CycleBand3Free ctx :=
  ⟨8, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_105_52.1,
    by rw [hq, hK]; exact ftC3_105_52.2⟩

/-- `(117,1)`: cycle `[11, 59, 1]` (period `3`, bands `4, 1, 7`) - band-3-free. -/
private theorem ftC3_117_1 :
    slopeOrbit 117 1 (1 + 3) = slopeOrbit 117 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 3 → canonGap 117 (slopeOrbit 117 1 j) ≠ 3 := by
  have e0 : slopeOrbit 117 1 0 = 1 := rfl
  have e1 : slopeOrbit 117 1 1 = 11 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 117 1 2 = 59 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 117 1 3 = 1 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 117 1 4 = 11 :=
    slopeOrbit_step_eval 3 6 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 117 1 4 = slopeOrbit 117 1 1
    rw [e4, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 117) (v := 11) (g := 3) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 117) (v := 59) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 117) (v := 1) (g := 6) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(117,1)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_117_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 117) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    Class3CycleBand3Free ctx :=
  ⟨3, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_117_1.1,
    by rw [hq, hK]; exact ftC3_117_1.2⟩

/-- `(117,4)`: cycle `[11, 59, 1]` (period `3`, bands `4, 1, 7`) - band-3-free. -/
private theorem ftC3_117_4 :
    slopeOrbit 117 4 (1 + 3) = slopeOrbit 117 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 3 → canonGap 117 (slopeOrbit 117 4 j) ≠ 3 := by
  have e0 : slopeOrbit 117 4 0 = 4 := rfl
  have e1 : slopeOrbit 117 4 1 = 11 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 117 4 2 = 59 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 117 4 3 = 1 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 117 4 4 = 11 :=
    slopeOrbit_step_eval 3 6 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 117 4 4 = slopeOrbit 117 4 1
    rw [e4, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 117) (v := 11) (g := 3) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 117) (v := 59) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 117) (v := 1) (g := 6) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(117,4)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_117_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 117) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    Class3CycleBand3Free ctx :=
  ⟨3, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_117_4.1,
    by rw [hq, hK]; exact ftC3_117_4.2⟩

/-- `(127,63)`: cycle `[125, 123, 119, 111, 95, 63]` (period `6`, bands `1, 1, 1, 1, 1, 2`) - band-3-free. -/
private theorem ftC3_127_63 :
    slopeOrbit 127 63 (1 + 6) = slopeOrbit 127 63 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 → canonGap 127 (slopeOrbit 127 63 j) ≠ 3 := by
  have e0 : slopeOrbit 127 63 0 = 63 := rfl
  have e1 : slopeOrbit 127 63 1 = 125 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 127 63 2 = 123 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 127 63 3 = 119 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 127 63 4 = 111 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 127 63 5 = 95 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 127 63 6 = 63 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 127 63 7 = 125 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 127 63 7 = slopeOrbit 127 63 1
    rw [e7, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1, canonGap_eval (q := 127) (v := 125) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e2, canonGap_eval (q := 127) (v := 123) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e3, canonGap_eval (q := 127) (v := 119) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e4, canonGap_eval (q := 127) (v := 111) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e5, canonGap_eval (q := 127) (v := 95) (g := 0) (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [e6, canonGap_eval (q := 127) (v := 63) (g := 1) (by norm_num) (by norm_num) (by norm_num)]; decide

/-- `(127,63)` passes the densepack band-3 cycle check. -/
theorem ftClass3Band3Free_of_datum_127_63 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 127) (hK : (class1SlopeDatum ctx).K₀ = 63) :
    Class3CycleBand3Free ctx :=
  ⟨6, by norm_num,
    by rw [hq, hK]; exact slopeOrbit_period_of_return ftC3_127_63.1,
    by rw [hq, hK]; exact ftC3_127_63.2⟩

/-- **The nineteen band-3-free densepack pairs of the sweep.** -/
def FtDensePackBand3FreeDatum (ctx : ActualFailureContext) : Prop :=
  ((class1SlopeDatum ctx).q = 65 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 65 ∧ (class1SlopeDatum ctx).K₀ = 6)
  ∨ ((class1SlopeDatum ctx).q = 65 ∧ (class1SlopeDatum ctx).K₀ = 32)
  ∨ ((class1SlopeDatum ctx).q = 73 ∧ (class1SlopeDatum ctx).K₀ = 36)
  ∨ ((class1SlopeDatum ctx).q = 75 ∧ (class1SlopeDatum ctx).K₀ = 12)
  ∨ ((class1SlopeDatum ctx).q = 85 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 85 ∧ (class1SlopeDatum ctx).K₀ = 8)
  ∨ ((class1SlopeDatum ctx).q = 89 ∧ (class1SlopeDatum ctx).K₀ = 44)
  ∨ ((class1SlopeDatum ctx).q = 91 ∧ (class1SlopeDatum ctx).K₀ = 3)
  ∨ ((class1SlopeDatum ctx).q = 91 ∧ (class1SlopeDatum ctx).K₀ = 6)
  ∨ ((class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 97 ∧ (class1SlopeDatum ctx).K₀ = 48)
  ∨ ((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 3)
  ∨ ((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 7)
  ∨ ((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 10)
  ∨ ((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 52)
  ∨ ((class1SlopeDatum ctx).q = 117 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 117 ∧ (class1SlopeDatum ctx).K₀ = 4)
  ∨ ((class1SlopeDatum ctx).q = 127 ∧ (class1SlopeDatum ctx).K₀ = 63)

/-- Every swept band-3-free pair empties the genuine dense start set. -/
theorem ftDensePackStarts_empty_of_band3FreeDatum (ctx : ActualFailureContext)
    (h : FtDensePackBand3FreeDatum ctx) :
    genuineDensePackStarts ctx = ∅ := by
  rcases h with ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_65_2 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_65_6 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_65_32 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_73_36 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_75_12 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_85_2 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_85_8 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_89_44 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_91_3 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_91_6 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_93_1 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_97_48 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_105_3 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_105_7 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_105_10 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_105_52 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_117_1 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_117_4 ctx hq hK)
  · exact densePackStarts_empty_of_cycleBand3Free ctx
      (ftClass3Band3Free_of_datum_127_63 ctx hq hK)

/-- **The densepack bridge at `128` (additive)**: the enumerated window (`q < 64`) plus
the swept mid band (`64 <= q < 128`, relieved of the nineteen closed pairs) plus
band-3-free periods on the tail (`128 <= q`) rebuild `Class3StartsEmpty` VERBATIM. -/
theorem ftDensePackStartsEmpty_split_at_128
    (hlow : ∀ ctx : ActualFailureContext, (class1SlopeDatum ctx).q < 64 →
      genuineDensePackStarts ctx = ∅)
    (hmid : ∀ ctx : ActualFailureContext, 64 ≤ (class1SlopeDatum ctx).q →
      (class1SlopeDatum ctx).q < 128 → ¬ FtDensePackBand3FreeDatum ctx →
      genuineDensePackStarts ctx = ∅)
    (htail : ∀ ctx : ActualFailureContext, 128 ≤ (class1SlopeDatum ctx).q →
      Class3CycleBand3Free ctx) :
    Class3StartsEmpty := by
  intro ctx
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 64 with h64 | h64
  · exact hlow ctx h64
  · rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 128 with h128 | h128
    · by_cases hP : FtDensePackBand3FreeDatum ctx
      · exact ftDensePackStarts_empty_of_band3FreeDatum ctx hP
      · exact hmid ctx h64 h128 hP
    · exact densePackStarts_empty_of_cycleBand3Free ctx (htail ctx h128)

/-! ## Part 4.  The per-lane sweep record (machine-readable) -/

/-- The fourteen b2-heavy class-0 survivor pairs, ALL with proved joint-congruence
conflicts (closed: the cross-demand; surviving: the off-fibre residue miss and the
window-ones content). -/
def finiteTailsSweepHeavyConflictPairs : List (ℕ × ℕ) :=
  [(19, 9), (25, 2), (25, 12), (27, 1), (27, 4), (27, 13), (29, 14), (35, 2), (37, 18), (39, 1), (43, 21), (45, 1), (45, 2), (45, 4)]

/-- The eight new fully closed class-1 moduli in `(100, 200)`. -/
def finiteTailsSweepClass1ClosedModuli : List ℕ :=
  [109, 113, 123, 127, 129, 151, 157, 171]

/-- The 49 class-1 divisor-pin pairs of `101 <= q < 200` closed outright (band-4-free
cycles). -/
def finiteTailsSweepClass1ClosedPairs : List (ℕ × ℕ) :=
  [(105, 1), (105, 2), (105, 3), (105, 10), (105, 17), (109, 54), (113, 56), (117, 6), (117, 19), (117, 58), (119, 3), (123, 1), (123, 20), (123, 61), (127, 63), (129, 1), (129, 21), (129, 64), (133, 66), (135, 1), (135, 2), (135, 4), (147, 3), (147, 24), (151, 75), (155, 2), (155, 77), (157, 78), (165, 5), (165, 27), (165, 82), (171, 1), (171, 4), (171, 9), (171, 28), (171, 85), (183, 91), (187, 5), (189, 1), (189, 3), (189, 4), (189, 31), (189, 94), (195, 1), (195, 2), (195, 6), (195, 7), (195, 32), (195, 97)]

/-- The 87 class-1 divisor-pin pairs of `101 <= q < 200` SURVIVING (cycles read band 4;
all on-cycle numerators are odd, so the odd-numerator refinement closes none). -/
def finiteTailsSweepClass1SurvivorPairs : List (ℕ × ℕ) :=
  [(101, 50), (103, 51), (105, 7), (105, 52), (107, 53), (111, 1), (111, 18), (111, 55), (115, 2), (115, 11), (115, 57), (117, 1), (117, 4), (119, 8), (119, 59), (121, 5), (121, 60), (125, 2), (125, 12), (125, 62), (131, 65), (133, 3), (133, 9), (135, 7), (135, 13), (135, 22), (135, 67), (137, 68), (139, 69), (141, 1), (141, 23), (141, 70), (143, 5), (143, 6), (143, 71), (145, 2), (145, 14), (145, 72), (147, 1), (147, 10), (147, 73), (149, 74), (153, 1), (153, 4), (153, 8), (153, 25), (153, 76), (155, 15), (159, 1), (159, 26), (159, 79), (161, 3), (161, 11), (161, 80), (163, 81), (165, 1), (165, 2), (165, 7), (165, 16), (167, 83), (169, 6), (169, 84), (173, 86), (175, 2), (175, 3), (175, 12), (175, 17), (175, 87), (177, 1), (177, 29), (177, 88), (179, 89), (181, 90), (183, 1), (183, 30), (185, 2), (185, 18), (185, 92), (187, 8), (187, 93), (189, 10), (189, 13), (191, 95), (193, 96), (195, 19), (197, 98), (199, 99)]

/-- The run pairs of odd `64 <= q < 128` closed outright (band-`{1,4}`-free cycle):
exactly one. -/
def finiteTailsSweepRunClosedPairs : List (ℕ × ℕ) := [(93, 15)]

/-- The 79 run pairs of odd `64 <= q < 128` SURVIVING (band 1 or band 4 on-cycle). -/
def finiteTailsSweepRunSurvivorPairs : List (ℕ × ℕ) :=
  [(65, 2), (65, 6), (65, 32), (67, 33), (69, 1), (69, 11), (69, 34), (71, 35), (73, 36), (75, 1), (75, 2), (75, 7), (75, 12), (75, 37), (77, 3), (77, 5), (77, 38), (79, 39), (81, 1), (81, 4), (81, 13), (81, 40), (83, 41), (85, 2), (85, 8), (85, 42), (87, 1), (87, 14), (87, 43), (89, 44), (91, 3), (91, 6), (91, 45), (93, 1), (93, 46), (95, 2), (95, 9), (95, 47), (97, 48), (99, 1), (99, 4), (99, 5), (99, 16), (99, 49), (101, 50), (103, 51), (105, 1), (105, 2), (105, 3), (105, 7), (105, 10), (105, 17), (105, 52), (107, 53), (109, 54), (111, 1), (111, 18), (111, 55), (113, 56), (115, 2), (115, 11), (115, 57), (117, 1), (117, 4), (117, 6), (117, 19), (117, 58), (119, 3), (119, 8), (119, 59), (121, 5), (121, 60), (123, 1), (123, 20), (123, 61), (125, 2), (125, 12), (125, 62), (127, 63)]

/-- The nineteen densepack pairs of odd `64 <= q < 128` closed outright (band-3-free
cycles). -/
def finiteTailsSweepDensePackClosedPairs : List (ℕ × ℕ) :=
  [(65, 2), (65, 6), (65, 32), (73, 36), (75, 12), (85, 2), (85, 8), (89, 44), (91, 3), (91, 6), (93, 1), (97, 48), (105, 3), (105, 7), (105, 10), (105, 52), (117, 1), (117, 4), (127, 63)]

/-- The 61 densepack pairs of odd `64 <= q < 128` SURVIVING (band 3 on-cycle). -/
def finiteTailsSweepDensePackSurvivorPairs : List (ℕ × ℕ) :=
  [(67, 33), (69, 1), (69, 11), (69, 34), (71, 35), (75, 1), (75, 2), (75, 7), (75, 37), (77, 3), (77, 5), (77, 38), (79, 39), (81, 1), (81, 4), (81, 13), (81, 40), (83, 41), (85, 42), (87, 1), (87, 14), (87, 43), (91, 45), (93, 15), (93, 46), (95, 2), (95, 9), (95, 47), (99, 1), (99, 4), (99, 5), (99, 16), (99, 49), (101, 50), (103, 51), (105, 1), (105, 2), (105, 17), (107, 53), (109, 54), (111, 1), (111, 18), (111, 55), (113, 56), (115, 2), (115, 11), (115, 57), (117, 6), (117, 19), (117, 58), (119, 3), (119, 8), (119, 59), (121, 5), (121, 60), (123, 1), (123, 20), (123, 61), (125, 2), (125, 12), (125, 62)]

theorem finiteTailsSweepHeavyConflictPairs_nonempty :
    finiteTailsSweepHeavyConflictPairs ≠ [] := by
  simp [finiteTailsSweepHeavyConflictPairs]

theorem finiteTailsSweepClass1ClosedModuli_nonempty :
    finiteTailsSweepClass1ClosedModuli ≠ [] := by
  simp [finiteTailsSweepClass1ClosedModuli]

theorem finiteTailsSweepClass1SurvivorPairs_nonempty :
    finiteTailsSweepClass1SurvivorPairs ≠ [] := by
  simp [finiteTailsSweepClass1SurvivorPairs]

/-- Honest machine-readable status of the finite-tails sweep. -/
def finiteTailsSweepStatus : List String :=
  [ "SUBJECT: the mechanical finite tails (post-wave-14 open item 4) - (1) the joint demand " ++
      "at the FOURTEEN b2-heavy class-0 survivors (Class0SurvivorB2HeavyRest), (2) the class-1 " ++
      "deep tail pushed from q < 100 to q < 200 by the divisor-pin cycle sweep, (3) the " ++
      "run/densepack band sweeps on odd 64 <= q < 128, (4) per-lane dispatchers (additive) + " ++
      "this machine-readable record.",
    "PART 1 VERDICT - JOINT-CONGRUENCE CONFLICTS AT ALL FOURTEEN PAIRS: at every b2-heavy " ++
      "pair the certified orbit period from index 1 EQUALS class0SurvivorPeriod q, and the " ++
      "class-0 deep slot (the residue the windowed check must miss) reads band >= 5, never band " ++
      "2 - so the class-0 bad residue class and the class-4 band-2 congruence are jointly " ++
      "unsatisfiable: NO class-4 fibre member can realize the class-0 violation " ++
      "(ftHeavyConflict_<q>_<K0>, dispatcher ftHeavyConflict_dispatch). Dossiers " ++
      "(q,K0):(c,rho;B2): (19,9):(9,6;{5,8,9}) (25,2):(10,0;{1,6,7}) (25,12):(10,8;{4,5,9}) " ++
      "(27,1):(9,0;{2,6,8}) (27,4):(9,0;{2,6,8}) (27,13):(9,7;{4,6,9}) (29,14):(14,10;{4,8,13}) " ++
      "(35,2):(5,0;{3,4}) (37,18):(18,10;{7,12,15,16}) (39,1):(4,0;{2}) (43,21):(7,6;{5,7}) " ++
      "(45,1):(5,0;{1,3}) (45,2):(5,0;{1,3}) (45,4):(5,0;{1,3}).",
    "PART 1 CONSEQUENCE - THE JOINT DEMAND DECOMPOSES: Class0SurvivorResidueMiss is EXACTLY " ++
      "its restriction to floor-realizing starts OFF the class-4 fibre " ++
      "(ftClass0ResidueMiss_iff_offFibre / _of_offFibre).  HONEST: this closes only the " ++
      "cross-demand; the off-fibre residue miss and the Return window-ones content at the " ++
      "fourteen pairs remain OPEN.  (39,1) is the unique b2-heavy pair with a unique band-2 " ++
      "residue: the lcm spacing closes the W <= 4 window regime outright " ++
      "(ftKeyInj_of_datum_39_1 - full ReturnKeyInjOn), and at Q odd the member-EVEN parity pin " ++
      "empties the val-0 fibre part (ftVal0Empty_of_datum_39_1) and floors slice valuations " ++
      "(ftSliceValPos_of_datum_39_1).  The other thirteen pairs have 2-4 band-2 residues - no " ++
      "mod-c spacing, no per-regime closure (honest).",
    "PART 2 VERDICT - CLASS-1 SWEEP TO q < 200: of the 136 divisor-pin pairs (2K0+1 | q, odd " ++
      "101 <= q < 200), 49 have BAND-4-FREE cycles and close the routed fibre outright " ++
      "(ftClass1Fibre_empty_of_datum_*); EIGHT moduli close completely - " ++
      "ftClass1ClosedModuli200 = {109, 113, 123, 127, 129, 151, 157, 171} extends the wave-3 " ++
      "class1ClosedModuli (per-modulus closures via the divisor pin + Nat.divisors " ++
      "enumeration).  STRUCTURAL: every on-cycle numerator is odd (the step 2^g*K - q is odd " ++
      "for odd q), so 'band 4 with odd numerator' is the SAME as 'band 4 on-cycle' from index 1 " ++
      "- no even-only-band-4 grade exists; the 87 remaining pairs genuinely read band 4 and " ++
      "SURVIVE (finiteTailsSweepClass1SurvivorPairs).",
    "PART 2 ORDER CROSS (wave-6 criteria applied): among the 87 survivors EXACTLY TWO have an " ++
      "order-exceptional cofactor - (105,7) with orbitOrderModulus = 15 (ftCofactor_105_7, " ++
      "ftSurvivor_105_7_exceptional; the band-4 fixed point K = 7) and (155,15) with cofactor " ++
      "31 (ftCofactor_155_15, ftSurvivor_155_15_exceptional).  All other survivors have " ++
      "cofactor order >= 12 (survey datum), where the ModulusTailCriteria order-floor pruning " ++
      "(class1BandFreePeriod_iff_long_of_order_gt) is live.  Bridge: ftClass1Deep_split_at_200 " ++
      "rebuilds the Class1PairResidual.deep field shape VERBATIM from the swept part plus a 200 " ++
      "<= q band-4-free-period tail.",
    "PART 3 VERDICT - RUN (band-{1,4} cycle check, odd 64 <= q < 128, 80 pairs): EXACTLY ONE " ++
      "pair closes - (93,15), cycle [27, 15], bands {2,3} (ftRunCloses_of_datum_93_15 : " ++
      "Class5CycleNumericCloses, via the new generic closer " ++
      "ftClass5CycleNumeric_of_cycle_band_free).  Band 1 is on-cycle at all 79 other pairs " ++
      "(finiteTailsSweepRunSurvivorPairs) - the run lane is band-1 saturated; the surviving " ++
      "demand is the cycle-density numeric, not emptiness.",
    "PART 3 VERDICT - DENSEPACK (band-3 cycle check, same range): NINETEEN pairs close - " ++
      "(65,2) (65,6) (65,32) (73,36) (75,12) (85,2) (85,8) (89,44) (91,3) (91,6) (93,1) (97,48) " ++
      "(105,3) (105,7) (105,10) (105,52) (117,1) (117,4) (127,63) " ++
      "(ftClass3Band3Free_of_datum_*, aggregate FtDensePackBand3FreeDatum, closures via " ++
      "densePackStarts_empty_of_cycleBand3Free); 61 pairs survive " ++
      "(finiteTailsSweepDensePackSurvivorPairs).",
    "DISPATCHERS (additive, wired to the existing consumers): ftClass1Deep_split_at_200 (the " ++
      "Class1PairResidual.deep shape, the class1PairDeep_split_at_tail successor at 200), " ++
      "ftRunSettlement_split_at_128 (RunCycleNumericSettlementHyp VERBATIM, mid band relieved " ++
      "of (93,15)), ftDensePackStartsEmpty_split_at_128 (Class3StartsEmpty VERBATIM, mid band " ++
      "relieved of the nineteen pairs), ftClass0ResidueMiss_of_offFibre (the " ++
      "Class0SurvivorResidueMiss consumer of ChernoffClass0SurvivorClosure, on-fibre part " ++
      "free).",
    "HONEST SURVIVING MASTER LIST: (a) the fourteen b2-heavy pairs - off-fibre residue miss + " ++
      "window-ones/envelope content (the conflict closes only the cross-demand; W <= 4 regime " ++
      "closed at (39,1) only); (b) class-1: the 87 band-4-reading pairs of 101 <= q < 200 plus " ++
      "the un-enumerated 200 <= q (and the 23 wave-5 pairs of q <= 99, untouched here); (c) " ++
      "run: the 79 band-1/4-reading pairs of 64 <= q < 128 plus 128 <= q; (d) densepack: the 61 " ++
      "band-3-reading pairs of 64 <= q < 128 plus 128 <= q.  NO unconditional closure of any " ++
      "capstone field is claimed; every bridge is conditional on the listed per-ctx hypotheses.",
    "HYGIENE: additive only - no existing module edited, NOT root-wired (built standalone as " ++
      "Erdos260.FiniteTailsSweep); no sorry / admit / new axiom / native_decide (decide only on " ++
      "small closed numeric, divisor-set and list goals); all #print axioms in [propext, " ++
      "Classical.choice, Quot.sound] or fewer." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem finiteTailsSweepStatus_nonempty : finiteTailsSweepStatus ≠ [] := by
  simp [finiteTailsSweepStatus]

/-! ## Part 5.  Axiom-cleanliness audit -/

#print axioms ftHeavyConflict_19_9
#print axioms ftHeavyConflict_25_2
#print axioms ftHeavyConflict_25_12
#print axioms ftHeavyConflict_27_1
#print axioms ftHeavyConflict_27_4
#print axioms ftHeavyConflict_27_13
#print axioms ftHeavyConflict_29_14
#print axioms ftHeavyConflict_35_2
#print axioms ftHeavyConflict_37_18
#print axioms ftHeavyConflict_39_1
#print axioms ftHeavyConflict_43_21
#print axioms ftHeavyConflict_45_1
#print axioms ftHeavyConflict_45_2
#print axioms ftHeavyConflict_45_4
#print axioms ftHeavyConflict_dispatch
#print axioms ftClass0ResidueMiss_of_offFibre
#print axioms ftClass0ResidueMiss_iff_offFibre
#print axioms ftKeyInj_of_datum_39_1
#print axioms ftVal0Empty_of_datum_39_1
#print axioms ftSliceValPos_of_datum_39_1
#print axioms ftClass1Fibre_empty_of_datum_105_1
#print axioms ftClass1Fibre_empty_of_datum_105_2
#print axioms ftClass1Fibre_empty_of_datum_105_3
#print axioms ftClass1Fibre_empty_of_datum_105_10
#print axioms ftClass1Fibre_empty_of_datum_105_17
#print axioms ftClass1Fibre_empty_of_datum_109_54
#print axioms ftClass1Fibre_empty_of_datum_113_56
#print axioms ftClass1Fibre_empty_of_datum_117_6
#print axioms ftClass1Fibre_empty_of_datum_117_19
#print axioms ftClass1Fibre_empty_of_datum_117_58
#print axioms ftClass1Fibre_empty_of_datum_119_3
#print axioms ftClass1Fibre_empty_of_datum_123_1
#print axioms ftClass1Fibre_empty_of_datum_123_20
#print axioms ftClass1Fibre_empty_of_datum_123_61
#print axioms ftClass1Fibre_empty_of_datum_127_63
#print axioms ftClass1Fibre_empty_of_datum_129_1
#print axioms ftClass1Fibre_empty_of_datum_129_21
#print axioms ftClass1Fibre_empty_of_datum_129_64
#print axioms ftClass1Fibre_empty_of_datum_133_66
#print axioms ftClass1Fibre_empty_of_datum_135_1
#print axioms ftClass1Fibre_empty_of_datum_135_2
#print axioms ftClass1Fibre_empty_of_datum_135_4
#print axioms ftClass1Fibre_empty_of_datum_147_3
#print axioms ftClass1Fibre_empty_of_datum_147_24
#print axioms ftClass1Fibre_empty_of_datum_151_75
#print axioms ftClass1Fibre_empty_of_datum_155_2
#print axioms ftClass1Fibre_empty_of_datum_155_77
#print axioms ftClass1Fibre_empty_of_datum_157_78
#print axioms ftClass1Fibre_empty_of_datum_165_5
#print axioms ftClass1Fibre_empty_of_datum_165_27
#print axioms ftClass1Fibre_empty_of_datum_165_82
#print axioms ftClass1Fibre_empty_of_datum_171_1
#print axioms ftClass1Fibre_empty_of_datum_171_4
#print axioms ftClass1Fibre_empty_of_datum_171_9
#print axioms ftClass1Fibre_empty_of_datum_171_28
#print axioms ftClass1Fibre_empty_of_datum_171_85
#print axioms ftClass1Fibre_empty_of_datum_183_91
#print axioms ftClass1Fibre_empty_of_datum_187_5
#print axioms ftClass1Fibre_empty_of_datum_189_1
#print axioms ftClass1Fibre_empty_of_datum_189_3
#print axioms ftClass1Fibre_empty_of_datum_189_4
#print axioms ftClass1Fibre_empty_of_datum_189_31
#print axioms ftClass1Fibre_empty_of_datum_189_94
#print axioms ftClass1Fibre_empty_of_datum_195_1
#print axioms ftClass1Fibre_empty_of_datum_195_2
#print axioms ftClass1Fibre_empty_of_datum_195_6
#print axioms ftClass1Fibre_empty_of_datum_195_7
#print axioms ftClass1Fibre_empty_of_datum_195_32
#print axioms ftClass1Fibre_empty_of_datum_195_97
#print axioms ftClass1Fibre_empty_of_modulus_eq_109
#print axioms ftClass1Fibre_empty_of_modulus_eq_113
#print axioms ftClass1Fibre_empty_of_modulus_eq_123
#print axioms ftClass1Fibre_empty_of_modulus_eq_127
#print axioms ftClass1Fibre_empty_of_modulus_eq_129
#print axioms ftClass1Fibre_empty_of_modulus_eq_151
#print axioms ftClass1Fibre_empty_of_modulus_eq_157
#print axioms ftClass1Fibre_empty_of_modulus_eq_171
#print axioms ftClass1Fibre_empty_of_mem_extended
#print axioms ftClass1Fibre_empty_of_band4FreeDatum
#print axioms ftClass1Deep_split_at_200
#print axioms ftCofactor_105_7
#print axioms ftCofactor_155_15
#print axioms ftSurvivor_105_7_exceptional
#print axioms ftSurvivor_155_15_exceptional
#print axioms ftClass5CycleNumeric_of_cycle_band_free
#print axioms ftRunCloses_of_datum_93_15
#print axioms ftRunSettlement_split_at_128
#print axioms ftClass3Band3Free_of_datum_65_2
#print axioms ftClass3Band3Free_of_datum_65_6
#print axioms ftClass3Band3Free_of_datum_65_32
#print axioms ftClass3Band3Free_of_datum_73_36
#print axioms ftClass3Band3Free_of_datum_75_12
#print axioms ftClass3Band3Free_of_datum_85_2
#print axioms ftClass3Band3Free_of_datum_85_8
#print axioms ftClass3Band3Free_of_datum_89_44
#print axioms ftClass3Band3Free_of_datum_91_3
#print axioms ftClass3Band3Free_of_datum_91_6
#print axioms ftClass3Band3Free_of_datum_93_1
#print axioms ftClass3Band3Free_of_datum_97_48
#print axioms ftClass3Band3Free_of_datum_105_3
#print axioms ftClass3Band3Free_of_datum_105_7
#print axioms ftClass3Band3Free_of_datum_105_10
#print axioms ftClass3Band3Free_of_datum_105_52
#print axioms ftClass3Band3Free_of_datum_117_1
#print axioms ftClass3Band3Free_of_datum_117_4
#print axioms ftClass3Band3Free_of_datum_127_63
#print axioms ftDensePackStarts_empty_of_band3FreeDatum
#print axioms ftDensePackStartsEmpty_split_at_128
#print axioms finiteTailsSweepHeavyConflictPairs_nonempty
#print axioms finiteTailsSweepClass1ClosedModuli_nonempty
#print axioms finiteTailsSweepClass1SurvivorPairs_nonempty
#print axioms finiteTailsSweepStatus_nonempty

end

end Erdos260
