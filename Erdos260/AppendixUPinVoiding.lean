import Erdos260.OnsetBoundClosure
import Erdos260.OrbitPinVoiding
import Erdos260.MissDistanceClosure
import Erdos260.AppendixNDescent
import Erdos260.Erdos260SummitCapstone

/-!
# Appendix U pin voiding: the periodic-continuation route to the deep orbit pins
# (`AppendixUPinVoiding`)

This module (NEW; it edits no existing file) transcribes the v22 manuscript's
Appendix U ("Sixth unconditional closure push: direct fixed-pin closure and the
reduced seventh fibre", tex 9610-9832) against the in-tree machinery, states the
ONE missing confinement atom the Wave-22 analysis identified
(`FixedPinCleanContinuation`), wires the conditional kill of the summit field
`deepOrbitPin`, and proves a genuinely NEW unconditional theorem on the value
side (the carry-integrality divisibility obstruction) that makes the needed atom
STRICTLY WEAKER than the manuscript's own U.1 statement.

## 1.  The honest U transcription (what U adds beyond the tree)

Appendix U has three components; two are ALREADY in tree:

* `lem:u-periodic-density-floor` (U.3, tex 9669-9687: a nonzero word of period
  `p ≤ 2^19` has `≥ X/p − O(L+p) ≥ (32/2^24)X` ones in `[X, 2X]`, beating
  `c0 = 17/2^24`) — this IS `periodic_no_sparse_shell` (`OnsetBoundClosure`),
  re-exported here as `appendixU_periodicDensityFloor`.
* the period table / dyadic-clean period cap — subsumed by
  `constGap_continuation_void` (`OnsetBoundClosure`): ANY eventual constant hit
  gap `0 < g ≤ 2^19` with window-compatible onset is absurd at every failing
  context.  The U.2 period-three table (the six words `001..110`, one `1` per
  period) needs no separate transcription: the one-per-period count is
  `bootOnes_pos_of_nonterminating`, and the constant-gap-3 instance of the
  collision is `seventhsPeriodicContinuation_void` below.

What U ADDS is exactly `lem:u-fixed-pin-periodic-continuation` (U.2, tex
9638-9666): "every RETAINED deep fixed-pin branch agrees on its active window
with a nonzero word of bounded period" — the CONFINEMENT step.  Its proof
consumes the manuscript's priority-deletion framework (dirty P4, run L.4, tower
exits L.3/M.5, endpoint/progress packages), none of which is transcribed; the
in-tree dictionary verdict (`FixedFamilyPeriodicity`) is that NO unconditional
per-gap identification between the orbit band and the word's hit gaps exists.
The confinement is therefore stated as the named atom and consumed
conditionally — exactly the analysis's Lane-C prediction.

## 2.  THE NEW THEOREM (unconditional): the value-route carry obstruction

`constGap_carry_divides`: for ANY non-terminating binary word with weighted
value `P/Q` whose hit gaps are eventually the constant `g`, the integer carry
recurrence forces the divisibility `(2^g − 1) ∣ Q·g`.  Mechanism: across one
period the carry obeys `z_{k+1} = 2^g·z_k − Q·(position)`; the affine recurrence
has the exact particular solution `Q·((2^g−1)·position + g·2^g)/(2^g−1)²`, and
the homogeneous deviation multiplies by `2^g` per period while the carry itself
is confined to `0 < z_k ≤ Q·(position+2)` — exponential growth against a linear
envelope forces the deviation to vanish IDENTICALLY, and integrality of the
resulting exact solution is the stated divisibility.

Consequences (all proved, unconditional):

* At each of the five fixed data the pinned value representation VIOLATES the
  divisibility: `(3,1)`: `3 ∤ 2·2^t`; `(21,3)`: `7 ∤ 3·2^t`; `(15,1)`:
  `15 ∤ 20·2^t` (via `3`); `(15,2)`: `15 ∤ 12·2^t` (via `5`); `(105,7)`:
  `15 ∤ 4·2^t` (via `3`).  Hence `fixedFamilyHit_anyOnsetContinuation_void`:
  a fixed-family hit with an eventually-band-constant gap tail at ANY onset —
  even an onset far beyond the shell window, where the in-tree shell route
  (`fixedFamily_cleanContinuation_void`, which needs `a k₀ ≤ X`) cannot fire —
  is absurd.  The value tension flagged in the brief is REAL and PROVED: the
  canonical band-`g` continuation has non-dyadic weighted value (odd part
  `(2^g−1)²` up to the head), while the pin forces the exactly-pinned value.
* HONEST ASYMMETRY: the sevenths stratum PASSES the divisibility
  (`sevenths_divisibility_consistent`: `7 ∣ (7·2^t)·3`) — the value route kills
  the five fixed pins but NOT the `u = 7` period-three fibre; there only the
  shell route (window-compatible onset) applies.

## 3.  The confinement atom and the conditional closure

* `AnyOnsetBandContinuation ctx` — the word's hit gaps are eventually the
  recurrent band of the datum, onset UNCONSTRAINED (strictly weaker than the
  in-tree `FixedFamilyCleanContinuation`, which demands `a k₀ ≤ X`).
* `FixedPinCleanContinuation` — THE ATOM: at every deep (`X > 2^986891`)
  band-2/3/4-pinned context the continuation holds.  This is the U.1 claim
  restricted to the PIN hypothesis class (strictly smaller than the
  fixed-family-hit class of `DeepFixedFamilyCleanContinuation`) and weakened to
  any-onset (admissible because of the NEW value-route kill).
* `deepOrbitPinVoiding_of_confinement` — the atom supplies the FULL
  `DeepOrbitPinVoiding`, i.e. the summit field `deepOrbitPin` verbatim; through
  the in-tree equivalences it also rebuilds the three v17 voiding fields and
  `DeepFixedFamilyVoid`.  `erdos260_of_confinement_and_rest` reaches the
  endpoint given the rest of the summit surface.
* `fixedPinCleanContinuation_iff_deepOrbitPinVoiding` — the honest no-free-lunch
  record: the atom is EQUIVALENT to the voiding it feeds (the kill empties the
  atom's hypothesis class), exactly as `FixedFamilyPeriodicity` proved for the
  window-onset form.  The atom is the manuscript-language FORM of the residual,
  not a strictly weaker waypoint.
* The exit-ledger bridge (`anyOnsetContinuation_iff_exitFreeTail`): the
  continuation is EXACTLY an eventually-exit-free L.3.1 ledger tail — so what
  the atom demands is that the exits VACATE some tail of the gap sequence,
  while the in-tree mass floor (`confinement_exitMass_floor`, re-export of
  `fixedFamily_exitMass_lower`: `X ≤ 2·emExitMass` at every fixed hit) shows
  exits carry HALF the reach span: the confinement demand and the pressure
  relocation push in opposite directions, which is the substance of the kill.

## 4.  U.2 / S / V / W (the sevenths), honest

* `seventhsPeriodicContinuation_void`: the cycle-persistent (period-three)
  sevenths stratum with window-compatible onset is VOID — the sound half of
  U.2 (`prop:u-seventh-periodic-direct`), no pin hypothesis even needed.
* `deepSeventhsPinVoid_of_exitActiveVoid`: `DeepSeventhsPinVoid` reduces to the
  EXIT-ACTIVE residual (`DeepSeventhsExitActiveVoid`) — the W2 obligation; the
  periodic branch is discharged by the constant-gap collision.
* NOT transcribed (flagged, per the analysis's Bug 4): the S/V `1/30` mass
  floors (`lem:s-sevenths-exit-floor`, `lem:v-certified-seventh-floor`) jump
  from "nonempty after priority deletion" to "mass `≥ (1/30)X|I_j|`" with no
  proof (the cited relocated pressure floor `lem:q-fixed-pin-exit-lower` is
  itself only asserted); W's certification lemmas consume T.2 = the Appendix R
  exit-share chain (Gap 1).  No sound fragment of V/W survives extraction
  beyond the reduction recorded here.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only — no
existing module is edited.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Part 0.  Arithmetic helpers -/

/-- Exponentials escape every linear envelope (ℕ form): `c + e·k < 2^k` at
`k = 2(c+e)+2`. -/
theorem appendixU_linear_lt_two_pow (c e : ℕ) : ∃ k : ℕ, c + e * k < 2 ^ k := by
  refine ⟨2 * (c + e) + 2, ?_⟩
  have hs : c + e + 1 ≤ 2 ^ (c + e) := Nat.lt_two_pow_self
  have hsq : (c + e + 1) * (c + e + 1) ≤ 2 ^ (c + e) * 2 ^ (c + e) :=
    Nat.mul_le_mul hs hs
  have hsplit : (2 : ℕ) ^ (2 * (c + e) + 2) = 4 * (2 ^ (c + e) * 2 ^ (c + e)) := by
    rw [show 2 * (c + e) + 2 = ((c + e) + (c + e)) + 2 by ring, pow_add, pow_add]
    ring
  rw [hsplit]
  nlinarith [hsq, Nat.zero_le c, Nat.zero_le e]

/-- Exponentials escape every linear envelope (ℤ form, arbitrary coefficients). -/
theorem appendixU_int_escape (C D : ℤ) : ∃ k : ℕ, C + D * (k : ℤ) < 2 ^ k := by
  obtain ⟨k, hk⟩ := appendixU_linear_lt_two_pow C.toNat D.toNat
  refine ⟨k, ?_⟩
  have h1 : C ≤ (C.toNat : ℤ) := Int.self_le_toNat C
  have h2 : D ≤ (D.toNat : ℤ) := Int.self_le_toNat D
  have h3 : D * (k : ℤ) ≤ (D.toNat : ℤ) * (k : ℤ) :=
    mul_le_mul_of_nonneg_right h2 (Int.natCast_nonneg k)
  have h4 : ((C.toNat + D.toNat * k : ℕ) : ℤ) < ((2 ^ k : ℕ) : ℤ) := by
    exact_mod_cast hk
  push_cast at h4
  linarith

/-- An odd prime never divides `m · 2^t` when it does not divide `m`. -/
theorem appendixU_odd_prime_not_dvd {p m : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (hm : ¬ p ∣ m) (t : ℕ) : ¬ p ∣ m * 2 ^ t := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact hm h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow hp h))

/-! ## Part 1.  The value-route core: constant gaps force the carry divisibility

The interior of every constant-gap period is hit-free (completeness of the hit
enumeration), so the carry doubles `g−1` times and then takes one hit step:
`z_{k+1} = 2^g z_k − Q·(a k₀ + (k+1)g)`.  The affine recurrence with the carry
envelope `0 < z ≤ Q(N+2)` forces the exact particular solution, whose
integrality is `(2^g − 1) ∣ Q·g`. -/

/-- Interior positions of a constant-gap tail carry digit `0`: any hit strictly
between two consecutive AP hits would break the enumeration. -/
theorem constGap_interior_zero {d a : ℕ → ℕ} {k₀ g' : ℕ}
    (hd : BinaryDigits d) (hseq : HitSequence d a)
    (hgap : ∀ k, k₀ ≤ k → hitGap a k = g' + 1)
    (m i : ℕ) (hi1 : 1 ≤ i) (hig : i < g' + 1) :
    d (a k₀ + m * (g' + 1) + i) = 0 := by
  have hAP := hitSequence_AP_of_const_gaps hseq hgap
  rcases hd (a k₀ + m * (g' + 1) + i) with h0 | h1
  · exact h0
  · exfalso
    obtain ⟨j, hj⟩ := hseq.complete _ h1
    have hgt : a k₀ < a j := by
      rw [hj]
      have h0' : 0 ≤ m * (g' + 1) := Nat.zero_le _
      linarith
    have hjk : k₀ < j := hseq.strict.lt_iff_lt.mp hgt
    obtain ⟨s, rfl⟩ : ∃ s, j = k₀ + s := ⟨j - k₀, by omega⟩
    have hAPs : a (k₀ + s) = a k₀ + s * (g' + 1) := hAP s
    have h1' : a k₀ + s * (g' + 1) = a k₀ + (m * (g' + 1) + i) := by
      rw [← hAPs, hj]
      exact Nat.add_assoc _ _ _
    have hcancel : s * (g' + 1) = m * (g' + 1) + i := Nat.add_left_cancel h1'
    have hL : s * (g' + 1) % (g' + 1) = 0 := Nat.mul_mod_left _ _
    have hR : (m * (g' + 1) + i) % (g' + 1) = i := by
      rw [mul_comm, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt hig
    rw [hcancel, hR] at hL
    omega

/-- **The one-period carry step on a constant-gap tail**: `g−1` doublings across
the hit-free interior, then one hit step — `z_{k+1} = 2^g·z_k − Q·(next hit)`. -/
theorem constGap_carry_step {Q : ℕ} {P : ℤ} {d a : ℕ → ℕ} {k₀ g' : ℕ}
    (hd : BinaryDigits d) (hseq : HitSequence d a)
    (hgap : ∀ k, k₀ ≤ k → hitGap a k = g' + 1) (k : ℕ) :
    integerCarry Q P d (a k₀ + (k + 1) * (g' + 1))
      = 2 ^ (g' + 1) * integerCarry Q P d (a k₀ + k * (g' + 1))
        - (Q : ℤ) * ((a k₀ + (k + 1) * (g' + 1) : ℕ) : ℤ) := by
  have hAP := hitSequence_AP_of_const_gaps hseq hgap
  have hz : ∀ j : ℕ, a k₀ + k * (g' + 1) < j → j ≤ a k₀ + k * (g' + 1) + g' →
      d j = 0 := by
    intro j hj1 hj2
    obtain ⟨N, hN⟩ : ∃ N, N = a k₀ + k * (g' + 1) := ⟨_, rfl⟩
    rw [← hN] at hj1 hj2
    obtain ⟨i, hji, hi1, hig⟩ : ∃ i, j = N + i ∧ 1 ≤ i ∧ i ≤ g' :=
      ⟨j - N, by omega, by omega, by omega⟩
    subst hji
    rw [hN]
    exact constGap_interior_zero hd hseq hgap k i hi1 (by omega)
  have hdouble := integerCarry_add_of_zero_digits Q P d (a k₀ + k * (g' + 1)) g' hz
  have hone : d (a k₀ + k * (g' + 1) + g' + 1) = 1 := by
    have hh := hseq.hit (k₀ + (k + 1))
    rw [hAP (k + 1)] at hh
    have he : a k₀ + (k + 1) * (g' + 1) = a k₀ + k * (g' + 1) + g' + 1 := by ring
    rwa [he] at hh
  have hsucc := integerCarry_succ_of_one Q P d hone
  have he : a k₀ + (k + 1) * (g' + 1) = a k₀ + k * (g' + 1) + g' + 1 := by ring
  rw [he, hsucc, hdouble]
  ring

/-- **THE VALUE-ROUTE CARRY OBSTRUCTION (NEW, unconditional)**: a non-terminating
binary word with weighted value `P/Q` whose hit gaps are EVENTUALLY the constant
`g` (any onset whatsoever) satisfies `(2^g − 1) ∣ Q·g`.  The carry recurrence
`z_{k+1} = 2^g z_k − Q·(a k₀ + (k+1)g)` has exact particular solution
`Q((2^g−1)·pos + g·2^g)/(2^g−1)²`; the homogeneous deviation grows like `2^{gk}`
against the linear carry envelope `0 < z ≤ Q(pos+2)`, hence vanishes, and
integrality of the particular solution at `k = 0` is the divisibility. -/
theorem constGap_carry_divides {Q : ℕ} {P : ℤ} {d a : ℕ → ℕ} {k₀ g : ℕ}
    (hQ : 0 < Q) (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hseq : HitSequence d a)
    (hgap : ∀ k, k₀ ≤ k → hitGap a k = g) :
    (2 ^ g - 1) ∣ Q * g := by
  -- gaps of a strictly monotone enumeration are positive
  have hg1 : 1 ≤ g := by
    have h := hgap k₀ le_rfl
    have hlt : a k₀ < a (k₀ + 1) := hseq.strict (Nat.lt_succ_self k₀)
    unfold hitGap at h
    omega
  obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  -- carry envelope along the AP
  have hzpos : ∀ k : ℕ, 0 < integerCarry Q P d (a k₀ + k * (g' + 1)) :=
    fun k => integerCarry_pos_of_not_eventuallyZero hQ hd heta hnonterm _
  have hzub : ∀ k : ℕ, integerCarry Q P d (a k₀ + k * (g' + 1))
      ≤ (Q : ℤ) * ((a k₀ + k * (g' + 1) + 2 : ℕ) : ℤ) :=
    fun k => (integerCarry_bounds_of_rational_value (a k₀ + k * (g' + 1)) hQ hd heta).2
  set M : ℤ := 2 ^ (g' + 1) - 1 with hMdef
  have h2T : (2 : ℤ) ≤ 2 ^ (g' + 1) := by
    have hp : (0 : ℤ) < 2 ^ g' := pow_pos (by norm_num) g'
    have h1 : (1 : ℤ) ≤ 2 ^ g' := by
      have := Int.add_one_le_iff.mpr hp
      linarith
    calc (2 : ℤ) = 2 * 1 := by ring
      _ ≤ 2 * 2 ^ g' := by linarith
      _ = 2 ^ (g' + 1) := by ring
  have hM1 : 1 ≤ M := by rw [hMdef]; linarith
  have hMT : M + 1 = 2 ^ (g' + 1) := by rw [hMdef]; ring
  -- the homogeneous deviation from the exact particular solution
  set w : ℕ → ℤ := fun k =>
    M ^ 2 * integerCarry Q P d (a k₀ + k * (g' + 1))
      - (Q : ℤ) * (M * ((a k₀ + k * (g' + 1) : ℕ) : ℤ) + ((g' : ℤ) + 1) * (M + 1))
    with hwdef
  have hwstep : ∀ k, w (k + 1) = (M + 1) * w k := by
    intro k
    have hstep := constGap_carry_step (Q := Q) (P := P) hd hseq hgap k
    simp only [hwdef]
    rw [hstep, ← hMT]
    push_cast
    ring
  have hwexp : ∀ k, w k = (M + 1) ^ k * w 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [hwstep k, ih]; ring
  -- the linear envelope on the deviation
  obtain ⟨C, hCdef⟩ : ∃ C : ℤ,
      C = M ^ 2 * (Q : ℤ) * (((a k₀ : ℕ) : ℤ) + 2)
        + (Q : ℤ) * (M * ((a k₀ : ℕ) : ℤ) + ((g' : ℤ) + 1) * (M + 1)) := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℤ,
      D = M ^ 2 * (Q : ℤ) * ((g' : ℤ) + 1) + (Q : ℤ) * M * ((g' : ℤ) + 1) := ⟨_, rfl⟩
  have hq0 : (0 : ℤ) < (Q : ℤ) := by exact_mod_cast hQ
  have hM0 : (0 : ℤ) ≤ M := by linarith
  have ha0 : (0 : ℤ) ≤ ((a k₀ : ℕ) : ℤ) := Int.natCast_nonneg _
  have hg0 : (0 : ℤ) ≤ (g' : ℤ) := Int.natCast_nonneg _
  have hbound : ∀ k : ℕ, w k ≤ C + D * (k : ℤ) ∧ -(C + D * (k : ℤ)) ≤ w k := by
    intro k
    have hR1 := hzpos k
    have hR2 := hzub k
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg _
    have hM2R : M ^ 2 * integerCarry Q P d (a k₀ + k * (g' + 1))
        ≤ M ^ 2 * ((Q : ℤ) * ((a k₀ + k * (g' + 1) + 2 : ℕ) : ℤ)) :=
      mul_le_mul_of_nonneg_left hR2 (sq_nonneg M)
    have hM2pos : (0 : ℤ) < M ^ 2 := by nlinarith [hM1]
    have hM2Rpos : 0 < M ^ 2 * integerCarry Q P d (a k₀ + k * (g' + 1)) :=
      mul_pos hM2pos hR1
    simp only [hwdef]
    rw [hCdef, hDdef]
    push_cast at hM2R ⊢
    constructor
    · nlinarith [hM2R, hq0, hM0, ha0, hk0, hg0,
        mul_nonneg (mul_nonneg hq0.le hM0) ha0,
        mul_nonneg (mul_nonneg hq0.le hM0) hg0,
        mul_nonneg hq0.le hM0,
        mul_nonneg hq0.le hg0,
        mul_nonneg (mul_nonneg (mul_nonneg hq0.le hM0) hg0) hk0,
        mul_nonneg (mul_nonneg hq0.le hM0) hk0,
        mul_nonneg (mul_nonneg (sq_nonneg M) hq0.le) ha0,
        mul_nonneg (sq_nonneg M) hq0.le,
        mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg M) hq0.le) hg0) hk0,
        mul_nonneg (mul_nonneg (sq_nonneg M) hq0.le) hk0]
    · nlinarith [hM2Rpos, hq0, hM0, ha0, hk0, hg0,
        mul_nonneg (mul_nonneg hq0.le hM0) ha0,
        mul_nonneg (mul_nonneg hq0.le hM0) hg0,
        mul_nonneg hq0.le hM0,
        mul_nonneg hq0.le hg0,
        mul_nonneg (mul_nonneg (mul_nonneg hq0.le hM0) hg0) hk0,
        mul_nonneg (mul_nonneg hq0.le hM0) hk0,
        mul_nonneg (mul_nonneg (sq_nonneg M) hq0.le) ha0,
        mul_nonneg (sq_nonneg M) hq0.le,
        mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg M) hq0.le) hg0) hk0,
        mul_nonneg (mul_nonneg (sq_nonneg M) hq0.le) hk0]
  -- exponential homogeneous part versus the linear envelope: w 0 = 0
  have hpowM : ∀ n : ℕ, (2 : ℤ) ^ n ≤ (M + 1) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        have h2M : (2 : ℤ) ≤ M + 1 := by linarith
        have h2n : (0 : ℤ) ≤ 2 ^ n := by positivity
        have hMn : (0 : ℤ) ≤ M + 1 := by linarith
        calc (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
          _ ≤ (M + 1) * (M + 1) ^ n := mul_le_mul h2M ih h2n hMn
          _ = (M + 1) ^ (n + 1) := by ring
  have hw0 : w 0 = 0 := by
    rcases lt_trichotomy (w 0) 0 with hneg | h0 | hpos
    · exfalso
      obtain ⟨k, hk⟩ := appendixU_int_escape C D
      have h1 := hwexp k
      have h2 := (hbound k).2
      have hw1 : 1 ≤ -(w 0) := by
        have := Int.add_one_le_iff.mpr hneg
        linarith
      have hMk : (0 : ℤ) ≤ (M + 1) ^ k := pow_nonneg (by linarith) k
      have hge : (2 : ℤ) ^ k ≤ -(w k) := by
        rw [h1]
        calc (2 : ℤ) ^ k ≤ (M + 1) ^ k := hpowM k
          _ = (M + 1) ^ k * 1 := (mul_one _).symm
          _ ≤ (M + 1) ^ k * (-(w 0)) := mul_le_mul_of_nonneg_left hw1 hMk
          _ = -((M + 1) ^ k * w 0) := by ring
      linarith
    · exact h0
    · exfalso
      obtain ⟨k, hk⟩ := appendixU_int_escape C D
      have h1 := hwexp k
      have h2 := (hbound k).1
      have hw1 : 1 ≤ w 0 := by
        have := Int.add_one_le_iff.mpr hpos
        linarith
      have hMk : (0 : ℤ) ≤ (M + 1) ^ k := pow_nonneg (by linarith) k
      have hge : (2 : ℤ) ^ k ≤ w k := by
        rw [h1]
        calc (2 : ℤ) ^ k ≤ (M + 1) ^ k := hpowM k
          _ = (M + 1) ^ k * 1 := (mul_one _).symm
          _ ≤ (M + 1) ^ k * w 0 := mul_le_mul_of_nonneg_left hw1 hMk
      linarith
  -- integrality of the exact solution at k = 0 is the divisibility
  simp only [hwdef] at hw0
  simp only [Nat.zero_mul, Nat.add_zero] at hw0
  have hdvdZ : M ∣ ((Q * (g' + 1) : ℕ) : ℤ) := by
    refine ⟨M * integerCarry Q P d (a k₀) - (Q : ℤ) * ((a k₀ : ℕ) : ℤ)
      - (Q : ℤ) * ((g' : ℤ) + 1), ?_⟩
    push_cast
    linear_combination -hw0
  have hMnat : ((2 ^ (g' + 1) - 1 : ℕ) : ℤ) = M := by
    have h1 : (1 : ℕ) ≤ 2 ^ (g' + 1) := Nat.one_le_two_pow
    rw [hMdef]
    push_cast [h1]
    ring
  have hfin : ((2 ^ (g' + 1) - 1 : ℕ) : ℤ) ∣ ((Q * (g' + 1) : ℕ) : ℤ) := by
    rw [hMnat]
    exact hdvdZ
  exact_mod_cast hfin

/-! ## Part 2.  The any-onset continuation and the five-data value-route kills -/

/-- **The any-onset band continuation**: the word's hit gaps are EVENTUALLY the
recurrent band of the datum — `FixedFamilyCleanContinuation` with the
window-compatibility constraint `a k₀ ≤ X` DROPPED.  The U.1 confinement claim
in its weakest in-tree-killable form. -/
def AnyOnsetBandContinuation (ctx : ActualFailureContext) : Prop :=
  ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
    hitGap ctx.n24CarryData.a k = fixedFamilyRecurrentBand ctx

/-- The window-onset clean continuation forgets to the any-onset form. -/
theorem anyOnset_of_cleanContinuation (ctx : ActualFailureContext)
    (hcc : FixedFamilyCleanContinuation ctx) : AnyOnsetBandContinuation ctx := by
  obtain ⟨k₀, _, hgap⟩ := hcc
  exact ⟨k₀, hgap⟩

/-- The recurrent band at the `(3,1)` datum is `2`. -/
theorem appendixU_band_3_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 3) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    fixedFamilyRecurrentBand ctx = 2 := by
  unfold fixedFamilyRecurrentBand
  rw [hq, hK]
  exact fixedFamilyBand_3_1

/-- The recurrent band at the `(21,3)` datum is `3`. -/
theorem appendixU_band_21_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    fixedFamilyRecurrentBand ctx = 3 := by
  unfold fixedFamilyRecurrentBand
  rw [hq, hK]
  exact fixedFamilyBand_21_3

/-- The recurrent band at the `(15,1)` datum is `4`. -/
theorem appendixU_band_15_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    fixedFamilyRecurrentBand ctx = 4 := by
  unfold fixedFamilyRecurrentBand
  rw [hq, hK]
  exact fixedFamilyBand_15_1

/-- The recurrent band at the `(15,2)` datum is `4`. -/
theorem appendixU_band_15_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    fixedFamilyRecurrentBand ctx = 4 := by
  unfold fixedFamilyRecurrentBand
  rw [hq, hK]
  exact fixedFamilyBand_15_2

/-- The recurrent band at the `(105,7)` datum is `4`. -/
theorem appendixU_band_105_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 7) :
    fixedFamilyRecurrentBand ctx = 4 := by
  unfold fixedFamilyRecurrentBand
  rw [hq, hK]
  exact fixedFamilyBand_105_7

/-- **`(3,1)` any-onset kill (value route)**: the pinned value `1/2^t` violates
`3 ∣ 2·2^t`. -/
theorem returnDatum_anyOnsetContinuation_void (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 3) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hcc : AnyOnsetBandContinuation ctx) : False := by
  obtain ⟨t, hQ, hval⟩ := return_datum_value_eq ctx hq hK
  obtain ⟨k₀, hgap⟩ := hcc
  rw [appendixU_band_3_1 ctx hq hK] at hgap
  have hval' : realWeightedValue (natBinaryAsReal ctx.d) = 1 / 2 ^ t := hval
  have heta : realWeightedValue (natBinaryAsReal ctx.d)
      = ((1 : ℤ) : ℝ) / ((2 ^ t : ℕ) : ℝ) := by
    rw [hval']
    push_cast
    ring
  have hdvd := constGap_carry_divides (Q := 2 ^ t) (P := 1)
    (Nat.two_pow_pos t) ctx.hd ctx.hnonterm heta ctx.n24CarryData.carry.hits hgap
  have he : (2 : ℕ) ^ 2 - 1 = 3 := by norm_num
  rw [he, show (2 ^ t * 2 : ℕ) = 2 * 2 ^ t by ring] at hdvd
  exact appendixU_odd_prime_not_dvd (by norm_num) (by norm_num) (by norm_num) t hdvd

/-- **`(21,3)` any-onset kill (value route)**: the pinned value `1/2^t` violates
`7 ∣ 3·2^t`. -/
theorem densePackDatum_anyOnsetContinuation_void (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3)
    (hcc : AnyOnsetBandContinuation ctx) : False := by
  obtain ⟨t, hQ, hval⟩ := densePack_datum_value_eq ctx hq hK
  obtain ⟨k₀, hgap⟩ := hcc
  rw [appendixU_band_21_3 ctx hq hK] at hgap
  have hval' : realWeightedValue (natBinaryAsReal ctx.d) = 1 / 2 ^ t := hval
  have heta : realWeightedValue (natBinaryAsReal ctx.d)
      = ((1 : ℤ) : ℝ) / ((2 ^ t : ℕ) : ℝ) := by
    rw [hval']
    push_cast
    ring
  have hdvd := constGap_carry_divides (Q := 2 ^ t) (P := 1)
    (Nat.two_pow_pos t) ctx.hd ctx.hnonterm heta ctx.n24CarryData.carry.hits hgap
  have he : (2 : ℕ) ^ 3 - 1 = 7 := by norm_num
  rw [he, show (2 ^ t * 3 : ℕ) = 3 * 2 ^ t by ring] at hdvd
  exact appendixU_odd_prime_not_dvd (by norm_num) (by norm_num) (by norm_num) t hdvd

/-- **`(15,1)` any-onset kill (value route)**: the pinned value `1/(5·2^t)`
violates `15 ∣ 20·2^t` (the factor `3`). -/
theorem towerFP15_1_anyOnsetContinuation_void (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hcc : AnyOnsetBandContinuation ctx) : False := by
  obtain ⟨t, hQ, hval⟩ := towerFP15_1_value_eq ctx hq hK
  obtain ⟨k₀, hgap⟩ := hcc
  rw [appendixU_band_15_1 ctx hq hK] at hgap
  have hval' : realWeightedValue (natBinaryAsReal ctx.d) = 1 / (5 * 2 ^ t) := hval
  have heta : realWeightedValue (natBinaryAsReal ctx.d)
      = ((1 : ℤ) : ℝ) / ((5 * 2 ^ t : ℕ) : ℝ) := by
    rw [hval']
    push_cast
    ring
  have hdvd := constGap_carry_divides (Q := 5 * 2 ^ t) (P := 1)
    (by positivity) ctx.hd ctx.hnonterm heta ctx.n24CarryData.carry.hits hgap
  have he : (2 : ℕ) ^ 4 - 1 = 15 := by norm_num
  rw [he] at hdvd
  have h3 : (3 : ℕ) ∣ 5 * 2 ^ t * 4 := dvd_trans (by norm_num) hdvd
  rw [show (5 * 2 ^ t * 4 : ℕ) = 20 * 2 ^ t by ring] at h3
  exact appendixU_odd_prime_not_dvd (by norm_num) (by norm_num) (by norm_num) t h3

/-- **`(15,2)` any-onset kill (value route)**: the pinned value `2/(3·2^t)`
violates `15 ∣ 12·2^t` (the factor `5`). -/
theorem towerFP15_2_anyOnsetContinuation_void (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (hcc : AnyOnsetBandContinuation ctx) : False := by
  obtain ⟨t, hQ, hval⟩ := towerFP15_2_value_eq ctx hq hK
  obtain ⟨k₀, hgap⟩ := hcc
  rw [appendixU_band_15_2 ctx hq hK] at hgap
  have hval' : realWeightedValue (natBinaryAsReal ctx.d) = 2 / (3 * 2 ^ t) := hval
  have heta : realWeightedValue (natBinaryAsReal ctx.d)
      = ((2 : ℤ) : ℝ) / ((3 * 2 ^ t : ℕ) : ℝ) := by
    rw [hval']
    push_cast
    ring
  have hdvd := constGap_carry_divides (Q := 3 * 2 ^ t) (P := 2)
    (by positivity) ctx.hd ctx.hnonterm heta ctx.n24CarryData.carry.hits hgap
  have he : (2 : ℕ) ^ 4 - 1 = 15 := by norm_num
  rw [he] at hdvd
  have h5 : (5 : ℕ) ∣ 3 * 2 ^ t * 4 := dvd_trans (by norm_num) hdvd
  rw [show (3 * 2 ^ t * 4 : ℕ) = 12 * 2 ^ t by ring] at h5
  exact appendixU_odd_prime_not_dvd (by norm_num) (by norm_num) (by norm_num) t h5

/-- **`(105,7)` any-onset kill (value route)**: the pinned value `1/2^t` violates
`15 ∣ 4·2^t` (the factor `3`). -/
theorem towerFP105_7_anyOnsetContinuation_void (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 7)
    (hcc : AnyOnsetBandContinuation ctx) : False := by
  obtain ⟨t, hQ, hval⟩ := towerFP105_7_value_eq ctx hq hK
  obtain ⟨k₀, hgap⟩ := hcc
  rw [appendixU_band_105_7 ctx hq hK] at hgap
  have hval' : realWeightedValue (natBinaryAsReal ctx.d) = 1 / 2 ^ t := hval
  have heta : realWeightedValue (natBinaryAsReal ctx.d)
      = ((1 : ℤ) : ℝ) / ((2 ^ t : ℕ) : ℝ) := by
    rw [hval']
    push_cast
    ring
  have hdvd := constGap_carry_divides (Q := 2 ^ t) (P := 1)
    (Nat.two_pow_pos t) ctx.hd ctx.hnonterm heta ctx.n24CarryData.carry.hits hgap
  have he : (2 : ℕ) ^ 4 - 1 = 15 := by norm_num
  rw [he] at hdvd
  have h3 : (3 : ℕ) ∣ 2 ^ t * 4 := dvd_trans (by norm_num) hdvd
  rw [show (2 ^ t * 4 : ℕ) = 4 * 2 ^ t by ring] at h3
  exact appendixU_odd_prime_not_dvd (by norm_num) (by norm_num) (by norm_num) t h3

/-- **THE FIVE-FAMILY ANY-ONSET KILL**: at every fixed-family hit the
band-constant continuation is absurd at ANY onset — strictly beyond the in-tree
window-onset kill `fixedFamily_cleanContinuation_void` (which demands
`a k₀ ≤ X`). -/
theorem fixedFamilyHit_anyOnsetContinuation_void (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hcc : AnyOnsetBandContinuation ctx) : False := by
  rcases hhit with ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩
  · exact returnDatum_anyOnsetContinuation_void ctx hq hK hcc
  · exact densePackDatum_anyOnsetContinuation_void ctx hq hK hcc
  · exact towerFP15_1_anyOnsetContinuation_void ctx hq hK hcc
  · exact towerFP15_2_anyOnsetContinuation_void ctx hq hK hcc
  · exact towerFP105_7_anyOnsetContinuation_void ctx hq hK hcc

/-- The any-onset kill at every orbit pin (the pins are fixed-family hits). -/
theorem fixedPin_anyOnsetContinuation_void (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2 ∨ Band3PinnedWide ctx ∨ OrbitBandPinned ctx 4)
    (hcc : AnyOnsetBandContinuation ctx) : False :=
  fixedFamilyHit_anyOnsetContinuation_void ctx
    (fixedFamilyHit_of_anyPin ctx hpin) hcc

/-- The U.1 verbatim (window-onset) kill at the pins — the shell route
(`fixedFamily_cleanContinuation_void`), recorded in the pin shape. -/
theorem fixedPin_windowContinuation_void (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2 ∨ Band3PinnedWide ctx ∨ OrbitBandPinned ctx 4)
    (hcc : FixedFamilyCleanContinuation ctx) : False :=
  fixedFamily_cleanContinuation_void ctx (fixedFamilyHit_of_anyPin ctx hpin) hcc

/-! ## Part 3.  The exit-ledger bridge (the binary classification route) -/

/-- **The continuation IS an exit-free L.3.1 ledger tail**: the any-onset band
continuation is EQUIVALENT to the eventual vanishing of the exit weights — the
sharpest in-tree reduction of the confinement: a long-enough exit-free tail of
the gap sequence is exactly what the atom demands. -/
theorem anyOnsetContinuation_iff_exitFreeTail (ctx : ActualFailureContext) :
    AnyOnsetBandContinuation ctx
      ↔ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → emExitWeight ctx k = 0 := by
  constructor
  · rintro ⟨k₀, hg⟩
    exact ⟨k₀, fun k hk => mdc_nonExit_weight_eq_zero ctx (hg k hk)⟩
  · rintro ⟨k₀, hw⟩
    refine ⟨k₀, fun k hk => ?_⟩
    have hwk := hw k hk
    by_cases h : hitGap ctx.n24CarryData.a k = fixedFamilyRecurrentBand ctx
    · exact h
    · exfalso
      unfold emExitWeight at hwk
      rw [if_neg h] at hwk
      have hlt : ctx.n24CarryData.a k < ctx.n24CarryData.a (k + 1) :=
        ctx.n24CarryData.carry.hits.strict (Nat.lt_succ_self k)
      unfold hitGap at hwk
      omega

/-- The in-tree pressure-relocation floor at every fixed hit (re-export, the
honest counterweight): the exits carry at least HALF the reach span — the
confinement atom demands they vacate a tail nonetheless. -/
theorem confinement_exitMass_floor (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) : ctx.shell.X ≤ 2 * emExitMass ctx :=
  fixedFamily_exitMass_lower ctx hhit

/-! ## Part 4.  THE CONFINEMENT ATOM and the conditional closure of
`deepOrbitPin` -/

/-- **THE CONFINEMENT ATOM (Appendix U's missing step, named)**: at every deep
(`X > 2^986891`) band-2/3/4-pinned context the word's hit gaps are eventually
the recurrent band — the v22 `lem:u-fixed-pin-periodic-continuation`
transcribed to the PIN hypothesis class (strictly smaller than the
fixed-family-hit class) and weakened to ANY onset (admissible by the new
value-route kill; the manuscript's own claim is the window-onset form). -/
def FixedPinCleanContinuation : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 986891 < ctx.X →
    (OrbitBandPinned ctx 2 ∨ Band3PinnedWide ctx ∨ OrbitBandPinned ctx 4) →
    AnyOnsetBandContinuation ctx

/-- **THE CONDITIONAL KILL**: the confinement atom supplies the FULL
`DeepOrbitPinVoiding` — the summit field `deepOrbitPin`, verbatim. -/
theorem deepOrbitPinVoiding_of_confinement (h : FixedPinCleanContinuation) :
    DeepOrbitPinVoiding := by
  intro ctx hX
  refine ⟨fun hpin => ?_, fun hpin => ?_, fun hpin => ?_⟩
  · exact fixedPin_anyOnsetContinuation_void ctx (Or.inl hpin)
      (h ctx hX (Or.inl hpin))
  · exact fixedPin_anyOnsetContinuation_void ctx (Or.inr (Or.inl hpin))
      (h ctx hX (Or.inr (Or.inl hpin)))
  · exact fixedPin_anyOnsetContinuation_void ctx (Or.inr (Or.inr hpin))
      (h ctx hX (Or.inr (Or.inr hpin)))

/-- **No free lunch (honest)**: the confinement atom is EQUIVALENT to the
voiding it feeds — the kill empties the atom's hypothesis class.  The atom is
the manuscript-language FORM of the residual `DeepOrbitPinVoiding`, not a
strictly weaker waypoint. -/
theorem fixedPinCleanContinuation_iff_deepOrbitPinVoiding :
    FixedPinCleanContinuation ↔ DeepOrbitPinVoiding := by
  constructor
  · exact deepOrbitPinVoiding_of_confinement
  · intro hv ctx hX hpin
    rcases hpin with hp | hp | hp
    · exact absurd hp (hv ctx hX).1
    · exact absurd hp (hv ctx hX).2.1
    · exact absurd hp (hv ctx hX).2.2

/-- The Appendix-U confinement atom is exactly the wave-8 deep fixed-family axis.
This is the direct version of the two-step equivalence through `DeepOrbitPinVoiding`. -/
theorem fixedPinCleanContinuation_iff_deepFixedFamilyVoid :
    FixedPinCleanContinuation ↔ DeepFixedFamilyVoid :=
  fixedPinCleanContinuation_iff_deepOrbitPinVoiding.trans
    deepOrbitPinVoiding_iff_deepFixedFamilyVoid

/-- The atom rebuilds the three v17 capstone voiding fields. -/
theorem threeVoidings_of_confinement (h : FixedPinCleanContinuation) :
    (∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 2)
      ∧ (∀ ctx : ActualFailureContext, ¬ Band3PinnedWide ctx)
      ∧ (∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 4) :=
  deepOrbitPinVoiding_iff_voidings.mp (deepOrbitPinVoiding_of_confinement h)

/-- The atom rebuilds the wave-8 deep family axis. -/
theorem deepFixedFamilyVoid_of_confinement (h : FixedPinCleanContinuation) :
    DeepFixedFamilyVoid :=
  threeVoidings_iff_deepFixedFamilyVoid.mp (threeVoidings_of_confinement h)

/-- **The summit wiring**: the confinement atom plus the REST of the summit
surface (as a function of the supplied pin axis) reaches the endpoint
`Erdos260Statement` — the `deepOrbitPin` field is exactly
`deepOrbitPinVoiding_of_confinement h`. -/
theorem erdos260_of_confinement_and_rest (h : FixedPinCleanContinuation)
    (rest : DeepOrbitPinVoiding → Erdos260SummitResidual) : Erdos260Statement :=
  erdos260_of_summitResidual (rest (deepOrbitPinVoiding_of_confinement h))

/-- The FAMILY-level confinement (the larger hypothesis class: every deep
fixed-family hit, pinned or not, carries the continuation) — it supplies the
pushed family voiding outright and the pin atom a fortiori. -/
def DeepFixedFamilyAnyOnsetContinuation : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 986891 < ctx.X → FixedFamilyHit ctx →
    AnyOnsetBandContinuation ctx

/-- The family-level confinement supplies the pushed deep family voiding. -/
theorem deepFixedFamilyVoidPush_of_anyOnsetContinuation
    (h : DeepFixedFamilyAnyOnsetContinuation) : DeepFixedFamilyVoidPush :=
  fun ctx hX hhit =>
    (fixedFamilyHit_anyOnsetContinuation_void ctx hhit (h ctx hX hhit)).elim

/-- The family-level confinement supplies the pin atom. -/
theorem fixedPinCleanContinuation_of_family
    (h : DeepFixedFamilyAnyOnsetContinuation) : FixedPinCleanContinuation :=
  fun ctx hX hpin => h ctx hX (fixedFamilyHit_of_anyPin ctx hpin)

/-! ## Part 5.  U.2: the sevenths split — the periodic half proved, the
exit-active residual named -/

/-- **The U.2 cycle-persistent (period-three) sevenths stratum**: a
window-compatible onset with all later hit gaps equal to `3` (the period of the
`1/7..6/7` digit table). -/
def SeventhsPeriodicContinuation (ctx : ActualFailureContext) : Prop :=
  ∃ k₀ : ℕ, ctx.n24CarryData.a k₀ ≤ ctx.X ∧
    ∀ k, k₀ ≤ k → hitGap ctx.n24CarryData.a k = 3

/-- **U.2's sound half, proved**: the period-three continuation is VOID at every
failing context (no sevenths pin even needed) — the constant-gap-3 instance of
the certified-cycle collision, density `1/3 > 17/2^24`. -/
theorem seventhsPeriodicContinuation_void (ctx : ActualFailureContext)
    (h : SeventhsPeriodicContinuation ctx) : False := by
  obtain ⟨k₀, honset, hgap⟩ := h
  exact constGap_continuation_void ctx (by norm_num) (by norm_num) honset hgap

/-- **The honest asymmetry**: the sevenths value `P/(7·2^t)` PASSES the
value-route divisibility at gap `3` — `7 ∣ (7·2^t)·3` — so the carry obstruction
does NOT kill the sevenths periodic stratum at off-window onsets; only the shell
route (window-compatible onset) applies there. -/
theorem sevenths_divisibility_consistent (t : ℕ) :
    (2 ^ 3 - 1 : ℕ) ∣ (7 * 2 ^ t) * 3 := by
  refine ⟨2 ^ t * 3, ?_⟩
  have he : (2 : ℕ) ^ 3 - 1 = 7 := by norm_num
  rw [he]
  ring

/-- **The exit-active sevenths residual (the W2 obligation, named)**: the deep
sevenths-pinned contexts WITHOUT the periodic continuation must be refuted.
The v22 V/W route to it (the `1/30` mass floors + the T.2 cap) is NOT
transcribed: the floors are asserted, not proved (analysis Bug 4), and T.2
inherits the refuted Appendix R chain. -/
def DeepSeventhsExitActiveVoid : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
    ∀ t : ℕ, ∀ P : ℤ, 2 ^ t ≤ ctx.Q →
      realWeightedValue (natBinaryAsReal ctx.d) = (P : ℝ) / ((7 * 2 ^ t : ℕ) : ℝ) →
      ¬ SeventhsPeriodicContinuation ctx → False

/-- **The U.2 reduction of `DeepSeventhsPinVoid`**: the periodic branch is
discharged by the constant-gap collision; only the exit-active residual
remains. -/
theorem deepSeventhsPinVoid_of_exitActiveVoid (h : DeepSeventhsExitActiveVoid) :
    DeepSeventhsPinVoid := by
  intro ctx hX t P h2t heta
  by_cases hper : SeventhsPeriodicContinuation ctx
  · exact seventhsPeriodicContinuation_void ctx hper
  · exact h ctx hX t P h2t heta hper

/-! ## Part 6.  The U.1 density floor, re-exported in the manuscript's shape -/

/-- **`lem:u-periodic-density-floor`, verbatim re-export**: a nonzero word of
eventual period `p ≤ 2^19` has no `c0`-sparse shell at any window-compatible
scale — this IS the in-tree `periodic_no_sparse_shell`; Appendix U's density
floor adds nothing beyond it. -/
theorem appendixU_periodicDensityFloor {d : ℕ → ℕ} {x p L : ℕ}
    (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d)
    (hp : 0 < p) (hple : p ≤ 524288)
    (hper : ∀ n, x < n → d (n + p) = d n)
    (hx : x ≤ 2 ^ L) (hL : 28 ≤ L) :
    ¬ ShellSparseAt d L :=
  periodic_no_sparse_shell hd hnonterm hp hple hper hx hL

/-! ## Part 7.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the Appendix U pin-voiding pass. -/
def appendixUPinVoidingStatus : List String :=
  [ "U TRANSCRIPTION VERDICT (exact): Appendix U = three components.  (1) " ++
      "lem:u-periodic-density-floor IS the in-tree periodic_no_sparse_shell " ++
      "(re-export appendixU_periodicDensityFloor); (2) the period table / " ++
      "dyadic-clean cap is subsumed by constGap_continuation_void (any constant " ++
      "gap 0 < g <= 2^19, window onset); (3) the ONLY new content is " ++
      "lem:u-fixed-pin-periodic-continuation - the CONFINEMENT (retained pinned " ++
      "branch follows the clean continuation), whose manuscript proof consumes " ++
      "the untranscribed priority-deletion framework.  It is stated here as the " ++
      "named atom FixedPinCleanContinuation, exactly as the Wave-22 analysis " ++
      "predicted (Lane C: 'conditionally formalizable - one new confinement " ++
      "atom').",
    "NEW UNCONDITIONAL THEOREM (the value route): constGap_carry_divides - any " ++
      "non-terminating binary word with weighted value P/Q and eventually " ++
      "constant hit gap g satisfies (2^g - 1) | Q*g (carry recurrence z' = " ++
      "2^g z - Q*pos; exponential homogeneous deviation vs the linear carry " ++
      "envelope 0 < z <= Q(pos+2) forces the exact particular solution; its " ++
      "integrality is the divisibility).  At the five fixed data the pinned " ++
      "values VIOLATE it: 3 | 2*2^t at (3,1); 7 | 3*2^t at (21,3); 15 | 20*2^t " ++
      "at (15,1); 15 | 12*2^t at (15,2); 15 | 4*2^t at (105,7) - all false.  " ++
      "Hence fixedFamilyHit_anyOnsetContinuation_void: the band continuation is " ++
      "absurd at ANY onset, strictly beyond the in-tree window-onset kill " ++
      "(fixedFamily_cleanContinuation_void needs a(k0) <= X).  This PROVES the " ++
      "brief's value tension: the canonical continuation's value is non-dyadic " ++
      "(odd part (2^g-1)^2 up to the head) against the exactly-pinned value.",
    "THE CONFINEMENT ATOM: FixedPinCleanContinuation - at deep (X > 2^986891) " ++
      "band-2/3/4-pinned contexts the hit gaps are eventually the recurrent " ++
      "band, onset UNCONSTRAINED (weaker than the manuscript's own window-onset " ++
      "U.1 claim, admissible because of the value-route kill; also restricted " ++
      "to the PIN class, smaller than DeepFixedFamilyCleanContinuation's " ++
      "fixed-hit class).  CONDITIONAL CLOSURE (proved): " ++
      "deepOrbitPinVoiding_of_confinement supplies the summit field " ++
      "deepOrbitPin VERBATIM; threeVoidings_of_confinement and " ++
      "deepFixedFamilyVoid_of_confinement rebuild the v17 fields and the " ++
      "wave-8 axis; erdos260_of_confinement_and_rest reaches the endpoint " ++
      "given the rest of the summit surface.",
    "NO FREE LUNCH (honest): fixedPinCleanContinuation_iff_deepOrbitPinVoiding " ++
      "- the atom is EQUIVALENT to the voiding it feeds (the kill empties its " ++
      "hypothesis class), the same phenomenon FixedFamilyPeriodicity proved for " ++
      "the window-onset form.  The atom is the manuscript-language FORM of the " ++
      "residual, not a strictly weaker waypoint.  Unconditional progress here " ++
      "is the KILL side (any onset, value route), not the supply side.",
    "THE BINARY-CLASSIFICATION BRIDGE (proved): " ++
      "anyOnsetContinuation_iff_exitFreeTail - the continuation is EXACTLY an " ++
      "eventually-exit-free L.3.1 ledger tail (emExitWeight = 0 from some " ++
      "index).  Honest counterweight (re-export confinement_exitMass_floor = " ++
      "fixedFamily_exitMass_lower): at every fixed hit X <= 2*emExitMass - " ++
      "exits carry HALF the reach span, every class-0 fibre window contains an " ++
      "exit (mdcFibre0_window_has_exit), so the atom demands the exits vacate " ++
      "a TAIL while the pressure relocation keeps them pervasive in the reach " ++
      "window: the two regimes are the substance of the kill, and no in-tree " ++
      "mechanism produces an unconditional long exit-free window at the pins " ++
      "(the brief's hoped-for exit-free-window floor does NOT exist in tree; " ++
      "the opposite floor does).",
    "U.2 SEVENTHS (the sound parts): seventhsPeriodicContinuation_void - the " ++
      "cycle-persistent period-three stratum is VOID at window-compatible " ++
      "onset (no pin needed; g = 3 instance of the certified-cycle collision); " ++
      "deepSeventhsPinVoid_of_exitActiveVoid - DeepSeventhsPinVoid reduces to " ++
      "the named exit-active residual DeepSeventhsExitActiveVoid (the W2 " ++
      "obligation).  HONEST ASYMMETRY (proved): " ++
      "sevenths_divisibility_consistent - 7 | (7*2^t)*3, the value route does " ++
      "NOT kill the sevenths periodic stratum at off-window onsets; the " ++
      "sevenths kill is shell-route only.",
    "S/V/W NOT TRANSCRIBED (flagged, analysis Bug 4): the 1/30 floors " ++
      "(lem:s-sevenths-exit-floor, lem:v-certified-seventh-floor) upgrade " ++
      "'nonempty after priority deletion' to mass >= (1/30)X|I_j| with no " ++
      "proof (the cited relocated pressure floor lem:q-fixed-pin-exit-lower " ++
      "is itself asserted); W's certification lemmas consume T.2 = the " ++
      "Appendix R exit-share chain, which the analysis refutes in the " ++
      "consumable shape (emfc_spacedShare_not_covering).  No sound V/W " ++
      "fragment survives beyond the reduction recorded here.",
    "HONEST RESIDUAL AFTER THIS MODULE: the open content of the deep pin axis " ++
      "is exactly FixedPinCleanContinuation (equivalently DeepOrbitPinVoiding, " ++
      "equivalently DeepFixedFamilyVoid) - now with a STRICTLY LARGER kill " ++
      "surface (any-onset continuations die, not only window-onset ones), so " ++
      "any future supply argument may place the periodicity onset anywhere; " ++
      "plus the sevenths exit-active residual DeepSeventhsExitActiveVoid for " ++
      "the value-axis record DeepSeventhsPinVoid.",
    "HYGIENE: additive only - ONE new module, no existing file edited, root " ++
      "import untouched; no sorry / admit / new axiom / native_decide; every " ++
      "key declaration passes #print axioms within [propext, Classical.choice, " ++
      "Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem appendixUPinVoidingStatus_nonempty : appendixUPinVoidingStatus ≠ [] := by
  simp [appendixUPinVoidingStatus]

/-! ## Part 8.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]`
or fewer. -/

#print axioms appendixU_linear_lt_two_pow
#print axioms appendixU_int_escape
#print axioms appendixU_odd_prime_not_dvd
#print axioms constGap_interior_zero
#print axioms constGap_carry_step
#print axioms constGap_carry_divides
#print axioms anyOnset_of_cleanContinuation
#print axioms appendixU_band_3_1
#print axioms appendixU_band_21_3
#print axioms appendixU_band_15_1
#print axioms appendixU_band_15_2
#print axioms appendixU_band_105_7
#print axioms returnDatum_anyOnsetContinuation_void
#print axioms densePackDatum_anyOnsetContinuation_void
#print axioms towerFP15_1_anyOnsetContinuation_void
#print axioms towerFP15_2_anyOnsetContinuation_void
#print axioms towerFP105_7_anyOnsetContinuation_void
#print axioms fixedFamilyHit_anyOnsetContinuation_void
#print axioms fixedPin_anyOnsetContinuation_void
#print axioms fixedPin_windowContinuation_void
#print axioms anyOnsetContinuation_iff_exitFreeTail
#print axioms confinement_exitMass_floor
#print axioms deepOrbitPinVoiding_of_confinement
#print axioms fixedPinCleanContinuation_iff_deepOrbitPinVoiding
#print axioms fixedPinCleanContinuation_iff_deepFixedFamilyVoid
#print axioms threeVoidings_of_confinement
#print axioms deepFixedFamilyVoid_of_confinement
#print axioms erdos260_of_confinement_and_rest
#print axioms deepFixedFamilyVoidPush_of_anyOnsetContinuation
#print axioms fixedPinCleanContinuation_of_family
#print axioms seventhsPeriodicContinuation_void
#print axioms sevenths_divisibility_consistent
#print axioms deepSeventhsPinVoid_of_exitActiveVoid
#print axioms appendixU_periodicDensityFloor
#print axioms appendixUPinVoidingStatus_nonempty

end

end Erdos260
