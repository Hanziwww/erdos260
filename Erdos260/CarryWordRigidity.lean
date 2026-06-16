import Erdos260.DyadicValueLever

/-!
# Carry-word rigidity — the integer-carry route against the failing-shell sparsity

This module (NEW; it edits no existing file) executes the proof route recorded at the end of
`DyadicValueLever.lean`: run the exact integer carry recursion
`R_{N+1} = 2·R_N − Q·(N+1)·d_{N+1}` (`integerCarry`, with `R_N = 2^N·(P − Q·S_N)` scaled to an
integer) against the failing-shell support-sparsity bound `|supportShell d X| < c0·X`.

## Part 1 — the carry congruence and the 2-adic divisibility

* `dvd_integerCarry_sub_pow_mul`: `Q ∣ R_N − 2^N·P` — the complete congruence content of the
  recursion (each step doubles and subtracts a multiple of `Q`).
* `two_pow_dvd_integerCarry` / `two_pow_le_integerCarry_of_pos`: writing `Q = u·2^t`, for
  `N ≥ t` the carry is divisible by `2^t`, so a positive carry is at least `2^t`.

## Part 2 — the termination dichotomy (`R_N = 0` from some point iff the expansion terminates)

* `eventuallyZero_of_integerCarry_eq_zero`: once the carry vanishes it stays zero and all
  later digits are forced to `0`.
* `integerCarry_eq_zero_of_eventuallyZero`: if the digits terminate, the carry must vanish
  (else the doubling `R_{M+h} = 2^h·R_M` beats the linear envelope `Q·(M+h+2)`).
* `integerCarry_exists_zero_iff_eventuallyZero` — the dichotomy, exactly.
* `integerCarry_pos_of_not_eventuallyZero`: on a non-terminating sequence the carry is
  positive at EVERY index (no later-one witness needed).

## Part 3 — the rigidity window (the next support element is forced)

* `pow_two_le_oddpart_of_zero_gap` — **the t-free gap bound**: with `Q = u·2^t` and `N ≥ t`,
  an all-zero gap of length `h` after `N` forces `2^h ≤ u·(N+h+2)`.  The `2^t` part of the
  denominator CANCELS (the carry is `≥ 2^t` by Part 1), so only the odd part `u` survives.
* `exists_one_in_window`: contrapositively, if `u·(N+h+2) < 2^h` there is a one in
  `(N, N+h]` — the next support element lies within an explicit `≈ log₂(u·N)` window.
* `dyadicValue_next_one`: the literal suggested route — value `1/2^t`, `Q = 2^t`, `P = 1`,
  forcing a one in `(N, N+h]` whenever `N+h+2 < 2^h`.

## Part 4 — the periodic denominators `1/(5·2^t)` and `2/(3·2^t)` (honest finding)

In the WEIGHTED recursion the digit term carries the factor `Q`, so modulo the odd factor
`u ∣ Q` the digits are INVISIBLE: `R_{N+1} ≡ 2·R_N (mod u)`, hence `R_N ≡ 2^N·P (mod u)`.
The hoped-for "periodic digit hits with density `1/ord_2(5) = 1/4` (resp. `1/2`)" does NOT
exist for this recursion — the periodicity lives entirely in the carry residue, not in the
digits.  What DOES survive:

* `integerCarry_ne_zero_of_odd_dvd`: `u ∣ Q`, `u` odd, `u ∤ P` force `R_N ≠ 0` for ALL `N`.
* `fifthValue_not_eventuallyZero` / `thirdsValue_not_eventuallyZero`: the values `1/(5·2^t)`
  and `2/(3·2^t)` have NO terminating binary realization — non-termination is forced by the
  value alone (in contrast to the dyadic `1/2^t`, which `dyadicValue_family_data_consistent`
  realizes both ways).  Since the shells already carry `hnonterm`, this voids nothing extra;
  the quantitative content of both periodic families is the same `u ∈ {3, 5}` window bound
  of Part 3.

## Part 5 — the support-count lower bound in the dyadic shell

* `supportShell_card_lower_of_gap`: if `u·(2X+2) < 2^g` (and `t ≤ X`), every length-`g`
  block of `(X, 2X]` contains a support element, so `X/g ≤ |supportShell d X|`.
* `supportShell_sparse_contradiction`: against `|supportShell d X| < c0·X` this is absurd as
  soon as `2g ≤ X` and `c0·(2g) ≤ 1`.

## Part 6 — the scale-bounded voiding (what closes, with exact thresholds)

The pinned failure constant is `c0 = manuscriptC0 = κ/64 = 17/16777216`.  With `X = 2^L`:

* every ctx has `Q < 2^(L−27)` (scale bound), so `g := 2L−25` works and the contradiction
  fires iff `17·(4L−50) ≤ 16777216`, i.e. `L ≤ 246736`:
  `actualFailureContext_scale_lower` — **UNCONDITIONAL: every failing context has
  `X > 2^246736`** (margin: `17·986894 = 16777198 ≤ 16777216`).
* with a value pin `value = P/(u·2^t)`, `u ≤ 7`, the t-free bound allows `g := L+4` and the
  contradiction fires iff `17·(2L+8) ≤ 16777216`, i.e. `L ≤ 493443`:
  `shellValueDyadic_scale_lower`, `fixedFamilyHit_scale_lower` (all five fixed families),
  `towerFifthValue_void_of_scale`, `towerThirdsValue_void_of_scale` — **pinned-value
  contexts need `X > 2^493443`**.

## Part 7 — what resists, and the deep residual levers (honest)

For `L > 493443` the rigidity density `≈ 1/(L+4)` is BELOW `c0` and the sparsity bound is
consistent with the carry rigidity; the failure structure only guarantees failing shells at
arbitrarily LARGE `X` (the wrong direction), so no choice of scale rescues the argument.
The full levers therefore remain open; the residual successor Props quantify ONLY over the
deep tail `X > 2^493443`:

* `DeepDyadicValueLever → DyadicValueLever` (`dyadicValueLever_of_deepScale`),
* `DeepTowerFifthValueLever → TowerFifthValueLever`, `DeepTowerThirdsValueLever →
  TowerThirdsValueLever`,
* `DeepFixedFamilyVoid → ∀ ctx, ¬FixedFamilyHit ctx` (`fixedFamilyHit_void_of_deepScale`) —
  ONE deep Prop voids all five families, including the two periodic pairs.
* Wiring (additive): `towerEscapeLever_of_towerEscape_deep` /
  `towerEscapeLever_of_towerEscape_deepFamilies`, `towerFixedPointResidual_of_deepLever`,
  and the endpoint `erdos260_of_deepDyadicValueLever` through `Erdos260DeepLeverResidual`.

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 0.  Elementary growth helpers -/

/-- `n² < 2^n` for `n ≥ 5`. -/
theorem carryWord_sq_lt_two_pow {n : ℕ} (hn : 5 ≤ n) : n * n < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have h1 : 2 * n + 1 ≤ n * n := by nlinarith
      have h2 : (n + 1) * (n + 1) = n * n + (2 * n + 1) := by ring
      have h3 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      omega

/-- The exponential beats any affine-in-`h` bound: `∃ h, a·(b+h) < 2^h`. -/
theorem carryWord_exists_mul_add_lt_two_pow (a b : ℕ) : ∃ h : ℕ, a * (b + h) < 2 ^ h := by
  refine ⟨(a + b + 5) * (a + b + 5), ?_⟩
  have hm5 : 5 ≤ a + b + 5 := by omega
  have hmm5 : 5 ≤ (a + b + 5) * (a + b + 5) := by nlinarith
  have hsq : ((a + b + 5) * (a + b + 5)) * ((a + b + 5) * (a + b + 5))
      < 2 ^ ((a + b + 5) * (a + b + 5)) := carryWord_sq_lt_two_pow hmm5
  have h1 : a * (b + (a + b + 5) * (a + b + 5))
      ≤ (a + b + 5) * ((a + b + 5) + (a + b + 5) * (a + b + 5)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : (a + b + 5) * ((a + b + 5) + (a + b + 5) * (a + b + 5))
      ≤ ((a + b + 5) * (a + b + 5)) * ((a + b + 5) * (a + b + 5)) := by nlinarith
  exact lt_of_le_of_lt (h1.trans h2) hsq

/-! ## Part 1.  The carry congruence and the 2-adic divisibility -/

/-- **The complete congruence content of the carry recursion**: `Q ∣ R_N − 2^N·P` (each step
doubles and subtracts a multiple of `Q`). -/
theorem dvd_integerCarry_sub_pow_mul (Q : ℕ) (P : ℤ) (d : ℕ → ℕ) (N : ℕ) :
    (Q : ℤ) ∣ integerCarry Q P d N - 2 ^ N * P := by
  induction N with
  | zero => simp
  | succ N ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨2 * c - ((N + 1 : ℕ) : ℤ) * (d (N + 1) : ℤ), ?_⟩
      rw [integerCarry_succ]
      linear_combination (2 : ℤ) * hc

/-- Writing `Q = u·2^t`, the carry at any index `N ≥ t` is divisible by `2^t` (both `2^N·P`
and `Q` are). -/
theorem two_pow_dvd_integerCarry {Q u t : ℕ} (hQfact : Q = u * 2 ^ t)
    (P : ℤ) (d : ℕ → ℕ) {N : ℕ} (htN : t ≤ N) :
    (2 : ℤ) ^ t ∣ integerCarry Q P d N := by
  have h1 : (2 : ℤ) ^ t ∣ (Q : ℤ) := by
    refine ⟨(u : ℤ), ?_⟩
    rw [hQfact]; push_cast; ring
  have h2 : (2 : ℤ) ^ t ∣ integerCarry Q P d N - 2 ^ N * P :=
    h1.trans (dvd_integerCarry_sub_pow_mul Q P d N)
  have h3 : (2 : ℤ) ^ t ∣ 2 ^ N * P :=
    dvd_mul_of_dvd_left (pow_dvd_pow 2 htN) P
  have h4 : integerCarry Q P d N
      = (integerCarry Q P d N - 2 ^ N * P) + 2 ^ N * P := by ring
  rw [h4]
  exact dvd_add h2 h3

/-- A positive carry at `N ≥ t` is at least `2^t` (`Q = u·2^t`). -/
theorem two_pow_le_integerCarry_of_pos {Q u t : ℕ} (hQfact : Q = u * 2 ^ t)
    (P : ℤ) (d : ℕ → ℕ) {N : ℕ} (htN : t ≤ N)
    (hRpos : 0 < integerCarry Q P d N) :
    (2 : ℤ) ^ t ≤ integerCarry Q P d N :=
  Int.le_of_dvd hRpos (two_pow_dvd_integerCarry hQfact P d htN)

/-! ## Part 2.  The termination dichotomy -/

/-- **Forward dichotomy**: once the carry vanishes it stays zero and all later digits are
forced to `0` — the expansion terminates. -/
theorem eventuallyZero_of_integerCarry_eq_zero {Q : ℕ} {P : ℤ} {d : ℕ → ℕ}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    {N : ℕ} (h0 : integerCarry Q P d N = 0) : EventuallyZero d := by
  have key : ∀ k : ℕ, integerCarry Q P d (N + k) = 0 ∧ (1 ≤ k → d (N + k) = 0) := by
    intro k
    induction k with
    | zero => exact ⟨h0, by omega⟩
    | succ k ih =>
        have hQz : (0 : ℤ) < (Q : ℤ) := by exact_mod_cast hQ
        have hMz : (0 : ℤ) < ((N + k + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos (N + k)
        have hQM : (0 : ℤ) < (Q : ℤ) * ((N + k + 1 : ℕ) : ℤ) := mul_pos hQz hMz
        rcases hd (N + k + 1) with hz | ho
        · constructor
          · show integerCarry Q P d ((N + k) + 1) = 0
            rw [integerCarry_succ, ih.1, hz]
            simp
          · intro _
            exact hz
        · exfalso
          have hb := (integerCarry_bounds_of_rational_value
            (Q := Q) (P := P) (d := d) (N + k + 1) hQ hd heta).1
          rw [integerCarry_succ, ih.1, ho] at hb
          push_cast at hb
          push_cast at hQM
          nlinarith [hb, hQM]
  refine ⟨N + 1, fun n hn => ?_⟩
  have h := (key (n - N)).2 (by omega)
  rwa [show N + (n - N) = n by omega] at h

/-- **Backward dichotomy**: if the digits terminate, the carry vanishes somewhere (else the
doubling across the all-zero tail beats the linear carry envelope). -/
theorem integerCarry_eq_zero_of_eventuallyZero {Q : ℕ} {P : ℤ} {d : ℕ → ℕ}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hev : EventuallyZero d) : ∃ N : ℕ, integerCarry Q P d N = 0 := by
  obtain ⟨M, hM⟩ := hev
  refine ⟨M, ?_⟩
  by_contra h0
  have hb0 := (integerCarry_bounds_of_rational_value
    (Q := Q) (P := P) (d := d) M hQ hd heta).1
  have hpos : 0 < integerCarry Q P d M := lt_of_le_of_ne hb0 (Ne.symm h0)
  obtain ⟨h, hh⟩ := carryWord_exists_mul_add_lt_two_pow Q (M + 2)
  have hgap := pow_two_le_of_zero_gap (Q := Q) (P := P) (d := d) (N := M) (h := h)
    hQ hd heta hpos (fun j hj1 hj2 => hM j (by omega))
  have hh' : Q * (M + h + 2) < 2 ^ h := by
    have he : M + 2 + h = M + h + 2 := by omega
    rwa [he] at hh
  have hcast : (Q : ℤ) * ((M + h + 2 : ℕ) : ℤ) < 2 ^ h := by exact_mod_cast hh'
  exact absurd hgap (not_le.mpr hcast)

/-- **The dichotomy, exactly**: the carry vanishes somewhere iff the expansion terminates. -/
theorem integerCarry_exists_zero_iff_eventuallyZero {Q : ℕ} {P : ℤ} {d : ℕ → ℕ}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) :
    (∃ N : ℕ, integerCarry Q P d N = 0) ↔ EventuallyZero d := by
  constructor
  · rintro ⟨N, h0⟩
    exact eventuallyZero_of_integerCarry_eq_zero hQ hd heta h0
  · exact integerCarry_eq_zero_of_eventuallyZero hQ hd heta

/-- On a non-terminating sequence the carry is POSITIVE at every index (the nonnegativity
bound upgraded through the dichotomy; no later-one witness needed). -/
theorem integerCarry_pos_of_not_eventuallyZero {Q : ℕ} {P : ℤ} {d : ℕ → ℕ}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hnonterm : ¬ EventuallyZero d) (N : ℕ) :
    0 < integerCarry Q P d N := by
  have hb := (integerCarry_bounds_of_rational_value
    (Q := Q) (P := P) (d := d) N hQ hd heta).1
  rcases lt_or_eq_of_le hb with hlt | heq
  · exact hlt
  · exact absurd (eventuallyZero_of_integerCarry_eq_zero hQ hd heta heq.symm) hnonterm

/-! ## Part 3.  The rigidity window -/

/-- **The t-free gap bound**: with `Q = u·2^t`, `N ≥ t` and positive carry, an all-zero gap
of length `h` after `N` forces `2^h ≤ u·(N+h+2)` — the `2^t` part of the denominator cancels
against the 2-adic lower bound on the carry, leaving only the odd part `u`. -/
theorem pow_two_le_oddpart_of_zero_gap {Q u t : ℕ} {P : ℤ} {d : ℕ → ℕ} {N h : ℕ}
    (hQfact : Q = u * 2 ^ t) (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (htN : t ≤ N) (hRpos : 0 < integerCarry Q P d N)
    (hzero : ∀ j : ℕ, N < j → j ≤ N + h → d j = 0) :
    (2 : ℤ) ^ h ≤ (u : ℤ) * ((N + h + 2 : ℕ) : ℤ) := by
  have hupper := (integerCarry_bounds_of_rational_value
    (Q := Q) (P := P) (d := d) (N + h) hQ hd heta).2
  have hrun := integerCarry_add_of_zero_digits Q P d N h hzero
  have hge : (2 : ℤ) ^ t ≤ integerCarry Q P d N :=
    two_pow_le_integerCarry_of_pos hQfact P d htN hRpos
  have hQcast : (Q : ℤ) = (u : ℤ) * 2 ^ t := by rw [hQfact]; push_cast; ring
  have hchain : (2 : ℤ) ^ h * 2 ^ t
      ≤ ((u : ℤ) * ((N + h + 2 : ℕ) : ℤ)) * 2 ^ t := by
    calc (2 : ℤ) ^ h * 2 ^ t
        ≤ 2 ^ h * integerCarry Q P d N :=
          mul_le_mul_of_nonneg_left hge (by positivity)
      _ = integerCarry Q P d (N + h) := hrun.symm
      _ ≤ (Q : ℤ) * ((N + h + 2 : ℕ) : ℤ) := hupper
      _ = ((u : ℤ) * ((N + h + 2 : ℕ) : ℤ)) * 2 ^ t := by rw [hQcast]; ring
  exact le_of_mul_le_mul_right hchain (by positivity)

/-- **The forced window**: if `u·(N+h+2) < 2^h` (with `Q = u·2^t`, `N ≥ t`, positive carry),
the digit word must HIT inside `(N, N+h]` — the next support element is within an explicit
`≈ log₂(u·N)` window. -/
theorem exists_one_in_window {Q u t : ℕ} {P : ℤ} {d : ℕ → ℕ} {N h : ℕ}
    (hQfact : Q = u * 2 ^ t) (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (htN : t ≤ N) (hRpos : 0 < integerCarry Q P d N)
    (hwin : (u : ℤ) * ((N + h + 2 : ℕ) : ℤ) < 2 ^ h) :
    ∃ j : ℕ, N < j ∧ j ≤ N + h ∧ d j = 1 := by
  by_contra hno
  push Not at hno
  have hzero : ∀ j : ℕ, N < j → j ≤ N + h → d j = 0 := by
    intro j h1 h2
    rcases hd j with h0 | h1'
    · exact h0
    · exact absurd h1' (hno j h1 h2)
  exact absurd (pow_two_le_oddpart_of_zero_gap hQfact hQ hd heta htN hRpos hzero)
    (not_le.mpr hwin)

/-- **The literal suggested route, executed**: for the exactly-dyadic value `1/2^t` run the
carry with `Q = 2^t`, `P = 1` (so `u = 1`).  On a non-terminating word, every index `N ≥ t`
sees a one in `(N, N+h]` as soon as `N+h+2 < 2^h` — gaps are at most `≈ log₂ N`,
INDEPENDENT of `t`. -/
theorem dyadicValue_next_one {d : ℕ → ℕ} (hd : BinaryDigits d) {t : ℕ}
    (heta : realWeightedValue (natBinaryAsReal d) = 1 / 2 ^ t)
    (hnonterm : ¬ EventuallyZero d) {N h : ℕ} (htN : t ≤ N)
    (hwin : ((N + h + 2 : ℕ) : ℤ) < 2 ^ h) :
    ∃ j : ℕ, N < j ∧ j ≤ N + h ∧ d j = 1 := by
  have hQ : 0 < 2 ^ t := Nat.two_pow_pos t
  have heta' : realWeightedValue (natBinaryAsReal d)
      = ((1 : ℤ) : ℝ) / ((2 ^ t : ℕ) : ℝ) := by
    rw [heta]; push_cast; ring
  have hRpos : 0 < integerCarry (2 ^ t) 1 d N :=
    integerCarry_pos_of_not_eventuallyZero hQ hd heta' hnonterm N
  refine exists_one_in_window (Q := 2 ^ t) (u := 1) (t := t) (P := 1)
    (by rw [one_mul]) hQ hd heta' htN hRpos ?_
  rwa [Int.natCast_one, one_mul]

/-! ## Part 4.  The periodic denominators: digits are invisible mod the odd factor, but the
value forces non-termination -/

/-- **Carry non-vanishing from the odd factor**: if `u ∣ Q`, `u` is odd and `u ∤ P`, then
`R_N ≠ 0` for ALL `N` — modulo `u` the recursion reads `R_{N+1} ≡ 2·R_N` (the digit term
carries the factor `Q ≡ 0`), so `R_N ≡ 2^N·P ≢ 0 (mod u)`.  This is pure arithmetic: no
value or digit hypothesis is used. -/
theorem integerCarry_ne_zero_of_odd_dvd {Q u : ℕ} {P : ℤ} {d : ℕ → ℕ}
    (hu : u ∣ Q) (huodd : Odd u) (hP : ¬ (u : ℤ) ∣ P) (N : ℕ) :
    integerCarry Q P d N ≠ 0 := by
  intro h0
  have h1 : (u : ℤ) ∣ (Q : ℤ) := Int.natCast_dvd_natCast.mpr hu
  have h2 : (u : ℤ) ∣ integerCarry Q P d N - 2 ^ N * P :=
    h1.trans (dvd_integerCarry_sub_pow_mul Q P d N)
  rw [h0, zero_sub, dvd_neg] at h2
  have huoddZ : Odd (u : ℤ) := by
    rcases huodd with ⟨k, hk⟩
    exact ⟨(k : ℤ), by exact_mod_cast hk⟩
  have hcop2 : IsCoprime ((u : ℤ)) (2 : ℤ) :=
    (Int.isCoprime_two_left.mpr huoddZ).symm
  have hcop : IsCoprime ((u : ℤ)) ((2 : ℤ) ^ N) := hcop2.pow_right
  exact hP (hcop.dvd_of_dvd_mul_left h2)

/-- A binary word whose weighted value is `P/Q` with an odd factor `u ∣ Q`, `u ∤ P` can
NEVER terminate (through the dichotomy of Part 2). -/
theorem not_eventuallyZero_of_odd_carry_factor {Q u : ℕ} {P : ℤ} {d : ℕ → ℕ}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hu : u ∣ Q) (huodd : Odd u) (hP : ¬ (u : ℤ) ∣ P) :
    ¬ EventuallyZero d := by
  intro hev
  obtain ⟨N, h0⟩ := integerCarry_eq_zero_of_eventuallyZero hQ hd heta hev
  exact integerCarry_ne_zero_of_odd_dvd hu huodd hP N h0

/-- **The `(15,1)` periodic family value forces an infinite word**: `value = 1/(5·2^t)` has
no terminating binary realization (`R_N ≡ 2^N ≢ 0 (mod 5)`). -/
theorem fifthValue_not_eventuallyZero {d : ℕ → ℕ} (hd : BinaryDigits d) (t : ℕ)
    (heta : realWeightedValue (natBinaryAsReal d) = 1 / (5 * 2 ^ t)) :
    ¬ EventuallyZero d := by
  have heta' : realWeightedValue (natBinaryAsReal d)
      = ((1 : ℤ) : ℝ) / ((5 * 2 ^ t : ℕ) : ℝ) := by
    rw [heta]; push_cast; ring
  exact not_eventuallyZero_of_odd_carry_factor (u := 5)
    (by positivity) hd heta' ⟨2 ^ t, rfl⟩ ⟨2, rfl⟩ (by decide)

/-- **The `(15,2)` periodic family value forces an infinite word**: `value = 2/(3·2^t)` has
no terminating binary realization (`R_N ≡ 2^{N+1} ≢ 0 (mod 3)`). -/
theorem thirdsValue_not_eventuallyZero {d : ℕ → ℕ} (hd : BinaryDigits d) (t : ℕ)
    (heta : realWeightedValue (natBinaryAsReal d) = 2 / (3 * 2 ^ t)) :
    ¬ EventuallyZero d := by
  have heta' : realWeightedValue (natBinaryAsReal d)
      = ((2 : ℤ) : ℝ) / ((3 * 2 ^ t : ℕ) : ℝ) := by
    rw [heta]; push_cast; ring
  exact not_eventuallyZero_of_odd_carry_factor (u := 3)
    (by positivity) hd heta' ⟨2 ^ t, rfl⟩ ⟨1, rfl⟩ (by decide)

/-! ## Part 5.  The support-count lower bound in the dyadic shell -/

/-- **The shell count lower bound**: with `Q = u·2^t`, `t ≤ X` and `u·(2X+2) < 2^g`, every
length-`g` block of `(X, 2X]` contains a support element, so `X/g ≤ |supportShell d X|`. -/
theorem supportShell_card_lower_of_gap {Q u t : ℕ} {P : ℤ} {d : ℕ → ℕ} {X g : ℕ}
    (hQfact : Q = u * 2 ^ t) (hQ : 0 < Q) (hd : BinaryDigits d)
    (hnonterm : ¬ EventuallyZero d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (htX : t ≤ X) (hg : 0 < g)
    (hwin : (u : ℤ) * ((2 * X + 2 : ℕ) : ℤ) < 2 ^ g) :
    X / g ≤ (supportShell d X).card := by
  classical
  have hblock : ∀ N : ℕ, X ≤ N → N + g ≤ 2 * X →
      ∃ j : ℕ, N < j ∧ j ≤ N + g ∧ d j = 1 := by
    intro N hXN h2X
    have htN : t ≤ N := le_trans htX hXN
    have hRpos : 0 < integerCarry Q P d N :=
      integerCarry_pos_of_not_eventuallyZero hQ hd heta hnonterm N
    refine exists_one_in_window hQfact hQ hd heta htN hRpos ?_
    refine lt_of_le_of_lt ?_ hwin
    have hle : N + g + 2 ≤ 2 * X + 2 := by omega
    have hle' : ((N + g + 2 : ℕ) : ℤ) ≤ ((2 * X + 2 : ℕ) : ℤ) := by exact_mod_cast hle
    exact mul_le_mul_of_nonneg_left hle' (Int.natCast_nonneg u)
  have hsurj : Set.SurjOn (fun n : ℕ => (n - X - 1) / g + 1)
      (↑(supportShell d X) : Set ℕ) (↑(Finset.Icc 1 (X / g)) : Set ℕ) := by
    intro i hi
    simp only [Finset.coe_Icc, Set.mem_Icc] at hi
    obtain ⟨hi1, hik⟩ := hi
    have higX : i * g ≤ X :=
      le_trans (mul_le_mul_left hik g) (Nat.div_mul_le_self X g)
    have hims : (i - 1) * g + g = i * g := by
      have hi' : i - 1 + 1 = i := by omega
      calc (i - 1) * g + g = ((i - 1) + 1) * g := by ring
        _ = i * g := by rw [hi']
    obtain ⟨j, hj1, hj2, hj3⟩ := hblock (X + (i - 1) * g)
      (Nat.le_add_right X _) (by omega)
    refine ⟨j, ?_, ?_⟩
    · rw [Finset.mem_coe, supportShell, Finset.mem_sdiff, mem_supportIn, mem_supportIn]
      constructor
      · exact ⟨by omega, by omega, hj3⟩
      · rintro ⟨-, hjX, -⟩
        omega
    · have hlow : (i - 1) * g ≤ j - X - 1 := by omega
      have hsucc : (i - 1 + 1) * g = (i - 1) * g + g := by ring
      have hhigh : j - X - 1 < (i - 1 + 1) * g := by
        rw [hsucc]; omega
      have hdiv : (j - X - 1) / g = i - 1 := Nat.div_eq_of_lt_le hlow hhigh
      show (j - X - 1) / g + 1 = i
      rw [hdiv]
      omega
  have hcard := Finset.card_le_card_of_surjOn
    (fun n : ℕ => (n - X - 1) / g + 1) hsurj
  rw [Nat.card_Icc] at hcard
  omega

/-- **The collision with the sparsity bound**: count lower bound `X/g` versus the failure
bound `|supportShell d X| < c0·X` is absurd as soon as `2g ≤ X` and `c0·(2g) ≤ 1`. -/
theorem supportShell_sparse_contradiction {Q u t : ℕ} {P : ℤ} {d : ℕ → ℕ} {X g : ℕ}
    {c0 : ℝ}
    (hQfact : Q = u * 2 ^ t) (hQ : 0 < Q) (hd : BinaryDigits d)
    (hnonterm : ¬ EventuallyZero d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (htX : t ≤ X) (hg : 0 < g)
    (hwin : (u : ℤ) * ((2 * X + 2 : ℕ) : ℤ) < 2 ^ g)
    (hX2g : 2 * g ≤ X)
    (hc0g : c0 * ((2 * g : ℕ) : ℝ) ≤ 1)
    (hfailure : ((supportShell d X).card : ℝ) < c0 * (X : ℝ)) : False := by
  have hlower := supportShell_card_lower_of_gap hQfact hQ hd hnonterm heta htX hg hwin
  have hD2 : 2 ≤ X / g := (Nat.le_div_iff_mul_le hg).mpr (by omega)
  have hXnn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hfail2 : ((X / g : ℕ) : ℝ) < c0 * (X : ℝ) :=
    lt_of_le_of_lt (by exact_mod_cast hlower) hfailure
  have hc0' : c0 * (2 * (g : ℝ)) ≤ 1 := by push_cast at hc0g; linarith
  have hmod := Nat.div_add_mod X g
  have hrlt : X % g < g := Nat.mod_lt X hg
  have hXeq : (X : ℝ) = (g : ℝ) * ((X / g : ℕ) : ℝ) + ((X % g : ℕ) : ℝ) := by
    exact_mod_cast hmod.symm
  have hrR : ((X % g : ℕ) : ℝ) + 1 ≤ (g : ℝ) := by exact_mod_cast hrlt
  have hD2R : (2 : ℝ) ≤ ((X / g : ℕ) : ℝ) := by exact_mod_cast hD2
  have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have h1 : 2 * (g : ℝ) * ((X / g : ℕ) : ℝ) < 2 * (g : ℝ) * (c0 * (X : ℝ)) :=
    mul_lt_mul_of_pos_left hfail2 (by positivity)
  have h2 : c0 * (2 * (g : ℝ)) * (X : ℝ) ≤ 1 * (X : ℝ) :=
    mul_le_mul_of_nonneg_right hc0' hXnn
  have h3 : 2 * (g : ℝ) * ((X / g : ℕ) : ℝ) < (X : ℝ) := by linarith
  have h5 : (g : ℝ) * 2 ≤ (g : ℝ) * ((X / g : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hD2R hgpos.le
  linarith

/-! ## Part 6.  Scale-bounded voiding of failing contexts (the exact thresholds) -/

/-- The shell projection preserves the digit word (rfl; recorded for rewriting). -/
theorem carryWord_shell_d_eq (ctx : ActualFailureContext) : ctx.shell.d = ctx.d := rfl

/-- The pinned failure constant, numerically: `c0 = κ/64 = 17/16777216`. -/
theorem carryWord_c0_eq : erdos260Constants.c0 = 17 / 16777216 := by
  show manuscriptC0 = 17 / 16777216
  unfold manuscriptC0 manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps
  norm_num

/-- Every failing context has dyadic exponent `L ≥ 28` (from the scale bound `2^27·Q < X`). -/
theorem carryWord_L_ge_28 (ctx : ActualFailureContext) {L : ℕ}
    (hL : ctx.X = 2 ^ L) : 28 ≤ L := by
  have hscale : 2 ^ 27 * ctx.Q < ctx.X := by
    simpa using shell_Q_scale_bound ctx
  have hQ1 : 1 ≤ ctx.Q := ctx.hQ
  by_contra hcon
  push Not at hcon
  have hX27 : ctx.X ≤ 2 ^ 27 := by
    rw [hL]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h27Q : 2 ^ 27 ≤ 2 ^ 27 * ctx.Q := by
    calc (2 : ℕ) ^ 27 = 2 ^ 27 * 1 := by ring
      _ ≤ 2 ^ 27 * ctx.Q := mul_le_mul_right hQ1 _
  omega

/-- Every failing context has `t < X` for `t = ν₂` of any divisor pattern: concretely
`Q < X` (scale bound), recorded once. -/
theorem carryWord_Q_lt_X (ctx : ActualFailureContext) : ctx.Q < ctx.X := by
  have hscale : 2 ^ 27 * ctx.Q < ctx.X := by
    simpa using shell_Q_scale_bound ctx
  have hQle : ctx.Q ≤ 2 ^ 27 * ctx.Q := Nat.le_mul_of_pos_left _ (by norm_num)
  omega

/-- **THE UNCONDITIONAL SCALE FLOOR**: no failing context exists at scale `X ≤ 2^246736`.
The carry rigidity forces `≥ X/(2L−25)` support elements in `(X, 2X]` (using only
`Q < 2^(L−27)`), and `17·(4L−50) ≤ 16777216` exactly when `L ≤ 246736`. -/
theorem actualFailureContext_void_of_scale (ctx : ActualFailureContext)
    (hXle : ctx.X ≤ 2 ^ 246736) : False := by
  obtain ⟨L, hL⟩ := ctx.hXdyadic
  have hL28 : 28 ≤ L := carryWord_L_ge_28 ctx hL
  have hLle : L ≤ 246736 := by
    have h2 : (2 : ℕ) ^ L ≤ 2 ^ 246736 := by rw [← hL]; exact hXle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  have hscale : 2 ^ 27 * ctx.Q < ctx.X := by
    simpa using shell_Q_scale_bound ctx
  have hQlt : ctx.Q < 2 ^ (L - 27) := by
    have hsplit : (2 : ℕ) ^ L = 2 ^ 27 * 2 ^ (L - 27) := by
      rw [← pow_add]
      congr 1
      omega
    have h := hscale
    rw [hL, hsplit] at h
    exact Nat.lt_of_mul_lt_mul_left h
  have hp2 : (2 : ℕ) ^ (L + 2) = 4 * 2 ^ L := by rw [pow_add]; ring
  have h1pow : 1 ≤ (2 : ℕ) ^ L := Nat.one_le_two_pow
  have hstep1 : 2 * ctx.X + 2 ≤ 2 ^ (L + 2) := by rw [hL]; omega
  have hwinN : ctx.Q * (2 * ctx.X + 2) < 2 ^ (2 * L - 25) := by
    calc ctx.Q * (2 * ctx.X + 2) ≤ ctx.Q * 2 ^ (L + 2) :=
          mul_le_mul_right hstep1 ctx.Q
      _ < 2 ^ (L - 27) * 2 ^ (L + 2) :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos (L + 2))).mpr hQlt
      _ = 2 ^ (2 * L - 25) := by
          rw [← pow_add]
          congr 1
          omega
  have hsq : L * L < 2 ^ L := carryWord_sq_lt_two_pow (by omega)
  have h4L : 4 * L ≤ L * L := mul_le_mul_left (by omega : 4 ≤ L) L
  have hX2g : 2 * (2 * L - 25) ≤ ctx.X := by rw [hL]; omega
  have hgpos : 0 < 2 * L - 25 := by omega
  obtain ⟨P, hP⟩ := ctx.hrational
  refine supportShell_sparse_contradiction (Q := ctx.Q) (u := ctx.Q) (t := 0)
    (P := P) (d := ctx.d) (X := ctx.X) (g := 2 * L - 25)
    (c0 := erdos260Constants.c0)
    (by simp) ctx.hQ ctx.hd ctx.hnonterm hP (Nat.zero_le _) hgpos
    (by exact_mod_cast hwinN) hX2g ?_ ctx.hfailure
  have hgle : 2 * (2 * L - 25) ≤ 986894 := by omega
  rw [carryWord_c0_eq]
  have hcast : ((2 * (2 * L - 25) : ℕ) : ℝ) ≤ 986894 := by exact_mod_cast hgle
  linarith

/-- The scale floor as a lower bound: EVERY failing context has `X > 2^246736`
(unconditional). -/
theorem actualFailureContext_scale_lower (ctx : ActualFailureContext) :
    2 ^ 246736 < ctx.X := by
  by_contra hcon
  push Not at hcon
  exact actualFailureContext_void_of_scale ctx hcon

/-- **The pinned-value workhorse**: a value representation `P/(u·2^t)` with SMALL odd part
`u ≤ 7` improves the gap to `g = L+4` (the `2^t` cancels), and `17·(2L+8) ≤ 16777216`
exactly when `L ≤ 493443`: no such context exists at scale `X ≤ 2^493443`. -/
theorem actualFailureContext_void_of_rep (ctx : ActualFailureContext)
    {u t : ℕ} {P : ℤ}
    (hu7 : u ≤ 7) (hupos : 0 < u)
    (heta : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ))
    (htX : t ≤ ctx.X)
    (hXle : ctx.X ≤ 2 ^ 493443) : False := by
  obtain ⟨L, hL⟩ := ctx.hXdyadic
  have hL28 : 28 ≤ L := carryWord_L_ge_28 ctx hL
  have hLle : L ≤ 493443 := by
    have h2 : (2 : ℕ) ^ L ≤ 2 ^ 493443 := by rw [← hL]; exact hXle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  have hp4 : (2 : ℕ) ^ (L + 4) = 16 * 2 ^ L := by rw [pow_add]; norm_num [mul_comm]
  have h32 : 32 ≤ (2 : ℕ) ^ L := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hwinN : u * (2 * ctx.X + 2) < 2 ^ (L + 4) := by
    calc u * (2 * ctx.X + 2) ≤ 7 * (2 * ctx.X + 2) :=
          mul_le_mul_left hu7 _
      _ < 2 ^ (L + 4) := by rw [hL]; omega
  have hsq : L * L < 2 ^ L := carryWord_sq_lt_two_pow (by omega)
  have h3L : 3 * L ≤ L * L := mul_le_mul_left (by omega : 3 ≤ L) L
  have hX2g : 2 * (L + 4) ≤ ctx.X := by rw [hL]; omega
  refine supportShell_sparse_contradiction (Q := u * 2 ^ t) (u := u) (t := t)
    (P := P) (d := ctx.d) (X := ctx.X) (g := L + 4)
    (c0 := erdos260Constants.c0)
    rfl (by positivity) ctx.hd ctx.hnonterm heta htX (by omega)
    (by exact_mod_cast hwinN) hX2g ?_ ctx.hfailure
  have hgle : 2 * (L + 4) ≤ 986894 := by omega
  rw [carryWord_c0_eq]
  have hcast : ((2 * (L + 4) : ℕ) : ℝ) ≤ 986894 := by exact_mod_cast hgle
  linarith

/-- **The dyadic-value voiding regime**: no failing context with `value = 1/2^t` exists at
scale `X ≤ 2^493443` (run the carry at `Q = 2^t`, `P = 1`, `u = 1`). -/
theorem shellValueDyadic_void_of_scale (ctx : ActualFailureContext)
    (hXle : ctx.X ≤ 2 ^ 493443) : ¬ ShellValueDyadic ctx := by
  rintro ⟨t, hdy⟩
  have hvK := shell_value_eq_K₀_div_Q ctx
  have heq : (1 : ℝ) / 2 ^ t = ((class1SlopeDatum ctx).K₀ : ℝ) / (ctx.Q : ℝ) := by
    have h := hdy.symm.trans hvK
    simpa using h
  have hK1 : (1 : ℝ) ≤ ((class1SlopeDatum ctx).K₀ : ℝ) := by
    exact_mod_cast (class1SlopeDatum ctx).hK₀_pos
  have hQpos : (0 : ℝ) < (ctx.Q : ℝ) := by exact_mod_cast ctx.hQ
  have h2t : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
  rw [div_eq_div_iff (by positivity) hQpos.ne'] at heq
  have hmul : (1 : ℝ) * 2 ^ t ≤ ((class1SlopeDatum ctx).K₀ : ℝ) * 2 ^ t :=
    mul_le_mul_of_nonneg_right hK1 h2t.le
  have hQge : (2 : ℝ) ^ t ≤ (ctx.Q : ℝ) := by linarith
  have hQgeN : 2 ^ t ≤ ctx.Q := by exact_mod_cast hQge
  have htX : t ≤ ctx.X := by
    have hlt : t < 2 ^ t := Nat.lt_two_pow_self
    have hQX : ctx.Q < ctx.X := carryWord_Q_lt_X ctx
    omega
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = ((1 : ℤ) : ℝ) / ((1 * 2 ^ t : ℕ) : ℝ) := by
    rw [show realWeightedValue (natBinaryAsReal ctx.d) = 1 / 2 ^ t from hdy]
    push_cast
    ring
  exact actualFailureContext_void_of_rep ctx (by norm_num) (by norm_num) heta' htX hXle

/-- The dyadic-value scale floor: any context with exactly-dyadic value has `X > 2^493443`. -/
theorem shellValueDyadic_scale_lower (ctx : ActualFailureContext)
    (h : ShellValueDyadic ctx) : 2 ^ 493443 < ctx.X := by
  by_contra hcon
  push Not at hcon
  exact shellValueDyadic_void_of_scale ctx hcon h

/-- **The fifth-value voiding regime**: no failing context with `value = 1/(5·2^t)` exists at
scale `X ≤ 2^493443` (carry at `Q = 5·2^t`, `P = 1`, `u = 5`). -/
theorem towerFifthValue_void_of_scale (ctx : ActualFailureContext)
    (hXle : ctx.X ≤ 2 ^ 493443) (t : ℕ) :
    realWeightedValue (natBinaryAsReal ctx.shell.d) ≠ 1 / (5 * 2 ^ t) := by
  intro hval
  have hvK := shell_value_eq_K₀_div_Q ctx
  have heq : (1 : ℝ) / (5 * 2 ^ t)
      = ((class1SlopeDatum ctx).K₀ : ℝ) / (ctx.Q : ℝ) := by
    have h := hval.symm.trans hvK
    simpa using h
  have hK1 : (1 : ℝ) ≤ ((class1SlopeDatum ctx).K₀ : ℝ) := by
    exact_mod_cast (class1SlopeDatum ctx).hK₀_pos
  have hQpos : (0 : ℝ) < (ctx.Q : ℝ) := by exact_mod_cast ctx.hQ
  have h2t : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
  rw [div_eq_div_iff (by positivity) hQpos.ne'] at heq
  have hmul : (1 : ℝ) * (5 * 2 ^ t)
      ≤ ((class1SlopeDatum ctx).K₀ : ℝ) * (5 * 2 ^ t) :=
    mul_le_mul_of_nonneg_right hK1 (by positivity)
  have hQge : (2 : ℝ) ^ t ≤ (ctx.Q : ℝ) := by linarith
  have hQgeN : 2 ^ t ≤ ctx.Q := by exact_mod_cast hQge
  have htX : t ≤ ctx.X := by
    have hlt : t < 2 ^ t := Nat.lt_two_pow_self
    have hQX : ctx.Q < ctx.X := carryWord_Q_lt_X ctx
    omega
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = ((1 : ℤ) : ℝ) / ((5 * 2 ^ t : ℕ) : ℝ) := by
    rw [show realWeightedValue (natBinaryAsReal ctx.d) = 1 / (5 * 2 ^ t) from hval]
    push_cast
    ring
  exact actualFailureContext_void_of_rep ctx (by norm_num) (by norm_num) heta' htX hXle

/-- **The thirds-value voiding regime**: no failing context with `value = 2/(3·2^t)` exists
at scale `X ≤ 2^493443` (carry at `Q = 3·2^t`, `P = 2`, `u = 3`). -/
theorem towerThirdsValue_void_of_scale (ctx : ActualFailureContext)
    (hXle : ctx.X ≤ 2 ^ 493443) (t : ℕ) :
    realWeightedValue (natBinaryAsReal ctx.shell.d) ≠ 2 / (3 * 2 ^ t) := by
  intro hval
  have hvK := shell_value_eq_K₀_div_Q ctx
  have heq : (2 : ℝ) / (3 * 2 ^ t)
      = ((class1SlopeDatum ctx).K₀ : ℝ) / (ctx.Q : ℝ) := by
    have h := hval.symm.trans hvK
    simpa using h
  have hK1 : (1 : ℝ) ≤ ((class1SlopeDatum ctx).K₀ : ℝ) := by
    exact_mod_cast (class1SlopeDatum ctx).hK₀_pos
  have hQpos : (0 : ℝ) < (ctx.Q : ℝ) := by exact_mod_cast ctx.hQ
  have h2t : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
  rw [div_eq_div_iff (by positivity) hQpos.ne'] at heq
  have hmul : (1 : ℝ) * (3 * 2 ^ t)
      ≤ ((class1SlopeDatum ctx).K₀ : ℝ) * (3 * 2 ^ t) :=
    mul_le_mul_of_nonneg_right hK1 (by positivity)
  have hQge : (2 : ℝ) ^ t ≤ (ctx.Q : ℝ) := by linarith
  have hQgeN : 2 ^ t ≤ ctx.Q := by exact_mod_cast hQge
  have htX : t ≤ ctx.X := by
    have hlt : t < 2 ^ t := Nat.lt_two_pow_self
    have hQX : ctx.Q < ctx.X := carryWord_Q_lt_X ctx
    omega
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = ((2 : ℤ) : ℝ) / ((3 * 2 ^ t : ℕ) : ℝ) := by
    rw [show realWeightedValue (natBinaryAsReal ctx.d) = 2 / (3 * 2 ^ t) from hval]
    push_cast
    ring
  exact actualFailureContext_void_of_rep ctx (by norm_num) (by norm_num) heta' htX hXle

/-- **All five fixed families are void at scale `X ≤ 2^493443`**: any fixed-family hit pins
`oddpart(Q) ∈ {1,3,5,7}`, so the t-free window applies with `u ≤ 7`. -/
theorem fixedFamilyHit_void_of_scale (ctx : ActualFailureContext)
    (hXle : ctx.X ≤ 2 ^ 493443) : ¬ FixedFamilyHit ctx := by
  intro hhit
  have hmem := fixedFamilyHit_oddpartQ_mem ctx hhit
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hu7 : ordCompl[2] ctx.Q ≤ 7 := by
    have hmem' : ordCompl[2] ctx.Q = 1 ∨ ordCompl[2] ctx.Q = 3
        ∨ ordCompl[2] ctx.Q = 5 ∨ ordCompl[2] ctx.Q = 7 := by simpa using hmem
    omega
  have hupos : 0 < ordCompl[2] ctx.Q := Nat.ordCompl_pos 2 ctx.hQ.ne'
  have hQfact : ctx.Q = ordCompl[2] ctx.Q * 2 ^ ctx.Q.factorization 2 := by
    have h := shell_Q_eq_oddpart_mul_pow ctx
    simpa using h
  obtain ⟨P, hP⟩ := ctx.hrational
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((ordCompl[2] ctx.Q * 2 ^ ctx.Q.factorization 2 : ℕ) : ℝ) := by
    rw [← hQfact]
    exact hP
  have htX : ctx.Q.factorization 2 ≤ ctx.X := by
    have h2t : 2 ^ ctx.Q.factorization 2 ≤ ctx.Q := Nat.ordProj_le 2 ctx.hQ.ne'
    have hlt : ctx.Q.factorization 2 < 2 ^ ctx.Q.factorization 2 := Nat.lt_two_pow_self
    have hQX : ctx.Q < ctx.X := carryWord_Q_lt_X ctx
    omega
  exact actualFailureContext_void_of_rep ctx hu7 hupos heta' htX hXle

/-- The fixed-family scale floor: any of the five surviving fixed families needs
`X > 2^493443`. -/
theorem fixedFamilyHit_scale_lower (ctx : ActualFailureContext)
    (h : FixedFamilyHit ctx) : 2 ^ 493443 < ctx.X := by
  by_contra hcon
  push Not at hcon
  exact fixedFamilyHit_void_of_scale ctx hcon h

/-- Band-2 `(3,1)` scale floor. -/
theorem returnFixedFamily_scale_lower (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 3) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    2 ^ 493443 < ctx.X :=
  fixedFamilyHit_scale_lower ctx (Or.inl ⟨hq, hK⟩)

/-- Band-3 `(21,3)` scale floor. -/
theorem densePackFixedFamily_scale_lower (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    2 ^ 493443 < ctx.X :=
  fixedFamilyHit_scale_lower ctx (Or.inr (Or.inl ⟨hq, hK⟩))

/-- Band-4 `(15,1)` scale floor (periodic family). -/
theorem towerFP15_1_scale_lower (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    2 ^ 493443 < ctx.X :=
  fixedFamilyHit_scale_lower ctx (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩)))

/-- Band-4 `(15,2)` scale floor (periodic family). -/
theorem towerFP15_2_scale_lower (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    2 ^ 493443 < ctx.X :=
  fixedFamilyHit_scale_lower ctx (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩))))

/-- Band-4 `(105,7)` scale floor. -/
theorem towerFP105_7_scale_lower (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 7) :
    2 ^ 493443 < ctx.X :=
  fixedFamilyHit_scale_lower ctx (Or.inr (Or.inr (Or.inr (Or.inr ⟨hq, hK⟩))))

/-! ## Part 7.  The deep residual levers and the additive wiring -/

/-- **The deep dyadic-value lever** — the residual successor of `DyadicValueLever`:
the dyadic-value exclusion is demanded ONLY at scales `X > 2^493443` (the shallow regime is
closed unconditionally by `shellValueDyadic_void_of_scale`). -/
def DeepDyadicValueLever : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X → ¬ ShellValueDyadic ctx

/-- The deep lever discharges the full lever (shallow scales are closed by the carry
rigidity). -/
theorem dyadicValueLever_of_deepScale (h : DeepDyadicValueLever) : DyadicValueLever := by
  intro ctx hdy
  by_cases hX : 2 ^ 493443 < ctx.X
  · exact h ctx hX hdy
  · exact shellValueDyadic_void_of_scale ctx (not_lt.mp hX) hdy

/-- The deep fifth-value lever — successor of `TowerFifthValueLever`. -/
def DeepTowerFifthValueLever : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
    ∀ t : ℕ, realWeightedValue (natBinaryAsReal ctx.shell.d) ≠ 1 / (5 * 2 ^ t)

/-- The deep fifth lever discharges the full fifth lever. -/
theorem towerFifthValueLever_of_deepScale (h : DeepTowerFifthValueLever) :
    TowerFifthValueLever := by
  intro ctx t hval
  by_cases hX : 2 ^ 493443 < ctx.X
  · exact h ctx hX t hval
  · exact towerFifthValue_void_of_scale ctx (not_lt.mp hX) t hval

/-- The deep thirds-value lever — successor of `TowerThirdsValueLever`. -/
def DeepTowerThirdsValueLever : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
    ∀ t : ℕ, realWeightedValue (natBinaryAsReal ctx.shell.d) ≠ 2 / (3 * 2 ^ t)

/-- The deep thirds lever discharges the full thirds lever. -/
theorem towerThirdsValueLever_of_deepScale (h : DeepTowerThirdsValueLever) :
    TowerThirdsValueLever := by
  intro ctx t hval
  by_cases hX : 2 ^ 493443 < ctx.X
  · exact h ctx hX t hval
  · exact towerThirdsValue_void_of_scale ctx (not_lt.mp hX) t hval

/-- **The deep family voiding** — ONE successor Prop for all five fixed families (including
the two periodic pairs): the hit exclusion is demanded only at `X > 2^493443`. -/
def DeepFixedFamilyVoid : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X → ¬ FixedFamilyHit ctx

/-- The deep family voiding discharges the FULL family voiding on every context. -/
theorem fixedFamilyHit_void_of_deepScale (h : DeepFixedFamilyVoid)
    (ctx : ActualFailureContext) : ¬ FixedFamilyHit ctx := by
  by_cases hX : 2 ^ 493443 < ctx.X
  · exact h ctx hX
  · exact fixedFamilyHit_void_of_scale ctx (not_lt.mp hX)

/-- Band-2 `(3,1)` void from the deep family Prop. -/
theorem returnFixedFamily_void_of_deepFamilies (h : DeepFixedFamilyVoid)
    (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) :=
  fun hh => fixedFamilyHit_void_of_deepScale h ctx (Or.inl hh)

/-- Band-3 `(21,3)` void from the deep family Prop. -/
theorem densePackFixedFamily_void_of_deepFamilies (h : DeepFixedFamilyVoid)
    (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) :=
  fun hh => fixedFamilyHit_void_of_deepScale h ctx (Or.inr (Or.inl hh))

/-- Band-4 `(15,1)` void from the deep family Prop. -/
theorem towerFP15_1Family_void_of_deepFamilies (h : DeepFixedFamilyVoid)
    (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 1) :=
  fun hh => fixedFamilyHit_void_of_deepScale h ctx (Or.inr (Or.inr (Or.inl hh)))

/-- Band-4 `(15,2)` void from the deep family Prop. -/
theorem towerFP15_2Family_void_of_deepFamilies (h : DeepFixedFamilyVoid)
    (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 2) :=
  fun hh => fixedFamilyHit_void_of_deepScale h ctx (Or.inr (Or.inr (Or.inr (Or.inl hh))))

/-- Band-4 `(105,7)` void from the deep family Prop. -/
theorem towerFP105Family_void_of_deepFamilies (h : DeepFixedFamilyVoid)
    (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 7) :=
  fun hh =>
    fixedFamilyHit_void_of_deepScale h ctx (Or.inr (Or.inr (Or.inr (Or.inr hh))))

/-- The tower escape shrinks under the DEEP lever (through the discharge). -/
theorem towerEscapeLever_of_towerEscape_deep (h : DeepDyadicValueLever)
    (ctx : ActualFailureContext) (hesc : TowerEscape ctx) : TowerEscapeLever ctx :=
  towerEscapeLever_of_towerEscape (dyadicValueLever_of_deepScale h) ctx hesc

/-- The tower escape also shrinks under the deep FAMILY voiding (the dropped `(105, 7)`
branch is a fixed-family hit). -/
theorem towerEscapeLever_of_towerEscape_deepFamilies (h : DeepFixedFamilyVoid)
    (ctx : ActualFailureContext) (hesc : TowerEscape ctx) : TowerEscapeLever ctx := by
  rcases hesc with h1 | h2 | h3 | h4 | ⟨hq, hK7 | hm⟩ | h6
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact absurd ⟨hq, hK7⟩ (towerFP105Family_void_of_deepFamilies h ctx)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hm⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6))))

/-- The tower field bridge under the deep lever: the lever residual rebuilds the full wave-4
`TowerFixedPointResidual`. -/
theorem towerFixedPointResidual_of_deepLever (h : DeepDyadicValueLever)
    (hres : TowerLeverResidual) : TowerFixedPointResidual :=
  towerFixedPointResidual_of_lever (dyadicValueLever_of_deepScale h) hres

/-- The tower field bridge under the deep family voiding. -/
theorem towerFixedPointResidual_of_deepFamilies (h : DeepFixedFamilyVoid)
    (hres : TowerLeverResidual) : TowerFixedPointResidual :=
  fun ctx hdeep hesc =>
    hres ctx hdeep (towerEscapeLever_of_towerEscape_deepFamilies h ctx hesc)

/-- **The deep-lever conditional endpoint residual**: the deep dyadic-value lever (demanded
only at `X > 2^493443`) plus the lever-shrunk wave-5 surfaces, the latter packaged as a
function of the discharged lever (the consumer may use the full lever to meet its
obligations — strictly more permissive than a verbatim field copy). -/
structure Erdos260DeepLeverResidual where
  /-- The deep dyadic-value lever (the only lever content not closed by this module). -/
  deepLever : DeepDyadicValueLever
  /-- The remaining wave-5 surfaces, given the discharged lever. -/
  surfaces : DyadicValueLever → Erdos260DyadicLeverResidual

namespace Erdos260DeepLeverResidual

/-- Discharge the deep lever into the wave-5 lever residual. -/
def toLeverResidual (R : Erdos260DeepLeverResidual) : Erdos260DyadicLeverResidual :=
  R.surfaces (dyadicValueLever_of_deepScale R.deepLever)

/-- The final statement from the deep-lever residual, through the wave-5/wave-4 capstones. -/
theorem toStatement (R : Erdos260DeepLeverResidual) : Erdos260Statement :=
  R.toLeverResidual.toStatement

end Erdos260DeepLeverResidual

/-- **The deep conditional endpoint**: `Erdos260Statement` from the deep dyadic-value lever
plus the lever-shrunk surfaces — the shallow half of the lever is supplied unconditionally by
the carry-word rigidity of this module. -/
theorem erdos260_of_deepDyadicValueLever (R : Erdos260DeepLeverResidual) :
    Erdos260Statement :=
  R.toStatement

/-! ## Part 8.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the carry-word rigidity module. -/
def carryWordRigidityStatus : List String :=
  [ "THE CARRY CONGRUENCE (unconditional): Q | R_N - 2^N*P (dvd_integerCarry_sub_pow_mul); " ++
      "writing Q = u*2^t, for N >= t the carry is divisible by 2^t " ++
      "(two_pow_dvd_integerCarry), so a positive carry is >= 2^t " ++
      "(two_pow_le_integerCarry_of_pos).",
    "THE TERMINATION DICHOTOMY (unconditional): R_N = 0 somewhere IFF the expansion " ++
      "terminates (integerCarry_exists_zero_iff_eventuallyZero; forward " ++
      "eventuallyZero_of_integerCarry_eq_zero forces all later digits to 0, backward " ++
      "integerCarry_eq_zero_of_eventuallyZero beats the doubling against the linear " ++
      "envelope); hence on a non-terminating word the carry is positive at EVERY index " ++
      "(integerCarry_pos_of_not_eventuallyZero).",
    "THE T-FREE RIGIDITY WINDOW (unconditional): with Q = u*2^t, N >= t, positive carry, " ++
      "an all-zero gap of length h forces 2^h <= u*(N+h+2) " ++
      "(pow_two_le_oddpart_of_zero_gap) - the 2^t part of the denominator CANCELS; " ++
      "contrapositive exists_one_in_window forces the next support element within an " ++
      "explicit ~log2(u*N) window; dyadicValue_next_one is the literal suggested route " ++
      "(value 1/2^t, Q = 2^t, P = 1, gaps <= ~log2 N independent of t).",
    "THE PERIODIC DENOMINATORS, HONEST FINDING: in the WEIGHTED recursion the digit term " ++
      "carries the factor Q, so mod the odd factor u | Q the digits are INVISIBLE " ++
      "(R_{N+1} = 2*R_N mod u): the hoped-for periodic digit hits with density 1/4 " ++
      "(ord_2(5)) resp. 1/2 (ord_2(3)) DO NOT EXIST for this recursion.  What survives: " ++
      "R_N = 2^N*P != 0 mod u (integerCarry_ne_zero_of_odd_dvd), so the values 1/(5*2^t) " ++
      "and 2/(3*2^t) have NO terminating binary realization " ++
      "(fifthValue_not_eventuallyZero, thirdsValue_not_eventuallyZero) - unlike the " ++
      "dyadic 1/2^t, which has terminating realizations.  The shells already carry " ++
      "hnonterm, so this voids nothing extra; quantitatively both periodic families " ++
      "reduce to the same u in {3,5} window bound.",
    "THE SHELL COUNT LOWER BOUND (unconditional): u*(2X+2) < 2^g and t <= X force a " ++
      "support element in every length-g block of (X, 2X], so X/g <= |supportShell d X| " ++
      "(supportShell_card_lower_of_gap); against the sparsity |supportShell| < c0*X this " ++
      "is absurd once 2g <= X and c0*(2g) <= 1 (supportShell_sparse_contradiction).",
    "THE UNCONDITIONAL SCALE FLOOR (the headline): every ActualFailureContext has " ++
      "X > 2^246736 (actualFailureContext_scale_lower; void form " ++
      "actualFailureContext_void_of_scale).  At c0 = kappa/64 = 17/16777216 " ++
      "(carryWord_c0_eq) and Q < 2^(L-27) the gap g = 2L-25 fires iff 17*(4L-50) <= " ++
      "16777216, i.e. L <= 246736 (margin 17*986894 = 16777198 <= 16777216).",
    "THE PINNED-VALUE REGIME (unconditional, deeper): any value pin P/(u*2^t) with u <= 7 " ++
      "allows the t-free gap g = L+4, firing iff L <= 493443: dyadic-value ctx " ++
      "(shellValueDyadic_void_of_scale / _scale_lower), fifth-value " ++
      "(towerFifthValue_void_of_scale), thirds-value (towerThirdsValue_void_of_scale), " ++
      "and ALL FIVE fixed families (fixedFamilyHit_void_of_scale / _scale_lower; " ++
      "per-family floors returnFixedFamily_scale_lower, densePackFixedFamily_scale_lower, " ++
      "towerFP15_1/15_2/105_7_scale_lower) are void at X <= 2^493443.",
    "WHAT RESISTS AND WHY (honest): for L > 493443 the rigidity density ~1/(L+4) is " ++
      "BELOW c0 = 17/16777216 and the sparsity bound is CONSISTENT with the carry " ++
      "rigidity; the global failure structure only produces failing shells at " ++
      "arbitrarily LARGE X (X >= any threshold via hlarge), never at a chosen small " ++
      "scale, so the density comparison cannot close the deep tail.  The full levers " ++
      "remain open; NO context with X > 2^493443 is claimed empty.",
    "THE DEEP RESIDUAL SUCCESSORS (the tail, exactly): DeepDyadicValueLever / " ++
      "DeepTowerFifthValueLever / DeepTowerThirdsValueLever / DeepFixedFamilyVoid demand " ++
      "the exclusions ONLY at X > 2^493443 and discharge the full levers " ++
      "(dyadicValueLever_of_deepScale, towerFifthValueLever_of_deepScale, " ++
      "towerThirdsValueLever_of_deepScale, fixedFamilyHit_void_of_deepScale + the five " ++
      "per-family voids *_void_of_deepFamilies).",
    "WIRING (additive): tower escape shrinks under either deep Prop " ++
      "(towerEscapeLever_of_towerEscape_deep, towerEscapeLever_of_towerEscape_deepFamilies; " ++
      "bridges towerFixedPointResidual_of_deepLever, " ++
      "towerFixedPointResidual_of_deepFamilies); endpoint " ++
      "erdos260_of_deepDyadicValueLever : Erdos260DeepLeverResidual -> Erdos260Statement " ++
      "through the wave-5 lever residual.  Nothing re-proved, no existing file edited." ]

theorem carryWordRigidityStatus_nonempty : carryWordRigidityStatus ≠ [] := by
  simp [carryWordRigidityStatus]

/-! ## Part 9.  Axiom-cleanliness audit -/

#print axioms carryWord_sq_lt_two_pow
#print axioms carryWord_exists_mul_add_lt_two_pow
#print axioms dvd_integerCarry_sub_pow_mul
#print axioms two_pow_dvd_integerCarry
#print axioms two_pow_le_integerCarry_of_pos
#print axioms eventuallyZero_of_integerCarry_eq_zero
#print axioms integerCarry_eq_zero_of_eventuallyZero
#print axioms integerCarry_exists_zero_iff_eventuallyZero
#print axioms integerCarry_pos_of_not_eventuallyZero
#print axioms pow_two_le_oddpart_of_zero_gap
#print axioms exists_one_in_window
#print axioms dyadicValue_next_one
#print axioms integerCarry_ne_zero_of_odd_dvd
#print axioms not_eventuallyZero_of_odd_carry_factor
#print axioms fifthValue_not_eventuallyZero
#print axioms thirdsValue_not_eventuallyZero
#print axioms supportShell_card_lower_of_gap
#print axioms supportShell_sparse_contradiction
#print axioms carryWord_c0_eq
#print axioms carryWord_L_ge_28
#print axioms carryWord_Q_lt_X
#print axioms actualFailureContext_void_of_scale
#print axioms actualFailureContext_scale_lower
#print axioms actualFailureContext_void_of_rep
#print axioms shellValueDyadic_void_of_scale
#print axioms shellValueDyadic_scale_lower
#print axioms towerFifthValue_void_of_scale
#print axioms towerThirdsValue_void_of_scale
#print axioms fixedFamilyHit_void_of_scale
#print axioms fixedFamilyHit_scale_lower
#print axioms returnFixedFamily_scale_lower
#print axioms densePackFixedFamily_scale_lower
#print axioms towerFP15_1_scale_lower
#print axioms towerFP15_2_scale_lower
#print axioms towerFP105_7_scale_lower
#print axioms dyadicValueLever_of_deepScale
#print axioms towerFifthValueLever_of_deepScale
#print axioms towerThirdsValueLever_of_deepScale
#print axioms fixedFamilyHit_void_of_deepScale
#print axioms returnFixedFamily_void_of_deepFamilies
#print axioms densePackFixedFamily_void_of_deepFamilies
#print axioms towerFP15_1Family_void_of_deepFamilies
#print axioms towerFP15_2Family_void_of_deepFamilies
#print axioms towerFP105Family_void_of_deepFamilies
#print axioms towerEscapeLever_of_towerEscape_deep
#print axioms towerEscapeLever_of_towerEscape_deepFamilies
#print axioms towerFixedPointResidual_of_deepLever
#print axioms towerFixedPointResidual_of_deepFamilies
#print axioms Erdos260DeepLeverResidual.toLeverResidual
#print axioms Erdos260DeepLeverResidual.toStatement
#print axioms erdos260_of_deepDyadicValueLever
#print axioms carryWordRigidityStatus_nonempty

end

end Erdos260
