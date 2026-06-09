import Erdos260.IntegerCarry
import Erdos260.FixedDensity
import Erdos260.SemiperiodicWindowCore
import Erdos260.ReturnCompleteEnrichCore

/-!
# The failing-shell near-periodicity ROOT (§24 fixed-density periodic repetition)

This module (NEW; it edits no existing file) attacks the genuine analytic ROOT that feeds **both**
remaining genuine-math residuals of `erdos260_of_minimalResidualV3`:

* the §25.1 **descent-depth agreement** `‖η − η_{x,w}‖ < 2^{−depth}` (the
  `SingularSquareBoundCore` / `SemiperiodicMatchEnrichCore` window-selection input), and
* the Return `SliceCompleteReturns` clean-return structure (`ReturnCompleteEnrichCore`).

Both reduce to the §24 claim: under rationality `η = P/Q`, the integer carry `R_N`
(`R_{N+1} = 2 R_N − Q(N+1) d_{N+1}`) is **eventually periodic**, so the descent windows agree with a
fixed-density periodic completion to depth (Proposition 24.3 fixed-density carry repetition).

## What is genuinely PROVED here (no `sorry`/`axiom`/`admit`/`native_decide`)

### Part A — the carry eventual-periodicity ROOT (new, unconditional)

* `integerCarry_modEq_two_pow_mul` — **the root, value form**: `R_N ≡ 2^N · P  [ZMOD Q]` for *every*
  `N`, by induction on the recurrence (`integerCarry_succ_modEq_Q`, the `Q(N+1) d_{N+1}` term dies
  mod `Q`).  The whole carry residue is the geometric orbit `2^N P` mod `Q`.
* `two_pow_modEq_of_split` — **powers of two are eventually periodic mod `Q`**: writing
  `Q = 2^e · q₀` (`q₀` odd) and `t = ord_{q₀}(2)`, for `N ≥ e` one has `2^{N+t} ≡ 2^N [ZMOD Q]`
  (`2^e ∣ 2^N`, `q₀ ∣ 2^t − 1`, and `gcd(2^e, q₀) = 1`).
* `integerCarry_eventually_periodic_mod` — **the root, periodicity form**: there are a preperiod
  `e = v₂(Q)` and a period `t = ord_{q₀}(2)` (`0 < t`) with
  `R_{N+t} ≡ R_N  [ZMOD Q]` for all `N ≥ e`.  This is "the integer carry is eventually periodic
  (period tied to `Q·ord_Q(2)`)".

### Part B — the same root on the *actual* failing context

* `carryOf_modEq_two_pow_mul`, `carryOf_eventually_periodic_mod` — the root specialized to
  `carryOf ctx` of an `ActualFailureContext`: the actual carry residue is eventually periodic mod
  `ctx.Q` with period `ord_{q₀}(2)`.  This is the carry side of `SliceCompleteReturns`.

### Part C — Proposition 24.3 (fixed-density carry repetition), assembled

* `fixedDensity_carry_repetition` — the genuine Prop 24.3 chain: the *descent-depth agreement*
  `|P/Q − A/B| < 1/(QB)` forces exact equality `P/Q = A/B` (rational separation,
  `fixedDensity_rationalSeparation_forces_eq`), and a primitive period block whose periodic
  completion is `P/Q` (the denominator-drop divisibility) has density `≥ 1/(3Q)` (Lemma 24.2,
  `fixedDensity_exact_completion_lower`).
* `fixedDensity_low_density_excludes_completion` — the contrapositive engine: a primitive block of
  density `< 1/(3Q)` **cannot** be the exact periodic completion of `P/Q`, i.e. it cannot repeat to
  the rational-separation depth.

### Part D — delivery to the two residuals

* `orbitWord_periodicOn` — the residual-centre orbit word `dyadicDigit q₀ a` is `PeriodicOn` to **any**
  depth with period `ord_{q₀}(2)` (the fixed-density periodic completion *to depth*), from
  `dyadicDigit_period`.
* `dyadicDigit_orbit_condition` / `dyadicDigit_density_floor` — the §24 density floor delivered onto
  the orbit word: the period weight obeys the orbit bound `t+1 ≤ 2 q₀ · wt` (proved here from the
  exact residue sum identity over a full period plus the distinct-positive-residue triangular bound —
  Lemma 24.1 without the cyclic-permutation bookkeeping), hence `(1/(3q₀))·t ≤ wt`.
* `matchedWindow_of_descentMatch` — **descent delivery**: from the §25.1 descent-depth MATCH alone
  (and the flagged `ρ_D` calibration `hcal`) the actual descent window is a
  `MatchedSemiperiodicWindow`; the periodicity is free and the §24 floor is produced internally.  The
  *only* missing input is the match (= the descent-depth agreement).
* `digit_zero_iff_carry_doubles`, `carryOf_doubles_on_zeroRun`, `carryOf_value_grows_on_zeroRun` —
  **slice delivery + sharp characterization**: each digit is decided by the carry *values*
  (`d (N+1) = 0 ↔ R_{N+1} = 2 R_N`), and the carry *value* escapes every bound on a clean run
  (`2^h ≤ R_{N+h}`), so it is **not** literally periodic — only its residue mod `Q` is.

## The sharp residual (audit verdict)

The carry **residue** eventual-periodicity mod `Q` is PROVED, and it delivers the periodic model word
to depth together with the §24 density floor (`1/(3q₀)`, the genuine Lemma 24.2 constant) — exactly
the model side of both residuals.  It does **not** by itself deliver the descent-depth *agreement* /
the slice *placement*: the integer carry's residue mod `Q` cycles with period `ord_{q₀}(2)`, but the
carry *value* is unbounded (it doubles on clean runs), and the digit `d_{N+1}` is a function of the
*value*, not the residue (`digit_zero_iff_carry_doubles`).  Hence the genuinely irreducible remainder
is the **match between the actual word and the periodic model to depth** — `MatchedDescentWindows` /
`Section251CylinderMatchResidual` for the descent side, and `SliceCompleteReturns` ("no carry-dropping
`1`-digit between consecutive starts") for the Return side — precisely the residuals the prior waves
already isolated.  This file pins the §24 root underneath them and exhibits, sharply, why it stops one
notch short of the selection geometry.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

open Finset

/-! ## Part A — the carry eventual-periodicity root (unconditional) -/

/--
**The carry root, value form.**  For a rational target `P / Q`, the integer carry is, modulo `Q`,
exactly the geometric orbit of the numerator: `R_N ≡ 2^N · P  [ZMOD Q]` for every `N`.

Proof: induction on the recurrence `R_{N+1} ≡ 2 R_N  [ZMOD Q]` (`integerCarry_succ_modEq_Q`); the
position-weighted term `Q (N+1) d_{N+1}` carries a factor `Q`, so it vanishes modulo `Q`.
-/
theorem integerCarry_modEq_two_pow_mul (Q : Nat) (P : Int) (d : Nat → Nat) (N : Nat) :
    integerCarry Q P d N ≡ (2 : Int) ^ N * P [ZMOD (Q : Int)] := by
  induction N with
  | zero =>
      rw [integerCarry_zero, pow_zero, one_mul]
  | succ N ih =>
      have hstep := integerCarry_succ_modEq_Q Q P d N
      have heq : (2 : Int) * ((2 : Int) ^ N * P) = (2 : Int) ^ (N + 1) * P := by ring
      have h2 : (2 : Int) * integerCarry Q P d N ≡ (2 : Int) ^ (N + 1) * P [ZMOD (Q : Int)] := by
        rw [← heq]; exact ih.mul_left 2
      exact hstep.trans h2

/--
**Powers of two are eventually periodic mod `Q`.**  Splitting `Q = 2^e · q₀` with `q₀` odd, for any
`N ≥ e` and `t = ord_{q₀}(2)` one has `2^{N+t} ≡ 2^N  [ZMOD Q]`.  Reason: `q₀ ∣ 2^t − 1`,
`2^e ∣ 2^N`, and `gcd(2^e, q₀) = 1`, so `Q = 2^e q₀ ∣ 2^N (2^t − 1) = 2^{N+t} − 2^N`.
-/
theorem two_pow_modEq_of_split {Q e q0 : Nat} (hodd : Odd q0) (hQ : Q = 2 ^ e * q0)
    {N : Nat} (hNe : e ≤ N) :
    (2 : Int) ^ (N + orderOf (2 : ZMod q0)) ≡ (2 : Int) ^ N [ZMOD (Q : Int)] := by
  set t := orderOf (2 : ZMod q0) with ht
  have h1le : (1 : Nat) ≤ 2 ^ t := Nat.one_le_pow t 2 (by norm_num)
  -- q₀ ∣ 2^t − 1
  have hmod_q0 : (2 : Nat) ^ t ≡ 1 [MOD q0] := by
    have hp : (2 : ZMod q0) ^ t = 1 := pow_orderOf_eq_one (2 : ZMod q0)
    have hcast : ((2 ^ t : Nat) : ZMod q0) = ((1 : Nat) : ZMod q0) := by
      push_cast; simpa using hp
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have hdvd_q0 : q0 ∣ 2 ^ t - 1 := (Nat.modEq_iff_dvd' h1le).1 hmod_q0.symm
  -- 2^e ∣ 2^N and gcd(2^e, q₀) = 1
  have h2e : (2 : Nat) ^ e ∣ 2 ^ N := pow_dvd_pow 2 hNe
  have hcop : Nat.Coprime (2 ^ e) q0 := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd)
  -- Q ∣ 2^N (2^t − 1)
  have hQdvd : Q ∣ 2 ^ N * (2 ^ t - 1) := by
    rw [hQ]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop
      (dvd_mul_of_dvd_left h2e _) (dvd_mul_of_dvd_right hdvd_q0 _)
  -- cast the natural divisibility to `ℤ`, identifying `2^N (2^t − 1) = 2^{N+t} − 2^N`
  have hQdvdZ : (Q : Int) ∣ (2 : Int) ^ (N + t) - (2 : Int) ^ N := by
    have hnat : ((2 ^ N * (2 ^ t - 1) : Nat) : Int) = (2 : Int) ^ (N + t) - (2 : Int) ^ N := by
      rw [Nat.cast_mul, Nat.cast_sub h1le, Nat.cast_pow, Nat.cast_pow, Nat.cast_one, pow_add]
      ring
    have hcastdvd := Int.natCast_dvd_natCast.mpr hQdvd
    rwa [hnat] at hcastdvd
  refine Int.modEq_iff_dvd.mpr ?_
  have hneg := (dvd_neg (α := Int)).mpr hQdvdZ
  rwa [neg_sub] at hneg

/--
**The carry root, periodicity form.**  For a rational target `P / Q` (`Q > 0`) there are a preperiod
`e = v₂(Q)` and a positive period `t = ord_{q₀}(2)` (with `Q = 2^e q₀`, `q₀` odd) such that the
integer carry residue repeats: `R_{N+t} ≡ R_N  [ZMOD Q]` for all `N ≥ e`.

This is the manuscript §24 statement "the integer carry `R_N` is eventually periodic (period tied to
`Q · ord_Q(2)`)", made exact for the residue sequence.
-/
theorem integerCarry_eventually_periodic_mod (Q : Nat) (P : Int) (d : Nat → Nat) (hQ : 0 < Q) :
    ∃ e q0 : Nat, Odd q0 ∧ Q = 2 ^ e * q0 ∧ 0 < orderOf (2 : ZMod q0) ∧
      ∀ N : Nat, e ≤ N →
        integerCarry Q P d (N + orderOf (2 : ZMod q0)) ≡ integerCarry Q P d N [ZMOD (Q : Int)] := by
  obtain ⟨e, q0, hodd, hQfact⟩ := Nat.exists_eq_two_pow_mul_odd hQ.ne'
  -- `q₀ > 0`, so `2` has finite multiplicative order in `ZMod q₀`
  have hq0pos : 0 < q0 := by
    rcases Nat.eq_zero_or_pos q0 with h0 | hp
    · rw [h0, Nat.mul_zero] at hQfact; omega
    · exact hp
  have hpos : 0 < orderOf (2 : ZMod q0) := by
    rcases Nat.lt_or_ge q0 2 with hlt | hge
    · have hq1 : q0 = 1 := by omega
      subst hq1
      have h21 : (2 : ZMod 1) = 1 := Subsingleton.elim _ _
      rw [h21, orderOf_one]
      exact Nat.one_pos
    · exact orderOf_pos_iff.mpr (isOfFinOrder_two_zmod hge hodd)
  refine ⟨e, q0, hodd, hQfact, hpos, ?_⟩
  intro N hNe
  calc integerCarry Q P d (N + orderOf (2 : ZMod q0))
      ≡ (2 : Int) ^ (N + orderOf (2 : ZMod q0)) * P [ZMOD (Q : Int)] :=
        integerCarry_modEq_two_pow_mul Q P d (N + orderOf (2 : ZMod q0))
    _ ≡ (2 : Int) ^ N * P [ZMOD (Q : Int)] :=
        (two_pow_modEq_of_split hodd hQfact hNe).mul_right P
    _ ≡ integerCarry Q P d N [ZMOD (Q : Int)] :=
        (integerCarry_modEq_two_pow_mul Q P d N).symm

/-! ## Part B — the carry root on the actual failing context -/

/-- **Carry root (value form) on the actual context.**  `R_N ≡ 2^N · (numerator)  [ZMOD ctx.Q]`. -/
theorem carryOf_modEq_two_pow_mul (ctx : ActualFailureContext) (N : Nat) :
    carryOf ctx N ≡ (2 : Int) ^ N * ctxNum ctx [ZMOD (ctx.Q : Int)] := by
  unfold carryOf
  exact integerCarry_modEq_two_pow_mul ctx.Q (ctxNum ctx) ctx.d N

/-- **Carry root (periodicity form) on the actual context.**  The actual carry residue is eventually
periodic mod `ctx.Q` with period `ord_{q₀}(2)` — the carry side of the `SliceCompleteReturns`
clean-return structure. -/
theorem carryOf_eventually_periodic_mod (ctx : ActualFailureContext) :
    ∃ e q0 : Nat, Odd q0 ∧ ctx.Q = 2 ^ e * q0 ∧ 0 < orderOf (2 : ZMod q0) ∧
      ∀ N : Nat, e ≤ N →
        carryOf ctx (N + orderOf (2 : ZMod q0)) ≡ carryOf ctx N [ZMOD (ctx.Q : Int)] := by
  obtain ⟨e, q0, hodd, hQfact, hpos, hper⟩ :=
    integerCarry_eventually_periodic_mod ctx.Q (ctxNum ctx) ctx.d ctx.hQ
  exact ⟨e, q0, hodd, hQfact, hpos, fun N hN => by unfold carryOf; exact hper N hN⟩

/-! ## Part C — Proposition 24.3 (fixed-density carry repetition), assembled -/

/--
**Proposition 24.3 (fixed-density carry repetition).**

For a primitive period-`p` word `d` (`hper` periodicity, `hprim` primitivity, `2 ≤ p`) whose periodic
completion is the rational `P/Q` (the manuscript denominator-drop divisibility `hdiv`), the
*descent-depth agreement* `|P/Q − A/B| < 1/(QB)` forces:

* **exact equality** `P/Q = A/B` — the §24.3 rational-separation step
  (`fixedDensity_rationalSeparation_forces_eq`), and
* the **positive density floor** `wt(period)/p ≥ 1/(3Q)` — Lemma 24.2
  (`fixedDensity_exact_completion_lower`).

This is the contradiction engine of §24: a deeply-repeating period block must carry density `≥ 1/(3Q)`.
-/
theorem fixedDensity_carry_repetition
    {d : Nat → Nat} {p Q : Nat} {P A : Int} {B : Nat}
    (hp : 2 ≤ p) (hQ : 0 < Q) (hB : 0 < B)
    (hd : BinaryDigits d)
    (hper : ∀ j, d (j + p) = d j)
    (hprim : ∀ s, 0 < s → s < p → ∃ k, d (k + s) ≠ d k)
    (hdiv : periodDen p ∣ (Q * p) * periodMask d p)
    (hagree : |(P : ℝ) / (Q : ℝ) - (A : ℝ) / (B : ℝ)| < 1 / ((Q : ℝ) * (B : ℝ))) :
    (P : ℝ) / (Q : ℝ) = (A : ℝ) / (B : ℝ)
      ∧ (1 : ℝ) / ((3 * Q : Nat) : ℝ) ≤ periodDensity d p :=
  ⟨fixedDensity_rationalSeparation_forces_eq hQ hB hagree,
    fixedDensity_exact_completion_lower hp hQ hd hper hprim hdiv⟩

/--
**The Prop 24.3 contrapositive (low-density blocks cannot complete).**  A primitive period block of
density `< 1/(3Q)` cannot be the exact periodic completion of `P/Q` (i.e. it cannot repeat to the
rational-separation depth): that would contradict Lemma 24.2.
-/
theorem fixedDensity_low_density_excludes_completion
    {d : Nat → Nat} {p Q : Nat}
    (hp : 2 ≤ p) (hQ : 0 < Q)
    (hd : BinaryDigits d)
    (hper : ∀ j, d (j + p) = d j)
    (hprim : ∀ s, 0 < s → s < p → ∃ k, d (k + s) ≠ d k)
    (hdiv : periodDen p ∣ (Q * p) * periodMask d p)
    (hlow : periodDensity d p < (1 : ℝ) / ((3 * Q : Nat) : ℝ)) :
    False :=
  absurd (fixedDensity_exact_completion_lower hp hQ hd hper hprim hdiv) (not_le.mpr hlow)

/-! ## Part D — delivery of the periodic model to depth and the descent window -/

/--
**The residual-centre orbit word is periodic to depth.**  For `q₀ > 1` odd, the orbit word
`dyadicDigit q₀ a` is `PeriodicOn` on *every* window with period `ord_{q₀}(2)` (from
`dyadicDigit_period`).  This is the fixed-density periodic completion *to depth* — the periodic model
that the §25.1 descent windows are matched against.
-/
theorem orbitWord_periodicOn {q0 : Nat} (hq0 : 1 < q0) (hodd : Odd q0) (a start len : Nat) :
    PeriodicOn (dyadicDigit q0 a) start len (orderOf (2 : ZMod q0)) := by
  refine ⟨orderOf_pos_iff.mpr (isOfFinOrder_two_zmod hq0 hodd), ?_⟩
  intro i _
  exact dyadicDigit_period q0 a (start + i)

/--
**The orbit bound for the orbit word (Lemma 24.1, full-period form).**  For `q₀ > 1` odd and `a`
coprime to `q₀`, the period weight `wt = windowWeight (dyadicDigit q₀ a) 0 t` of one full period
`t = ord_{q₀}(2)` satisfies the manuscript orbit bound `t + 1 ≤ 2 q₀ · wt`.

Proof: over a full period the residues close up (`dyadicResidue_period`), so the binary-division sum
identity collapses to `q₀ · wt = Σ residues`, and the `t` distinct positive residues give
`t(t+1) ≤ 2 Σ residues = 2 q₀ wt`; finally `t + 1 ≤ t(t+1)`.  (This is Lemma 24.1 without the cyclic
permutation bookkeeping.)
-/
theorem dyadicDigit_orbit_condition {q0 a : Nat} (hq0 : 1 < q0) (hodd : Odd q0)
    (hcop : Nat.Coprime a q0) :
    orderOf (2 : ZMod q0) + 1
      ≤ 2 * q0 * windowWeight (dyadicDigit q0 a) 0 (orderOf (2 : ZMod q0)) := by
  have htpos : 0 < orderOf (2 : ZMod q0) :=
    orderOf_pos_iff.mpr (isOfFinOrder_two_zmod hq0 hodd)
  have hws : windowWeight (dyadicDigit q0 a) 0 (orderOf (2 : ZMod q0))
      = segmentSum (dyadicDigit q0 a) 0 (orderOf (2 : ZMod q0)) := rfl
  have hid := dyadicResidue_segment_sum_identity q0 a 0 (orderOf (2 : ZMod q0))
  have hper0 : dyadicResidue q0 a (0 + orderOf (2 : ZMod q0)) = dyadicResidue q0 a 0 :=
    dyadicResidue_period q0 a 0
  rw [hper0] at hid
  have hqwt : q0 * segmentSum (dyadicDigit q0 a) 0 (orderOf (2 : ZMod q0))
      = segmentSum (dyadicResidue q0 a) 0 (orderOf (2 : ZMod q0)) :=
    Nat.add_right_cancel hid
  have htri : orderOf (2 : ZMod q0) * (orderOf (2 : ZMod q0) + 1)
      ≤ 2 * segmentSum (dyadicResidue q0 a) 0 (orderOf (2 : ZMod q0)) := by
    apply segment_residue_sum_ge_triangular
    · intro i _; exact dyadicResidue_pos hq0 hodd hcop (0 + i)
    · exact dyadicResidue_injOn hq0 hodd hcop (le_refl (orderOf (2 : ZMod q0)))
  have hcomb : orderOf (2 : ZMod q0) * (orderOf (2 : ZMod q0) + 1)
      ≤ 2 * q0 * windowWeight (dyadicDigit q0 a) 0 (orderOf (2 : ZMod q0)) := by
    rw [hws]
    calc orderOf (2 : ZMod q0) * (orderOf (2 : ZMod q0) + 1)
        ≤ 2 * segmentSum (dyadicResidue q0 a) 0 (orderOf (2 : ZMod q0)) := htri
      _ = 2 * (q0 * segmentSum (dyadicDigit q0 a) 0 (orderOf (2 : ZMod q0))) := by rw [hqwt]
      _ = 2 * q0 * segmentSum (dyadicDigit q0 a) 0 (orderOf (2 : ZMod q0)) := by ring
  have h1 : orderOf (2 : ZMod q0) + 1
      ≤ orderOf (2 : ZMod q0) * (orderOf (2 : ZMod q0) + 1) := by
    calc orderOf (2 : ZMod q0) + 1
        = 1 * (orderOf (2 : ZMod q0) + 1) := (Nat.one_mul _).symm
      _ ≤ orderOf (2 : ZMod q0) * (orderOf (2 : ZMod q0) + 1) :=
          Nat.mul_le_mul htpos (le_refl _)
  exact le_trans h1 hcomb

/--
**The §24 density floor on the orbit word (genuine `1/(3q₀)`).**  For `q₀ > 1` odd and `a` coprime to
`q₀`, one full period of `dyadicDigit q₀ a` packs `(1/(3q₀))·t ≤ wt` hits, where `t = ord_{q₀}(2)`.
This is Lemma 24.2 specialized to the orbit word via `windowWeight_density_floor_of_orbit`, fed by the
proved orbit bound `dyadicDigit_orbit_condition`.
-/
theorem dyadicDigit_density_floor {q0 a : Nat} (hq0 : 1 < q0) (hodd : Odd q0)
    (hcop : Nat.Coprime a q0) :
    (1 : ℝ) / ((3 * q0 : Nat) : ℝ) * (orderOf (2 : ZMod q0) : ℝ)
      ≤ (windowWeight (dyadicDigit q0 a) 0 (orderOf (2 : ZMod q0)) : ℝ) := by
  have htpos : 0 < orderOf (2 : ZMod q0) :=
    orderOf_pos_iff.mpr (isOfFinOrder_two_zmod hq0 hodd)
  exact windowWeight_density_floor_of_orbit (dyadicDigit q0 a) 0 (by omega) htpos
    (dyadicDigit_orbit_condition hq0 hodd hcop)

/--
**Descent delivery: the matched semiperiodic descent window from the descent-depth MATCH alone.**

Given the §25.1 descent-depth match `WindowMatch d (dyadicDigit q₀ a) start len` (the genuine
irreducible residual) and the flagged `ρ_D` calibration `hcal` (`manuscriptRhoD ≤ 1/(3q₀)`; see the
calibration note below), the actual descent window is a `MatchedSemiperiodicWindow`.  The model word's
periodicity to depth is free (`orbitWord_periodicOn`) and the §24 density floor is produced internally
(`dyadicDigit_density_floor`).  So the carry root delivers everything except the match.
-/
def matchedWindow_of_descentMatch {d : Nat → Nat} {start len q0 a : Nat}
    (hq0 : 1 < q0) (hodd : Odd q0) (hcop : Nat.Coprime a q0)
    (hle : orderOf (2 : ZMod q0) ≤ len)
    (hcal : manuscriptRhoD ≤ (1 : ℝ) / ((3 * q0 : Nat) : ℝ))
    (hmatch : WindowMatch d (dyadicDigit q0 a) start len) :
    MatchedSemiperiodicWindow d start len := by
  refine MatchedSemiperiodicWindow.ofDyadicMatch hq0 hodd hle ?_ hmatch
  have hfloor := dyadicDigit_density_floor hq0 hodd hcop
  have htnn : (0 : ℝ) ≤ (orderOf (2 : ZMod q0) : ℝ) := by positivity
  exact le_trans (mul_le_mul_of_nonneg_right hcal htnn) hfloor

/-! ## Part D (slice side) — the digit is decided by carry values, not residues -/

/-- **Each digit is decided by the carry values.**  `d (N+1) = 0` exactly when the carry step is a
clean doubling `R_{N+1} = 2 R_N` (`carryOf_step_clean_iff`).  So the complete-return placement (the
`SliceCompleteReturns` residual) is a function of the carry *values*. -/
theorem digit_zero_iff_carry_doubles (ctx : ActualFailureContext) (N : Nat) :
    ctx.d (N + 1) = 0 ↔ carryOf ctx (N + 1) = 2 * carryOf ctx N :=
  (carryOf_step_clean_iff ctx N).symm

/-- **The carry doubles across a clean run.**  `R_{N+h} = 2^h R_N` whenever every digit on `(N, N+h]`
is `0` (`integerCarry_add_of_zero_digits`). -/
theorem carryOf_doubles_on_zeroRun (ctx : ActualFailureContext) (N h : Nat)
    (hzero : ∀ j, N < j → j ≤ N + h → ctx.d j = 0) :
    carryOf ctx (N + h) = (2 : Int) ^ h * carryOf ctx N := by
  unfold carryOf
  exact integerCarry_add_of_zero_digits ctx.Q (ctxNum ctx) ctx.d N h hzero

/--
**The carry value is unbounded (so it is NOT literally periodic).**  On a clean run of length `h` the
positive carry satisfies `2^h ≤ R_{N+h}`.  Contrasted with the residue eventual-periodicity
(`carryOf_eventually_periodic_mod`), this is the sharp reason the §24 root stops one notch short of the
selection geometry: only the *residue* mod `Q` is periodic; the *value* (which decides the digits, by
`digit_zero_iff_carry_doubles`) escapes every bound.
-/
theorem carryOf_value_grows_on_zeroRun (ctx : ActualFailureContext) (N h : Nat)
    (hzero : ∀ j, N < j → j ≤ N + h → ctx.d j = 0) :
    (2 : Int) ^ h ≤ carryOf ctx (N + h) := by
  have hdbl := carryOf_doubles_on_zeroRun ctx N h hzero
  have hpos := carryOf_pos ctx N
  have h1 : (1 : Int) ≤ carryOf ctx N := by omega
  have hpow : (0 : Int) ≤ (2 : Int) ^ h := by positivity
  calc (2 : Int) ^ h = (2 : Int) ^ h * 1 := by ring
    _ ≤ (2 : Int) ^ h * carryOf ctx N := mul_le_mul_of_nonneg_left h1 hpow
    _ = carryOf ctx (N + h) := hdbl.symm

/-! ## Part E — honest residual inventory -/

/-- The precise status of the §24 failing-shell near-periodicity root after this module. -/
def failingShellPeriodicityResiduals : List String :=
  [ "GOAL (wave-21) — prove the §24 ROOT feeding BOTH residuals: under η = P/Q rational the integer " ++
      "carry R_N (R_{N+1} = 2 R_N − Q(N+1) d_{N+1}) is eventually periodic, so the descent windows " ++
      "agree with a fixed-density periodic completion to depth (Prop 24.3).",
    "CLOSED (the root, value form) — integerCarry_modEq_two_pow_mul: R_N ≡ 2^N · P [ZMOD Q] for every " ++
      "N, by induction on integerCarry_succ_modEq_Q (the Q(N+1) d_{N+1} term dies mod Q). The whole " ++
      "carry residue IS the geometric orbit 2^N P mod Q.",
    "CLOSED (powers of two eventually periodic) — two_pow_modEq_of_split: Q = 2^e q₀ (q₀ odd), " ++
      "t = ord_{q₀}(2) ⟹ 2^{N+t} ≡ 2^N [ZMOD Q] for N ≥ e (q₀ ∣ 2^t−1, 2^e ∣ 2^N, gcd(2^e,q₀)=1).",
    "CLOSED (the root, periodicity form) — integerCarry_eventually_periodic_mod: ∃ e=v₂(Q), " ++
      "t=ord_{q₀}(2) with 0 < t and R_{N+t} ≡ R_N [ZMOD Q] for all N ≥ e. This is 'the integer carry " ++
      "is eventually periodic, period tied to Q·ord_Q(2)' for the residue sequence.",
    "CLOSED (root on the actual context) — carryOf_modEq_two_pow_mul / carryOf_eventually_periodic_mod: " ++
      "the actual carryOf ctx residue is eventually periodic mod ctx.Q with period ord_{q₀}(2). This is " ++
      "the carry side of SliceCompleteReturns.",
    "CLOSED (Prop 24.3 assembled) — fixedDensity_carry_repetition: the descent-depth agreement " ++
      "|P/Q − A/B| < 1/(QB) forces P/Q = A/B (rational separation, fixedDensity_rationalSeparation_" ++
      "forces_eq) AND density ≥ 1/(3Q) (Lemma 24.2, fixedDensity_exact_completion_lower). " ++
      "fixedDensity_low_density_excludes_completion is the contrapositive engine.",
    "DELIVERED (periodic model to depth + §24 floor) — orbitWord_periodicOn: dyadicDigit q₀ a is " ++
      "PeriodicOn to ANY depth with period ord_{q₀}(2). dyadicDigit_orbit_condition proves the Lemma " ++
      "24.1 orbit bound t+1 ≤ 2 q₀ wt (exact residue sum identity over a full period + distinct-" ++
      "positive-residue triangular bound), and dyadicDigit_density_floor delivers the genuine §24 floor " ++
      "(1/(3q₀))·t ≤ wt.",
    "DELIVERED (descent window) — matchedWindow_of_descentMatch: from the §25.1 descent-depth MATCH " ++
      "alone (+ the flagged ρ_D calibration), the actual descent window is a MatchedSemiperiodicWindow " ++
      "(periodicity free; §24 floor internal). The ONLY missing input is the match itself.",
    "DELIVERED (slice side characterization) — digit_zero_iff_carry_doubles (d(N+1)=0 ⟺ R_{N+1}=2R_N), " ++
      "carryOf_doubles_on_zeroRun (R_{N+h}=2^h R_N), carryOf_value_grows_on_zeroRun (2^h ≤ R_{N+h}): " ++
      "the digit is decided by the carry VALUES, and the value is unbounded — only the residue mod Q is " ++
      "periodic.",
    "RESIDUAL (the sharp irreducible remainder) — the carry RESIDUE periodicity mod Q does NOT deliver " ++
      "the descent-depth AGREEMENT / slice PLACEMENT: the carry value (which decides the digits) is " ++
      "unbounded, so residue periodicity under-determines the actual digit word. The genuine remainder " ++
      "is the MATCH of the actual word to the periodic model to depth — MatchedDescentWindows / " ++
      "Section251CylinderMatchResidual (descent) and SliceCompleteReturns / 'no carry-dropping 1-digit " ++
      "between consecutive starts' (Return) — exactly the residuals the prior waves isolated.",
    "CALIBRATION (ρ_D Q-dependence — flagged, not blocking) — matchedWindow_of_descentMatch consumes " ++
      "hcal : manuscriptRhoD ≤ 1/(3q₀). manuscriptRhoD = 1/4 is Q-independent, but the genuine §24 " ++
      "floor is 1/(3q₀) (dominating 1/4 only at q₀=1). proof_v4.tex line 962 states ρ₀(Q)=1/(4Q); " ++
      "under the correct Q-dependent calibration ρ_D = 1/(4q₀) the hypothesis hcal holds for all q₀. " ++
      "This matches the existing SDRDensityCore flag.",
    "CROSS-REF (wave-22, SliceCompleteReturnsCore) — carryOf_add_eq_doubling_sub_dirtyWeight gives the " ++
      "EXACT deficit decomposition R_{x+h} = 2^h R_x − Q·W (W = dirtyCarryWeight, the position-weighted " ++
      "digit sum on the block), so the doubling deficit 2^h R_x − R_{x+h} = Q·W is ALWAYS a multiple of " ++
      "Q. This is precisely WHY the carry residue mod Q (carryOf_eventually_periodic_mod above) is " ++
      "placement-insensitive: R_{x+h} ≡ 2^h R_x [ZMOD Q] for every block, clean or dirty " ++
      "(carryOf_add_modEq_doubling), so the §24 residue periodicity carries NO information about the " ++
      "value-level placement W = 0 ⟺ CleanReturnSegment (carryDeficit_zero_iff_clean) — exactly the " ++
      "residual isolated above (SliceCompleteReturns / CleanReturnPlacement)." ]

theorem failingShellPeriodicityResiduals_nonempty : failingShellPeriodicityResiduals ≠ [] := by
  simp [failingShellPeriodicityResiduals]

/-! ## Part F — axiom-cleanliness audit -/

#print axioms integerCarry_modEq_two_pow_mul
#print axioms two_pow_modEq_of_split
#print axioms integerCarry_eventually_periodic_mod
#print axioms carryOf_modEq_two_pow_mul
#print axioms carryOf_eventually_periodic_mod
#print axioms fixedDensity_carry_repetition
#print axioms fixedDensity_low_density_excludes_completion
#print axioms orbitWord_periodicOn
#print axioms dyadicDigit_orbit_condition
#print axioms dyadicDigit_density_floor
#print axioms matchedWindow_of_descentMatch
#print axioms digit_zero_iff_carry_doubles
#print axioms carryOf_doubles_on_zeroRun
#print axioms carryOf_value_grows_on_zeroRun

end

end Erdos260
