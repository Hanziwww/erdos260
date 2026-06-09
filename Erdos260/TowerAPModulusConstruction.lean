import Mathlib
import Erdos260.TowerSlopeAffineLaw
import Erdos260.TowerLandingConstruction
import Erdos260.IntegerCarry
import Erdos260.CarryRecurrence

/-!
# The Tower AP-modulus parametrization: the Mersenne period of the recurrent slope

`TowerSlopeAffineLaw.lean` reduced the Tower slope atom to one residual: the
manuscript **AP-modulus datum** `(Q, h₁, h₂, a, b)` with the divisibilities
`h_Γ ∣ D_Γ = 2^{S_Γ} − 1` (the AP step modulus divides the Mersenne period),
which `towerSlopeAtomOfAPModuli` consumes.  The honest status recorded there was:

> the oddness field `Odd H` is a theorem (`apModulus_odd`); the genuinely
> geometric residual is the *identification* of the recurrent slope's modulus
> data `(Q, h₁, h₂, a, b)` with the failing-shell carry geometry — the AP
> subfibre parametrisation `B_{x_s} = B_{x_0} + s·K_Γ` (E.2–E.5).

This file **closes the arithmetic half** of that parametrization and **reduces**
the rest to a single sharply-stated geometric residual.

## What is genuinely proved here (no `sorry`, no `axiom`, no `native_decide`)

### 1. The Mersenne period is *equivalent* to oddness

* `odd_dvd_two_pow_totient_sub_one` — **the key new arithmetic fact**: every odd
  `m` divides `2^{φ(m)} − 1`.  The exponent `φ(m)` is an explicit, genuine
  Mersenne period (`S_Γ`), produced by the Fermat–Euler theorem
  `2^{φ(m)} ≡ 1 [MOD m]` for `gcd(2,m)=1`.
* `exists_mersenne_period_of_odd`, `odd_iff_exists_dvd_mersenne` —
  `Odd m ↔ ∃ S ≥ 1, m ∣ 2^S − 1`.  The manuscript divisibility
  `K_Γ ∣ D_Γ = 2^{S_Γ} − 1` is therefore **exactly equivalent to oddness of the
  modulus**, the converse of `apModulus_odd`.  Since the recurrent slope's
  reduced denominator is *already proved odd* (`carryCycle_den_odd`, by the
  2-adic descent), the Mersenne-period divisibility is **not an extra geometric
  hypothesis** — it is automatic.

### 2. The AP-modulus datum from oddness alone

* `towerSlopeAtomOfOddModuli` / `towerOfSlopeOfOddModuli` — the `TowerSlopeAtom`
  (and the full Phase-7 `TowerTransientFactoryData`) **constructed from oddness**
  of the AP moduli, with the Mersenne divisibilities discharged internally via
  `φ`.  This shows the `hd₁ : h₁ ∣ 2^a − 1`, `hd₂ : h₂ ∣ 2^b − 1` inputs of
  `towerSlopeAtomOfAPModuli` are *redundant*.

### 3. The Mersenne period in the actual integer carry recurrence

* `integerCarry_modEq_Q_pow` — `R_N ≡ 2^N · P [ZMOD Q]`: the carry residues mod
  the target denominator `Q` are exactly the doubling orbit of `P = R_0`
  (from `integerCarry_succ_modEq_Q`), the residue-level shadow of the E.13
  doubling law.
* `integerCarry_zeroRun_modEq_of_dvd_mersenne` / `integerCarry_zeroRun_modEq_totient`
  — **the carry-side parametrization**: across a zero-digit run of Mersenne-period
  length `S` (with `q ∣ 2^S − 1`, e.g. `S = φ(q)` for odd `q`) the integer carry
  *returns to its residue* mod `q`:  `R_{N+S} ≡ R_N [ZMOD q]`.  This is the AP /
  periodic subfibre structure read off directly from the integer-carry doubling
  `R_{N+h} = 2^h R_N` (`integerCarry_add_of_zero_digits`), with the modulus
  dividing the Mersenne period `2^S − 1`.

### 4. The capstone: AP-modulus datum *from the recurrent cycle*

* `den_ge_two_of_Ioo`, `recurrentSlope_den_ge_two`,
  `recurrentSlope_den_odd_dvd_mersenne` — for a recurrent `CarryFibreCycleData`
  with rational slopes, every cycle slope `μ_i` has reduced denominator
  `q_i = (μ_i).den` that is **odd, `≥ 2`, and divides the Mersenne period
  `2^{φ(q_i)} − 1`** — the manuscript `K_Γ ∣ D_Γ` for the *actual* recurrent
  slope.
* `towerSlopeAtomOfRecurrentCycle` / `towerOfSlopeOfRecurrentCycle` — the
  `TowerSlopeAtom` and full Tower factory **constructed from a recurrent
  carry-fibre cycle** (rational slopes) plus a nonzero target denominator `Q`,
  closing the chain *recurrent cycle → odd denominator → Mersenne period →
  Tower slope atom → Phase-7 factory*.

## Honest status

The AP-modulus parametrization is **REDUCED**, with its arithmetic core
**CLOSED**:

* **CLOSED.**  The "modulus `K_Γ` divides the Mersenne period
  `D_Γ = 2^{S_Γ} − 1`" half of E.2–E.5 is now a theorem, *equivalent to oddness*
  (`odd_iff_exists_dvd_mersenne`), and oddness of the recurrent slope denominator
  is itself already proved (`carryCycle_den_odd`).  No Mersenne-divisibility
  hypothesis is needed any longer.

* **REDUCED.**  The full `TowerSlopeAtom` is constructed from a recurrent
  `CarryFibreCycleData` with rational slopes (`towerSlopeAtomOfRecurrentCycle`),
  and the period is exhibited at the level of the raw integer carry
  (`integerCarry_zeroRun_modEq_totient`).

* **IRREDUCIBLE residual (precise).**  What remains *not* formalized is the
  geometric realization: producing, from the raw `integerCarry` data of an actual
  failing shell, the recurrent cycle datum `(D : CarryFibreCycleData, μ : Fin
  D.n → ℚ, hcast : (μ i : ℝ) = D.slope i)` together with its nonzero `Q` — i.e.
  the additive AP-subfibre geometry `B_{x_s} = B_{x_0} + s·K_Γ` indexing the
  fibre by actual shell positions and the assignment of normalized rational
  slopes to recurrent vertices.  This is the unformalized Appendix E.2–E.4
  shell/fibre combinatorics; everything *given* such a triple is now a theorem.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1. The Mersenne period of an odd modulus

The manuscript period `D_Γ = 2^{S_Γ} − 1`: every odd modulus divides such a
Mersenne number, with the Euler totient `φ` providing an explicit exponent.  This
is the *converse* of `apModulus_odd` (`TowerLandingConstruction`), and together
they make "divides a Mersenne number" equivalent to "odd". -/

/--
**Every odd modulus divides a Mersenne number `2^{φ(m)} − 1`.**

By the Fermat–Euler theorem `2^{φ(m)} ≡ 1 [MOD m]` (valid since `gcd(2,m)=1` for
odd `m`), so `m ∣ 2^{φ(m)} − 1`.  The totient `φ(m)` is the explicit manuscript
Mersenne period `S_Γ`. -/
theorem odd_dvd_two_pow_totient_sub_one {m : ℕ} (hm : Odd m) :
    m ∣ 2 ^ Nat.totient m - 1 := by
  have hcop : Nat.Coprime 2 m := hm.coprime_two_left
  have hmod : (2 : ℕ) ^ Nat.totient m ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop
  have hle : (1 : ℕ) ≤ 2 ^ Nat.totient m := Nat.one_le_pow (Nat.totient m) 2 (by norm_num)
  exact (Nat.modEq_iff_dvd' hle).mp hmod.symm

/-- The Mersenne exponent `φ(m)` is `≥ 1` for any odd `m` (since odd `⇒ m > 0`). -/
theorem one_le_totient_of_odd {m : ℕ} (hm : Odd m) : 1 ≤ Nat.totient m :=
  Nat.totient_pos.mpr hm.pos

/--
**A Mersenne period exists for every odd modulus.**  `Odd m ⇒ ∃ S ≥ 1, m ∣ 2^S − 1`,
witnessed by `S = φ(m)`.  This is the existence form of the manuscript
`K_Γ ∣ D_Γ = 2^{S_Γ} − 1`, derived purely from oddness. -/
theorem exists_mersenne_period_of_odd {m : ℕ} (hm : Odd m) :
    ∃ S : ℕ, 1 ≤ S ∧ m ∣ 2 ^ S - 1 :=
  ⟨Nat.totient m, one_le_totient_of_odd hm, odd_dvd_two_pow_totient_sub_one hm⟩

/--
**"Divides a Mersenne number" is equivalent to "odd".**

`Odd m ↔ ∃ S ≥ 1, m ∣ 2^S − 1`.  The forward direction is the new Euler/totient
argument; the converse is the existing `odd_of_dvd_odd ∘ odd_two_pow_sub_one`
(`TowerLandingConstruction`).  Hence the manuscript AP-modulus divisibility
`K_Γ ∣ D_Γ = 2^{S_Γ} − 1` carries *exactly* the information that `K_Γ` is odd —
which the 2-adic descent already proves for recurrent slopes
(`carryCycle_den_odd`). -/
theorem odd_iff_exists_dvd_mersenne {m : ℕ} :
    Odd m ↔ ∃ S : ℕ, 1 ≤ S ∧ m ∣ 2 ^ S - 1 := by
  constructor
  · exact exists_mersenne_period_of_odd
  · rintro ⟨S, hS, hdvd⟩
    exact odd_of_dvd_odd (odd_two_pow_sub_one hS) hdvd

/-! ## 2. The AP-modulus datum from oddness alone

The Mersenne divisibilities `h₁ ∣ 2^a − 1`, `h₂ ∣ 2^b − 1` consumed by
`towerSlopeAtomOfAPModuli` are now *redundant*: oddness of `h₁, h₂` produces them
via `φ`.  We repackage the slope atom and the full Tower factory accordingly. -/

/--
**`TowerSlopeAtom` from oddness of the AP moduli.**

Given `Q ≠ 0`, odd AP moduli `h₁, h₂`, and the cycle nontriviality
`2 ≤ lcm h₁ h₂`, this builds the slope atom by feeding
`towerSlopeAtomOfAPModuli` with the *derived* Mersenne exponents
`a = φ(h₁)`, `b = φ(h₂)` and the divisibilities
`odd_dvd_two_pow_totient_sub_one`.  The Mersenne-divisibility input has been
eliminated. -/
def towerSlopeAtomOfOddModuli (Q h₁ h₂ : ℕ) (hQ : Q ≠ 0)
    (ho₁ : Odd h₁) (ho₂ : Odd h₂) (hH2 : 2 ≤ Nat.lcm h₁ h₂) : TowerSlopeAtom :=
  towerSlopeAtomOfAPModuli Q h₁ h₂ (Nat.totient h₁) (Nat.totient h₂) hQ
    (one_le_totient_of_odd ho₁) (one_le_totient_of_odd ho₂)
    (odd_dvd_two_pow_totient_sub_one ho₁) (odd_dvd_two_pow_totient_sub_one ho₂) hH2

/--
**Tower transient factory data from oddness of the AP moduli.**

Feeding `towerSlopeAtomOfOddModuli` through the proved `towerOfSlope` chain yields
the budget-respecting Phase-7 `TowerTransientFactoryData`, with the Mersenne
divisibilities discharged from oddness alone. -/
def towerOfSlopeOfOddModuli (Q h₁ h₂ : ℕ) (hQ : Q ≠ 0)
    (ho₁ : Odd h₁) (ho₂ : Odd h₂) (hH2 : 2 ≤ Nat.lcm h₁ h₂) {X : ℝ} (hX : 0 ≤ X) :
    TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ X :=
  towerOfSlope (towerSlopeAtomOfOddModuli Q h₁ h₂ hQ ho₁ ho₂ hH2) hX

/-- **Non-vacuity.**  `Q = 1`, `h₁ = h₂ = 5` (odd), `lcm = 5 ≥ 2` builds a genuine
`TowerSlopeAtom` of slope modulus `5` (the `twoCycleExample` modulus) from oddness
alone, with the Mersenne period `5 ∣ 2^{φ(5)} − 1 = 2^4 − 1 = 15` derived. -/
theorem towerSlopeAtomOfOddModuli_nonvacuous :
    ∃ a : TowerSlopeAtom, a.H = 5 :=
  ⟨towerSlopeAtomOfOddModuli 1 5 5 (by norm_num) ⟨2, by norm_num⟩ ⟨2, by norm_num⟩
      (by norm_num),
    by norm_num [towerSlopeAtomOfOddModuli, towerSlopeAtomOfAPModuli]⟩

/-! ## 3. The Mersenne period in the integer carry recurrence

We expose the period directly on the raw integer carry `R_N = integerCarry Q P d N`
(`IntegerCarry.lean`), using only its recurrence. -/

/--
**Carry residues mod `Q` are the doubling orbit of `P`.**

`R_N ≡ 2^N · P [ZMOD Q]`.  The subtracted term `Q·(N+1)·d_{N+1}` of the carry
recurrence vanishes mod `Q` (`integerCarry_succ_modEq_Q`), so the residues mod the
target denominator `Q` evolve by pure doubling from `R_0 = P` — the residue-level
shadow of the E.13 doubling law. -/
theorem integerCarry_modEq_Q_pow (Q : ℕ) (P : ℤ) (d : ℕ → ℕ) (N : ℕ) :
    integerCarry Q P d N ≡ 2 ^ N * P [ZMOD (Q : ℤ)] := by
  induction N with
  | zero =>
      calc integerCarry Q P d 0 = 2 ^ 0 * P := by rw [integerCarry_zero, pow_zero, one_mul]
        _ ≡ 2 ^ 0 * P [ZMOD (Q : ℤ)] := Int.ModEq.refl _
  | succ N ih =>
      have hstep := integerCarry_succ_modEq_Q Q P d N
      have hdbl : (2 : ℤ) * integerCarry Q P d N ≡ 2 * (2 ^ N * P) [ZMOD (Q : ℤ)] :=
        Int.ModEq.mul_left 2 ih
      have hcomb : integerCarry Q P d (N + 1) ≡ 2 * (2 ^ N * P) [ZMOD (Q : ℤ)] :=
        hstep.trans hdbl
      rw [show (2 : ℤ) ^ (N + 1) * P = 2 * (2 ^ N * P) by ring]
      exact hcomb

/--
**The carry returns to its residue across a zero run of Mersenne-period length.**

If `q ∣ 2^S − 1` (so `2^S ≡ 1 [ZMOD q]`) and the digits in `(N, N+S]` are all
zero, then the integer carry satisfies `R_{N+S} ≡ R_N [ZMOD q]`.  Across the zero
run the carry doubles exactly (`integerCarry_add_of_zero_digits`),
`R_{N+S} = 2^S · R_N`, and `2^S ≡ 1 [ZMOD q]` collapses it back to `R_N`.

This is the manuscript AP-subfibre periodicity at the level of the raw integer
carry: the reachable carry states over a zero run are periodic mod `q` with a
period dividing the Mersenne period `2^S − 1`. -/
theorem integerCarry_zeroRun_modEq_of_dvd_mersenne (Q : ℕ) (P : ℤ) (d : ℕ → ℕ)
    (N S : ℕ) {q : ℕ} (hq : (q : ℤ) ∣ 2 ^ S - 1)
    (hzero : ∀ j : ℕ, N < j → j ≤ N + S → d j = 0) :
    integerCarry Q P d (N + S) ≡ integerCarry Q P d N [ZMOD (q : ℤ)] := by
  rw [integerCarry_add_of_zero_digits Q P d N S hzero]
  have h1 : (2 : ℤ) ^ S ≡ 1 [ZMOD (q : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    have heq : (1 : ℤ) - 2 ^ S = -(2 ^ S - 1) := by ring
    rw [heq]
    exact dvd_neg.mpr hq
  have h2 := Int.ModEq.mul_right (integerCarry Q P d N) h1
  simpa using h2

/--
**Totient form of the carry Mersenne periodicity.**

For an *odd* modulus `q`, the explicit Mersenne period `S = φ(q)` works: across a
zero run of length `φ(q)` the carry returns to its residue mod `q`,
`R_{N+φ(q)} ≡ R_N [ZMOD q]`.  The period `φ(q)` is the manuscript `S_Γ` and
`q ∣ 2^{φ(q)} − 1` is the Mersenne divisibility, both proved. -/
theorem integerCarry_zeroRun_modEq_totient (Q : ℕ) (P : ℤ) (d : ℕ → ℕ) (N : ℕ) {q : ℕ}
    (hq : Odd q)
    (hzero : ∀ j : ℕ, N < j → j ≤ N + Nat.totient q → d j = 0) :
    integerCarry Q P d (N + Nat.totient q) ≡ integerCarry Q P d N [ZMOD (q : ℤ)] := by
  refine integerCarry_zeroRun_modEq_of_dvd_mersenne Q P d N (Nat.totient q) ?_ hzero
  have hnat : q ∣ 2 ^ Nat.totient q - 1 := odd_dvd_two_pow_totient_sub_one hq
  have hcast : ((2 ^ Nat.totient q - 1 : ℕ) : ℤ) = (2 : ℤ) ^ Nat.totient q - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow (Nat.totient q) 2 (by norm_num))]
    push_cast; ring
  rw [← hcast]
  exact_mod_cast hnat

/-! ## 4. The AP-modulus datum for the recurrent carry cycle

We now produce the full manuscript AP-modulus datum for the *actual* recurrent
slope of a `CarryFibreCycleData`, combining the proved oddness
(`carryCycle_den_odd`) with the new Mersenne period. -/

/-- A reduced rational strictly between `0` and `1` has denominator `≥ 2`
(its denominator is nonzero and cannot be `1`, else it would be an integer). -/
theorem den_ge_two_of_Ioo {μ : ℚ} (h0 : 0 < μ) (h1 : μ < 1) : 2 ≤ μ.den := by
  rcases Nat.lt_or_ge μ.den 2 with hlt | hge
  · exfalso
    have hdnz : μ.den ≠ 0 := μ.den_nz
    have hd1 : μ.den = 1 := by omega
    have hμ : ((μ.num : ℚ)) = μ := (Rat.den_eq_one_iff μ).mp hd1
    rw [← hμ] at h0 h1
    have hp : 0 < μ.num := by exact_mod_cast h0
    have hq : μ.num < 1 := by exact_mod_cast h1
    omega
  · exact hge

/-- Every recurrent cycle slope has reduced denominator `≥ 2`: the slopes are open
(`0 < μ_i < 1` by E.6), hence non-integral. -/
theorem recurrentSlope_den_ge_two (D : CarryFibreCycleData) (μ : Fin D.n → ℚ)
    (hcast : ∀ i, (μ i : ℝ) = D.slope i) (i : Fin D.n) : 2 ≤ (μ i).den := by
  have hopen := D.slope_open i
  rw [← hcast i] at hopen
  exact den_ge_two_of_Ioo (by exact_mod_cast hopen.1) (by exact_mod_cast hopen.2)

/--
**The recurrent slope's modulus divides a Mersenne period.**

For a recurrent `CarryFibreCycleData` with rational slopes, every cycle slope
`μ_i` has reduced denominator `q_i = (μ_i).den` that is **odd**
(`carryCycle_den_odd`, the 2-adic descent) and **divides the Mersenne period
`2^{φ(q_i)} − 1`** (the new totient argument).  This is the manuscript
`K_Γ ∣ D_Γ = 2^{S_Γ} − 1` for the actual recurrent slope, fully proved. -/
theorem recurrentSlope_den_odd_dvd_mersenne (D : CarryFibreCycleData) (μ : Fin D.n → ℚ)
    (hcast : ∀ i, (μ i : ℝ) = D.slope i) (i : Fin D.n) :
    Odd (μ i).den ∧ (μ i).den ∣ 2 ^ Nat.totient (μ i).den - 1 := by
  have hodd := carryCycle_den_odd D μ hcast i
  exact ⟨hodd, odd_dvd_two_pow_totient_sub_one hodd⟩

/--
**`TowerSlopeAtom` from a recurrent carry-fibre cycle.**

Given a recurrent `CarryFibreCycleData` with rational slopes (`hcast`), a chosen
cycle vertex `i`, and a nonzero target denominator `Q`, this builds the slope atom
with AP modulus `H = (μ_i).den`:

* `Odd H` is `carryCycle_den_odd` (the 2-adic descent), and
* `H ∣ 2^{φ(H)} − 1` (the Mersenne period) follows by
  `odd_dvd_two_pow_totient_sub_one`, so the AP-modulus divisibility is automatic;
* `2 ≤ H` is `recurrentSlope_den_ge_two` (slope openness E.6).

This closes the chain *recurrent cycle → odd denominator → Mersenne period →
Tower slope atom*. -/
def towerSlopeAtomOfRecurrentCycle (D : CarryFibreCycleData) (μ : Fin D.n → ℚ)
    (hcast : ∀ i, (μ i : ℝ) = D.slope i) (i : Fin D.n) (Q : ℕ) (hQ : Q ≠ 0) :
    TowerSlopeAtom where
  Q := Q
  H := (μ i).den
  hQ := hQ
  hH := carryCycle_den_odd D μ hcast i
  hH2 := recurrentSlope_den_ge_two D μ hcast i

/--
**Tower transient factory data from a recurrent carry-fibre cycle.**

The full Phase-7 `TowerTransientFactoryData`, with the carry-fibre recurrent
cycle, the E.13 closure, the Tower budget *and* the AP-modulus datum (Mersenne
period) all discharged; the lone remaining input is the geometric realization of
the cycle datum `(D, μ, hcast)` from the failing-shell carry. -/
def towerOfSlopeOfRecurrentCycle (D : CarryFibreCycleData) (μ : Fin D.n → ℚ)
    (hcast : ∀ i, (μ i : ℝ) = D.slope i) (i : Fin D.n) (Q : ℕ) (hQ : Q ≠ 0)
    {X : ℝ} (hX : 0 ≤ X) :
    TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ X :=
  towerOfSlope (towerSlopeAtomOfRecurrentCycle D μ hcast i Q hQ) hX

/-- **Non-vacuity of the capstone.**  The hand-built `oneCycleExample` (slope
`1/3`, a genuine E.13 fixed point) is a recurrent `CarryFibreCycleData` with
rational slopes; the capstone produces from it a `TowerSlopeAtom` of AP modulus
`H = 3`, with the Mersenne period `3 ∣ 2^{φ(3)} − 1 = 2^2 − 1 = 3` derived. -/
theorem towerSlopeAtomOfRecurrentCycle_nonvacuous :
    ∃ a : TowerSlopeAtom, a.H = 3 := by
  have hden : ((1 : ℚ) / 3).den = 3 := by
    have e : (1 : ℚ) / 3 = ((1 : ℤ) : ℚ) / ((3 : ℤ) : ℚ) := by norm_num
    rw [e]
    have h := Rat.den_div_eq_of_coprime (a := (1 : ℤ)) (b := (3 : ℤ)) (by norm_num)
      (Nat.coprime_one_left _)
    exact_mod_cast h
  refine ⟨towerSlopeAtomOfRecurrentCycle oneCycleExample (fun _ => (1 : ℚ) / 3) ?_
      ⟨0, oneCycleExample.hn⟩ 1 (by norm_num), ?_⟩
  · intro i
    show (((1 : ℚ) / 3 : ℚ) : ℝ) = (1 / 3 : ℝ)
    norm_num
  · show ((1 : ℚ) / 3).den = 3
    exact hden

end

end Erdos260
