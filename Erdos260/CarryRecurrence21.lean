import Mathlib

/-!
# The carry recurrence (§21.1) of the Erdős-#260 manuscript

This file formalizes, from scratch over an arbitrary digit sequence, the *integral carry*
that opens §21 ("Carry recurrence and positive-density pressure") of
`proof_v4_repaired_core_v71_p2_preprint_hygiene.tex`.

The manuscript object is
`R_N = Q · 2^N · (η − ∑_{n ≤ N} n·d_n / 2^n)` with `η = P/Q`, satisfying

* (21.1)  `R_{N+1} = 2·R_N − Q·(N+1)·d_{N+1}`,
* (21.2)  `0 ≤ R_N ≤ Q·(N+2)`.

Because `η` is rational, the genuine state lives in `ℤ`: with `R_0 = P` an integer, the whole
sequence is integral.  We therefore *define* the carry by the integer recurrence (21.1) over a
digit sequence `d : ℕ → ℤ` and parameters `P₀ Q : ℤ`, and prove:

1. `carry_succ` — the recurrence (21.1), true by definition.
2. `carry_closed_form` — the telescoped integer closed form
   `R_N + Q·∑_{i ≤ N} i·d_i·2^{N-i} = 2^N·R_0`, equivalently the manuscript's
   carry-clean iteration identity (Remark "Carry-clean complete returns").
   `carry_div_eq` re-expresses this over `ℚ` as `R_N/Q = 2^N·η − ∑ i·d_i·2^{N-i}`,
   the literal §21 formula with `η = P₀/Q`.
3. `carry_fract_doubling` — the **digit-independence** fact: over `ℚ` the quotient
   `R_N / Q` advances by *pure doubling up to an integer*, so its fractional part
   `{R_N/Q}` carries **no** information about the digits.  This was the crux of a real
   bug in an earlier manuscript draft (`(R_n/Q) mod 1` is gap-blind), so it is isolated
   here as a fact future work must AVOID misusing.
4. `greedyCarry_bounds` / `carry_greedy_bounds` — the boundedness invariant (21.2)
   `0 ≤ R_N ≤ Q·(N+2)`, proved by induction for the genuine carry of a valid digit
   sequence, i.e. the greedy digit choice `d_{N+1} = 1 ↔ Q(N+1) ≤ 2 R_N` that keeps the
   carry inside its window.  The greedy digits are `0/1` (`greedyDigit_mem`) and the
   greedy carry is an instance of the general recurrence (`greedyCarry_eq_carry`).
-/

namespace Erdos260.CarryRecurrence21

/-! ## 1. Definition and the recurrence (21.1) -/

/-- The integral carry `R_N` of §21, defined over an arbitrary digit sequence `d`
with initial value `R_0 = P₀` (intended `P₀ = P`, the numerator of `η = P/Q`).
The recurrence is the boxed identity (21.1)
`R_{N+1} = 2·R_N − Q·(N+1)·d_{N+1}`. -/
def carry (P₀ Q : ℤ) (d : ℕ → ℤ) : ℕ → ℤ
  | 0 => P₀
  | (N + 1) => 2 * carry P₀ Q d N - Q * ((N : ℤ) + 1) * d (N + 1)

@[simp] theorem carry_zero (P₀ Q : ℤ) (d : ℕ → ℤ) : carry P₀ Q d 0 = P₀ := rfl

/-- **The carry recurrence (21.1)**, true by definition. -/
theorem carry_succ (P₀ Q : ℤ) (d : ℕ → ℤ) (N : ℕ) :
    carry P₀ Q d (N + 1) = 2 * carry P₀ Q d N - Q * ((N : ℤ) + 1) * d (N + 1) := rfl

/-! ## 2. Closed form (telescoped integer identity) -/

/-- The telescoped digit sum `∑_{i ≤ N} i·d_i·2^{N-i}` appearing in the closed form.
(The `i = 0` term vanishes, so the range may start at `0`.) -/
def carrySum (d : ℕ → ℤ) (N : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (N + 1), (i : ℤ) * d i * 2 ^ (N - i)

theorem carrySum_succ (d : ℕ → ℤ) (N : ℕ) :
    carrySum d (N + 1) = 2 * carrySum d N + ((N : ℤ) + 1) * d (N + 1) := by
  unfold carrySum
  rw [Finset.sum_range_succ]
  have key : (∑ i ∈ Finset.range (N + 1), (i : ℤ) * d i * 2 ^ (N + 1 - i))
      = 2 * ∑ i ∈ Finset.range (N + 1), (i : ℤ) * d i * 2 ^ (N - i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have hsub : N + 1 - i = (N - i) + 1 := by omega
    rw [hsub, pow_succ]
    ring
  rw [key]
  simp only [Nat.sub_self, pow_zero, mul_one]
  push_cast
  ring

/-- **Telescoped closed form.** `R_N + Q·∑_{i ≤ N} i·d_i·2^{N-i} = 2^N·R_0`.
Equivalently `R_N = 2^N·R_0 − Q·∑ i·d_i·2^{N-i}`, the integer form of the manuscript's
carry-clean iteration `R_z = 2^{z-x}R_x − Q ∑ 2^{z-x-i}(x+i)d_{x+i}` (taken from `x = 0`). -/
theorem carry_closed_form (P₀ Q : ℤ) (d : ℕ → ℤ) (N : ℕ) :
    carry P₀ Q d N + Q * carrySum d N = 2 ^ N * P₀ := by
  induction N with
  | zero => simp [carry, carrySum]
  | succ N ih =>
      rw [carry_succ, carrySum_succ]
      linear_combination 2 * ih

/-- **Rational closed form (the literal §21 formula).** With `η = P₀/Q`,
`R_N / Q = 2^N·η − ∑_{i ≤ N} i·d_i·2^{N-i}`, i.e.
`R_N/(Q·2^N) = η − ∑_{i ≤ N} i·d_i/2^i`. -/
theorem carry_div_eq (P₀ Q : ℤ) (d : ℕ → ℤ) (hQ : Q ≠ 0) (N : ℕ) :
    (carry P₀ Q d N : ℚ) / (Q : ℚ)
      = (2 : ℚ) ^ N * ((P₀ : ℚ) / (Q : ℚ)) - (carrySum d N : ℚ) := by
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ
  have hcast : (carry P₀ Q d N : ℚ) + (Q : ℚ) * (carrySum d N : ℚ)
      = (2 : ℚ) ^ N * (P₀ : ℚ) := by
    exact_mod_cast carry_closed_form P₀ Q d N
  field_simp
  linear_combination hcast

/-! ## 3. Digit-independence: the fractional part of `R_N/Q` doubles -/

/-- **Digit-independence (the gap-blind fact).** Over `ℚ`, the quotient `R_N / Q` evolves by
pure doubling up to an integer: there is `m : ℤ` (namely `(N+1)·d_{N+1}`) with
`R_{N+1}/Q = 2·(R_N/Q) − m`.  Hence the fractional part `{R_N/Q}` simply doubles and is
**independent of the digit** `d_{N+1}`: the subtracted term `Q·(N+1)·d_{N+1}` is an integer
multiple of `Q`, so it disappears modulo `1`.  Consequently `{R_N/Q}` carries no information
about the digit sequence — the bug an earlier draft made by reading digits off this orbit. -/
theorem carry_fract_doubling (P₀ Q : ℤ) (d : ℕ → ℤ) (hQ : Q ≠ 0) (N : ℕ) :
    ∃ m : ℤ, (carry P₀ Q d (N + 1) : ℚ) / (Q : ℚ)
      = 2 * ((carry P₀ Q d N : ℚ) / (Q : ℚ)) - (m : ℚ) := by
  refine ⟨((N : ℤ) + 1) * d (N + 1), ?_⟩
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ
  have hrec : (carry P₀ Q d (N + 1) : ℚ)
      = 2 * (carry P₀ Q d N : ℚ) - (Q : ℚ) * (((N : ℤ) + 1) * d (N + 1) : ℤ) := by
    rw [carry_succ]; push_cast; ring
  rw [hrec]
  field_simp

/-! ## 4. Boundedness (21.2) for the genuine (greedy) carry -/

/-- The genuine carry of a *valid* digit sequence: at each step the digit is chosen greedily,
`d_{N+1} = 1` exactly when `Q·(N+1) ≤ 2·R_N`, which keeps the carry inside the window
`[0, Q·(N+2)]`.  Defined directly by the recurrence; `greedyCarry_eq_carry` identifies it with
`carry P₀ Q (greedyDigit P₀ Q)`. -/
def greedyCarry (P₀ Q : ℤ) : ℕ → ℤ
  | 0 => P₀
  | (N + 1) =>
      if Q * ((N : ℤ) + 1) ≤ 2 * greedyCarry P₀ Q N
      then 2 * greedyCarry P₀ Q N - Q * ((N : ℤ) + 1)
      else 2 * greedyCarry P₀ Q N

/-- The greedy digit sequence: `d_{N+1} = 1 ↔ Q·(N+1) ≤ 2·R_N`, else `0` (and `d_0 = 0`). -/
def greedyDigit (P₀ Q : ℤ) : ℕ → ℤ
  | 0 => 0
  | (N + 1) => if Q * ((N : ℤ) + 1) ≤ 2 * greedyCarry P₀ Q N then 1 else 0

theorem greedyCarry_succ_eq (P₀ Q : ℤ) (N : ℕ) :
    greedyCarry P₀ Q (N + 1) =
      if Q * ((N : ℤ) + 1) ≤ 2 * greedyCarry P₀ Q N
      then 2 * greedyCarry P₀ Q N - Q * ((N : ℤ) + 1)
      else 2 * greedyCarry P₀ Q N := rfl

theorem greedyDigit_succ_eq (P₀ Q : ℤ) (N : ℕ) :
    greedyDigit P₀ Q (N + 1) =
      if Q * ((N : ℤ) + 1) ≤ 2 * greedyCarry P₀ Q N then 1 else 0 := rfl

/-- The greedy digits are genuine binary digits. -/
theorem greedyDigit_mem (P₀ Q : ℤ) (k : ℕ) :
    greedyDigit P₀ Q k = 0 ∨ greedyDigit P₀ Q k = 1 := by
  cases k with
  | zero => exact Or.inl rfl
  | succ N => rw [greedyDigit_succ_eq]; split_ifs <;> simp

/-- The greedy carry obeys the recurrence (21.1) with the greedy digit. -/
theorem greedyCarry_succ (P₀ Q : ℤ) (N : ℕ) :
    greedyCarry P₀ Q (N + 1)
      = 2 * greedyCarry P₀ Q N - Q * ((N : ℤ) + 1) * greedyDigit P₀ Q (N + 1) := by
  rw [greedyCarry_succ_eq, greedyDigit_succ_eq]
  split_ifs with h <;> ring

/-- The greedy carry is the general carry fed the greedy digits. -/
theorem greedyCarry_eq_carry (P₀ Q : ℤ) (N : ℕ) :
    greedyCarry P₀ Q N = carry P₀ Q (greedyDigit P₀ Q) N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [greedyCarry_succ, ih, ← carry_succ]

/-- **Boundedness invariant (21.2).** For the genuine (greedy) carry with valid initial datum
`0 ≤ R_0 ≤ 2Q` (i.e. `0 ≤ P₀ ≤ Q·(0+2)`) and `Q > 0`, the carry stays in its window:
`0 ≤ R_N ≤ Q·(N+2)` for every `N`. -/
theorem greedyCarry_bounds (P₀ Q : ℤ) (hQ : 0 < Q) (h0 : 0 ≤ P₀) (h2 : P₀ ≤ Q * 2) (N : ℕ) :
    0 ≤ greedyCarry P₀ Q N ∧ greedyCarry P₀ Q N ≤ Q * ((N : ℤ) + 2) := by
  induction N with
  | zero =>
      have hz : greedyCarry P₀ Q 0 = P₀ := rfl
      refine ⟨by rw [hz]; exact h0, ?_⟩
      rw [hz]; push_cast; linarith [h2]
  | succ N ih =>
      obtain ⟨ihlo, ihhi⟩ := ih
      rw [greedyCarry_succ_eq]
      push_cast
      split_ifs with h
      · exact ⟨by linarith, by nlinarith [ihhi]⟩
      · exact ⟨by linarith, by nlinarith [ihhi, hQ, h]⟩

/-- The genuine carry (21.2) bound, transported onto the general `carry` of the greedy digits. -/
theorem carry_greedy_bounds (P₀ Q : ℤ) (hQ : 0 < Q) (h0 : 0 ≤ P₀) (h2 : P₀ ≤ Q * 2) (N : ℕ) :
    0 ≤ carry P₀ Q (greedyDigit P₀ Q) N
      ∧ carry P₀ Q (greedyDigit P₀ Q) N ≤ Q * ((N : ℤ) + 2) := by
  rw [← greedyCarry_eq_carry]
  exact greedyCarry_bounds P₀ Q hQ h0 h2 N

end Erdos260.CarryRecurrence21
