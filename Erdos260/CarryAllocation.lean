import Mathlib
import Erdos260.CarryDataFactory
import Erdos260.Constants

/-!
# Numerical allocation `hAlloc` (manuscript K.4 step)

This file proves the K.4 numerical allocation inequality

  `cPr · X · (r + 1) + K · Y + K · T + (r + 1)² · (L + B + 1) ≤ (r + 1) · X`

required by `CarryDataFromFailure` from the failure hypothesis
`shell.hfailure : (K : ℝ) < cQ · X` and a sufficiently-large dyadic `X`.

This file retains the rigorous, parameter-generic ingredients:

1. **`hAlloc_from_kBound`**: parametric algebra — given any cPr, cQ, K, X, r,
   Y, T, L, B with `K ≤ cQ · X` and the dominate inequality
   `cPr · X · (r + 1) + cQ · X · (Y + T) + (r + 1)² · (L + B + 1) ≤
     (r + 1) · X`, derive the `K`-form. This is a 4-line linear-arithmetic
   reduction.

2. **Polynomial-vs-exponential growth lemmas**
   (`eight_mul_add_four_le_two_pow`, `four_mul_LB1_le_two_pow`,
   `manuscript_carry_growth`): the elementary `Nat` bounds that feed the
   dominate inequalities and the carry threshold `carryLogThreshold`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ### Polynomial vs exponential growth lemmas -/

/--
`8 L + 4 ≤ 2 ^ L` for `L ≥ 6`.

Base case `L = 6`: `52 ≤ 64`.
Inductive step uses `2 ^ (n+1) = 2 · 2^n` and linear arithmetic with
`n ≥ 6` (to ensure `8(n+1)+4 ≤ 2(8n+4)`).
-/
theorem eight_mul_add_four_le_two_pow {L : Nat} (h : 6 ≤ L) :
    8 * L + 4 ≤ 2 ^ L := by
  induction L with
  | zero => omega
  | succ n ih =>
    by_cases hn : 6 ≤ n
    · have h_ih := ih hn
      have h_pow_succ : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      rw [h_pow_succ]
      linarith
    · have h_eq : n + 1 = 6 := by omega
      rw [h_eq]
      decide

/--
`4 · (L + B + 1) ≤ 2 ^ L` for `L ≥ B + 6`.  Combines
`eight_mul_add_four_le_two_pow` with `4(L+B+1) ≤ 8L+4` (which needs `B ≤ L`).
-/
theorem four_mul_LB1_le_two_pow {L B : Nat} (h : B + 6 ≤ L) :
    4 * (L + B + 1) ≤ 2 ^ L := by
  have h_6 : 6 ≤ L := by omega
  have h_8L := eight_mul_add_four_le_two_pow h_6
  omega

/-! ### `hAlloc` real-valued reductions -/

/--
**Step 1**: parametric hAlloc from `K ≤ cQ · X` and the dominate
inequality (where `K` has been replaced by `cQ · X` in the `Y` and `T`
terms).
-/
theorem hAlloc_from_kBound
    {X K L B r : Nat} {T Y cPr cQ : ℝ}
    (hY_nn : 0 ≤ Y) (hT_nn : 0 ≤ T)
    (hK_le : (K : ℝ) ≤ cQ * (X : ℝ))
    (h_dominate :
        cPr * (X : ℝ) * ((r : ℝ) + 1) +
          cQ * (X : ℝ) * (Y + T) +
          ((r : ℝ) + 1) ^ 2 * ((L : ℝ) + (B : ℝ) + 1) ≤
        ((r : ℝ) + 1) * (X : ℝ)) :
    cPr * (X : ℝ) * ((r : ℝ) + 1) + (K : ℝ) * Y + (K : ℝ) * T +
        ((r : ℝ) + 1) ^ 2 * ((L : ℝ) + (B : ℝ) + 1) ≤
      ((r : ℝ) + 1) * (X : ℝ) := by
  have hKY : (K : ℝ) * Y ≤ cQ * (X : ℝ) * Y :=
    mul_le_mul_of_nonneg_right hK_le hY_nn
  have hKT : (K : ℝ) * T ≤ cQ * (X : ℝ) * T :=
    mul_le_mul_of_nonneg_right hK_le hT_nn
  have h_split : cQ * (X : ℝ) * (Y + T) =
      cQ * (X : ℝ) * Y + cQ * (X : ℝ) * T := by ring
  linarith

/--
Budgeted form of the K.4 dominate inequality.

The proof-v4 carry pressure argument pays the pressure term with half of
`(r+1)X`, then separately budgets the threshold contribution and the boundary
gap-error contribution by one quarter each.
-/
theorem hDominate_from_threshold_and_error_budget
    {X L B r : Nat} {T Y cPr c0 : ℝ}
    (hcPr : cPr ≤ (1 / 2 : ℝ))
    (hThreshold :
      c0 * (X : ℝ) * (Y + T) ≤ ((r : ℝ) + 1) * (X : ℝ) / 4)
    (hError :
      ((r : ℝ) + 1) ^ 2 * ((L : ℝ) + (B : ℝ) + 1) ≤
        ((r : ℝ) + 1) * (X : ℝ) / 4) :
    cPr * (X : ℝ) * ((r : ℝ) + 1) +
        c0 * (X : ℝ) * (Y + T) +
        ((r : ℝ) + 1) ^ 2 * ((L : ℝ) + (B : ℝ) + 1) ≤
      ((r : ℝ) + 1) * (X : ℝ) := by
  have hX_nonneg : (0 : ℝ) ≤ X := by exact_mod_cast Nat.zero_le X
  have hr_nonneg : (0 : ℝ) ≤ (r : ℝ) + 1 := by positivity
  have hPressure :
      cPr * (X : ℝ) * ((r : ℝ) + 1) ≤
        ((r : ℝ) + 1) * (X : ℝ) / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hcPr
      (mul_nonneg hX_nonneg hr_nonneg)]
  linarith

/-! ### Carry threshold -/

/--
The dyadic-log threshold required for `hAlloc` at the pinned manuscript
choice (`r = 1, Y = T = 0`): `L ≥ B + 6` is enough.

For downstream consumers the corresponding cardinal threshold is
`2 ^ carryLogThreshold B`.
-/
def carryLogThreshold (B : Nat) : Nat := B + 6

/-- The cardinal carry threshold: `2 ^ (B + 6)`. -/
def carryThreshold (B : Nat) : Nat := 2 ^ carryLogThreshold B

/-! ### Polynomial growth bound for the manuscript-strict carry choice

The manuscript-strict carry allocation (`r = L`, `Y = ε · L`, `T = 2 L + C_Q`)
reduces to a polynomial-vs-exponential inequality.  We keep the loose
sufficient condition `1024 · (L + 1)³ + 8 · (L + 1)² · B ≤ 2^L`, decoupled from
the carry algebra, as a reusable arithmetic lemma.
-/

/--
Polynomial vs exponential helper for the manuscript-strict carry allocation.

The exact growth condition needed: for `L ≥ B + 16`,
`1024 · (L + 1)³ + 8 · (L + 1)² · B ≤ 2^L`.

Proof by induction on L from a base `L = B + 16`; the inductive step uses
`(n + 2)³ ≤ 2 · (n + 1)³` (true for `n ≥ 3`) and standard pow_succ.
-/
theorem manuscript_carry_growth (L B : Nat) (hL : B + 25 ≤ L) :
    1024 * (L + 1) ^ 3 + 8 * (L + 1) ^ 2 * B ≤ 2 ^ L := by
  have hBL : B ≤ L := by omega
  suffices h : 1024 * (L + 1) ^ 3 + 8 * (L + 1) ^ 2 * L ≤ 2 ^ L by
    have h_mono : 8 * (L + 1) ^ 2 * B ≤ 8 * (L + 1) ^ 2 * L :=
      Nat.mul_le_mul_left _ hBL
    omega
  have hL_25 : 25 ≤ L := by omega
  suffices h : 1032 * (L + 1) ^ 3 ≤ 2 ^ L by
    have h_step : 8 * (L + 1) ^ 2 * L ≤ 8 * (L + 1) ^ 3 := by
      have hL_le : L ≤ L + 1 := Nat.le_succ _
      have : 8 * (L + 1) ^ 2 * L ≤ 8 * (L + 1) ^ 2 * (L + 1) := by
        exact Nat.mul_le_mul_left _ hL_le
      have h_eq : 8 * (L + 1) ^ 2 * (L + 1) = 8 * (L + 1) ^ 3 := by ring
      omega
    omega
  clear hL hBL
  induction L, hL_25 using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h_cube : (n + 2) ^ 3 ≤ 2 * (n + 1) ^ 3 := by
      have hn3 : 3 ≤ n := by omega
      nlinarith [sq_nonneg (n - 3 : ℤ), sq_nonneg ((n : ℤ) - 4)]
    have h_pow_succ : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    calc 1032 * (n + 1 + 1) ^ 3
        = 1032 * (n + 2) ^ 3 := by ring_nf
      _ ≤ 1032 * (2 * (n + 1) ^ 3) := by
            exact Nat.mul_le_mul_left _ h_cube
      _ = 2 * (1032 * (n + 1) ^ 3) := by ring
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (n + 1) := by rw [h_pow_succ]

/--
Boundary gap-error budget from polynomial-vs-exponential growth.

If the carry order is at most the dyadic exponent (`r <= L`) and `L` is beyond
the carry denominator threshold `B + 25`, then the error term
`(r+1)^2(L+B+1)` is paid by one quarter of `(r+1)X`.
-/
theorem hErrorBudget_from_carry_growth
    {X L B r : Nat}
    (hX : X = 2 ^ L)
    (hr : r <= L)
    (hL : B + 25 <= L) :
    ((r : ℝ) + 1) ^ 2 * ((L : ℝ) + (B : ℝ) + 1) <=
      ((r : ℝ) + 1) * (X : ℝ) / 4 := by
  have hg := manuscript_carry_growth L B hL
  have hpoly : 4 * (r + 1) * (L + B + 1) <=
      1024 * (L + 1) ^ 3 + 8 * (L + 1) ^ 2 * B := by
    nlinarith [sq_nonneg (L + 1 : Nat), Nat.succ_le_succ hr]
  have h4_le_pow : 4 * (r + 1) * (L + B + 1) <= 2 ^ L := hpoly.trans hg
  have h4_le_X_nat : 4 * (r + 1) * (L + B + 1) <= X := by
    rw [hX]
    exact h4_le_pow
  have h4_le_X :
      (4 : ℝ) * ((r : ℝ) + 1) * ((L : ℝ) + (B : ℝ) + 1) <= (X : ℝ) := by
    exact_mod_cast h4_le_X_nat
  have hsmall :
      ((r : ℝ) + 1) * ((L : ℝ) + (B : ℝ) + 1) <= (X : ℝ) / 4 := by
    nlinarith
  have hr_nonneg : 0 <= (r : ℝ) + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsmall hr_nonneg
  nlinarith

/--
Threshold budget from the K.4 smallness `c₀ << κ`.

If `c₀ <= κ / 16`, the active threshold range has `Y + T <= 4L`, and
the chosen order satisfies `κL <= r+1`, then the threshold contribution is
paid by one quarter of `(r+1)X`.
-/
theorem hThresholdBudget_from_kappa_floor
    {X L r : Nat} {Y T c0 kappa : ℝ}
    (hkappa_nonneg : 0 <= kappa)
    (hc0_small : c0 <= kappa / 16)
    (hYT_nonneg : 0 <= Y + T)
    (hYT : Y + T <= 4 * (L : ℝ))
    (hOrder : kappa * (L : ℝ) <= (r : ℝ) + 1) :
    c0 * (X : ℝ) * (Y + T) <= ((r : ℝ) + 1) * (X : ℝ) / 4 := by
  have hX_nonneg : (0 : ℝ) <= X := by exact_mod_cast Nat.zero_le X
  have hkdiv_nonneg : 0 <= kappa / 16 := by nlinarith
  have hmul1 : c0 * (Y + T) <= (kappa / 16) * (4 * (L : ℝ)) := by
    exact mul_le_mul hc0_small hYT hYT_nonneg hkdiv_nonneg
  have hmul2 : c0 * (Y + T) <= ((r : ℝ) + 1) / 4 := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hmul2 hX_nonneg]

end

end Erdos260
