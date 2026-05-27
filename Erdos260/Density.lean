import Mathlib
import Erdos260.RealCarry
import Erdos260.Support

/-!
# Dyadic density interfaces

This file records the explicit, no-asymptotic statement of Theorem A from
`proof_v2.tex`.  It is an interface proposition, not an assumed theorem.
-/

namespace Erdos260

noncomputable section

/-- Natural binary digits, viewed as real-valued digits. -/
def natBinaryAsReal (d : Nat -> Nat) : Nat -> ℝ :=
  fun n => (d n : ℝ)

/-- A positive natural number of the form `2^L`. -/
def Dyadic (X : Nat) : Prop :=
  ∃ L : Nat, X = 2 ^ L

/--
Positive linear lower density on all sufficiently large dyadic shells, with all
constants explicit.
-/
def PositiveDyadicShellDensityReal (d : Nat -> Nat) (c : ℝ) : Prop :=
  0 < c ∧
    ∃ X0 : Nat, ∀ X : Nat, Dyadic X -> X0 <= X ->
      c * (X : ℝ) <= ((supportShell d X).card : ℝ)

/--
The exact Theorem A interface used to bridge the manuscript to the final
Erdős 260 target.  This is deliberately a `Prop`, so no local estimate is
treated as a proved dependency while the remaining proof is being formalized.
-/
def TheoremAStatement : Prop :=
  ∀ (Q : Nat) (d : Nat -> Nat),
    0 < Q ->
      BinaryDigits d ->
      ¬ EventuallyZero d ->
      (∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) ->
      ∃ c : ℝ, PositiveDyadicShellDensityReal d c

theorem natBinaryAsReal_digits {d : Nat -> Nat} (hd : BinaryDigits d) :
    RealBinaryDigits (natBinaryAsReal d) := by
  intro n
  rcases hd n with h | h <;> simp [natBinaryAsReal, h]

theorem dyadic_pos {X : Nat} (hX : Dyadic X) :
    0 < X := by
  rcases hX with ⟨L, rfl⟩
  positivity

theorem dyadic_one : Dyadic 1 := by
  exact ⟨0, by simp⟩

theorem dyadic_pow_two (L : Nat) : Dyadic (2 ^ L) :=
  ⟨L, rfl⟩

theorem dyadic_two_mul {X : Nat} (hX : Dyadic X) :
    Dyadic (2 * X) := by
  rcases hX with ⟨L, rfl⟩
  refine ⟨L + 1, ?_⟩
  rw [pow_succ]
  omega

theorem dyadic_mul_two {X : Nat} (hX : Dyadic X) :
    Dyadic (X * 2) := by
  simpa [Nat.mul_comm] using dyadic_two_mul hX

theorem dyadic_monotone_pow {L : Nat} :
    L <= 2 ^ L :=
  Nat.le_of_lt Nat.lt_two_pow_self

theorem positiveDyadicShellDensityReal_pos {d : Nat -> Nat} {c : ℝ}
    (h : PositiveDyadicShellDensityReal d c) :
    0 < c :=
  h.1

theorem positiveDyadicShellDensityReal_eventual {d : Nat -> Nat} {c : ℝ}
    (h : PositiveDyadicShellDensityReal d c) :
    ∃ X0 : Nat, ∀ X : Nat, Dyadic X -> X0 <= X ->
      c * (X : ℝ) <= ((supportShell d X).card : ℝ) :=
  h.2

theorem PositiveDyadicShellDensityReal.eventually_nonempty
    {d : Nat -> Nat} {c : ℝ}
    (h : PositiveDyadicShellDensityReal d c) :
    ∃ X0 : Nat, ∀ X : Nat, Dyadic X -> X0 <= X ->
      (supportShell d X).Nonempty := by
  rcases h with ⟨hc, X0, hX0⟩
  refine ⟨X0, ?_⟩
  intro X hX hlarge
  have hXposNat : 0 < X := dyadic_pos hX
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast hXposNat
  have hprod : 0 < c * (X : ℝ) := mul_pos hc hXpos
  have hcard : 0 < ((supportShell d X).card : ℝ) :=
    hprod.trans_le (hX0 X hX hlarge)
  have hcardNat : 0 < (supportShell d X).card := by
    exact_mod_cast hcard
  exact Finset.card_pos.1 hcardNat

theorem PositiveDyadicShellDensityReal.mono_const
    {d : Nat -> Nat} {c c' : ℝ}
    (h : PositiveDyadicShellDensityReal d c) (hc' : 0 < c') (hle : c' <= c) :
    PositiveDyadicShellDensityReal d c' := by
  rcases h with ⟨hc, X0, hX0⟩
  refine ⟨hc', X0, ?_⟩
  intro X hX hlarge
  have hXnonneg : 0 <= (X : ℝ) := by positivity
  have hleX : c' * (X : ℝ) <= c * (X : ℝ) :=
    mul_le_mul_of_nonneg_right hle hXnonneg
  exact hleX.trans (hX0 X hX hlarge)

theorem PositiveDyadicShellDensityReal.half_const
    {d : Nat -> Nat} {c : ℝ}
    (h : PositiveDyadicShellDensityReal d c) :
    PositiveDyadicShellDensityReal d (c / 2) := by
  have hhalf : 0 < c / 2 := by linarith [h.1]
  have hle : c / 2 <= c := by linarith [h.1]
  exact h.mono_const hhalf hle

theorem positiveDyadicShellDensityReal_of_rat
    {d : Nat -> Nat} {c : Rat}
    (h : PositiveDyadicShellDensity d c) :
    PositiveDyadicShellDensityReal d (c : ℝ) := by
  rcases h with ⟨hc, X0, hX0⟩
  refine ⟨by exact_mod_cast hc, X0, ?_⟩
  intro X _ hlarge
  have hrat := hX0 X hlarge
  have hreal :
      (((c * (X : Rat)) : Rat) : ℝ) <=
        ((((supportShell d X).card : Rat) : Rat) : ℝ) := by
    exact_mod_cast hrat
  simpa using hreal

theorem positiveDyadicShellDensityReal_not_eventually_lt {d : Nat -> Nat} {c : ℝ}
    (hdens : PositiveDyadicShellDensityReal d c)
    (hupper : ∀ᶠ X : Nat in Filter.atTop,
      ((supportShell d X).card : ℝ) < c * (X : ℝ)) :
    False := by
  rcases hdens with ⟨hc, X0, hdens⟩
  rcases Filter.eventually_atTop.1 hupper with ⟨X1, hX1⟩
  let M := max X0 X1
  let X := 2 ^ M
  have hMX : M <= X := Nat.le_of_lt Nat.lt_two_pow_self
  have hX0le : X0 <= X := (le_max_left X0 X1).trans hMX
  have hX1le : X1 <= X := (le_max_right X0 X1).trans hMX
  have hlower : c * (X : ℝ) <= ((supportShell d X).card : ℝ) :=
    hdens X ⟨M, rfl⟩ hX0le
  have hlt : ((supportShell d X).card : ℝ) < c * (X : ℝ) :=
    hX1 X hX1le
  linarith

theorem positiveDyadicShellDensityReal_not_eventually_pow_lt {d : Nat -> Nat} {c : ℝ}
    (hdens : PositiveDyadicShellDensityReal d c)
    (hupper : ∀ᶠ L : Nat in Filter.atTop,
      ((supportShell d (2 ^ L)).card : ℝ) < c * ((2 ^ L : Nat) : ℝ)) :
    False := by
  rcases hdens with ⟨hc, X0, hdens⟩
  rcases Filter.eventually_atTop.1 hupper with ⟨L1, hL1⟩
  let L := max L1 X0
  have hX0le : X0 <= 2 ^ L := by
    have hXL : L <= 2 ^ L := Nat.le_of_lt Nat.lt_two_pow_self
    exact (le_max_right L1 X0).trans hXL
  have hL1le : L1 <= L := le_max_left L1 X0
  have hlower : c * ((2 ^ L : Nat) : ℝ) <= ((supportShell d (2 ^ L)).card : ℝ) :=
    hdens (2 ^ L) ⟨L, rfl⟩ hX0le
  have hlt : ((supportShell d (2 ^ L)).card : ℝ) < c * ((2 ^ L : Nat) : ℝ) :=
    hL1 L hL1le
  linarith

/-- A dyadic shell support is sublinear along powers of two, with all constants explicit. -/
def DyadicShellSublinearReal (d : Nat -> Nat) : Prop :=
  ∀ eps : ℝ, 0 < eps ->
    ∀ᶠ L : Nat in Filter.atTop,
      ((supportShell d (2 ^ L)).card : ℝ) < eps * ((2 ^ L : Nat) : ℝ)

theorem PositiveDyadicShellDensityReal.not_sublinear
    {d : Nat -> Nat} {c : ℝ}
    (hdens : PositiveDyadicShellDensityReal d c)
    (hsub : DyadicShellSublinearReal d) :
    False := by
  exact positiveDyadicShellDensityReal_not_eventually_pow_lt hdens
    (hsub c hdens.1)

theorem positiveDyadicShellDensityReal_not_sublinear
    {d : Nat -> Nat}
    (hdens : ∃ c : ℝ, PositiveDyadicShellDensityReal d c)
    (hsub : DyadicShellSublinearReal d) :
    False := by
  rcases hdens with ⟨c, hc⟩
  exact hc.not_sublinear hsub

theorem dyadicShellSublinearReal_of_eventual_bound
    {d : Nat -> Nat}
    (h :
      ∀ eps : ℝ, 0 < eps ->
        ∀ᶠ L : Nat in Filter.atTop,
          ((supportShell d (2 ^ L)).card : ℝ) <
            eps * ((2 ^ L : Nat) : ℝ)) :
    DyadicShellSublinearReal d :=
  h

theorem theoremA_contradicts_sublinear_rational_digit
    (hA : TheoremAStatement) {Q : Nat} {d : Nat -> Nat}
    (hQ : 0 < Q) (hd : BinaryDigits d) (hnot : ¬ EventuallyZero d)
    (hvalue :
      ∃ P : Int, realWeightedValue (natBinaryAsReal d) =
        (P : ℝ) / (Q : ℝ))
    (hsub : DyadicShellSublinearReal d) :
    False := by
  have hdens : ∃ c : ℝ, PositiveDyadicShellDensityReal d c :=
    hA Q d hQ hd hnot hvalue
  exact positiveDyadicShellDensityReal_not_sublinear hdens hsub

end

end Erdos260
