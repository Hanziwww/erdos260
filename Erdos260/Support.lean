import Mathlib

/-!
# Supports and dyadic density

This file provides the basic vocabulary for Theorem A in `proof_v2.tex`: binary
digits, the support set, its counting function, and the positive dyadic-density
target.
-/

namespace Erdos260

/-- A natural-valued digit sequence whose values are only `0` and `1`. -/
def BinaryDigits (d : Nat -> Nat) : Prop :=
  forall n, d n = 0 \/ d n = 1

/-- The support of a binary digit sequence. -/
def support (d : Nat -> Nat) : Set Nat :=
  {n | d n = 1}

/-- Support restricted to `[1, X]`, as a finite set. -/
def supportIn (d : Nat -> Nat) (X : Nat) : Finset Nat :=
  (Finset.Icc 1 X).filter fun n => d n = 1

/-- The counting function `A_S(X) = #(S ∩ [1, X])`. -/
def supportCount (d : Nat -> Nat) (X : Nat) : Nat :=
  (supportIn d X).card

/-- The dyadic shell `(X, 2X]` of the support. -/
def supportShell (d : Nat -> Nat) (X : Nat) : Finset Nat :=
  supportIn d (2 * X) \ supportIn d X

/-- The digit sequence is eventually zero. -/
def EventuallyZero (d : Nat -> Nat) : Prop :=
  exists N, forall n, N <= n -> d n = 0

/-- The support is unbounded; for binary digits this is equivalent to not being eventually zero. -/
def Nonterminating (d : Nat -> Nat) : Prop :=
  forall N, exists n, N <= n /\ d n = 1

/-- Positive lower density in every sufficiently large dyadic shell. -/
def PositiveDyadicDensity (d : Nat -> Nat) (c : Rat) : Prop :=
  0 < c /\
    exists X0 : Nat, forall X : Nat, X0 <= X ->
      c * (X : Rat) <= (supportCount d (2 * X) : Rat) - (supportCount d X : Rat)

/-- The same positive dyadic-density target, expressed directly with shell cardinalities. -/
def PositiveDyadicShellDensity (d : Nat -> Nat) (c : Rat) : Prop :=
  0 < c /\
    exists X0 : Nat, forall X : Nat, X0 <= X ->
      c * (X : Rat) <= ((supportShell d X).card : Rat)

@[simp]
theorem mem_supportIn (d : Nat -> Nat) (X n : Nat) :
    n ∈ supportIn d X <-> 1 <= n /\ n <= X /\ d n = 1 := by
  simp [supportIn, and_assoc]

theorem supportIn_subset_Icc (d : Nat -> Nat) (X : Nat) :
    supportIn d X ⊆ Finset.Icc 1 X := by
  intro n hn
  rw [Finset.mem_Icc]
  exact ⟨(mem_supportIn d X n).1 hn |>.1,
    (mem_supportIn d X n).1 hn |>.2.1⟩

theorem supportIn_card_le (d : Nat -> Nat) (X : Nat) :
    (supportIn d X).card <= X := by
  have hsubset := Finset.card_le_card (supportIn_subset_Icc d X)
  have hcard : (Finset.Icc 1 X).card <= X := by
    simp
  exact hsubset.trans hcard

theorem supportCount_mono (d : Nat -> Nat) {X Y : Nat} (hXY : X <= Y) :
    supportCount d X <= supportCount d Y := by
  unfold supportCount
  exact Finset.card_le_card fun n hn => by
    rw [mem_supportIn] at hn
    rw [mem_supportIn]
    exact ⟨hn.1, hXY.trans' hn.2.1, hn.2.2⟩

@[simp]
theorem mem_supportShell (d : Nat -> Nat) (X n : Nat) :
    n ∈ supportShell d X <-> X < n /\ n <= 2 * X /\ d n = 1 := by
  rw [supportShell, Finset.mem_sdiff, mem_supportIn, mem_supportIn]
  constructor
  · intro h
    rcases h with ⟨⟨h1, h2, hd⟩, hnot⟩
    refine ⟨?_, h2, hd⟩
    by_contra hnle
    exact hnot ⟨h1, Nat.le_of_not_gt hnle, hd⟩
  · intro h
    rcases h with ⟨hXn, h2, hd⟩
    have hnpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le X) hXn
    refine ⟨⟨Nat.succ_le_of_lt hnpos, h2, hd⟩, ?_⟩
    intro hx
    exact (Nat.not_le_of_gt hXn) hx.2.1

theorem supportIn_subset_two_mul (d : Nat -> Nat) (X : Nat) :
    supportIn d X ⊆ supportIn d (2 * X) := by
  intro n hn
  rw [mem_supportIn] at hn
  rw [mem_supportIn]
  exact ⟨hn.1, hn.2.1.trans (by omega), hn.2.2⟩

theorem supportShell_subset_supportIn_two_mul (d : Nat -> Nat) (X : Nat) :
    supportShell d X ⊆ supportIn d (2 * X) := by
  intro n hn
  exact (Finset.mem_sdiff.1 hn).1

theorem supportShell_disjoint_supportIn (d : Nat -> Nat) (X : Nat) :
    Disjoint (supportShell d X) (supportIn d X) := by
  rw [Finset.disjoint_left]
  intro n hn hs
  exact (Finset.mem_sdiff.1 hn).2 hs

theorem supportShell_subset_Ioc (d : Nat -> Nat) (X : Nat) :
    supportShell d X ⊆ Finset.Ioc X (2 * X) := by
  intro n hn
  rw [Finset.mem_Ioc]
  have h := (mem_supportShell d X n).1 hn
  exact ⟨h.1, h.2.1⟩

theorem supportShell_card_le_length (d : Nat -> Nat) (X : Nat) :
    (supportShell d X).card <= X := by
  have hsubset := Finset.card_le_card (supportShell_subset_Ioc d X)
  have hcard : (Finset.Ioc X (2 * X)).card <= X := by
    simp
    omega
  exact hsubset.trans hcard

theorem supportShell_card (d : Nat -> Nat) (X : Nat) :
    (supportShell d X).card = supportCount d (2 * X) - supportCount d X := by
  rw [supportShell, supportCount, supportCount]
  exact Finset.card_sdiff_of_subset (supportIn_subset_two_mul d X)

theorem supportCount_two_mul_eq_add_shell (d : Nat -> Nat) (X : Nat) :
    supportCount d (2 * X) = supportCount d X + (supportShell d X).card := by
  have hmono : supportCount d X <= supportCount d (2 * X) :=
    supportCount_mono d (by omega : X <= 2 * X)
  rw [supportShell_card]
  omega

theorem supportCount_add_shell_eq_two_mul (d : Nat -> Nat) (X : Nat) :
    supportCount d X + (supportShell d X).card = supportCount d (2 * X) := by
  rw [supportCount_two_mul_eq_add_shell]

theorem supportShell_card_le_supportCount_two_mul (d : Nat -> Nat) (X : Nat) :
    (supportShell d X).card <= supportCount d (2 * X) := by
  rw [supportShell_card]
  omega

theorem supportShell_disjoint_of_two_mul_le {d : Nat -> Nat} {X Y : Nat}
    (hXY : 2 * X <= Y) :
    Disjoint (supportShell d X) (supportShell d Y) := by
  rw [Finset.disjoint_left]
  intro n hnX hnY
  have hX := (mem_supportShell d X n).1 hnX
  have hY := (mem_supportShell d Y n).1 hnY
  exact Nat.not_lt_of_ge (hX.2.1.trans hXY) hY.1

theorem supportShell_disjoint_two_mul (d : Nat -> Nat) (X : Nat) :
    Disjoint (supportShell d X) (supportShell d (2 * X)) :=
  supportShell_disjoint_of_two_mul_le (d := d) (X := X) (Y := 2 * X) le_rfl

theorem supportShell_card_rat (d : Nat -> Nat) (X : Nat) :
    ((supportShell d X).card : Rat) =
      (supportCount d (2 * X) : Rat) - (supportCount d X : Rat) := by
  rw [supportShell_card]
  exact Nat.cast_sub (supportCount_mono d (by omega : X <= 2 * X))

theorem supportShell_card_real (d : Nat -> Nat) (X : Nat) :
    ((supportShell d X).card : ℝ) =
      (supportCount d (2 * X) : ℝ) - (supportCount d X : ℝ) := by
  rw [supportShell_card]
  exact Nat.cast_sub (supportCount_mono d (by omega : X <= 2 * X))

theorem positiveDyadicDensity_iff_shell (d : Nat -> Nat) (c : Rat) :
    PositiveDyadicDensity d c <-> PositiveDyadicShellDensity d c := by
  constructor
  · intro h
    rcases h with ⟨hc, X0, hX0⟩
    refine ⟨hc, X0, ?_⟩
    intro X hX
    rw [supportShell_card_rat]
    exact hX0 X hX
  · intro h
    rcases h with ⟨hc, X0, hX0⟩
    refine ⟨hc, X0, ?_⟩
    intro X hX
    have hshell := hX0 X hX
    rwa [supportShell_card_rat] at hshell

theorem not_eventuallyZero_iff_nonterminating {d : Nat -> Nat} (hd : BinaryDigits d) :
    (Not (EventuallyZero d)) <-> Nonterminating d := by
  constructor
  · intro hnot N
    by_contra hN
    apply hnot
    refine ⟨N, ?_⟩
    intro n hn
    rcases hd n with hzero | hone
    · exact hzero
    · exact False.elim (hN ⟨n, hn, hone⟩)
  · intro hnon hzero
    rcases hzero with ⟨N, hN⟩
    rcases hnon N with ⟨n, hn, hone⟩
    rw [hN n hn] at hone
    contradiction

end Erdos260
