import Mathlib
import Erdos260.Gap

/-!
# Adjacent support gaps

This file connects the zero-gap carry bounds to actual adjacent hits of the
binary support.
-/

namespace Erdos260

noncomputable section

open scoped Topology

/-- Two support positions with no support point strictly between them. -/
def AdjacentHits (d : Nat -> Nat) (a b : Nat) : Prop :=
  a < b ∧ d a = 1 ∧ d b = 1 ∧ ∀ j : Nat, a < j -> j < b -> d j = 0

theorem AdjacentHits.lt {d : Nat -> Nat} {a b : Nat} (h : AdjacentHits d a b) :
    a < b := h.1

theorem AdjacentHits.left_hit {d : Nat -> Nat} {a b : Nat} (h : AdjacentHits d a b) :
    d a = 1 := h.2.1

theorem AdjacentHits.right_hit {d : Nat -> Nat} {a b : Nat} (h : AdjacentHits d a b) :
    d b = 1 := h.2.2.1

theorem AdjacentHits.zero_between {d : Nat -> Nat} {a b j : Nat}
    (h : AdjacentHits d a b) (haj : a < j) (hjb : j < b) :
    d j = 0 := h.2.2.2 j haj hjb

theorem AdjacentHits.zero_gap_condition {d : Nat -> Nat} {a b : Nat}
    (h : AdjacentHits d a b) :
    ∀ j : Nat, a < j -> j <= a + (b - a - 1) -> d j = 0 := by
  intro j haj hj
  exact h.zero_between haj (by omega)

/--
Adjacent support gap bound once the later hit lies below a dyadic scale and the
constant factor is absorbed into `2^B`.
-/
theorem adjacent_hit_gap_len_le_dyadic_scale {Q C B X L : Nat} {P : Int}
    {d : Nat -> Nat} {a b : Nat}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hadj : AdjacentHits d a b)
    (hX : X = 2 ^ L)
    (hscale : b + 1 <= C * X)
    (hconst : Q * C <= 2 ^ B) :
    b - a <= L + B + 1 := by
  have hab : a < b := hadj.lt
  have hpos : 0 < integerCarry Q P d a :=
    integerCarry_pos_of_later_one (Q := Q) (P := P) (d := d) (N := a) (M := b)
      hQ hd heta hab hadj.right_hit
  have hzero := hadj.zero_gap_condition
  have hscale' : a + (b - a - 1) + 2 <= C * X := by
    have heq : a + (b - a - 1) + 2 = b + 1 := by omega
    rw [heq]
    exact hscale
  have hle := zero_gap_len_le_dyadic_scale (Q := Q) (C := C) (B := B) (X := X) (L := L)
    (P := P) (d := d) (N := a) (h := b - a - 1)
    hQ hd heta hpos hzero hX hscale' hconst
  have hgap_eq : b - a = (b - a - 1) + 1 := by omega
  rw [hgap_eq]
  exact Nat.succ_le_succ hle

theorem adjacent_hit_gap_len_le_of_dyadic_scale {Q C B X : Nat} {P : Int}
    {d : Nat -> Nat} {a b : Nat}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hadj : AdjacentHits d a b)
    (hX : Dyadic X)
    (hscale : b + 1 <= C * X)
    (hconst : Q * C <= 2 ^ B) :
    ∃ L : Nat, X = 2 ^ L ∧ b - a <= L + B + 1 := by
  rcases hX with ⟨L, hL⟩
  exact ⟨L, hL, adjacent_hit_gap_len_le_dyadic_scale hQ hd heta hadj hL hscale hconst⟩

end

end Erdos260
