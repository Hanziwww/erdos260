import Mathlib
import Erdos260.Density

/-!
# DeepMind-compatible target and first bridge lemmas

The final theorem target is stated in the same shape as the DeepMind
`formal-conjectures` Erdős 260 problem.  The lemmas in this file are proved
unconditionally and prepare the finite-prefix and eventual-positivity bridge
from integer-indexed sequences to natural supports.
-/

namespace Erdos260

open Filter Finset
open scoped Topology

noncomputable section

/-- The term appearing in the DeepMind Erdős 260 statement. -/
def erdosTerm (a : Nat -> Int) (n : Nat) : ℝ :=
  (a n : ℝ) / (2 : ℝ) ^ (a n)

/-- A natural-positive version of the Erdős 260 term. -/
def erdosNatTerm (b : Nat -> Nat) (n : Nat) : ℝ :=
  (b n : ℝ) / (2 : ℝ) ^ (b n)

/-- Finite prefix of the DeepMind-indexed series. -/
def erdosFinitePrefix (a : Nat -> Int) (N : Nat) : ℝ :=
  ∑ n ∈ Finset.range N, erdosTerm a n

/--
The local statement matching the DeepMind formal-conjectures target:
superlinear strictly increasing integer exponents force irrationality of the
weighted binary series.
-/
def Erdos260Statement : Prop :=
  ∀ (a : Nat -> Int) (s : ℝ),
    StrictMono a ->
      Filter.Tendsto (fun n : Nat => (a n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop ->
      HasSum (fun n : Nat => erdosTerm a n) s ->
      Irrational s

/-- Removing a finite prefix from a convergent series. -/
theorem hasSum_nat_tail {f : Nat -> ℝ} {s : ℝ} (h : HasSum f s) (N : Nat) :
    HasSum (fun n : Nat => f (n + N)) (s - ∑ n ∈ Finset.range N, f n) := by
  rw [hasSum_nat_add_iff]
  simpa [sub_add_cancel] using h

/-- Every finite prefix of the DeepMind-indexed series is rational. -/
theorem erdosFinitePrefix_rational (a : Nat -> Int) (N : Nat) :
    ∃ q : Rat, erdosFinitePrefix a N = (q : ℝ) := by
  refine ⟨∑ n ∈ Finset.range N, ((a n : Rat) / (2 : Rat) ^ (a n)), ?_⟩
  simp [erdosFinitePrefix, erdosTerm]

/-- Irrationality is unchanged by adding a rational finite prefix. -/
theorem irrational_add_rational_iff (x : ℝ) (q : Rat) :
    Irrational (x + (q : ℝ)) <-> Irrational x := by
  simp

/-- Irrationality is unchanged by subtracting a rational finite prefix. -/
theorem irrational_sub_rational_iff (x : ℝ) (q : Rat) :
    Irrational (x - (q : ℝ)) <-> Irrational x := by
  simp

theorem eventually_pos_of_ratio_tendsto_atTop {a : Nat -> Int}
    (h : Filter.Tendsto (fun n : Nat => (a n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop) :
    Filter.Eventually (fun n : Nat => 0 < a n) Filter.atTop := by
  filter_upwards
    [h.eventually (eventually_gt_atTop (0 : ℝ)), eventually_gt_atTop (0 : Nat)]
    with n hratio hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmul : 0 < ((a n : ℝ) / (n : ℝ)) * (n : ℝ) := mul_pos hratio hnreal
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hnreal
  rw [div_mul_cancel₀ _ hne] at hmul
  exact_mod_cast hmul

theorem exists_eventual_pos_of_ratio_tendsto_atTop {a : Nat -> Int}
    (h : Filter.Tendsto (fun n : Nat => (a n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop) :
    ∃ N : Nat, ∀ n : Nat, N <= n -> 0 < a n :=
  Filter.eventually_atTop.1 (eventually_pos_of_ratio_tendsto_atTop h)

theorem erdosTerm_eq_natTerm_of_pos {m : Int} (hm : 0 < m) :
    (m : ℝ) / (2 : ℝ) ^ m = ((m.toNat : Nat) : ℝ) / (2 : ℝ) ^ (m.toNat) := by
  have hmcast : ((m.toNat : Nat) : Int) = m := Int.toNat_of_nonneg hm.le
  have hmreal : ((m.toNat : Nat) : ℝ) = (m : ℝ) := by exact_mod_cast hmcast
  calc
    (m : ℝ) / (2 : ℝ) ^ m =
        ((m.toNat : Nat) : ℝ) / (2 : ℝ) ^ (((m.toNat : Nat) : Int)) := by
          rw [hmcast, hmreal]
    _ = ((m.toNat : Nat) : ℝ) / (2 : ℝ) ^ (m.toNat) := by
          rw [zpow_natCast]

theorem strictMono_toNat_tail_of_eventually_pos {a : Nat -> Int}
    (ha : StrictMono a) {N : Nat}
    (hpos : ∀ n : Nat, N <= n -> 0 < a n) :
    StrictMono (fun k : Nat => (a (k + N)).toNat) := by
  intro i j hij
  have hijn : i + N < j + N := by omega
  have hlt : a (i + N) < a (j + N) := ha hijn
  have hleft : 0 <= a (i + N) := (hpos (i + N) (by omega)).le
  have hright : 0 <= a (j + N) := (hpos (j + N) (by omega)).le
  have hltInt :
      (((a (i + N)).toNat : Nat) : Int) < (((a (j + N)).toNat : Nat) : Int) := by
    rwa [Int.toNat_of_nonneg hleft, Int.toNat_of_nonneg hright]
  exact_mod_cast hltInt

theorem erdosTerm_tail_eq_natTerm_of_eventually_pos {a : Nat -> Int} {N : Nat}
    (hpos : ∀ n : Nat, N <= n -> 0 < a n) (k : Nat) :
    erdosTerm a (k + N) = erdosNatTerm (fun j : Nat => (a (j + N)).toNat) k := by
  unfold erdosTerm erdosNatTerm
  exact erdosTerm_eq_natTerm_of_pos (hpos (k + N) (by omega))

/--
The binary digit sequence attached to the positive tail of an integer exponent
sequence.  It marks the natural values attained by `a (k + N)`.
-/
noncomputable def tailDigit (a : Nat -> Int) (N m : Nat) : Nat := by
  classical
  exact if ∃ k : Nat, (a (k + N)).toNat = m then 1 else 0

theorem tailDigit_binary (a : Nat -> Int) (N : Nat) :
    BinaryDigits (tailDigit a N) := by
  intro m
  unfold tailDigit
  classical
  by_cases h : ∃ k : Nat, (a (k + N)).toNat = m <;> simp [h]

theorem tailDigit_eq_one_iff (a : Nat -> Int) (N m : Nat) :
    tailDigit a N m = 1 <-> ∃ k : Nat, (a (k + N)).toNat = m := by
  unfold tailDigit
  classical
  by_cases h : ∃ k : Nat, (a (k + N)).toNat = m <;> simp [h]

end

end Erdos260
