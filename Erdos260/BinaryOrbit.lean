import Mathlib

/-!
# Binary orbit density primitives

This file records the finite combinatorial and arithmetic core used in Lemma 24.1
of `proof_v2.tex`: binary division of one residue, summation over a finite orbit,
the distinct-positive-residue lower bound, and the final density inequality.
-/

namespace Erdos260

open Finset

/-- The quotient bit in the binary division step `2 r = eps q + r'`. -/
def binaryQuotient (q r : Nat) : Nat :=
  (2 * r) / q

/-- The next remainder in the binary division step `2 r = eps q + r'`. -/
def binaryRemainder (q r : Nat) : Nat :=
  (2 * r) % q

theorem binary_division_identity (q r : Nat) :
    2 * r = binaryQuotient q r * q + binaryRemainder q r := by
  rw [binaryQuotient, binaryRemainder]
  simpa [Nat.mul_comm] using (Nat.div_add_mod (2 * r) q).symm

theorem binaryRemainder_lt {q r : Nat} (hq : 0 < q) :
    binaryRemainder q r < q := by
  exact Nat.mod_lt (2 * r) hq

theorem binaryQuotient_le_one {q r : Nat} (hq : 0 < q) (hr : r < q) :
    binaryQuotient q r <= 1 := by
  rw [binaryQuotient]
  have hlt : 2 * r < 2 * q := Nat.mul_lt_mul_of_pos_left hr (by norm_num)
  have hdivlt : (2 * r) / q < 2 := by
    rw [Nat.div_lt_iff_lt_mul hq]
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt
  omega

theorem binaryQuotient_eq_zero_or_one {q r : Nat} (hq : 0 < q) (hr : r < q) :
    binaryQuotient q r = 0 \/ binaryQuotient q r = 1 := by
  have h := binaryQuotient_le_one hq hr
  omega

/-- The cyclic successor on `Fin t`, implemented as addition by one modulo `t`. -/
def cyclicSucc (t : Nat) (ht : 0 < t) : Equiv.Perm (Fin t) :=
  finCycle ⟨1 % t, Nat.mod_lt 1 ht⟩

theorem strictMono_nat_add_one_le
    (r : Nat -> Nat) (hr : StrictMono r) (hpos : forall i, 1 <= r i) :
    forall i, i + 1 <= r i := by
  intro i
  induction i with
  | zero =>
      simpa using hpos 0
  | succ i ih =>
      have hstep : r i + 1 <= r (i + 1) := Nat.succ_le_of_lt (hr (Nat.lt_succ_self i))
      exact Nat.succ_le_of_lt ((Nat.lt_succ_iff.mpr ih).trans_le hstep)

theorem two_mul_sum_range_add_one (t : Nat) :
    2 * (∑ i ∈ range t, (i + 1)) = t * (t + 1) := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      rw [sum_range_succ]
      nlinarith [ih]

theorem strictMono_positive_sum_ge_triangular
    (r : Nat -> Nat) (hr : StrictMono r) (hpos : forall i, 1 <= r i) (t : Nat) :
    t * (t + 1) <= 2 * ∑ i ∈ range t, r i := by
  have hsum : (∑ i ∈ range t, (i + 1)) <= ∑ i ∈ range t, r i :=
    sum_le_sum fun i _ => strictMono_nat_add_one_le r hr hpos i
  have htwice := Nat.mul_le_mul_left 2 hsum
  simpa [two_mul_sum_range_add_one] using htwice

theorem strictMono_fin_nat_add_one_le {t : Nat}
    (r : Fin t -> Nat) (hr : StrictMono r) (hpos : forall i, 1 <= r i) :
    forall i : Fin t, (i : Nat) + 1 <= r i := by
  intro i
  have hclaim : forall n (hn : n < t), n + 1 <= r ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
        intro hn
        simpa using hpos ⟨0, hn⟩
    | succ n ih =>
        intro hn
        have hn' : n < t := Nat.lt_of_succ_lt hn
        have hlt : r ⟨n, hn'⟩ < r ⟨n + 1, hn⟩ := by
          exact hr (by simp)
        have hstep : r ⟨n, hn'⟩ + 1 <= r ⟨n + 1, hn⟩ :=
          Nat.succ_le_of_lt hlt
        exact Nat.succ_le_of_lt ((Nat.lt_succ_iff.mpr (ih hn')).trans_le hstep)
  exact hclaim i i.2

theorem strictMono_fin_positive_sum_ge_triangular {t : Nat}
    (r : Fin t -> Nat) (hr : StrictMono r) (hpos : forall i, 1 <= r i) :
    t * (t + 1) <= 2 * ∑ i, r i := by
  have hsum : (∑ i : Fin t, ((i : Nat) + 1)) <= ∑ i, r i :=
    sum_le_sum fun i _ => strictMono_fin_nat_add_one_le r hr hpos i
  have htwice := Nat.mul_le_mul_left 2 hsum
  have htri : 2 * (∑ i : Fin t, ((i : Nat) + 1)) = t * (t + 1) := by
    simpa [Fin.sum_univ_eq_sum_range (fun i : Nat => i + 1) t]
      using two_mul_sum_range_add_one t
  simpa [htri] using htwice

theorem positive_finset_sum_ge_triangular
    (s : Finset Nat) {t : Nat} (hcard : s.card = t)
    (hpos : forall x, x ∈ s -> 1 <= x) :
    t * (t + 1) <= 2 * ∑ x ∈ s, x := by
  let e : Fin t ↪o Nat := s.orderEmbOfFin hcard
  have hepos : forall i : Fin t, 1 <= e i := by
    intro i
    exact hpos (e i) (Finset.orderEmbOfFin_mem s hcard i)
  have htri := strictMono_fin_positive_sum_ge_triangular (fun i : Fin t => e i) e.strictMono hepos
  have hsum_eq : (∑ i : Fin t, e i) = ∑ x ∈ s, x := by
    have hinj : Set.InjOn (fun i : Fin t => e i) (Finset.univ : Finset (Fin t)) := by
      intro a _ b _ hab
      exact e.injective hab
    rw [← Finset.image_orderEmbOfFin_univ s hcard]
    exact (Finset.sum_image (s := (Finset.univ : Finset (Fin t)))
      (g := fun i : Fin t => e i) (f := fun x : Nat => x) hinj).symm
  simpa [hsum_eq] using htri

theorem binaryDivision_sum_identity_fin {q t : Nat}
    (r eps : Fin t -> Nat) (sigma : Equiv.Perm (Fin t))
    (hdiv : forall i, 2 * r i = eps i * q + r (sigma i)) :
    q * (∑ i, eps i) = ∑ i, r i := by
  have hsum : (∑ i : Fin t, 2 * r i) =
      ∑ i : Fin t, (eps i * q + r (sigma i)) := by
    exact sum_congr rfl fun i _ => hdiv i
  have hsum' : 2 * (∑ i, r i) = (∑ i, eps i) * q + ∑ i, r i := by
    simpa [sum_add_distrib, Finset.mul_sum, Finset.sum_mul, Equiv.sum_comp sigma r,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum
  have hmain : (∑ i, eps i) * q = ∑ i, r i := by
    omega
  simpa [Nat.mul_comm] using hmain

theorem binaryDivision_sum_identity_range {q t : Nat}
    (r eps : Nat -> Nat) (sigma : Equiv.Perm (Fin t))
    (hdiv : forall i : Fin t, 2 * r i = eps i * q + r (sigma i)) :
    q * (∑ i ∈ range t, eps i) = ∑ i ∈ range t, r i := by
  have hfin := binaryDivision_sum_identity_fin
    (fun i : Fin t => r i) (fun i : Fin t => eps i) sigma hdiv
  simpa [Fin.sum_univ_eq_sum_range] using hfin

/--
Arithmetic tail of Lemma 24.1: if the digit count `k` satisfies
`q * k = sum r_i`, the sorted residues have doubled triangular lower bound, and
`q <= C * t`, then `t + 1 <= 2 * C * k`.
-/
theorem orbit_digit_density_arithmetic
    {q C t k : Nat}
    (ht : 0 < t)
    (hq : q <= C * t)
    (hsum : t * (t + 1) <= 2 * q * k) :
    t + 1 <= 2 * C * k := by
  have hqk : 2 * q * k <= 2 * (C * t) * k := by
    exact Nat.mul_le_mul_right k (Nat.mul_le_mul_left 2 hq)
  have hmain : t * (t + 1) <= t * (2 * C * k) := by
    calc
      t * (t + 1) <= 2 * q * k := hsum
      _ <= 2 * (C * t) * k := hqk
      _ = t * (2 * C * k) := by ring
  exact Nat.le_of_mul_le_mul_left hmain ht

theorem orbit_digit_density_real_lower_half {C t k : Nat}
    (hC : 0 < C) (ht : 0 < t) (hdens : t + 1 <= 2 * C * k) :
    (1 : ℝ) / ((2 * C : Nat) : ℝ) <= (k : ℝ) / (t : ℝ) := by
  have ht_le : t <= 2 * C * k := by omega
  have ht_real : (t : ℝ) <= (2 * C * k : Nat) := by exact_mod_cast ht_le
  norm_num [Nat.cast_mul] at ht_real ⊢
  have hCpos : 0 < (C : ℝ) := by exact_mod_cast hC
  have htpos : 0 < (t : ℝ) := by exact_mod_cast ht
  field_simp [hCpos.ne', htpos.ne']
  nlinarith

theorem orbit_digit_density_real_lower_third {C t k : Nat}
    (hC : 0 < C) (ht : 0 < t) (hdens : t + 1 <= 2 * C * k) :
    (1 : ℝ) / ((3 * C : Nat) : ℝ) <= (k : ℝ) / (t : ℝ) := by
  have hthird_half :
      (1 : ℝ) / ((3 * C : Nat) : ℝ) <= (1 : ℝ) / ((2 * C : Nat) : ℝ) := by
    have hCpos : 0 < (C : ℝ) := by exact_mod_cast hC
    norm_num [Nat.cast_mul]
    field_simp [hCpos.ne']
    nlinarith
  exact hthird_half.trans (orbit_digit_density_real_lower_half hC ht hdens)

/--
Finite orbit form of Lemma 24.1.  The permutation `sigma` is the cyclic successor
on the residue orbit; `hdiv` is the binary division identity
`2 r_i = eps_i q + r_{sigma i}`.  The theorem performs both summations and the
distinct-positive-residue lower bound internally.
-/
theorem binary_orbit_digit_density_fin
    {q C t k : Nat} {r eps : Fin t -> Nat} (sigma : Equiv.Perm (Fin t))
    (ht : 0 < t)
    (hq : q <= C * t)
    (hrpos : forall i, 1 <= r i)
    (hrinj : Function.Injective r)
    (hdiv : forall i, 2 * r i = eps i * q + r (sigma i))
    (hk : k = ∑ i, eps i) :
    t + 1 <= 2 * C * k := by
  let s : Finset Nat := Finset.univ.image r
  have hcard : s.card = t := by
    simp [s, Finset.card_image_of_injective, hrinj]
  have hpos : forall x, x ∈ s -> 1 <= x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact hrpos i
  have htri_s : t * (t + 1) <= 2 * ∑ x ∈ s, x :=
    positive_finset_sum_ge_triangular s hcard hpos
  have hsum_image : (∑ x ∈ s, x) = ∑ i, r i := by
    have hinj : Set.InjOn r (Finset.univ : Finset (Fin t)) := by
      intro a _ b _ hab
      exact hrinj hab
    simpa [s] using Finset.sum_image hinj
  have hsum_orbit : q * k = ∑ i, r i := by
    rw [hk]
    exact binaryDivision_sum_identity_fin r eps sigma hdiv
  have hsum : t * (t + 1) <= 2 * q * k := by
    calc
      t * (t + 1) <= 2 * ∑ x ∈ s, x := htri_s
      _ = 2 * (∑ i, r i) := by rw [hsum_image]
      _ = 2 * (q * k) := by rw [← hsum_orbit]
      _ = 2 * q * k := by ring
  exact orbit_digit_density_arithmetic ht hq hsum

/--
The same finite orbit density theorem specialized to the cyclic successor
`i ↦ i + 1 mod t`.
-/
theorem binary_orbit_digit_density_cycle
    {q C t k : Nat} {r eps : Fin t -> Nat}
    (ht : 0 < t)
    (hq : q <= C * t)
    (hrpos : forall i, 1 <= r i)
    (hrinj : Function.Injective r)
    (hdiv : forall i, 2 * r i = eps i * q + r (cyclicSucc t ht i))
    (hk : k = ∑ i, eps i) :
    t + 1 <= 2 * C * k :=
  binary_orbit_digit_density_fin (cyclicSucc t ht) ht hq hrpos hrinj hdiv hk

/--
`range t` indexed version of `binary_orbit_digit_density_fin`.  This is the
shape closest to the manuscript notation `j = 0, ..., t-1`.
-/
theorem binary_orbit_digit_density_range
    {q C t k : Nat} (r eps : Nat -> Nat) (sigma : Equiv.Perm (Fin t))
    (ht : 0 < t)
    (hq : q <= C * t)
    (hrpos : forall i, i ∈ range t -> 1 <= r i)
    (hrinj : forall i j, i < t -> j < t -> r i = r j -> i = j)
    (hdiv : forall i : Fin t, 2 * r i = eps i * q + r (sigma i))
    (hk : k = ∑ i ∈ range t, eps i) :
    t + 1 <= 2 * C * k := by
  have hrpos_fin : forall i : Fin t, 1 <= (fun j : Fin t => r j) i := by
    intro i
    exact hrpos i (mem_range.mpr i.2)
  have hrinj_fin : Function.Injective (fun i : Fin t => r i) := by
    intro i j hij
    exact Fin.ext (hrinj i j i.2 j.2 hij)
  have hk_fin : k = ∑ i : Fin t, (fun j : Fin t => eps j) i := by
    simpa [Fin.sum_univ_eq_sum_range] using hk
  exact binary_orbit_digit_density_fin sigma ht hq hrpos_fin hrinj_fin hdiv hk_fin

/--
Binary-division version with the quotient bits and remainders built in.  The
hypothesis `hstep` says that the listed residues advance by one binary
division step along the cyclic order.
-/
theorem binary_orbit_digit_density_binaryQuotient_range
    {q C t k : Nat} (r : Nat -> Nat)
    (ht : 0 < t)
    (hq : q <= C * t)
    (hrpos : forall i, i ∈ range t -> 1 <= r i)
    (hrinj : forall i j, i < t -> j < t -> r i = r j -> i = j)
    (hstep : forall i : Fin t, r (cyclicSucc t ht i) = binaryRemainder q (r i))
    (hk : k = ∑ i ∈ range t, binaryQuotient q (r i)) :
    t + 1 <= 2 * C * k := by
  refine binary_orbit_digit_density_range r (fun i => binaryQuotient q (r i))
    (cyclicSucc t ht) ht hq hrpos hrinj ?_ hk
  intro i
  rw [hstep i]
  exact binary_division_identity q (r i)

theorem binary_orbit_digit_density_binaryQuotient_range_real_lower
    {q C t k : Nat} (r : Nat -> Nat)
    (hC : 0 < C)
    (ht : 0 < t)
    (hq : q <= C * t)
    (hrpos : forall i, i ∈ range t -> 1 <= r i)
    (hrinj : forall i j, i < t -> j < t -> r i = r j -> i = j)
    (hstep : forall i : Fin t, r (cyclicSucc t ht i) = binaryRemainder q (r i))
    (hk : k = ∑ i ∈ range t, binaryQuotient q (r i)) :
    (1 : ℝ) / ((3 * C : Nat) : ℝ) <= (k : ℝ) / (t : ℝ) := by
  exact orbit_digit_density_real_lower_third hC ht
    (binary_orbit_digit_density_binaryQuotient_range r ht hq hrpos hrinj hstep hk)

end Erdos260
