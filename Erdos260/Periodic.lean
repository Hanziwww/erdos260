import Mathlib
import Erdos260.Support

/-!
# Finite periodic-word arithmetic

This file records elementary finite-period arithmetic used around Lemma 24.2:
binary masks, their weights, the denominator `2^p - 1`, and the denominator
drop `D ∣ A*M -> D/gcd(D,A) ∣ M`.
-/

namespace Erdos260

open Finset

noncomputable section

/-- Little-endian binary mask of a period word of length `p`. -/
def periodMask (d : Nat -> Nat) (p : Nat) : Nat :=
  ∑ j ∈ range p, d j * 2 ^ j

/-- Number of ones in a period word of length `p`. -/
def periodWeight (d : Nat -> Nat) (p : Nat) : Nat :=
  ∑ j ∈ range p, d j

/-- Denominator of a purely periodic binary word of period `p`. -/
def periodDen (p : Nat) : Nat :=
  2 ^ p - 1

theorem sum_range_two_pow_eq_periodDen (p : Nat) :
    (∑ j ∈ range p, 2 ^ j) = periodDen p := by
  unfold periodDen
  induction p with
  | zero => simp
  | succ p ih =>
      rw [sum_range_succ, ih]
      have hpow : 1 <= 2 ^ p := Nat.succ_le_of_lt (Nat.pow_pos (by norm_num : 0 < 2))
      omega

theorem periodDen_pos {p : Nat} (hp : 0 < p) :
    0 < periodDen p := by
  unfold periodDen
  have h : 1 < 2 ^ p := Nat.one_lt_pow hp.ne' (by norm_num)
  omega

theorem periodMask_le_periodDen {d : Nat -> Nat} (hd : BinaryDigits d) (p : Nat) :
    periodMask d p <= periodDen p := by
  have hsum : periodMask d p <= ∑ j ∈ range p, 2 ^ j := by
    unfold periodMask
    exact sum_le_sum fun j _ => by
      rcases hd j with h | h <;> simp [h]
  rwa [sum_range_two_pow_eq_periodDen] at hsum

theorem periodWeight_le_length {d : Nat -> Nat} (hd : BinaryDigits d) (p : Nat) :
    periodWeight d p <= p := by
  unfold periodWeight
  calc
    (∑ j ∈ range p, d j) <= ∑ j ∈ range p, 1 := by
      exact sum_le_sum fun j _ => by
        rcases hd j with h | h <;> simp [h]
    _ = p := by simp

theorem periodDensity_nat_bound {d : Nat -> Nat} (hd : BinaryDigits d) (p : Nat) :
    periodWeight d p <= p :=
  periodWeight_le_length hd p

theorem periodMask_eq_zero_of_zero {d : Nat -> Nat} {p : Nat}
    (hzero : ∀ j : Nat, j < p -> d j = 0) :
    periodMask d p = 0 := by
  unfold periodMask
  exact sum_eq_zero fun j hj => by
    rw [mem_range] at hj
    simp [hzero j hj]

theorem periodWeight_eq_zero_of_zero {d : Nat -> Nat} {p : Nat}
    (hzero : ∀ j : Nat, j < p -> d j = 0) :
    periodWeight d p = 0 := by
  unfold periodWeight
  exact sum_eq_zero fun j hj => by
    rw [mem_range] at hj
    exact hzero j hj

theorem periodWeight_pos_of_exists_one {d : Nat -> Nat} {p : Nat}
    (hone : ∃ j : Nat, j < p ∧ d j = 1) :
    0 < periodWeight d p := by
  rcases hone with ⟨j, hj, hdj⟩
  unfold periodWeight
  have hmem : j ∈ range p := by simpa using hj
  calc
    0 < d j := by simp [hdj]
    _ <= ∑ k ∈ range p, d k := by
          exact single_le_sum (fun _ _ => Nat.zero_le _) hmem

theorem periodMask_pos_of_exists_one {d : Nat -> Nat} {p : Nat}
    (hone : ∃ j : Nat, j < p ∧ d j = 1) :
    0 < periodMask d p := by
  rcases hone with ⟨j, hj, hdj⟩
  unfold periodMask
  have hmem : j ∈ range p := by simpa using hj
  calc
    0 < d j * 2 ^ j := by
          simp [hdj, Nat.pow_pos (by norm_num : 0 < 2)]
    _ <= ∑ k ∈ range p, d k * 2 ^ k := by
          exact single_le_sum
            (s := range p) (f := fun k => d k * 2 ^ k)
            (fun _ _ => Nat.zero_le _) hmem

theorem all_zero_of_periodWeight_eq_zero {d : Nat -> Nat} {p : Nat}
    (hweight : periodWeight d p = 0) :
    ∀ j : Nat, j < p -> d j = 0 := by
  intro j hj
  by_contra hne
  have hpos : 0 < d j := Nat.pos_of_ne_zero hne
  unfold periodWeight at hweight
  have hmem : j ∈ range p := by simpa using hj
  have hle : d j <= ∑ k ∈ range p, d k :=
    single_le_sum (fun _ _ => Nat.zero_le _) hmem
  omega

theorem all_zero_of_periodMask_eq_zero {d : Nat -> Nat} {p : Nat}
    (hd : BinaryDigits d) (hmask : periodMask d p = 0) :
    ∀ j : Nat, j < p -> d j = 0 := by
  intro j hj
  rcases hd j with hzero | hone
  · exact hzero
  · have hpos := periodMask_pos_of_exists_one
      (d := d) (p := p) ⟨j, hj, hone⟩
    omega

theorem exists_one_of_periodWeight_pos {d : Nat -> Nat} {p : Nat}
    (hd : BinaryDigits d) (hpos : 0 < periodWeight d p) :
    ∃ j : Nat, j < p ∧ d j = 1 := by
  by_contra hnone
  have hzero : ∀ j : Nat, j < p -> d j = 0 := by
    intro j hj
    rcases hd j with hdj | hdj
    · exact hdj
    · exact False.elim (hnone ⟨j, hj, hdj⟩)
  have hweight_zero := periodWeight_eq_zero_of_zero hzero
  omega

theorem periodMask_eq_periodDen_of_one {d : Nat -> Nat} {p : Nat}
    (hone : ∀ j : Nat, j < p -> d j = 1) :
    periodMask d p = periodDen p := by
  unfold periodMask
  rw [← sum_range_two_pow_eq_periodDen p]
  exact sum_congr rfl fun j hj => by
    rw [mem_range] at hj
    simp [hone j hj]

theorem periodWeight_eq_length_of_one {d : Nat -> Nat} {p : Nat}
    (hone : ∀ j : Nat, j < p -> d j = 1) :
    periodWeight d p = p := by
  unfold periodWeight
  calc
    (∑ j ∈ range p, d j) = ∑ j ∈ range p, 1 := by
      exact sum_congr rfl fun j hj => by
        rw [mem_range] at hj
        simp [hone j hj]
    _ = p := by simp

theorem periodWeight_lt_length_of_exists_zero {d : Nat -> Nat} {p : Nat}
    (hd : BinaryDigits d) (hzero : ∃ j : Nat, j < p ∧ d j = 0) :
    periodWeight d p < p := by
  rcases hzero with ⟨j, hj, hdj⟩
  unfold periodWeight
  have hmem : j ∈ range p := by simpa using hj
  have hdecomp :
      (∑ k ∈ range p, d k) =
        d j + ∑ k ∈ (range p).erase j, d k := by
    exact (Finset.add_sum_erase (s := range p) (f := d) hmem).symm
  have herase_le :
      (∑ k ∈ (range p).erase j, d k) <= ((range p).erase j).card := by
    calc
      (∑ k ∈ (range p).erase j, d k) <=
          ∑ _k ∈ (range p).erase j, 1 := by
            exact sum_le_sum fun k _ => by
              rcases hd k with h | h <;> simp [h]
      _ = ((range p).erase j).card := by simp
  have hcard : ((range p).erase j).card = p - 1 := by
    simp [hmem]
  rw [hdecomp, hdj]
  omega

theorem periodMask_lt_periodDen_of_exists_zero {d : Nat -> Nat} {p : Nat}
    (hd : BinaryDigits d) (hzero : ∃ j : Nat, j < p ∧ d j = 0) :
    periodMask d p < periodDen p := by
  rcases hzero with ⟨j, hj, hdj⟩
  unfold periodMask
  rw [← sum_range_two_pow_eq_periodDen p]
  have hmem : j ∈ range p := by simpa using hj
  have hmask_decomp :
      (∑ k ∈ range p, d k * 2 ^ k) =
        d j * 2 ^ j + ∑ k ∈ (range p).erase j, d k * 2 ^ k := by
    exact (Finset.add_sum_erase
      (s := range p) (f := fun k => d k * 2 ^ k) hmem).symm
  have hfull_decomp :
      (∑ k ∈ range p, 2 ^ k) =
        2 ^ j + ∑ k ∈ (range p).erase j, 2 ^ k := by
    exact (Finset.add_sum_erase
      (s := range p) (f := fun k => 2 ^ k) hmem).symm
  have herase_le :
      (∑ k ∈ (range p).erase j, d k * 2 ^ k) <=
        ∑ k ∈ (range p).erase j, 2 ^ k := by
    exact sum_le_sum fun k _ => by
      rcases hd k with h | h <;> simp [h]
  rw [hmask_decomp, hfull_decomp, hdj]
  have hpowpos : 0 < 2 ^ j := Nat.pow_pos (by norm_num : 0 < 2)
  omega

theorem all_one_of_periodWeight_eq_length {d : Nat -> Nat} {p : Nat}
    (hd : BinaryDigits d) (hweight : periodWeight d p = p) :
    ∀ j : Nat, j < p -> d j = 1 := by
  intro j hj
  rcases hd j with hzero | hone
  · have hlt := periodWeight_lt_length_of_exists_zero
      (d := d) (p := p) hd ⟨j, hj, hzero⟩
    omega
  · exact hone

theorem all_one_of_periodMask_eq_periodDen {d : Nat -> Nat} {p : Nat}
    (hd : BinaryDigits d) (hmask : periodMask d p = periodDen p) :
    ∀ j : Nat, j < p -> d j = 1 := by
  intro j hj
  rcases hd j with hzero | hone
  · have hlt := periodMask_lt_periodDen_of_exists_zero
      (d := d) (p := p) hd ⟨j, hj, hzero⟩
    omega
  · exact hone

theorem div_gcd_dvd_of_dvd_mul {D A M : Nat} (hD : 0 < D) (h : D ∣ A * M) :
    D / D.gcd A ∣ M := by
  have hmod0 : A * M ≡ 0 [MOD D] := (Nat.modEq_zero_iff_dvd).2 h
  have hmod : A * M ≡ A * 0 [MOD D] := by simpa using hmod0
  have hcancel := hmod.cancel_left_div_gcd hD
  simpa using (Nat.modEq_zero_iff_dvd).1 hcancel

theorem period_den_div_gcd_dvd_mask_of_dvd {p A M : Nat}
    (hp : 0 < p) (h : periodDen p ∣ A * M) :
    periodDen p / (periodDen p).gcd A ∣ M :=
  div_gcd_dvd_of_dvd_mul (periodDen_pos hp) h

theorem period_den_gcd_le_factor {p A : Nat} (hA : 0 < A) :
    (periodDen p).gcd A <= A :=
  Nat.gcd_le_right (periodDen p) hA

theorem period_den_drop_dvd_mask_of_dvd_Qp {Q p M : Nat}
    (hp : 0 < p) (h : periodDen p ∣ (Q * p) * M) :
    periodDen p / (periodDen p).gcd (Q * p) ∣ M :=
  period_den_div_gcd_dvd_mask_of_dvd hp h

theorem period_den_gcd_Qp_le {Q p : Nat} (hQ : 0 < Q) (hp : 0 < p) :
    (periodDen p).gcd (Q * p) <= Q * p :=
  period_den_gcd_le_factor (Nat.mul_pos hQ hp)

/-- Periodicity is preserved by adding any multiple of the period. -/
theorem digit_add_mul_period {d : Nat -> Nat} {p : Nat}
    (hper : ∀ j, d (j + p) = d j) (n i : Nat) :
    d (i + n * p) = d i := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hh : i + (m + 1) * p = (i + m * p) + p := by ring
      rw [hh, hper, ih]

/--
**Lemma 24.2 (fixed density under repetition), real form.**

If the binary word `d` is `p`-periodic (`d (j + p) = d j` for all `j`), then
the number of ones in `k` full periods is exactly `k` times the one-count of a
single period:
`periodWeight d (k · p) = k · periodWeight d p`.

This is the manuscript's "fixed density period repetition" of Lemma 24.2: the
support density `ρ₀(Q) = periodWeight d p / p` is invariant under repeating the
period block.  Unconditional real theorem.
-/
theorem periodWeight_repeat {d : Nat -> Nat} {p : Nat}
    (hper : ∀ j, d (j + p) = d j) (k : Nat) :
    periodWeight d (k * p) = k * periodWeight d p := by
  induction k with
  | zero => simp [periodWeight]
  | succ m ih =>
      have hh : (m + 1) * p = m * p + p := by ring
      rw [hh]
      unfold periodWeight
      rw [Finset.sum_range_add]
      have hinner :
          ∑ x ∈ Finset.range p, d (m * p + x) = ∑ x ∈ Finset.range p, d x := by
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [Nat.add_comm (m * p) x]
        exact digit_add_mul_period hper m x
      rw [hinner]
      unfold periodWeight at ih
      rw [ih]
      ring

/-! ## Bridge lemmas for Lemma 24.2

The following lemmas connect the finite period word `d` (length `p`, mask
`M = periodMask d p`, denominator `D = periodDen p = 2^p - 1`) to the binary
orbit `O_j = 2^j M % D`.  They formalize that the binary expansion of `M / D`
is the cyclic repetition of `w`, which is exactly the content used in the
manuscript proof of Lemma 24.2.
-/

/-- Modular periodicity of powers of two: `2^k ≡ 2^(k % p) [MOD 2^p - 1]`. -/
theorem two_pow_modEq_mod (p k : Nat) :
    2 ^ k ≡ 2 ^ (k % p) [MOD periodDen p] := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp [periodDen]
  · conv_lhs => rw [← Nat.div_add_mod k p]
    rw [pow_add, pow_mul]
    have h1 : (2 : ℕ) ^ p ≡ 1 [MOD periodDen p] := by
      have hle : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_pow p 2 (by norm_num)
      have hd : periodDen p ∣ 2 ^ p - 1 := dvd_refl _
      exact ((Nat.modEq_iff_dvd' hle).2 hd).symm
    calc (2 ^ p) ^ (k / p) * 2 ^ (k % p)
        ≡ 1 ^ (k / p) * 2 ^ (k % p) [MOD periodDen p] :=
          Nat.ModEq.mul_right _ (h1.pow _)
      _ = 2 ^ (k % p) := by rw [one_pow, one_mul]

/-- Reindexing a sum over `range p` by the cyclic shift `i ↦ (i + j) % p`. -/
theorem sum_range_cyclic_shift {M : Type*} [AddCommMonoid M]
    (f : Nat → M) (p j : Nat) (hp : 0 < p) :
    ∑ i ∈ range p, f ((i + j) % p) = ∑ i ∈ range p, f i := by
  classical
  have hinj : Set.InjOn (fun i => (i + j) % p) (range p) := by
    intro x hx y hy hxy
    simp only [coe_range, Set.mem_Iio] at hx hy
    have hmod : (x + j) ≡ (y + j) [MOD p] := hxy
    have hxy' : x ≡ y [MOD p] := Nat.ModEq.add_right_cancel' j hmod
    calc x = x % p := (Nat.mod_eq_of_lt hx).symm
      _ = y % p := hxy'
      _ = y := Nat.mod_eq_of_lt hy
  have himage : (range p).image (fun i => (i + j) % p) = range p := by
    apply Finset.eq_of_subset_of_card_le
    · intro s hs
      rcases Finset.mem_image.1 hs with ⟨i, _, rfl⟩
      exact mem_range.2 (Nat.mod_lt _ hp)
    · rw [Finset.card_image_of_injOn hinj, card_range]
  rw [← Finset.sum_image hinj, himage]

/-- Uniqueness of finite binary representations: two `0/1`-sequences with the same
weighted sum `∑ a i 2^i` over `range p` agree on `range p`. -/
theorem binary_digits_unique :
    ∀ (p : Nat) {a b : Nat → Nat}, BinaryDigits a → BinaryDigits b →
      (∑ i ∈ range p, a i * 2 ^ i = ∑ i ∈ range p, b i * 2 ^ i) →
      ∀ i, i < p → a i = b i := by
  intro p
  induction p with
  | zero => intro a b _ _ _ i hi; omega
  | succ n ih =>
      intro a b ha hb hsum i hi
      rw [Finset.sum_range_succ' (fun i => a i * 2 ^ i) n,
          Finset.sum_range_succ' (fun i => b i * 2 ^ i) n] at hsum
      have hA : ∑ i ∈ range n, a (i + 1) * 2 ^ (i + 1)
          = 2 * ∑ i ∈ range n, a (i + 1) * 2 ^ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
      have hB : ∑ i ∈ range n, b (i + 1) * 2 ^ (i + 1)
          = 2 * ∑ i ∈ range n, b (i + 1) * 2 ^ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
      rw [hA, hB] at hsum
      simp only [pow_zero, mul_one] at hsum
      have ha0 := ha 0
      have hb0 := hb 0
      have key : a 0 = b 0 ∧
          (∑ i ∈ range n, a (i + 1) * 2 ^ i) = ∑ i ∈ range n, b (i + 1) * 2 ^ i := by
        rcases ha0 with h | h <;> rcases hb0 with h' | h' <;> omega
      have ha' : BinaryDigits (fun k => a (k + 1)) := fun k => ha (k + 1)
      have hb' : BinaryDigits (fun k => b (k + 1)) := fun k => hb (k + 1)
      have hrec := ih ha' hb' key.2
      cases i with
      | zero => exact key.1
      | succ j => exact hrec j (by omega)

/-- If the mask is strictly below `D = 2^p - 1`, the word has a zero digit. -/
theorem exists_zero_of_periodMask_lt {d : Nat → Nat} {p : Nat}
    (hd : BinaryDigits d) (hlt : periodMask d p < periodDen p) :
    ∃ i, i < p ∧ d i = 0 := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hone : ∀ i, i < p → d i = 1 := by
    intro i hi
    rcases hd i with h | h
    · exact absurd h (hno i hi)
    · exact h
  have := periodMask_eq_periodDen_of_one hone
  omega

/-- **Bridge lemma.** The binary orbit value `2^j * M % D` equals the cyclic
shift `∑ i, d i * 2^((i+j) % p)` of the mask, provided the mask is not the
all-ones value `D`.  This is the formal statement that the binary expansion of
`M/D` is the cyclic repetition of the period word `w`. -/
theorem periodMask_two_pow_mod {d : Nat → Nat} {p : Nat}
    (hp : 0 < p) (hd : BinaryDigits d) (hlt : periodMask d p < periodDen p) (j : Nat) :
    (2 ^ j * periodMask d p) % periodDen p
      = ∑ i ∈ range p, d i * 2 ^ ((i + j) % p) := by
  have hEq : (2 ^ j * periodMask d p) = ∑ i ∈ range p, d i * 2 ^ (i + j) := by
    unfold periodMask
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_add]; ring
  have hcong : (∑ i ∈ range p, d i * 2 ^ (i + j))
      ≡ (∑ i ∈ range p, d i * 2 ^ ((i + j) % p)) [MOD periodDen p] := by
    show (∑ i ∈ range p, d i * 2 ^ (i + j)) % periodDen p
       = (∑ i ∈ range p, d i * 2 ^ ((i + j) % p)) % periodDen p
    rw [Finset.sum_nat_mod, Finset.sum_nat_mod (f := fun i => d i * 2 ^ ((i + j) % p))]
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      Nat.ModEq.mul_left (d i) (two_pow_modEq_mod p (i + j))
  have hfull : ∑ i ∈ range p, (2 : ℕ) ^ ((i + j) % p) = periodDen p := by
    rw [sum_range_cyclic_shift (fun s => (2 : ℕ) ^ s) p j hp]
    exact sum_range_two_pow_eq_periodDen p
  have hRlt : (∑ i ∈ range p, d i * 2 ^ ((i + j) % p)) < periodDen p := by
    rcases exists_zero_of_periodMask_lt hd hlt with ⟨i0, hi0, hdi0⟩
    rw [← hfull]
    apply Finset.sum_lt_sum
    · intro i _; rcases hd i with h | h <;> simp [h]
    · refine ⟨i0, mem_range.2 hi0, ?_⟩
      rw [hdi0, Nat.zero_mul]
      exact pow_pos (by norm_num) _
  calc (2 ^ j * periodMask d p) % periodDen p
      = (∑ i ∈ range p, d i * 2 ^ (i + j)) % periodDen p := by rw [hEq]
    _ = (∑ i ∈ range p, d i * 2 ^ ((i + j) % p)) % periodDen p := hcong
    _ = ∑ i ∈ range p, d i * 2 ^ ((i + j) % p) := Nat.mod_eq_of_lt hRlt

/-- The cyclic shift `i ↦ (i + j) % p` is inverted by `s ↦ (s + (p - j % p)) % p`. -/
theorem cyc_shift_inv {p : Nat} (hp : 0 < p) (i j : Nat) (hi : i < p) :
    ((i + j) % p + (p - j % p)) % p = i := by
  rw [Nat.add_mod i j p, Nat.mod_eq_of_lt hi]
  have h1 : j % p < p := Nat.mod_lt _ hp
  set m := j % p with hm
  clear_value m
  rcases Nat.lt_or_ge (i + m) p with h | h
  · rw [Nat.mod_eq_of_lt h]
    have he : (i + m) + (p - m) = i + p := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · have h2 : i + m - p < p := by omega
    have heq : (i + m) % p = i + m - p := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt h2]
    rw [heq]
    have he : (i + m - p) + (p - m) = i := by omega
    rw [he, Nat.mod_eq_of_lt hi]

/-- Standard-form bridge: the orbit value written as `∑ u, c_u 2^u` with the
permuted digits `c_u = d ((u + (p - j % p)) % p)`. -/
theorem periodMask_two_pow_mod_std {d : Nat → Nat} {p : Nat}
    (hp : 0 < p) (hd : BinaryDigits d) (hlt : periodMask d p < periodDen p) (j : Nat) :
    (2 ^ j * periodMask d p) % periodDen p
      = ∑ u ∈ range p, d ((u + (p - j % p)) % p) * 2 ^ u := by
  rw [periodMask_two_pow_mod hp hd hlt j,
      ← sum_range_cyclic_shift (fun u => d ((u + (p - j % p)) % p) * 2 ^ u) p j hp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  simp only [cyc_shift_inv hp i j hi]

/-- A cyclic period (`d ((v + c) % p) = d v` for `v < p`) of a `p`-periodic word
upgrades to a genuine global period `d (k + c) = d k`. -/
theorem digit_periodic_of_cyclic {d : Nat → Nat} {p c : Nat} (hp : 0 < p)
    (hper : ∀ j, d (j + p) = d j)
    (hcyc : ∀ v, v < p → d ((v + c) % p) = d v) :
    ∀ k, d (k + c) = d k := by
  have hmod : ∀ n, d n = d (n % p) := by
    intro n
    have h := digit_add_mul_period hper (n / p) (n % p)
    rw [Nat.mod_add_div' n p] at h
    exact h
  intro k
  have hkc : (k + c) % p = (k % p + c) % p := (Nat.mod_add_mod k p c).symm
  calc d (k + c) = d ((k + c) % p) := hmod (k + c)
    _ = d ((k % p + c) % p) := by rw [hkc]
    _ = d (k % p) := hcyc (k % p) (Nat.mod_lt _ hp)
    _ = d k := (hmod k).symm

/-- If two distinct orbit values coincide, the word has a nontrivial cyclic period.
This is the engine that converts `ord_q(2) < p` into a sub-period of `w`. -/
theorem digit_cyclic_of_orbit_eq {d : Nat → Nat} {p : Nat}
    (hp : 0 < p) (hd : BinaryDigits d) (hlt : periodMask d p < periodDen p)
    {a b : Nat} (hab : a < b) (hb : b < p)
    (heq : (2 ^ a * periodMask d p) % periodDen p
         = (2 ^ b * periodMask d p) % periodDen p) :
    ∀ v, v < p → d ((v + (b - a)) % p) = d v := by
  rw [periodMask_two_pow_mod_std hp hd hlt a,
      periodMask_two_pow_mod_std hp hd hlt b] at heq
  have hca : BinaryDigits (fun u => d ((u + (p - a % p)) % p)) := fun u => hd _
  have hcb : BinaryDigits (fun u => d ((u + (p - b % p)) % p)) := fun u => hd _
  have huniq := binary_digits_unique p hca hcb heq
  intro v hv
  have hkey := huniq ((v + b) % p) (Nat.mod_lt _ hp)
  have ea : a % p = a := Nat.mod_eq_of_lt (lt_trans hab hb)
  have lhs_eq : ((v + b) % p + (p - a % p)) % p = (v + (b - a)) % p := by
    rw [Nat.mod_add_mod, ea]
    have hthis : (v + b) + (p - a) = (v + (b - a)) + p := by omega
    rw [hthis, Nat.add_mod_right]
  have rhs_eq : ((v + b) % p + (p - b % p)) % p = v := cyc_shift_inv hp v b hv
  rw [lhs_eq, rhs_eq] at hkey
  exact hkey

/-- The sum of the binary orbit over one period equals `D · wt(w)`.  Each bit of
`M` lands in every position exactly once over the `p` cyclic shifts. -/
theorem sum_orbit_eq {d : Nat → Nat} {p : Nat}
    (hp : 0 < p) (hd : BinaryDigits d) (hlt : periodMask d p < periodDen p) :
    ∑ j ∈ range p, (2 ^ j * periodMask d p) % periodDen p
      = periodDen p * periodWeight d p := by
  have hstep : ∀ j ∈ range p, (2 ^ j * periodMask d p) % periodDen p
      = ∑ i ∈ range p, d i * 2 ^ ((i + j) % p) :=
    fun j _ => periodMask_two_pow_mod hp hd hlt j
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  have hinner : ∀ i ∈ range p,
      ∑ j ∈ range p, d i * 2 ^ ((i + j) % p) = d i * periodDen p := by
    intro i _
    rw [← Finset.mul_sum]
    congr 1
    rw [show (∑ j ∈ range p, (2 : ℕ) ^ ((i + j) % p))
          = ∑ j ∈ range p, (2 : ℕ) ^ ((j + i) % p) from
        Finset.sum_congr rfl (fun j _ => by rw [Nat.add_comm i j]),
      sum_range_cyclic_shift (fun s => (2 : ℕ) ^ s) p i hp]
    exact sum_range_two_pow_eq_periodDen p
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]
  unfold periodWeight
  ring

end

end Erdos260
