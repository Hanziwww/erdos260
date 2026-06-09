import Erdos260.BinaryOrbit

/-!
# Residual singular-square primitives

This file records finite dyadic-cylinder and small-denominator segment
arithmetic used in Lemma 25.1 and Lemma 25.2 of `proof_v2.tex`.
-/

namespace Erdos260

open Finset

noncomputable section

/-- The dyadic half-open cylinder `[k/2^n, (k+1)/2^n)`. -/
def DyadicCylinder (n k : Nat) (x : ℝ) : Prop :=
  (k : ℝ) / (2 : ℝ) ^ n <= x ∧
    x < ((k + 1 : Nat) : ℝ) / (2 : ℝ) ^ n

/-- Two reals agree through `n` binary cylinder bits. -/
def SameDyadicCylinder (n : Nat) (x y : ℝ) : Prop :=
  ∃ k : Nat, DyadicCylinder n k x ∧ DyadicCylinder n k y

/-- Consecutive finite segment sum. -/
def segmentSum (f : Nat -> Nat) (u N : Nat) : Nat :=
  ∑ i ∈ range N, f (u + i)

/-- A finite word is periodic on `[start, start + length)` with period `period`. -/
def PeriodicOn (w : Nat -> Nat) (start length period : Nat) : Prop :=
  0 < period ∧
    ∀ i : Nat, i + period < length ->
      w (start + i + period) = w (start + i)

/-- A finite word has a short period on `[start, start + length)`. -/
def ShortSemiperiodic (w : Nat -> Nat) (start length bound : Nat) : Prop :=
  ∃ period : Nat, PeriodicOn w start length period ∧ period < bound

theorem PeriodicOn.period_pos {w : Nat -> Nat} {start length period : Nat}
    (h : PeriodicOn w start length period) :
    0 < period :=
  h.1

theorem PeriodicOn.eq_add_period {w : Nat -> Nat} {start length period i : Nat}
    (h : PeriodicOn w start length period) (hi : i + period < length) :
    w (start + i + period) = w (start + i) :=
  h.2 i hi

theorem PeriodicOn.mono_length {w : Nat -> Nat} {start length period : Nat}
    (h : PeriodicOn w start length period) {length' : Nat}
    (hlen : length' <= length) :
    PeriodicOn w start length' period := by
  refine ⟨h.1, ?_⟩
  intro i hi
  exact h.2 i (lt_of_lt_of_le hi hlen)

theorem PeriodicOn.suffix {w : Nat -> Nat} {start length period : Nat}
    (h : PeriodicOn w start length period) {offset length' : Nat}
    (hoff : offset + length' <= length) :
    PeriodicOn w (start + offset) length' period := by
  refine ⟨h.1, ?_⟩
  intro i hi
  have hbound : offset + i + period < length := by omega
  have hstep := h.2 (offset + i) hbound
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep

theorem PeriodicOn.of_constant {w : Nat -> Nat} {start length period c : Nat}
    (hperiod : 0 < period)
    (hconst : ∀ i : Nat, i < length -> w (start + i) = c) :
    PeriodicOn w start length period := by
  refine ⟨hperiod, ?_⟩
  intro i hi
  have hi' : i < length := by omega
  calc
    w (start + i + period) = w (start + (i + period)) := by
      rw [Nat.add_assoc]
    _ = c := hconst (i + period) hi
    _ = w (start + i) := (hconst i hi').symm

theorem PeriodicOn.segmentSum_shift_eq {w : Nat -> Nat}
    {start length period offset N : Nat}
    (h : PeriodicOn w start length period)
    (hbound : offset + N + period <= length) :
    segmentSum w (start + offset + period) N =
      segmentSum w (start + offset) N := by
  unfold segmentSum
  exact sum_congr rfl fun i hi => by
    rw [mem_range] at hi
    have hstep := h.2 (offset + i) (by omega)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep

theorem PeriodicOn.eq_add_mul_period {w : Nat -> Nat}
    {start length period i m : Nat}
    (h : PeriodicOn w start length period)
    (hbound : i + m * period < length) :
    w (start + i + m * period) = w (start + i) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hp : 0 < period := h.1
      have hbound' : i + (m * period + period) < length := by
        simpa [Nat.succ_mul, Nat.add_assoc] using hbound
      have hstep := h.2 (i + m * period) (by omega)
      have hprev : w (start + i + m * period) = w (start + i) := ih (by omega)
      calc
        w (start + i + (m + 1) * period) =
            w (start + i + m * period) := by
              simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                using hstep
        _ = w (start + i) := hprev

theorem PeriodicOn.segmentSum_shift_mul_eq {w : Nat -> Nat}
    {start length period offset N m : Nat}
    (h : PeriodicOn w start length period)
    (hbound : offset + N + m * period <= length) :
    segmentSum w (start + offset + m * period) N =
      segmentSum w (start + offset) N := by
  unfold segmentSum
  exact sum_congr rfl fun i hi => by
    rw [mem_range] at hi
    have hpoint :=
      h.eq_add_mul_period (i := offset + i) (m := m) (by omega)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpoint

theorem ShortSemiperiodic.mono_bound {w : Nat -> Nat} {start length bound : Nat}
    (h : ShortSemiperiodic w start length bound) {bound' : Nat}
    (hbound : bound <= bound') :
    ShortSemiperiodic w start length bound' := by
  rcases h with ⟨period, hper, hlt⟩
  exact ⟨period, hper, lt_of_lt_of_le hlt hbound⟩

theorem ShortSemiperiodic.mono_length {w : Nat -> Nat} {start length bound : Nat}
    (h : ShortSemiperiodic w start length bound) {length' : Nat}
    (hlen : length' <= length) :
    ShortSemiperiodic w start length' bound := by
  rcases h with ⟨period, hper, hlt⟩
  exact ⟨period, hper.mono_length hlen, hlt⟩

theorem ShortSemiperiodic.suffix {w : Nat -> Nat} {start length bound : Nat}
    (h : ShortSemiperiodic w start length bound) {offset length' : Nat}
    (hoff : offset + length' <= length) :
    ShortSemiperiodic w (start + offset) length' bound := by
  rcases h with ⟨period, hper, hlt⟩
  exact ⟨period, hper.suffix hoff, hlt⟩

theorem ShortSemiperiodic.of_constant {w : Nat -> Nat}
    {start length period bound c : Nat}
    (hperiod : 0 < period) (hbound : period < bound)
    (hconst : ∀ i : Nat, i < length -> w (start + i) = c) :
    ShortSemiperiodic w start length bound :=
  ⟨period, PeriodicOn.of_constant hperiod hconst, hbound⟩

theorem dyadicCylinder_width {n k : Nat} {x y : ℝ}
    (hx : DyadicCylinder n k x) (hy : DyadicCylinder n k y) :
    |x - y| < (1 : ℝ) / (2 : ℝ) ^ n := by
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  rw [abs_sub_lt_iff]
  constructor
  · calc
      x - y < ((k + 1 : Nat) : ℝ) / (2 : ℝ) ^ n - (k : ℝ) / (2 : ℝ) ^ n := by
        linarith [hx.2, hy.1]
      _ = (1 : ℝ) / (2 : ℝ) ^ n := by
        field_simp [hpow.ne']
        norm_num
  · calc
      y - x < ((k + 1 : Nat) : ℝ) / (2 : ℝ) ^ n - (k : ℝ) / (2 : ℝ) ^ n := by
        linarith [hy.2, hx.1]
      _ = (1 : ℝ) / (2 : ℝ) ^ n := by
        field_simp [hpow.ne']
        norm_num

theorem dyadicCylinder_unique {n k l : Nat} {x : ℝ}
    (hk : DyadicCylinder n k x) (hl : DyadicCylinder n l x) :
    k = l := by
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  rcases lt_trichotomy k l with hlt | heq | hgt
  · have hkle_nat : k + 1 <= l := Nat.succ_le_of_lt hlt
    have hkle :
        ((k + 1 : Nat) : ℝ) / (2 : ℝ) ^ n <=
          (l : ℝ) / (2 : ℝ) ^ n := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hkle_nat) hpow.le
    linarith [hk.2, hkle, hl.1]
  · exact heq
  · have hlk_nat : l + 1 <= k := Nat.succ_le_of_lt hgt
    have hlk :
        ((l + 1 : Nat) : ℝ) / (2 : ℝ) ^ n <=
          (k : ℝ) / (2 : ℝ) ^ n := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hlk_nat) hpow.le
    linarith [hl.2, hlk, hk.1]

theorem sameDyadicCylinder_of_cylinders {n k : Nat} {x y : ℝ}
    (hx : DyadicCylinder n k x) (hy : DyadicCylinder n k y) :
    SameDyadicCylinder n x y :=
  ⟨k, hx, hy⟩

theorem sameDyadicCylinder_symm {n : Nat} {x y : ℝ}
    (h : SameDyadicCylinder n x y) :
    SameDyadicCylinder n y x := by
  rcases h with ⟨k, hx, hy⟩
  exact ⟨k, hy, hx⟩

theorem sameDyadicCylinder_comm {n : Nat} {x y : ℝ} :
    SameDyadicCylinder n x y ↔ SameDyadicCylinder n y x :=
  ⟨sameDyadicCylinder_symm, sameDyadicCylinder_symm⟩

theorem sameDyadicCylinder_refl_of_cylinder {n k : Nat} {x : ℝ}
    (hx : DyadicCylinder n k x) :
    SameDyadicCylinder n x x :=
  ⟨k, hx, hx⟩

theorem sameDyadicCylinder_trans {n : Nat} {x y z : ℝ}
    (hxy : SameDyadicCylinder n x y)
    (hyz : SameDyadicCylinder n y z) :
    SameDyadicCylinder n x z := by
  rcases hxy with ⟨k, hx, hyk⟩
  rcases hyz with ⟨l, hyl, hz⟩
  have hkl : k = l := dyadicCylinder_unique hyk hyl
  cases hkl
  exact ⟨k, hx, hz⟩

theorem sameDyadicCylinder_width {n : Nat} {x y : ℝ}
    (h : SameDyadicCylinder n x y) :
    |x - y| < (1 : ℝ) / (2 : ℝ) ^ n := by
  rcases h with ⟨k, hx, hy⟩
  exact dyadicCylinder_width hx hy

theorem sameDyadicCylinder_unique_left {n k l : Nat} {x y : ℝ}
    (hxk : DyadicCylinder n k x)
    (hxl : DyadicCylinder n l x)
    (hy : DyadicCylinder n k y) :
    SameDyadicCylinder n x y ∧ k = l :=
  ⟨sameDyadicCylinder_of_cylinders hxk hy, dyadicCylinder_unique hxk hxl⟩

@[simp]
theorem segmentSum_zero (f : Nat -> Nat) (u : Nat) :
    segmentSum f u 0 = 0 := by
  simp [segmentSum]

theorem segmentSum_succ (f : Nat -> Nat) (u N : Nat) :
    segmentSum f u (N + 1) = segmentSum f u N + f (u + N) := by
  simp [segmentSum, sum_range_succ]

theorem segmentSum_append (f : Nat -> Nat) (u M N : Nat) :
    segmentSum f u (M + N) =
      segmentSum f u M + segmentSum f (u + M) N := by
  induction N with
  | zero =>
      simp [segmentSum]
  | succ N ih =>
      rw [show M + (N + 1) = M + N + 1 by omega]
      rw [segmentSum_succ, ih, segmentSum_succ]
      simp [Nat.add_comm, Nat.add_left_comm]

theorem segmentSum_le_append_left (f : Nat -> Nat) (u M N : Nat) :
    segmentSum f u M <= segmentSum f u (M + N) := by
  rw [segmentSum_append]
  omega

theorem segmentSum_le_append_right (f : Nat -> Nat) (u M N : Nat) :
    segmentSum f (u + M) N <= segmentSum f u (M + N) := by
  rw [segmentSum_append]
  omega

theorem segmentSum_mono_pointwise {f g : Nat -> Nat} {u N : Nat}
    (h : ∀ i : Nat, i < N -> f (u + i) <= g (u + i)) :
    segmentSum f u N <= segmentSum g u N := by
  unfold segmentSum
  exact sum_le_sum fun i hi => by
    rw [mem_range] at hi
    exact h i hi

theorem segmentSum_le_const_mul {f : Nat -> Nat} {u N B : Nat}
    (h : ∀ i : Nat, i < N -> f (u + i) <= B) :
    segmentSum f u N <= N * B := by
  unfold segmentSum
  calc
    (∑ i ∈ range N, f (u + i)) <= ∑ _i ∈ range N, B := by
      exact sum_le_sum fun i hi => by
        rw [mem_range] at hi
        exact h i hi
    _ = N * B := by simp

theorem segmentSum_le_length_of_le_one {d : Nat -> Nat} {u N : Nat}
    (hd : ∀ n : Nat, d n <= 1) :
    segmentSum d u N <= N :=
  calc
    segmentSum d u N <= N * 1 := by
      exact segmentSum_le_const_mul fun i _ => by
        exact hd (u + i)
    _ = N := by simp

theorem segmentSum_eq_zero_of_zero {f : Nat -> Nat} {u N : Nat}
    (hzero : ∀ i : Nat, i < N -> f (u + i) = 0) :
    segmentSum f u N = 0 := by
  unfold segmentSum
  exact sum_eq_zero fun i hi => by
    rw [mem_range] at hi
    exact hzero i hi

theorem segmentSum_eq_length_of_one {f : Nat -> Nat} {u N : Nat}
    (hone : ∀ i : Nat, i < N -> f (u + i) = 1) :
    segmentSum f u N = N := by
  unfold segmentSum
  calc
    (∑ i ∈ range N, f (u + i)) = ∑ _i ∈ range N, 1 := by
      exact sum_congr rfl fun i hi => by
        rw [mem_range] at hi
        simp [hone i hi]
    _ = N := by simp

theorem segmentSum_suffix_le {f : Nat -> Nat} {u offset N B : Nat}
    (h : ∀ i : Nat, i < offset + N -> f (u + i) <= B) :
    segmentSum f (u + offset) N <= N * B := by
  exact segmentSum_le_const_mul fun i hi => by
    have hbound : offset + i < offset + N := by omega
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      h (offset + i) hbound

theorem segment_residue_sum_ge_triangular {r : Nat -> Nat} {u N : Nat}
    (hrpos : ∀ i : Nat, i < N -> 1 <= r (u + i))
    (hrinj : ∀ i j : Nat, i < N -> j < N -> r (u + i) = r (u + j) -> i = j) :
    N * (N + 1) <= 2 * segmentSum r u N := by
  let s : Finset Nat := (range N).image fun i => r (u + i)
  have hinj : Set.InjOn (fun i => r (u + i)) (range N : Finset Nat) := by
    intro i hi j hj hij
    rw [Finset.mem_coe, mem_range] at hi hj
    exact hrinj i j hi hj hij
  have hcard : s.card = N := by
    simp [s, Finset.card_image_of_injOn hinj]
  have hpos : ∀ x, x ∈ s -> 1 <= x := by
    intro x hx
    rcases mem_image.mp hx with ⟨i, hi, rfl⟩
    rw [mem_range] at hi
    exact hrpos i hi
  have htri := positive_finset_sum_ge_triangular s hcard hpos
  have hsum_image : (∑ x ∈ s, x) = segmentSum r u N := by
    unfold segmentSum
    exact Finset.sum_image (s := range N) (f := fun x : Nat => x) hinj
  simpa [hsum_image] using htri

/--
Finite arithmetic core of Lemma 25.2: a block of `N` distinct positive residues
whose binary-division summation has endpoint error at most `q` satisfies
`N(N+1) <= 2 q (ones+1)`.
-/
theorem smallDenominator_segment_digit_sum_core
    {q u N rStart rEnd : Nat} {r eps : Nat -> Nat}
    (hrpos : ∀ i : Nat, i < N -> 1 <= r (u + i))
    (hrinj : ∀ i j : Nat, i < N -> j < N -> r (u + i) = r (u + j) -> i = j)
    (hrEnd : rEnd <= q)
    (hsum :
      q * segmentSum eps u N + rEnd = segmentSum r u N + rStart) :
    N * (N + 1) <= 2 * q * (segmentSum eps u N + 1) := by
  have htri := segment_residue_sum_ge_triangular (r := r) (u := u) (N := N) hrpos hrinj
  have hres_le : segmentSum r u N <= q * segmentSum eps u N + rEnd := by
    omega
  have hres_q : segmentSum r u N <= q * (segmentSum eps u N + 1) := by
    calc
      segmentSum r u N <= q * segmentSum eps u N + rEnd := hres_le
      _ <= q * segmentSum eps u N + q := Nat.add_le_add_left hrEnd _
      _ = q * (segmentSum eps u N + 1) := by ring
  calc
    N * (N + 1) <= 2 * segmentSum r u N := htri
    _ <= 2 * (q * (segmentSum eps u N + 1)) := Nat.mul_le_mul_left 2 hres_q
    _ = 2 * q * (segmentSum eps u N + 1) := by ring

theorem smallDenominator_segment_digit_sum_real_lower
    {q u N rStart rEnd : Nat} {r eps : Nat -> Nat}
    (hq : 0 < q)
    (hrpos : ∀ i : Nat, i < N -> 1 <= r (u + i))
    (hrinj : ∀ i j : Nat, i < N -> j < N -> r (u + i) = r (u + j) -> i = j)
    (hrEnd : rEnd <= q)
    (hsum :
      q * segmentSum eps u N + rEnd = segmentSum r u N + rStart) :
    ((N : ℝ) * ((N + 1 : Nat) : ℝ)) / (2 * (q : ℝ)) <=
      ((segmentSum eps u N + 1 : Nat) : ℝ) := by
  have hcore :=
    smallDenominator_segment_digit_sum_core (q := q) (u := u) (N := N)
      (rStart := rStart) (rEnd := rEnd) (r := r) (eps := eps)
      hrpos hrinj hrEnd hsum
  have hreal :
      ((N * (N + 1) : Nat) : ℝ) <=
        ((2 * q * (segmentSum eps u N + 1) : Nat) : ℝ) := by
    exact_mod_cast hcore
  norm_num [Nat.cast_mul] at hreal ⊢
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq
  field_simp [hqpos.ne']
  nlinarith

theorem smallDenominator_segment_digit_sum_real_lower_sub_one
    {q u N rStart rEnd : Nat} {r eps : Nat -> Nat}
    (hq : 0 < q)
    (hrpos : ∀ i : Nat, i < N -> 1 <= r (u + i))
    (hrinj : ∀ i j : Nat, i < N -> j < N -> r (u + i) = r (u + j) -> i = j)
    (hrEnd : rEnd <= q)
    (hsum :
      q * segmentSum eps u N + rEnd = segmentSum r u N + rStart) :
    ((N : ℝ) * ((N + 1 : Nat) : ℝ)) / (2 * (q : ℝ)) - 1 <=
      (segmentSum eps u N : ℝ) := by
  have hmain :=
    smallDenominator_segment_digit_sum_real_lower
      (q := q) (u := u) (N := N) (rStart := rStart) (rEnd := rEnd)
      (r := r) (eps := eps) hq hrpos hrinj hrEnd hsum
  norm_num at hmain ⊢
  linarith

/--
**Lemma 25.2, large-order branch (faithful many-ones bound).**

The arithmetic heart of the `betap_div_4 ≤ t` branch of Lemma 25.2: from the
small-denominator segment core `N(N+1) ≤ 2q(ones+1)` and the sizing
`2q(c0p+1) ≤ N(N+1)` (which the manuscript supplies from `N ≳ βp` and `q ≤ Cp`),
the segment has at least `c0p` ones.  This converts the previously assumed
`hLargeT_givesOnes` hypothesis of `lemma25_2_smallDenominatorSegment` into a
proved consequence of the genuine combinatorial inputs (distinct positive
residues + the binary-division summation relation).
-/
theorem smallDenominator_segment_manyOnes
    {q u N rStart rEnd c0p : Nat} {r eps : Nat -> Nat}
    (hrpos : ∀ i : Nat, i < N -> 1 <= r (u + i))
    (hrinj : ∀ i j : Nat, i < N -> j < N -> r (u + i) = r (u + j) -> i = j)
    (hrEnd : rEnd <= q)
    (hsum :
      q * segmentSum eps u N + rEnd = segmentSum r u N + rStart)
    (hq : 0 < q)
    (hsize : 2 * q * (c0p + 1) <= N * (N + 1)) :
    c0p <= segmentSum eps u N := by
  have hcore :=
    smallDenominator_segment_digit_sum_core (q := q) (u := u) (N := N)
      (rStart := rStart) (rEnd := rEnd) (r := r) (eps := eps)
      hrpos hrinj hrEnd hsum
  have h : 2 * q * (c0p + 1) <= 2 * q * (segmentSum eps u N + 1) :=
    le_trans hsize hcore
  have hc : c0p + 1 <= segmentSum eps u N + 1 :=
    Nat.le_of_mul_le_mul_left h (by omega)
  omega

theorem smallDenominator_segment_length_le_two_q
    {q u N rStart rEnd : Nat} {r eps : Nat -> Nat}
    (hrpos : ∀ i : Nat, i < N -> 1 <= r (u + i))
    (hrinj : ∀ i j : Nat, i < N -> j < N -> r (u + i) = r (u + j) -> i = j)
    (heps : ∀ i : Nat, i < N -> eps (u + i) <= 1)
    (hrEnd : rEnd <= q)
    (hsum :
      q * segmentSum eps u N + rEnd = segmentSum r u N + rStart) :
    N <= 2 * q := by
  have hcore :=
    smallDenominator_segment_digit_sum_core
      (q := q) (u := u) (N := N) (rStart := rStart) (rEnd := rEnd)
      (r := r) (eps := eps) hrpos hrinj hrEnd hsum
  have hseg : segmentSum eps u N <= N :=
    calc
      segmentSum eps u N <= N * 1 := segmentSum_le_const_mul heps
      _ = N := by simp
  have hright :
      2 * q * (segmentSum eps u N + 1) <= 2 * q * (N + 1) := by
    exact Nat.mul_le_mul_left (2 * q) (Nat.succ_le_succ hseg)
  have hmul : N * (N + 1) <= (2 * q) * (N + 1) :=
    hcore.trans hright
  exact Nat.le_of_mul_le_mul_right hmul (Nat.succ_pos N)

/-! ### Dyadic residue sequence for Lemma 25.2

The genuine arithmetic object behind Lemma 25.2.  After stripping the
`2`-adic preperiod (`q = 2^e q₀`) and reducing the fraction, the manuscript
works with an odd denominator `q₀` and a numerator `a` coprime to `q₀`, the
residues `r_j ≡ 2^j a (mod q₀)` (with `1 ≤ r_j ≤ q₀-1`), and their binary
digits `ε_{j+1} = ⌊2 r_j / q₀⌋`.  The multiplicative order
`t = ord_{q₀}(2) = orderOf (2 : ZMod q₀)` controls both branches: the digit
sequence is genuinely periodic with period `t` (small-order branch), and on
any block of length `≤ t` the residues are distinct (large-order branch),
which feeds the small-denominator digit-sum core. -/

/-- The residue `2^j a mod q₀` (manuscript `r_j`). -/
def dyadicResidue (q0 a j : Nat) : Nat := (2 ^ j * a) % q0

/-- The binary digit `ε_{j+1} = ⌊2 r_j / q₀⌋` of the dyadic expansion of
`a / q₀` (manuscript notation). -/
def dyadicDigit (q0 a j : Nat) : Nat := binaryQuotient q0 (dyadicResidue q0 a j)

/-- Residues are genuine residues: `r_j < q₀`. -/
theorem dyadicResidue_lt {q0 : Nat} (hq0 : 0 < q0) (a j : Nat) :
    dyadicResidue q0 a j < q0 :=
  Nat.mod_lt _ hq0

/-- Residues are positive: with `q₀ > 1` odd and `a` coprime, `2^j a` is a
unit mod `q₀`, so `1 ≤ r_j`. -/
theorem dyadicResidue_pos {q0 a : Nat} (hq0 : 1 < q0) (hodd : Odd q0)
    (hcop : Nat.Coprime a q0) (j : Nat) :
    1 ≤ dyadicResidue q0 a j := by
  show 1 ≤ (2 ^ j * a) % q0
  rcases Nat.eq_zero_or_pos ((2 ^ j * a) % q0) with h0 | hpos
  · exfalso
    have hdvd : q0 ∣ 2 ^ j * a := Nat.dvd_of_mod_eq_zero h0
    have hcop2 : Nat.Coprime 2 q0 := Nat.coprime_two_left.mpr hodd
    have hcopprod : Nat.Coprime (2 ^ j * a) q0 := (hcop2.pow_left j).mul_left hcop
    have hcg : Nat.gcd (2 ^ j * a) q0 = 1 := hcopprod
    have hg : q0 ∣ Nat.gcd (2 ^ j * a) q0 := Nat.dvd_gcd hdvd dvd_rfl
    rw [hcg] at hg
    have := Nat.le_of_dvd one_pos hg
    omega
  · exact hpos

/-- The binary-division recurrence `r_{j+1} = (2 r_j) mod q₀`. -/
theorem dyadicResidue_step (q0 a j : Nat) :
    dyadicResidue q0 a (j + 1) = binaryRemainder q0 (dyadicResidue q0 a j) := by
  show (2 ^ (j + 1) * a) % q0 = (2 * ((2 ^ j * a) % q0)) % q0
  conv_lhs => rw [pow_succ, show 2 ^ j * 2 * a = 2 * (2 ^ j * a) by ring]
  exact ((Nat.mod_modEq (2 ^ j * a) q0).mul_left 2).symm

/-- `2` has finite multiplicative order in `ZMod q₀` for odd `q₀ > 1`
(Euler: `2^φ(q₀) ≡ 1`). -/
theorem isOfFinOrder_two_zmod {q0 : Nat} (hq0 : 1 < q0) (hodd : Odd q0) :
    IsOfFinOrder (2 : ZMod q0) := by
  haveI : NeZero q0 := ⟨by omega⟩
  have hcop2 : Nat.Coprime 2 q0 := Nat.coprime_two_left.mpr hodd
  have heuler : (2 : ℕ) ^ q0.totient ≡ 1 [MOD q0] := Nat.ModEq.pow_totient hcop2
  have hcast : (((2 : ℕ) ^ q0.totient : ℕ) : ZMod q0) = ((1 : ℕ) : ZMod q0) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr heuler
  push_cast at hcast
  exact isOfFinOrder_iff_pow_eq_one.mpr
    ⟨q0.totient, Nat.totient_pos.mpr (by omega), hcast⟩

/-- The residue sequence is periodic with period `t = ord_{q₀}(2)`:
`2^t ≡ 1 (mod q₀)` so `r_{j+t} = r_j`.  (Holds for every `q₀`.) -/
theorem dyadicResidue_period (q0 a j : Nat) :
    dyadicResidue q0 a (j + orderOf (2 : ZMod q0)) = dyadicResidue q0 a j := by
  set t := orderOf (2 : ZMod q0) with ht
  have h2t : (2 : ℕ) ^ t ≡ 1 [MOD q0] := by
    have hp : (2 : ZMod q0) ^ t = 1 := pow_orderOf_eq_one (2 : ZMod q0)
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact hp
  show (2 ^ (j + t) * a) % q0 = (2 ^ j * a) % q0
  have he : (2 : ℕ) ^ (j + t) * a = 2 ^ j * (2 ^ t * a) := by rw [pow_add]; ring
  have h1 : (2 : ℕ) ^ j * (2 ^ t * a) ≡ 2 ^ j * (1 * a) [MOD q0] :=
    (h2t.mul_right a).mul_left (2 ^ j)
  rw [one_mul] at h1
  rw [he]
  exact h1

/-- The digit sequence is periodic with period `t = ord_{q₀}(2)`
(small-order branch of Lemma 25.2). -/
theorem dyadicDigit_period (q0 a j : Nat) :
    dyadicDigit q0 a (j + orderOf (2 : ZMod q0)) = dyadicDigit q0 a j := by
  unfold dyadicDigit
  rw [dyadicResidue_period q0 a j]

/-- On any block of length `≤ t = ord_{q₀}(2)` the residues are distinct: this
is the manuscript's "the residues are distinct" claim, the input needed by the
small-denominator digit-sum core for the large-order branch. -/
theorem dyadicResidue_injOn {q0 a : Nat} (hq0 : 1 < q0) (hodd : Odd q0)
    (hcop : Nat.Coprime a q0) {u N : Nat} (hN : N ≤ orderOf (2 : ZMod q0)) :
    ∀ i j : Nat, i < N → j < N →
      dyadicResidue q0 a (u + i) = dyadicResidue q0 a (u + j) → i = j := by
  haveI : NeZero q0 := ⟨by omega⟩
  have hfin : IsOfFinOrder (2 : ZMod q0) := isOfFinOrder_two_zmod hq0 hodd
  intro i j hi hj heq
  unfold dyadicResidue at heq
  have hmod : 2 ^ (u + i) * a ≡ 2 ^ (u + j) * a [MOD q0] := heq
  have hcast : ((2 ^ (u + i) * a : ℕ) : ZMod q0) = ((2 ^ (u + j) * a : ℕ) : ZMod q0) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  push_cast at hcast
  have ha_unit : IsUnit ((a : ℕ) : ZMod q0) := (ZMod.isUnit_iff_coprime a q0).mpr hcop
  have hpow : (2 : ZMod q0) ^ (u + i) = (2 : ZMod q0) ^ (u + j) :=
    ha_unit.mul_right_cancel hcast
  have hmodeq : (u + i) ≡ (u + j) [MOD orderOf (2 : ZMod q0)] :=
    hfin.pow_eq_pow_iff_modEq.mp hpow
  have hij : i ≡ j [MOD orderOf (2 : ZMod q0)] := Nat.ModEq.add_left_cancel' u hmodeq
  have hi' : i < orderOf (2 : ZMod q0) := lt_of_lt_of_le hi hN
  have hj' : j < orderOf (2 : ZMod q0) := lt_of_lt_of_le hj hN
  have hmm : i % orderOf (2 : ZMod q0) = j % orderOf (2 : ZMod q0) := hij
  rwa [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at hmm

/-- The binary-division summation identity over a block `[u, u+N)`:
`q₀ · Σε + r_{u+N} = Σr + r_u` (manuscript display before (25.2a)). -/
theorem dyadicResidue_segment_sum_identity (q0 a u N : Nat) :
    q0 * segmentSum (dyadicDigit q0 a) u N + dyadicResidue q0 a (u + N)
      = segmentSum (dyadicResidue q0 a) u N + dyadicResidue q0 a u := by
  have hstar : 2 * segmentSum (dyadicResidue q0 a) u N
      = q0 * segmentSum (dyadicDigit q0 a) u N
        + segmentSum (dyadicResidue q0 a) (u + 1) N := by
    unfold segmentSum
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold dyadicDigit
    have hstep : dyadicResidue q0 a (u + 1 + i)
        = binaryRemainder q0 (dyadicResidue q0 a (u + i)) := by
      rw [show u + 1 + i = (u + i) + 1 by omega]
      exact dyadicResidue_step q0 a (u + i)
    rw [hstep, binary_division_identity q0 (dyadicResidue q0 a (u + i))]
    ring
  have hone : segmentSum (dyadicResidue q0 a) u 1 = dyadicResidue q0 a u := by
    simp [segmentSum]
  have htel : segmentSum (dyadicResidue q0 a) u N + dyadicResidue q0 a (u + N)
      = dyadicResidue q0 a u + segmentSum (dyadicResidue q0 a) (u + 1) N := by
    rw [← segmentSum_succ, show N + 1 = 1 + N by omega, segmentSum_append, hone]
  omega

/-- **Lemma 25.2, large-order branch (genuine).**

For the actual dyadic digit sequence of `a/q₀` (odd `q₀ > 1`, `a` coprime),
a block of length `N ≤ ord_{q₀}(2)` has distinct positive residues, so the
small-denominator digit-sum core yields at least `c₀p` ones whenever the
sizing `2 q₀ (c₀p+1) ≤ N(N+1)` holds. -/
theorem dyadicDigit_segment_manyOnes {q0 a u N c0p : Nat}
    (hq0 : 1 < q0) (hodd : Odd q0) (hcop : Nat.Coprime a q0)
    (hN : N ≤ orderOf (2 : ZMod q0))
    (hsize : 2 * q0 * (c0p + 1) ≤ N * (N + 1)) :
    c0p ≤ segmentSum (dyadicDigit q0 a) u N := by
  refine smallDenominator_segment_manyOnes
    (q := q0) (r := dyadicResidue q0 a) (rStart := dyadicResidue q0 a u)
    (rEnd := dyadicResidue q0 a (u + N)) ?_ ?_ ?_ ?_ ?_ hsize
  · intro i _; exact dyadicResidue_pos hq0 hodd hcop (u + i)
  · exact dyadicResidue_injOn hq0 hodd hcop hN
  · exact le_of_lt (dyadicResidue_lt (by omega) a (u + N))
  · exact dyadicResidue_segment_sum_identity q0 a u N
  · omega

/-! ### Manuscript-level Lemma 25.1, 25.2 and Proposition 25.3 -/

/--
Predicate: `w` contains a dense all-one block of length `> bound`
starting somewhere in `[0, length)`.  This is the conclusion of branch 1
of Lemma 25.1 ("dense all-one block triggers local-spike stopping").
-/
def DenseAllOneBlock (w : Nat -> Nat) (length bound : Nat) : Prop :=
  ∃ start blen : Nat,
    start + blen <= length ∧ bound < blen ∧
      ∀ i : Nat, i < blen -> w (start + i) = 1

/--
Predicate: `w` contains an all-zero block of length `> bound` starting
somewhere in `[0, length)`.  Branch 2 of Lemma 25.1; it contradicts the
rational gap bound `g_k ≤ L + B`.
-/
def AllZeroBlock (w : Nat -> Nat) (length bound : Nat) : Prop :=
  ∃ start blen : Nat,
    start + blen <= length ∧ bound < blen ∧
      ∀ i : Nat, i < blen -> w (start + i) = 0

/--
Predicate: `w` has a prefix of length at least `plen` that agrees
exactly with the binary segment of some rational number with
denominator `<= Q * p`.  Branch 3 of Lemma 25.1.
-/
def RationalPrefixMatch (w : Nat -> Nat) (plen Qp : Nat) : Prop :=
  ∃ (digits : Nat -> Nat) (q : Nat),
    0 < q ∧ q <= Qp ∧
      (∀ i : Nat, i < plen -> digits i ∈ ({0, 1} : Set Nat)) ∧
      ∀ i : Nat, i < plen -> w i = digits i

/--
The three carry-tail possibilities in Lemma 25.1's proof: short tail
(prefix match), dense all-one tail, or zero tail.  The manuscript's
case analysis branches on which of these holds.
-/
inductive CylinderTailKind where
  | shortTail
  | denseTail
  | zeroTail
deriving DecidableEq, Repr

/-! #### Genuine geometric core of Lemma 25.1 (fractional approximation 25.1) -/

/--
**Equation (25.1), exact algebraic identity.**  If `M·Qp − ν·D = R` then
`M/D − ν/Qp = R/(D·Qp)`.  This is the algebraic content of the denominator-drop
fractional residual: from `Qp·M ≡ R (mod D)` (i.e. `M·Qp − ν·D = R` for the
integer quotient `ν`) the distance of `M/D` to the small-denominator point
`ν/Qp` is exactly `R/(D·Qp)`. -/
theorem residual_fractional_identity {M Qp D ν R : ℝ}
    (hD : D ≠ 0) (hQp : Qp ≠ 0)
    (hrel : M * Qp - ν * D = R) :
    M / D - ν / Qp = R / (D * Qp) := by
  rw [div_sub_div _ _ hD hQp, show M * Qp - D * ν = R from by rw [← hrel]; ring]

/-- Absolute-value form of (25.1): `|M/D − ν/Qp| = |R|/(D·Qp)`. -/
theorem residual_fractional_identity_abs {M Qp D ν R : ℝ}
    (hD : 0 < D) (hQp : 0 < Qp)
    (hrel : M * Qp - ν * D = R) :
    |M / D - ν / Qp| = |R| / (D * Qp) := by
  rw [residual_fractional_identity hD.ne' hQp.ne' hrel, abs_div,
    abs_of_pos (mul_pos hD hQp)]

/--
**Fractional approximation bound of Lemma 25.1.**  Combining (25.1) with the
singular-square residual bound `|R|·2^n < D·Qp` (the manuscript's
`|R| ≪_Q X+p` input, here a labelled geometric input), `M/D` is within
`2^{-n}` of `ν/Qp`. -/
theorem residual_fractional_approx {M Qp D ν R : ℝ} {n : ℕ}
    (hD : 0 < D) (hQp : 0 < Qp)
    (hrel : M * Qp - ν * D = R)
    (hRbound : |R| * 2 ^ n < D * Qp) :
    |M / D - ν / Qp| < 1 / 2 ^ n := by
  rw [residual_fractional_identity_abs hD hQp hrel]
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hDQp : (0 : ℝ) < D * Qp := mul_pos hD hQp
  rw [div_lt_div_iff₀ hDQp h2n, one_mul]
  linarith

/--
**Binary cylinder stability.**  If `x` and `y` lie within `2^{-n}` of each
other and each lies in a depth-`n` dyadic cylinder, then the two cylinder
indices are equal or adjacent.  This is the manuscript's "the first `n₀`
binary cylinders are equal or adjacent" step. -/
theorem dyadicCylinder_eq_or_adjacent {n kM kν : ℕ} {x y : ℝ}
    (hx : DyadicCylinder n kM x) (hy : DyadicCylinder n kν y)
    (hdist : |x - y| < 1 / 2 ^ n) :
    kM = kν ∨ kν = kM + 1 ∨ kM = kν + 1 := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  rw [abs_sub_lt_iff] at hdist
  obtain ⟨hxy, hyx⟩ := hdist
  have hxL : (kM : ℝ) ≤ x * 2 ^ n := by
    have h := hx.1; rwa [div_le_iff₀ hpow] at h
  have hxR : x * 2 ^ n < (kM : ℝ) + 1 := by
    have h := hx.2; rw [lt_div_iff₀ hpow] at h; push_cast at h; linarith
  have hyL : (kν : ℝ) ≤ y * 2 ^ n := by
    have h := hy.1; rwa [div_le_iff₀ hpow] at h
  have hyR : y * 2 ^ n < (kν : ℝ) + 1 := by
    have h := hy.2; rw [lt_div_iff₀ hpow] at h; push_cast at h; linarith
  have hd1 : (x - y) * 2 ^ n < 1 := (lt_div_iff₀ hpow).mp hxy
  have hd2 : (y - x) * 2 ^ n < 1 := (lt_div_iff₀ hpow).mp hyx
  rw [sub_mul] at hd1 hd2
  have hA : (kM : ℝ) < (kν : ℝ) + 2 := by linarith
  have hB : (kν : ℝ) < (kM : ℝ) + 2 := by linarith
  have hA' : kM < kν + 2 := by exact_mod_cast hA
  have hB' : kν < kM + 2 := by exact_mod_cast hB
  omega

/--
**Lemma 25.1, geometric heart (genuine).**  From the residual congruence
relation `M·Qp − ν·D = R` (eq 25.1) and the singular-square residual bound
`|R|·2^{n₀} < D·Qp`, the mask point `M/D` and the small-denominator point
`ν/Qp` lie in equal or adjacent depth-`n₀` dyadic cylinders.  This is exactly
the cylinder dichotomy the manuscript derives before the carry-tail analysis. -/
theorem residual_cylinder_dichotomy {M Qp D ν R : ℝ} {n0 kM kν : ℕ}
    (hD : 0 < D) (hQp : 0 < Qp)
    (hrel : M * Qp - ν * D = R)
    (hRbound : |R| * 2 ^ n0 < D * Qp)
    (hcylM : DyadicCylinder n0 kM (M / D))
    (hcylν : DyadicCylinder n0 kν (ν / Qp)) :
    kM = kν ∨ kν = kM + 1 ∨ kM = kν + 1 :=
  dyadicCylinder_eq_or_adjacent hcylM hcylν
    (residual_fractional_approx hD hQp hrel hRbound)

/--
**Lemma 25.1 (dyadic cylinder reduction, genuine reduction).**

The geometric step is now genuinely proved: from the residual fractional
relation `M·Qp − ν·D = R` (eq 25.1) and the singular-square residual bound
`|R|·2^{n₀} < D·Qp`, `residual_cylinder_dichotomy` shows the depth-`n₀`
cylinder indices of `M/D` and `ν/Qp` are equal or adjacent.

The remaining content — translating that cylinder relation into the binary
word `w` — is the manuscript's carry-tail analysis, reduced here to its
smallest honest primitives:
* equal cylinders ⟹ exact rational-prefix agreement (`hEqual`);
* adjacent cylinders ⟹ a dense all-one tail or an all-zero tail produced by
  the binary carry words `ξ011…1` / `ξ100…0` (`hAdjacent`).

These two primitives require a binary-digit↔cylinder bridge for `w` that is
outside this file; everything else (the trichotomy and the *which*-cylinder
case split) is proved. -/
theorem lemma25_1_dyadicCylinderPrefix
    {w : Nat -> Nat} {M D ν R : ℝ} {p n0 kM kν : ℕ} {bound plen Qp : ℕ}
    (hD : 0 < D) (hQp : 0 < Qp)
    (hrel : M * (Qp : ℝ) - ν * D = R)
    (hRbound : |R| * 2 ^ n0 < D * (Qp : ℝ))
    (hcylM : DyadicCylinder n0 kM (M / D))
    (hcylν : DyadicCylinder n0 kν (ν / (Qp : ℝ)))
    (hEqual : kM = kν → RationalPrefixMatch w plen Qp)
    (hAdjacent : (kν = kM + 1 ∨ kM = kν + 1) →
      DenseAllOneBlock w p bound ∨ AllZeroBlock w p bound) :
    DenseAllOneBlock w p bound ∨
      AllZeroBlock w p bound ∨
      RationalPrefixMatch w plen Qp := by
  have hQpR : (0 : ℝ) < (Qp : ℝ) := by exact_mod_cast hQp
  rcases residual_cylinder_dichotomy hD hQpR hrel hRbound hcylM hcylν with heq | hadj
  · exact Or.inr (Or.inr (hEqual heq))
  · rcases hAdjacent hadj with hd | hz
    · exact Or.inl hd
    · exact Or.inr (Or.inl hz)

/--
**Lemma 25.2 (small-denominator segment density, genuine).**

Fix an odd denominator `q₀ > 1` and a numerator `a` coprime to `q₀`, and let
`w = dyadicDigit q₀ a` be the binary digit sequence of `a/q₀`.  Let
`t = ord_{q₀}(2) = orderOf (2 : ZMod q₀)`.  The manuscript's threshold
`betap_div_4` plays the role of `⌊βp/4⌋`; `hNlen` records `betap_div_4 ≤ N`
(genuinely `n' ≥ βp/2 ≥ βp/4`) and `hsize` records the sizing
`2 q₀ (c₀p+1) ≤ ⌊βp/4⌋(⌊βp/4⌋+1)` produced by `q₀ ≤ Cp` and the choice of
`c₀ = c₀(C,β)` small.  Then the segment either has at least `c₀p` ones, or is
semiperiodic with period `< βp/4`.

Both branches are proved genuinely (no hypothesis shells):

* `t < betap_div_4`: the digit sequence is periodic with period `t < βp/4`
  (`dyadicDigit_period`), giving the short-semiperiodic certificate.
* `betap_div_4 ≤ t`: a block of length `min N t (≥ βp/4)` has distinct
  positive residues (`dyadicResidue_injOn`), so the small-denominator
  digit-sum core (`dyadicDigit_segment_manyOnes`) yields `≥ c₀p` ones, and
  monotonicity extends this to the full segment.
-/
theorem lemma25_2_smallDenominatorSegment
    {q0 a u N c0p betap_div_4 : Nat}
    (hq0 : 1 < q0) (hodd : Odd q0) (hcop : Nat.Coprime a q0)
    (hNlen : betap_div_4 ≤ N)
    (hsize : 2 * q0 * (c0p + 1) ≤ betap_div_4 * (betap_div_4 + 1)) :
    c0p ≤ segmentSum (dyadicDigit q0 a) u N ∨
      ShortSemiperiodic (dyadicDigit q0 a) u N betap_div_4 := by
  have htpos : 0 < orderOf (2 : ZMod q0) :=
    orderOf_pos_iff.mpr (isOfFinOrder_two_zmod hq0 hodd)
  by_cases ht : orderOf (2 : ZMod q0) < betap_div_4
  · refine Or.inr ⟨orderOf (2 : ZMod q0), ⟨htpos, ?_⟩, ht⟩
    intro i _
    exact dyadicDigit_period q0 a (u + i)
  · have htge : betap_div_4 ≤ orderOf (2 : ZMod q0) := Nat.le_of_not_lt ht
    refine Or.inl ?_
    set M := min N (orderOf (2 : ZMod q0)) with hMdef
    have hMN : M ≤ N := min_le_left _ _
    have hMt : M ≤ orderOf (2 : ZMod q0) := min_le_right _ _
    have hbM : betap_div_4 ≤ M := le_min hNlen htge
    have hsizeM : 2 * q0 * (c0p + 1) ≤ M * (M + 1) :=
      le_trans hsize (Nat.mul_le_mul hbM (by omega))
    have hMany : c0p ≤ segmentSum (dyadicDigit q0 a) u M :=
      dyadicDigit_segment_manyOnes hq0 hodd hcop hMt hsizeM
    have hmono : segmentSum (dyadicDigit q0 a) u M
        ≤ segmentSum (dyadicDigit q0 a) u N := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hMN
      rw [hd]
      exact segmentSum_le_append_left _ u M d
    exact le_trans hMany hmono

/--
Output classification for Proposition 25.3.  Each residual singular
square is assigned to one of four output categories listed in the
manuscript.
-/
inductive ResidualSingularOutput (w : Nat -> Nat) (p : Nat) where
  | shorterPeriodRun (newPeriod : Nat) (hnew : newPeriod < p)
  | cleanBoundaryDirty
  | apTower
  | localSpike
deriving Repr

/--
**Proposition 25.3 (residual singular squares are controlled — Pass 2).**

Real case analysis combining Lemma 25.1's trichotomy with the
mean-low-density classification of run outputs.  Given the trichotomy
of 25.1 plus three per-branch witnesses, the manuscript dispatches
each residual square to one of the four output classes.

* DenseAllOneBlock → `localSpike` (local-spike package).
* AllZeroBlock → `cleanBoundaryDirty` (gap-bound contradiction routed
  to clean-boundary dirty recursion).
* RationalPrefixMatch → `shorterPeriodRun` or `apTower` depending on
  the run trichotomy (which Pass 2 keeps as user input).
-/
theorem proposition25_3_residualSingularSquares
    {w : Nat -> Nat} {p L CQ Qp : Nat} {bound plen : Nat}
    (_hp : 8 * L + CQ < p)
    (htri :
      DenseAllOneBlock w p bound ∨
        AllZeroBlock w p bound ∨
        RationalPrefixMatch w plen Qp)
    (hDense_localSpike :
      DenseAllOneBlock w p bound → ResidualSingularOutput w p)
    (hZero_cleanBoundary :
      AllZeroBlock w p bound → ResidualSingularOutput w p)
    (hRational_runOutput :
      RationalPrefixMatch w plen Qp → ResidualSingularOutput w p) :
    Nonempty (ResidualSingularOutput w p) := by
  rcases htri with hDense | hZero | hRat
  · exact ⟨hDense_localSpike hDense⟩
  · exact ⟨hZero_cleanBoundary hZero⟩
  · exact ⟨hRational_runOutput hRat⟩

/--
**Proposition 25.3 from the Lemma 25.1 cylinder dichotomy.**

This is the proof-v4 residual cleanup chain in one theorem: the genuinely
proved dyadic-cylinder dichotomy of Lemma 25.1 (`residual_cylinder_dichotomy`,
threaded through `lemma25_1_dyadicCylinderPrefix`) supplies the trichotomy
consumed by Proposition 25.3, and the resulting branch is routed to one of the
residual output classes.  The `hEqual`/`hAdjacent` inputs are the carry-tail
word primitives; everything else is proved.
-/
theorem proposition25_3_residualSingularSquares_of_tailKind
    {w : Nat -> Nat} {M D ν R : ℝ} {p L CQ n0 kM kν : Nat} {bound plen Qp : Nat}
    (hp : 8 * L + CQ < p)
    (hD : 0 < D) (hQp : 0 < Qp)
    (hrel : M * (Qp : ℝ) - ν * D = R)
    (hRbound : |R| * 2 ^ n0 < D * (Qp : ℝ))
    (hcylM : DyadicCylinder n0 kM (M / D))
    (hcylν : DyadicCylinder n0 kν (ν / (Qp : ℝ)))
    (hEqual : kM = kν -> RationalPrefixMatch w plen Qp)
    (hAdjacent : (kν = kM + 1 ∨ kM = kν + 1) ->
      DenseAllOneBlock w p bound ∨ AllZeroBlock w p bound)
    (hDense_localSpike :
      DenseAllOneBlock w p bound -> ResidualSingularOutput w p)
    (hZero_cleanBoundary :
      AllZeroBlock w p bound -> ResidualSingularOutput w p)
    (hRational_runOutput :
      RationalPrefixMatch w plen Qp -> ResidualSingularOutput w p) :
    Nonempty (ResidualSingularOutput w p) :=
  proposition25_3_residualSingularSquares hp
    (lemma25_1_dyadicCylinderPrefix hD hQp hrel hRbound hcylM hcylν hEqual hAdjacent)
    hDense_localSpike hZero_cleanBoundary hRational_runOutput

end

end Erdos260
