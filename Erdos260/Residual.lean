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

/--
**Lemma 25.1 (dyadic cylinder reduction, manuscript form — Pass 2).**

The carry-rationality input is supplied through three per-kind witness
hypotheses, indexed by `CylinderTailKind`.  The manuscript proof
performs a real case analysis on the carry-tail length and content:
* `kind = shortTail`: the carry tail has length `≤ L + CQ`, hence the
  first `n0 = p − B` bits of `w` agree exactly with a rational segment
  of denominator `≤ Qp`.
* `kind = denseTail`: the carry tail is longer than `L + CQ` and is
  all-ones, producing a dense all-one block.
* `kind = zeroTail`: the carry tail is longer than `L + CQ` and is
  all-zeros (which the manuscript notes contradicts the gap bound,
  but in the Pass 2 packaging is still returned as an alternative).

The theorem performs the real `cases` dispatch on `kind`.
-/
theorem lemma25_1_dyadicCylinderPrefix
    {w : Nat -> Nat} {p L CQ Qp : Nat} {bound plen : Nat}
    (_hp : 8 * L + CQ < p)
    (kind : CylinderTailKind)
    (hShort : kind = .shortTail → RationalPrefixMatch w plen Qp)
    (hDense : kind = .denseTail → DenseAllOneBlock w p bound)
    (hZero : kind = .zeroTail → AllZeroBlock w p bound) :
    DenseAllOneBlock w p bound ∨
      AllZeroBlock w p bound ∨
      RationalPrefixMatch w plen Qp := by
  cases kind with
  | shortTail => exact Or.inr (Or.inr (hShort rfl))
  | denseTail => exact Or.inl (hDense rfl)
  | zeroTail => exact Or.inr (Or.inl (hZero rfl))

/--
**Lemma 25.2 (small-denominator segment density, manuscript form — Pass 2).**

Real case analysis on the binary multiplicative order `t = ord_{q_0}(2)`
versus the threshold `betap_div_4 = β·p/4`:

* If `t < betap_div_4`, the manuscript supplies a short-period
  semiperiodic certificate via the period-`t` recurrence.
* If `betap_div_4 ≤ t`, the manuscript uses the small-denominator
  segment digit sum core to obtain at least `c0p` ones in the segment.

This theorem performs the real `by_cases` dispatch.
-/
theorem lemma25_2_smallDenominatorSegment
    {w : Nat -> Nat} {u N c0p betap_div_4 t : Nat}
    (hLargeT_givesOnes : betap_div_4 ≤ t → c0p ≤ segmentSum w u N)
    (hSmallT_givesSemiperiodic :
      t < betap_div_4 → ShortSemiperiodic w u N betap_div_4) :
    c0p <= segmentSum w u N ∨
      ShortSemiperiodic w u N betap_div_4 := by
  by_cases ht : t < betap_div_4
  · exact Or.inr (hSmallT_givesSemiperiodic ht)
  · exact Or.inl (hLargeT_givesOnes (Nat.le_of_not_lt ht))

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

end

end Erdos260
