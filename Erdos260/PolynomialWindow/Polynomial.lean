import Erdos260.PolynomialWindow.Basic
import Mathlib.Analysis.Polynomial.Order
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Localization.Integral

/-!
# Polynomial normalization and elementary growth

The public weight is a polynomial over `ℚ`.  The carry argument, however,
needs integer coefficients.  `IntegralNormalization` records the precise
denominator-clearing certificate.  Its multiplier is allowed to be negative:
this is necessary when the original polynomial has negative leading
coefficient and the normalized polynomial is required to have positive
leading coefficient.
-/

noncomputable section

open Filter Set
open scoped BigOperators

namespace Erdos260.PolynomialWindow

/-- A denominator-clearing certificate with a positive leading coefficient.

The equation is deliberately stated in the standard monomial basis, using
`Polynomial.map`; no alternative opaque notion of an integer-valued
polynomial is introduced. -/
structure IntegralNormalization (p : Polynomial ℚ) where
  multiplier : ℤ
  multiplier_ne_zero : multiplier ≠ 0
  poly : Polynomial ℤ
  poly_ne_zero : poly ≠ 0
  leadingCoeff_pos : 0 < poly.leadingCoeff
  map_eq :
    poly.map (algebraMap ℤ ℚ) = (multiplier : ℚ) • p

/-- Clearing denominators and, if necessary, changing the overall sign gives
an integer polynomial with positive leading coefficient. -/
theorem exists_integralNormalization {p : Polynomial ℚ} (hp : p ≠ 0) :
    Nonempty (IntegralNormalization p) := by
  let q : Polynomial ℤ :=
    IsLocalization.integerNormalization (nonZeroDivisors ℤ) p
  obtain ⟨a, ha_mem, ha_map⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) p
  have ha : a ≠ 0 := by
    simpa [mem_nonZeroDivisors_iff_ne_zero] using ha_mem
  have hq : q ≠ 0 := by
    intro hq0
    apply hp
    exact IsFractionRing.integerNormalization_eq_zero_iff.mp hq0
  have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  rcases lt_or_gt_of_ne hlc with hlc_neg | hlc_pos
  · refine ⟨{
      multiplier := -a
      multiplier_ne_zero := neg_ne_zero.mpr ha
      poly := -q
      poly_ne_zero := neg_ne_zero.mpr hq
      leadingCoeff_pos := ?_
      map_eq := ?_ }⟩
    · simpa using neg_pos.mpr hlc_neg
    · rw [Polynomial.map_neg, ha_map]
      simp [Algebra.smul_def]
  · refine ⟨{
      multiplier := a
      multiplier_ne_zero := ha
      poly := q
      poly_ne_zero := hq
      leadingCoeff_pos := hlc_pos
      map_eq := ha_map }⟩

/-- The absolute value of the normalization multiplier is a positive natural
number.  This is the magnitude of the common-denominator certificate. -/
theorem IntegralNormalization.multiplier_natAbs_pos {p : Polynomial ℚ}
    (h : IntegralNormalization p) : 0 < h.multiplier.natAbs :=
  Int.natAbs_pos.mpr h.multiplier_ne_zero

/-- Mapping the normalization identity through evaluation gives the expected
pointwise identity over `ℚ`. -/
theorem IntegralNormalization.eval_map_eq {p : Polynomial ℚ}
    (h : IntegralNormalization p) (n : ℚ) :
    (h.poly.map (algebraMap ℤ ℚ)).eval n =
      (h.multiplier : ℚ) * p.eval n := by
  have := congrArg (fun r : Polynomial ℚ => r.eval n) h.map_eq
  simpa using this

/-- The real polynomial associated to an integer normalization. -/
def IntegralNormalization.realPoly {p : Polynomial ℚ}
    (h : IntegralNormalization p) : Polynomial ℝ :=
  h.poly.map (algebraMap ℤ ℝ)

theorem IntegralNormalization.realPoly_ne_zero {p : Polynomial ℚ}
    (h : IntegralNormalization p) : h.realPoly ≠ 0 := by
  exact (Polynomial.map_ne_zero_iff
    (FaithfulSMul.algebraMap_injective ℤ ℝ)).mpr h.poly_ne_zero

theorem IntegralNormalization.realPoly_leadingCoeff_pos {p : Polynomial ℚ}
    (h : IntegralNormalization p) : 0 < h.realPoly.leadingCoeff := by
  rw [IntegralNormalization.realPoly,
    Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero]
  · change (0 : ℝ) < (h.poly.leadingCoeff : ℝ)
    exact_mod_cast h.leadingCoeff_pos
  · simpa using (FaithfulSMul.algebraMap_injective ℤ ℝ).ne
      h.leadingCoeff_pos.ne'

/-- A positively normalized polynomial is eventually positive on natural
arguments.  The statement uses an explicit cutoff, as required by the uniform
window interfaces later in the development. -/
theorem IntegralNormalization.eventually_eval_nat_pos {p : Polynomial ℚ}
    (h : IntegralNormalization p) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → 0 < h.realPoly.eval (n : ℝ) := by
  let R := h.realPoly
  have hR0 : R ≠ 0 := h.realPoly_ne_zero
  by_cases hdeg : R.natDegree = 0
  · refine ⟨0, fun n hn => ?_⟩
    change 0 < R.eval (n : ℝ)
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
    have hlc : R.leadingCoeff = R.coeff 0 := by
      simp [Polynomial.leadingCoeff, hdeg]
    rw [← hlc]
    simpa [R] using h.realPoly_leadingCoeff_pos
  · have hdegree : 0 < R.degree := by
      exact Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)
    have htend : Tendsto (fun x : ℝ => R.eval x) atTop atTop :=
      R.tendsto_atTop_of_leadingCoeff_nonneg hdegree
        h.realPoly_leadingCoeff_pos.le
    obtain ⟨x₀, hx₀⟩ :=
      Filter.Eventually.exists_forall_of_atTop (htend.eventually_gt_atTop 0)
    refine ⟨Nat.ceil x₀, fun n hn => hx₀ (n : ℝ) ?_⟩
    exact le_trans (Nat.le_ceil x₀) (by exact_mod_cast hn)

/-! ## Removing the `b`-primary denominator -/

/-- Product of the prime-power factors of `q` whose primes divide `b`. -/
def basePrimaryPart (b q : ℕ) : ℕ :=
  ∏ r ∈ q.primeFactors with r ∣ b, r ^ q.factorization r

/-- Product of the prime-power factors of `q` whose primes do not divide `b`. -/
def baseCoprimePart (b q : ℕ) : ℕ :=
  ∏ r ∈ q.primeFactors with ¬r ∣ b, r ^ q.factorization r

/-- The denominator split used when a finite base-`b` prefix is absorbed. -/
structure BaseDenominatorSplit (b q : ℕ) where
  primary : ℕ
  coprime : ℕ
  exponent : ℕ
  factorization : q = primary * coprime
  primary_dvd_pow : primary ∣ b ^ exponent
  coprime_base : Nat.Coprime coprime b

theorem basePrimaryPart_mul_baseCoprimePart {b q : ℕ} (hq : q ≠ 0) :
    q = basePrimaryPart b q * baseCoprimePart b q := by
  classical
  calc
    q = ∏ r ∈ q.primeFactors, r ^ q.factorization r :=
      Nat.prod_primeFactors_pow_factorization hq
    _ = basePrimaryPart b q * baseCoprimePart b q := by
      exact (Finset.prod_filter_mul_prod_filter_not q.primeFactors
        (fun r => r ∣ b) (fun r => r ^ q.factorization r)).symm

theorem baseCoprimePart_coprime (b q : ℕ) :
    Nat.Coprime (baseCoprimePart b q) b := by
  classical
  rw [baseCoprimePart, Nat.coprime_prod_left_iff]
  intro r hr
  have hr' := Finset.mem_filter.mp hr
  have hprime : r.Prime := Nat.prime_of_mem_primeFactors hr'.1
  have hcop : Nat.Coprime r b := hprime.coprime_iff_not_dvd.mpr hr'.2
  exact hcop.pow_left _

theorem basePrimaryPart_dvd_pow (b q : ℕ) :
    basePrimaryPart b q ∣
      b ^ (∑ r ∈ q.primeFactors with r ∣ b, q.factorization r) := by
  classical
  unfold basePrimaryPart
  calc
    (∏ r ∈ q.primeFactors with r ∣ b, r ^ q.factorization r) ∣
        ∏ r ∈ q.primeFactors with r ∣ b, b ^ q.factorization r := by
          apply Finset.prod_dvd_prod_of_dvd
          intro r hr
          exact pow_dvd_pow_of_dvd (Finset.mem_filter.mp hr).2 _
    _ = b ^ (∑ r ∈ q.primeFactors with r ∣ b, q.factorization r) := by
      exact Finset.prod_pow_eq_pow_sum
        (q.primeFactors.filter fun r => r ∣ b) (fun r => q.factorization r) b

/-- Every positive denominator is the product of a factor absorbed by a finite
base-`b` prefix and a factor coprime to `b`. -/
theorem exists_baseDenominatorSplit {b q : ℕ} (hq : 0 < q) :
    Nonempty (BaseDenominatorSplit b q) := by
  let e := ∑ r ∈ q.primeFactors with r ∣ b, q.factorization r
  exact ⟨{
    primary := basePrimaryPart b q
    coprime := baseCoprimePart b q
    exponent := e
    factorization := basePrimaryPart_mul_baseCoprimePart hq.ne'
    primary_dvd_pow := by
      simpa [e] using basePrimaryPart_dvd_pow b q
    coprime_base := baseCoprimePart_coprime b q }⟩

/-- The canonical denominator split, with the minimal explicit exponent used
throughout the quantitative argument. -/
def canonicalBaseDenominatorSplit (b q : ℕ) (hq : 0 < q) :
    BaseDenominatorSplit b q :=
  { primary := basePrimaryPart b q
    coprime := baseCoprimePart b q
    exponent := ∑ r ∈ q.primeFactors with r ∣ b, q.factorization r
    factorization := basePrimaryPart_mul_baseCoprimePart hq.ne'
    primary_dvd_pow := basePrimaryPart_dvd_pow b q
    coprime_base := baseCoprimePart_coprime b q }

/-- The canonical absorption exponent is logarithmic in the full reduced
denominator. -/
theorem canonicalBaseDenominatorSplit_exponent_le_log (b q : ℕ)
    (hq : 0 < q) :
    (canonicalBaseDenominatorSplit b q hq).exponent ≤ Nat.log 2 q := by
  classical
  let factors := q.primeFactors.filter fun r => r ∣ b
  let e := ∑ r ∈ factors, q.factorization r
  have hprod :
      (∏ r ∈ factors, 2 ^ q.factorization r) ≤
        ∏ r ∈ factors, r ^ q.factorization r := by
    apply Finset.prod_le_prod
    · intro r hr
      exact Nat.zero_le _
    · intro r hr
      have hrPrime : r.Prime :=
        Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1
      exact Nat.pow_le_pow_left hrPrime.two_le _
  have htwo : 2 ^ e ≤ basePrimaryPart b q := by
    calc
      2 ^ e = ∏ r ∈ factors, 2 ^ q.factorization r := by
        dsimp [e]
        rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ ∏ r ∈ factors, r ^ q.factorization r := hprod
      _ = basePrimaryPart b q := by
        rfl
  have hprimaryDvd : basePrimaryPart b q ∣ q := by
    refine ⟨baseCoprimePart b q, ?_⟩
    exact basePrimaryPart_mul_baseCoprimePart hq.ne'
  have hprimaryLe : basePrimaryPart b q ≤ q := Nat.le_of_dvd hq hprimaryDvd
  have he : e ≤ Nat.log 2 q :=
    Nat.le_log_of_pow_le (by omega) (htwo.trans hprimaryLe)
  simpa only [canonicalBaseDenominatorSplit, factors, e] using he

/-- Arithmetic core of denominator absorption for any certified split. -/
theorem BaseDenominatorSplit.mul_pow_den_dvd_coprime
    {b q : ℕ} (h : BaseDenominatorSplit b q)
    (η : ℚ) (hq : q = η.den) :
    (η * (b : ℚ) ^ h.exponent).den ∣ h.coprime := by
  have hprod_pos : 0 < h.primary * h.coprime := by
    rw [← h.factorization, hq]
    exact η.den_pos
  have hp_ne : h.primary ≠ 0 :=
    (Nat.pos_of_mul_pos_right hprod_pos).ne'
  obtain ⟨c, hc⟩ := h.primary_dvd_pow
  let z : ℤ := η.num * (c : ℤ)
  have heq :
      η * (b : ℚ) ^ h.exponent = Rat.divInt z (h.coprime : ℤ) := by
    rw [Rat.divInt_eq_div]
    calc
      η * (b : ℚ) ^ h.exponent =
          ((η.num : ℚ) / (η.den : ℚ)) * (b : ℚ) ^ h.exponent :=
        congrArg (fun x : ℚ => x * (b : ℚ) ^ h.exponent)
          (Rat.num_div_den η).symm
      _ = (z : ℚ) / (h.coprime : ℚ) := by
        have hden_cast :
            (η.den : ℚ) = (h.primary : ℚ) * h.coprime := by
          have hfac : η.den = h.primary * h.coprime := by
            rw [← hq]
            exact h.factorization
          exact_mod_cast hfac
        have hc_cast :
            (b : ℚ) ^ h.exponent = (h.primary : ℚ) * c := by
          exact_mod_cast hc
        rw [hden_cast, hc_cast]
        simp only [Int.cast_mul, Int.cast_natCast, z]
        field_simp
  rw [heq]
  exact Int.natCast_dvd_natCast.mp (Rat.den_dvd z h.coprime)

/-- Logarithmically bounded version of denominator absorption. -/
theorem exists_coprime_denominator_after_prefix_logBound
    (η : ℚ) {b : ℕ} (_hb : 2 ≤ b) :
    ∃ e Q : ℕ, 0 < Q ∧ Nat.Coprime Q b ∧
      e ≤ Nat.log 2 η.den ∧
      (η * (b : ℚ) ^ e).den ∣ Q := by
  let h := canonicalBaseDenominatorSplit b η.den η.den_pos
  refine ⟨h.exponent, h.coprime, ?_, h.coprime_base, ?_, ?_⟩
  · have hprod : 0 < h.primary * h.coprime := by
      rw [← h.factorization]
      exact η.den_pos
    exact Nat.pos_of_mul_pos_left hprod
  · exact canonicalBaseDenominatorSplit_exponent_le_log b η.den η.den_pos
  · exact h.mul_pow_den_dvd_coprime η rfl

/-- Multiplication by a sufficiently long base-`b` prefix removes every
denominator prime shared with `b`.  The surviving denominator divides the
explicit coprime part of the original reduced denominator. -/
theorem exists_coprime_denominator_after_prefix (η : ℚ) {b : ℕ} (_hb : 2 ≤ b) :
    ∃ e Q : ℕ, 0 < Q ∧ Nat.Coprime Q b ∧
      (η * (b : ℚ) ^ e).den ∣ Q := by
  let hsplit : BaseDenominatorSplit b η.den :=
    Classical.choice (exists_baseDenominatorSplit η.den_pos)
  have hprod_pos : 0 < hsplit.primary * hsplit.coprime := by
    simpa [← hsplit.factorization] using η.den_pos
  have hp_ne : hsplit.primary ≠ 0 := by
    exact (Nat.pos_of_mul_pos_right hprod_pos).ne'
  have hQ_pos : 0 < hsplit.coprime := Nat.pos_of_mul_pos_left hprod_pos
  obtain ⟨c, hc⟩ := hsplit.primary_dvd_pow
  let z : ℤ := η.num * (c : ℤ)
  have heq :
      η * (b : ℚ) ^ hsplit.exponent =
        Rat.divInt z (hsplit.coprime : ℤ) := by
    rw [Rat.divInt_eq_div]
    calc
      η * (b : ℚ) ^ hsplit.exponent =
          ((η.num : ℚ) / (η.den : ℚ)) * (b : ℚ) ^ hsplit.exponent :=
        congrArg (fun x : ℚ => x * (b : ℚ) ^ hsplit.exponent)
          (Rat.num_div_den η).symm
      _ = (z : ℚ) / (hsplit.coprime : ℚ) := by
        have hden_cast :
            (η.den : ℚ) = (hsplit.primary : ℚ) * hsplit.coprime := by
          exact_mod_cast hsplit.factorization
        have hc_cast :
            (b : ℚ) ^ hsplit.exponent = (hsplit.primary : ℚ) * c := by
          exact_mod_cast hc
        rw [hden_cast, hc_cast]
        simp only [Int.cast_mul, Int.cast_natCast, z]
        field_simp
  refine ⟨hsplit.exponent, hsplit.coprime, hQ_pos,
    hsplit.coprime_base, ?_⟩
  rw [heq]
  exact Int.natCast_dvd_natCast.mp (Rat.den_dvd z hsplit.coprime)

/-! ## Vandermonde scale -/

/-- Number of pairwise-difference factors for `d + 1` interpolation nodes. -/
def vandermondeExponent (d : ℕ) : ℕ :=
  ∑ i : Fin (d + 1), (Finset.Ioi i).card

theorem vandermondeExponent_eq_choose (d : ℕ) :
    vandermondeExponent d = (d + 1).choose 2 := by
  induction d with
  | zero => simp [vandermondeExponent]
  | succ d ih =>
      rw [vandermondeExponent]
      simp only [Fin.card_Ioi]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ]
      have htail :
          Finset.univ.sum (fun i : Fin (d + 1) =>
            d + 2 - 1 - ((i : ℕ) + 1)) =
            vandermondeExponent d := by
        unfold vandermondeExponent
        simp only [Fin.card_Ioi]
        apply Finset.sum_congr rfl
        intro i hi
        omega
      rw [htail, ih]
      rw [show d + 1 + 1 - 1 - 0 = d + 1 by omega]
      simpa only [Nat.choose_one_right] using
        (Nat.choose_succ_succ' (d + 1) 1).symm

theorem vandermondeExponent_eq (d : ℕ) :
    vandermondeExponent d = d * (d + 1) / 2 := by
  rw [vandermondeExponent_eq_choose, Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_comm]

/-- Integer Vandermonde determinant of `d + 1` nodes. -/
def integerVandermonde {d : ℕ} (x : Fin (d + 1) → ℤ) : ℤ :=
  (Matrix.vandermonde x).det

theorem integerVandermonde_eq_product {d : ℕ} (x : Fin (d + 1) → ℤ) :
    integerVandermonde x =
      ∏ i : Fin (d + 1), ∏ j ∈ Finset.Ioi i, (x j - x i) := by
  exact Matrix.det_vandermonde x

/-- A Vandermonde determinant formed from nodes in an integer interval of
length `H` has size at most `H^s`, where `s = d(d+1)/2`. -/
theorem integerVandermonde_natAbs_le {d H : ℕ} {A : ℤ}
    (x : Fin (d + 1) → ℤ)
    (hx : ∀ i, A ≤ x i ∧ x i ≤ A + H) :
    (integerVandermonde x).natAbs ≤ H ^ vandermondeExponent d := by
  have hdiff (i j : Fin (d + 1)) : (x j - x i).natAbs ≤ H := by
    obtain ⟨hi_lower, hi_upper⟩ := hx i
    obtain ⟨hj_lower, hj_upper⟩ := hx j
    rw [← Int.ofNat_le, Int.natCast_natAbs]
    rw [abs_le]
    constructor <;> omega
  rw [integerVandermonde_eq_product]
  change Int.natAbsHom
    (∏ i : Fin (d + 1), ∏ j ∈ Finset.Ioi i, (x j - x i)) ≤ _
  simp only [map_prod]
  calc
    (∏ i : Fin (d + 1), ∏ j ∈ Finset.Ioi i,
        (x j - x i).natAbs) ≤
        ∏ i : Fin (d + 1), ∏ _j ∈ Finset.Ioi i, H := by
      gcongr with i hi j hj
      exact hdiff i j
    _ = H ^ vandermondeExponent d := by
      rw [vandermondeExponent]
      simp only [Finset.prod_const, Finset.prod_pow_eq_pow_sum]

/-- If an integer multiple of a rational number is integral, its reduced
denominator divides that integer multiplier. -/
theorem rat_den_dvd_natAbs_of_int_mul_eq_int {q : ℚ} {a z : ℤ}
    (h : (a : ℚ) * q = (z : ℚ)) : q.den ∣ a.natAbs := by
  have hcross : a * q.num = (q.den : ℤ) * z := by
    have h' := h
    rw [← Rat.num_div_den q] at h'
    field_simp at h'
    exact_mod_cast h'
  have hdint : (q.den : ℤ) ∣ a * q.num := by
    exact ⟨z, hcross⟩
  have hdnat : q.den ∣ (a * q.num).natAbs :=
    Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdint)
  rw [Int.natAbs_mul] at hdnat
  exact q.reduced.symm.dvd_of_dvd_mul_right hdnat

/-- Integer values at `d + 1` integer nodes force the reduced denominator of
the leading coefficient to divide the corresponding Vandermonde
determinant. -/
theorem leadingCoeff_den_dvd_integerVandermonde {d : ℕ}
    (P : Polynomial ℚ) (hdeg : P.natDegree = d)
    (x : Fin (d + 1) → ℤ) (y : Fin (d + 1) → ℤ)
    (hy : ∀ i, P.eval (x i : ℚ) = (y i : ℚ)) :
    P.leadingCoeff.den ∣ (integerVandermonde x).natAbs := by
  let Vz : Matrix (Fin (d + 1)) (Fin (d + 1)) ℤ := Matrix.vandermonde x
  let Vq : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ :=
    Vz.map (algebraMap ℤ ℚ)
  let coeffs : Fin (d + 1) → ℚ := fun j => P.coeff j
  have hsystem : Matrix.mulVec Vq coeffs = fun i => (y i : ℚ) := by
    funext i
    rw [← hy i]
    rw [Polynomial.eval_eq_sum_range'
      (show P.natDegree < d + 1 by omega)]
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [Vq, Vz, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Matrix.vandermonde_apply, map_pow, coeffs]
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  have hadj := congrArg
    (fun v : Fin (d + 1) → ℚ =>
      Matrix.mulVec Vq.adjugate v (Fin.last d)) hsystem
  have hadj_left :
      Matrix.mulVec Vq.adjugate (Matrix.mulVec Vq coeffs) (Fin.last d) =
        Vq.det * P.leadingCoeff := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, coeffs]
    simp [Polynomial.leadingCoeff, hdeg]
  let z : ℤ := Matrix.mulVec Vz.adjugate y (Fin.last d)
  have hadj_right :
      Matrix.mulVec Vq.adjugate (fun i => (y i : ℚ)) (Fin.last d) = (z : ℚ) := by
    have hmapAdj :
        Vq.adjugate = Vz.adjugate.map (algebraMap ℤ ℚ) := by
      change (Vz.map (algebraMap ℤ ℚ)).adjugate =
        Vz.adjugate.map (algebraMap ℤ ℚ)
      exact (RingHom.map_adjugate (algebraMap ℤ ℚ) Vz).symm
    rw [hmapAdj]
    exact (RingHom.map_mulVec (algebraMap ℤ ℚ) Vz.adjugate y
      (Fin.last d)).symm
  have hdet : Vq.det = (integerVandermonde x : ℚ) := by
    change (Vz.map (algebraMap ℤ ℚ)).det =
      ((Matrix.vandermonde x).det : ℚ)
    simpa [Vz] using (RingHom.map_det (algebraMap ℤ ℚ) Vz).symm
  apply rat_den_dvd_natAbs_of_int_mul_eq_int
    (q := P.leadingCoeff) (a := integerVandermonde x) (z := z)
  calc
    (integerVandermonde x : ℚ) * P.leadingCoeff =
        Vq.det * P.leadingCoeff := by rw [hdet]
    _ = Matrix.mulVec Vq.adjugate (Matrix.mulVec Vq coeffs) (Fin.last d) :=
      hadj_left.symm
    _ = Matrix.mulVec Vq.adjugate (fun i => (y i : ℚ)) (Fin.last d) := hadj
    _ = (z : ℚ) := hadj_right

/-- Telescoping identity for consecutive blocks of `d` gaps in a monotone
natural sequence. -/
theorem sum_stride_spans (x : ℕ → ℕ) (hx : Monotone x) (d t : ℕ) :
    (∑ r ∈ Finset.range t, (x ((r + 1) * d) - x (r * d))) =
      x (t * d) - x 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ, ih]
      have hzero : x 0 ≤ x (t * d) := hx (Nat.zero_le _)
      have hstep : x (t * d) ≤ x ((t + 1) * d) := by
        apply hx
        exact Nat.mul_le_mul_right d (Nat.le_succ t)
      have hindex : (t + 1) * d = t * d + d := by ring
      rw [hindex]
      rw [hindex] at hstep
      omega

/-- Among `K` increasing points in an interval of length `H`, one block of
`d + 1` consecutive points has span at most the appropriate averaged scale.
The division-free inequality is the form used by the fibre argument. -/
theorem exists_short_stride_cluster {d K H : ℕ} (hd : 0 < d) (hK : d < K)
    (x : ℕ → ℕ) (hx : StrictMono x)
    (hdiam : x (K - 1) - x 0 ≤ H) :
    ∃ r < (K - 1) / d,
      ((K - 1) / d) * (x ((r + 1) * d) - x (r * d)) ≤ H := by
  let t := (K - 1) / d
  have hd_le : d ≤ K - 1 := by omega
  have ht_pos : 0 < t := Nat.div_pos hd_le hd
  have htd : t * d ≤ K - 1 := by
    exact Nat.div_mul_le_self (K - 1) d
  have hsum :
      (∑ r ∈ Finset.range t, (x ((r + 1) * d) - x (r * d))) ≤ H := by
    rw [sum_stride_spans x hx.monotone]
    have hendpoint : x (t * d) ≤ x (K - 1) := hx.monotone htd
    omega
  let span : ℕ → ℕ := fun r => x ((r + 1) * d) - x (r * d)
  have hrange : (Finset.range t).Nonempty := by
    exact ⟨0, Finset.mem_range.mpr ht_pos⟩
  obtain ⟨r, hr, hmin⟩ :=
    Finset.exists_min_image (Finset.range t) span hrange
  refine ⟨r, Finset.mem_range.mp hr, ?_⟩
  have havg := Finset.card_nsmul_le_sum (Finset.range t) span (span r) hmin
  simp only [Finset.card_range, nsmul_eq_mul] at havg
  exact havg.trans hsum

/-- The positive `s`-th root of the reduced denominator of the leading
coefficient.  This is the natural scale in the integral-fibre estimate. -/
def leadingDenominatorScale (P : Polynomial ℚ) (d : ℕ) : ℝ :=
  (P.leadingCoeff.den : ℝ) ^ ((vandermondeExponent d : ℝ)⁻¹)

theorem leadingDenominatorScale_pos (P : Polynomial ℚ) (d : ℕ) :
    0 < leadingDenominatorScale P d := by
  unfold leadingDenominatorScale
  positivity

/-- Quantitative integral-fibre bound for an increasing enumeration of the
fibre.  It is deliberately stated with an ambient sequence, so subsequent
applications do not need to transport a variable-cardinality `Finset` through
casts. -/
theorem integralFiber_sequence_bound {d K H : ℕ} (hd : 0 < d)
    (P : Polynomial ℚ) (hdeg : P.natDegree = d)
    (x : ℕ → ℕ) (hx : StrictMono x)
    (y : ℕ → ℤ)
    (hy : ∀ i < K, P.eval (x i : ℚ) = (y i : ℚ))
    (hdiam : x (K - 1) - x 0 ≤ H) :
    (K : ℝ) ≤ d + d * H / leadingDenominatorScale P d := by
  by_cases hK : K ≤ d
  · have hK' : (K : ℝ) ≤ d := by exact_mod_cast hK
    have htail : 0 ≤ (d : ℝ) * H / leadingDenominatorScale P d :=
      div_nonneg (mul_nonneg (by positivity) (by positivity))
        (leadingDenominatorScale_pos P d).le
    exact hK'.trans (le_add_of_nonneg_right htail)
  have hdK : d < K := Nat.lt_of_not_ge hK
  obtain ⟨r, hr, havg⟩ :=
    exists_short_stride_cluster hd hdK x hx hdiam
  let t : ℕ := (K - 1) / d
  let span : ℕ := x ((r + 1) * d) - x (r * d)
  let nodes : Fin (d + 1) → ℤ := fun i => (x (r * d + i) : ℤ)
  let values : Fin (d + 1) → ℤ := fun i => y (r * d + i)
  have htd : t * d ≤ K - 1 := by
    exact Nat.div_mul_le_self (K - 1) d
  have hrblock : (r + 1) * d ≤ t * d := by
    exact Nat.mul_le_mul_right d hr
  have hnode_index (i : Fin (d + 1)) : r * d + (i : ℕ) < K := by
    have hi : (i : ℕ) ≤ d := Nat.le_of_lt_succ i.isLt
    have : r * d + (i : ℕ) ≤ (r + 1) * d := by
      calc
        r * d + (i : ℕ) ≤ r * d + d := Nat.add_le_add_left hi _
        _ = (r + 1) * d := by ring
    omega
  have hvalues : ∀ i, P.eval (nodes i : ℚ) = (values i : ℚ) := by
    intro i
    simpa only [nodes, values, Int.cast_natCast] using
      hy (r * d + (i : ℕ)) (hnode_index i)
  have hnodes_injective : Function.Injective nodes := by
    intro i j hij
    have hxij : x (r * d + (i : ℕ)) = x (r * d + (j : ℕ)) := by
      change (x (r * d + (i : ℕ)) : ℤ) =
        (x (r * d + (j : ℕ)) : ℤ) at hij
      exact Int.ofNat_inj.mp hij
    have hindex := hx.injective hxij
    exact Fin.ext (Nat.add_left_cancel hindex)
  have hdet_ne : integerVandermonde nodes ≠ 0 := by
    unfold integerVandermonde
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hnodes_injective
  have hden_dvd :
      P.leadingCoeff.den ∣ (integerVandermonde nodes).natAbs :=
    leadingCoeff_den_dvd_integerVandermonde P hdeg nodes values hvalues
  have hden_le_det :
      P.leadingCoeff.den ≤ (integerVandermonde nodes).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hdet_ne) hden_dvd
  have hspan_index : r * d ≤ (r + 1) * d := by
    exact Nat.mul_le_mul_right d (Nat.le_succ r)
  have hspan_eq : span = x ((r + 1) * d) - x (r * d) := rfl
  have hnodes_interval (i : Fin (d + 1)) :
      (x (r * d) : ℤ) ≤ nodes i ∧
        nodes i ≤ (x (r * d) : ℤ) + span := by
    have hi : (i : ℕ) ≤ d := Nat.le_of_lt_succ i.isLt
    have hleft_index : r * d ≤ r * d + (i : ℕ) := Nat.le_add_right _ _
    have hright_index : r * d + (i : ℕ) ≤ (r + 1) * d := by
      calc
        r * d + (i : ℕ) ≤ r * d + d := Nat.add_le_add_left hi _
        _ = (r + 1) * d := by ring
    have hleft := hx.monotone hleft_index
    have hright := hx.monotone hright_index
    constructor
    · change (x (r * d) : ℤ) ≤ (x (r * d + (i : ℕ)) : ℤ)
      exact_mod_cast hleft
    · change (x (r * d + (i : ℕ)) : ℤ) ≤
        (x (r * d) : ℤ) + (span : ℤ)
      rw [hspan_eq]
      have hstart_end : x (r * d) ≤ x ((r + 1) * d) :=
        hx.monotone hspan_index
      rw [Int.natCast_sub hstart_end]
      have hright' :
          (x (r * d + (i : ℕ)) : ℤ) ≤ (x ((r + 1) * d) : ℤ) := by
        exact_mod_cast hright
      omega
  have hdet_le :
      (integerVandermonde nodes).natAbs ≤
        span ^ vandermondeExponent d :=
    integerVandermonde_natAbs_le nodes hnodes_interval
  have hden_power :
      P.leadingCoeff.den ≤ span ^ vandermondeExponent d :=
    hden_le_det.trans hdet_le
  have hs_nat : 0 < vandermondeExponent d := by
    rw [vandermondeExponent_eq]
    apply Nat.div_pos
    · nlinarith
    · norm_num
  have hroot_le : leadingDenominatorScale P d ≤ span := by
    unfold leadingDenominatorScale
    apply (Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity)
      (by exact_mod_cast hs_nat)).2
    rw [Real.rpow_natCast]
    exact_mod_cast hden_power
  have hspan_pos : 0 < span := by
    have hindex_lt : r * d < (r + 1) * d := by
      nlinarith
    have hvalue_lt := hx hindex_lt
    exact Nat.sub_pos_of_lt hvalue_lt
  have ht_root_le : (t : ℝ) * leadingDenominatorScale P d ≤ H := by
    have havg' : t * span ≤ H := by simpa only [t, span] using havg
    have hcast : (t : ℝ) * span ≤ H := by exact_mod_cast havg'
    exact (mul_le_mul_of_nonneg_left hroot_le (by positivity)).trans hcast
  have hKd_le_td : K - d ≤ t * d := by
    have hfloor : (K - 1) - d < (K - 1) / d * d :=
      Nat.lt_div_mul_self hd (by omega)
    dsimp [t]
    omega
  have hK_le : K ≤ d + t * d := by omega
  have ht_le : (t : ℝ) ≤ H / leadingDenominatorScale P d := by
    exact (le_div_iff₀ (leadingDenominatorScale_pos P d)).2 ht_root_le
  have hK_real : (K : ℝ) ≤ d + (t : ℝ) * d := by
    exact_mod_cast hK_le
  calc
    (K : ℝ) ≤ d + (t : ℝ) * d := hK_real
    _ = d + d * (t : ℝ) := by ring
    _ ≤ d + d * (H / leadingDenominatorScale P d) := by gcongr
    _ = d + d * H / leadingDenominatorScale P d := by ring

/-! ### From finite fibres to increasing sequences -/

/-- Extend a finite increasing enumeration by an arithmetic tail. -/
def extendFiniteOrderEmbedding {K : ℕ} (e : Fin K ↪o ℕ) (hK : 0 < K) :
    ℕ → ℕ := fun n =>
  if hn : n < K then e ⟨n, hn⟩
  else e ⟨K - 1, by omega⟩ + (n - (K - 1))

@[simp] theorem extendFiniteOrderEmbedding_apply_lt {K : ℕ}
    (e : Fin K ↪o ℕ) (hK : 0 < K) {n : ℕ} (hn : n < K) :
    extendFiniteOrderEmbedding e hK n = e ⟨n, hn⟩ := by
  simp [extendFiniteOrderEmbedding, hn]

theorem extendFiniteOrderEmbedding_strictMono {K : ℕ}
    (e : Fin K ↪o ℕ) (hK : 0 < K) :
    StrictMono (extendFiniteOrderEmbedding e hK) := by
  apply strictMono_nat_of_lt_succ
  intro n
  by_cases hnext : n + 1 < K
  · have hn : n < K := by omega
    rw [extendFiniteOrderEmbedding_apply_lt e hK hn,
      extendFiniteOrderEmbedding_apply_lt e hK hnext]
    exact e.strictMono (by simp only [Fin.mk_lt_mk]; omega)
  · by_cases hn : n < K
    · have hn_eq : n = K - 1 := by omega
      subst n
      simp only [extendFiniteOrderEmbedding]
      have hlast : K - 1 < K := by omega
      have hnotnext : ¬K - 1 + 1 < K := by omega
      rw [dif_pos hlast, dif_neg hnotnext]
      have hval : (⟨K - 1, hlast⟩ : Fin K) = ⟨K - 1, by omega⟩ := rfl
      rw [hval]
      omega
    · simp only [extendFiniteOrderEmbedding]
      rw [dif_neg hn, dif_neg hnext]
      omega

/-- Integer-valued points of a rational polynomial in the closed natural
interval `[A, A + H]`. -/
noncomputable def integralFiber (P : Polynomial ℚ) (A H : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc A (A + H)).filter
    (fun n => ∃ z : ℤ, P.eval (n : ℚ) = (z : ℚ))

theorem mem_integralFiber_iff {P : Polynomial ℚ} {A H n : ℕ} :
    n ∈ integralFiber P A H ↔
      A ≤ n ∧ n ≤ A + H ∧ ∃ z : ℤ, P.eval (n : ℚ) = (z : ℚ) := by
  classical
  simp [integralFiber, and_assoc]

/-- Exact finite-set form of the integral-fibre estimate. -/
theorem integralFiber_card_bound {d : ℕ} (hd : 0 < d)
    (P : Polynomial ℚ) (hdeg : P.natDegree = d) (A H : ℕ) :
    ((integralFiber P A H).card : ℝ) ≤
      d + d * H / leadingDenominatorScale P d := by
  classical
  let s := integralFiber P A H
  let K := s.card
  by_cases hsmall : K ≤ d
  · have hsmall' : (K : ℝ) ≤ d := by exact_mod_cast hsmall
    have htail : 0 ≤ (d : ℝ) * H / leadingDenominatorScale P d :=
      div_nonneg (mul_nonneg (by positivity) (by positivity))
        (leadingDenominatorScale_pos P d).le
    simpa only [K, s] using hsmall'.trans (le_add_of_nonneg_right htail)
  have hdK : d < K := Nat.lt_of_not_ge hsmall
  have hK : 0 < K := hd.trans hdK
  let e : Fin K ↪o ℕ := s.orderEmbOfFin rfl
  let x : ℕ → ℕ := extendFiniteOrderEmbedding e hK
  have hx : StrictMono x := extendFiniteOrderEmbedding_strictMono e hK
  have hx_eq (i : ℕ) (hi : i < K) : x i = e ⟨i, hi⟩ := by
    exact extendFiniteOrderEmbedding_apply_lt e hK hi
  have hintegral (i : ℕ) (hi : i < K) :
      ∃ z : ℤ, P.eval (x i : ℚ) = (z : ℚ) := by
    have hmem : e ⟨i, hi⟩ ∈ s := s.orderEmbOfFin_mem rfl ⟨i, hi⟩
    have hmem' : e ⟨i, hi⟩ ∈ integralFiber P A H := by simpa only [s] using hmem
    obtain ⟨_, _, z, hz⟩ := mem_integralFiber_iff.mp hmem'
    exact ⟨z, by simpa only [hx_eq i hi] using hz⟩
  let y : ℕ → ℤ := fun i =>
    if hi : i < K then Classical.choose (hintegral i hi) else 0
  have hy : ∀ i < K, P.eval (x i : ℚ) = (y i : ℚ) := by
    intro i hi
    simp only [y, dif_pos hi]
    exact Classical.choose_spec (hintegral i hi)
  have hzero_lt : 0 < K := hK
  have hlast_lt : K - 1 < K := by omega
  have hzero_mem : x 0 ∈ integralFiber P A H := by
    have hmem : e ⟨0, hzero_lt⟩ ∈ s :=
      s.orderEmbOfFin_mem rfl ⟨0, hzero_lt⟩
    simpa only [s, hx_eq 0 hzero_lt] using hmem
  have hlast_mem : x (K - 1) ∈ integralFiber P A H := by
    have hmem : e ⟨K - 1, hlast_lt⟩ ∈ s :=
      s.orderEmbOfFin_mem rfl ⟨K - 1, hlast_lt⟩
    simpa only [s, hx_eq (K - 1) hlast_lt] using hmem
  have hdiam : x (K - 1) - x 0 ≤ H := by
    have hzero_bounds := (mem_integralFiber_iff.mp hzero_mem).1
    have hlast_bounds := (mem_integralFiber_iff.mp hlast_mem).2.1
    omega
  have hbound := integralFiber_sequence_bound hd P hdeg x hx y hy hdiam
  simpa only [K, s] using hbound

/-- Manuscript form of `eq:fibre`, with the negative denominator exponent
displayed explicitly. -/
theorem integralFiber_card_bound_rpow {d : ℕ} (hd : 0 < d)
    (P : Polynomial ℚ) (hdeg : P.natDegree = d) (A H : ℕ) :
    ((integralFiber P A H).card : ℝ) ≤
      d + d * H * (P.leadingCoeff.den : ℝ) ^
        (-((vandermondeExponent d : ℝ)⁻¹)) := by
  have h := integralFiber_card_bound hd P hdeg A H
  unfold leadingDenominatorScale at h
  rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity)] at h
  exact h

/-! ## Quantitative sampling -/

/-- Evaluation form of Lagrange interpolation on `d + 1` labelled nodes. -/
theorem eval_eq_lagrange_sum {d : ℕ} (f : Polynomial ℝ)
    (hdeg : f.natDegree ≤ d) (v : Fin (d + 1) → ℝ)
    (hv : Function.Injective v) (z : ℝ) :
    f.eval z = ∑ i : Fin (d + 1),
      f.eval (v i) *
        ∏ j ∈ (Finset.univ.erase i), (v i - v j)⁻¹ * (z - v j) := by
  by_cases hf : f = 0
  · subst f
    simp
  have hdegree : f.degree < ((Finset.univ : Finset (Fin (d + 1))).card : ℕ) := by
    rw [Finset.card_fin]
    exact (Polynomial.natDegree_lt_iff_degree_lt hf).mp
      (hdeg.trans_lt (Nat.lt_succ_self d))
  have hv_on : Set.InjOn v (↑(Finset.univ : Finset (Fin (d + 1))) : Set (Fin (d + 1))) :=
    by
      intro i _ j _ hij
      exact hv hij
  have hinterp :
      f = Lagrange.interpolate Finset.univ v (fun i => f.eval (v i)) :=
    Lagrange.eq_interpolate (s := Finset.univ) (v := v) hv_on hdegree
  calc
    f.eval z =
        (Lagrange.interpolate Finset.univ v (fun i => f.eval (v i))).eval z := by
      exact congrArg (fun p : Polynomial ℝ => p.eval z) hinterp
    _ = _ := by
      simp only [Lagrange.interpolate_apply,
        Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Lagrange.basis, Polynomial.eval_prod,
        Lagrange.basisDivisor, Polynomial.eval_sub, Polynomial.eval_X]

/-- A separated-node Lagrange estimate.  All constants are explicit, which
lets the later uniform window arguments avoid hidden `O`-notation. -/
theorem lagrange_bound_of_separated {d : ℕ} (f : Polynomial ℝ)
    (hdeg : f.natDegree ≤ d) (v : Fin (d + 1) → ℝ)
    (hv : Function.Injective v) {R Y H : ℝ}
    (hR : 0 < R) (hY : 0 ≤ Y) (hH : 0 ≤ H)
    (hsep : ∀ i j, i ≠ j → R ≤ |v i - v j|)
    (hval : ∀ i, |f.eval (v i)| ≤ Y)
    {z : ℝ} (hz : ∀ i, |z - v i| ≤ H) :
    |f.eval z| ≤ (d + 1) * Y * (H / R) ^ d := by
  rw [eval_eq_lagrange_sum f hdeg v hv z]
  calc
    |∑ i : Fin (d + 1),
        f.eval (v i) *
          ∏ j ∈ Finset.univ.erase i, (v i - v j)⁻¹ * (z - v j)| ≤
        ∑ i : Fin (d + 1),
          |f.eval (v i) *
            ∏ j ∈ Finset.univ.erase i, (v i - v j)⁻¹ * (z - v j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (d + 1), Y * (H / R) ^ d := by
      gcongr with i
      have hfactor (j : Fin (d + 1)) (hji : j ∈ Finset.univ.erase i) :
          |(v i - v j)⁻¹ * (z - v j)| ≤ H / R := by
        have hij : i ≠ j := (Finset.mem_erase.mp hji).1.symm
        rw [abs_mul, abs_inv, inv_mul_eq_div]
        exact div_le_div₀ hH (hz j) hR (hsep i j hij)
      have hprod :
          ∏ j ∈ Finset.univ.erase i, |(v i - v j)⁻¹ * (z - v j)| ≤
            (H / R) ^ d := by
        calc
          ∏ j ∈ Finset.univ.erase i, |(v i - v j)⁻¹ * (z - v j)| ≤
              ∏ _j ∈ Finset.univ.erase i, H / R := by
            gcongr with j hj
            exact hfactor j hj
          _ = (H / R) ^ d := by
            rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
              Finset.card_fin]
            simp only [Nat.add_sub_cancel]
      rw [abs_mul, Finset.abs_prod]
      exact mul_le_mul (hval i) hprod
        (Finset.prod_nonneg fun _ _ => abs_nonneg _)
        hY
    _ = (d + 1) * Y * (H / R) ^ d := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      push_cast
      ring

theorem strictMono_nat_gap {x : ℕ → ℕ} (hx : StrictMono x)
    {a b : ℕ} (hab : a ≤ b) : b - a ≤ x b - x a := by
  have h := hx.add_le_nat (b - a) a
  rw [Nat.sub_add_cancel hab] at h
  omega

/-- An explicit constant for the polynomial sampling lemma. -/
def samplingConstant (d : ℕ) : ℝ :=
  (d + 1 : ℝ) * (2 * (d + 1 : ℝ)) ^ d

theorem samplingConstant_pos (d : ℕ) : 0 < samplingConstant d := by
  unfold samplingConstant
  positivity

/-- Sequence form of the sampling estimate in `lem:sampling`: among `U`
increasing integer samples in an interval of length `H`, values bounded by
`Y` control the polynomial throughout that interval. -/
theorem polynomial_sampling_sequence {d U A H : ℕ}
    (hU : 2 * d + 1 ≤ U)
    (f : Polynomial ℝ) (hdeg : f.natDegree ≤ d)
    (x : ℕ → ℕ) (hx : StrictMono x)
    (hsample : ∀ i < U, A ≤ x i ∧ x i ≤ A + H)
    {Y : ℝ} (hY : 0 ≤ Y)
    (hval : ∀ i < U, |f.eval (x i : ℝ)| ≤ Y)
    {z : ℝ} (hz : (A : ℝ) ≤ z ∧ z ≤ A + H) :
    |f.eval z| ≤ samplingConstant d * Y *
      (1 + (H : ℝ) / U) ^ d := by
  let t : ℕ := U / (d + 1)
  have hden_pos : 0 < d + 1 := by omega
  have hden_le : d + 1 ≤ U := by omega
  have ht_pos : 0 < t := Nat.div_pos hden_le hden_pos
  have htd_le : t * (d + 1) ≤ U := by
    simpa only [t, Nat.mul_comm] using Nat.div_mul_le_self U (d + 1)
  let v : Fin (d + 1) → ℝ := fun i => (x ((i : ℕ) * t) : ℝ)
  have hindex (i : Fin (d + 1)) : (i : ℕ) * t < U := by
    have hi : (i : ℕ) < d + 1 := i.isLt
    have hlt : (i : ℕ) * t < (d + 1) * t :=
      Nat.mul_lt_mul_of_pos_right hi ht_pos
    rw [Nat.mul_comm (d + 1) t] at hlt
    exact hlt.trans_le htd_le
  have hv : Function.Injective v := by
    intro i j hij
    have hxeq : x ((i : ℕ) * t) = x ((j : ℕ) * t) := by
      change (x ((i : ℕ) * t) : ℝ) = (x ((j : ℕ) * t) : ℝ) at hij
      exact_mod_cast hij
    have hidx := hx.injective hxeq
    have hvaleq : (i : ℕ) = (j : ℕ) := Nat.mul_right_cancel ht_pos hidx
    exact Fin.ext hvaleq
  have hsep (i j : Fin (d + 1)) (hij : i ≠ j) :
      (t : ℝ) ≤ |v i - v j| := by
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hrank : (i : ℕ) * t ≤ (j : ℕ) * t :=
        Nat.mul_le_mul_right t hijlt.le
      have hrank_gap : t ≤ (j : ℕ) * t - (i : ℕ) * t := by
        have : (i : ℕ) + 1 ≤ (j : ℕ) := hijlt
        rw [← Nat.sub_mul]
        have hone : 1 ≤ (j : ℕ) - (i : ℕ) := by omega
        simpa only [one_mul] using Nat.mul_le_mul_right t hone
      have hvalue_gap := strictMono_nat_gap hx hrank
      have hxy : x ((i : ℕ) * t) ≤ x ((j : ℕ) * t) := hx.monotone hrank
      change (t : ℝ) ≤
        |(x ((i : ℕ) * t) : ℝ) - (x ((j : ℕ) * t) : ℝ)|
      rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hxy)), neg_sub,
        ← Nat.cast_sub hxy]
      exact_mod_cast hrank_gap.trans hvalue_gap
    · have hrank : (j : ℕ) * t ≤ (i : ℕ) * t :=
        Nat.mul_le_mul_right t hjilt.le
      have hrank_gap : t ≤ (i : ℕ) * t - (j : ℕ) * t := by
        have : (j : ℕ) + 1 ≤ (i : ℕ) := hjilt
        rw [← Nat.sub_mul]
        have hone : 1 ≤ (i : ℕ) - (j : ℕ) := by omega
        simpa only [one_mul] using Nat.mul_le_mul_right t hone
      have hvalue_gap := strictMono_nat_gap hx hrank
      have hxy : x ((j : ℕ) * t) ≤ x ((i : ℕ) * t) := hx.monotone hrank
      change (t : ℝ) ≤
        |(x ((i : ℕ) * t) : ℝ) - (x ((j : ℕ) * t) : ℝ)|
      rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hxy)),
        ← Nat.cast_sub hxy]
      exact_mod_cast hrank_gap.trans hvalue_gap
  have hvval (i : Fin (d + 1)) : |f.eval (v i)| ≤ Y := by
    simpa only [v] using hval ((i : ℕ) * t) (hindex i)
  have hvdist (i : Fin (d + 1)) : |z - v i| ≤ H := by
    obtain ⟨hilow, hihigh⟩ := hsample ((i : ℕ) * t) (hindex i)
    have hilow' : (A : ℝ) ≤ (x ((i : ℕ) * t) : ℝ) := by exact_mod_cast hilow
    have hihigh' : (x ((i : ℕ) * t) : ℝ) ≤ (A + H : ℕ) := by
      exact_mod_cast hihigh
    change |z - (x ((i : ℕ) * t) : ℝ)| ≤ (H : ℝ)
    rw [abs_le]
    constructor <;> push_cast at hihigh' hz ⊢ <;> linarith
  have hbase := lagrange_bound_of_separated f hdeg v hv
    (R := (t : ℝ)) (Y := Y) (H := (H : ℝ))
    (by exact_mod_cast ht_pos) hY (by positivity) hsep hvval hvdist
  have hU_pos : (0 : ℝ) < U := by exact_mod_cast (hden_pos.trans_le hden_le)
  have ht_pos_real : (0 : ℝ) < t := by exact_mod_cast ht_pos
  have hUt_nat : U ≤ 2 * (d + 1) * t := by
    have hlt := Nat.lt_div_mul_add (a := U) (b := d + 1) hden_pos
    dsimp [t] at hlt ⊢
    nlinarith
  have hUt : (U : ℝ) ≤ 2 * (d + 1 : ℝ) * t := by
    exact_mod_cast hUt_nat
  have hratio0 :
      (H : ℝ) / t ≤ 2 * (d + 1 : ℝ) * H / U := by
    apply (le_div_iff₀ hU_pos).2
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ ht_pos_real).2
    have hmul := mul_le_mul_of_nonneg_left hUt (show (0 : ℝ) ≤ H by positivity)
    nlinarith
  have hratio :
      (H : ℝ) / t ≤
        2 * (d + 1 : ℝ) * (1 + (H : ℝ) / U) := by
    calc
      (H : ℝ) / t ≤ 2 * (d + 1 : ℝ) * H / U := hratio0
      _ ≤ 2 * (d + 1 : ℝ) * (1 + (H : ℝ) / U) := by
        have : (0 : ℝ) ≤ 2 * (d + 1 : ℝ) := by positivity
        rw [mul_div_assoc]
        nlinarith
  calc
    |f.eval z| ≤ (d + 1) * Y * ((H : ℝ) / t) ^ d := hbase
    _ ≤ (d + 1) * Y *
        (2 * (d + 1 : ℝ) * (1 + (H : ℝ) / U)) ^ d := by
      gcongr
    _ = samplingConstant d * Y * (1 + (H : ℝ) / U) ^ d := by
      unfold samplingConstant
      rw [mul_pow]
      ring

/-- Finite-set form of the sampling lemma.  The `Finset` itself supplies the
distinctness of the integer samples. -/
theorem polynomial_sampling_finset {d A H : ℕ}
    (f : Polynomial ℝ) (hdeg : f.natDegree ≤ d)
    (samples : Finset ℕ) (hcard : 2 * d + 1 ≤ samples.card)
    (hsample : ∀ n ∈ samples, A ≤ n ∧ n ≤ A + H)
    {Y : ℝ} (hY : 0 ≤ Y)
    (hval : ∀ n ∈ samples, |f.eval (n : ℝ)| ≤ Y)
    {z : ℝ} (hz : (A : ℝ) ≤ z ∧ z ≤ A + H) :
    |f.eval z| ≤ samplingConstant d * Y *
      (1 + (H : ℝ) / samples.card) ^ d := by
  have hcard_pos : 0 < samples.card := by omega
  let e : Fin samples.card ↪o ℕ := samples.orderEmbOfFin rfl
  let x : ℕ → ℕ := extendFiniteOrderEmbedding e hcard_pos
  have hx : StrictMono x := extendFiniteOrderEmbedding_strictMono e hcard_pos
  have hx_eq (i : ℕ) (hi : i < samples.card) : x i = e ⟨i, hi⟩ :=
    extendFiniteOrderEmbedding_apply_lt e hcard_pos hi
  have hsamples_seq :
      ∀ i < samples.card, A ≤ x i ∧ x i ≤ A + H := by
    intro i hi
    have hmem : e ⟨i, hi⟩ ∈ samples :=
      samples.orderEmbOfFin_mem rfl ⟨i, hi⟩
    simpa only [hx_eq i hi] using hsample _ hmem
  have hval_seq :
      ∀ i < samples.card, |f.eval (x i : ℝ)| ≤ Y := by
    intro i hi
    have hmem : e ⟨i, hi⟩ ∈ samples :=
      samples.orderEmbOfFin_mem rfl ⟨i, hi⟩
    simpa only [hx_eq i hi] using hval _ hmem
  exact polynomial_sampling_sequence hcard f hdeg x hx hsamples_seq hY hval_seq hz

/-- Formula label `eq:fibre`, exposing the integral-fibre conclusion under
the same explicit sequence interface used in its proof. -/
theorem eq_fibre {d K H : ℕ} (hd : 0 < d)
    (P : Polynomial ℚ) (hdeg : P.natDegree = d)
    (x : ℕ → ℕ) (hx : StrictMono x) (y : ℕ → ℤ)
    (hy : ∀ i < K, P.eval (x i : ℚ) = (y i : ℚ))
    (hdiam : x (K - 1) - x 0 ≤ H) :
    (K : ℝ) ≤ d + d * H / leadingDenominatorScale P d :=
  integralFiber_sequence_bound hd P hdeg x hx y hy hdiam

/-- Manuscript lemma `lem:sampling`, bundling its sampling and integral-fibre
parts without asymptotic notation. -/
theorem lem_sampling {d U A H K : ℕ} (hd : 0 < d)
    (hU : 2 * d + 1 ≤ U)
    (f : Polynomial ℝ) (hfdeg : f.natDegree ≤ d)
    (samples : ℕ → ℕ) (hsamplesMono : StrictMono samples)
    (hsample : ∀ i < U, A ≤ samples i ∧ samples i ≤ A + H)
    {Y : ℝ} (hY : 0 ≤ Y)
    (hval : ∀ i < U, |f.eval (samples i : ℝ)| ≤ Y)
    {z : ℝ} (hz : (A : ℝ) ≤ z ∧ z ≤ A + H)
    (P : Polynomial ℚ) (hPdeg : P.natDegree = d)
    (fibre : ℕ → ℕ) (hfibreMono : StrictMono fibre)
    (values : ℕ → ℤ)
    (hvalues : ∀ i < K, P.eval (fibre i : ℚ) = (values i : ℚ))
    (hdiam : fibre (K - 1) - fibre 0 ≤ H) :
    |f.eval z| ≤ samplingConstant d * Y * (1 + (H : ℝ) / U) ^ d ∧
      (K : ℝ) ≤ d + d * H / leadingDenominatorScale P d := by
  exact ⟨polynomial_sampling_sequence hU f hfdeg samples hsamplesMono
      hsample hY hval hz,
    eq_fibre hd P hPdeg fibre hfibreMono values hvalues hdiam⟩

/-! ## Discrete polynomial sublevel sets -/

/-- Product factorization over `ℂ` forces every small-value point to lie near
at least one root. -/
theorem exists_root_norm_le_sublevelRadius {d : ℕ} (hd : 0 < d)
    (p : Polynomial ℂ) (hp : p ≠ 0) (hdeg : p.natDegree = d)
    {z : ℂ} {Y : ℝ} (hY : 0 ≤ Y) (heval : ‖p.eval z‖ ≤ Y) :
    ∃ r ∈ p.roots,
      ‖z - r‖ ≤ (Y / ‖p.leadingCoeff‖) ^ ((d : ℝ)⁻¹) := by
  let roots := p.roots
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hroot_card : roots.card = d := by
    dsimp [roots]
    rw [← hdeg]
    exact hsplits.natDegree_eq_card_roots.symm
  have hroots_ne : roots ≠ 0 := by
    intro hzero
    have : roots.card = 0 := by simp [hzero]
    omega
  have hlc_ne : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hlc_pos : 0 < ‖p.leadingCoeff‖ := norm_pos_iff.mpr hlc_ne
  have hnorm_prod :
      ‖(roots.map fun r => z - r).prod‖ =
        (roots.map fun r => ‖z - r‖).prod := by
    induction roots using Multiset.induction_on with
    | empty => simp
    | @cons r roots ih => simp [ih]
  have hnorm_eval :
      ‖p.eval z‖ = ‖p.leadingCoeff‖ *
        (roots.map fun r => ‖z - r‖).prod := by
    rw [hsplits.eval_eq_prod_roots, norm_mul]
    exact congrArg (fun u : ℝ => ‖p.leadingCoeff‖ * u) hnorm_prod
  have hprod_le :
      (roots.map fun r => ‖z - r‖).prod ≤ Y / ‖p.leadingCoeff‖ := by
    apply (le_div_iff₀ hlc_pos).2
    rw [mul_comm, ← hnorm_eval]
    exact heval
  let R : ℝ := (Y / ‖p.leadingCoeff‖) ^ ((d : ℝ)⁻¹)
  have hratio_nonneg : 0 ≤ Y / ‖p.leadingCoeff‖ :=
    div_nonneg hY hlc_pos.le
  have hR_pow : R ^ d = Y / ‖p.leadingCoeff‖ := by
    dsimp [R]
    exact Real.rpow_inv_natCast_pow hratio_nonneg hd.ne'
  by_contra hnear
  push Not at hnear
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hconst : (roots.map fun _r => R).prod = R ^ roots.card := by
    induction roots using Multiset.induction_on with
    | empty => simp
    | @cons r roots ih => simp [pow_succ']
  have hstrict :
      (roots.map fun _r => R).prod <
        (roots.map fun r => ‖z - r‖).prod := by
    rcases hR_nonneg.eq_or_lt with hR_zero | hR_pos
    · rw [← hR_zero] at hconst ⊢
      have hcard_pos : 0 < roots.card := by omega
      rw [hconst, zero_pow hcard_pos.ne']
      exact Multiset.prod_pos (fun u hu => by
        obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hu
        exact hR_zero.trans_lt (hnear r hr))
    · exact Multiset.prod_map_lt_prod_map hroots_ne
        (fun _r => R) (fun r => ‖z - r‖)
        (fun _r _ => hR_pos) (fun r hr => hnear r hr)
  have hR_lt : R ^ d < (roots.map fun r => ‖z - r‖).prod := by
    rw [hconst, hroot_card] at hstrict
    exact hstrict
  rw [hR_pow] at hR_lt
  exact (not_lt_of_ge hprod_le) hR_lt

/-- At most `1 + 2R` distinct integers can lie within real distance `R` of
one centre. -/
theorem int_finset_card_le_center_radius (s : Finset ℤ) {c R : ℝ}
    (hR : 0 ≤ R) (hs : ∀ n ∈ s, |(n : ℝ) - c| ≤ R) :
    (s.card : ℝ) ≤ 1 + 2 * R := by
  by_cases hempty : s = ∅
  · subst s
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hs_nonempty : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let lo : ℤ := s.min' hs_nonempty
  let hi : ℤ := s.max' hs_nonempty
  have hlo_mem : lo ∈ s := s.min'_mem hs_nonempty
  have hhi_mem : hi ∈ s := s.max'_mem hs_nonempty
  have hlohi : lo ≤ hi := s.min'_le_max' hs_nonempty
  have hsubset : s ⊆ Finset.Icc lo hi := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨s.min'_le n hn, s.le_max' n hn⟩
  have hcard_nat : s.card ≤ (Finset.Icc lo hi).card :=
    Finset.card_le_card hsubset
  have hcard_int : (s.card : ℤ) ≤ hi + 1 - lo := by
    have hcast : (s.card : ℤ) ≤ ((Finset.Icc lo hi).card : ℤ) := by
      exact_mod_cast hcard_nat
    have hIcc : ((Finset.Icc lo hi).card : ℤ) = hi + 1 - lo :=
      Int.card_Icc_of_le lo hi (by omega)
    exact hcast.trans_eq hIcc
  have hcard_real : (s.card : ℝ) ≤ (hi : ℝ) + 1 - (lo : ℝ) := by
    exact_mod_cast hcard_int
  have hlo := abs_le.mp (hs lo hlo_mem)
  have hhi := abs_le.mp (hs hi hhi_mem)
  exact hcard_real.trans (by linarith)

/-- Integer points in `[L,U]` on which a real polynomial has absolute value
at most `Y`. -/
def integerSublevelSet (f : Polynomial ℝ) (L U : ℤ) (Y : ℝ) : Finset ℤ :=
  (Finset.Icc L U).filter fun n => |f.eval (n : ℝ)| ≤ Y

theorem mem_integerSublevelSet_iff {f : Polynomial ℝ} {L U n : ℤ} {Y : ℝ} :
    n ∈ integerSublevelSet f L U Y ↔
      L ≤ n ∧ n ≤ U ∧ |f.eval (n : ℝ)| ≤ Y := by
  simp [integerSublevelSet, and_assoc]

/-- The exact discrete sublevel estimate `eq:sublevel`. -/
theorem integerSublevelSet_card_bound {d : ℕ} (hd : 0 < d)
    (f : Polynomial ℝ) (hf : f ≠ 0) (hdeg : f.natDegree = d)
    (L U : ℤ) {Y : ℝ} (hY : 0 ≤ Y) :
    ((integerSublevelSet f L U Y).card : ℝ) ≤
      d + 2 * d *
        (Y / |f.leadingCoeff|) ^ ((d : ℝ)⁻¹) := by
  classical
  let p : Polynomial ℂ := f.map Complex.ofRealHom
  have hp : p ≠ 0 := by
    dsimp [p]
    exact (Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr hf
  have hpdeg : p.natDegree = d := by
    dsimp [p]
    simpa using hdeg
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hroots_card : p.roots.card = d := by
    rw [← hpdeg]
    exact hsplits.natDegree_eq_card_roots.symm
  let roots : Finset ℂ := p.roots.toFinset
  have hroots_nonempty : roots.Nonempty := by
    have hmulti : p.roots ≠ 0 := by
      intro hzero
      have : p.roots.card = 0 := by simp [hzero]
      omega
    obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hmulti
    exact ⟨r, by simpa only [roots, Multiset.mem_toFinset] using hr⟩
  have hroots_fin_card : roots.card ≤ d := by
    exact p.roots.toFinset_card_le.trans_eq hroots_card
  let sublevel := integerSublevelSet f L U Y
  let R : ℝ := (Y / |f.leadingCoeff|) ^ ((d : ℝ)⁻¹)
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hlc_norm : ‖p.leadingCoeff‖ = |f.leadingCoeff| := by
    dsimp [p]
    rw [Polynomial.leadingCoeff_map Complex.ofRealHom]
    simp only [Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs]
  have hnear (n : ℤ) (hn : n ∈ sublevel) :
      ∃ r ∈ roots, |(n : ℝ) - r.re| ≤ R := by
    have hn' : n ∈ integerSublevelSet f L U Y := by simpa only [sublevel] using hn
    have heval_real := (mem_integerSublevelSet_iff.mp hn').2.2
    let evalReal : ℝ := Polynomial.eval (n : ℝ) f
    have heval_complex : ‖p.eval ((n : ℝ) : ℂ)‖ ≤ Y := by
      have heq : p.eval ((n : ℝ) : ℂ) = (evalReal : ℂ) := by
        change (f.map Complex.ofRealHom).eval (Complex.ofRealHom (n : ℝ)) =
          Complex.ofRealHom evalReal
        dsimp only [evalReal]
        exact Polynomial.eval_map_apply (p := f) (f := Complex.ofRealHom) (n : ℝ)
      rw [heq, Complex.norm_real, Real.norm_eq_abs]
      simpa only [evalReal] using heval_real
    obtain ⟨r, hr, hrnear⟩ :=
      exists_root_norm_le_sublevelRadius hd p hp hpdeg hY heval_complex
    refine ⟨r, ?_, ?_⟩
    · simpa only [roots, Multiset.mem_toFinset] using hr
    · have hre : |(n : ℝ) - r.re| ≤ ‖((n : ℝ) : ℂ) - r‖ := by
        simpa only [Complex.sub_re, Complex.ofReal_re] using
          Complex.abs_re_le_norm (((n : ℝ) : ℂ) - r)
      dsimp [R]
      rw [← hlc_norm]
      exact hre.trans hrnear
  let root0 : ℂ := Classical.choose hroots_nonempty
  have hroot0_mem : root0 ∈ roots := Classical.choose_spec hroots_nonempty
  let assign : ℤ → ℂ := fun n =>
    if hn : n ∈ sublevel then Classical.choose (hnear n hn) else root0
  have hassign_mem (n : ℤ) (hn : n ∈ sublevel) : assign n ∈ roots := by
    simp only [assign, dif_pos hn]
    exact (Classical.choose_spec (hnear n hn)).1
  have hassign_near (n : ℤ) (hn : n ∈ sublevel) :
      |(n : ℝ) - (assign n).re| ≤ R := by
    simp only [assign, dif_pos hn]
    exact (Classical.choose_spec (hnear n hn)).2
  have hpartition :
      sublevel.card =
        ∑ r ∈ roots, (sublevel.filter fun n => assign n = r).card := by
    exact Finset.card_eq_sum_card_fiberwise
      (fun n hn => hassign_mem n hn)
  have hpartition_real :
      (sublevel.card : ℝ) =
        ∑ r ∈ roots,
          ((sublevel.filter fun n => assign n = r).card : ℝ) := by
    exact_mod_cast hpartition
  have hfiber (r : ℂ) (hr : r ∈ roots) :
      ((sublevel.filter fun n => assign n = r).card : ℝ) ≤ 1 + 2 * R := by
    apply int_finset_card_le_center_radius _ hR_nonneg
    intro n hn
    have hn_sub : n ∈ sublevel := (Finset.mem_filter.mp hn).1
    have hn_assign : assign n = r := (Finset.mem_filter.mp hn).2
    simpa only [hn_assign] using hassign_near n hn_sub
  calc
    ((integerSublevelSet f L U Y).card : ℝ) = (sublevel.card : ℝ) := by rfl
    _ = ∑ r ∈ roots,
          ((sublevel.filter fun n => assign n = r).card : ℝ) := hpartition_real
    _ ≤ ∑ _r ∈ roots, (1 + 2 * R) := by
      gcongr with r hr
      exact hfiber r hr
    _ = (roots.card : ℝ) * (1 + 2 * R) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d : ℝ) * (1 + 2 * R) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hroots_fin_card
      · positivity
    _ = d + 2 * d *
          (Y / |f.leadingCoeff|) ^ ((d : ℝ)⁻¹) := by
      dsimp [R]
      ring

/-- Formula label `eq:sublevel`. -/
theorem eq_sublevel {d : ℕ} (hd : 0 < d)
    (f : Polynomial ℝ) (hf : f ≠ 0) (hdeg : f.natDegree = d)
    (L U : ℤ) {Y : ℝ} (hY : 0 ≤ Y) :
    ((integerSublevelSet f L U Y).card : ℝ) ≤
      d + 2 * d * (Y / |f.leadingCoeff|) ^ ((d : ℝ)⁻¹) :=
  integerSublevelSet_card_bound hd f hf hdeg L U hY

end Erdos260.PolynomialWindow
