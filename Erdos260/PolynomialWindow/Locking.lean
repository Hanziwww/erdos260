import Erdos260.PolynomialWindow.Windows
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.LinearAlgebra.Lagrange

/-!
# Polynomial graph locking

This file contains the algebraic core of polynomial locking.  A graph carries
an explicit positive natural denominator and an integer-coefficient polynomial
witness; no opaque integer-valued-polynomial object is introduced.
-/

noncomputable section

open scoped BigOperators

namespace Erdos260.PolynomialWindow

namespace CarrySeries

/-- A fixed positive gap word realized from a support point. -/
def GapWordAt (D : CarrySeries) : ℕ → Erdos260.GapWord → Prop
  | _x, [] => True
  | x, g :: gs => D.IsSupportGap x g ∧ D.GapWordAt (x + g) gs

theorem GapWordAt.positive {D : CarrySeries} {x : ℕ}
    {gaps : Erdos260.GapWord} (h : D.GapWordAt x gaps) :
    Erdos260.GapWord.Positive gaps := by
  induction gaps generalizing x with
  | nil => simp [Erdos260.GapWord.Positive]
  | cons g gs ih =>
      simp only [GapWordAt] at h
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact h.1.1
      · exact ih h.2 q hq

theorem GapWordAt.append_left {D : CarrySeries} {x : ℕ}
    (left right : Erdos260.GapWord)
    (h : D.GapWordAt x (left ++ right)) :
    D.GapWordAt x left := by
  induction left generalizing x with
  | nil => trivial
  | cons g gs ih =>
      simp only [List.cons_append, GapWordAt] at h ⊢
      exact ⟨h.1, ih h.2⟩

theorem GapWordAt.prefix {D : CarrySeries} {x : ℕ}
    {left right : Erdos260.GapWord} (hprefix : left.IsPrefix right)
    (h : D.GapWordAt x right) :
    D.GapWordAt x left := by
  obtain ⟨tail, rfl⟩ := hprefix
  exact GapWordAt.append_left left tail h

theorem GapWordAt.append_iff {D : CarrySeries} {x : ℕ}
    (left right : Erdos260.GapWord) :
    D.GapWordAt x (left ++ right) ↔
      D.GapWordAt x left ∧
        D.GapWordAt (x + Erdos260.GapWord.span left) right := by
  induction left generalizing x with
  | nil => simp [GapWordAt, Erdos260.GapWord.span]
  | cons g gs ih =>
      simp only [List.cons_append, GapWordAt,
        Erdos260.GapWord.span, List.sum_cons]
      rw [ih]
      constructor
      · rintro ⟨hgap, hleft, hright⟩
        exact ⟨⟨hgap, hleft⟩, by
          simpa only [Erdos260.GapWord.span, add_assoc] using hright⟩
      · rintro ⟨⟨hgap, hleft⟩, hright⟩
        exact ⟨hgap, hleft, by
          simpa only [Erdos260.GapWord.span, add_assoc] using hright⟩

/-- Consecutive gaps from the canonical positive-support enumeration are a
genuine carry gap word. -/
theorem gapWordAt_enumeration (D : CarrySeries) (i n : ℕ) :
    D.GapWordAt (D.positiveEnumeration.a i)
      (Erdos260.enumerationGapWord D.positiveEnumeration i n) := by
  induction n generalizing i with
  | zero => simp [Erdos260.enumerationGapWord, GapWordAt]
  | succ n ih =>
      rw [Erdos260.enumerationGapWord_succ]
      simp only [GapWordAt]
      refine ⟨D.positiveEnumeration_gap_isSupportGap i, ?_⟩
      have hmono :
          D.positiveEnumeration.a i ≤ D.positiveEnumeration.a (i + 1) :=
        D.positiveEnumeration.strictMono.monotone (by omega)
      have hstep :
          D.positiveEnumeration.a i +
              Erdos260.supportGap D.positiveEnumeration i =
            D.positiveEnumeration.a (i + 1) := by
        unfold Erdos260.supportGap
        omega
      rw [hstep]
      exact ih (i + 1)

theorem carry_across_gap (D : CarrySeries) {x g : ℕ}
    (hgap : D.IsSupportGap x g) :
    D.carry (x + g) =
      (D.base : ℤ) ^ g * D.carry x -
        (D.denominator : ℤ) * intPolynomialValue D.weight (x + g) := by
  have hg : 0 < g := hgap.1
  have hinside := D.carry_inside_gap x g hgap (g - 1) (by omega)
  rw [show x + g = (x + (g - 1)) + 1 by omega, D.carry_succ,
    hinside]
  have hend : x + g ∈ D.support := hgap.2.2.1
  have hdigit : supportDigitInt D.support (x + g) = 1 := by
    simp [supportDigitInt, hend]
  rw [show x + (g - 1) + 1 = x + g by omega, hdigit, mul_one]
  have hpow : (D.base : ℤ) ^ g =
      (D.base : ℤ) * (D.base : ℤ) ^ (g - 1) := by
    calc
      (D.base : ℤ) ^ g = (D.base : ℤ) ^ ((g - 1) + 1) := by
        congr 1
        omega
      _ = (D.base : ℤ) ^ (g - 1) * (D.base : ℤ) := by rw [pow_succ]
      _ = _ := by ring
  rw [hpow]
  ring

end CarrySeries

/-- Translate an integral polynomial by a natural amount. -/
def translateIntPolynomial (w : Polynomial ℤ) (h : ℕ) : Polynomial ℤ :=
  w.comp (Polynomial.X - Polynomial.C (h : ℤ))

theorem eval_translateIntPolynomial_of_le (w : Polynomial ℤ)
    {h y : ℕ} (hhy : h ≤ y) :
    (translateIntPolynomial w h).eval (y : ℤ) =
      intPolynomialValue w (y - h) := by
  simp only [translateIntPolynomial, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, intPolynomialValue]
  congr 1
  exact_mod_cast (Nat.cast_sub hhy : ((y - h : ℕ) : ℤ) = (y : ℤ) - h)

/-- Polynomial correction attached to a positive gap word, written as a
polynomial in its terminal coordinate. -/
def wordCorrection (b : ℕ) (w : Polynomial ℤ) :
    Erdos260.GapWord → Polynomial ℤ
  | [] => 0
  | _g :: gs =>
      wordCorrection b w gs +
        (b : ℤ) ^ Erdos260.GapWord.span gs •
          translateIntPolynomial w (Erdos260.GapWord.span gs)

theorem wordCorrection_degree_le (b : ℕ) (w : Polynomial ℤ)
    (gaps : Erdos260.GapWord) :
    (wordCorrection b w gaps).natDegree ≤ w.natDegree := by
  induction gaps with
  | nil => simp [wordCorrection]
  | cons g gs ih =>
      simp only [wordCorrection]
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · exact ih
      · apply (Polynomial.natDegree_smul_le _ _).trans
        rw [translateIntPolynomial, Polynomial.natDegree_comp]
        rw [Polynomial.natDegree_X_sub_C]
        simp

theorem eval_wordCorrection_cons (b : ℕ) (w : Polynomial ℤ)
    (g : ℕ) (gs : Erdos260.GapWord) (x : ℕ) :
    (wordCorrection b w (g :: gs)).eval
        (x + g + Erdos260.GapWord.span gs : ℤ) =
      (wordCorrection b w gs).eval
          (x + g + Erdos260.GapWord.span gs : ℤ) +
        (b : ℤ) ^ Erdos260.GapWord.span gs *
          intPolynomialValue w (x + g) := by
  simp only [wordCorrection, Polynomial.eval_add, Polynomial.eval_smul,
    smul_eq_mul]
  have htranslate := eval_translateIntPolynomial_of_le w
    (h := Erdos260.GapWord.span gs)
    (y := x + g + Erdos260.GapWord.span gs) (by omega)
  have hcast :
      ((x + g + Erdos260.GapWord.span gs : ℕ) : ℤ) =
        (x : ℤ) + g + Erdos260.GapWord.span gs := by push_cast; ring
  rw [← hcast, htranslate]
  rw [show x + g + Erdos260.GapWord.span gs -
    Erdos260.GapWord.span gs = x + g by omega]

namespace CarrySeries

/-- Formula label `eq:wordrec`: iteration of the carry recurrence along an
actual gap word. -/
theorem carry_word_recurrence (D : CarrySeries) {x : ℕ}
    {gaps : Erdos260.GapWord} (hword : D.GapWordAt x gaps) :
    D.carry (x + Erdos260.GapWord.span gaps) +
        (D.denominator : ℤ) *
          (wordCorrection D.base D.weight gaps).eval
            (x + Erdos260.GapWord.span gaps : ℤ) =
      (D.base : ℤ) ^ Erdos260.GapWord.span gaps * D.carry x := by
  induction gaps generalizing x with
  | nil => simp [wordCorrection, Erdos260.GapWord.span]
  | cons g gs ih =>
      simp only [GapWordAt] at hword
      have hrec := ih hword.2
      have hacross := D.carry_across_gap hword.1
      have heval := eval_wordCorrection_cons D.base D.weight g gs x
      simp only [Erdos260.GapWord.span, List.sum_cons] at heval ⊢
      have harg :
          (x : ℤ) + (g + gs.sum : ℕ) =
            (x : ℤ) + (g : ℤ) + (gs.sum : ℤ) := by push_cast; ring
      rw [harg, heval]
      rw [show x + (g + gs.sum) = x + g + gs.sum by omega]
      have hrec' :
          D.carry (x + g + gs.sum) +
              (D.denominator : ℤ) *
                (wordCorrection D.base D.weight gs).eval
                  ((x : ℤ) + g + gs.sum) =
            (D.base : ℤ) ^ gs.sum * D.carry (x + g) := by
        simpa only [Erdos260.GapWord.span, Nat.cast_add, add_assoc] using hrec
      calc
        D.carry (x + g + gs.sum) +
            (D.denominator : ℤ) *
              ((wordCorrection D.base D.weight gs).eval
                  ((x : ℤ) + g + gs.sum) +
                (D.base : ℤ) ^ gs.sum *
                  intPolynomialValue D.weight (x + g)) =
            (D.carry (x + g + gs.sum) +
              (D.denominator : ℤ) *
                (wordCorrection D.base D.weight gs).eval
                  ((x : ℤ) + g + gs.sum)) +
              (D.base : ℤ) ^ gs.sum *
                ((D.denominator : ℤ) *
                  intPolynomialValue D.weight (x + g)) := by ring
        _ = (D.base : ℤ) ^ gs.sum * D.carry (x + g) +
              (D.base : ℤ) ^ gs.sum *
                ((D.denominator : ℤ) *
                  intPolynomialValue D.weight (x + g)) := by rw [hrec']
        _ = (D.base : ℤ) ^ gs.sum *
              ((D.base : ℤ) ^ g * D.carry x -
                (D.denominator : ℤ) *
                  intPolynomialValue D.weight (x + g)) +
              (D.base : ℤ) ^ gs.sum *
                ((D.denominator : ℤ) *
                  intPolynomialValue D.weight (x + g)) := by rw [hacross]
        _ = (D.base : ℤ) ^ (g + gs.sum) * D.carry x := by
          rw [pow_add]
          ring

/-- Formula label `eq:wordrec`. -/
theorem eq_wordrec (D : CarrySeries) {x : ℕ}
    {gaps : Erdos260.GapWord} (hword : D.GapWordAt x gaps) :
    D.carry (x + Erdos260.GapWord.span gaps) +
        (D.denominator : ℤ) *
          (wordCorrection D.base D.weight gaps).eval
            (x + Erdos260.GapWord.span gaps : ℤ) =
      (D.base : ℤ) ^ Erdos260.GapWord.span gaps * D.carry x :=
  D.carry_word_recurrence hword

end CarrySeries

/-! ## Highest-coefficient state -/

/-- Normalized top state. -/
def topState (A θ : ℚ) : ℚ := θ / A

/-- Formula label `eq:topmap`. -/
theorem topState_update {A θ : ℚ} (hA : A ≠ 0) (b g : ℕ) :
    topState A ((b : ℚ) ^ g * θ - A) =
      (b : ℚ) ^ g * topState A θ - 1 := by
  unfold topState
  field_simp

/-- Apply the normalized top-state map successively along a gap word. -/
def topStateAlong (b : ℕ) : Erdos260.GapWord → ℝ → ℝ
  | [], μ => μ
  | g :: gs, μ => topStateAlong b gs ((b : ℝ) ^ g * μ - 1)

@[simp]
theorem topStateAlong_nil (b : ℕ) (μ : ℝ) :
    topStateAlong b [] μ = μ := rfl

@[simp]
theorem topStateAlong_cons (b g : ℕ) (gs : Erdos260.GapWord) (μ : ℝ) :
    topStateAlong b (g :: gs) μ =
      topStateAlong b gs ((b : ℝ) ^ g * μ - 1) := rfl

theorem topStateAlong_append (b : ℕ)
    (left right : Erdos260.GapWord) (μ : ℝ) :
    topStateAlong b (left ++ right) μ =
      topStateAlong b right (topStateAlong b left μ) := by
  induction left generalizing μ with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.cons_append, topStateAlong]
      exact ih ((b : ℝ) ^ g * μ - 1)

/-- Rational version of the normalized top-state trajectory. -/
def topStateAlongRat (b : ℕ) : Erdos260.GapWord → ℚ → ℚ
  | [], μ => μ
  | g :: gs, μ => topStateAlongRat b gs ((b : ℚ) ^ g * μ - 1)

@[simp]
theorem topStateAlongRat_nil (b : ℕ) (μ : ℚ) :
    topStateAlongRat b [] μ = μ := rfl

@[simp]
theorem topStateAlongRat_cons (b g : ℕ) (gs : Erdos260.GapWord) (μ : ℚ) :
    topStateAlongRat b (g :: gs) μ =
      topStateAlongRat b gs ((b : ℚ) ^ g * μ - 1) := rfl

theorem topStateAlongRat_append (b : ℕ)
    (left right : Erdos260.GapWord) (μ : ℚ) :
    topStateAlongRat b (left ++ right) μ =
      topStateAlongRat b right (topStateAlongRat b left μ) := by
  induction left generalizing μ with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.cons_append, topStateAlongRat]
      exact ih ((b : ℚ) ^ g * μ - 1)

/-- The rational and real top-state trajectories agree under coercion. -/
theorem topStateAlongRat_cast (b : ℕ) (gaps : Erdos260.GapWord) (μ : ℚ) :
    ((topStateAlongRat b gaps μ : ℚ) : ℝ) =
      topStateAlong b gaps (μ : ℝ) := by
  induction gaps generalizing μ with
  | nil => rfl
  | cons g gs ih =>
      simp only [topStateAlongRat, topStateAlong_cons]
      calc
        ((topStateAlongRat b gs ((b : ℚ) ^ g * μ - 1) : ℚ) : ℝ) =
            topStateAlong b gs (((b : ℚ) ^ g * μ - 1 : ℚ) : ℝ) :=
          ih ((b : ℚ) ^ g * μ - 1)
        _ = topStateAlong b gs ((b : ℝ) ^ g * (μ : ℝ) - 1) := by
          congr 1
          norm_num

/-- Interior highest-coefficient state. -/
def InteriorState (b : ℕ) (μ : ℝ) : Prop :=
  0 < (b - 1 : ℝ) * μ ∧ (b - 1 : ℝ) * μ < 1

/-- Strict exterior highest-coefficient state. -/
def StrictExteriorState (b : ℕ) (μ : ℝ) : Prop :=
  μ < 0 ∨ 1 < (b - 1 : ℝ) * μ

theorem interior_successor_unique {b : ℕ} (hb : 2 ≤ b) {μ : ℝ}
    {g h : ℕ} (_hg : 0 < g) (_hh : 0 < h)
    (hμ : InteriorState b μ)
    (hgInt : InteriorState b ((b : ℝ) ^ g * μ - 1))
    (hhInt : InteriorState b ((b : ℝ) ^ h * μ - 1)) : g = h := by
  have hbReal : (1 : ℝ) < b := by exact_mod_cast hb
  have hbminus : (0 : ℝ) < b - 1 := by linarith
  have hμpos : 0 < μ := pos_of_mul_pos_right hμ.1 hbminus.le
  have hinterval (r : ℕ)
      (hrInt : InteriorState b ((b : ℝ) ^ r * μ - 1)) :
      1 < (b : ℝ) ^ r * μ ∧
        (b : ℝ) ^ r * μ < (b : ℝ) / (b - 1 : ℝ) := by
    constructor
    · nlinarith [hrInt.1]
    · apply (lt_div_iff₀ hbminus).mpr
      nlinarith [hrInt.2]
  have hgI := hinterval g hgInt
  have hhI := hinterval h hhInt
  rcases lt_trichotomy g h with hlt | heq | hgt
  · have hpow : (b : ℝ) ^ (g + 1) ≤ (b : ℝ) ^ h := by
      exact pow_le_pow_right₀ hbReal.le (by omega)
    have hmul : (b : ℝ) * ((b : ℝ) ^ g * μ) ≤
        (b : ℝ) ^ h * μ := by
      calc
        (b : ℝ) * ((b : ℝ) ^ g * μ) =
            (b : ℝ) ^ (g + 1) * μ := by rw [pow_succ']; ring
        _ ≤ (b : ℝ) ^ h * μ :=
          mul_le_mul_of_nonneg_right hpow hμpos.le
    have hupper : (b : ℝ) / (b - 1 : ℝ) ≤ b := by
      have hbTwo : (2 : ℝ) ≤ b := by exact_mod_cast hb
      have hbminusOne : (1 : ℝ) ≤ b - 1 := by linarith
      exact div_le_self (by positivity) hbminusOne
    have hlower : (b : ℝ) < (b : ℝ) * ((b : ℝ) ^ g * μ) := by
      simpa only [mul_one] using
        mul_lt_mul_of_pos_left hgI.1 (show (0 : ℝ) < b by positivity)
    linarith [hhI.2, hmul, hupper, hlower]
  · exact heq
  · have hpow : (b : ℝ) ^ (h + 1) ≤ (b : ℝ) ^ g := by
      exact pow_le_pow_right₀ hbReal.le (by omega)
    have hmul : (b : ℝ) * ((b : ℝ) ^ h * μ) ≤
        (b : ℝ) ^ g * μ := by
      calc
        (b : ℝ) * ((b : ℝ) ^ h * μ) =
            (b : ℝ) ^ (h + 1) * μ := by rw [pow_succ']; ring
        _ ≤ (b : ℝ) ^ g * μ :=
          mul_le_mul_of_nonneg_right hpow hμpos.le
    have hupper : (b : ℝ) / (b - 1 : ℝ) ≤ b := by
      have hbTwo : (2 : ℝ) ≤ b := by exact_mod_cast hb
      have hbminusOne : (1 : ℝ) ≤ b - 1 := by linarith
      exact div_le_self (by positivity) hbminusOne
    have hlower : (b : ℝ) < (b : ℝ) * ((b : ℝ) ^ h * μ) := by
      simpa only [mul_one] using
        mul_lt_mul_of_pos_left hhI.1 (show (0 : ℝ) < b by positivity)
    linarith [hgI.2, hmul, hupper, hlower]

theorem lowerExterior_forward {b g : ℕ} (hb : 2 ≤ b) {μ : ℝ}
    (hμ : μ < 0) : (b : ℝ) ^ g * μ - 1 < 0 := by
  have hpow : 0 < (b : ℝ) ^ g := by positivity
  nlinarith

theorem upperExterior_forward {b g : ℕ} (hb : 2 ≤ b) (hg : 0 < g)
    {μ : ℝ} (hμ : 1 < (b - 1 : ℝ) * μ) :
    1 < (b - 1 : ℝ) * ((b : ℝ) ^ g * μ - 1) := by
  have hbReal : (1 : ℝ) < b := by exact_mod_cast hb
  have hpow : (b : ℝ) ≤ (b : ℝ) ^ g := by
    calc
      (b : ℝ) = (b : ℝ) ^ 1 := by simp
      _ ≤ (b : ℝ) ^ g := pow_le_pow_right₀ hbReal.le (by omega)
  have hE : 0 < (b - 1 : ℝ) * μ - 1 := by linarith
  have hidentity :
      (b - 1 : ℝ) * ((b : ℝ) ^ g * μ - 1) - 1 =
        (b : ℝ) ^ g * ((b - 1 : ℝ) * μ - 1) +
          ((b : ℝ) ^ g - b) := by ring
  have hpos :
      0 < (b - 1 : ℝ) * ((b : ℝ) ^ g * μ - 1) - 1 := by
    rw [hidentity]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (pow_pos (zero_lt_one.trans hbReal) _) hE)
      (sub_nonneg.mpr hpow)
  linarith

/-- Algebraic core used later in the full window-span theorem
`lem:dichotomy`. -/
theorem lem_dichotomy_algebraic (b : ℕ) (hb : 2 ≤ b) :
    (∀ μ : ℝ, InteriorState b μ → ∀ g h : ℕ, 0 < g → 0 < h →
      InteriorState b ((b : ℝ) ^ g * μ - 1) →
      InteriorState b ((b : ℝ) ^ h * μ - 1) → g = h) ∧
    (∀ μ : ℝ, μ < 0 → ∀ g : ℕ,
      (b : ℝ) ^ g * μ - 1 < 0) ∧
    (∀ μ : ℝ, 1 < (b - 1 : ℝ) * μ → ∀ g : ℕ, 0 < g →
      1 < (b - 1 : ℝ) * ((b : ℝ) ^ g * μ - 1)) := by
  exact ⟨fun _ hμ _ _ hg hh hgI hhI =>
      interior_successor_unique hb hg hh hμ hgI hhI,
    fun _ hμ _ => lowerExterior_forward hb hμ,
    fun _ hμ _ hg => upperExterior_forward hb hg hμ⟩

/-! ## Finite-span interior--exterior dichotomy -/

/-- The two boundary states omitted by `InteriorState` and
`StrictExteriorState`. -/
def BoundaryState (b : ℕ) (μ : ℝ) : Prop :=
  (b - 1 : ℝ) * μ = 0 ∨ (b - 1 : ℝ) * μ = 1

theorem state_trichotomy (b : ℕ) (hb : 2 ≤ b) (μ : ℝ) :
    InteriorState b μ ∨ BoundaryState b μ ∨ StrictExteriorState b μ := by
  let t : ℝ := (b - 1 : ℝ) * μ
  by_cases ht0 : 0 < t
  · by_cases ht1 : t < 1
    · exact Or.inl ⟨ht0, ht1⟩
    · have h1t : 1 ≤ t := le_of_not_gt ht1
      rcases eq_or_lt_of_le h1t with hEq | hLt
      · exact Or.inr (Or.inl (Or.inr hEq.symm))
      · exact Or.inr (Or.inr (Or.inr hLt))
  · have ht0' : t ≤ 0 := le_of_not_gt ht0
    rcases eq_or_lt_of_le ht0' with hEq | hLt
    · exact Or.inr (Or.inl (Or.inl hEq))
    · have hbminus : (0 : ℝ) < b - 1 := by
        have hbReal : (2 : ℝ) ≤ b := by exact_mod_cast hb
        linarith
      have hμ : μ < 0 := by
        by_contra hnot
        have hμ0 : 0 ≤ μ := le_of_not_gt hnot
        exact (not_lt_of_ge (mul_nonneg hbminus.le hμ0)) hLt
      exact Or.inr (Or.inr (Or.inl hμ))

theorem interior_not_boundary {b : ℕ} {μ : ℝ}
    (h : InteriorState b μ) : ¬BoundaryState b μ := by
  intro hboundary
  rcases hboundary with hzero | hone <;> linarith [h.1, h.2]

theorem interior_not_strictExterior {b : ℕ} (hb : 2 ≤ b) {μ : ℝ}
    (h : InteriorState b μ) : ¬StrictExteriorState b μ := by
  have hbminus : (0 : ℝ) < b - 1 := by
    have hbReal : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  intro hexterior
  rcases hexterior with hneg | hupp
  · have hμpos : 0 < μ := pos_of_mul_pos_right h.1 hbminus.le
    linarith
  · linarith [h.2]

theorem boundary_not_strictExterior {b : ℕ} (hb : 2 ≤ b) {μ : ℝ}
    (h : BoundaryState b μ) : ¬StrictExteriorState b μ := by
  have hbminus : (0 : ℝ) < b - 1 := by
    have hbReal : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  intro hexterior
  rcases h with hzero | hone
  · have hμ : μ = 0 := (mul_eq_zero.mp hzero).resolve_left hbminus.ne'
    rcases hexterior with hneg | hupp
    · norm_num [hμ] at hneg
    · norm_num [hμ] at hupp
  · rcases hexterior with hneg | hupp
    · have hμpos : 0 < μ := by
        apply pos_of_mul_pos_right (show 0 < (b - 1 : ℝ) * μ by linarith)
        exact hbminus.le
      linarith
    · linarith

theorem strictExterior_forward {b g : ℕ} (hb : 2 ≤ b) (hg : 0 < g)
    {μ : ℝ} (hμ : StrictExteriorState b μ) :
    StrictExteriorState b ((b : ℝ) ^ g * μ - 1) := by
  rcases hμ with hlow | hupp
  · exact Or.inl (lowerExterior_forward hb hlow)
  · exact Or.inr (upperExterior_forward hb hg hupp)

theorem lowerBoundary_forward {b g : ℕ} (hb : 2 ≤ b) {μ : ℝ}
    (hμ : (b - 1 : ℝ) * μ = 0) :
    StrictExteriorState b ((b : ℝ) ^ g * μ - 1) := by
  have hbminus : (0 : ℝ) < b - 1 := by
    have hbReal : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hμzero : μ = 0 := (mul_eq_zero.mp hμ).resolve_left hbminus.ne'
  left
  simp [hμzero]

theorem upperBoundary_forward_one {b : ℕ} (_hb : 2 ≤ b) {μ : ℝ}
    (hμ : (b - 1 : ℝ) * μ = 1) :
    BoundaryState b ((b : ℝ) ^ (1 : ℕ) * μ - 1) := by
  right
  have hid :
      (b - 1 : ℝ) * ((b : ℝ) ^ (1 : ℕ) * μ - 1) =
        (b : ℝ) * ((b - 1 : ℝ) * μ) - (b - 1 : ℝ) := by
    rw [pow_one]
    ring
  rw [hid, hμ]
  ring

theorem upperBoundary_forward_large {b g : ℕ} (hb : 2 ≤ b) (hg : 1 < g)
    {μ : ℝ} (hμ : (b - 1 : ℝ) * μ = 1) :
    StrictExteriorState b ((b : ℝ) ^ g * μ - 1) := by
  right
  have hbReal : (1 : ℝ) < b := by exact_mod_cast hb
  have hpow : (b : ℝ) < (b : ℝ) ^ g := by
    calc
      (b : ℝ) = (b : ℝ) ^ (1 : ℕ) := by simp
      _ < (b : ℝ) ^ g := pow_lt_pow_right₀ hbReal hg
  have hid :
      (b - 1 : ℝ) * ((b : ℝ) ^ g * μ - 1) - 1 =
        (b : ℝ) ^ g * ((b - 1 : ℝ) * μ - 1) +
          ((b : ℝ) ^ g - b) := by ring
  have hdiff :
      0 < (b - 1 : ℝ) * ((b : ℝ) ^ g * μ - 1) - 1 := by
    rw [hid, hμ]
    simpa using hpow
  linarith

/-- Total span of gaps whose starting state is interior. -/
noncomputable def interiorSpanAlong (b : ℕ) :
    Erdos260.GapWord → ℝ → ℕ
  | [], _μ => 0
  | g :: gs, μ => by
      classical
      exact (if InteriorState b μ then g else 0) +
        interiorSpanAlong b gs ((b : ℝ) ^ g * μ - 1)

/-- Total span of gaps whose starting state is a boundary state. -/
noncomputable def boundarySpanAlong (b : ℕ) :
    Erdos260.GapWord → ℝ → ℕ
  | [], _μ => 0
  | g :: gs, μ => by
      classical
      exact (if BoundaryState b μ then g else 0) +
        boundarySpanAlong b gs ((b : ℝ) ^ g * μ - 1)

/-- Total span of gaps whose starting state is strictly exterior.  Forward
invariance below shows that these gaps form a suffix. -/
noncomputable def exteriorSpanAlong (b : ℕ) :
    Erdos260.GapWord → ℝ → ℕ
  | [], _μ => 0
  | g :: gs, μ => by
      classical
      exact (if StrictExteriorState b μ then g else 0) +
        exteriorSpanAlong b gs ((b : ℝ) ^ g * μ - 1)

theorem boundarySpanAlong_eq_zero_of_strictExterior {b : ℕ} (hb : 2 ≤ b)
    {gaps : Erdos260.GapWord} (hpositive : Erdos260.GapWord.Positive gaps)
    {μ : ℝ} (hμ : StrictExteriorState b μ) :
    boundarySpanAlong b gaps μ = 0 := by
  induction gaps generalizing μ with
  | nil => simp [boundarySpanAlong]
  | cons g gs ih =>
      have hg : 0 < g := hpositive g (by simp)
      have hgs : Erdos260.GapWord.Positive gs := by
        intro h hh
        exact hpositive h (by simp [hh])
      have hnot : ¬BoundaryState b μ := by
        exact fun hboundary => boundary_not_strictExterior hb hboundary hμ
      have hnext := strictExterior_forward hb hg hμ
      simp [boundarySpanAlong, hnot, ih hgs hnext]

theorem interiorSpanAlong_eq_zero_of_strictExterior {b : ℕ} (hb : 2 ≤ b)
    {gaps : Erdos260.GapWord} (hpositive : Erdos260.GapWord.Positive gaps)
    {μ : ℝ} (hμ : StrictExteriorState b μ) :
    interiorSpanAlong b gaps μ = 0 := by
  induction gaps generalizing μ with
  | nil => simp [interiorSpanAlong]
  | cons g gs ih =>
      have hg : 0 < g := hpositive g (by simp)
      have hgs : Erdos260.GapWord.Positive gs := by
        intro h hh
        exact hpositive h (by simp [hh])
      have hnot : ¬InteriorState b μ := by
        intro hinterior
        exact interior_not_strictExterior hb hinterior hμ
      have hnext := strictExterior_forward hb hg hμ
      simp [interiorSpanAlong, hnot, ih hgs hnext]

/-- Boundary states never return to the open interior region. -/
theorem interiorSpanAlong_eq_zero_of_boundary {b : ℕ} (hb : 2 ≤ b)
    {gaps : Erdos260.GapWord} (hpositive : Erdos260.GapWord.Positive gaps)
    {μ : ℝ} (hμ : BoundaryState b μ) :
    interiorSpanAlong b gaps μ = 0 := by
  induction gaps generalizing μ with
  | nil => simp [interiorSpanAlong]
  | cons g gs ih =>
      have hg : 0 < g := hpositive g (by simp)
      have hgs : Erdos260.GapWord.Positive gs := by
        intro q hq
        exact hpositive q (by simp [hq])
      have hnot : ¬InteriorState b μ := fun h => interior_not_boundary h hμ
      rcases hμ with hlower | hupper
      · have hnext := lowerBoundary_forward (g := g) hb hlower
        have htail := interiorSpanAlong_eq_zero_of_strictExterior hb hgs hnext
        simp [interiorSpanAlong, hnot, htail]
      · by_cases hgOne : g = 1
        · subst g
          have hnext := upperBoundary_forward_one hb hupper
          have htail := ih hgs hnext
          simpa [interiorSpanAlong, hnot] using htail
        · have hgLarge : 1 < g := by omega
          have hnext := upperBoundary_forward_large hb hgLarge hupper
          have htail := interiorSpanAlong_eq_zero_of_strictExterior hb hgs hnext
          simp [interiorSpanAlong, hnot, htail]

/-- Longest initial word whose starting state and every state after an
included gap remain strictly interior. -/
noncomputable def interiorTrajectory (b : ℕ) :
    Erdos260.GapWord → ℝ → Erdos260.GapWord
  | [], _μ => []
  | g :: gs, μ => by
      classical
      let ν := (b : ℝ) ^ g * μ - 1
      exact if InteriorState b μ ∧ InteriorState b ν then
        g :: interiorTrajectory b gs ν
      else []

theorem interiorTrajectory_isPrefix (b : ℕ)
    (gaps : Erdos260.GapWord) (μ : ℝ) :
    (interiorTrajectory b gaps μ).IsPrefix gaps := by
  induction gaps generalizing μ with
  | nil => simp [interiorTrajectory]
  | cons g gs ih =>
      let ν := (b : ℝ) ^ g * μ - 1
      by_cases hboth : InteriorState b μ ∧ InteriorState b ν
      · obtain ⟨tail, htail⟩ := ih ν
        refine ⟨tail, ?_⟩
        simpa [interiorTrajectory, ν, hboth] using congrArg (List.cons g) htail
      · simp [interiorTrajectory, ν, hboth]

theorem interiorTrajectory_positive {b : ℕ}
    {gaps : Erdos260.GapWord} (hpositive : Erdos260.GapWord.Positive gaps)
    (μ : ℝ) :
    Erdos260.GapWord.Positive (interiorTrajectory b gaps μ) := by
  intro g hg
  exact hpositive g ((interiorTrajectory_isPrefix b gaps μ).mem hg)

theorem interiorTrajectory_start {b : ℕ}
    {gaps : Erdos260.GapWord} {μ : ℝ}
    (hne : interiorTrajectory b gaps μ ≠ []) :
    InteriorState b μ := by
  cases gaps with
  | nil => exact (hne rfl).elim
  | cons g gs =>
      let ν := (b : ℝ) ^ g * μ - 1
      by_cases hboth : InteriorState b μ ∧ InteriorState b ν
      · exact hboth.1
      · have hempty : interiorTrajectory b (g :: gs) μ = [] := by
          simp [interiorTrajectory, ν, hboth]
        exact (hne hempty).elim

/-- Every vertex of the selected trajectory, including its terminal vertex,
is strictly interior. -/
theorem interiorTrajectory_state {b : ℕ}
    (gaps : Erdos260.GapWord) {μ : ℝ} (hμ : InteriorState b μ)
    (i : ℕ) (hi : i ≤ (interiorTrajectory b gaps μ).length) :
    InteriorState b
      (topStateAlong b ((interiorTrajectory b gaps μ).take i) μ) := by
  induction gaps generalizing μ i with
  | nil =>
      have hi0 : i = 0 := by simpa [interiorTrajectory] using hi
      subst i
      simpa [interiorTrajectory] using hμ
  | cons g gs ih =>
      let ν := (b : ℝ) ^ g * μ - 1
      by_cases hν : InteriorState b ν
      · have hboth : InteriorState b μ ∧ InteriorState b ν := ⟨hμ, hν⟩
        cases i with
        | zero => simpa [interiorTrajectory] using hμ
        | succ i =>
            have hiTail : i ≤ (interiorTrajectory b gs ν).length := by
              simpa [interiorTrajectory, ν, hboth] using hi
            have htail := ih hν i hiTail
            simpa [interiorTrajectory, ν, hboth, topStateAlong] using htail
      · have hboth : ¬(InteriorState b μ ∧ InteriorState b ν) := by
          intro h
          exact hν h.2
        have hi0 : i = 0 := by
          simpa [interiorTrajectory, ν, hboth] using hi
        subst i
        simpa [interiorTrajectory, ν, hboth] using hμ

/-- Two genuine all-vertices-interior trajectories with the same initial
state have the same prefix at every length available in both trajectories.
This is the proof-bearing form of deterministic interior continuation. -/
theorem interiorTrajectory_take_eq {b : ℕ} (hb : 2 ≤ b)
    (left right : Erdos260.GapWord) (μ : ℝ) (r : ℕ)
    (hleftPositive : Erdos260.GapWord.Positive left)
    (hrightPositive : Erdos260.GapWord.Positive right)
    (hleft : r ≤ (interiorTrajectory b left μ).length)
    (hright : r ≤ (interiorTrajectory b right μ).length) :
    (interiorTrajectory b left μ).take r =
      (interiorTrajectory b right μ).take r := by
  induction r generalizing left right μ with
  | zero => rfl
  | succ r ih =>
      cases left with
      | nil => simp [interiorTrajectory] at hleft
      | cons g gs =>
          cases right with
          | nil => simp [interiorTrajectory] at hright
          | cons h hs =>
              let νg : ℝ := (b : ℝ) ^ g * μ - 1
              let νh : ℝ := (b : ℝ) ^ h * μ - 1
              have hbothg : InteriorState b μ ∧ InteriorState b νg := by
                by_contra hnot
                simp [interiorTrajectory, νg, hnot] at hleft
              have hbothh : InteriorState b μ ∧ InteriorState b νh := by
                by_contra hnot
                simp [interiorTrajectory, νh, hnot] at hright
              have hgpos : 0 < g := hleftPositive g (by simp)
              have hhpos : 0 < h := hrightPositive h (by simp)
              have hgh : g = h := interior_successor_unique hb hgpos hhpos
                hbothg.1 hbothg.2 hbothh.2
              subst h
              have hleftTail : r ≤
                  (interiorTrajectory b gs νg).length := by
                simpa [interiorTrajectory, νg, hbothg] using hleft
              have hrightTail : r ≤
                  (interiorTrajectory b hs νg).length := by
                have hbothh' : InteriorState b μ ∧ InteriorState b νg := hbothh
                simpa [interiorTrajectory, νg, hbothh'] using hright
              have hgsPositive : Erdos260.GapWord.Positive gs := by
                intro q hq
                exact hleftPositive q (by simp [hq])
              have hhsPositive : Erdos260.GapWord.Positive hs := by
                intro q hq
                exact hrightPositive q (by simp [hq])
              have htail := ih gs hs νg hgsPositive hhsPositive
                hleftTail hrightTail
              simpa [interiorTrajectory, νg, hbothg] using
                congrArg (List.cons g) htail

/-- Deterministic interior continuations from the same state are comparable
by the prefix order. -/
theorem interiorTrajectory_prefix_or_prefix {b : ℕ} (hb : 2 ≤ b)
    (left right : Erdos260.GapWord) (μ : ℝ)
    (hleftPositive : Erdos260.GapWord.Positive left)
    (hrightPositive : Erdos260.GapWord.Positive right) :
    (interiorTrajectory b left μ).IsPrefix
        (interiorTrajectory b right μ) ∨
      (interiorTrajectory b right μ).IsPrefix
        (interiorTrajectory b left μ) := by
  by_cases hlen :
      (interiorTrajectory b left μ).length ≤
        (interiorTrajectory b right μ).length
  · left
    apply List.prefix_iff_eq_take.mpr
    simpa only [List.take_length] using
      interiorTrajectory_take_eq hb left right μ
        (interiorTrajectory b left μ).length
        hleftPositive hrightPositive le_rfl hlen
  · right
    have hlen' :
        (interiorTrajectory b right μ).length ≤
          (interiorTrajectory b left μ).length := by omega
    apply List.prefix_iff_eq_take.mpr
    simpa only [List.take_length] using
      interiorTrajectory_take_eq hb right left μ
        (interiorTrajectory b right μ).length
        hrightPositive hleftPositive le_rfl hlen'

/-- A word all of whose vertices are interior is exactly the canonical
interior trajectory selected from itself. -/
theorem interiorTrajectory_eq_self_of_prefix_states {b : ℕ}
    (gaps : Erdos260.GapWord) (μ : ℝ)
    (hstates : ∀ i : ℕ, i ≤ gaps.length →
      InteriorState b (topStateAlong b (gaps.take i) μ)) :
    interiorTrajectory b gaps μ = gaps := by
  induction gaps generalizing μ with
  | nil => rfl
  | cons g gs ih =>
      let ν : ℝ := (b : ℝ) ^ g * μ - 1
      have hμ : InteriorState b μ := by
        simpa [topStateAlong] using hstates 0 (by simp)
      have hν : InteriorState b ν := by
        simpa [ν, topStateAlong] using hstates 1 (by simp)
      have htailStates : ∀ i : ℕ, i ≤ gs.length →
          InteriorState b (topStateAlong b (gs.take i) ν) := by
        intro i hi
        have h := hstates (i + 1) (by simp; omega)
        simpa [ν, topStateAlong] using h
      have htail := ih ν htailStates
      simp [interiorTrajectory, ν, hμ, hν, htail]

/-- Replacing the total interior span by the genuine all-vertices-interior
trajectory loses at most its one transition gap. -/
theorem interiorSpanAlong_le_trajectory_add_cap {b cap : ℕ} (hb : 2 ≤ b)
    {gaps : Erdos260.GapWord} (hpositive : Erdos260.GapWord.Positive gaps)
    (hcap : ∀ g ∈ gaps, g ≤ cap) (μ : ℝ) :
    interiorSpanAlong b gaps μ ≤
      Erdos260.GapWord.span (interiorTrajectory b gaps μ) + cap := by
  induction gaps generalizing μ with
  | nil => simp [interiorSpanAlong, interiorTrajectory,
      Erdos260.GapWord.span]
  | cons g gs ih =>
      have hg : 0 < g := hpositive g (by simp)
      have hgcap : g ≤ cap := hcap g (by simp)
      have hgs : Erdos260.GapWord.Positive gs := by
        intro q hq
        exact hpositive q (by simp [hq])
      have hcapgs : ∀ q ∈ gs, q ≤ cap := by
        intro q hq
        exact hcap q (by simp [hq])
      let ν := (b : ℝ) ^ g * μ - 1
      by_cases hμ : InteriorState b μ
      · by_cases hν : InteriorState b ν
        · have htail := ih hgs hcapgs ν
          have hν' : InteriorState b ((b : ℝ) ^ g * μ - 1) := by
            simpa only [ν] using hν
          have htail' :
              interiorSpanAlong b gs ((b : ℝ) ^ g * μ - 1) ≤
                Erdos260.GapWord.span
                    (interiorTrajectory b gs ((b : ℝ) ^ g * μ - 1)) + cap := by
            simpa only [ν] using htail
          change interiorSpanAlong b gs ((b : ℝ) ^ g * μ - 1) ≤
              (interiorTrajectory b gs ((b : ℝ) ^ g * μ - 1)).sum + cap
            at htail'
          simp only [interiorSpanAlong, hμ, if_pos]
          rw [show interiorTrajectory b (g :: gs) μ =
              g :: interiorTrajectory b gs ((b : ℝ) ^ g * μ - 1) by
            simp [interiorTrajectory, hμ, hν']]
          simp only [Erdos260.GapWord.span, List.sum_cons]
          omega
        · have htailZero : interiorSpanAlong b gs ν = 0 := by
            rcases state_trichotomy b hb ν with hνInt | hνBoundary | hνExt
            · exact (hν hνInt).elim
            · exact interiorSpanAlong_eq_zero_of_boundary hb hgs hνBoundary
            · exact interiorSpanAlong_eq_zero_of_strictExterior hb hgs hνExt
          have hν' : ¬InteriorState b ((b : ℝ) ^ g * μ - 1) := by
            simpa only [ν] using hν
          have htailZero' :
              interiorSpanAlong b gs ((b : ℝ) ^ g * μ - 1) = 0 := by
            simpa only [ν] using htailZero
          simp [interiorSpanAlong, interiorTrajectory, hμ, hν',
            htailZero', Erdos260.GapWord.span]
          omega
      · have hzero : interiorSpanAlong b (g :: gs) μ = 0 := by
          rcases state_trichotomy b hb μ with hμInt | hμBoundary | hμExt
          · exact (hμ hμInt).elim
          · exact interiorSpanAlong_eq_zero_of_boundary hb hpositive hμBoundary
          · exact interiorSpanAlong_eq_zero_of_strictExterior hb hpositive hμExt
        simp [hzero]

theorem exteriorSpanAlong_eq_span_of_strictExterior {b : ℕ} (hb : 2 ≤ b)
    {gaps : Erdos260.GapWord} (hpositive : Erdos260.GapWord.Positive gaps)
    {μ : ℝ} (hμ : StrictExteriorState b μ) :
    exteriorSpanAlong b gaps μ = Erdos260.GapWord.span gaps := by
  induction gaps generalizing μ with
  | nil => simp [exteriorSpanAlong, Erdos260.GapWord.span]
  | cons g gs ih =>
      have hg : 0 < g := hpositive g (by simp)
      have hgs : Erdos260.GapWord.Positive gs := by
        intro h hh
        exact hpositive h (by simp [hh])
      have hnext := strictExterior_forward hb hg hμ
      simp [exteriorSpanAlong, Erdos260.GapWord.span, hμ, ih hgs hnext]

/-- Boundary states can consume only unit gaps, apart from the one gap that
exits the boundary. -/
theorem boundarySpanAlong_le_cap_add_length {b cap : ℕ} (hb : 2 ≤ b)
    {gaps : Erdos260.GapWord} (hpositive : Erdos260.GapWord.Positive gaps)
    (hcap : ∀ g ∈ gaps, g ≤ cap) (μ : ℝ) :
    boundarySpanAlong b gaps μ ≤ cap + gaps.length := by
  induction gaps generalizing μ with
  | nil => simp [boundarySpanAlong]
  | cons g gs ih =>
      have hg : 0 < g := hpositive g (by simp)
      have hgcap : g ≤ cap := hcap g (by simp)
      have hgs : Erdos260.GapWord.Positive gs := by
        intro h hh
        exact hpositive h (by simp [hh])
      have hcapgs : ∀ h ∈ gs, h ≤ cap := by
        intro h hh
        exact hcap h (by simp [hh])
      by_cases hboundary : BoundaryState b μ
      · rcases hboundary with hlower | hupper
        · have hboundary' : BoundaryState b μ := Or.inl hlower
          have hnext := lowerBoundary_forward (g := g) hb hlower
          have htail := boundarySpanAlong_eq_zero_of_strictExterior hb hgs hnext
          simp [boundarySpanAlong, hboundary', htail]
          omega
        · have hboundary' : BoundaryState b μ := Or.inr hupper
          by_cases hgOne : g = 1
          · subst g
            have hnext := upperBoundary_forward_one hb hupper
            have htail := ih hgs hcapgs
              ((b : ℝ) ^ (1 : ℕ) * μ - 1)
            have htail' :
                boundarySpanAlong b gs ((b : ℝ) * μ - 1) ≤
                  cap + gs.length := by
              simpa only [pow_one] using htail
            rw [boundarySpanAlong]
            simp only [if_pos hboundary', pow_one, List.length_cons]
            omega
          · have hgLarge : 1 < g := by omega
            have hnext := upperBoundary_forward_large hb hgLarge hupper
            have htail := boundarySpanAlong_eq_zero_of_strictExterior hb hgs hnext
            simp [boundarySpanAlong, hboundary', htail]
            omega
      · have htail := ih hgs hcapgs ((b : ℝ) ^ g * μ - 1)
        simp [boundarySpanAlong, hboundary]
        omega

theorem classifiedSpanAlong (b : ℕ) (hb : 2 ≤ b)
    (gaps : Erdos260.GapWord) (μ : ℝ) :
    interiorSpanAlong b gaps μ + boundarySpanAlong b gaps μ +
        exteriorSpanAlong b gaps μ = Erdos260.GapWord.span gaps := by
  induction gaps generalizing μ with
  | nil => simp [interiorSpanAlong, boundarySpanAlong, exteriorSpanAlong,
      Erdos260.GapWord.span]
  | cons g gs ih =>
      rcases state_trichotomy b hb μ with hinterior | hboundary | hexterior
      · have hnBoundary := interior_not_boundary hinterior
        have hnExterior := interior_not_strictExterior hb hinterior
        have ihnext := ih ((b : ℝ) ^ g * μ - 1)
        simpa [interiorSpanAlong, boundarySpanAlong, exteriorSpanAlong,
          Erdos260.GapWord.span, hinterior, hnBoundary, hnExterior,
          add_assoc, add_comm, add_left_comm] using
            congrArg (fun n : ℕ => g + n) ihnext
      · have hnInterior : ¬InteriorState b μ := by
          exact fun h => interior_not_boundary h hboundary
        have hnExterior := boundary_not_strictExterior hb hboundary
        have ihnext := ih ((b : ℝ) ^ g * μ - 1)
        simpa [interiorSpanAlong, boundarySpanAlong, exteriorSpanAlong,
          Erdos260.GapWord.span, hboundary, hnInterior, hnExterior,
          add_assoc, add_comm, add_left_comm] using
            congrArg (fun n : ℕ => g + n) ihnext
      · have hnInterior : ¬InteriorState b μ := by
          exact fun h => interior_not_strictExterior hb h hexterior
        have hnBoundary : ¬BoundaryState b μ := by
          exact fun h => boundary_not_strictExterior hb h hexterior
        have ihnext := ih ((b : ℝ) ^ g * μ - 1)
        simpa [interiorSpanAlong, boundarySpanAlong, exteriorSpanAlong,
          Erdos260.GapWord.span, hexterior, hnInterior, hnBoundary,
          add_assoc, add_comm, add_left_comm] using
            congrArg (fun n : ℕ => g + n) ihnext

/-- Manuscript lemma `lem:dichotomy`, in exact finite-span form.  The
hypothesis says that the explicit boundary loss is at most half the available
span.  The exterior part is a suffix by
`exteriorSpanAlong_eq_span_of_strictExterior`. -/
theorem lem_dichotomy {b cap : ℕ} (hb : 2 ≤ b)
    {gaps : Erdos260.GapWord} (hpositive : Erdos260.GapWord.Positive gaps)
    (hcap : ∀ g ∈ gaps, g ≤ cap) (μ : ℝ)
    (hlong : 2 * (cap + gaps.length) ≤ Erdos260.GapWord.span gaps) :
    (∀ ν : ℝ, InteriorState b ν → ∀ g h : ℕ, 0 < g → 0 < h →
        InteriorState b ((b : ℝ) ^ g * ν - 1) →
        InteriorState b ((b : ℝ) ^ h * ν - 1) → g = h) ∧
      (Erdos260.GapWord.span gaps ≤ 4 * interiorSpanAlong b gaps μ ∨
        Erdos260.GapWord.span gaps ≤ 4 * exteriorSpanAlong b gaps μ) := by
  constructor
  · exact (lem_dichotomy_algebraic b hb).1
  · have hboundary :=
      boundarySpanAlong_le_cap_add_length hb hpositive hcap μ
    have hpartition := classifiedSpanAlong b hb gaps μ
    omega

/-- A rational polynomial graph of degree at most `d`, together with a
positive denominator certificate in the ordinary monomial basis. -/
structure PolynomialGraph (d : ℕ) where
  poly : Polynomial ℚ
  degree_le : poly.natDegree ≤ d
  denominator : ℕ
  denominator_pos : 0 < denominator
  integralPoly : Polynomial ℤ
  certificate :
    integralPoly.map (algebraMap ℤ ℚ) =
      (denominator : ℚ) • poly

namespace PolynomialGraph

theorem denominator_ne_zero {d : ℕ} (G : PolynomialGraph d) :
    G.denominator ≠ 0 := G.denominator_pos.ne'

theorem integral_value_certificate {d : ℕ} (G : PolynomialGraph d)
    (n : ℤ) :
    ((G.integralPoly.eval n : ℤ) : ℚ) =
      (G.denominator : ℚ) * G.poly.eval (n : ℚ) := by
  have h := congrArg (fun P : Polynomial ℚ => P.eval (n : ℚ)) G.certificate
  have hcert :
      (G.integralPoly.map (algebraMap ℤ ℚ)).eval (n : ℚ) =
        (G.denominator : ℚ) * G.poly.eval (n : ℚ) := by
    simpa only [Polynomial.eval_smul, smul_eq_mul, Int.cast_natCast] using h
  calc
    ((G.integralPoly.eval n : ℤ) : ℚ) =
        (G.integralPoly.map (algebraMap ℤ ℚ)).eval (n : ℚ) := by
      exact (Polynomial.eval_map_apply (p := G.integralPoly)
        (f := algebraMap ℤ ℚ) n).symm
    _ = _ := hcert

/-- Rational image of an integral weight polynomial. -/
def rationalWeight (w : Polynomial ℤ) : Polynomial ℚ :=
  w.map (algebraMap ℤ ℚ)

theorem rationalWeight_eval_nat (w : Polynomial ℤ) (n : ℕ) :
    (rationalWeight w).eval (n : ℚ) =
      (intPolynomialValue w n : ℚ) := by
  unfold rationalWeight intPolynomialValue
  exact Polynomial.eval_map_apply (p := w)
    (f := algebraMap ℤ ℚ) (n : ℤ)

/-- Transform of a carry graph after appending one gap. -/
def transformPoly {d : ℕ} (G : PolynomialGraph d)
    (b Q g : ℕ) (w : Polynomial ℤ) : Polynomial ℚ :=
  (b : ℚ) ^ g •
      G.poly.comp (Polynomial.X - Polynomial.C (g : ℚ)) -
    (Q : ℚ) • rationalWeight w

/-- Integral certificate transported through the same graph transform. -/
def transformIntegral {d : ℕ} (G : PolynomialGraph d)
    (b Q g : ℕ) (w : Polynomial ℤ) : Polynomial ℤ :=
  (b : ℤ) ^ g •
      G.integralPoly.comp (Polynomial.X - Polynomial.C (g : ℤ)) -
    ((G.denominator * Q : ℕ) : ℤ) • w

theorem transformPoly_degree_le {d : ℕ} (G : PolynomialGraph d)
    (b Q g : ℕ) (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d) :
    (G.transformPoly b Q g w).natDegree ≤ d := by
  unfold transformPoly
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_smul_le _ _).trans
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C]
    simpa using G.degree_le
  · apply (Polynomial.natDegree_smul_le _ _).trans
    rw [rationalWeight]
    exact (Polynomial.natDegree_map_le
      (f := algebraMap ℤ ℚ) (p := w)).trans hwdeg

theorem transform_certificate {d : ℕ} (G : PolynomialGraph d)
    (b Q g : ℕ) (w : Polynomial ℤ) :
    (G.transformIntegral b Q g w).map (algebraMap ℤ ℚ) =
      (G.denominator : ℚ) • G.transformPoly b Q g w := by
  ext n
  simp only [transformIntegral, transformPoly, rationalWeight,
    Polynomial.coeff_map, Polynomial.coeff_sub, Polynomial.coeff_smul,
    Nat.cast_mul, smul_eq_mul]
  push_cast
  have hcert := congrArg (fun P : Polynomial ℚ => P.coeff n) G.certificate
  simp only [Polynomial.coeff_map, Polynomial.coeff_smul] at hcert
  have hcomp :
      (G.integralPoly.comp (Polynomial.X - Polynomial.C (g : ℤ))).map
          (algebraMap ℤ ℚ) =
        (G.integralPoly.map (algebraMap ℤ ℚ)).comp
          (Polynomial.X - Polynomial.C (g : ℚ)) := by
    rw [Polynomial.map_comp]
    congr 1
    simp
  have hcompCoeff := congrArg (fun P : Polynomial ℚ => P.coeff n) hcomp
  rw [G.certificate] at hcompCoeff
  rw [Polynomial.smul_comp] at hcompCoeff
  simp only [Polynomial.coeff_map, Polynomial.coeff_smul, smul_eq_mul]
    at hcompCoeff
  have hcompCoeff' :
      ((G.integralPoly.comp
          (Polynomial.X - Polynomial.C (g : ℤ))).coeff n : ℚ) =
        (G.denominator : ℚ) *
          (G.poly.comp
            (Polynomial.X - Polynomial.C (g : ℚ))).coeff n := by
    exact hcompCoeff
  change (b : ℚ) ^ g *
      ((G.integralPoly.comp
        (Polynomial.X - Polynomial.C (g : ℤ))).coeff n : ℚ) -
      (G.denominator : ℚ) * (Q : ℚ) * (w.coeff n : ℚ) =
    (G.denominator : ℚ) *
      ((b : ℚ) ^ g *
          (G.poly.comp
            (Polynomial.X - Polynomial.C (g : ℚ))).coeff n -
        (Q : ℚ) * (w.coeff n : ℚ))
  rw [hcompCoeff']
  ring

/-- Graph transform with its denominator certificate preserved. -/
def transform {d : ℕ} (G : PolynomialGraph d)
    (b Q g : ℕ) (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d) :
    PolynomialGraph d where
  poly := G.transformPoly b Q g w
  degree_le := G.transformPoly_degree_le b Q g w hwdeg
  denominator := G.denominator
  denominator_pos := G.denominator_pos
  integralPoly := G.transformIntegral b Q g w
  certificate := G.transform_certificate b Q g w

@[simp]
theorem transform_denominator {d : ℕ} (G : PolynomialGraph d)
    (b Q g : ℕ) (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d) :
    (G.transform b Q g w hwdeg).denominator = G.denominator := rfl

theorem transformPoly_eval {d : ℕ} (G : PolynomialGraph d)
    (b Q g : ℕ) (w : Polynomial ℤ) (y : ℚ) :
    (G.transformPoly b Q g w).eval y =
      (b : ℚ) ^ g * G.poly.eval (y - g) -
        (Q : ℚ) * (rationalWeight w).eval y := by
  simp [transformPoly, Polynomial.eval_comp, smul_eq_mul]

/-- A common one-gap graph transform is injective on the underlying rational
polynomial. -/
theorem transformPoly_injective {b Q g : ℕ} (hb : 2 ≤ b)
    (w : Polynomial ℤ) :
    Function.Injective (fun P : Polynomial ℚ =>
      (b : ℚ) ^ g •
          P.comp (Polynomial.X - Polynomial.C (g : ℚ)) -
        (Q : ℚ) • rationalWeight w) := by
  intro P R h
  have hscaled :
      (b : ℚ) ^ g •
          P.comp (Polynomial.X - Polynomial.C (g : ℚ)) =
        (b : ℚ) ^ g •
          R.comp (Polynomial.X - Polynomial.C (g : ℚ)) :=
    sub_left_inj.mp h
  have hscalar : (b : ℚ) ^ g ≠ 0 := by positivity
  have hcomp :
      P.comp (Polynomial.X - Polynomial.C (g : ℚ)) =
        R.comp (Polynomial.X - Polynomial.C (g : ℚ)) := by
    ext n
    have hn := congrArg (fun S : Polynomial ℚ => S.coeff n) hscaled
    simp only [Polynomial.coeff_smul, smul_eq_mul] at hn
    exact mul_left_cancel₀ hscalar hn
  have hinverse := congrArg
    (fun S : Polynomial ℚ => S.comp (Polynomial.X + Polynomial.C (g : ℚ)))
    hcomp
  simpa [Polynomial.comp_assoc] using hinverse

/-- Top-degree coefficient update underlying `eq:topmap`. -/
theorem transformPoly_coeff_of_degree {d : ℕ} (G : PolynomialGraph d)
    (hGdeg : G.poly.natDegree = d)
    (b Q g : ℕ) (w : Polynomial ℤ) (_hwdeg : w.natDegree ≤ d) :
    (G.transformPoly b Q g w).coeff d =
      (b : ℚ) ^ g * G.poly.coeff d -
        (Q : ℚ) * (w.coeff d : ℚ) := by
  have hshiftDegree :
      (G.poly.comp (Polynomial.X - Polynomial.C (g : ℚ))).natDegree = d := by
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, hGdeg]
    simp
  have hshiftLead :
      (G.poly.comp (Polynomial.X - Polynomial.C (g : ℚ))).leadingCoeff =
        G.poly.leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp (by
      rw [Polynomial.natDegree_X_sub_C]
      norm_num), Polynomial.leadingCoeff_X_sub_C, one_pow, mul_one]
  have hshiftCoeff :
      (G.poly.comp (Polynomial.X - Polynomial.C (g : ℚ))).coeff d =
        G.poly.coeff d := by
    have hleft := Polynomial.coeff_natDegree
      (p := G.poly.comp (Polynomial.X - Polynomial.C (g : ℚ)))
    rw [hshiftDegree] at hleft
    have hright := Polynomial.coeff_natDegree (p := G.poly)
    rw [hGdeg] at hright
    exact hleft.trans (hshiftLead.trans hright.symm)
  unfold transformPoly rationalWeight
  simp only [Polynomial.coeff_sub, Polynomial.coeff_smul,
    Polynomial.coeff_map, hshiftCoeff]
  change (b : ℚ) ^ g * G.poly.coeff d -
      (Q : ℚ) * (w.coeff d : ℚ) = _
  ring

/-- Translation by a constant preserves the coefficient at any fixed degree
which bounds the degree of the polynomial. -/
theorem coeff_comp_X_sub_C_of_natDegree_le {d : ℕ} (P : Polynomial ℚ)
    (hPdeg : P.natDegree ≤ d) (g : ℕ) :
    (P.comp (Polynomial.X - Polynomial.C (g : ℚ))).coeff d = P.coeff d := by
  by_cases hdegree : P.natDegree = d
  · have hshiftDegree :
        (P.comp (Polynomial.X - Polynomial.C (g : ℚ))).natDegree = d := by
      rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, hdegree]
      simp
    have hshiftLead :
        (P.comp (Polynomial.X - Polynomial.C (g : ℚ))).leadingCoeff =
          P.leadingCoeff := by
      rw [Polynomial.leadingCoeff_comp (by
        rw [Polynomial.natDegree_X_sub_C]
        norm_num), Polynomial.leadingCoeff_X_sub_C, one_pow, mul_one]
    have hleft := Polynomial.coeff_natDegree
      (p := P.comp (Polynomial.X - Polynomial.C (g : ℚ)))
    rw [hshiftDegree] at hleft
    have hright := Polynomial.coeff_natDegree (p := P)
    rw [hdegree] at hright
    exact hleft.trans (hshiftLead.trans hright.symm)
  · have hPstrict : P.natDegree < d := lt_of_le_of_ne hPdeg hdegree
    have hcompStrict :
        (P.comp (Polynomial.X - Polynomial.C (g : ℚ))).natDegree < d := by
      rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C]
      simpa using hPstrict
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hcompStrict,
      Polynomial.coeff_eq_zero_of_natDegree_lt hPstrict]

/-- Fixed-degree version of the top coefficient update.  It remains valid
when either polynomial has degree strictly below the ambient degree. -/
theorem transformPoly_coeff_of_degree_le {d : ℕ} (G : PolynomialGraph d)
    (b Q g : ℕ) (w : Polynomial ℤ) :
    (G.transformPoly b Q g w).coeff d =
      (b : ℚ) ^ g * G.poly.coeff d -
        (Q : ℚ) * (w.coeff d : ℚ) := by
  unfold transformPoly rationalWeight
  simp only [Polynomial.coeff_sub, Polynomial.coeff_smul,
    Polynomial.coeff_map,
    coeff_comp_X_sub_C_of_natDegree_le G.poly G.degree_le g]
  change (b : ℚ) ^ g * G.poly.coeff d -
      (Q : ℚ) * (w.coeff d : ℚ) = _
  ring

/-- Normalized fixed-degree state of a carry graph. -/
def normalizedTopState {d : ℕ} (G : PolynomialGraph d)
    (Q : ℕ) (w : Polynomial ℤ) : ℚ :=
  topState ((Q : ℚ) * (w.coeff d : ℚ)) (G.poly.coeff d)

/-- The reduced denominator of the normalized top state divides the graph
certificate denominator times the fixed integral leading scale.  This is the
exact arithmetic bridge behind the manuscript estimate `q \ll W^s`. -/
theorem normalizedTopState_den_dvd {d Q : ℕ} (G : PolynomialGraph d)
    (hQ : 0 < Q) (w : Polynomial ℤ) (hw : 0 < w.coeff d) :
    (G.normalizedTopState Q w).den ∣
      G.denominator * Q * (w.coeff d).natAbs := by
  have hcert := congrArg (fun P : Polynomial ℚ => P.coeff d) G.certificate
  simp only [Polynomial.coeff_map, Polynomial.coeff_smul, smul_eq_mul]
    at hcert
  have hwabs : ((w.coeff d).natAbs : ℤ) = w.coeff d := by
    rw [Int.natCast_natAbs, abs_of_pos hw]
  have hwabsQ : ((w.coeff d).natAbs : ℚ) = (w.coeff d : ℚ) := by
    change (((w.coeff d).natAbs : ℤ) : ℚ) = (w.coeff d : ℚ)
    exact_mod_cast hwabs
  have hscaled :
      ((G.denominator * Q * (w.coeff d).natAbs : ℕ) : ℚ) *
          G.normalizedTopState Q w =
        (G.integralPoly.coeff d : ℚ) := by
    unfold normalizedTopState topState
    push_cast
    rw [hwabsQ, div_eq_mul_inv]
    field_simp
    simpa [mul_assoc, mul_comm, mul_left_comm] using hcert.symm
  apply rat_den_dvd_natAbs_of_int_mul_eq_int
    (a := (G.denominator * Q * (w.coeff d).natAbs : ℕ))
    (z := G.integralPoly.coeff d)
  simpa using hscaled

theorem normalizedTopState_den_le {d Q : ℕ} (G : PolynomialGraph d)
    (hQ : 0 < Q) (w : Polynomial ℤ) (hw : 0 < w.coeff d) :
    (G.normalizedTopState Q w).den ≤
      G.denominator * Q * (w.coeff d).natAbs :=
  Nat.le_of_dvd (Nat.mul_pos (Nat.mul_pos G.denominator_pos hQ)
      (Int.natAbs_pos.mpr hw.ne'))
    (G.normalizedTopState_den_dvd hQ w hw)

/-- One graph transform realizes exactly the rational state map
`μ ↦ b^g μ - 1`. -/
theorem normalizedTopState_transform {d : ℕ} (G : PolynomialGraph d)
    (b Q g : ℕ) (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d)
    (hA : (Q : ℚ) * (w.coeff d : ℚ) ≠ 0) :
    normalizedTopState (G.transform b Q g w hwdeg) Q w =
      (b : ℚ) ^ g * normalizedTopState G Q w - 1 := by
  unfold normalizedTopState
  rw [show (G.transform b Q g w hwdeg).poly =
      G.transformPoly b Q g w by rfl,
    transformPoly_coeff_of_degree_le]
  exact topState_update hA b g

/-- Formula label `eq:topmap`. -/
theorem eq_topmap {d : ℕ} (G : PolynomialGraph d)
    (b Q g : ℕ) (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d)
    (hA : (Q : ℚ) * (w.coeff d : ℚ) ≠ 0) :
    normalizedTopState (G.transform b Q g w hwdeg) Q w =
      (b : ℚ) ^ g * normalizedTopState G Q w - 1 :=
  G.normalizedTopState_transform b Q g w hwdeg hA

/-- Formula label `eq:graphden` for an already constructed locked graph. -/
theorem eq_graphden {d H : ℕ} (G : PolynomialGraph d)
    (hden : G.denominator ≤ H ^ vandermondeExponent d) :
    1 ≤ G.denominator ∧
      G.denominator ≤ H ^ vandermondeExponent d ∧
      G.integralPoly.map (algebraMap ℤ ℚ) =
        (G.denominator : ℚ) • G.poly :=
  ⟨G.denominator_pos, hden, G.certificate⟩

theorem integralPoly_degree_le {d : ℕ} (G : PolynomialGraph d) :
    G.integralPoly.natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hPzero : G.poly.coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (G.degree_le.trans_lt hn)
  have hcoeff := congrArg (fun P : Polynomial ℚ => P.coeff n) G.certificate
  simp only [Polynomial.coeff_map, Polynomial.coeff_smul, smul_eq_mul,
    hPzero, mul_zero] at hcoeff
  exact Int.cast_injective hcoeff

/-- Common-denominator integer polynomial for the difference of two locked
graphs. -/
def differenceIntegral {d : ℕ} (G H : PolynomialGraph d) : Polynomial ℤ :=
  (H.denominator : ℤ) • G.integralPoly -
    (G.denominator : ℤ) • H.integralPoly

/-- A common graph transform cancels its polynomial correction in the
difference certificate. -/
theorem differenceIntegral_transform {d : ℕ} (G H : PolynomialGraph d)
    (b Q g : ℕ) (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d) :
    differenceIntegral (G.transform b Q g w hwdeg)
        (H.transform b Q g w hwdeg) =
      (b : ℤ) ^ g •
        (differenceIntegral G H).comp
          (Polynomial.X - Polynomial.C (g : ℤ)) := by
  unfold differenceIntegral transform transformIntegral
  simp only [Polynomial.sub_comp, Polynomial.smul_comp]
  module

/-- Apply a common sequence of gap transforms to a graph. -/
def transformWord {d : ℕ} (G : PolynomialGraph d)
    (b Q : ℕ) (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d) :
    Erdos260.GapWord → PolynomialGraph d
  | [] => G
  | g :: gs => (G.transform b Q g w hwdeg).transformWord b Q w hwdeg gs

@[simp]
theorem transformWord_nil {d : ℕ} (G : PolynomialGraph d)
    (b Q : ℕ) (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d) :
    G.transformWord b Q w hwdeg [] = G := rfl

@[simp]
theorem transformWord_cons {d : ℕ} (G : PolynomialGraph d)
    (b Q g : ℕ) (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d)
    (gs : Erdos260.GapWord) :
    G.transformWord b Q w hwdeg (g :: gs) =
      (G.transform b Q g w hwdeg).transformWord b Q w hwdeg gs := rfl

/-- Sequential graph transforms respect concatenation of gap words. -/
theorem transformWord_append {d : ℕ} (G : PolynomialGraph d)
    (b Q : ℕ) (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d)
    (left right : Erdos260.GapWord) :
    G.transformWord b Q w hwdeg (left ++ right) =
      (G.transformWord b Q w hwdeg left).transformWord b Q w hwdeg right := by
  induction left generalizing G with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.cons_append, transformWord_cons]
      exact ih (G.transform b Q g w hwdeg)

/-- A graph transform depends on a graph certificate only through its
underlying rational polynomial. -/
theorem transform_poly_eq_of_poly_eq {d : ℕ} {G H : PolynomialGraph d}
    (hpoly : G.poly = H.poly) (b Q g : ℕ) (w : Polynomial ℤ)
    (hwdeg : w.natDegree ≤ d) :
    (G.transform b Q g w hwdeg).poly =
      (H.transform b Q g w hwdeg).poly := by
  change G.transformPoly b Q g w = H.transformPoly b Q g w
  unfold transformPoly
  rw [hpoly]

/-- Iterated common transforms preserve equality of the underlying rational
polynomials, independently of the chosen denominator certificates. -/
theorem transformWord_poly_eq_of_poly_eq {d : ℕ} {G H : PolynomialGraph d}
    (hpoly : G.poly = H.poly) (b Q : ℕ) (w : Polynomial ℤ)
    (hwdeg : w.natDegree ≤ d) (gaps : Erdos260.GapWord) :
    (G.transformWord b Q w hwdeg gaps).poly =
      (H.transformWord b Q w hwdeg gaps).poly := by
  induction gaps generalizing G H with
  | nil => exact hpoly
  | cons g gs ih =>
      simp only [transformWord_cons]
      exact ih (G := G.transform b Q g w hwdeg)
        (H := H.transform b Q g w hwdeg)
        (transform_poly_eq_of_poly_eq hpoly b Q g w hwdeg)

@[simp]
theorem transformWord_denominator {d : ℕ} (G : PolynomialGraph d)
    (b Q : ℕ) (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d)
    (gaps : Erdos260.GapWord) :
    (G.transformWord b Q w hwdeg gaps).denominator = G.denominator := by
  induction gaps generalizing G with
  | nil => rfl
  | cons g gs ih =>
      simp only [transformWord_cons]
      rw [ih, transform_denominator]

/-- A common gap word acts on the graph's normalized top coefficient by the
exact iterated rational top-state map. -/
theorem normalizedTopState_transformWord {d : ℕ} (G : PolynomialGraph d)
    (b Q : ℕ) (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d)
    (hA : (Q : ℚ) * (w.coeff d : ℚ) ≠ 0)
    (gaps : Erdos260.GapWord) :
    normalizedTopState (G.transformWord b Q w hwdeg gaps) Q w =
      topStateAlongRat b gaps (normalizedTopState G Q w) := by
  induction gaps generalizing G with
  | nil => rfl
  | cons g gs ih =>
      simp only [transformWord_cons, topStateAlongRat_cons]
      rw [ih, normalizedTopState_transform G b Q g w hwdeg hA]

/-- A locked graph that contains one genuine carry point continues to contain
the genuine carry point after every actual common gap word. -/
theorem transformWord_eval_carry (D : CarrySeries)
    (G : PolynomialGraph D.weight.natDegree) {x : ℕ}
    {gaps : Erdos260.GapWord}
    (hfit : G.poly.eval (x : ℚ) = (D.carry x : ℚ))
    (hword : D.GapWordAt x gaps) :
    (G.transformWord D.base D.denominator D.weight le_rfl gaps).poly.eval
        ((x + Erdos260.GapWord.span gaps : ℕ) : ℚ) =
      (D.carry (x + Erdos260.GapWord.span gaps) : ℚ) := by
  induction gaps generalizing G x with
  | nil => simpa [Erdos260.GapWord.span] using hfit
  | cons g gs ih =>
      simp only [CarrySeries.GapWordAt] at hword
      have hfirst :
          (G.transform D.base D.denominator g D.weight le_rfl).poly.eval
              ((x + g : ℕ) : ℚ) = (D.carry (x + g) : ℚ) := by
        change (G.transformPoly D.base D.denominator g D.weight).eval
            ((x + g : ℕ) : ℚ) = (D.carry (x + g) : ℚ)
        rw [G.transformPoly_eval, rationalWeight_eval_nat]
        have hx : ((x + g : ℕ) : ℚ) - (g : ℚ) = (x : ℚ) := by
          push_cast
          ring
        rw [hx, hfit]
        exact_mod_cast (D.carry_across_gap hword.1).symm
      have htail := ih
        (G.transform D.base D.denominator g D.weight le_rfl)
        hfirst hword.2
      simpa only [transformWord_cons, Erdos260.GapWord.span, List.sum_cons,
        Nat.cast_add, add_assoc] using htail

/-- Scalar divisibility in a graph difference is preserved, with an extra
factor `b^span`, by every common continuation. -/
theorem exists_differenceIntegral_transformWord_factor {d B : ℕ}
    (G H : PolynomialGraph d) (b Q : ℕ) (w : Polynomial ℤ)
    (hwdeg : w.natDegree ≤ d) (gaps : Erdos260.GapWord)
    (K : Polynomial ℤ)
    (hK : differenceIntegral G H = (B : ℤ) • K) :
    ∃ K' : Polynomial ℤ,
      differenceIntegral (G.transformWord b Q w hwdeg gaps)
          (H.transformWord b Q w hwdeg gaps) =
        (((b ^ Erdos260.GapWord.span gaps) * B : ℕ) : ℤ) • K' := by
  induction gaps generalizing G H B K with
  | nil =>
      refine ⟨K, ?_⟩
      simpa [Erdos260.GapWord.span] using hK
  | cons g gs ih =>
      let shift : Polynomial ℤ := Polynomial.X - Polynomial.C (g : ℤ)
      let K₁ : Polynomial ℤ := K.comp shift
      have hfirst :
          differenceIntegral (G.transform b Q g w hwdeg)
              (H.transform b Q g w hwdeg) =
            (((b ^ g) * B : ℕ) : ℤ) • K₁ := by
        rw [differenceIntegral_transform, hK]
        simp only [Polynomial.smul_comp, K₁, shift]
        rw [smul_smul]
        congr 1
      obtain ⟨K', htail⟩ := ih
        (G.transform b Q g w hwdeg) (H.transform b Q g w hwdeg)
        K₁ (B := (b ^ g) * B) hfirst
      refine ⟨K', ?_⟩
      simp only [transformWord_cons, Erdos260.GapWord.span, List.sum_cons]
      rw [htail]
      congr 1
      simp only [Erdos260.GapWord.span]
      rw [pow_add]
      ring_nf

/-- Formula label `eq:divisiblegraphs` at coefficient level. -/
theorem exists_differenceIntegral_transformWord_pow_factor {d : ℕ}
    (G H : PolynomialGraph d) (b Q : ℕ) (w : Polynomial ℤ)
    (hwdeg : w.natDegree ≤ d) (gaps : Erdos260.GapWord) :
    ∃ K : Polynomial ℤ,
      differenceIntegral (G.transformWord b Q w hwdeg gaps)
          (H.transformWord b Q w hwdeg gaps) =
        (b : ℤ) ^ Erdos260.GapWord.span gaps • K := by
  obtain ⟨K, hK⟩ := exists_differenceIntegral_transformWord_factor
    G H b Q w hwdeg gaps (differenceIntegral G H) (B := 1) (by simp)
  refine ⟨K, ?_⟩
  simpa only [mul_one, Int.natCast_pow] using hK

/-- A common continuation is injective on the underlying graph polynomial. -/
theorem transformWord_poly_injective {d b Q : ℕ} (hb : 2 ≤ b)
    (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d)
    (gaps : Erdos260.GapWord) (G H : PolynomialGraph d)
    (hpoly : (G.transformWord b Q w hwdeg gaps).poly =
      (H.transformWord b Q w hwdeg gaps).poly) :
    G.poly = H.poly := by
  induction gaps generalizing G H with
  | nil => exact hpoly
  | cons g gs ih =>
      have hfirst := ih (G.transform b Q g w hwdeg)
        (H.transform b Q g w hwdeg) hpoly
      exact transformPoly_injective hb w hfirst

end PolynomialGraph

/-! ## Augmented Vandermonde determinants -/

/-- An augmented Vandermonde matrix whose first column is a vector `r` and
whose remaining columns are `1, x, ..., x^(n-1)`. -/
def augmentedVandermonde {n : ℕ} (x r : Fin (n + 1) → ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j => Fin.cases (r i) (fun k => x i ^ (k : ℕ)) j

@[simp]
theorem augmentedVandermonde_apply_zero {n : ℕ}
    (x r : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    augmentedVandermonde x r i 0 = r i := by
  rfl

@[simp]
theorem augmentedVandermonde_apply_succ {n : ℕ}
    (x r : Fin (n + 1) → ℤ) (i : Fin (n + 1)) (j : Fin n) :
    augmentedVandermonde x r i j.succ = x i ^ (j : ℕ) := by
  rfl

/-- A degree `< n` polynomial evaluation column is dependent on the `n`
Vandermonde columns. -/
theorem augmentedVandermonde_det_eval_eq_zero {n : ℕ}
    (x : Fin (n + 1) → ℤ) (F : Polynomial ℤ)
    (hdeg : F.natDegree < n) :
    (augmentedVandermonde x (fun i => F.eval (x i))).det = 0 := by
  let A := augmentedVandermonde x (fun _ => 0)
  let c : Fin (n + 1) → ℤ :=
    Fin.cases 0 (fun j => F.coeff (j : ℕ))
  have hcolumn (i : Fin (n + 1)) :
      (∑ j, c j • A i j) = F.eval (x i) := by
    rw [Polynomial.eval_eq_sum_range' hdeg]
    rw [← Fin.sum_univ_eq_sum_range]
    rw [Fin.sum_univ_succ]
    simp [c, A]
  have hmatrix :
      A.updateCol 0 (fun i => ∑ j, c j • A i j) =
        augmentedVandermonde x (fun i => F.eval (x i)) := by
    ext i j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa [smul_eq_mul] using hcolumn i
    · simp [A, augmentedVandermonde]
  rw [← hmatrix, Matrix.det_updateCol_sum]
  simp [c]

theorem augmentedVandermonde_update_zero {n : ℕ}
    (x r s : Fin (n + 1) → ℤ) :
    (augmentedVandermonde x r).updateCol 0 s =
      augmentedVandermonde x s := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp
  · simp

/-- Adding a polynomial of degree `< n` to the augmented column leaves the
determinant unchanged. -/
theorem augmentedVandermonde_det_add_eval {n : ℕ}
    (x r : Fin (n + 1) → ℤ) (F : Polynomial ℤ)
    (hdeg : F.natDegree < n) :
    (augmentedVandermonde x (fun i => r i + F.eval (x i))).det =
      (augmentedVandermonde x r).det := by
  let e : Fin (n + 1) → ℤ := fun i => F.eval (x i)
  have hadd : (fun i => r i + F.eval (x i)) = r + e := by
    rfl
  rw [hadd, ← augmentedVandermonde_update_zero x r (r + e)]
  rw [Matrix.det_updateCol_add]
  rw [augmentedVandermonde_update_zero, augmentedVandermonde_update_zero]
  rw [augmentedVandermonde_det_eval_eq_zero x F hdeg, add_zero]

/-- If a common integer divides every entry in the augmented column, it
divides the augmented determinant. -/
theorem dvd_augmentedVandermonde_det {n : ℕ} (B : ℤ)
    (x r : Fin (n + 1) → ℤ) (hdiv : ∀ i, B ∣ r i) :
    B ∣ (augmentedVandermonde x r).det := by
  choose q hq using hdiv
  have hr : r = B • q := by
    funext i
    simpa [smul_eq_mul] using hq i
  rw [hr, ← augmentedVandermonde_update_zero x q (B • q)]
  rw [Matrix.det_updateCol_smul]
  rw [augmentedVandermonde_update_zero]
  exact dvd_mul_right B _

theorem augmentedVandermonde_det_smul {n : ℕ} (B : ℤ)
    (x r : Fin (n + 1) → ℤ) :
    (augmentedVandermonde x (B • r)).det =
      B * (augmentedVandermonde x r).det := by
  rw [← augmentedVandermonde_update_zero x r (B • r)]
  rw [Matrix.det_updateCol_smul]
  rw [augmentedVandermonde_update_zero]

/-- Sharp last-column expansion bound.  Only the carry column contributes an
`R` factor; every minor is a Vandermonde determinant controlled by the window
width. -/
theorem augmentedVandermonde_natAbs_le {d R W : ℕ} {A : ℤ}
    (x r : Fin (d + 2) → ℤ)
    (hx : ∀ i, A ≤ x i ∧ x i ≤ A + W)
    (hr : ∀ i, (r i).natAbs ≤ R) :
    (augmentedVandermonde (n := d + 1) x r).det.natAbs ≤
      (d + 2) * R * W ^ vandermondeExponent d := by
  let M := augmentedVandermonde (n := d + 1) x r
  have hminor (i : Fin (d + 2)) :
      M.submatrix i.succAbove Fin.succ =
        Matrix.vandermonde (fun j : Fin (d + 1) => x (i.succAbove j)) := by
    ext j k
    rfl
  have hminor_bound (i : Fin (d + 2)) :
      (M.submatrix i.succAbove Fin.succ).det.natAbs ≤
        W ^ vandermondeExponent d := by
    rw [hminor]
    exact integerVandermonde_natAbs_le
      (fun j : Fin (d + 1) => x (i.succAbove j))
      (fun j => hx (i.succAbove j))
  have hterm (i : Fin (d + 2)) :
      (((-1 : ℤ) ^ (i : ℕ) * M i 0 *
          (M.submatrix i.succAbove Fin.succ).det).natAbs) ≤
        R * W ^ vandermondeExponent d := by
    rw [Int.natAbs_mul, Int.natAbs_mul]
    simp only [Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow,
      one_mul]
    exact Nat.mul_le_mul (by simpa [M] using hr i) (hminor_bound i)
  rw [Matrix.det_succ_column_zero]
  calc
    (∑ i : Fin (d + 2),
        (-1 : ℤ) ^ (i : ℕ) * M i 0 *
          (M.submatrix i.succAbove Fin.succ).det).natAbs ≤
        ∑ i : Fin (d + 2),
          (((-1 : ℤ) ^ (i : ℕ) * M i 0 *
            (M.submatrix i.succAbove Fin.succ).det).natAbs) := by
      simpa using Int.natAbs_sum_le (Finset.univ : Finset (Fin (d + 2)))
        (fun i => (-1 : ℤ) ^ (i : ℕ) * M i 0 *
          (M.submatrix i.succAbove Fin.succ).det)
    _ ≤ ∑ _i : Fin (d + 2), R * W ^ vandermondeExponent d := by
      exact Finset.sum_le_sum fun i _ => hterm i
    _ = (d + 2) * R * W ^ vandermondeExponent d := by
      simp [mul_assoc]

/-- Determinant-vanishing form of polynomial locking: recurrence divisibility
and a strict size gap force any `d + 2` augmented samples to be dependent. -/
theorem augmentedVandermonde_det_eq_zero_of_locking
    {d R W B : ℕ} {A : ℤ}
    (x r : Fin (d + 2) → ℤ) (F : Polynomial ℤ)
    (hFdeg : F.natDegree ≤ d)
    (hx : ∀ i, A ≤ x i ∧ x i ≤ A + W)
    (hr : ∀ i, (r i).natAbs ≤ R)
    (hdiv : ∀ i, (B : ℤ) ∣ r i + F.eval (x i))
    (hlarge : (d + 2) * R * W ^ vandermondeExponent d < B) :
    (augmentedVandermonde (n := d + 1) x r).det = 0 := by
  have hFdeg' : F.natDegree < d + 1 := by omega
  have hdvdCorrected :
      (B : ℤ) ∣
        (augmentedVandermonde (n := d + 1) x
          (fun i => r i + F.eval (x i))).det :=
    dvd_augmentedVandermonde_det (B : ℤ) x
      (fun i => r i + F.eval (x i)) hdiv
  have hdvd :
      (B : ℤ) ∣ (augmentedVandermonde (n := d + 1) x r).det := by
    rwa [augmentedVandermonde_det_add_eval x r F hFdeg'] at hdvdCorrected
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
  have hbound := augmentedVandermonde_natAbs_le x r hx hr
  have hlt :
      (augmentedVandermonde (n := d + 1) x r).det.natAbs < B :=
    hbound.trans_lt hlarge
  simpa using hlt

/-- Once `d + 1` independent samples define a certified graph, vanishing of
the augmented determinant for one further sample forces that sample onto the
same graph. -/
theorem PolynomialGraph.eval_eq_of_augmented_det_eq_zero {d : ℕ}
    (G : PolynomialGraph d)
    (x r : Fin (d + 1) → ℤ) (hx : Function.Injective x)
    (hfit : ∀ i, G.poly.eval (x i : ℚ) = (r i : ℚ))
    (z t : ℤ)
    (hdet :
      (augmentedVandermonde (n := d + 1) (Fin.snoc x z)
        (Fin.snoc r t)).det = 0) :
    G.poly.eval (z : ℚ) = (t : ℚ) := by
  let xs : Fin (d + 2) → ℤ := Fin.snoc x z
  let rs : Fin (d + 2) → ℤ := Fin.snoc r t
  let scaled : Fin (d + 2) → ℤ := (G.denominator : ℤ) • rs
  let diff : Fin (d + 2) → ℤ :=
    fun i => scaled i - G.integralPoly.eval (xs i)
  have hdeg : (-G.integralPoly).natDegree < d + 1 := by
    rw [Polynomial.natDegree_neg]
    exact G.integralPoly_degree_le.trans_lt (by omega)
  have hdiff_as_add :
      diff = fun i => scaled i + (-G.integralPoly).eval (xs i) := by
    funext i
    simp [diff, sub_eq_add_neg]
  have hscaled_det :
      (augmentedVandermonde (n := d + 1) xs scaled).det = 0 := by
    rw [show scaled = (G.denominator : ℤ) • rs by rfl]
    rw [augmentedVandermonde_det_smul]
    simpa [xs, rs] using congrArg (fun q : ℤ => (G.denominator : ℤ) * q) hdet
  have hdiff_det :
      (augmentedVandermonde (n := d + 1) xs diff).det = 0 := by
    rw [hdiff_as_add]
    rw [augmentedVandermonde_det_add_eval xs scaled
      (-G.integralPoly) hdeg]
    exact hscaled_det
  have hbase_integral (i : Fin (d + 1)) :
      G.integralPoly.eval (x i) = (G.denominator : ℤ) * r i := by
    have hcert := G.integral_value_certificate (x i)
    rw [hfit i] at hcert
    exact_mod_cast hcert
  have hdiff_base (i : Fin (d + 1)) : diff i.castSucc = 0 := by
    simp only [diff, scaled, xs, rs, Fin.snoc_castSucc, Pi.smul_apply,
      smul_eq_mul]
    rw [hbase_integral]
    ring
  let M := augmentedVandermonde (n := d + 1) xs diff
  have hminor :
      (M.submatrix (Fin.last (d + 1)).succAbove Fin.succ).det =
        (Matrix.vandermonde x).det := by
    congr 1
    ext i j
    simp [M, xs, augmentedVandermonde]
  have hminor_ne :
      (M.submatrix (Fin.last (d + 1)).succAbove Fin.succ).det ≠ 0 := by
    rw [hminor]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hx
  have hlast_product :
      (-1 : ℤ) ^ ((Fin.last (d + 1) : Fin (d + 2)) : ℕ) *
          diff (Fin.last (d + 1)) *
          (M.submatrix (Fin.last (d + 1)).succAbove Fin.succ).det = 0 := by
    have hexpand := hdiff_det
    change M.det = 0 at hexpand
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_castSucc] at hexpand
    have hfirst :
        (∑ i : Fin (d + 1),
          (-1 : ℤ) ^ ((i.castSucc : Fin (d + 2)) : ℕ) *
            M i.castSucc 0 *
            (M.submatrix i.castSucc.succAbove Fin.succ).det) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [show M i.castSucc 0 = diff i.castSucc by rfl, hdiff_base]
      ring
    rw [hfirst, zero_add] at hexpand
    exact hexpand
  have hdiff_last : diff (Fin.last (d + 1)) = 0 := by
    rcases mul_eq_zero.mp hlast_product with hleft | hright
    · rcases mul_eq_zero.mp hleft with hsign | hdiff
      · exact False.elim ((pow_ne_zero _ (by norm_num : (-1 : ℤ) ≠ 0)) hsign)
      · exact hdiff
    · exact False.elim (hminor_ne hright)
  have hdiff_last' :
      (G.denominator : ℤ) * t - G.integralPoly.eval z = 0 := by
    simpa [diff, scaled, xs, rs, smul_eq_mul] using hdiff_last
  have hdiffQ :
      (G.denominator : ℚ) * (t : ℚ) -
        ((G.integralPoly.eval z : ℤ) : ℚ) = 0 := by
    exact_mod_cast hdiff_last'
  rw [G.integral_value_certificate z] at hdiffQ
  have hmul :
      (G.denominator : ℚ) * (t : ℚ) =
        (G.denominator : ℚ) * G.poly.eval (z : ℚ) := by
    linarith
  exact (mul_left_cancel₀ (by exact_mod_cast G.denominator_ne_zero) hmul).symm

/-- Interpolation at `d + 1` integer points produces a graph whose common
monomial denominator is the absolute Vandermonde determinant.  The determinant
bound is recorded simultaneously, which is the algebraic content of
`eq:graphden`. -/
theorem exists_polynomialGraph_of_integer_samples {d H : ℕ} {A : ℤ}
    (P : Polynomial ℚ) (hdeg : P.natDegree ≤ d)
    (x : Fin (d + 1) → ℤ) (hx : Function.Injective x)
    (hx_interval : ∀ i, A ≤ x i ∧ x i ≤ A + H)
    (y : Fin (d + 1) → ℤ)
    (hy : ∀ i, P.eval (x i : ℚ) = (y i : ℚ)) :
    ∃ G : PolynomialGraph d,
      G.poly = P ∧
      G.denominator ≤ H ^ vandermondeExponent d := by
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
  let zvec : Fin (d + 1) → ℤ := Matrix.mulVec Vz.adjugate y
  have hmapAdj :
      Vq.adjugate = Vz.adjugate.map (algebraMap ℤ ℚ) := by
    change (Vz.map (algebraMap ℤ ℚ)).adjugate =
      Vz.adjugate.map (algebraMap ℤ ℚ)
    exact (RingHom.map_adjugate (algebraMap ℤ ℚ) Vz).symm
  have hright :
      Matrix.mulVec Vq.adjugate (fun i => (y i : ℚ)) =
        fun j => (zvec j : ℚ) := by
    funext j
    rw [hmapAdj]
    exact (RingHom.map_mulVec (algebraMap ℤ ℚ) Vz.adjugate y j).symm
  have hdet_map : Vq.det = ((Vz.det : ℤ) : ℚ) := by
    change (Vz.map (algebraMap ℤ ℚ)).det = (Vz.det : ℚ)
    exact (RingHom.map_det (algebraMap ℤ ℚ) Vz).symm
  have hcoeff (j : Fin (d + 1)) :
      (Vz.det : ℚ) * coeffs j = (zvec j : ℚ) := by
    have hadj := congrArg
      (fun v : Fin (d + 1) → ℚ => Matrix.mulVec Vq.adjugate v j) hsystem
    calc
      (Vz.det : ℚ) * coeffs j = Vq.det * coeffs j := by rw [hdet_map]
      _ = Matrix.mulVec Vq.adjugate (Matrix.mulVec Vq coeffs) j := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul,
          Matrix.smul_mulVec, Matrix.one_mulVec]
        rfl
      _ = Matrix.mulVec Vq.adjugate (fun i => (y i : ℚ)) j := hadj
      _ = (zvec j : ℚ) := congrFun hright j
  have hdet_ne : Vz.det ≠ 0 := by
    change (Matrix.vandermonde x).det ≠ 0
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hx
  let T : ℕ := Vz.det.natAbs
  have hT_pos : 0 < T := Int.natAbs_pos.mpr hdet_ne
  let icoeffs : Fin (d + 1) → ℤ := fun j => Vz.det.sign * zvec j
  let integral : Polynomial ℤ := Polynomial.ofFn (d + 1) icoeffs
  have hcoeff_scaled (j : Fin (d + 1)) :
      (icoeffs j : ℚ) = (T : ℚ) * P.coeff j := by
    have habs : (T : ℤ) = Vz.det.sign * Vz.det := by
      exact (Int.sign_mul_self Vz.det).symm
    have habsQ : (T : ℚ) = (Vz.det.sign : ℚ) * (Vz.det : ℚ) := by
      exact_mod_cast habs
    calc
      (icoeffs j : ℚ) = (Vz.det.sign : ℚ) * (zvec j : ℚ) := by
        simp only [icoeffs, Int.cast_mul]
      _ = (Vz.det.sign : ℚ) * ((Vz.det : ℚ) * coeffs j) := by
        rw [hcoeff j]
      _ = (T : ℚ) * P.coeff j := by
        dsimp only [coeffs]
        rw [habsQ]
        ring
  have hcertificate :
      integral.map (algebraMap ℤ ℚ) = (T : ℚ) • P := by
    ext n
    by_cases hn : n < d + 1
    · simp only [integral, Polynomial.coeff_map,
        Polynomial.ofFn_coeff_eq_val_of_lt _ hn,
        Polynomial.coeff_smul, smul_eq_mul]
      exact hcoeff_scaled ⟨n, hn⟩
    · have hn_ge : d + 1 ≤ n := Nat.le_of_not_gt hn
      have hPzero : P.coeff n = 0 := by
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt (by omega))
      simp only [integral, Polynomial.coeff_map,
        Polynomial.ofFn_coeff_eq_zero_of_ge _ hn_ge,
        map_zero, Polynomial.coeff_smul, smul_eq_mul, hPzero, mul_zero]
  let G : PolynomialGraph d :=
    { poly := P
      degree_le := hdeg
      denominator := T
      denominator_pos := hT_pos
      integralPoly := integral
      certificate := hcertificate }
  refine ⟨G, rfl, ?_⟩
  change Vz.det.natAbs ≤ H ^ vandermondeExponent d
  exact integerVandermonde_natAbs_le x hx_interval

/-- Manuscript lemma `lem:locking`, in an explicit finite-occurrence form.
The recurrence correction `F` is shared by all occurrences.  Its divisibility
and the sharp size inequality are the exact hypotheses discharged by the
nonrare-prefix estimates. -/
theorem lem_locking {ι : Type*} [Fintype ι]
    {d R W B : ℕ} {A : ℤ}
    (x r : ι → ℤ) (F : Polynomial ℤ)
    (hx : Function.Injective x)
    (hx_interval : ∀ i, A ≤ x i ∧ x i ≤ A + W)
    (hr : ∀ i, (r i).natAbs ≤ R)
    (hFdeg : F.natDegree ≤ d)
    (hdiv : ∀ i, (B : ℤ) ∣ r i + F.eval (x i))
    (hcard : d + 1 ≤ Fintype.card ι)
    (hlarge : (d + 2) * R * W ^ vandermondeExponent d < B) :
    ∃ G : PolynomialGraph d,
      G.denominator ≤ W ^ vandermondeExponent d ∧
      ∀ i, G.poly.eval (x i : ℚ) = (r i : ℚ) := by
  classical
  have hecard : Fintype.card (Fin (d + 1)) ≤ Fintype.card ι := by
    simpa using hcard
  let e : Fin (d + 1) ↪ ι :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hecard)
  let x₀ : Fin (d + 1) → ℤ := fun j => x (e j)
  let r₀ : Fin (d + 1) → ℤ := fun j => r (e j)
  have hx₀ : Function.Injective x₀ := hx.comp e.injective
  let v : Fin (d + 1) → ℚ := fun j => (x₀ j : ℚ)
  let q : Fin (d + 1) → ℚ := fun j => (r₀ j : ℚ)
  have hv : Function.Injective v := by
    intro i j hij
    apply hx₀
    exact Int.cast_injective hij
  have hv_on :
      Set.InjOn v (↑(Finset.univ : Finset (Fin (d + 1))) : Set (Fin (d + 1))) :=
    hv.injOn
  let P : Polynomial ℚ := Lagrange.interpolate Finset.univ v q
  have hPfit (j : Fin (d + 1)) :
      P.eval (x₀ j : ℚ) = (r₀ j : ℚ) := by
    exact Lagrange.eval_interpolate_at_node q hv_on (Finset.mem_univ j)
  have hPdeg : P.natDegree ≤ d := by
    rw [Polynomial.natDegree_le_iff_degree_le]
    simpa [P] using Lagrange.degree_interpolate_le q hv_on
  obtain ⟨G, hGpoly, hGden⟩ :=
    exists_polynomialGraph_of_integer_samples P hPdeg x₀ hx₀
      (fun j => hx_interval (e j)) r₀ hPfit
  have hGfit (j : Fin (d + 1)) :
      G.poly.eval (x₀ j : ℚ) = (r₀ j : ℚ) := by
    rw [hGpoly]
    exact hPfit j
  refine ⟨G, hGden, fun i => ?_⟩
  by_cases hi : i ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hi
    exact hGfit j
  · let xs : Fin (d + 2) → ℤ := Fin.snoc x₀ (x i)
    let rs : Fin (d + 2) → ℤ := Fin.snoc r₀ (r i)
    have hxs_interval : ∀ k, A ≤ xs k ∧ xs k ≤ A + W := by
      intro k
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simpa [xs] using hx_interval i
      · simpa [xs, x₀] using hx_interval (e j)
    have hrs : ∀ k, (rs k).natAbs ≤ R := by
      intro k
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simpa [rs] using hr i
      · simpa [rs, r₀] using hr (e j)
    have hdivs : ∀ k, (B : ℤ) ∣ rs k + F.eval (xs k) := by
      intro k
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simpa [rs, xs] using hdiv i
      · simpa [rs, xs, r₀, x₀] using hdiv (e j)
    have hdet :
        (augmentedVandermonde (n := d + 1) xs rs).det = 0 :=
      augmentedVandermonde_det_eq_zero_of_locking xs rs F hFdeg
        hxs_interval hrs hdivs hlarge
    exact G.eval_eq_of_augmented_det_eq_zero x₀ r₀ hx₀ hGfit
      (x i) (r i) (by simpa [xs, rs] using hdet)

/-- A common gap word among genuine carry occurrences automatically supplies
the correction polynomial and divisibility hypotheses of `lem_locking`. -/
theorem lockedGraph_of_commonGapWord (D : CarrySeries)
    (anchors : Finset ℕ) (gaps : Erdos260.GapWord)
    {A : ℤ} {W R : ℕ}
    (hword : ∀ x ∈ anchors, D.GapWordAt x gaps)
    (hterminal : ∀ x ∈ anchors,
      A ≤ (x + Erdos260.GapWord.span gaps : ℕ) ∧
        (x + Erdos260.GapWord.span gaps : ℕ) ≤ A + W)
    (hcarry : ∀ x ∈ anchors,
      (D.carry (x + Erdos260.GapWord.span gaps)).natAbs ≤ R)
    (hcard : D.weight.natDegree + 1 ≤ anchors.card)
    (hlarge :
      (D.weight.natDegree + 2) * R *
          W ^ vandermondeExponent D.weight.natDegree <
        D.base ^ Erdos260.GapWord.span gaps) :
    ∃ G : PolynomialGraph D.weight.natDegree,
      G.denominator ≤ W ^ vandermondeExponent D.weight.natDegree ∧
      ∀ x ∈ anchors,
        G.poly.eval (x + Erdos260.GapWord.span gaps : ℚ) =
          (D.carry (x + Erdos260.GapWord.span gaps) : ℚ) := by
  classical
  let terminal : (↥anchors) → ℤ := fun x =>
    (x.1 + Erdos260.GapWord.span gaps : ℕ)
  let value : (↥anchors) → ℤ := fun x =>
    D.carry (x.1 + Erdos260.GapWord.span gaps)
  let correction : Polynomial ℤ :=
    (D.denominator : ℤ) • wordCorrection D.base D.weight gaps
  have hterminal_injective : Function.Injective terminal := by
    intro x y hxy
    apply Subtype.ext
    dsimp [terminal] at hxy
    exact Nat.add_right_cancel (by exact_mod_cast hxy)
  have hterminal_interval : ∀ x, A ≤ terminal x ∧ terminal x ≤ A + W := by
    intro x
    simpa only [terminal] using hterminal x.1 x.2
  have hvalue : ∀ x, (value x).natAbs ≤ R := by
    intro x
    exact hcarry x.1 x.2
  have hcorrection_degree : correction.natDegree ≤ D.weight.natDegree := by
    exact (Polynomial.natDegree_smul_le _ _).trans
      (wordCorrection_degree_le D.base D.weight gaps)
  have hdiv : ∀ x,
      ((D.base ^ Erdos260.GapWord.span gaps : ℕ) : ℤ) ∣
        value x + correction.eval (terminal x) := by
    intro x
    have hrec := D.carry_word_recurrence (hword x.1 x.2)
    have heq :
        value x + correction.eval (terminal x) =
          (D.base : ℤ) ^ Erdos260.GapWord.span gaps * D.carry x.1 := by
      simpa only [value, correction, terminal, Polynomial.eval_smul,
        smul_eq_mul, Int.natCast_pow, Int.natCast_add] using hrec
    rw [heq]
    exact dvd_mul_right _ _
  have hcard' :
      D.weight.natDegree + 1 ≤ Fintype.card (↥anchors) := by
    simpa using hcard
  obtain ⟨G, hden, hfit⟩ :=
    lem_locking terminal value correction hterminal_injective
      hterminal_interval hvalue hcorrection_degree hdiv hcard' hlarge
  refine ⟨G, hden, ?_⟩
  intro x hx
  convert hfit ⟨x, hx⟩ using 1
  simp [terminal]

/-! ## Locked graphs for canonical window-prefix fibres -/

/-- Enumeration indices realizing one canonical locking prefix. -/
def realizedPrefixIndices (D : CarrySeries) (N W m bound : ℕ)
    (pfx : Erdos260.GapWord) : Finset ℕ :=
  (longWindowIndices D.positiveEnumeration N W m bound).filter fun k =>
    lockingPrefix D.positiveEnumeration k m bound = pfx

/-- Actual support anchors of one prefix fibre. -/
def realizedPrefixAnchors (D : CarrySeries) (N W m bound : ℕ)
    (pfx : Erdos260.GapWord) : Finset ℕ :=
  (realizedPrefixIndices D N W m bound pfx).image D.positiveEnumeration.a

/-- The actual continuation after the canonical shortest locking prefix. -/
def postLockingWord {S : Set ℕ} (e : Erdos260.SupportEnumeration S)
    (k m bound : ℕ) : Erdos260.GapWord :=
  (forwardGapWord e k m).drop (lockingPrefix e k m bound).length

theorem lockingPrefix_append_postLockingWord {S : Set ℕ}
    (e : Erdos260.SupportEnumeration S) (k m bound : ℕ) :
    lockingPrefix e k m bound ++ postLockingWord e k m bound =
      forwardGapWord e k m := by
  exact (List.prefix_append_drop
    (Erdos260.GapWord.firstPrefixAbove_isPrefix
      (forwardGapWord e k m) bound)).symm

theorem postLockingWord_positive {S : Set ℕ}
    (e : Erdos260.SupportEnumeration S) (k m bound : ℕ) :
    Erdos260.GapWord.Positive (postLockingWord e k m bound) := by
  intro g hg
  apply forwardGapWord_positive e k m g
  exact List.mem_of_mem_drop hg

theorem postLockingWord_length_le {S : Set ℕ}
    (e : Erdos260.SupportEnumeration S) (k m bound : ℕ) :
    (postLockingWord e k m bound).length ≤ m := by
  unfold postLockingWord
  rw [List.length_drop]
  exact (Nat.sub_le _ _).trans (by
    rw [forwardGapWord_length])

/-- Every gap in an actual post-locking word inherits the local geometry cap. -/
theorem postLockingWord_gap_le (D : CarrySeries)
    {N W m cap bound k : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hk : k ∈ longWindowIndices D.positiveEnumeration N W m bound) :
    ∀ g ∈ postLockingWord D.positiveEnumeration k m bound, g ≤ cap := by
  intro g hg
  have hfull : g ∈ forwardGapWord D.positiveEnumeration k m :=
    List.mem_of_mem_drop hg
  simp only [forwardGapWord, Erdos260.enumerationGapWord,
    List.mem_map, List.mem_range] at hfull
  obtain ⟨r, hr, rfl⟩ := hfull
  have hkWindow : k ∈ windowIndices D.positiveEnumeration N W :=
    (Finset.mem_filter.mp hk).1
  have hkIco := Finset.mem_Ico.mp hkWindow
  exact hgeom.gaps_le (k + r) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)

theorem lockingPrefix_span_add_postSpan {S : Set ℕ}
    (e : Erdos260.SupportEnumeration S) (k m bound : ℕ) :
    Erdos260.GapWord.span (lockingPrefix e k m bound) +
        Erdos260.GapWord.span (postLockingWord e k m bound) =
      forwardSpan e k m := by
  have h := congrArg List.sum
    (lockingPrefix_append_postLockingWord e k m bound)
  rw [List.sum_append] at h
  rw [← forwardGapWord_span e k m]
  simpa only [Erdos260.GapWord.span] using h

/-- The post-prefix continuation is a genuine carry gap word starting at the
prefix terminal point. -/
theorem postLockingWord_gapWordAt (D : CarrySeries) (k m bound : ℕ) :
    D.GapWordAt
      (D.positiveEnumeration.a k +
        Erdos260.GapWord.span
          (lockingPrefix D.positiveEnumeration k m bound))
      (postLockingWord D.positiveEnumeration k m bound) := by
  let pfx := lockingPrefix D.positiveEnumeration k m bound
  let post := postLockingWord D.positiveEnumeration k m bound
  have hsplit : pfx ++ post = forwardGapWord D.positiveEnumeration k m := by
    exact lockingPrefix_append_postLockingWord D.positiveEnumeration k m bound
  have happ : D.GapWordAt (D.positiveEnumeration.a k) (pfx ++ post) := by
    rw [hsplit]
    exact D.gapWordAt_enumeration k m
  have htail := (CarrySeries.GapWordAt.append_iff pfx post).mp happ |>.2
  simpa only [pfx, post] using htail

/-- The finite interior/exterior dichotomy applied to the genuine
post-locking continuation of one canonical window. -/
theorem canonicalPost_dichotomy (D : CarrySeries)
    {N W m cap bound k : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hk : k ∈ longWindowIndices D.positiveEnumeration N W m bound)
    (G : PolynomialGraph D.weight.natDegree)
    (hlong : 2 * (cap +
      (postLockingWord D.positiveEnumeration k m bound).length) ≤
        Erdos260.GapWord.span
          (postLockingWord D.positiveEnumeration k m bound)) :
    let post := postLockingWord D.positiveEnumeration k m bound
    Erdos260.GapWord.span post ≤
        4 * interiorSpanAlong D.base post
          ((PolynomialGraph.normalizedTopState G D.denominator D.weight : ℚ) : ℝ) ∨
      Erdos260.GapWord.span post ≤
        4 * exteriorSpanAlong D.base post
          ((PolynomialGraph.normalizedTopState G D.denominator D.weight : ℚ) : ℝ) := by
  let post := postLockingWord D.positiveEnumeration k m bound
  have hkWindow : k ∈ windowIndices D.positiveEnumeration N W :=
    (Finset.mem_filter.mp hk).1
  have hcapFull : ∀ g ∈ forwardGapWord D.positiveEnumeration k m, g ≤ cap := by
    intro g hg
    simp only [forwardGapWord, Erdos260.enumerationGapWord,
      List.mem_map, List.mem_range] at hg
    obtain ⟨r, hr, rfl⟩ := hg
    have hkIco := Finset.mem_Ico.mp hkWindow
    exact hgeom.gaps_le (k + r) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  have hcapPost : ∀ g ∈ post, g ≤ cap := by
    intro g hg
    exact hcapFull g (List.mem_of_mem_drop hg)
  exact (lem_dichotomy (b := D.base) (cap := cap) D.base_ge_two
    (postLockingWord_positive D.positiveEnumeration k m bound)
    hcapPost
    ((PolynomialGraph.normalizedTopState G D.denominator D.weight : ℚ) : ℝ)
    hlong).2

theorem realizedPrefixAnchors_card (D : CarrySeries) (N W m bound : ℕ)
    (pfx : Erdos260.GapWord) :
    (realizedPrefixAnchors D N W m bound pfx).card =
      (realizedPrefixIndices D N W m bound pfx).card := by
  unfold realizedPrefixAnchors
  exact Finset.card_image_of_injective _ D.positiveEnumeration.strictMono.injective

/-- Every anchor in a canonical prefix fibre genuinely realizes that gap
word in the carry recurrence. -/
theorem realizedPrefix_gapWordAt (D : CarrySeries) (N W m bound : ℕ)
    (pfx : Erdos260.GapWord) :
    ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
      D.GapWordAt x pfx := by
  classical
  intro x hx
  rw [realizedPrefixAnchors, Finset.mem_image] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  have hpfx : lockingPrefix D.positiveEnumeration k m bound = pfx := by
    exact (Finset.mem_filter.mp hk).2
  have hfull := D.gapWordAt_enumeration k m
  rw [← hpfx]
  exact CarrySeries.GapWordAt.prefix
    (Erdos260.GapWord.firstPrefixAbove_isPrefix
      (forwardGapWord D.positiveEnumeration k m) bound) hfull

/-- A graph locked on a canonical prefix follows the genuine carry value at
the endpoint of any one actual post-prefix continuation in that fibre. -/
theorem lockedGraph_postWord_eval (D : CarrySeries)
    (N W m bound : ℕ) (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree)
    (hfit : ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
      G.poly.eval (x + Erdos260.GapWord.span pfx : ℚ) =
        (D.carry (x + Erdos260.GapWord.span pfx) : ℚ))
    {k : ℕ} (hk : k ∈ realizedPrefixIndices D N W m bound pfx) :
    let post := postLockingWord D.positiveEnumeration k m bound
    (G.transformWord D.base D.denominator D.weight le_rfl post).poly.eval
        ((D.positiveEnumeration.a k + forwardSpan D.positiveEnumeration k m : ℕ) : ℚ) =
      (D.carry
        (D.positiveEnumeration.a k + forwardSpan D.positiveEnumeration k m) : ℚ) := by
  let post := postLockingWord D.positiveEnumeration k m bound
  have hpfx : lockingPrefix D.positiveEnumeration k m bound = pfx :=
    (Finset.mem_filter.mp hk).2
  have hanchor : D.positiveEnumeration.a k ∈
      realizedPrefixAnchors D N W m bound pfx := by
    rw [realizedPrefixAnchors, Finset.mem_image]
    exact ⟨k, hk, rfl⟩
  have hstart :
      G.poly.eval
          ((D.positiveEnumeration.a k + Erdos260.GapWord.span pfx : ℕ) : ℚ) =
        (D.carry
          (D.positiveEnumeration.a k + Erdos260.GapWord.span pfx) : ℚ) := by
    simpa only [Nat.cast_add] using
      hfit (D.positiveEnumeration.a k) hanchor
  have hstart' :
      G.poly.eval
          ((D.positiveEnumeration.a k +
            Erdos260.GapWord.span
              (lockingPrefix D.positiveEnumeration k m bound) : ℕ) : ℚ) =
        (D.carry
          (D.positiveEnumeration.a k +
            Erdos260.GapWord.span
              (lockingPrefix D.positiveEnumeration k m bound)) : ℚ) := by
    simpa only [hpfx] using hstart
  have hcontinued := G.transformWord_eval_carry D hstart'
    (postLockingWord_gapWordAt D k m bound)
  have hspan := lockingPrefix_span_add_postSpan
    D.positiveEnumeration k m bound
  have hcoord :
      (D.positiveEnumeration.a k +
          Erdos260.GapWord.span
            (lockingPrefix D.positiveEnumeration k m bound)) +
          Erdos260.GapWord.span post =
        D.positiveEnumeration.a k + forwardSpan D.positiveEnumeration k m := by
    dsimp only [post]
    omega
  rw [hcoord] at hcontinued
  dsimp only [post]
  exact hcontinued

/-- Concrete locking wrapper for a nonrare realized prefix.  The word and
its recurrence are generated internally from the canonical support
enumeration. -/
theorem lockedGraph_of_realizedPrefix (D : CarrySeries)
    (N W m bound : ℕ) (pfx : Erdos260.GapWord)
    {A : ℤ} {H R : ℕ}
    (hterminal : ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
      A ≤ (x + Erdos260.GapWord.span pfx : ℕ) ∧
        (x + Erdos260.GapWord.span pfx : ℕ) ≤ A + H)
    (hcarry : ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
      (D.carry (x + Erdos260.GapWord.span pfx)).natAbs ≤ R)
    (hcard : D.weight.natDegree + 1 ≤
      (realizedPrefixIndices D N W m bound pfx).card)
    (hlarge :
      (D.weight.natDegree + 2) * R *
          H ^ vandermondeExponent D.weight.natDegree <
        D.base ^ Erdos260.GapWord.span pfx) :
    ∃ G : PolynomialGraph D.weight.natDegree,
      G.denominator ≤ H ^ vandermondeExponent D.weight.natDegree ∧
      ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
        G.poly.eval (x + Erdos260.GapWord.span pfx : ℚ) =
          (D.carry (x + Erdos260.GapWord.span pfx) : ℚ) := by
  apply lockedGraph_of_commonGapWord D
    (realizedPrefixAnchors D N W m bound pfx) pfx
  · exact realizedPrefix_gapWordAt D N W m bound pfx
  · exact hterminal
  · exact hcarry
  · rw [realizedPrefixAnchors_card]
    exact hcard
  · exact hlarge

/-- Fully geometric locking of a nonrare canonical prefix.  Terminal
coordinates and carry heights are discharged from the real window geometry;
only the final explicit exponential-versus-polynomial inequality remains for
the asymptotic layer. -/
theorem lockedGraph_of_nonrarePrefix (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (hcard : D.weight.natDegree + 1 ≤
      (realizedPrefixIndices D N W m bound pfx).card)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (hlarge :
      (D.weight.natDegree + 2) *
          (D.heightNatConstant * (N + W + bound + cap + 1) ^
            D.weight.natDegree) *
          (W + bound + cap) ^ vandermondeExponent D.weight.natDegree <
        D.base ^ Erdos260.GapWord.span pfx) :
    ∃ G : PolynomialGraph D.weight.natDegree,
      G.denominator ≤
        (W + bound + cap) ^ vandermondeExponent D.weight.natDegree ∧
      ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
        G.poly.eval (x + Erdos260.GapWord.span pfx : ℚ) =
          (D.carry (x + Erdos260.GapWord.span pfx) : ℚ) := by
  classical
  have hcardPos : 0 < (realizedPrefixIndices D N W m bound pfx).card :=
    (Nat.succ_pos D.weight.natDegree).trans_le hcard
  obtain ⟨k₀, hk₀⟩ := Finset.card_pos.mp hcardPos
  have hpfx : pfx ∈
      realizedLockingPrefixes D.positiveEnumeration N W m bound := by
    rw [realizedLockingPrefixes, Finset.mem_image]
    refine ⟨k₀, (Finset.mem_filter.mp hk₀).1, ?_⟩
    exact (Finset.mem_filter.mp hk₀).2
  have hpfxBounds := realizedLockingPrefix_bounds
    D.positiveEnumeration hgeom hpfx
  apply lockedGraph_of_realizedPrefix D N W m bound pfx
      (A := (N : ℤ)) (H := W + bound + cap)
      (R := D.heightNatConstant *
        (N + W + bound + cap + 1) ^ D.weight.natDegree)
  · intro x hx
    rw [realizedPrefixAnchors, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hkLong := (Finset.mem_filter.mp hk).1
    have hkWindow : k ∈ windowIndices D.positiveEnumeration N W :=
      (Finset.mem_filter.mp hkLong).1
    have hkIco := Finset.mem_Ico.mp hkWindow
    have hxLower : N < D.positiveEnumeration.a k :=
      (Erdos260.firstIndexAbove_spec D.positiveEnumeration N).trans_le
        (D.positiveEnumeration.strictMono.monotone hkIco.1)
    have hxUpper : D.positiveEnumeration.a k ≤ N + W :=
      Erdos260.firstIndexAbove_minimal D.positiveEnumeration (N + W) k hkIco.2
    constructor
    · exact_mod_cast (by omega : N ≤
        D.positiveEnumeration.a k + Erdos260.GapWord.span pfx)
    · exact_mod_cast (by omega :
        D.positiveEnumeration.a k + Erdos260.GapWord.span pfx ≤
          N + (W + bound + cap))
  · intro x hx
    rw [realizedPrefixAnchors, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hkLong := (Finset.mem_filter.mp hk).1
    have hkWindow : k ∈ windowIndices D.positiveEnumeration N W :=
      (Finset.mem_filter.mp hkLong).1
    have hkIco := Finset.mem_Ico.mp hkWindow
    have hxUpper : D.positiveEnumeration.a k ≤ N + W :=
      Erdos260.firstIndexAbove_minimal D.positiveEnumeration (N + W) k hkIco.2
    let y := D.positiveEnumeration.a k + Erdos260.GapWord.span pfx
    have hyLower : D.positiveFrom ≤ y := by
      dsimp [y]
      have hxLower : N < D.positiveEnumeration.a k :=
        (Erdos260.firstIndexAbove_spec D.positiveEnumeration N).trans_le
          (D.positiveEnumeration.strictMono.monotone hkIco.1)
      omega
    have hyUpper : y ≤ N + W + bound + cap := by
      dsimp [y]
      omega
    have hcarry := D.carry_natAbs_le hyLower
    exact hcarry.trans (by
      gcongr)
  · exact hcard
  · exact hlarge

/-- Fixed coefficient in the explicit locking threshold. -/
def lockingPolynomialConstant (D : CarrySeries) : ℕ :=
  (D.weight.natDegree + 2) * D.heightNatConstant

/-- Total polynomial exponent in the determinant-size bound. -/
def lockingPolynomialExponent (D : CarrySeries) : ℕ :=
  D.weight.natDegree + vandermondeExponent D.weight.natDegree

/-- An exact logarithmic threshold at which the locking divisibility power
dominates the full determinant bound. -/
def lockingThreshold (D : CarrySeries) (N : ℕ) : ℕ :=
  Nat.clog D.base (lockingPolynomialConstant D + 1) +
    lockingPolynomialExponent D * (Nat.log D.base (3 * N + 1) + 1)

/-- Canonical nonrare prefixes lock with no unproved size hypothesis once
their logarithmic threshold and the gap cap fit inside the anchor scale. -/
theorem lockedGraph_of_nonrarePrefix_explicit (D : CarrySeries)
    {N W m cap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hW : W ≤ N)
    (hscale : lockingThreshold D N + cap ≤ N)
    (pfx : Erdos260.GapWord)
    (hcard : D.weight.natDegree + 1 ≤
      (realizedPrefixIndices D N W m (lockingThreshold D N) pfx).card)
    (hpositiveFrom : D.positiveFrom ≤ N) :
    ∃ G : PolynomialGraph D.weight.natDegree,
      G.denominator ≤
        (W + lockingThreshold D N + cap) ^
          vandermondeExponent D.weight.natDegree ∧
      ∀ x ∈ realizedPrefixAnchors D N W m (lockingThreshold D N) pfx,
        G.poly.eval (x + Erdos260.GapWord.span pfx : ℚ) =
          (D.carry (x + Erdos260.GapWord.span pfx) : ℚ) := by
  classical
  let bound := lockingThreshold D N
  let X := 3 * N + 1
  let exponent := lockingPolynomialExponent D
  let constant := lockingPolynomialConstant D
  have hcardPos : 0 <
      (realizedPrefixIndices D N W m bound pfx).card :=
    (Nat.succ_pos D.weight.natDegree).trans_le hcard
  obtain ⟨k₀, hk₀⟩ := Finset.card_pos.mp hcardPos
  have hpfx : pfx ∈
      realizedLockingPrefixes D.positiveEnumeration N W m bound := by
    rw [realizedLockingPrefixes, Finset.mem_image]
    refine ⟨k₀, (Finset.mem_filter.mp hk₀).1, ?_⟩
    exact (Finset.mem_filter.mp hk₀).2
  have hpfxSpan : bound < Erdos260.GapWord.span pfx := by
    have hbounds := realizedLockingPrefix_bounds
      D.positiveEnumeration hgeom hpfx
    exact hbounds.2.1
  have hscale' : bound + cap ≤ N := by
    simpa only [bound] using hscale
  apply lockedGraph_of_nonrarePrefix D hgeom pfx hcard hpositiveFrom
  have hy : N + W + bound + cap + 1 ≤ X := by
    dsimp [X]
    omega
  have hH : W + bound + cap ≤ X := by
    dsimp [X]
    omega
  have hsize :
      (D.weight.natDegree + 2) *
          (D.heightNatConstant * (N + W + bound + cap + 1) ^
            D.weight.natDegree) *
          (W + bound + cap) ^ vandermondeExponent D.weight.natDegree ≤
        constant * X ^ exponent := by
    dsimp [constant, exponent, lockingPolynomialConstant,
      lockingPolynomialExponent]
    calc
      (D.weight.natDegree + 2) *
            (D.heightNatConstant * (N + W + bound + cap + 1) ^
              D.weight.natDegree) *
            (W + bound + cap) ^ vandermondeExponent D.weight.natDegree =
          ((D.weight.natDegree + 2) * D.heightNatConstant) *
            (N + W + bound + cap + 1) ^ D.weight.natDegree *
            (W + bound + cap) ^ vandermondeExponent D.weight.natDegree := by
        ring
      _ ≤ ((D.weight.natDegree + 2) * D.heightNatConstant) *
            X ^ D.weight.natDegree *
            X ^ vandermondeExponent D.weight.natDegree := by
        gcongr
      _ = ((D.weight.natDegree + 2) * D.heightNatConstant) *
            X ^ (D.weight.natDegree +
              vandermondeExponent D.weight.natDegree) := by
        rw [pow_add]
        ring
  have hpoly := CarrySeries.polynomial_lt_base_pow_logScale D.base_ge_two
    constant X exponent
  have hthreshold :
      Nat.clog D.base (constant + 1) +
          exponent * (Nat.log D.base X + 1) = bound := by
    rfl
  rw [hthreshold] at hpoly
  simpa only [bound] using hsize.trans_lt (hpoly.trans
    (Nat.pow_lt_pow_right
      (lt_of_lt_of_le (by decide : 1 < 2) D.base_ge_two) hpfxSpan))

end Erdos260.PolynomialWindow
