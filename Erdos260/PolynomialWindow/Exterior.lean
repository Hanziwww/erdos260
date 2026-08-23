import Erdos260.PolynomialWindow.Locking

/-!
# Exterior polynomial-graph estimates

This file formalizes the arithmetic separation and exponential top-state
growth used by the exterior branch, followed by the source encoding used in
its census.  The discrete sublevel estimate itself is proved in
`Polynomial.lean` as `integerSublevelSet_card_bound`.
-/

noncomputable section

open scoped BigOperators

namespace Erdos260.PolynomialWindow

/-! ## Rational separation at a certified scale -/

namespace PolynomialGraph

/-- Natural integral scale for the normalized top coefficient of a locked
graph. -/
def topStateScale {d : ℕ} (G : PolynomialGraph d)
    (Q : ℕ) (w : Polynomial ℤ) : ℕ :=
  G.denominator * Q * (w.coeff d).natAbs

theorem topStateScale_pos {d : ℕ} (G : PolynomialGraph d)
    {Q : ℕ} (hQ : 0 < Q) (w : Polynomial ℤ)
    (hw : 0 < w.coeff d) :
    0 < G.topStateScale Q w := by
  unfold topStateScale
  exact Nat.mul_pos (Nat.mul_pos G.denominator_pos hQ)
    (Int.natAbs_pos.mpr hw.ne')

/-- The normalized top state has an explicit integral multiple. -/
theorem topStateScale_mul_normalizedTopState {d : ℕ}
    (G : PolynomialGraph d) {Q : ℕ} (hQ : 0 < Q)
    (w : Polynomial ℤ) (hw : 0 < w.coeff d) :
    (G.topStateScale Q w : ℚ) * G.normalizedTopState Q w =
      (G.integralPoly.coeff d : ℚ) := by
  have hcert := congrArg (fun P : Polynomial ℚ => P.coeff d) G.certificate
  simp only [Polynomial.coeff_map, Polynomial.coeff_smul, smul_eq_mul]
    at hcert
  have hwabs : ((w.coeff d).natAbs : ℤ) = w.coeff d := by
    rw [Int.natCast_natAbs, abs_of_pos hw]
  have hQrat : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hwrat : (w.coeff d : ℚ) ≠ 0 := by exact_mod_cast hw.ne'
  have hwabsQ : ((w.coeff d).natAbs : ℚ) = (w.coeff d : ℚ) := by
    change (((w.coeff d).natAbs : ℤ) : ℚ) = (w.coeff d : ℚ)
    exact_mod_cast hwabs
  unfold topStateScale normalizedTopState topState
  push_cast
  rw [hwabsQ]
  rw [div_eq_mul_inv]
  field_simp
  simpa [mul_assoc, mul_comm, mul_left_comm] using hcert.symm

theorem coeff_eq_topWeight_mul_normalizedTopState {d : ℕ}
    (G : PolynomialGraph d) {Q : ℕ} (hQ : 0 < Q)
    (w : Polynomial ℤ) (hw : 0 < w.coeff d) :
    G.poly.coeff d =
      ((Q : ℚ) * (w.coeff d : ℚ)) * G.normalizedTopState Q w := by
  have hQrat : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hwrat : (w.coeff d : ℚ) ≠ 0 := by exact_mod_cast hw.ne'
  unfold normalizedTopState topState
  field_simp

theorem coeff_cast_eq_topWeight_mul_normalizedTopState {d : ℕ}
    (G : PolynomialGraph d) {Q : ℕ} (hQ : 0 < Q)
    (w : Polynomial ℤ) (hw : 0 < w.coeff d) :
    (G.poly.coeff d : ℝ) =
      ((Q : ℕ) : ℝ) * (w.coeff d : ℝ) *
        ((G.normalizedTopState Q w : ℚ) : ℝ) := by
  exact_mod_cast G.coeff_eq_topWeight_mul_normalizedTopState hQ w hw

end PolynomialGraph

/-- A nonzero rational whose multiple by the positive integer `T` is integral
has absolute value at least `1 / T`. -/
theorem inv_scale_le_abs_of_integral {T : ℕ} (hT : 0 < T)
    {μ : ℚ} {z : ℤ} (hscale : (T : ℚ) * μ = (z : ℚ)) (hμ : μ ≠ 0) :
    (1 : ℚ) / T ≤ |μ| := by
  have hz : z ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero] at hscale
    exact hμ (mul_eq_zero.mp hscale |>.resolve_left (by positivity))
  have hzabs : (1 : ℚ) ≤ |(z : ℚ)| := by
    have hzabsInt : (1 : ℤ) ≤ |z| := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hz))
    exact_mod_cast hzabsInt
  have hTq : (0 : ℚ) < T := by exact_mod_cast hT
  have habsScale : (T : ℚ) * |μ| = |(z : ℚ)| := by
    rw [← hscale, abs_mul, abs_of_pos hTq]
  rw [div_le_iff₀ hTq]
  rw [mul_comm, habsScale]
  exact hzabs

/-- A common integral scale for `μ` also provides the same scale for the upper
exterior excess `(b-1)μ-1`. -/
theorem upperExcess_integral_scale {T b : ℕ} {μ : ℚ} {z : ℤ}
    (hscale : (T : ℚ) * μ = (z : ℚ)) :
    (T : ℚ) * (((b - 1 : ℕ) : ℚ) * μ - 1) =
      (((b - 1 : ℕ) : ℤ) * z - T : ℤ) := by
  push_cast
  rw [mul_sub, mul_one]
  calc
    (T : ℚ) * (((b - 1 : ℕ) : ℚ) * μ) - T =
        ((b - 1 : ℕ) : ℚ) * ((T : ℚ) * μ) - T := by ring
    _ = ((b - 1 : ℕ) : ℚ) * (z : ℚ) - T := by rw [hscale]

/-- Quantitative separation from the two strict exterior boundaries. -/
theorem strictExterior_separation {T b : ℕ} (hT : 0 < T)
    {μ : ℚ} {z : ℤ} (hscale : (T : ℚ) * μ = (z : ℚ))
    (hext : μ < 0 ∨ 1 < ((b - 1 : ℕ) : ℚ) * μ) :
    (1 : ℚ) / T ≤ -μ ∨
      (1 : ℚ) / T ≤ ((b - 1 : ℕ) : ℚ) * μ - 1 := by
  rcases hext with hneg | hupp
  · left
    have hμ : μ ≠ 0 := ne_of_lt hneg
    have h := inv_scale_le_abs_of_integral hT hscale hμ
    rwa [abs_of_neg hneg] at h
  · right
    let E : ℚ := ((b - 1 : ℕ) : ℚ) * μ - 1
    have hEpos : 0 < E := by dsimp [E]; linarith
    have hEscale :
        (T : ℚ) * E = (((b - 1 : ℕ) : ℤ) * z - T : ℤ) := by
      exact upperExcess_integral_scale hscale
    have h := inv_scale_le_abs_of_integral hT hEscale hEpos.ne'
    simpa [E, abs_of_pos hEpos] using h

/-- A strict exterior normalized state of a locked graph is separated from
the boundary at its explicit integral scale. -/
theorem PolynomialGraph.normalizedTopState_strictExterior_separation
    {d b : ℕ} (G : PolynomialGraph d) {Q : ℕ} (hQ : 0 < Q)
    (w : Polynomial ℤ) (hw : 0 < w.coeff d)
    (hext : G.normalizedTopState Q w < 0 ∨
      1 < ((b - 1 : ℕ) : ℚ) * G.normalizedTopState Q w) :
    (1 : ℚ) / G.topStateScale Q w ≤ -G.normalizedTopState Q w ∨
      (1 : ℚ) / G.topStateScale Q w ≤
        ((b - 1 : ℕ) : ℚ) * G.normalizedTopState Q w - 1 := by
  exact strictExterior_separation (G.topStateScale_pos hQ w hw)
    (G.topStateScale_mul_normalizedTopState hQ w hw) hext

/-! ## Exponential growth after strict exit -/

/-- Lower exterior states move away from zero by at least the full base power
of the continuation span. -/
theorem lowerExterior_growth {b : ℕ} (hb : 2 ≤ b)
    (gaps : Erdos260.GapWord) {μ : ℝ} (hμ : μ < 0) :
    (b : ℝ) ^ Erdos260.GapWord.span gaps * (-μ) ≤
      -(topStateAlong b gaps μ) := by
  induction gaps generalizing μ with
  | nil => simp [Erdos260.GapWord.span]
  | cons g gs ih =>
      have hnext : (b : ℝ) ^ g * μ - 1 < 0 :=
        lowerExterior_forward hb hμ
      have hstep : (b : ℝ) ^ g * (-μ) ≤
          -((b : ℝ) ^ g * μ - 1) := by
        have hpow : 0 ≤ (b : ℝ) ^ g := by positivity
        nlinarith
      simp only [topStateAlong_cons, Erdos260.GapWord.span, List.sum_cons,
        pow_add]
      calc
        (b : ℝ) ^ g * (b : ℝ) ^ Erdos260.GapWord.span gs * (-μ) =
            (b : ℝ) ^ Erdos260.GapWord.span gs *
              ((b : ℝ) ^ g * (-μ)) := by ring
        _ ≤ (b : ℝ) ^ Erdos260.GapWord.span gs *
              (-((b : ℝ) ^ g * μ - 1)) := by
          gcongr
        _ ≤ -(topStateAlong b gs ((b : ℝ) ^ g * μ - 1)) :=
          ih hnext

/-- Upper exterior excess after a single positive gap. -/
theorem upperExcess_step_growth {b g : ℕ} (hb : 2 ≤ b) (hg : 0 < g)
    (μ : ℝ) :
    (b : ℝ) ^ g * ((b - 1 : ℝ) * μ - 1) ≤
      (b - 1 : ℝ) * ((b : ℝ) ^ g * μ - 1) - 1 := by
  have hbReal : (1 : ℝ) < b := by exact_mod_cast hb
  have hpow : (b : ℝ) ≤ (b : ℝ) ^ g := by
    calc
      (b : ℝ) = (b : ℝ) ^ 1 := by simp
      _ ≤ (b : ℝ) ^ g := pow_le_pow_right₀ hbReal.le (by omega)
  nlinarith

/-- Upper exterior excess grows by at least the full base power along a
positive continuation word. -/
theorem upperExterior_growth {b : ℕ} (hb : 2 ≤ b)
    {gaps : Erdos260.GapWord} (hgaps : Erdos260.GapWord.Positive gaps)
    {μ : ℝ} (hμ : 1 < (b - 1 : ℝ) * μ) :
    (b : ℝ) ^ Erdos260.GapWord.span gaps *
        ((b - 1 : ℝ) * μ - 1) ≤
      (b - 1 : ℝ) * topStateAlong b gaps μ - 1 := by
  induction gaps generalizing μ with
  | nil => simp [Erdos260.GapWord.span]
  | cons g gs ih =>
      have hg : 0 < g := hgaps g (by simp)
      have htail : Erdos260.GapWord.Positive gs := by
        intro q hq
        exact hgaps q (by simp [hq])
      have hnext : 1 <
          (b - 1 : ℝ) * ((b : ℝ) ^ g * μ - 1) :=
        upperExterior_forward hb hg hμ
      have hstep := upperExcess_step_growth hb hg μ
      simp only [topStateAlong_cons, Erdos260.GapWord.span, List.sum_cons,
        pow_add]
      calc
        (b : ℝ) ^ g * (b : ℝ) ^ Erdos260.GapWord.span gs *
              ((b - 1 : ℝ) * μ - 1) =
            (b : ℝ) ^ Erdos260.GapWord.span gs *
              ((b : ℝ) ^ g * ((b - 1 : ℝ) * μ - 1)) := by ring
        _ ≤ (b : ℝ) ^ Erdos260.GapWord.span gs *
              ((b - 1 : ℝ) * ((b : ℝ) ^ g * μ - 1) - 1) := by
          gcongr
        _ ≤ (b - 1 : ℝ) *
              topStateAlong b gs ((b : ℝ) ^ g * μ - 1) - 1 :=
          ih htail hnext

/-- Strict exterior separation followed by a positive continuation forces an
explicit exponential lower bound on the transformed top coefficient. -/
theorem transformedTopCoeff_abs_lower {d b Q : ℕ}
    (hb : 2 ≤ b) (hQ : 0 < Q)
    (G : PolynomialGraph d) (w : Polynomial ℤ)
    (hw : 0 < w.coeff d) (hwdeg : w.natDegree ≤ d)
    (gaps : Erdos260.GapWord) (hpositive : Erdos260.GapWord.Positive gaps)
    (hext : G.normalizedTopState Q w < 0 ∨
      1 < ((b - 1 : ℕ) : ℚ) * G.normalizedTopState Q w) :
    (b : ℝ) ^ Erdos260.GapWord.span gaps /
        ((G.topStateScale Q w : ℝ) * (b - 1 : ℝ)) ≤
      abs (((G.transformWord b Q w hwdeg gaps).poly.coeff d : ℚ) : ℝ) := by
  let μ : ℚ := G.normalizedTopState Q w
  let T := G.topStateScale Q w
  let A : ℝ := (Q : ℝ) * (w.coeff d : ℝ)
  let ν : ℚ :=
    (G.transformWord b Q w hwdeg gaps).normalizedTopState Q w
  have hTpos : (0 : ℝ) < T := by
    exact_mod_cast G.topStateScale_pos hQ w hw
  have hbReal : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbminus : (1 : ℝ) ≤ b - 1 := by linarith
  have hbminusPos : (0 : ℝ) < b - 1 := by linarith
  have hAone : (1 : ℝ) ≤ A := by
    have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hwone : (1 : ℝ) ≤ w.coeff d := by exact_mod_cast hw
    dsimp [A]
    nlinarith
  have hbpow : (0 : ℝ) < (b : ℝ) ^ Erdos260.GapWord.span gaps := by
    positivity
  have hAnonzero : (Q : ℚ) * (w.coeff d : ℚ) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast hQ.ne') (by exact_mod_cast hw.ne')
  have hν : (ν : ℝ) = topStateAlong b gaps (μ : ℝ) := by
    have hνQ := PolynomialGraph.normalizedTopState_transformWord
      G b Q w hwdeg hAnonzero gaps
    dsimp only [ν, μ]
    rw [hνQ]
    exact topStateAlongRat_cast b gaps (G.normalizedTopState Q w)
  have hcoeff :
      (((G.transformWord b Q w hwdeg gaps).poly.coeff d : ℚ) : ℝ) =
        A * (ν : ℝ) := by
    simpa only [A, ν] using
      PolynomialGraph.coeff_cast_eq_topWeight_mul_normalizedTopState
        (G.transformWord b Q w hwdeg gaps) hQ w hw
  have hscale : (T : ℚ) * μ = (G.integralPoly.coeff d : ℚ) := by
    exact G.topStateScale_mul_normalizedTopState hQ w hw
  have hdenomCompare :
      (b : ℝ) ^ Erdos260.GapWord.span gaps /
          ((T : ℝ) * (b - 1 : ℝ)) ≤
        (b : ℝ) ^ Erdos260.GapWord.span gaps / (T : ℝ) := by
    apply div_le_div_of_nonneg_left hbpow.le hTpos
    nlinarith
  rcases hext with hneg | hupp
  · have hnegμ : μ < 0 := by simpa only [μ] using hneg
    have hμne : μ ≠ 0 := ne_of_lt hnegμ
    have hsepQ := inv_scale_le_abs_of_integral
      (G.topStateScale_pos hQ w hw) hscale hμne
    have hsepQ' : (1 : ℚ) / T ≤ -μ := by
      simpa [abs_of_neg hnegμ] using hsepQ
    have hsepCast : ((((1 : ℚ) / T : ℚ)) : ℝ) ≤ ((-μ : ℚ) : ℝ) := by
      exact_mod_cast hsepQ'
    have hsep : (1 : ℝ) / T ≤ -(μ : ℝ) := by
      norm_num at hsepCast ⊢
      exact hsepCast
    have hscaled :
        (b : ℝ) ^ Erdos260.GapWord.span gaps / (T : ℝ) ≤
          (b : ℝ) ^ Erdos260.GapWord.span gaps * (-(μ : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hsep hbpow.le
      simpa [div_eq_mul_inv, mul_assoc] using this
    have hgrowth := lowerExterior_growth hb gaps
      (show (μ : ℝ) < 0 by exact_mod_cast hnegμ)
    rw [← hν] at hgrowth
    have hνneg : (ν : ℝ) < 0 := by
      have hpositiveRight : 0 < -(ν : ℝ) :=
        (div_pos hbpow hTpos).trans_le (hscaled.trans hgrowth)
      linarith
    rw [hcoeff, abs_mul, abs_of_nonneg (zero_le_one.trans hAone),
      abs_of_neg hνneg]
    exact hdenomCompare.trans
      (hscaled.trans (hgrowth.trans (by
        exact le_mul_of_one_le_left (by linarith : 0 ≤ -(ν : ℝ)) hAone)))
  · let E : ℚ := ((b - 1 : ℕ) : ℚ) * μ - 1
    have huppμ : 1 < ((b - 1 : ℕ) : ℚ) * μ := by
      simpa only [μ] using hupp
    have hEpos : 0 < E := by dsimp [E]; linarith
    have hEscale :
        (T : ℚ) * E =
          (((b - 1 : ℕ) : ℤ) * G.integralPoly.coeff d - T : ℤ) := by
      exact upperExcess_integral_scale hscale
    have hsepQ := inv_scale_le_abs_of_integral
      (G.topStateScale_pos hQ w hw) hEscale hEpos.ne'
    have hsepQ' : (1 : ℚ) / T ≤ E := by
      simpa [abs_of_pos hEpos] using hsepQ
    have hsepCast : ((((1 : ℚ) / T : ℚ)) : ℝ) ≤ ((E : ℚ) : ℝ) := by
      exact_mod_cast hsepQ'
    have hsep : (1 : ℝ) / T ≤ (E : ℝ) := by
      norm_num at hsepCast ⊢
      exact hsepCast
    have hscaled :
        (b : ℝ) ^ Erdos260.GapWord.span gaps / (T : ℝ) ≤
          (b : ℝ) ^ Erdos260.GapWord.span gaps * (E : ℝ) := by
      have := mul_le_mul_of_nonneg_left hsep hbpow.le
      simpa [div_eq_mul_inv, mul_assoc] using this
    have huppReal : 1 < (b - 1 : ℝ) * (μ : ℝ) := by
      have huppCast : (1 : ℝ) <
          ((((b - 1 : ℕ) : ℚ)) : ℝ) * (μ : ℝ) := by
        exact_mod_cast huppμ
      rw [show ((((b - 1 : ℕ) : ℚ)) : ℝ) = (b : ℝ) - 1 by
        norm_num [Nat.cast_sub (by omega : 1 ≤ b)]] at huppCast
      exact huppCast
    have hgrowth := upperExterior_growth hb hpositive huppReal
    rw [← hν] at hgrowth
    have hEcast : (E : ℝ) = (b - 1 : ℝ) * (μ : ℝ) - 1 := by
      dsimp [E]
      push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ b)]
      norm_num
    rw [hEcast] at hscaled
    have hνpos : (0 : ℝ) < ν := by
      nlinarith [hscaled, hbpow]
    rw [hcoeff, abs_mul, abs_of_nonneg (zero_le_one.trans hAone),
      abs_of_pos hνpos]
    have htarget :
        (b : ℝ) ^ Erdos260.GapWord.span gaps /
            ((T : ℝ) * (b - 1 : ℝ)) ≤ (ν : ℝ) := by
      apply (div_le_iff₀ (mul_pos hTpos hbminusPos)).2
      have hscaled' := hscaled.trans hgrowth
      field_simp [hTpos.ne', hbminusPos.ne'] at hscaled' ⊢
      nlinarith
    exact htarget.trans (le_mul_of_one_le_left hνpos.le hAone)

/-! ## Canonical strict-exterior suffix and selected word -/

/-- Closed complement of the strict exterior region. -/
theorem nonStrictExterior_bounds {b : ℕ} (_hb : 2 ≤ b) {μ : ℝ}
    (hμ : ¬StrictExteriorState b μ) :
    0 ≤ μ ∧ (b - 1 : ℝ) * μ ≤ 1 := by
  unfold StrictExteriorState at hμ
  push Not at hμ
  exact hμ

/-- Positive gaps up to `cap` whose successor state is not strictly
exterior. -/
noncomputable def nonExteriorSuccessorGaps (b : ℕ) (μ : ℝ) (cap : ℕ) :
    Finset ℕ := by
  classical
  exact (Finset.Icc 1 cap).filter fun g =>
    ¬StrictExteriorState b ((b : ℝ) ^ g * μ - 1)

/-- At any state there are at most two positive gaps that keep the next
state in the closed interior/boundary band. -/
theorem nonExteriorSuccessorGaps_card_le_two {b : ℕ} (hb : 2 ≤ b)
    (μ : ℝ) (cap : ℕ) :
    (nonExteriorSuccessorGaps b μ cap).card ≤ 2 := by
  classical
  let s := nonExteriorSuccessorGaps b μ cap
  by_cases hs : s.Nonempty
  · let g0 := s.min' hs
    have hg0mem : g0 ∈ s := s.min'_mem hs
    have hg0state :
        ¬StrictExteriorState b ((b : ℝ) ^ g0 * μ - 1) := by
      exact (Finset.mem_filter.mp hg0mem).2
    have hg0bounds := nonStrictExterior_bounds hb hg0state
    have hg0lower : (1 : ℝ) ≤ (b : ℝ) ^ g0 * μ := by
      linarith [hg0bounds.1]
    have hμpos : 0 < μ := by
      have hpowpos : (0 : ℝ) < (b : ℝ) ^ g0 := by positivity
      nlinarith
    have hsubset : s ⊆ Finset.Icc g0 (g0 + 1) := by
      intro g hg
      have hg0g : g0 ≤ g := s.min'_le g hg
      have hgstate :
          ¬StrictExteriorState b ((b : ℝ) ^ g * μ - 1) :=
        (Finset.mem_filter.mp hg).2
      have hgbounds := nonStrictExterior_bounds hb hgstate
      have hbReal : (2 : ℝ) ≤ b := by exact_mod_cast hb
      have hbminus : (1 : ℝ) ≤ b - 1 := by linarith
      have hνle : (b : ℝ) ^ g * μ - 1 ≤ 1 := by
        have hνnonneg : 0 ≤ (b : ℝ) ^ g * μ - 1 := hgbounds.1
        have hmulLower :
            (b : ℝ) ^ g * μ - 1 ≤
              (b - 1 : ℝ) * ((b : ℝ) ^ g * μ - 1) := by
          exact le_mul_of_one_le_left hνnonneg hbminus
        exact hmulLower.trans hgbounds.2
      have hgupper : (b : ℝ) ^ g * μ ≤ 2 := by linarith
      have hgle : g ≤ g0 + 1 := by
        by_contra hnot
        have hexp : g0 + 2 ≤ g := by omega
        have hpow :
            (b : ℝ) ^ (g0 + 2) ≤ (b : ℝ) ^ g := by
          exact pow_le_pow_right₀
            (by exact_mod_cast (show 1 ≤ b by omega)) hexp
        have hmul :
            (b : ℝ) ^ (g0 + 2) * μ ≤ (b : ℝ) ^ g * μ :=
          mul_le_mul_of_nonneg_right hpow hμpos.le
        have hlarge : (4 : ℝ) ≤ (b : ℝ) ^ (g0 + 2) * μ := by
          rw [pow_add]
          have hbsq : (4 : ℝ) ≤ (b : ℝ) ^ (2 : ℕ) := by
            nlinarith [sq_nonneg ((b : ℝ) - 2)]
          nlinarith
        linarith
      exact Finset.mem_Icc.mpr ⟨hg0g, hgle⟩
    calc
      s.card ≤ (Finset.Icc g0 (g0 + 1)).card :=
        Finset.card_le_card hsubset
      _ = 2 := by simp; omega
  · simp only [Finset.not_nonempty_iff_eq_empty] at hs
    simp [s, hs]

/-- Exact-length words whose state is non-exterior at the start of every
listed gap.  The final gap may be the transition into the exterior region. -/
noncomputable def preExteriorCandidates (b : ℕ) (μ : ℝ) (cap : ℕ) :
    ℕ → Finset Erdos260.GapWord
  | 0 => {[]}
  | r + 1 => by
      classical
      exact if ¬StrictExteriorState b μ then
        (Finset.Icc 1 cap).biUnion fun g =>
          (preExteriorCandidates b ((b : ℝ) ^ g * μ - 1) cap r).image
            fun tail => g :: tail
      else ∅

theorem preExteriorCandidates_eq_empty_of_strict {b : ℕ} {μ : ℝ}
    {cap r : ℕ} (hμ : StrictExteriorState b μ) :
    preExteriorCandidates b μ cap (r + 1) = ∅ := by
  simp [preExteriorCandidates, hμ]

/-- The state-determined portion has binary branching; only its final exit
gap has `cap` choices. -/
theorem preExteriorCandidates_card_le {b cap r : ℕ} (hb : 2 ≤ b)
    (μ : ℝ) :
    (preExteriorCandidates b μ cap r).card ≤
      if r = 0 then 1 else cap * 2 ^ (r - 1) := by
  classical
  induction r using Nat.twoStepInduction generalizing μ with
  | zero => simp [preExteriorCandidates]
  | one =>
      by_cases hμ : StrictExteriorState b μ
      · simp [preExteriorCandidates, hμ]
      · have hcard := Finset.card_biUnion_le
          (s := Finset.Icc 1 cap)
          (t := fun g =>
            (preExteriorCandidates b ((b : ℝ) ^ g * μ - 1) cap 0).image
              fun tail => g :: tail)
        have hone (g : ℕ) :
            ((preExteriorCandidates b ((b : ℝ) ^ g * μ - 1) cap 0).image
              fun tail => g :: tail).card ≤ 1 := by
          exact Finset.card_image_le.trans (by simp [preExteriorCandidates])
        calc
          (preExteriorCandidates b μ cap 1).card ≤
              ∑ g ∈ Finset.Icc 1 cap,
                ((preExteriorCandidates b ((b : ℝ) ^ g * μ - 1) cap 0).image
                  fun tail => g :: tail).card := by
            simpa [preExteriorCandidates, hμ] using hcard
          _ ≤ ∑ _g ∈ Finset.Icc 1 cap, 1 := by
            exact Finset.sum_le_sum fun g _ => hone g
          _ = cap := by simp
          _ = (if 1 = 0 then 1 else cap * 2 ^ (1 - 1)) := by simp
  | more r ih0 ih1 =>
      by_cases hμ : StrictExteriorState b μ
      · simp [preExteriorCandidates, hμ]
      · let successors := nonExteriorSuccessorGaps b μ cap
        let family : ℕ → Finset Erdos260.GapWord := fun g =>
          (preExteriorCandidates b ((b : ℝ) ^ g * μ - 1) cap (r + 1)).image
            fun tail => g :: tail
        have hunion :
            (Finset.Icc 1 cap).biUnion family =
              successors.biUnion family := by
          apply Finset.Subset.antisymm
          · intro word hword
            rw [Finset.mem_biUnion] at hword
            obtain ⟨g, hgIcc, hgword⟩ := hword
            rw [Finset.mem_image] at hgword
            obtain ⟨tail, htail, rfl⟩ := hgword
            have hnext :
                ¬StrictExteriorState b ((b : ℝ) ^ g * μ - 1) := by
              intro hstrict
              rw [preExteriorCandidates_eq_empty_of_strict hstrict] at htail
              simp at htail
            rw [Finset.mem_biUnion]
            refine ⟨g, ?_, ?_⟩
            · exact Finset.mem_filter.mpr ⟨hgIcc, hnext⟩
            · exact Finset.mem_image.mpr ⟨tail, htail, rfl⟩
          · intro word hword
            rw [Finset.mem_biUnion] at hword ⊢
            obtain ⟨g, hgsucc, hgword⟩ := hword
            exact ⟨g, (Finset.mem_filter.mp hgsucc).1, hgword⟩
        have hcardUnion := Finset.card_biUnion_le
          (s := successors) (t := family)
        have hfamily (g : ℕ) :
            (family g).card ≤ cap * 2 ^ r := by
          have hi := ih1 ((b : ℝ) ^ g * μ - 1)
          have hrne : r + 1 ≠ 0 := by omega
          exact Finset.card_image_le.trans (by
            simpa only [hrne, if_false, Nat.add_sub_cancel] using hi)
        have hsucc := nonExteriorSuccessorGaps_card_le_two hb μ cap
        calc
          (preExteriorCandidates b μ cap (r + 2)).card =
              ((Finset.Icc 1 cap).biUnion family).card := by
            simp [preExteriorCandidates, hμ, family]
          _ = (successors.biUnion family).card := by rw [hunion]
          _ ≤ ∑ g ∈ successors, (family g).card := hcardUnion
          _ ≤ ∑ _g ∈ successors, cap * 2 ^ r := by
            exact Finset.sum_le_sum fun g _ => hfamily g
          _ = successors.card * (cap * 2 ^ r) := by simp
          _ ≤ 2 * (cap * 2 ^ r) := Nat.mul_le_mul_right _ hsucc
          _ = cap * 2 ^ ((r + 2) - 1) := by
            rw [show (r + 2) - 1 = r + 1 by omega, pow_succ]
            ring
          _ = (if r + 2 = 0 then 1 else cap * 2 ^ ((r + 2) - 1)) := by
            simp

/-- Prefix before the first strictly exterior state. -/
noncomputable def preExteriorWord (b : ℕ) :
    Erdos260.GapWord → ℝ → Erdos260.GapWord
  | [], _μ => []
  | g :: gs, μ => by
      classical
      exact if StrictExteriorState b μ then []
        else g :: preExteriorWord b gs ((b : ℝ) ^ g * μ - 1)

/-- Suffix beginning at the first strictly exterior state. -/
noncomputable def strictExteriorSuffix (b : ℕ) :
    Erdos260.GapWord → ℝ → Erdos260.GapWord
  | [], _μ => []
  | g :: gs, μ => by
      classical
      exact if StrictExteriorState b μ then g :: gs
        else strictExteriorSuffix b gs ((b : ℝ) ^ g * μ - 1)

theorem preExteriorWord_append_strictExteriorSuffix (b : ℕ)
    (gaps : Erdos260.GapWord) (μ : ℝ) :
    preExteriorWord b gaps μ ++ strictExteriorSuffix b gaps μ = gaps := by
  induction gaps generalizing μ with
  | nil => rfl
  | cons g gs ih =>
      by_cases hext : StrictExteriorState b μ
      · simp [preExteriorWord, strictExteriorSuffix, hext]
      · simp only [preExteriorWord, strictExteriorSuffix, hext, if_false,
          List.cons_append]
        rw [ih]

/-- The canonical pre-exterior word belongs to the binary branching census
at its actual length. -/
theorem preExteriorWord_mem_candidates {b cap : ℕ}
    {gaps : Erdos260.GapWord}
    (hpositive : Erdos260.GapWord.Positive gaps)
    (hcap : ∀ g ∈ gaps, g ≤ cap) (μ : ℝ) :
    preExteriorWord b gaps μ ∈
      preExteriorCandidates b μ cap (preExteriorWord b gaps μ).length := by
  induction gaps generalizing μ with
  | nil => simp [preExteriorWord, preExteriorCandidates]
  | cons g gs ih =>
      have hgpos : 1 ≤ g := hpositive g (by simp)
      have hgcap : g ≤ cap := hcap g (by simp)
      have hgs : Erdos260.GapWord.Positive gs := by
        intro q hq
        exact hpositive q (by simp [hq])
      have hcapgs : ∀ q ∈ gs, q ≤ cap := by
        intro q hq
        exact hcap q (by simp [hq])
      by_cases hext : StrictExteriorState b μ
      · simp [preExteriorWord, hext, preExteriorCandidates]
      · let ν := (b : ℝ) ^ g * μ - 1
        have htail := ih hgs hcapgs ν
        simp only [preExteriorWord, hext, if_false, List.length_cons]
        rw [preExteriorCandidates, if_pos hext]
        rw [Finset.mem_biUnion]
        refine ⟨g, Finset.mem_Icc.mpr ⟨hgpos, hgcap⟩, ?_⟩
        rw [Finset.mem_image]
        exact ⟨preExteriorWord b gs ν, htail, rfl⟩

/-- Every member of the exact-length census has the advertised length. -/
theorem preExteriorCandidates_length {b cap r : ℕ} {μ : ℝ}
    {word : Erdos260.GapWord}
    (hword : word ∈ preExteriorCandidates b μ cap r) :
    word.length = r := by
  induction r generalizing μ word with
  | zero => simpa [preExteriorCandidates] using hword
  | succ r ih =>
      by_cases hμ : StrictExteriorState b μ
      · rw [preExteriorCandidates_eq_empty_of_strict hμ] at hword
        simp at hword
      · rw [preExteriorCandidates, if_pos hμ,
            Finset.mem_biUnion] at hword
        obtain ⟨g, _hg, htail⟩ := hword
        rw [Finset.mem_image] at htail
        obtain ⟨tail, htail, rfl⟩ := htail
        simp only [List.length_cons]
        rw [ih htail]

/-- Pre-exterior records of every length up to `m`.  Keeping the length in the
record is important: it is part of the recoverable source data in the exterior
census. -/
noncomputable def boundedPreExteriorCandidates (b : ℕ) (μ : ℝ)
    (cap m : ℕ) : Finset Erdos260.GapWord :=
  (Finset.range (m + 1)).biUnion fun r =>
    preExteriorCandidates b μ cap r

theorem mem_boundedPreExteriorCandidates_iff {b cap m : ℕ} {μ : ℝ}
    {word : Erdos260.GapWord} :
    word ∈ boundedPreExteriorCandidates b μ cap m ↔
      word.length ≤ m ∧ word ∈ preExteriorCandidates b μ cap word.length := by
  classical
  rw [boundedPreExteriorCandidates, Finset.mem_biUnion]
  constructor
  · rintro ⟨r, hr, hword⟩
    have hrle : r ≤ m := by
      simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hr
    have hlength : word.length = r := preExteriorCandidates_length hword
    subst r
    exact ⟨hrle, hword⟩
  · rintro ⟨hlength, hword⟩
    exact ⟨word.length,
      by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hlength,
      hword⟩

/-- Uniform record census before the first strict exterior state.  The loose
factor `m + 1` pays for recording the exact length; the state-determined part
has only binary branching. -/
theorem boundedPreExteriorCandidates_card_le {b cap m : ℕ}
    (hb : 2 ≤ b) (μ : ℝ) :
    (boundedPreExteriorCandidates b μ cap m).card ≤
      (m + 1) * (1 + cap * 2 ^ m) := by
  classical
  have hunion := Finset.card_biUnion_le
    (s := Finset.range (m + 1))
    (t := fun r => preExteriorCandidates b μ cap r)
  have hterm (r : ℕ) (hr : r ∈ Finset.range (m + 1)) :
      (preExteriorCandidates b μ cap r).card ≤ 1 + cap * 2 ^ m := by
    have hrle : r ≤ m := by
      simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hr
    have hcard := preExteriorCandidates_card_le (b := b) (cap := cap)
      (r := r) hb μ
    cases r with
    | zero => simp [preExteriorCandidates]
    | succ r =>
        simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one] at hcard
        have hp : 2 ^ r ≤ 2 ^ m :=
          Nat.pow_le_pow_right (by omega) (by omega)
        exact hcard.trans <|
          (Nat.mul_le_mul_left cap hp).trans (Nat.le_add_left _ _)
  calc
    (boundedPreExteriorCandidates b μ cap m).card ≤
        ∑ r ∈ Finset.range (m + 1),
          (preExteriorCandidates b μ cap r).card := hunion
    _ ≤ ∑ _r ∈ Finset.range (m + 1), (1 + cap * 2 ^ m) := by
      exact Finset.sum_le_sum fun r hr => hterm r hr
    _ = (m + 1) * (1 + cap * 2 ^ m) := by simp

/-- Every actual positive bounded-gap pre-exterior record is captured by the
bounded census as soon as its length is at most `m`. -/
theorem preExteriorWord_mem_boundedCandidates {b cap m : ℕ}
    {gaps : Erdos260.GapWord}
    (hpositive : Erdos260.GapWord.Positive gaps)
    (hcap : ∀ g ∈ gaps, g ≤ cap)
    (μ : ℝ) (hlength : (preExteriorWord b gaps μ).length ≤ m) :
    preExteriorWord b gaps μ ∈ boundedPreExteriorCandidates b μ cap m := by
  rw [mem_boundedPreExteriorCandidates_iff]
  exact ⟨hlength, preExteriorWord_mem_candidates hpositive hcap μ⟩

theorem strictExteriorSuffix_positive {b : ℕ}
    {gaps : Erdos260.GapWord} (hpositive : Erdos260.GapWord.Positive gaps)
    (μ : ℝ) :
    Erdos260.GapWord.Positive (strictExteriorSuffix b gaps μ) := by
  intro g hg
  apply hpositive g
  have hmem : g ∈ preExteriorWord b gaps μ ++ strictExteriorSuffix b gaps μ := by
    simp [hg]
  rwa [preExteriorWord_append_strictExteriorSuffix] at hmem

/-- The strict-exterior span is exactly the span of the canonical suffix. -/
theorem span_strictExteriorSuffix_eq_exteriorSpan {b : ℕ} (hb : 2 ≤ b)
    {gaps : Erdos260.GapWord} (hpositive : Erdos260.GapWord.Positive gaps)
    (μ : ℝ) :
    Erdos260.GapWord.span (strictExteriorSuffix b gaps μ) =
      exteriorSpanAlong b gaps μ := by
  induction gaps generalizing μ with
  | nil => simp [strictExteriorSuffix, exteriorSpanAlong,
      Erdos260.GapWord.span]
  | cons g gs ih =>
      have hgs : Erdos260.GapWord.Positive gs := by
        intro q hq
        exact hpositive q (by simp [hq])
      by_cases hext : StrictExteriorState b μ
      · rw [exteriorSpanAlong_eq_span_of_strictExterior hb hpositive hext]
        simp [strictExteriorSuffix, hext]
      · simp only [strictExteriorSuffix, exteriorSpanAlong, hext, if_false,
          zero_add]
        exact ih hgs ((b : ℝ) ^ g * μ - 1)

/-- State at the start of the canonical strict-exterior suffix. -/
noncomputable def exteriorEntryState (b : ℕ)
    (gaps : Erdos260.GapWord) (μ : ℝ) : ℝ :=
  topStateAlong b (preExteriorWord b gaps μ) μ

theorem exteriorEntryState_strict {b : ℕ}
    {gaps : Erdos260.GapWord} {μ : ℝ}
    (hne : strictExteriorSuffix b gaps μ ≠ []) :
    StrictExteriorState b (exteriorEntryState b gaps μ) := by
  induction gaps generalizing μ with
  | nil => exact (hne rfl).elim
  | cons g gs ih =>
      by_cases hext : StrictExteriorState b μ
      · rw [exteriorEntryState, preExteriorWord, if_pos hext,
            topStateAlong_nil]
        exact hext
      · have htail :
            strictExteriorSuffix b gs ((b : ℝ) ^ g * μ - 1) ≠ [] := by
          simpa [strictExteriorSuffix, hext] using hne
        have hi := ih htail
        simpa [exteriorEntryState, preExteriorWord, hext,
          topStateAlong] using hi

/-- Short selected word beginning at strict exit. -/
noncomputable def selectedExteriorWord (b : ℕ)
    (gaps : Erdos260.GapWord) (μ : ℝ) (threshold : ℕ) :
    Erdos260.GapWord :=
  (strictExteriorSuffix b gaps μ).firstPrefixAbove threshold

/-- Exact selected-word bounds used in the exterior census. -/
theorem selectedExteriorWord_bounds {b cap threshold : ℕ} (hb : 2 ≤ b)
    {gaps : Erdos260.GapWord} (hpositive : Erdos260.GapWord.Positive gaps)
    (hcap : ∀ g ∈ gaps, g ≤ cap) (μ : ℝ)
    (hspan : threshold < exteriorSpanAlong b gaps μ) :
    StrictExteriorState b (exteriorEntryState b gaps μ) ∧
      Erdos260.GapWord.Positive
        (selectedExteriorWord b gaps μ threshold) ∧
      threshold < Erdos260.GapWord.span
        (selectedExteriorWord b gaps μ threshold) ∧
      Erdos260.GapWord.span (selectedExteriorWord b gaps μ threshold) ≤
        threshold + cap ∧
      (selectedExteriorWord b gaps μ threshold).length ≤ gaps.length := by
  let suffix := strictExteriorSuffix b gaps μ
  have hsuffixPositive : Erdos260.GapWord.Positive suffix :=
    strictExteriorSuffix_positive hpositive μ
  have hsuffixSpan : threshold < Erdos260.GapWord.span suffix := by
    rw [span_strictExteriorSuffix_eq_exteriorSpan hb hpositive]
    exact hspan
  have hsuffixNe : suffix ≠ [] := by
    intro hzero
    rw [hzero] at hsuffixSpan
    simp [Erdos260.GapWord.span] at hsuffixSpan
  have hcapSuffix : ∀ g ∈ suffix, g ≤ cap := by
    intro g hg
    apply hcap g
    have hmem : g ∈ preExteriorWord b gaps μ ++ suffix := by simp [hg]
    rwa [preExteriorWord_append_strictExteriorSuffix] at hmem
  refine ⟨exteriorEntryState_strict hsuffixNe,
    Erdos260.GapWord.firstPrefixAbove_positive
      suffix threshold hsuffixPositive,
    Erdos260.GapWord.lt_span_firstPrefixAbove_of_lt_span
      suffix threshold hsuffixSpan,
    Erdos260.GapWord.span_firstPrefixAbove_le_add
      suffix threshold cap hcapSuffix, ?_⟩
  have hsuffixLen : suffix.length ≤ gaps.length := by
    apply List.IsSuffix.length_le
    exact ⟨preExteriorWord b gaps μ, by
      simpa [suffix] using
        preExteriorWord_append_strictExteriorSuffix b gaps μ⟩
  exact (Erdos260.GapWord.firstPrefixAbove_length_le suffix threshold).trans
    hsuffixLen

/-! ## Exterior entry and the selected graph transform -/

/-- The locked graph transported to the first strictly exterior state. -/
noncomputable def PolynomialGraph.exteriorEntryGraph {d : ℕ}
    (G : PolynomialGraph d) (b Q : ℕ) (w : Polynomial ℤ)
    (hwdeg : w.natDegree ≤ d) (gaps : Erdos260.GapWord) :
    PolynomialGraph d :=
  G.transformWord b Q w hwdeg
    (preExteriorWord b gaps
      ((G.normalizedTopState Q w : ℚ) : ℝ))

/-- The rational state of the entry graph is exactly the real state selected
by `preExteriorWord`. -/
theorem PolynomialGraph.exteriorEntryGraph_state_cast {d b Q : ℕ}
    (G : PolynomialGraph d) (w : Polynomial ℤ)
    (hwdeg : w.natDegree ≤ d)
    (hA : (Q : ℚ) * (w.coeff d : ℚ) ≠ 0)
    (gaps : Erdos260.GapWord) :
    (((G.exteriorEntryGraph b Q w hwdeg gaps).normalizedTopState Q w : ℚ) : ℝ) =
      exteriorEntryState b gaps
        ((G.normalizedTopState Q w : ℚ) : ℝ) := by
  unfold PolynomialGraph.exteriorEntryGraph exteriorEntryState
  rw [PolynomialGraph.normalizedTopState_transformWord
    G b Q w hwdeg hA]
  exact topStateAlongRat_cast b
    (preExteriorWord b gaps
      ((G.normalizedTopState Q w : ℚ) : ℝ))
    (G.normalizedTopState Q w)

/-- A nonempty canonical exterior suffix supplies the strict rational state
required by the coefficient-growth lemma. -/
theorem PolynomialGraph.exteriorEntryGraph_strict {d b Q : ℕ}
    (hb : 2 ≤ b) (G : PolynomialGraph d) (w : Polynomial ℤ)
    (hwdeg : w.natDegree ≤ d)
    (hA : (Q : ℚ) * (w.coeff d : ℚ) ≠ 0)
    {gaps : Erdos260.GapWord}
    (hne : strictExteriorSuffix b gaps
      ((G.normalizedTopState Q w : ℚ) : ℝ) ≠ []) :
    (G.exteriorEntryGraph b Q w hwdeg gaps).normalizedTopState Q w < 0 ∨
      1 < ((b - 1 : ℕ) : ℚ) *
        (G.exteriorEntryGraph b Q w hwdeg gaps).normalizedTopState Q w := by
  have hstrict := exteriorEntryState_strict (b := b) hne
  have hstate := G.exteriorEntryGraph_state_cast (b := b) w hwdeg hA gaps
  unfold StrictExteriorState at hstrict
  rw [← hstate] at hstrict
  rcases hstrict with hneg | hupp
  · left
    exact_mod_cast hneg
  · right
    have hbsub :
        (((b - 1 : ℕ) : ℚ) : ℝ) = (b : ℝ) - 1 := by
      norm_num [Nat.cast_sub (by omega : 1 ≤ b)]
    rw [← hbsub] at hupp
    exact_mod_cast hupp

@[simp]
theorem PolynomialGraph.exteriorEntryGraph_topStateScale {d b Q : ℕ}
    (G : PolynomialGraph d) (w : Polynomial ℤ)
    (hwdeg : w.natDegree ≤ d) (gaps : Erdos260.GapWord) :
    (G.exteriorEntryGraph b Q w hwdeg gaps).topStateScale Q w =
      G.topStateScale Q w := by
  simp [PolynomialGraph.exteriorEntryGraph,
    PolynomialGraph.topStateScale]

/-- The graph after the selected strict-exterior word. -/
noncomputable def PolynomialGraph.selectedExteriorGraph {d : ℕ}
    (G : PolynomialGraph d) (b Q : ℕ) (w : Polynomial ℤ)
    (hwdeg : w.natDegree ≤ d) (gaps : Erdos260.GapWord)
    (threshold : ℕ) : PolynomialGraph d :=
  (G.exteriorEntryGraph b Q w hwdeg gaps).transformWord b Q w hwdeg
    (selectedExteriorWord b gaps
      ((G.normalizedTopState Q w : ℚ) : ℝ) threshold)

/-- The selected strict-exterior continuation has the quantitative leading
coefficient lower bound used by the coordinate census. -/
theorem PolynomialGraph.selectedExteriorTopCoeff_abs_lower {d b Q : ℕ}
    (hb : 2 ≤ b) (hQ : 0 < Q)
    (G : PolynomialGraph d) (w : Polynomial ℤ)
    (hw : 0 < w.coeff d) (hwdeg : w.natDegree ≤ d)
    {gaps : Erdos260.GapWord}
    (hpositive : Erdos260.GapWord.Positive gaps)
    {threshold : ℕ}
    (hspan : threshold < exteriorSpanAlong b gaps
      ((G.normalizedTopState Q w : ℚ) : ℝ)) :
    (b : ℝ) ^ Erdos260.GapWord.span
          (selectedExteriorWord b gaps
            ((G.normalizedTopState Q w : ℚ) : ℝ) threshold) /
        ((G.topStateScale Q w : ℝ) * (b - 1 : ℝ)) ≤
      abs ((((G.selectedExteriorGraph b Q w hwdeg gaps threshold).poly.coeff d : ℚ) : ℝ)) := by
  let μ : ℝ := ((G.normalizedTopState Q w : ℚ) : ℝ)
  let suffix := strictExteriorSuffix b gaps μ
  let selected := selectedExteriorWord b gaps μ threshold
  have hsuffixSpan : threshold < Erdos260.GapWord.span suffix := by
    rw [span_strictExteriorSuffix_eq_exteriorSpan hb hpositive]
    exact hspan
  have hsuffixNe : suffix ≠ [] := by
    intro hzero
    rw [hzero] at hsuffixSpan
    simp [Erdos260.GapWord.span] at hsuffixSpan
  have hselectedPositive : Erdos260.GapWord.Positive selected := by
    apply Erdos260.GapWord.firstPrefixAbove_positive
    exact strictExteriorSuffix_positive hpositive μ
  have hA : (Q : ℚ) * (w.coeff d : ℚ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hQ.ne') (by exact_mod_cast hw.ne')
  have hext := G.exteriorEntryGraph_strict hb w hwdeg hA hsuffixNe
  have hlower := transformedTopCoeff_abs_lower hb hQ
    (G.exteriorEntryGraph b Q w hwdeg gaps) w hw hwdeg selected
    hselectedPositive hext
  simpa only [PolynomialGraph.selectedExteriorGraph, selected, μ,
    PolynomialGraph.exteriorEntryGraph_topStateScale] using hlower

/-- The prefix before strict exit followed by the selected word is an actual
prefix of the original continuation. -/
theorem preExteriorWord_append_selectedExteriorWord_isPrefix (b : ℕ)
    (gaps : Erdos260.GapWord) (μ : ℝ) (threshold : ℕ) :
    (preExteriorWord b gaps μ ++
      selectedExteriorWord b gaps μ threshold).IsPrefix gaps := by
  have hselected :
      (selectedExteriorWord b gaps μ threshold).IsPrefix
        (strictExteriorSuffix b gaps μ) :=
    Erdos260.GapWord.firstPrefixAbove_isPrefix
      (strictExteriorSuffix b gaps μ) threshold
  obtain ⟨tail, htail⟩ := hselected
  refine ⟨tail, ?_⟩
  calc
    (preExteriorWord b gaps μ ++
          selectedExteriorWord b gaps μ threshold) ++ tail =
        preExteriorWord b gaps μ ++
          (selectedExteriorWord b gaps μ threshold ++ tail) := by
            rw [List.append_assoc]
    _ = preExteriorWord b gaps μ ++ strictExteriorSuffix b gaps μ := by
      rw [htail]
    _ = gaps := preExteriorWord_append_strictExteriorSuffix b gaps μ

/-- If the ambient continuation is genuine, the selected exterior graph
passes through the genuine carry at its selected terminal coordinate. -/
theorem PolynomialGraph.selectedExteriorGraph_eval_carry
    (D : CarrySeries)
    (G : PolynomialGraph D.weight.natDegree) {x : ℕ}
    {gaps : Erdos260.GapWord} {threshold : ℕ}
    (hfit : G.poly.eval (x : ℚ) = (D.carry x : ℚ))
    (hword : D.GapWordAt x gaps) :
    let μ : ℝ := ((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)
    let pre := preExteriorWord D.base gaps μ
    let selected := selectedExteriorWord D.base gaps μ threshold
    (G.selectedExteriorGraph D.base D.denominator D.weight le_rfl
        gaps threshold).poly.eval
          ((x + Erdos260.GapWord.span pre +
            Erdos260.GapWord.span selected : ℕ) : ℚ) =
      (D.carry (x + Erdos260.GapWord.span pre +
        Erdos260.GapWord.span selected) : ℚ) := by
  let μ : ℝ := ((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)
  let pre := preExteriorWord D.base gaps μ
  let selected := selectedExteriorWord D.base gaps μ threshold
  have hpref : (pre ++ selected).IsPrefix gaps := by
    simpa only [pre, selected, μ] using
      preExteriorWord_append_selectedExteriorWord_isPrefix
        D.base gaps μ threshold
  have hactual : D.GapWordAt x (pre ++ selected) :=
    CarrySeries.GapWordAt.prefix hpref hword
  have hcontinued := G.transformWord_eval_carry D hfit hactual
  have hgraph :
      G.transformWord D.base D.denominator D.weight le_rfl
          (pre ++ selected) =
        G.selectedExteriorGraph D.base D.denominator D.weight le_rfl
          gaps threshold := by
    rw [PolynomialGraph.transformWord_append]
    rfl
  rw [hgraph] at hcontinued
  simpa only [Erdos260.GapWord.span, List.sum_append,
    Nat.add_assoc, pre, selected, μ] using hcontinued

/-- Real polynomial represented by the selected exterior graph. -/
def PolynomialGraph.selectedExteriorRealPoly {d : ℕ}
    (G : PolynomialGraph d) (b Q : ℕ) (w : Polynomial ℤ)
    (hwdeg : w.natDegree ≤ d) (gaps : Erdos260.GapWord)
    (threshold : ℕ) : Polynomial ℝ :=
  (G.selectedExteriorGraph b Q w hwdeg gaps threshold).poly.map
    (algebraMap ℚ ℝ)

@[simp]
theorem PolynomialGraph.selectedExteriorRealPoly_coeff {d : ℕ}
    (G : PolynomialGraph d) (b Q : ℕ) (w : Polynomial ℤ)
    (hwdeg : w.natDegree ≤ d) (gaps : Erdos260.GapWord)
    (threshold n : ℕ) :
    (G.selectedExteriorRealPoly b Q w hwdeg gaps threshold).coeff n =
      (((G.selectedExteriorGraph b Q w hwdeg gaps threshold).poly.coeff n : ℚ) : ℝ) := by
  simp [PolynomialGraph.selectedExteriorRealPoly]

/-- Positive strict-exterior span prevents loss of the ambient top degree. -/
theorem PolynomialGraph.selectedExteriorRealPoly_degree_eq {d b Q : ℕ}
    (hb : 2 ≤ b) (hQ : 0 < Q)
    (G : PolynomialGraph d) (w : Polynomial ℤ)
    (hw : 0 < w.coeff d) (hwdeg : w.natDegree ≤ d)
    {gaps : Erdos260.GapWord}
    (hpositive : Erdos260.GapWord.Positive gaps)
    {threshold : ℕ}
    (hspan : threshold < exteriorSpanAlong b gaps
      ((G.normalizedTopState Q w : ℚ) : ℝ)) :
    (G.selectedExteriorRealPoly b Q w hwdeg gaps threshold).natDegree = d := by
  let selected := selectedExteriorWord b gaps
    ((G.normalizedTopState Q w : ℚ) : ℝ) threshold
  have hlower := G.selectedExteriorTopCoeff_abs_lower hb hQ w hw hwdeg
    hpositive hspan
  have hscalePos : (0 : ℝ) < (G.topStateScale Q w : ℝ) := by
    exact_mod_cast G.topStateScale_pos hQ w hw
  have hbminus : (0 : ℝ) < b - 1 := by
    have hbReal : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hp : (0 : ℝ) < (b : ℝ) ^ Erdos260.GapWord.span selected := by
    positivity
  have hleft :
      0 < (b : ℝ) ^ Erdos260.GapWord.span selected /
        ((G.topStateScale Q w : ℝ) * (b - 1 : ℝ)) := by
    exact div_pos hp (mul_pos hscalePos hbminus)
  have hcoeffAbs :
      0 < abs ((((G.selectedExteriorGraph b Q w hwdeg gaps threshold).poly.coeff d : ℚ) : ℝ)) :=
    hleft.trans_le (by simpa only [selected] using hlower)
  have hcoeff :
      (G.selectedExteriorRealPoly b Q w hwdeg gaps threshold).coeff d ≠ 0 := by
    intro hzero
    have hzero' :
        (((G.selectedExteriorGraph b Q w hwdeg gaps threshold).poly.coeff d : ℚ) : ℝ) = 0 := by
      simpa only [G.selectedExteriorRealPoly_coeff] using hzero
    rw [hzero'] at hcoeffAbs
    simp at hcoeffAbs
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact (Polynomial.natDegree_map_le.trans
      (G.selectedExteriorGraph b Q w hwdeg gaps threshold).degree_le)
  · exact hcoeff

/-- Exact exterior terminal-coordinate census obtained by combining the
degree certificate with the discrete polynomial sublevel theorem. -/
theorem PolynomialGraph.selectedExteriorSublevel_card_bound {d b Q : ℕ}
    (hd : 0 < d) (hb : 2 ≤ b) (hQ : 0 < Q)
    (G : PolynomialGraph d) (w : Polynomial ℤ)
    (hw : 0 < w.coeff d) (hwdeg : w.natDegree ≤ d)
    {gaps : Erdos260.GapWord}
    (hpositive : Erdos260.GapWord.Positive gaps)
    {threshold : ℕ}
    (hspan : threshold < exteriorSpanAlong b gaps
      ((G.normalizedTopState Q w : ℚ) : ℝ))
    (L U : ℤ) {Y : ℝ} (hY : 0 ≤ Y) :
    ((integerSublevelSet
      (G.selectedExteriorRealPoly b Q w hwdeg gaps threshold)
      L U Y).card : ℝ) ≤
      d + 2 * d *
        (Y /
          |(G.selectedExteriorRealPoly b Q w hwdeg gaps threshold).leadingCoeff|) ^
            ((d : ℝ)⁻¹) := by
  let f := G.selectedExteriorRealPoly b Q w hwdeg gaps threshold
  have hdeg : f.natDegree = d :=
    G.selectedExteriorRealPoly_degree_eq hb hQ w hw hwdeg hpositive hspan
  have hf : f ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg
    simp at hdeg
    omega
  exact integerSublevelSet_card_bound hd f hf hdeg L U hY

/-- Natural-coordinate version of a polynomial sublevel set. -/
def naturalSublevelSet (f : Polynomial ℝ) (L U : ℕ) (Y : ℝ) : Finset ℕ :=
  (Finset.Icc L U).filter fun n => |f.eval (n : ℝ)| ≤ Y

@[simp]
theorem mem_naturalSublevelSet_iff {f : Polynomial ℝ} {L U n : ℕ}
    {Y : ℝ} :
    n ∈ naturalSublevelSet f L U Y ↔
      L ≤ n ∧ n ≤ U ∧ |f.eval (n : ℝ)| ≤ Y := by
  simp [naturalSublevelSet, and_assoc]

theorem naturalSublevelSet_card_le_integer (f : Polynomial ℝ)
    (L U : ℕ) (Y : ℝ) :
    (naturalSublevelSet f L U Y).card ≤
      (integerSublevelSet f (L : ℤ) (U : ℤ) Y).card := by
  let encode : (↥(naturalSublevelSet f L U Y)) →
      ↥(integerSublevelSet f (L : ℤ) (U : ℤ) Y) := fun n =>
    ⟨(n.1 : ℤ), by
      rw [mem_integerSublevelSet_iff]
      have hn := mem_naturalSublevelSet_iff.mp n.2
      exact ⟨by exact_mod_cast hn.1, by exact_mod_cast hn.2.1,
        by simpa using hn.2.2⟩⟩
  have hencode : Function.Injective encode := by
    intro left right heq
    apply Subtype.ext
    have hval : (left.1 : ℤ) = (right.1 : ℤ) :=
      congrArg Subtype.val heq
    exact Int.ofNat_inj.mp hval
  exact Finset.card_le_card_of_injective hencode

/-- A source in the exterior census.  The record and selected word determine
the displacement from the window start to the terminal coordinate. -/
structure ExteriorSource (Record Word : Type*)
    (displacement : Record → Word → ℕ) where
  windowStart : ℕ
  record : Record
  word : Word
  terminal : ℕ
  terminal_eq : terminal = windowStart + displacement record word

/-! ## Actual exterior codes from canonical windows -/

/-- Occurrences in one locked prefix fibre whose genuine post-prefix
continuation contains the requested amount of strict exterior span. -/
noncomputable def exteriorEligibleIndices (D : CarrySeries)
    (N W m bound : ℕ) (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ) : Finset ℕ :=
  (realizedPrefixIndices D N W m bound pfx).filter fun k =>
    threshold < exteriorSpanAlong D.base
      (postLockingWord D.positiveEnumeration k m bound)
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))

abbrev PreExteriorRecord (b cap m : ℕ) (μ : ℝ) :=
  ↥(boundedPreExteriorCandidates b μ cap m)

abbrev SelectedExteriorRecord (cap threshold m : ℕ) :=
  ↥(boundedPositiveGapWords (threshold + cap) m)

def actualExteriorDisplacement {b cap m threshold : ℕ} {μ : ℝ}
    (record : PreExteriorRecord b cap m μ)
    (word : SelectedExteriorRecord cap threshold m) : ℕ :=
  Erdos260.GapWord.span record.1 + Erdos260.GapWord.span word.1

/-- The source object attached to one genuine eligible occurrence. -/
noncomputable def actualExteriorSource (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(exteriorEligibleIndices D N W m bound pfx G threshold)) :
    let μ : ℝ :=
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
    ExteriorSource (PreExteriorRecord D.base cap m μ)
      (SelectedExteriorRecord cap threshold m)
      (actualExteriorDisplacement (b := D.base) (cap := cap)
        (m := m) (threshold := threshold) (μ := μ)) := by
  let μ : ℝ :=
    (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
  let post := postLockingWord D.positiveEnumeration k.1 m bound
  have hkRealized : k.1 ∈ realizedPrefixIndices D N W m bound pfx :=
    (Finset.mem_filter.mp k.2).1
  have hspan : threshold < exteriorSpanAlong D.base post μ := by
    simpa only [post, μ] using (Finset.mem_filter.mp k.2).2
  have hpositive : Erdos260.GapWord.Positive post :=
    postLockingWord_positive D.positiveEnumeration k.1 m bound
  have hcap : ∀ g ∈ post, g ≤ cap :=
    postLockingWord_gap_le D hgeom (Finset.mem_filter.mp hkRealized).1
  have hpostLength : post.length ≤ m :=
    postLockingWord_length_le D.positiveEnumeration k.1 m bound
  let recordWord := preExteriorWord D.base post μ
  have hrecordLength : recordWord.length ≤ m := by
    have hpref : recordWord.IsPrefix post := by
      exact ⟨strictExteriorSuffix D.base post μ,
        preExteriorWord_append_strictExteriorSuffix D.base post μ⟩
    exact hpref.length_le.trans hpostLength
  have hrecord : recordWord ∈
      boundedPreExteriorCandidates D.base μ cap m := by
    exact preExteriorWord_mem_boundedCandidates hpositive hcap μ hrecordLength
  let selectedWord := selectedExteriorWord D.base post μ threshold
  have hselectedBounds := selectedExteriorWord_bounds D.base_ge_two
    hpositive hcap μ hspan
  have hselected : selectedWord ∈
      boundedPositiveGapWords (threshold + cap) m := by
    rw [mem_boundedPositiveGapWords_iff]
    exact ⟨hselectedBounds.2.1, hselectedBounds.2.2.2.1,
      hselectedBounds.2.2.2.2.trans hpostLength⟩
  let record : PreExteriorRecord D.base cap m μ := ⟨recordWord, hrecord⟩
  let word : SelectedExteriorRecord cap threshold m :=
    ⟨selectedWord, hselected⟩
  exact
    { windowStart := D.positiveEnumeration.a k.1 +
        Erdos260.GapWord.span pfx
      record := record
      word := word
      terminal := D.positiveEnumeration.a k.1 +
        Erdos260.GapWord.span pfx +
        Erdos260.GapWord.span recordWord +
        Erdos260.GapWord.span selectedWord
      terminal_eq := by
        simp [actualExteriorDisplacement, record, word]
        omega }

@[simp]
theorem actualExteriorSource_record_val (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(exteriorEligibleIndices D N W m bound pfx G threshold)) :
    let post := postLockingWord D.positiveEnumeration k.1 m bound
    let μ : ℝ :=
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
    (actualExteriorSource D (bound := bound) hgeom pfx G threshold k).record.1 =
      preExteriorWord D.base post μ := by
  rfl

@[simp]
theorem actualExteriorSource_word_val (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(exteriorEligibleIndices D N W m bound pfx G threshold)) :
    let post := postLockingWord D.positiveEnumeration k.1 m bound
    let μ : ℝ :=
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
    (actualExteriorSource D (bound := bound) hgeom pfx G threshold k).word.1 =
      selectedExteriorWord D.base post μ threshold := by
  rfl

@[simp]
theorem actualExteriorSource_terminal (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(exteriorEligibleIndices D N W m bound pfx G threshold)) :
    let post := postLockingWord D.positiveEnumeration k.1 m bound
    let μ : ℝ :=
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
    let pre := preExteriorWord D.base post μ
    let selected := selectedExteriorWord D.base post μ threshold
    (actualExteriorSource D (bound := bound) hgeom pfx G threshold k).terminal =
      D.positiveEnumeration.a k.1 + Erdos260.GapWord.span pfx +
        Erdos260.GapWord.span pre + Erdos260.GapWord.span selected := by
  rfl

/-- Polynomial graph determined solely by an exterior record and selected
word. -/
def exteriorCodeGraph (D : CarrySeries)
    (G : PolynomialGraph D.weight.natDegree)
    {cap m threshold : ℕ} {μ : ℝ}
    (record : PreExteriorRecord D.base cap m μ)
    (word : SelectedExteriorRecord cap threshold m) :
    PolynomialGraph D.weight.natDegree :=
  G.transformWord D.base D.denominator D.weight le_rfl
    (record.1 ++ word.1)

def exteriorCodeRealPoly (D : CarrySeries)
    (G : PolynomialGraph D.weight.natDegree)
    {cap m threshold : ℕ} {μ : ℝ}
    (record : PreExteriorRecord D.base cap m μ)
    (word : SelectedExteriorRecord cap threshold m) : Polynomial ℝ :=
  (exteriorCodeGraph D G record word).poly.map (algebraMap ℚ ℝ)

theorem exteriorCodeRealPoly_degree_le (D : CarrySeries)
    (G : PolynomialGraph D.weight.natDegree)
    {cap m threshold : ℕ} {μ : ℝ}
    (record : PreExteriorRecord D.base cap m μ)
    (word : SelectedExteriorRecord cap threshold m) :
    (exteriorCodeRealPoly D G record word).natDegree ≤
      D.weight.natDegree :=
  Polynomial.natDegree_map_le.trans
    (exteriorCodeGraph D G record word).degree_le

theorem actualExteriorSource_codeGraph (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(exteriorEligibleIndices D N W m bound pfx G threshold)) :
    exteriorCodeGraph D G
        (actualExteriorSource D (bound := bound) hgeom pfx G threshold k).record
        (actualExteriorSource D (bound := bound) hgeom pfx G threshold k).word =
      G.selectedExteriorGraph D.base D.denominator D.weight le_rfl
        (postLockingWord D.positiveEnumeration k.1 m bound) threshold := by
  unfold exteriorCodeGraph PolynomialGraph.selectedExteriorGraph
    PolynomialGraph.exteriorEntryGraph
  rw [actualExteriorSource_record_val, actualExteriorSource_word_val,
    G.transformWord_append]

/-- The actual exterior source map is injective.  Equality of source objects
recovers the support anchor, hence the enumeration index. -/
theorem actualExteriorSource_injective (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ) :
    Function.Injective
      (actualExteriorSource D (bound := bound) hgeom pfx G threshold) := by
  intro left right heq
  have hstart := congrArg
    (fun source => source.windowStart) heq
  apply Subtype.ext
  apply D.positiveEnumeration.strictMono.injective
  exact Nat.add_right_cancel hstart

noncomputable def actualExteriorSources (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ) := by
  classical
  exact (Finset.univ : Finset
      (↥(exteriorEligibleIndices D N W m bound pfx G threshold))).image
    (actualExteriorSource D (bound := bound) hgeom pfx G threshold)

theorem actualExteriorSources_card (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ) :
    (actualExteriorSources D (bound := bound) hgeom pfx G threshold).card =
      (exteriorEligibleIndices D N W m bound pfx G threshold).card := by
  classical
  unfold actualExteriorSources
  rw [Finset.card_image_of_injective]
  · simp
  · exact actualExteriorSource_injective D hgeom pfx G threshold

/-- A genuine eligible exterior code evaluates to the genuine carry at its
terminal coordinate. -/
theorem actualExterior_terminal_eval (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree)
    (hfit : ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
      G.poly.eval (x + Erdos260.GapWord.span pfx : ℚ) =
        (D.carry (x + Erdos260.GapWord.span pfx) : ℚ))
    (threshold : ℕ)
    (k : ↥(exteriorEligibleIndices D N W m bound pfx G threshold)) :
    let post := postLockingWord D.positiveEnumeration k.1 m bound
    let μ : ℝ :=
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
    let pre := preExteriorWord D.base post μ
    let selected := selectedExteriorWord D.base post μ threshold
    let terminal := D.positiveEnumeration.a k.1 +
      Erdos260.GapWord.span pfx + Erdos260.GapWord.span pre +
      Erdos260.GapWord.span selected
    (G.selectedExteriorGraph D.base D.denominator D.weight le_rfl
      post threshold).poly.eval (terminal : ℚ) =
        (D.carry terminal : ℚ) := by
  let post := postLockingWord D.positiveEnumeration k.1 m bound
  let μ : ℝ :=
    (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
  let pre := preExteriorWord D.base post μ
  let selected := selectedExteriorWord D.base post μ threshold
  let terminal := D.positiveEnumeration.a k.1 +
    Erdos260.GapWord.span pfx + Erdos260.GapWord.span pre +
    Erdos260.GapWord.span selected
  have hkRealized : k.1 ∈ realizedPrefixIndices D N W m bound pfx :=
    (Finset.mem_filter.mp k.2).1
  have hanchor : D.positiveEnumeration.a k.1 ∈
      realizedPrefixAnchors D N W m bound pfx := by
    rw [realizedPrefixAnchors, Finset.mem_image]
    exact ⟨k.1, hkRealized, rfl⟩
  have hstart := hfit (D.positiveEnumeration.a k.1) hanchor
  have hpfxEq : lockingPrefix D.positiveEnumeration k.1 m bound = pfx :=
    (Finset.mem_filter.mp hkRealized).2
  have hstart' :
      G.poly.eval
          ((D.positiveEnumeration.a k.1 +
            Erdos260.GapWord.span
              (lockingPrefix D.positiveEnumeration k.1 m bound) : ℕ) : ℚ) =
        (D.carry (D.positiveEnumeration.a k.1 +
          Erdos260.GapWord.span
            (lockingPrefix D.positiveEnumeration k.1 m bound)) : ℚ) := by
    simpa only [hpfxEq, Nat.cast_add] using hstart
  have hword := postLockingWord_gapWordAt D k.1 m bound
  have hcontinued := G.selectedExteriorGraph_eval_carry
    (threshold := threshold) D hstart' hword
  rw [hpfxEq] at hcontinued
  simpa only [post, μ, pre, selected, terminal, Nat.add_assoc] using hcontinued

/-- The actual selected terminal remains inside the local geometry envelope. -/
theorem actualExterior_terminal_bounds (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(exteriorEligibleIndices D N W m bound pfx G threshold)) :
    let post := postLockingWord D.positiveEnumeration k.1 m bound
    let μ : ℝ :=
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
    let pre := preExteriorWord D.base post μ
    let selected := selectedExteriorWord D.base post μ threshold
    let terminal := D.positiveEnumeration.a k.1 +
      Erdos260.GapWord.span pfx + Erdos260.GapWord.span pre +
      Erdos260.GapWord.span selected
    N < terminal ∧ terminal ≤ N + W + m * cap := by
  let post := postLockingWord D.positiveEnumeration k.1 m bound
  let μ : ℝ :=
    (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
  let pre := preExteriorWord D.base post μ
  let selected := selectedExteriorWord D.base post μ threshold
  let terminal := D.positiveEnumeration.a k.1 +
    Erdos260.GapWord.span pfx + Erdos260.GapWord.span pre +
    Erdos260.GapWord.span selected
  have hkRealized : k.1 ∈ realizedPrefixIndices D N W m bound pfx :=
    (Finset.mem_filter.mp k.2).1
  have hkLong : k.1 ∈
      longWindowIndices D.positiveEnumeration N W m bound :=
    (Finset.mem_filter.mp hkRealized).1
  have hkWindow : k.1 ∈ windowIndices D.positiveEnumeration N W :=
    (Finset.mem_filter.mp hkLong).1
  have hkIco := Finset.mem_Ico.mp hkWindow
  have hanchorLower : N < D.positiveEnumeration.a k.1 :=
    (Erdos260.firstIndexAbove_spec D.positiveEnumeration N).trans_le
      (D.positiveEnumeration.strictMono.monotone hkIco.1)
  have hanchorUpper : D.positiveEnumeration.a k.1 ≤ N + W :=
    Erdos260.firstIndexAbove_minimal D.positiveEnumeration (N + W) k.1 hkIco.2
  have hpref : (pre ++ selected).IsPrefix post := by
    simpa only [pre, selected, post, μ] using
      preExteriorWord_append_selectedExteriorWord_isPrefix
        D.base post μ threshold
  obtain ⟨tail, htail⟩ := hpref
  have hselectedSpan :
      Erdos260.GapWord.span pre + Erdos260.GapWord.span selected ≤
        Erdos260.GapWord.span post := by
    have hsum := congrArg List.sum htail
    simp only [List.sum_append] at hsum
    change pre.sum + selected.sum ≤ post.sum
    omega
  have hsplit := lockingPrefix_span_add_postSpan
    D.positiveEnumeration k.1 m bound
  have hpfxEq : lockingPrefix D.positiveEnumeration k.1 m bound = pfx :=
    (Finset.mem_filter.mp hkRealized).2
  rw [hpfxEq] at hsplit
  have hsplit' :
      Erdos260.GapWord.span pfx + Erdos260.GapWord.span post =
        forwardSpan D.positiveEnumeration k.1 m := by
    simpa only [post] using hsplit
  have hforward := WindowGeometry.forwardSpan_le D.positiveEnumeration
    hgeom hkWindow
  have htotal :
      Erdos260.GapWord.span pfx + Erdos260.GapWord.span pre +
          Erdos260.GapWord.span selected ≤ m * cap := by
    omega
  dsimp only [pre, selected, post, μ] at htotal
  dsimp only [terminal]
  omega

theorem actualExterior_terminal_carry_bound (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(exteriorEligibleIndices D N W m bound pfx G threshold)) :
    let post := postLockingWord D.positiveEnumeration k.1 m bound
    let μ : ℝ :=
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
    let pre := preExteriorWord D.base post μ
    let selected := selectedExteriorWord D.base post μ threshold
    let terminal := D.positiveEnumeration.a k.1 +
      Erdos260.GapWord.span pfx + Erdos260.GapWord.span pre +
      Erdos260.GapWord.span selected
    (D.carry terminal).natAbs ≤
      D.heightNatConstant * (N + W + m * cap + 1) ^
        D.weight.natDegree := by
  let post := postLockingWord D.positiveEnumeration k.1 m bound
  let μ : ℝ :=
    (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
  let pre := preExteriorWord D.base post μ
  let selected := selectedExteriorWord D.base post μ threshold
  let terminal := D.positiveEnumeration.a k.1 +
    Erdos260.GapWord.span pfx + Erdos260.GapWord.span pre +
    Erdos260.GapWord.span selected
  have hbounds := actualExterior_terminal_bounds D hgeom pfx G threshold k
  have hbounds' : N < terminal ∧ terminal ≤ N + W + m * cap := by
    simpa only [post, μ, pre, selected, terminal] using hbounds
  have hcarry := D.carry_natAbs_le (hpositiveFrom.trans hbounds'.1.le)
  calc
    (D.carry terminal).natAbs ≤
        D.heightNatConstant * (terminal + 1) ^ D.weight.natDegree := hcarry
    _ ≤ D.heightNatConstant * (N + W + m * cap + 1) ^
          D.weight.natDegree := by
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_left (Nat.add_le_add_right hbounds'.2 1) _

/-- Real evaluation form of `actualExterior_terminal_eval`. -/
theorem actualExteriorSource_real_eval (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree)
    (hfit : ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
      G.poly.eval (x + Erdos260.GapWord.span pfx : ℚ) =
        (D.carry (x + Erdos260.GapWord.span pfx) : ℚ))
    (threshold : ℕ)
    (k : ↥(exteriorEligibleIndices D N W m bound pfx G threshold)) :
    let source := actualExteriorSource D (bound := bound)
      hgeom pfx G threshold k
    (exteriorCodeRealPoly D G source.record source.word).eval
        (source.terminal : ℝ) = (D.carry source.terminal : ℝ) := by
  let source := actualExteriorSource D (bound := bound)
    hgeom pfx G threshold k
  have hq := actualExterior_terminal_eval D pfx G hfit threshold k
  have hgraph := actualExteriorSource_codeGraph D hgeom pfx G threshold k
  have hterminal := actualExteriorSource_terminal D hgeom pfx G threshold k
  dsimp only at hq hterminal
  rw [← hgraph, ← hterminal] at hq
  dsimp only [source]
  have hmap :
      (exteriorCodeRealPoly D G
        (actualExteriorSource D (bound := bound) hgeom pfx G threshold k).record
        (actualExteriorSource D (bound := bound) hgeom pfx G threshold k).word).eval
          ((actualExteriorSource D (bound := bound)
            hgeom pfx G threshold k).terminal : ℝ) =
        (((exteriorCodeGraph D G
          (actualExteriorSource D (bound := bound) hgeom pfx G threshold k).record
          (actualExteriorSource D (bound := bound) hgeom pfx G threshold k).word).poly.eval
            ((actualExteriorSource D (bound := bound)
              hgeom pfx G threshold k).terminal : ℚ) : ℚ) : ℝ) := by
    unfold exteriorCodeRealPoly
    simpa using Polynomial.eval_map_apply
      (p := (exteriorCodeGraph D G
        (actualExteriorSource D (bound := bound) hgeom pfx G threshold k).record
        (actualExteriorSource D (bound := bound) hgeom pfx G threshold k).word).poly)
      (f := algebraMap ℚ ℝ)
      ((actualExteriorSource D (bound := bound)
        hgeom pfx G threshold k).terminal : ℚ)
  rw [hmap]
  exact_mod_cast hq

/-! ## Exterior source recovery -/

/-- The actual exterior encoding: record, selected word, terminal coordinate. -/
def exteriorSourceMap {Record Word : Type*}
    {displacement : Record → Word → ℕ}
    (source : ExteriorSource Record Word displacement) :
    Record × Word × ℕ :=
  (source.record, source.word, source.terminal)

/-- Coordinate recovery is proved from the deterministic displacement; it is
not stored as an injectivity field. -/
theorem exteriorSourceMap_injective {Record Word : Type*}
    {displacement : Record → Word → ℕ} :
    Function.Injective
      (exteriorSourceMap (displacement := displacement)) := by
  intro left right hmap
  have hrecord : left.record = right.record := (Prod.mk.inj hmap).1
  have htail : (left.word, left.terminal) =
      (right.word, right.terminal) := (Prod.mk.inj hmap).2
  have hword : left.word = right.word := (Prod.mk.inj htail).1
  have hterminal : left.terminal = right.terminal := (Prod.mk.inj htail).2
  have hstart : left.windowStart = right.windowStart := by
    rw [left.terminal_eq, right.terminal_eq, hrecord, hword] at hterminal
    omega
  cases left
  cases right
  simp_all

/-- Finite exterior census obtained from the proved source encoding. -/
theorem exteriorSource_card_le {Record Word : Type*}
    [Fintype Record] [Fintype Word]
    {displacement : Record → Word → ℕ}
    (sources : Finset (ExteriorSource Record Word displacement))
    (terminals : Finset ℕ)
    (hterminal : ∀ s ∈ sources, s.terminal ∈ terminals) :
    sources.card ≤ Fintype.card Record * Fintype.card Word * terminals.card := by
  classical
  let target := Record × Word × terminals
  let encode : (↥sources) → target := fun s =>
    (s.1.record, s.1.word, ⟨s.1.terminal, hterminal s.1 s.2⟩)
  have hencode : Function.Injective encode := by
    intro left right heq
    apply Subtype.ext
    apply exteriorSourceMap_injective
    exact Prod.ext (Prod.mk.inj heq).1
      (Prod.ext (Prod.mk.inj (Prod.mk.inj heq).2).1
        (congrArg Subtype.val (Prod.mk.inj (Prod.mk.inj heq).2).2))
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa [target, Fintype.card_prod, mul_assoc] using hcard

/-- Fibrewise exterior census.  Unlike `exteriorSource_card_le`, the terminal
set may depend on the pre-exterior record and on the selected exterior word;
this is the form needed to insert the polynomial sublevel bound. -/
theorem exteriorSource_card_le_fibres {Record Word : Type*}
    [Fintype Record] [Fintype Word]
    {displacement : Record → Word → ℕ}
    (sources : Finset (ExteriorSource Record Word displacement))
    (terminals : Record → Word → Finset ℕ)
    (hterminal : ∀ s ∈ sources,
      s.terminal ∈ terminals s.record s.word) :
    sources.card ≤
      ∑ record : Record, ∑ word : Word, (terminals record word).card := by
  classical
  let recordFiber (record : Record) :=
    sources.filter fun s => s.record = record
  let wordFiber (record : Record) (word : Word) :=
    (recordFiber record).filter fun s => s.word = word
  have hrecords :
      sources.card = ∑ record : Record, (recordFiber record).card := by
    exact Finset.card_eq_sum_card_fiberwise fun _s _hs => Finset.mem_univ _
  have hwords (record : Record) :
      (recordFiber record).card =
        ∑ word : Word, (wordFiber record word).card := by
    exact Finset.card_eq_sum_card_fiberwise fun _s _hs => Finset.mem_univ _
  have hfibre (record : Record) (word : Word) :
      (wordFiber record word).card ≤ (terminals record word).card := by
    let encode : (↥(wordFiber record word)) → ↥(terminals record word) :=
      fun s => ⟨s.1.terminal, by
        have hsWord := Finset.mem_filter.mp s.2
        have hsRecord := Finset.mem_filter.mp hsWord.1
        have ht := hterminal s.1 hsRecord.1
        simpa only [hsRecord.2, hsWord.2] using ht⟩
    have hencode : Function.Injective encode := by
      intro left right heq
      have hleft := Finset.mem_filter.mp left.2
      have hright := Finset.mem_filter.mp right.2
      have hleftRecord := Finset.mem_filter.mp hleft.1
      have hrightRecord := Finset.mem_filter.mp hright.1
      have hrecord : left.1.record = right.1.record :=
        hleftRecord.2.trans hrightRecord.2.symm
      have hword : left.1.word = right.1.word :=
        hleft.2.trans hright.2.symm
      have hterminalEq : left.1.terminal = right.1.terminal :=
        congrArg Subtype.val heq
      apply Subtype.ext
      apply exteriorSourceMap_injective
      exact Prod.ext hrecord (Prod.ext hword hterminalEq)
    exact Finset.card_le_card_of_injective hencode
  rw [hrecords]
  apply Finset.sum_le_sum
  intro record _hrecord
  rw [hwords]
  exact Finset.sum_le_sum fun word _hword => hfibre record word

/-- Mass form of the fibrewise exterior census. -/
theorem exteriorSourceMass_le_fibres {Record Word : Type*}
    [Fintype Record] [Fintype Word]
    {displacement : Record → Word → ℕ}
    (sources : Finset (ExteriorSource Record Word displacement))
    (terminals : Record → Word → Finset ℕ)
    (hterminal : ∀ s ∈ sources,
      s.terminal ∈ terminals s.record s.word)
    (span : ExteriorSource Record Word displacement → ℕ)
    {Vmax : ℕ} (hspan : ∀ s ∈ sources, span s ≤ Vmax) :
    ∑ s ∈ sources, span s ≤
      (∑ record : Record, ∑ word : Word,
        (terminals record word).card) * Vmax := by
  calc
    ∑ s ∈ sources, span s ≤ ∑ _s ∈ sources, Vmax := by
      gcongr with s hs
      exact hspan s hs
    _ = sources.card * Vmax := by simp
    _ ≤ (∑ record : Record, ∑ word : Word,
          (terminals record word).card) * Vmax := by
      gcongr
      exact exteriorSource_card_le_fibres sources terminals hterminal

/-- Explicit mass form of the exterior contribution.  Subsequent asymptotic
specialization supplies the manuscript's `o(mW)` bound. -/
theorem prop_exterior_census {Record Word : Type*}
    [Fintype Record] [Fintype Word]
    {displacement : Record → Word → ℕ}
    (sources : Finset (ExteriorSource Record Word displacement))
    (terminals : Finset ℕ) (span : ExteriorSource Record Word displacement → ℕ)
    (hterminal : ∀ s ∈ sources, s.terminal ∈ terminals)
    {Vmax : ℕ} (hspan : ∀ s ∈ sources, span s ≤ Vmax) :
    ∑ s ∈ sources, span s ≤
      Fintype.card Record * Fintype.card Word * terminals.card * Vmax := by
  calc
    ∑ s ∈ sources, span s ≤ ∑ _s ∈ sources, Vmax := by
      gcongr with s hs
      exact hspan s hs
    _ = sources.card * Vmax := by simp
    _ ≤ (Fintype.card Record * Fintype.card Word * terminals.card) * Vmax := by
      gcongr
      exact exteriorSource_card_le sources terminals hterminal
    _ = _ := rfl

/-! ## Fibre partition for actual exterior occurrences -/

noncomputable def actualExteriorTerminalFibre (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (record : PreExteriorRecord D.base cap m
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)))
    (word : SelectedExteriorRecord cap threshold m) : Finset ℕ := by
  classical
  let sources := actualExteriorSources D (bound := bound)
    hgeom pfx G threshold
  exact (sources.filter fun source =>
    source.record = record ∧ source.word = word).image fun source =>
      source.terminal

theorem actualExteriorSource_terminal_mem_fibre (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (source : ExteriorSource
      (PreExteriorRecord D.base cap m
        (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)))
      (SelectedExteriorRecord cap threshold m)
      (actualExteriorDisplacement (b := D.base) (cap := cap)
        (m := m) (threshold := threshold)
        (μ := (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)))))
    (hsource : source ∈ actualExteriorSources D (bound := bound)
      hgeom pfx G threshold) :
    source.terminal ∈ actualExteriorTerminalFibre D (bound := bound)
      hgeom pfx G threshold source.record source.word := by
  classical
  rw [actualExteriorTerminalFibre, Finset.mem_image]
  exact ⟨source, Finset.mem_filter.mpr ⟨hsource, rfl, rfl⟩, rfl⟩

/-- Every terminal in an actual record/word fibre lies in the corresponding
polynomial sublevel set. -/
theorem actualExteriorTerminalFibre_subset_sublevel (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree)
    (hfit : ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
      G.poly.eval (x + Erdos260.GapWord.span pfx : ℚ) =
        (D.carry (x + Erdos260.GapWord.span pfx) : ℚ))
    (threshold : ℕ)
    (record : PreExteriorRecord D.base cap m
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)))
    (word : SelectedExteriorRecord cap threshold m) :
    actualExteriorTerminalFibre D (bound := bound)
        hgeom pfx G threshold record word ⊆
      naturalSublevelSet (exteriorCodeRealPoly D G record word)
        N (N + W + m * cap)
        (D.heightNatConstant * (N + W + m * cap + 1) ^
          D.weight.natDegree : ℕ) := by
  classical
  intro terminal hterminal
  rw [actualExteriorTerminalFibre, Finset.mem_image] at hterminal
  obtain ⟨source, hsourceFilter, rfl⟩ := hterminal
  have hsourceData := Finset.mem_filter.mp hsourceFilter
  have hsource := hsourceData.1
  have hrecord : source.record = record := hsourceData.2.1
  have hword : source.word = word := hsourceData.2.2
  rw [actualExteriorSources, Finset.mem_image] at hsource
  obtain ⟨k, _hk, hsourceEq⟩ := hsource
  have hbounds := actualExterior_terminal_bounds D hgeom pfx G threshold k
  have hcarry := actualExterior_terminal_carry_bound D hgeom hpositiveFrom
    pfx G threshold k
  have heval := actualExteriorSource_real_eval D hgeom pfx G hfit threshold k
  dsimp only at hbounds hcarry heval
  have hterminalEq :
      (actualExteriorSource D (bound := bound)
        hgeom pfx G threshold k).terminal = source.terminal :=
    congrArg (fun s => s.terminal) hsourceEq
  have hrecordEq :
      (actualExteriorSource D (bound := bound)
        hgeom pfx G threshold k).record = record :=
    (congrArg (fun s => s.record) hsourceEq).trans hrecord
  have hwordEq :
      (actualExteriorSource D (bound := bound)
        hgeom pfx G threshold k).word = word :=
    (congrArg (fun s => s.word) hsourceEq).trans hword
  have hterminalProjection :=
    actualExteriorSource_terminal D (bound := bound)
      hgeom pfx G threshold k
  dsimp only at hterminalProjection
  have hexplicitTerminal := hterminalProjection.symm.trans hterminalEq
  rw [hexplicitTerminal] at hbounds hcarry
  rw [hterminalEq] at heval
  rw [hrecordEq, hwordEq] at heval
  rw [mem_naturalSublevelSet_iff]
  refine ⟨hbounds.1.le, hbounds.2, ?_⟩
  rw [heval]
  have hcast :
      ((D.carry source.terminal).natAbs : ℝ) ≤
        (D.heightNatConstant * (N + W + m * cap + 1) ^
          D.weight.natDegree : ℕ) := by
    exact_mod_cast hcarry
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast

/-- A nonempty actual record/word fibre is represented by a genuine selected
strict-exterior graph, so its real code polynomial retains the full weight
degree.  Nonemptiness is used only to recover one genuine occurrence; no
realizability field is stored in the code. -/
theorem exteriorCodeRealPoly_degree_eq_of_fibre_nonempty (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree)
    (threshold : ℕ)
    (record : PreExteriorRecord D.base cap m
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)))
    (word : SelectedExteriorRecord cap threshold m)
    (hne : (actualExteriorTerminalFibre D (bound := bound)
      hgeom pfx G threshold record word).Nonempty) :
    (exteriorCodeRealPoly D G record word).natDegree =
      D.weight.natDegree := by
  classical
  obtain ⟨terminal, hterminal⟩ := hne
  rw [actualExteriorTerminalFibre, Finset.mem_image] at hterminal
  obtain ⟨source, hsourceFilter, _hterminalEq⟩ := hterminal
  have hsourceData := Finset.mem_filter.mp hsourceFilter
  have hsource := hsourceData.1
  have hrecord : source.record = record := hsourceData.2.1
  have hword : source.word = word := hsourceData.2.2
  rw [actualExteriorSources, Finset.mem_image] at hsource
  obtain ⟨k, _hk, hsourceEq⟩ := hsource
  let post := postLockingWord D.positiveEnumeration k.1 m bound
  have hspan : threshold < exteriorSpanAlong D.base post
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)) := by
    simpa only [post] using (Finset.mem_filter.mp k.2).2
  have hpositive : Erdos260.GapWord.Positive post :=
    postLockingWord_positive D.positiveEnumeration k.1 m bound
  have hdeg := G.selectedExteriorRealPoly_degree_eq D.base_ge_two
    D.denominator_pos D.weight hw le_rfl hpositive hspan
  have hrecordEq :
      (actualExteriorSource D (bound := bound)
        hgeom pfx G threshold k).record = record :=
    (congrArg (fun s => s.record) hsourceEq).trans hrecord
  have hwordEq :
      (actualExteriorSource D (bound := bound)
        hgeom pfx G threshold k).word = word :=
    (congrArg (fun s => s.word) hsourceEq).trans hword
  have hcode := actualExteriorSource_codeGraph D hgeom pfx G threshold k
  rw [hrecordEq, hwordEq] at hcode
  unfold exteriorCodeRealPoly
  rw [hcode]
  simpa only [PolynomialGraph.selectedExteriorRealPoly, post] using hdeg

/-- The leading coefficient of every realized exterior code grows at least
exponentially in the requested strict-exterior span. -/
theorem exteriorCodeLeadingCoeff_abs_lower_of_fibre_nonempty
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree)
    (threshold : ℕ)
    (record : PreExteriorRecord D.base cap m
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)))
    (word : SelectedExteriorRecord cap threshold m)
    (hne : (actualExteriorTerminalFibre D (bound := bound)
      hgeom pfx G threshold record word).Nonempty) :
    (D.base : ℝ) ^ threshold /
        ((G.topStateScale D.denominator D.weight : ℝ) *
          (D.base - 1 : ℝ)) ≤
      |(exteriorCodeRealPoly D G record word).leadingCoeff| := by
  classical
  have hdegree := exteriorCodeRealPoly_degree_eq_of_fibre_nonempty D hw
    hgeom pfx G threshold record word hne
  obtain ⟨terminal, hterminal⟩ := hne
  rw [actualExteriorTerminalFibre, Finset.mem_image] at hterminal
  obtain ⟨source, hsourceFilter, _hterminalEq⟩ := hterminal
  have hsourceData := Finset.mem_filter.mp hsourceFilter
  have hsource := hsourceData.1
  have hrecord : source.record = record := hsourceData.2.1
  have hword : source.word = word := hsourceData.2.2
  rw [actualExteriorSources, Finset.mem_image] at hsource
  obtain ⟨k, _hk, hsourceEq⟩ := hsource
  let post := postLockingWord D.positiveEnumeration k.1 m bound
  let selected := selectedExteriorWord D.base post
    (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)) threshold
  have hspan : threshold < exteriorSpanAlong D.base post
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)) := by
    simpa only [post] using (Finset.mem_filter.mp k.2).2
  have hpositive : Erdos260.GapWord.Positive post :=
    postLockingWord_positive D.positiveEnumeration k.1 m bound
  have hlower := G.selectedExteriorTopCoeff_abs_lower D.base_ge_two
    D.denominator_pos D.weight hw le_rfl hpositive hspan
  have hrecordEq :
      (actualExteriorSource D (bound := bound)
        hgeom pfx G threshold k).record = record :=
    (congrArg (fun s => s.record) hsourceEq).trans hrecord
  have hwordEq :
      (actualExteriorSource D (bound := bound)
        hgeom pfx G threshold k).word = word :=
    (congrArg (fun s => s.word) hsourceEq).trans hword
  have hcode := actualExteriorSource_codeGraph D hgeom pfx G threshold k
  rw [hrecordEq, hwordEq] at hcode
  have hcoeff :
      (exteriorCodeRealPoly D G record word).leadingCoeff =
        (((G.selectedExteriorGraph D.base D.denominator D.weight le_rfl
          post threshold).poly.coeff D.weight.natDegree : ℚ) : ℝ) := by
    rw [← Polynomial.coeff_natDegree, hdegree]
    simp only [exteriorCodeRealPoly, Polynomial.coeff_map]
    rw [hcode]
    rfl
  have hpow : (D.base : ℝ) ^ threshold ≤
      (D.base : ℝ) ^ Erdos260.GapWord.span selected := by
    apply pow_le_pow_right₀
    · exact_mod_cast (le_trans (by omega : 1 ≤ 2) D.base_ge_two)
    · have hselectedBounds := selectedExteriorWord_bounds D.base_ge_two
        hpositive (fun g hg => by
          exact postLockingWord_gap_le D hgeom
            (Finset.mem_filter.mp
              ((Finset.mem_filter.mp k.2).1)).1 g hg)
        (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)) hspan
      simpa only [selected] using hselectedBounds.2.2.1.le
  have hdenPos : (0 : ℝ) <
      (G.topStateScale D.denominator D.weight : ℝ) *
        (D.base - 1 : ℝ) := by
    apply mul_pos
    · exact_mod_cast G.topStateScale_pos D.denominator_pos D.weight hw
    · have hb : (2 : ℝ) ≤ D.base := by exact_mod_cast D.base_ge_two
      linarith
  calc
    (D.base : ℝ) ^ threshold /
        ((G.topStateScale D.denominator D.weight : ℝ) *
          (D.base - 1 : ℝ)) ≤
      (D.base : ℝ) ^ Erdos260.GapWord.span selected /
        ((G.topStateScale D.denominator D.weight : ℝ) *
          (D.base - 1 : ℝ)) := by
            exact (div_le_div_iff_of_pos_right hdenPos).2 hpow
    _ ≤ |(exteriorCodeRealPoly D G record word).leadingCoeff| := by
      rw [hcoeff]
      simpa only [selected, post] using hlower

/-- Quantitative sublevel estimate for one genuine exterior code fibre. -/
theorem actualExteriorTerminalFibre_card_bound (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree)
    (hfit : ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
      G.poly.eval (x + Erdos260.GapWord.span pfx : ℚ) =
        (D.carry (x + Erdos260.GapWord.span pfx) : ℚ))
    (threshold : ℕ)
    (record : PreExteriorRecord D.base cap m
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)))
    (word : SelectedExteriorRecord cap threshold m) :
    (((actualExteriorTerminalFibre D (bound := bound)
      hgeom pfx G threshold record word).card : ℕ) : ℝ) ≤
      D.weight.natDegree + 2 * D.weight.natDegree *
        ((D.heightNatConstant * (N + W + m * cap + 1) ^
            D.weight.natDegree : ℕ) /
          |(exteriorCodeRealPoly D G record word).leadingCoeff|) ^
            (((D.weight.natDegree : ℝ))⁻¹) := by
  classical
  let fibre := actualExteriorTerminalFibre D (bound := bound)
    hgeom pfx G threshold record word
  let f := exteriorCodeRealPoly D G record word
  let Y : ℝ :=
    (D.heightNatConstant * (N + W + m * cap + 1) ^
      D.weight.natDegree : ℕ)
  by_cases hne : fibre.Nonempty
  · have hdegree : f.natDegree = D.weight.natDegree := by
      exact exteriorCodeRealPoly_degree_eq_of_fibre_nonempty D hw
        hgeom pfx G threshold record word hne
    have hf : f ≠ 0 := by
      intro hzero
      rw [hzero] at hdegree
      simp at hdegree
      omega
    have hsubset : fibre ⊆ naturalSublevelSet f N
        (N + W + m * cap) Y := by
      simpa only [fibre, f, Y] using
        actualExteriorTerminalFibre_subset_sublevel D hgeom hpositiveFrom
          pfx G hfit threshold record word
    have hnatCard : fibre.card ≤
        (naturalSublevelSet f N (N + W + m * cap) Y).card :=
      Finset.card_le_card hsubset
    have hintCard := naturalSublevelSet_card_le_integer f N
      (N + W + m * cap) Y
    have hsublevel := integerSublevelSet_card_bound hd f hf hdegree
      (N : ℤ) ((N + W + m * cap : ℕ) : ℤ) (by positivity : 0 ≤ Y)
    have hcards : (fibre.card : ℝ) ≤
        ((integerSublevelSet f (N : ℤ)
          ((N + W + m * cap : ℕ) : ℤ) Y).card : ℝ) := by
      exact_mod_cast hnatCard.trans hintCard
    exact hcards.trans (by simpa only [f, Y] using hsublevel)
  · have hempty : fibre = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hnonneg :
        (0 : ℝ) ≤ D.weight.natDegree + 2 * D.weight.natDegree *
          (Y / |f.leadingCoeff|) ^ (((D.weight.natDegree : ℝ))⁻¹) := by
      positivity
    simpa only [fibre, f, Y, hempty, Finset.card_empty, Nat.cast_zero]
      using hnonneg

/-- Uniform version of the exterior fibre estimate, with the code-dependent
leading coefficient replaced by the exponential strict-exterior gain. -/
theorem actualExteriorTerminalFibre_card_bound_uniform (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree)
    (hfit : ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
      G.poly.eval (x + Erdos260.GapWord.span pfx : ℚ) =
        (D.carry (x + Erdos260.GapWord.span pfx) : ℚ))
    (threshold : ℕ)
    (record : PreExteriorRecord D.base cap m
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)))
    (word : SelectedExteriorRecord cap threshold m) :
    (((actualExteriorTerminalFibre D (bound := bound)
      hgeom pfx G threshold record word).card : ℕ) : ℝ) ≤
      D.weight.natDegree + 2 * D.weight.natDegree *
        (((D.heightNatConstant * (N + W + m * cap + 1) ^
              D.weight.natDegree : ℕ) : ℝ) *
            ((G.topStateScale D.denominator D.weight : ℕ) : ℝ) *
            (D.base - 1 : ℝ) /
          (D.base : ℝ) ^ threshold) ^
            (((D.weight.natDegree : ℝ))⁻¹) := by
  classical
  let fibre := actualExteriorTerminalFibre D (bound := bound)
    hgeom pfx G threshold record word
  let f := exteriorCodeRealPoly D G record word
  let Y : ℝ :=
    (D.heightNatConstant * (N + W + m * cap + 1) ^
      D.weight.natDegree : ℕ)
  let B : ℝ :=
    (G.topStateScale D.denominator D.weight : ℕ) *
      (D.base - 1 : ℝ)
  have hraw := actualExteriorTerminalFibre_card_bound D hd hw hgeom
    hpositiveFrom pfx G hfit threshold record word
  by_cases hne : fibre.Nonempty
  · have hlower : (D.base : ℝ) ^ threshold / B ≤
        |f.leadingCoeff| := by
      simpa only [fibre, f, B, Nat.cast_mul] using
        exteriorCodeLeadingCoeff_abs_lower_of_fibre_nonempty D hw hgeom
          pfx G threshold record word hne
    have hbaseCastPos : (0 : ℝ) < D.base := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) D.base_ge_two)
    have hbasePos : (0 : ℝ) < (D.base : ℝ) ^ threshold :=
      pow_pos hbaseCastPos _
    have hBPos : (0 : ℝ) < B := by
      dsimp only [B]
      apply mul_pos
      · exact_mod_cast G.topStateScale_pos D.denominator_pos D.weight hw
      · have hb : (2 : ℝ) ≤ D.base := by exact_mod_cast D.base_ge_two
        linarith
    have hlowerPos : (0 : ℝ) < (D.base : ℝ) ^ threshold / B :=
      div_pos hbasePos hBPos
    have hlcPos : (0 : ℝ) < |f.leadingCoeff| := hlowerPos.trans_le hlower
    have hY : 0 ≤ Y := by positivity
    have hratio : Y / |f.leadingCoeff| ≤
        Y * B / (D.base : ℝ) ^ threshold := by
      calc
        Y / |f.leadingCoeff| ≤ Y /
            ((D.base : ℝ) ^ threshold / B) := by
          apply (div_le_div_iff₀ hlcPos hlowerPos).2
          exact mul_le_mul_of_nonneg_left hlower hY
        _ = Y * B / (D.base : ℝ) ^ threshold := by
          field_simp [hbasePos.ne', hBPos.ne']
    have hrpow :
        (Y / |f.leadingCoeff|) ^ (((D.weight.natDegree : ℝ))⁻¹) ≤
          (Y * B / (D.base : ℝ) ^ threshold) ^
            (((D.weight.natDegree : ℝ))⁻¹) :=
      Real.rpow_le_rpow (div_nonneg hY hlcPos.le) hratio (by positivity)
    calc
      (fibre.card : ℝ) ≤ D.weight.natDegree +
          2 * D.weight.natDegree *
            (Y / |f.leadingCoeff|) ^
              (((D.weight.natDegree : ℝ))⁻¹) := by
        simpa only [fibre, f, Y] using hraw
      _ ≤ D.weight.natDegree + 2 * D.weight.natDegree *
          (Y * B / (D.base : ℝ) ^ threshold) ^
            (((D.weight.natDegree : ℝ))⁻¹) := by gcongr
      _ = D.weight.natDegree + 2 * D.weight.natDegree *
          (((D.heightNatConstant * (N + W + m * cap + 1) ^
                D.weight.natDegree : ℕ) : ℝ) *
              ((G.topStateScale D.denominator D.weight : ℕ) : ℝ) *
              (D.base - 1 : ℝ) /
            (D.base : ℝ) ^ threshold) ^
              (((D.weight.natDegree : ℝ))⁻¹) := by
        dsimp only [Y, B]
        push_cast
        congr 3
        ring
  · have hempty : fibre = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hbaseCastPos : (0 : ℝ) < D.base := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) D.base_ge_two)
    have hBNonneg : 0 ≤ B := by
      dsimp only [B]
      apply mul_nonneg (Nat.cast_nonneg _)
      have hb : (2 : ℝ) ≤ D.base := by exact_mod_cast D.base_ge_two
      linarith
    have hratioNonneg :
        0 ≤ Y * B / (D.base : ℝ) ^ threshold :=
      div_nonneg (mul_nonneg (by positivity) hBNonneg)
        (pow_pos hbaseCastPos _).le
    have hnonneg :
        (0 : ℝ) ≤ D.weight.natDegree + 2 * D.weight.natDegree *
          (Y * B / (D.base : ℝ) ^ threshold) ^
            (((D.weight.natDegree : ℝ))⁻¹) := by
      exact add_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
          (Real.rpow_nonneg hratioNonneg _))
    simpa only [fibre, f, Y, B, hempty, Finset.card_empty, Nat.cast_zero,
      Nat.cast_mul, mul_assoc] using hnonneg

/-- The genuine exterior occurrences in one locked prefix fibre are bounded by
the sum of their record/word terminal fibres.  This is the exact source-map
stage preceding the polynomial sublevel estimate. -/
theorem actualExteriorEligible_card_le_fibres (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ) :
    (exteriorEligibleIndices D N W m bound pfx G threshold).card ≤
      ∑ record : PreExteriorRecord D.base cap m
          (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)),
        ∑ word : SelectedExteriorRecord cap threshold m,
          (actualExteriorTerminalFibre D (bound := bound)
            hgeom pfx G threshold record word).card := by
  classical
  let sources := actualExteriorSources D (bound := bound)
    hgeom pfx G threshold
  have hcard := exteriorSource_card_le_fibres sources
    (actualExteriorTerminalFibre D (bound := bound)
      hgeom pfx G threshold)
    (actualExteriorSource_terminal_mem_fibre D (bound := bound)
      hgeom pfx G threshold)
  rw [actualExteriorSources_card D hgeom pfx G threshold] at hcard
  exact hcard

/-- Full exterior census for one locked prefix and graph: the only multiplicity
left after the injective source map is the finite record census, the finite
selected-word census, and the uniform polynomial sublevel fibre bound. -/
theorem actualExteriorEligible_card_bound (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree)
    (hfit : ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
      G.poly.eval (x + Erdos260.GapWord.span pfx : ℚ) =
        (D.carry (x + Erdos260.GapWord.span pfx) : ℚ))
    (threshold : ℕ) :
    ((exteriorEligibleIndices D N W m bound pfx G threshold).card : ℝ) ≤
      (Fintype.card (PreExteriorRecord D.base cap m
        (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))) : ℝ) *
      (Fintype.card (SelectedExteriorRecord cap threshold m) : ℝ) *
      (D.weight.natDegree + 2 * D.weight.natDegree *
        (((D.heightNatConstant * (N + W + m * cap + 1) ^
              D.weight.natDegree : ℕ) : ℝ) *
            ((G.topStateScale D.denominator D.weight : ℕ) : ℝ) *
            (D.base - 1 : ℝ) /
          (D.base : ℝ) ^ threshold) ^
            (((D.weight.natDegree : ℝ))⁻¹)) := by
  classical
  let C : ℝ := D.weight.natDegree + 2 * D.weight.natDegree *
    (((D.heightNatConstant * (N + W + m * cap + 1) ^
          D.weight.natDegree : ℕ) : ℝ) *
        ((G.topStateScale D.denominator D.weight : ℕ) : ℝ) *
        (D.base - 1 : ℝ) /
      (D.base : ℝ) ^ threshold) ^
        (((D.weight.natDegree : ℝ))⁻¹)
  have hcensus := actualExteriorEligible_card_le_fibres D (bound := bound)
    hgeom pfx G threshold
  have hcensusReal :
      ((exteriorEligibleIndices D N W m bound pfx G threshold).card : ℝ) ≤
        ∑ record : PreExteriorRecord D.base cap m
            (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)),
          ∑ word : SelectedExteriorRecord cap threshold m,
            ((actualExteriorTerminalFibre D (bound := bound)
              hgeom pfx G threshold record word).card : ℝ) := by
    exact_mod_cast hcensus
  calc
    ((exteriorEligibleIndices D N W m bound pfx G threshold).card : ℝ) ≤
        ∑ record : PreExteriorRecord D.base cap m
            (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)),
          ∑ word : SelectedExteriorRecord cap threshold m,
            ((actualExteriorTerminalFibre D (bound := bound)
              hgeom pfx G threshold record word).card : ℝ) := hcensusReal
    _ ≤ ∑ _record : PreExteriorRecord D.base cap m
            (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)),
          ∑ _word : SelectedExteriorRecord cap threshold m, C := by
      apply Finset.sum_le_sum
      intro record _hrecord
      apply Finset.sum_le_sum
      intro word _hword
      simpa only [C] using actualExteriorTerminalFibre_card_bound_uniform
        D hd hw hgeom hpositiveFrom pfx G hfit threshold record word
    _ = (Fintype.card (PreExteriorRecord D.base cap m
            (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))) : ℝ) *
          (Fintype.card (SelectedExteriorRecord cap threshold m) : ℝ) * C := by
      simp [mul_assoc]
    _ = (Fintype.card (PreExteriorRecord D.base cap m
            (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))) : ℝ) *
          (Fintype.card (SelectedExteriorRecord cap threshold m) : ℝ) *
          (D.weight.natDegree + 2 * D.weight.natDegree *
            (((D.heightNatConstant * (N + W + m * cap + 1) ^
                  D.weight.natDegree : ℕ) : ℝ) *
                ((G.topStateScale D.denominator D.weight : ℕ) : ℝ) *
                (D.base - 1 : ℝ) /
              (D.base : ℝ) ^ threshold) ^
                (((D.weight.natDegree : ℝ))⁻¹)) := by rfl

/-- Manuscript proposition `prop:exterior` in its finite uniform form for one
locked prefix fibre.  Summing this bound over the realized nonrare prefixes
is purely finite; the completion module performs the parameter choice that
turns its right-hand side into a uniform little-`o` term. -/
theorem prop_exterior (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hpositiveFrom : D.positiveFrom ≤ N)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree)
    (hfit : ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
      G.poly.eval (x + Erdos260.GapWord.span pfx : ℚ) =
        (D.carry (x + Erdos260.GapWord.span pfx) : ℚ))
    (threshold : ℕ) :
    ((∑ k ∈ exteriorEligibleIndices D N W m bound pfx G threshold,
        forwardSpan D.positiveEnumeration k m : ℕ) : ℝ) ≤
      (Fintype.card (PreExteriorRecord D.base cap m
        (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))) : ℝ) *
      (Fintype.card (SelectedExteriorRecord cap threshold m) : ℝ) *
      (D.weight.natDegree + 2 * D.weight.natDegree *
        (((D.heightNatConstant * (N + W + m * cap + 1) ^
              D.weight.natDegree : ℕ) : ℝ) *
            ((G.topStateScale D.denominator D.weight : ℕ) : ℝ) *
            (D.base - 1 : ℝ) /
          (D.base : ℝ) ^ threshold) ^
            (((D.weight.natDegree : ℝ))⁻¹)) *
      (m * cap : ℕ) := by
  have hmassNat :
      (∑ k ∈ exteriorEligibleIndices D N W m bound pfx G threshold,
          forwardSpan D.positiveEnumeration k m : ℕ) ≤
        (exteriorEligibleIndices D N W m bound pfx G threshold).card *
          (m * cap) := by
    calc
      (∑ k ∈ exteriorEligibleIndices D N W m bound pfx G threshold,
          forwardSpan D.positiveEnumeration k m : ℕ) ≤
          ∑ _k ∈ exteriorEligibleIndices D N W m bound pfx G threshold,
            m * cap := by
        gcongr with k hk
        have hkRealized : k ∈ realizedPrefixIndices D N W m bound pfx :=
          (Finset.mem_filter.mp hk).1
        have hkWindow : k ∈ windowIndices D.positiveEnumeration N W :=
          (Finset.mem_filter.mp (Finset.mem_filter.mp hkRealized).1).1
        exact WindowGeometry.forwardSpan_le D.positiveEnumeration hgeom hkWindow
      _ = (exteriorEligibleIndices D N W m bound pfx G threshold).card *
          (m * cap) := by simp
  have hmassReal :
      ((∑ k ∈ exteriorEligibleIndices D N W m bound pfx G threshold,
          forwardSpan D.positiveEnumeration k m : ℕ) : ℝ) ≤
        ((exteriorEligibleIndices D N W m bound pfx G threshold).card : ℝ) *
          (m * cap : ℕ) := by
    exact_mod_cast hmassNat
  have hcard := actualExteriorEligible_card_bound D hd hw hgeom
    hpositiveFrom pfx G hfit threshold
  exact hmassReal.trans (mul_le_mul_of_nonneg_right hcard (by positivity))

end Erdos260.PolynomialWindow
