import Erdos260.PolynomialWindow.Locking

/-!
# Interior algebraic spikes

This file first closes the two fidelity-critical pieces used by the interior
count: high-frequency graph coalescence and the source-map injection.  The
later block census is built on these proved interfaces, not encoded as fields.
-/

noncomputable section

open scoped BigOperators

namespace Erdos260.PolynomialWindow

/-! ## Interior numerator dynamics -/

/-- Multiplication by a natural number coprime to the reduced denominator
does not change that denominator. -/
theorem natCast_mul_den_of_coprime (x : ℚ) (n : ℕ)
    (h : Nat.Coprime n x.den) :
    ((n : ℚ) * x).den = x.den := by
  rw [Rat.mul_den]
  have hprod : Nat.Coprime (n * x.num.natAbs) x.den :=
    h.mul_left x.reduced
  rw [show (((n : ℚ).num * x.num).natAbs) = n * x.num.natAbs by
    rw [Rat.num_natCast, Int.natAbs_mul, Int.natAbs_natCast]]
  simp [hprod.gcd_eq_one]

/-- A top-state step preserves a denominator coprime to the base. -/
theorem topStateStep_den_eq (b g : ℕ) (μ : ℚ)
    (hcop : Nat.Coprime b μ.den) :
    ((b : ℚ) ^ g * μ - 1).den = μ.den := by
  rw [Rat.sub_ofNat_den]
  simpa only [Nat.cast_pow] using
    natCast_mul_den_of_coprime μ (b ^ g) (hcop.pow_left g)

/-- Coprime denominators are invariant along a whole gap word. -/
theorem topStateAlongRat_den_eq (b : ℕ) (gaps : Erdos260.GapWord) (μ : ℚ)
    (hcop : Nat.Coprime b μ.den) :
    (topStateAlongRat b gaps μ).den = μ.den := by
  induction gaps generalizing μ with
  | nil => rfl
  | cons g gs ih =>
      let ν : ℚ := (b : ℚ) ^ g * μ - 1
      have hstep : ν.den = μ.den := topStateStep_den_eq b g μ hcop
      have hcopν : Nat.Coprime b ν.den := by simpa only [hstep] using hcop
      exact (ih ν hcopν).trans hstep

/-- Iterating the top-state map is multiplication by the full base power
followed by subtraction of one integer correction. -/
theorem exists_topStateAlongRat_eq_mul_sub_int (b : ℕ)
    (gaps : Erdos260.GapWord) (μ : ℚ) :
    ∃ z : ℤ,
      topStateAlongRat b gaps μ =
        μ * (b : ℚ) ^ Erdos260.GapWord.span gaps - z := by
  induction gaps generalizing μ with
  | nil =>
      refine ⟨0, ?_⟩
      simp [Erdos260.GapWord.span]
  | cons g gs ih =>
      obtain ⟨z, hz⟩ := ih ((b : ℚ) ^ g * μ - 1)
      refine ⟨(b : ℤ) ^ Erdos260.GapWord.span gs + z, ?_⟩
      simp only [topStateAlongRat_cons, hz, Erdos260.GapWord.span,
        List.sum_cons, pow_add]
      push_cast
      ring

/-- Once a word spans a denominator-absorption exponent, its terminal state
has denominator dividing the fixed coprime part. -/
theorem topStateAlongRat_den_dvd_of_absorbed_prefix
    (b e Q : ℕ) (μ : ℚ) (gaps : Erdos260.GapWord)
    (hspan : e ≤ Erdos260.GapWord.span gaps)
    (hden : (μ * (b : ℚ) ^ e).den ∣ Q) :
    (topStateAlongRat b gaps μ).den ∣ Q := by
  let t := Erdos260.GapWord.span gaps - e
  have hexponent : e + t = Erdos260.GapWord.span gaps := by
    dsimp [t]
    omega
  have hfactor :
      μ * (b : ℚ) ^ Erdos260.GapWord.span gaps =
        (μ * (b : ℚ) ^ e) * (b : ℚ) ^ t := by
    rw [← hexponent, pow_add]
    ring
  have hmul :
      ((μ * (b : ℚ) ^ e) * (b : ℚ) ^ t).den ∣
        (μ * (b : ℚ) ^ e).den := by
    have hraw := Rat.mul_den_dvd
      (μ * (b : ℚ) ^ e) ((b : ℚ) ^ t)
    simpa using hraw
  obtain ⟨z, hz⟩ := exists_topStateAlongRat_eq_mul_sub_int b gaps μ
  rw [hz, Rat.sub_intCast_den, hfactor]
  exact hmul.trans hden

/-- Coprimality with the base follows automatically from the fixed
coprime denominator bound after absorption. -/
theorem topStateAlongRat_den_coprime_of_absorbed_prefix
    (b e Q : ℕ) (μ : ℚ) (gaps : Erdos260.GapWord)
    (hspan : e ≤ Erdos260.GapWord.span gaps)
    (hQcop : Nat.Coprime Q b)
    (hden : (μ * (b : ℚ) ^ e).den ∣ Q) :
    Nat.Coprime b (topStateAlongRat b gaps μ).den := by
  apply Nat.Coprime.symm
  exact Nat.Coprime.of_dvd_left
    (topStateAlongRat_den_dvd_of_absorbed_prefix b e Q μ gaps hspan hden)
    hQcop

/-- Rational state after the first `i` gaps. -/
def rationalTopStateAt (b : ℕ) (gaps : Erdos260.GapWord) (μ : ℚ)
    (i : ℕ) : ℚ :=
  topStateAlongRat b (gaps.take i) μ

theorem rationalTopStateAt_succ (b : ℕ) (gaps : Erdos260.GapWord) (μ : ℚ)
    (i : ℕ) (hi : i < gaps.length) :
    rationalTopStateAt b gaps μ (i + 1) =
      (b : ℚ) ^ gaps[i] * rationalTopStateAt b gaps μ i - 1 := by
  have htake : gaps.take (i + 1) = gaps.take i ++ [gaps[i]] := by
    simpa only [List.concat_eq_append] using (List.take_concat_get hi).symm
  unfold rationalTopStateAt
  rw [htake, topStateAlongRat_append]
  rfl

/-- Canonical prefix removed to absorb all denominator factors shared with
the base. -/
def denominatorAbsorptionPrefix (gaps : Erdos260.GapWord) (e : ℕ) :
    Erdos260.GapWord :=
  gaps.firstPrefixAtLeast e

/-- Once a positive prefix has already reached the absorption span, extending
the ambient word cannot change the canonical absorption prefix. -/
theorem firstPrefixAtLeast_eq_of_prefix
    {short long : Erdos260.GapWord} {e : ℕ}
    (hprefix : short.IsPrefix long) (hne : short ≠ [])
    (hcross : e ≤ Erdos260.GapWord.span short) :
    short.firstPrefixAtLeast e = long.firstPrefixAtLeast e := by
  obtain ⟨tail, rfl⟩ := hprefix
  induction short generalizing e with
  | nil => exact (hne rfl).elim
  | cons g gs ih =>
      by_cases heg : e ≤ g
      · simp [Erdos260.GapWord.firstPrefixAtLeast, heg]
      · have htailCross : e - g ≤ Erdos260.GapWord.span gs := by
          change e - g ≤ gs.sum
          change e ≤ g + gs.sum at hcross
          omega
        by_cases hgs : gs = []
        · subst gs
          simp only [Erdos260.GapWord.span, List.sum_nil] at htailCross
          omega
        · simp only [List.cons_append,
            Erdos260.GapWord.firstPrefixAtLeast, heg, if_false]
          exact congrArg (List.cons g) (ih hgs htailCross)

/-- Extending a positive-span word past a strict crossing cannot change its
first prefix that crosses the prescribed bound. -/
theorem firstPrefixAbove_eq_of_prefix
    {short long : Erdos260.GapWord} {bound : ℕ}
    (hprefix : short.IsPrefix long)
    (hcross : bound < Erdos260.GapWord.span short) :
    short.firstPrefixAbove bound = long.firstPrefixAbove bound := by
  obtain ⟨tail, rfl⟩ := hprefix
  induction short generalizing bound with
  | nil => simp [Erdos260.GapWord.span] at hcross
  | cons g gs ih =>
      by_cases hbg : bound < g
      · simp [Erdos260.GapWord.firstPrefixAbove, hbg]
      · have htailCross : bound - g < Erdos260.GapWord.span gs := by
          change bound - g < gs.sum
          change bound < g + gs.sum at hcross
          omega
        simp only [List.cons_append,
          Erdos260.GapWord.firstPrefixAbove, hbg, if_false]
        exact congrArg (List.cons g) (ih htailCross)

/-- Remaining word after denominator absorption. -/
def denominatorStabilizedSuffix (gaps : Erdos260.GapWord) (e : ℕ) :
    Erdos260.GapWord :=
  gaps.drop (denominatorAbsorptionPrefix gaps e).length

theorem denominatorAbsorptionPrefix_append_suffix
    (gaps : Erdos260.GapWord) (e : ℕ) :
    denominatorAbsorptionPrefix gaps e ++
      denominatorStabilizedSuffix gaps e = gaps := by
  exact Erdos260.GapWord.firstPrefixAtLeast_append_drop gaps e

theorem denominatorAbsorptionPrefix_span_ge
    (gaps : Erdos260.GapWord) (e : ℕ)
    (hspan : e ≤ Erdos260.GapWord.span gaps) :
    e ≤ Erdos260.GapWord.span (denominatorAbsorptionPrefix gaps e) := by
  exact Erdos260.GapWord.span_firstPrefixAtLeast_ge gaps e hspan

/-- Denominator absorption overshoots its exponent by at most one bounded
gap, including the harmless `e = 0` convention. -/
theorem denominatorAbsorptionPrefix_span_le_add
    (gaps : Erdos260.GapWord) (e cap : ℕ)
    (hcap : ∀ g ∈ gaps, g ≤ cap) :
    Erdos260.GapWord.span (denominatorAbsorptionPrefix gaps e) ≤ e + cap := by
  induction gaps generalizing e with
  | nil => simp [denominatorAbsorptionPrefix,
      Erdos260.GapWord.firstPrefixAtLeast, Erdos260.GapWord.span]
  | cons g gs ih =>
      have hgcap : g ≤ cap := hcap g (by simp)
      have htailcap : ∀ q ∈ gs, q ≤ cap := by
        intro q hq
        exact hcap q (by simp [hq])
      simp only [denominatorAbsorptionPrefix,
        Erdos260.GapWord.firstPrefixAtLeast]
      by_cases heg : e ≤ g
      · simp [heg, Erdos260.GapWord.span]
        omega
      · rw [if_neg heg]
        simp only [Erdos260.GapWord.span, List.sum_cons]
        have hrec := ih (e - g) htailcap
        simp only [denominatorAbsorptionPrefix] at hrec
        change (Erdos260.GapWord.firstPrefixAtLeast gs (e - g)).sum ≤
            e - g + cap at hrec
        omega

theorem denominatorStabilizedSuffix_positive
    {gaps : Erdos260.GapWord}
    (hpositive : Erdos260.GapWord.Positive gaps) (e : ℕ) :
    Erdos260.GapWord.Positive (denominatorStabilizedSuffix gaps e) := by
  intro g hg
  apply hpositive g
  exact List.mem_of_mem_drop hg

/-- Exact numerator update when the denominator is coprime to the base. -/
theorem topStateStep_num_eq (b g : ℕ) (μ : ℚ)
    (hcop : Nat.Coprime b μ.den) :
    ((b : ℚ) ^ g * μ - 1).num =
      (b : ℤ) ^ g * μ.num - μ.den := by
  let ν : ℚ := (b : ℚ) ^ g * μ - 1
  have hden : ν.den = μ.den := topStateStep_den_eq b g μ hcop
  have hrepr : ν =
      ((b : ℚ) ^ g * (μ.num : ℚ) - μ.den) / μ.den := by
    dsimp [ν]
    calc
      (b : ℚ) ^ g * μ - 1 =
          (b : ℚ) ^ g * ((μ.num : ℚ) / μ.den) - 1 := by
            rw [μ.num_div_den]
      _ = ((b : ℚ) ^ g * (μ.num : ℚ) - μ.den) / μ.den := by
        field_simp
  have hnumRat : (ν.num : ℚ) =
      (b : ℚ) ^ g * (μ.num : ℚ) - μ.den := by
    have hcanonical := ν.num_div_den
    rw [hden] at hcanonical
    conv_rhs at hcanonical => rw [hrepr]
    field_simp at hcanonical
    exact hcanonical
  simpa only [ν, Nat.cast_pow] using (show
    ν.num = (b : ℤ) ^ g * μ.num - μ.den by exact_mod_cast hnumRat)

/-- A finite interior orbit written with its common reduced denominator.  The
recurrence is stored because it is the defining dynamical relation; all bounds
and counting consequences below are proved from it. -/
structure InteriorNumeratorOrbit (b q : ℕ) where
  base_ge_two : 2 ≤ b
  denominator_pos : 0 < q
  gaps : Erdos260.GapWord
  gaps_positive : Erdos260.GapWord.Positive gaps
  numerators : Fin (gaps.length + 1) → ℕ
  numerator_pos : ∀ i, 0 < numerators i
  numerator_upper : ∀ i, (b - 1) * numerators i < q
  recurrence : ∀ i : Fin gaps.length,
    b ^ gaps.get i * numerators i.castSucc = q + numerators i.succ

namespace InteriorNumeratorOrbit

theorem rational_num_natAbs_pos {b : ℕ} (hb : 2 ≤ b) (x : ℚ)
    (hx : InteriorState b (x : ℝ)) :
    0 < x.num.natAbs := by
  have hbReal : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbminus : (0 : ℝ) < b - 1 := by linarith
  have hxReal : (0 : ℝ) < x := pos_of_mul_pos_right hx.1 hbminus.le
  have hxRat : (0 : ℚ) < x := by exact_mod_cast hxReal
  exact Int.natAbs_pos.mpr (Rat.num_pos.mpr hxRat).ne'

theorem rational_num_upper {b : ℕ} (hb : 2 ≤ b) (x : ℚ)
    (hx : InteriorState b (x : ℝ)) :
    (b - 1) * x.num.natAbs < x.den := by
  have hbOne : 1 ≤ b := by omega
  have hbReal : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbminus : (0 : ℝ) < b - 1 := by linarith
  have hxReal : (0 : ℝ) < x := pos_of_mul_pos_right hx.1 hbminus.le
  have hxRat : (0 : ℚ) < x := by exact_mod_cast hxReal
  have hnumPos : 0 < x.num := Rat.num_pos.mpr hxRat
  have hdenReal : (0 : ℝ) < x.den := by positivity
  have hdiv :
      ((b - 1 : ℝ) * (x.num : ℝ)) / (x.den : ℝ) < 1 := by
    calc
      ((b - 1 : ℝ) * (x.num : ℝ)) / (x.den : ℝ) =
          (b - 1 : ℝ) * (x : ℝ) := by
        rw [Rat.cast_def]
        ring
      _ < 1 := hx.2
  have hmul : (b - 1 : ℝ) * (x.num : ℝ) < (x.den : ℝ) :=
    (div_lt_one hdenReal).mp hdiv
  have hnumCast : ((x.num.natAbs : ℕ) : ℝ) = (x.num : ℝ) := by
    norm_num [abs_of_pos (show (0 : ℝ) < (x.num : ℝ) by exact_mod_cast hnumPos)]
  have hcast : (((b - 1) * x.num.natAbs : ℕ) : ℝ) < (x.den : ℝ) := by
    push_cast
    rw [Nat.cast_sub hbOne, Nat.cast_one, hnumCast]
    exact hmul
  exact_mod_cast hcast

/-- Package a genuine rational interior trajectory into the natural-number
recurrence used by the block argument.  No numerator sequence or recurrence
is supplied as an assumption. -/
def ofRational (b : ℕ) (hb : 2 ≤ b)
    (gaps : Erdos260.GapWord) (hpositive : Erdos260.GapWord.Positive gaps)
    (μ : ℚ) (hcop : Nat.Coprime b μ.den)
    (hinterior : ∀ i : Fin (gaps.length + 1),
      InteriorState b ((rationalTopStateAt b gaps μ i : ℚ) : ℝ)) :
    InteriorNumeratorOrbit b μ.den where
  base_ge_two := hb
  denominator_pos := μ.den_pos
  gaps := gaps
  gaps_positive := hpositive
  numerators := fun i => (rationalTopStateAt b gaps μ i).num.natAbs
  numerator_pos := fun i => rational_num_natAbs_pos hb _ (hinterior i)
  numerator_upper := fun i => by
    have h := rational_num_upper hb _ (hinterior i)
    have hden : (rationalTopStateAt b gaps μ i).den = μ.den :=
      topStateAlongRat_den_eq b (gaps.take i) μ hcop
    simpa only [hden] using h
  recurrence := fun i => by
    let x : ℚ := rationalTopStateAt b gaps μ i
    let y : ℚ := rationalTopStateAt b gaps μ (i + 1)
    have hstate : y = (b : ℚ) ^ gaps[i] * x - 1 :=
      rationalTopStateAt_succ b gaps μ i i.isLt
    have hxden : x.den = μ.den :=
      topStateAlongRat_den_eq b (gaps.take i) μ hcop
    have hcopx : Nat.Coprime b x.den := by simpa only [hxden] using hcop
    have hnum : y.num = (b : ℤ) ^ gaps[i] * x.num - μ.den := by
      rw [hstate, topStateStep_num_eq b gaps[i] x hcopx, hxden]
    have hxnum : 0 < x.num := by
      apply Rat.num_pos.mpr
      have hbReal : (2 : ℝ) ≤ b := by exact_mod_cast hb
      have hbminus : (0 : ℝ) < b - 1 := by linarith
      have hxReal : (0 : ℝ) < x :=
        pos_of_mul_pos_right (hinterior i.castSucc).1 hbminus.le
      exact_mod_cast hxReal
    have hynum : 0 < y.num := by
      apply Rat.num_pos.mpr
      have hbReal : (2 : ℝ) ≤ b := by exact_mod_cast hb
      have hbminus : (0 : ℝ) < b - 1 := by linarith
      have hyReal : (0 : ℝ) < y :=
        pos_of_mul_pos_right (hinterior i.succ).1 hbminus.le
      exact_mod_cast hyReal
    have hxcast : (x.num.natAbs : ℤ) = x.num := by
      rw [Int.natCast_natAbs, abs_of_pos hxnum]
    have hycast : (y.num.natAbs : ℤ) = y.num := by
      rw [Int.natCast_natAbs, abs_of_pos hynum]
    have hnum' : (b : ℤ) ^ gaps[i] * x.num = (μ.den : ℤ) + y.num := by
      omega
    rw [← hxcast, ← hycast] at hnum'
    exact_mod_cast hnum'

/-- The prefix state extracted from a transformed locked graph is the same
rational trajectory used by `ofRational`. -/
theorem rationalTopStateAt_eq_normalized_transformWord {d : ℕ}
    (G : PolynomialGraph d) (b Q : ℕ) (w : Polynomial ℤ)
    (hwdeg : w.natDegree ≤ d)
    (hA : (Q : ℚ) * (w.coeff d : ℚ) ≠ 0)
    (gaps : Erdos260.GapWord) (i : ℕ) :
    rationalTopStateAt b gaps (PolynomialGraph.normalizedTopState G Q w) i =
      PolynomialGraph.normalizedTopState
        (G.transformWord b Q w hwdeg (gaps.take i)) Q w := by
  unfold rationalTopStateAt
  exact (PolynomialGraph.normalizedTopState_transformWord G b Q w hwdeg hA
    (gaps.take i)).symm

/-- Build the numerator recurrence directly from a locked graph and its
genuine transformed prefix states. -/
def ofLockedGraph {d : ℕ} (G : PolynomialGraph d)
    (b Q : ℕ) (hb : 2 ≤ b)
    (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d)
    (hA : (Q : ℚ) * (w.coeff d : ℚ) ≠ 0)
    (gaps : Erdos260.GapWord) (hpositive : Erdos260.GapWord.Positive gaps)
    (hcop : Nat.Coprime b (PolynomialGraph.normalizedTopState G Q w).den)
    (hinterior : ∀ i : Fin (gaps.length + 1),
      InteriorState b
        ((PolynomialGraph.normalizedTopState
          (G.transformWord b Q w hwdeg (gaps.take i)) Q w : ℚ) : ℝ)) :
    InteriorNumeratorOrbit b (PolynomialGraph.normalizedTopState G Q w).den :=
  ofRational b hb gaps hpositive (PolynomialGraph.normalizedTopState G Q w) hcop (by
    intro i
    rw [rationalTopStateAt_eq_normalized_transformWord
      G b Q w hwdeg hA gaps i]
    exact hinterior i)

/-- Build the interior numerator orbit after automatically deleting the
shortest prefix that absorbs the base-primary denominator.  The only state
hypothesis concerns genuine prefixes of the original interior word. -/
def ofLockedGraphAfterAbsorption {d : ℕ} (G : PolynomialGraph d)
    (b Q e Qcop : ℕ) (hb : 2 ≤ b)
    (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d)
    (hA : (Q : ℚ) * (w.coeff d : ℚ) ≠ 0)
    (gaps : Erdos260.GapWord) (hpositive : Erdos260.GapWord.Positive gaps)
    (hspan : e ≤ Erdos260.GapWord.span gaps)
    (hQcop : Nat.Coprime Qcop b)
    (hden :
      (G.normalizedTopState Q w * (b : ℚ) ^ e).den ∣ Qcop)
    (hinterior : ∀ pfx : Erdos260.GapWord, pfx.IsPrefix gaps →
      InteriorState b
        (((G.transformWord b Q w hwdeg pfx).normalizedTopState Q w : ℚ) : ℝ)) :
    let pre := denominatorAbsorptionPrefix gaps e
    let G' := G.transformWord b Q w hwdeg pre
    InteriorNumeratorOrbit b (G'.normalizedTopState Q w).den := by
  let pre := denominatorAbsorptionPrefix gaps e
  let suffix := denominatorStabilizedSuffix gaps e
  let G' := G.transformWord b Q w hwdeg pre
  have hpreSpan : e ≤ Erdos260.GapWord.span pre :=
    denominatorAbsorptionPrefix_span_ge gaps e hspan
  have hstate :
      G'.normalizedTopState Q w =
        topStateAlongRat b pre (G.normalizedTopState Q w) := by
    dsimp only [G']
    exact G.normalizedTopState_transformWord b Q w hwdeg hA pre
  have hcopState : Nat.Coprime b (G'.normalizedTopState Q w).den := by
    rw [hstate]
    exact topStateAlongRat_den_coprime_of_absorbed_prefix
      b e Qcop (G.normalizedTopState Q w) pre hpreSpan hQcop hden
  have hsuffixPositive : Erdos260.GapWord.Positive suffix := by
    exact denominatorStabilizedSuffix_positive hpositive e
  apply ofLockedGraph G' b Q hb w hwdeg hA suffix hsuffixPositive hcopState
  intro i
  let pfx := pre ++ suffix.take i
  have hpfxPrefix : pfx.IsPrefix gaps := by
    have htake : (suffix.take i).IsPrefix suffix := List.take_prefix _ _
    obtain ⟨tail, htail⟩ := htake
    refine ⟨tail, ?_⟩
    calc
      (pre ++ suffix.take i) ++ tail =
          pre ++ (suffix.take i ++ tail) := by rw [List.append_assoc]
      _ = pre ++ suffix := by rw [htail]
      _ = gaps := denominatorAbsorptionPrefix_append_suffix gaps e
  have hi := hinterior pfx hpfxPrefix
  have hgraph :
      G'.transformWord b Q w hwdeg (suffix.take i) =
        G.transformWord b Q w hwdeg pfx := by
    dsimp only [G', pfx]
    rw [G.transformWord_append]
  simpa only [hgraph] using hi

/-- The dichotomy's interior mass yields a genuine all-vertices-interior
trajectory.  Once that trajectory is longer than the supplied absorption
loss, the complete coprime numerator orbit is constructed automatically. -/
def ofLongInteriorTrajectory {d : ℕ} (G : PolynomialGraph d)
    (b Q e Qcop cap : ℕ) (hb : 2 ≤ b)
    (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d)
    (hA : (Q : ℚ) * (w.coeff d : ℚ) ≠ 0)
    (gaps : Erdos260.GapWord) (hpositive : Erdos260.GapWord.Positive gaps)
    (hcap : ∀ g ∈ gaps, g ≤ cap)
    (hQcop : Nat.Coprime Qcop b)
    (hden :
      (G.normalizedTopState Q w * (b : ℚ) ^ e).den ∣ Qcop)
    (hlong : e + cap < interiorSpanAlong b gaps
      (((G.normalizedTopState Q w : ℚ) : ℝ))) :
    let trajectory := interiorTrajectory b gaps
      (((G.normalizedTopState Q w : ℚ) : ℝ))
    let pre := denominatorAbsorptionPrefix trajectory e
    let G' := G.transformWord b Q w hwdeg pre
    InteriorNumeratorOrbit b (G'.normalizedTopState Q w).den := by
  let μ : ℝ := ((G.normalizedTopState Q w : ℚ) : ℝ)
  let trajectory := interiorTrajectory b gaps μ
  have htrajLoss := interiorSpanAlong_le_trajectory_add_cap hb hpositive hcap μ
  have hlong' : e + cap < interiorSpanAlong b gaps μ := by
    simpa only [μ] using hlong
  change interiorSpanAlong b gaps μ ≤ trajectory.sum + cap at htrajLoss
  have htrajSpan : e < Erdos260.GapWord.span trajectory := by
    change e < trajectory.sum
    omega
  have htrajNe : trajectory ≠ [] := by
    intro hzero
    rw [hzero] at htrajSpan
    simp [Erdos260.GapWord.span] at htrajSpan
  have hstart : InteriorState b μ := interiorTrajectory_start htrajNe
  have htrajPositive : Erdos260.GapWord.Positive trajectory :=
    interiorTrajectory_positive hpositive μ
  apply ofLockedGraphAfterAbsorption G b Q e Qcop hb w hwdeg hA
    trajectory htrajPositive htrajSpan.le hQcop hden
  intro pfx hpfx
  have hlen : pfx.length ≤ trajectory.length := hpfx.length_le
  have hpfxTake : trajectory.take pfx.length = pfx := by
    obtain ⟨tail, htail⟩ := hpfx
    rw [← htail]
    simp
  have hreal := interiorTrajectory_state gaps hstart pfx.length hlen
  rw [hpfxTake] at hreal
  have hrat := G.normalizedTopState_transformWord b Q w hwdeg hA pfx
  have hcast := topStateAlongRat_cast b pfx (G.normalizedTopState Q w)
  rw [← hrat] at hcast
  rw [hcast]
  exact hreal

/-- A long interior branch automatically supplies a logarithmically bounded
absorption prefix, a fixed coprime denominator bound, and the resulting
numerator orbit. -/
theorem exists_stabilizedInteriorOrbit {d b Q cap : ℕ}
    (hb : 2 ≤ b) (G : PolynomialGraph d)
    (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d)
    (hA : (Q : ℚ) * (w.coeff d : ℚ) ≠ 0)
    {gaps : Erdos260.GapWord}
    (hpositive : Erdos260.GapWord.Positive gaps)
    (hcap : ∀ g ∈ gaps, g ≤ cap)
    (hlong : Nat.log 2 (G.normalizedTopState Q w).den + cap <
      interiorSpanAlong b gaps
        (((G.normalizedTopState Q w : ℚ) : ℝ))) :
    ∃ e Qcop : ℕ, 0 < Qcop ∧ Nat.Coprime Qcop b ∧
      e ≤ Nat.log 2 (G.normalizedTopState Q w).den ∧
      let trajectory := interiorTrajectory b gaps
        (((G.normalizedTopState Q w : ℚ) : ℝ))
      let pre := denominatorAbsorptionPrefix trajectory e
      let G' := G.transformWord b Q w hwdeg pre
      Nonempty (InteriorNumeratorOrbit b (G'.normalizedTopState Q w).den) := by
  obtain ⟨e, Qcop, hQcopPos, hQcop, he, hden⟩ :=
    exists_coprime_denominator_after_prefix_logBound
      (G.normalizedTopState Q w) hb
  refine ⟨e, Qcop, hQcopPos, hQcop, he, ?_⟩
  apply Nonempty.intro
  apply ofLongInteriorTrajectory G b Q e Qcop cap hb w hwdeg hA
    gaps hpositive hcap hQcop hden
  omega

/-- Canonical proof-bearing decomposition of the base-primary part of a
rational top-state denominator. -/
structure TopStateAbsorptionData (b : ℕ) (μ : ℚ) where
  exponent : ℕ
  coprimePart : ℕ
  coprimePart_pos : 0 < coprimePart
  coprime_base : Nat.Coprime coprimePart b
  coprimePart_le_den : coprimePart ≤ μ.den
  exponent_le_log : exponent ≤ Nat.log 2 μ.den
  residual_den_dvd : (μ * (b : ℚ) ^ exponent).den ∣ coprimePart

/-- The canonical denominator split is selected internally from the actual
state; callers do not supply an absorption exponent or coprime part. -/
noncomputable def chosenTopStateAbsorption (b : ℕ) (_hb : 2 ≤ b)
    (μ : ℚ) : TopStateAbsorptionData b μ := by
  classical
  let split := canonicalBaseDenominatorSplit b μ.den μ.den_pos
  have hcopDvd : split.coprime ∣ μ.den := by
    refine ⟨split.primary, ?_⟩
    simpa only [Nat.mul_comm] using split.factorization
  exact
    { exponent := split.exponent
      coprimePart := split.coprime
      coprimePart_pos := Nat.pos_of_dvd_of_pos hcopDvd μ.den_pos
      coprime_base := split.coprime_base
      coprimePart_le_den := Nat.le_of_dvd μ.den_pos hcopDvd
      exponent_le_log :=
        canonicalBaseDenominatorSplit_exponent_le_log b μ.den μ.den_pos
      residual_den_dvd := split.mul_pow_den_dvd_coprime μ rfl }

/-- Quantitative denominator band for the initial locked state.  A graph
certificate of size at most `T` gives the manuscript's `q \ll T`, with the
implicit constant made explicit as `Q * |w_d|`. -/
theorem normalizedTopState_den_le_of_graph_den_le {d Q T : ℕ}
    (G : PolynomialGraph d) (hG : G.denominator ≤ T)
    (hQ : 0 < Q) (w : Polynomial ℤ) (hw : 0 < w.coeff d) :
    (G.normalizedTopState Q w).den ≤
      T * Q * (w.coeff d).natAbs := by
  exact (G.normalizedTopState_den_le hQ w hw).trans (by
    gcongr)

/-- Formula label `eq:denrec`. -/
theorem eq_denrec {b q : ℕ} (O : InteriorNumeratorOrbit b q)
    (i : Fin O.gaps.length) :
    0 < O.numerators i.succ ∧
      (b - 1) * O.numerators i.succ < q ∧
      b ^ O.gaps.get i * O.numerators i.castSucc =
        q + O.numerators i.succ :=
  ⟨O.numerator_pos _, O.numerator_upper _, O.recurrence i⟩

theorem denominator_gt_one {b q : ℕ} (O : InteriorNumeratorOrbit b q) :
    1 < q := by
  let i : Fin (O.gaps.length + 1) := ⟨0, by omega⟩
  have hb := O.base_ge_two
  have hbminus : 1 ≤ b - 1 := by omega
  have hr := O.numerator_pos i
  have hu := O.numerator_upper i
  nlinarith

theorem numerator_lt_denominator {b q : ℕ}
    (O : InteriorNumeratorOrbit b q) (i : Fin (O.gaps.length + 1)) :
    O.numerators i < q := by
  have hb := O.base_ge_two
  have hbminus : 1 ≤ b - 1 := by omega
  have hr := O.numerator_pos i
  have hu := O.numerator_upper i
  nlinarith

/-- Every interior gap satisfies the explicit paper bound `b^g < 2q`. -/
theorem gap_power_lt_two_mul_denominator {b q : ℕ}
    (O : InteriorNumeratorOrbit b q) (i : Fin O.gaps.length) :
    b ^ O.gaps.get i < 2 * q := by
  have hrone : 1 ≤ O.numerators i.castSucc := O.numerator_pos _
  have hmul : b ^ O.gaps.get i ≤
      b ^ O.gaps.get i * O.numerators i.castSucc := by
    simpa only [mul_one] using
      Nat.mul_le_mul_left (b ^ O.gaps.get i) hrone
  rw [O.recurrence i] at hmul
  have hnext := O.numerator_lt_denominator i.succ
  omega

/-- Multiplying the individual gap bounds yields the quantitative mean-gap
input in `eq:qz`. -/
theorem span_power_le {b q : ℕ} (O : InteriorNumeratorOrbit b q) :
    b ^ Erdos260.GapWord.span O.gaps ≤ (2 * q) ^ O.gaps.length := by
  have hprod :
      (∏ i : Fin O.gaps.length, b ^ O.gaps.get i) ≤
        ∏ _i : Fin O.gaps.length, 2 * q := by
    exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      (fun i _ => (O.gap_power_lt_two_mul_denominator i).le)
  have hpowsum :
      (∏ i : Fin O.gaps.length, b ^ O.gaps.get i) =
        b ^ ∑ i : Fin O.gaps.length, O.gaps.get i := by
    simpa using Finset.prod_pow_eq_pow_sum
      (Finset.univ : Finset (Fin O.gaps.length))
      (fun i => O.gaps.get i) b
  rw [hpowsum] at hprod
  simpa [Erdos260.GapWord.span, Fin.sum_univ_getElem] using hprod

/-- Formula label `eq:qz`, in an exact real-power form. -/
theorem meanGap_rpow_le {b q : ℕ} (O : InteriorNumeratorOrbit b q)
    (hne : O.gaps ≠ []) :
    Real.rpow (b : ℝ)
        ((Erdos260.GapWord.span O.gaps : ℝ) / O.gaps.length) ≤
      2 * q := by
  have hn : O.gaps.length ≠ 0 := by
    simpa [List.length_eq_zero_iff] using hne
  have hpowNat := O.span_power_le
  have hpowReal :
      ((b : ℝ) ^ Erdos260.GapWord.span O.gaps) ≤
        ((2 * q : ℕ) : ℝ) ^ O.gaps.length := by
    exact_mod_cast hpowNat
  have hnReal : (0 : ℝ) < O.gaps.length := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hroot := Real.rpow_le_rpow (by positivity :
      (0 : ℝ) ≤ (b : ℝ) ^ Erdos260.GapWord.span O.gaps)
      hpowReal (by positivity : (0 : ℝ) ≤ (O.gaps.length : ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast (by positivity) hn] at hroot
  have hleft :
      Real.rpow (b : ℝ)
          ((Erdos260.GapWord.span O.gaps : ℝ) / O.gaps.length) =
        (((b : ℝ) ^ Erdos260.GapWord.span O.gaps) ^
          ((O.gaps.length : ℝ)⁻¹)) := by
    rw [div_eq_mul_inv]
    change (b : ℝ) ^
        ((Erdos260.GapWord.span O.gaps : ℝ) *
          (O.gaps.length : ℝ)⁻¹) = _
    rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
  rw [hleft]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hroot

/-- Formula label `eq:qz`: the recurrence controls both the mean gap and every
individual gap. -/
theorem eq_qz {b q : ℕ} (O : InteriorNumeratorOrbit b q)
    (hne : O.gaps ≠ []) :
    Real.rpow (b : ℝ)
        ((Erdos260.GapWord.span O.gaps : ℝ) / O.gaps.length) ≤
          2 * q ∧
      ∀ i : Fin O.gaps.length,
        b ^ O.gaps.get i < 2 * q :=
  ⟨O.meanGap_rpow_le hne, O.gap_power_lt_two_mul_denominator⟩

end InteriorNumeratorOrbit

/-! ## Denominator and mean-gap bands -/

/-- Lower dyadic band used for both stabilized denominators and mean gaps. -/
def dyadicFloorBand (n : ℕ) : ℕ := 2 ^ Nat.log 2 n

theorem dyadicFloorBand_pos (n : ℕ) : 0 < dyadicFloorBand n := by
  simp [dyadicFloorBand]

theorem dyadicFloorBand_le {n : ℕ} (hn : 0 < n) :
    dyadicFloorBand n ≤ n := by
  exact Nat.pow_log_le_self 2 hn.ne'

theorem dyadicFloorBand_lt_two_mul (n : ℕ) :
    n < 2 * dyadicFloorBand n := by
  calc
    n < 2 ^ (Nat.log 2 n + 1) :=
      Nat.lt_pow_succ_log_self (by omega : 1 < 2) n
    _ = 2 * dyadicFloorBand n := by
      rw [pow_succ]
      simp [dyadicFloorBand, mul_comm]

/-- Dyadic lower band of the integer mean gap. -/
def meanGapBand (span count : ℕ) : ℕ :=
  dyadicFloorBand (span / count)

theorem meanGapBand_pos (span count : ℕ) :
    0 < meanGapBand span count := dyadicFloorBand_pos _

theorem meanGapBand_bounds {span count : ℕ}
    (hcount : 0 < count) (hmean : count ≤ span) :
    meanGapBand span count ≤ span / count ∧
      span / count < 2 * meanGapBand span count := by
  have hdivPos : 0 < span / count := Nat.div_pos hmean hcount
  exact ⟨dyadicFloorBand_le hdivPos,
    dyadicFloorBand_lt_two_mul (span / count)⟩

/-- Multiplicative form of the mean-gap band bounds, convenient for the
greedy cover. -/
theorem meanGapBand_span_bounds {span count : ℕ}
    (hcount : 0 < count) (hmean : count ≤ span) :
    meanGapBand span count * count ≤ span ∧
      span < 2 * meanGapBand span count * count := by
  have hbounds := meanGapBand_bounds hcount hmean
  constructor
  · exact (Nat.le_div_iff_mul_le hcount).mp hbounds.1
  · exact (Nat.div_lt_iff_lt_mul hcount).mp hbounds.2

theorem denominatorBand_bounds {b q : ℕ}
    (O : InteriorNumeratorOrbit b q) :
    dyadicFloorBand q ≤ q ∧ q < 2 * dyadicFloorBand q :=
  ⟨dyadicFloorBand_le O.denominator_pos,
    dyadicFloorBand_lt_two_mul q⟩

/-- The quantitative lower bound on the mean gap after comparing the retained
interior span with the number of gaps.  This is the arithmetic core preceding
the dyadic rounding in `eq:zmin`. -/
theorem meanGap_lower_bound {C0 δ L m z : ℝ}
    (hδ : 0 < δ) (hL : 0 < L) (hz : 0 ≤ z)
    (hm : m ≤ Real.sqrt δ * L)
    (hspan : C0 * L ≤ 8 * m * z) :
    C0 / (8 * Real.sqrt δ) ≤ z := by
  have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hmz : m * z ≤ (Real.sqrt δ * L) * z :=
    mul_le_mul_of_nonneg_right hm hz
  have hscaled : 8 * m * z ≤ 8 * (Real.sqrt δ * L) * z := by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hmz (by norm_num : (0 : ℝ) ≤ 8)
  have hcancel : C0 * L ≤ (8 * Real.sqrt δ * z) * L := by
    calc
      C0 * L ≤ 8 * m * z := hspan
      _ ≤ 8 * (Real.sqrt δ * L) * z := hscaled
      _ = (8 * Real.sqrt δ * z) * L := by ring
  have hC0 : C0 ≤ 8 * Real.sqrt δ * z :=
    le_of_mul_le_mul_right hcancel hL
  apply (div_le_iff₀ (mul_pos (by norm_num) hsqrt)).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using hC0

/-- Formula label `eq:zmin`, with the dyadic convention `Z ≤ z < 2Z`.
The displayed constant is explicit rather than hidden in Vinogradov notation. -/
theorem eq_zmin {C0 δ L m z Z : ℝ}
    (hδ : 0 < δ) (hL : 0 < L) (hz : 0 ≤ z)
    (hm : m ≤ Real.sqrt δ * L)
    (hspan : C0 * L ≤ 8 * m * z)
    (hzBand : z < 2 * Z) :
    C0 / (16 * Real.sqrt δ) < Z := by
  have hmean := meanGap_lower_bound hδ hL hz hm hspan
  have hhalf :
      C0 / (16 * Real.sqrt δ) =
        (C0 / (8 * Real.sqrt δ)) / 2 := by ring
  rw [hhalf]
  linarith

/-- The exact natural-number version of
`ceil (log_b (C * D))` used for the greedy block scale. -/
def logarithmicBlockScale (b C D : ℕ) : ℕ :=
  Nat.clog b (C * D)

/-- Every genuine interior gap lies below the canonical logarithmic block
scale attached to the dyadic denominator band. -/
theorem InteriorNumeratorOrbit.gap_le_logarithmicBlockScale {b q : ℕ}
    (O : InteriorNumeratorOrbit b q) :
    ∀ g ∈ O.gaps,
      g ≤ logarithmicBlockScale b 4 (dyadicFloorBand q) := by
  intro g hg
  obtain ⟨r, hr, hget⟩ := List.getElem_of_mem hg
  let i : Fin O.gaps.length := ⟨r, hr⟩
  have hgap := O.gap_power_lt_two_mul_denominator i
  have hqband := denominatorBand_bounds O
  have hb := O.base_ge_two
  have hget' : O.gaps.get i = g := by
    simpa [i] using hget
  have hpow : b ^ g < 4 * dyadicFloorBand q := by
    rw [hget'] at hgap
    omega
  unfold logarithmicBlockScale
  exact ((Nat.lt_clog_iff_pow_lt (by omega : 1 < b)).2 hpow).le

theorem logarithmicBlockScale_four_pos {b D : ℕ}
    (hb : 2 ≤ b) (hD : 0 < D) :
    0 < logarithmicBlockScale b 4 D := by
  unfold logarithmicBlockScale
  rw [Nat.lt_clog_iff_pow_lt (by omega : 1 < b)]
  simp
  omega

/-- Formula label `eq:ellbound`.  If `D ≤ Cq W^s`, `W ≤ N`, and
`N < b^(L+1)`, then the exact ceiling logarithm is at most `s(L+1)` plus a
constant depending only on `b`, `C`, and `Cq`. -/
theorem eq_ellbound {b C Cq D W N L s : ℕ}
    (hb : 2 ≤ b) (hD : D ≤ Cq * W ^ s)
    (hW : W ≤ N) (hN : N < b ^ (L + 1)) :
    logarithmicBlockScale b C D ≤
      Nat.clog b (C * Cq) + s * (L + 1) := by
  apply (Nat.clog_le_iff_le_pow (by omega : 1 < b)).2
  have hWN : W ≤ b ^ (L + 1) := hW.trans hN.le
  have hWpow : W ^ s ≤ (b ^ (L + 1)) ^ s := by
    exact Nat.pow_le_pow_left hWN s
  have hconst : C * Cq ≤ b ^ Nat.clog b (C * Cq) :=
    Nat.le_pow_clog (by omega : 1 < b) _
  calc
    C * D ≤ C * (Cq * W ^ s) := Nat.mul_le_mul_left C hD
    _ = (C * Cq) * W ^ s := by simp [mul_assoc]
    _ ≤ b ^ Nat.clog b (C * Cq) * (b ^ (L + 1)) ^ s :=
      Nat.mul_le_mul hconst hWpow
    _ = b ^ (Nat.clog b (C * Cq) + s * (L + 1)) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      simp [mul_comm]

/-! ## Greedy logarithmic blocks -/

/-- A minimal crossing block overshoots its target by at most one maximal
gap. -/
theorem greedyBlock_span_le_add {block : Erdos260.GapWord} {bound cap : ℕ}
    (hblock : Erdos260.GapWord.IsGreedyBlock bound block)
    (hcap : ∀ g ∈ block, g ≤ cap) :
    Erdos260.GapWord.span block ≤ bound + cap := by
  have hlen : 0 < block.length := List.length_pos_iff.mpr hblock.1
  let r := block.length - 1
  have hrlt : r < block.length := by dsimp [r]; omega
  have hprefix : Erdos260.GapWord.prefixSpan block r < bound :=
    hblock.2.2 r hrlt
  have hlast : block.getLast hblock.1 ≤ cap :=
    hcap _ (List.getLast_mem hblock.1)
  have hsum :
      Erdos260.GapWord.span block =
        Erdos260.GapWord.prefixSpan block r + block.getLast hblock.1 := by
    unfold Erdos260.GapWord.span Erdos260.GapWord.prefixSpan
    calc
      block.sum =
          ((block.take r) ++ (block.drop r)).sum := by
        rw [List.take_append_drop]
      _ = (block.take r).sum + (block.drop r).sum := by simp
      _ = (block.take r).sum + block.getLast hblock.1 := by
        rw [show r = block.length - 1 by rfl, List.drop_length_sub_one hblock.1]
        simp
  rw [hsum]
  omega

/-- Formula label `eq:blockspan`. -/
theorem greedyBlock_three_four_span {ell : ℕ}
    {block : Erdos260.GapWord}
    (hblock : Erdos260.GapWord.IsGreedyBlock (3 * ell) block)
    (hcap : ∀ g ∈ block, g ≤ ell) :
    3 * ell ≤ Erdos260.GapWord.span block ∧
      Erdos260.GapWord.span block ≤ 4 * ell := by
  refine ⟨hblock.2.1, ?_⟩
  have h := greedyBlock_span_le_add hblock hcap
  omega

/-- Formula label `eq:blockspan`. -/
theorem eq_blockspan {ell : ℕ}
    {block : Erdos260.GapWord}
    (hblock : Erdos260.GapWord.IsGreedyBlock (3 * ell) block)
    (hcap : ∀ g ∈ block, g ≤ ell) :
    3 * ell ≤ Erdos260.GapWord.span block ∧
      Erdos260.GapWord.span block ≤ 4 * ell :=
  greedyBlock_three_four_span hblock hcap

/-- Exact span identity for the deterministic greedy decomposition. -/
theorem greedyDecompose_completed_add_remainder_span
    (word : Erdos260.GapWord) (bound : ℕ) (hbound : 0 < bound) :
    ((word.greedyDecompose bound).completed.map
        Erdos260.GapWord.span).sum +
      (word.greedyDecompose bound).remainder.span = word.span := by
  have hvalid := Erdos260.GapWord.greedyDecompose_valid word bound hbound
  have hsum := congrArg List.sum hvalid.1
  change
    ((word.greedyDecompose bound).completed.map List.sum).sum +
        (word.greedyDecompose bound).remainder.sum = word.sum
  simpa using hsum

/-- Before any additional block filtering, completed greedy blocks cover at
least half the word once the word spans twice the crossing threshold. -/
theorem greedyDecompose_half_cover (word : Erdos260.GapWord) (bound : ℕ)
    (hbound : 0 < bound) (hlong : 2 * bound ≤ word.span) :
    word.span ≤ 2 *
      ((word.greedyDecompose bound).completed.map
        Erdos260.GapWord.span).sum := by
  have hvalid := Erdos260.GapWord.greedyDecompose_valid word bound hbound
  have hsum := greedyDecompose_completed_add_remainder_span word bound hbound
  have hrem := hvalid.2.2
  omega

/-- Formula label `eq:cover`, isolated from the classification details: if
the prefix/remainder losses and filtered-block losses each consume at most the
displayed fractions, retained blocks control the original window span. -/
theorem retainedBlock_cover {V prefixLoss incompleteLoss filteredLoss retained : ℕ}
    (hdecomp : V ≤ prefixLoss + incompleteLoss + filteredLoss + retained)
    (hprefix : 8 * prefixLoss ≤ V)
    (hincomplete : 8 * incompleteLoss ≤ V)
    (hfiltered : 4 * filteredLoss ≤ V) :
    V ≤ 4 * retained := by
  omega

/-- Formula label `eq:cover`. -/
theorem eq_cover {V prefixLoss incompleteLoss filteredLoss retained : ℕ}
    (hdecomp : V ≤ prefixLoss + incompleteLoss + filteredLoss + retained)
    (hprefix : 8 * prefixLoss ≤ V)
    (hincomplete : 8 * incompleteLoss ≤ V)
    (hfiltered : 4 * filteredLoss ≤ V) :
    V ≤ 4 * retained :=
  retainedBlock_cover hdecomp hprefix hincomplete hfiltered

/-! ### Canonical retained blocks of an actual interior word -/

def completedGreedyBlocks (word : Erdos260.GapWord) (ell : ℕ) :
    List Erdos260.GapWord :=
  (word.greedyDecompose (3 * ell)).completed

/-- Greedy decomposition is stable under extension: every completed block
of a prefix remains, in the same position, after more gaps are appended.
The auxiliary fuel statement is what makes this a theorem about the actual
recursive implementation rather than an extra specification assumption. -/
theorem greedyDecomposeAux_completed_prefix_of_prefix
    {short long : Erdos260.GapWord} {shortFuel longFuel bound : ℕ}
    (hprefix : short.IsPrefix long)
    (hshortFuel : short.length ≤ shortFuel)
    (hlongFuel : long.length ≤ longFuel) :
    (Erdos260.GapWord.greedyDecomposeAux shortFuel short bound).completed.IsPrefix
      (Erdos260.GapWord.greedyDecomposeAux longFuel long bound).completed := by
  induction shortFuel generalizing short long longFuel with
  | zero =>
      have hshort : short = [] :=
        List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hshortFuel)
      subst short
      simp [Erdos260.GapWord.greedyDecomposeAux]
  | succ shortFuel ih =>
      by_cases hcross : 0 < bound ∧ bound ≤ Erdos260.GapWord.span short
      · have hshortNe : short ≠ [] := by
          intro hzero
          subst short
          simp [Erdos260.GapWord.span] at hcross
          omega
        have hspanLe : Erdos260.GapWord.span short ≤
            Erdos260.GapWord.span long := by
          rcases hprefix with ⟨tail, rfl⟩
          simp [Erdos260.GapWord.span]
        have hlongCross : 0 < bound ∧ bound ≤ Erdos260.GapWord.span long :=
          ⟨hcross.1, hcross.2.trans hspanLe⟩
        cases longFuel with
        | zero =>
            have hlong : long = [] :=
              List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlongFuel)
            have hlength := hprefix.length_le
            rw [hlong] at hlength
            simp only [List.length_nil, Nat.le_zero] at hlength
            exact (hshortNe (List.eq_nil_of_length_eq_zero hlength)).elim
        | succ longFuel =>
            have hblockEq : short.firstPrefixAtLeast bound =
                long.firstPrefixAtLeast bound :=
              firstPrefixAtLeast_eq_of_prefix hprefix hshortNe hcross.2
            have hblockNe : short.firstPrefixAtLeast bound ≠ [] :=
              Erdos260.GapWord.firstPrefixAtLeast_ne_nil short bound
                hcross.1 hcross.2
            have hblockLen :
                (short.firstPrefixAtLeast bound).length ≤ short.length :=
              (Erdos260.GapWord.firstPrefixAtLeast_isPrefix short bound).length_le
            simp only [Erdos260.GapWord.greedyDecomposeAux,
              if_pos hcross, if_pos hlongCross]
            rw [← hblockEq]
            apply List.cons_prefix_cons.mpr
            constructor
            · rfl
            · apply ih (hprefix.drop (short.firstPrefixAtLeast bound).length)
              · rw [List.length_drop]
                have hpositive : 0 < (short.firstPrefixAtLeast bound).length :=
                  List.length_pos_iff.mpr hblockNe
                omega
              · rw [List.length_drop]
                have hpositive : 0 < (short.firstPrefixAtLeast bound).length :=
                  List.length_pos_iff.mpr hblockNe
                have hlength := hprefix.length_le
                omega
      · simp only [Erdos260.GapWord.greedyDecomposeAux, if_neg hcross]
        exact List.nil_prefix

/-- The canonical completed-block list of a prefix is a prefix of the
completed-block list of every extension. -/
theorem completedGreedyBlocks_prefix_of_prefix
    {short long : Erdos260.GapWord} {ell : ℕ}
    (hprefix : short.IsPrefix long) :
    (completedGreedyBlocks short ell).IsPrefix
      (completedGreedyBlocks long ell) := by
  exact greedyDecomposeAux_completed_prefix_of_prefix hprefix le_rfl le_rfl

def completedGreedyBlock (word : Erdos260.GapWord) (ell : ℕ)
    (i : Fin (completedGreedyBlocks word ell).length) :
    Erdos260.GapWord :=
  (completedGreedyBlocks word ell)[i.1]

def completedGreedyPrefix (word : Erdos260.GapWord) (ell r : ℕ) :
    Erdos260.GapWord :=
  ((completedGreedyBlocks word ell).take r).flatten

def completedGreedyThrough (word : Erdos260.GapWord) (ell : ℕ)
    (i : Fin (completedGreedyBlocks word ell).length) :
    Erdos260.GapWord :=
  completedGreedyPrefix word ell (i + 1)

def retainedGreedyBlockIndices (word : Erdos260.GapWord)
    (ell Z : ℕ) : Finset (Fin (completedGreedyBlocks word ell).length) :=
  Finset.univ.filter fun i =>
    (completedGreedyBlock word ell i).length ≤ 16 * ell / Z

def discardedGreedyBlockIndices (word : Erdos260.GapWord)
    (ell Z : ℕ) : Finset (Fin (completedGreedyBlocks word ell).length) :=
  Finset.univ.filter fun i =>
    16 * ell / Z < (completedGreedyBlock word ell i).length

def retainedGreedyBlockSpan (word : Erdos260.GapWord)
    (ell Z : ℕ) : ℕ :=
  ∑ i ∈ retainedGreedyBlockIndices word ell Z,
    Erdos260.GapWord.span (completedGreedyBlock word ell i)

def discardedGreedyBlockSpan (word : Erdos260.GapWord)
    (ell Z : ℕ) : ℕ :=
  ∑ i ∈ discardedGreedyBlockIndices word ell Z,
    Erdos260.GapWord.span (completedGreedyBlock word ell i)

theorem completedGreedyBlock_mem (word : Erdos260.GapWord) (ell : ℕ)
    (i : Fin (completedGreedyBlocks word ell).length) :
    completedGreedyBlock word ell i ∈ completedGreedyBlocks word ell := by
  simpa only [completedGreedyBlock, List.get_eq_getElem] using
    (List.get_mem (completedGreedyBlocks word ell) i)

theorem completedGreedyThrough_eq_append (word : Erdos260.GapWord)
    (ell : ℕ) (i : Fin (completedGreedyBlocks word ell).length) :
    completedGreedyThrough word ell i =
      completedGreedyPrefix word ell i ++
        completedGreedyBlock word ell i := by
  have htake := List.take_concat_get
    (l := completedGreedyBlocks word ell) i.isLt
  have htake' :
      (completedGreedyBlocks word ell).take (i + 1) =
        (completedGreedyBlocks word ell).take i ++
          [(completedGreedyBlocks word ell)[i.1]] := by
    simpa only [List.concat_eq_append] using htake.symm
  unfold completedGreedyThrough completedGreedyPrefix completedGreedyBlock
  rw [htake', List.flatten_append]
  simp only [List.flatten_singleton]

/-- Every completed greedy prefix already present in a shorter word is
unchanged after extending the ambient word. -/
theorem completedGreedyPrefix_eq_of_prefix
    {short long : Erdos260.GapWord} {ell r : ℕ}
    (hprefix : short.IsPrefix long)
    (hr : r ≤ (completedGreedyBlocks short ell).length) :
    completedGreedyPrefix short ell r =
      completedGreedyPrefix long ell r := by
  obtain ⟨tail, htail⟩ := completedGreedyBlocks_prefix_of_prefix
    (ell := ell) hprefix
  unfold completedGreedyPrefix
  rw [← htail, List.take_append_of_le_length hr]

/-- Matching block positions in comparable words have the same flattened
greedy continuation through that block. -/
theorem completedGreedyThrough_eq_of_prefix
    {short long : Erdos260.GapWord} {ell : ℕ}
    (hprefix : short.IsPrefix long)
    (left : Fin (completedGreedyBlocks short ell).length)
    (right : Fin (completedGreedyBlocks long ell).length)
    (hindex : left.1 = right.1) :
    completedGreedyThrough short ell left =
      completedGreedyThrough long ell right := by
  unfold completedGreedyThrough
  have hr : left.1 + 1 ≤ (completedGreedyBlocks short ell).length := by
    omega
  simpa only [hindex] using
    completedGreedyPrefix_eq_of_prefix hprefix hr

/-- Matching block positions in comparable words expose the same canonical
greedy block. -/
theorem completedGreedyBlock_eq_of_prefix
    {short long : Erdos260.GapWord} {ell : ℕ}
    (hprefix : short.IsPrefix long)
    (left : Fin (completedGreedyBlocks short ell).length)
    (right : Fin (completedGreedyBlocks long ell).length)
    (hindex : left.1 = right.1) :
    completedGreedyBlock short ell left =
      completedGreedyBlock long ell right := by
  have hbefore : completedGreedyPrefix short ell left.1 =
      completedGreedyPrefix long ell right.1 := by
    have hr : left.1 ≤ (completedGreedyBlocks short ell).length :=
      left.isLt.le
    simpa only [hindex] using
      completedGreedyPrefix_eq_of_prefix hprefix hr
  have hthrough := completedGreedyThrough_eq_of_prefix
    hprefix left right hindex
  rw [completedGreedyThrough_eq_append,
    completedGreedyThrough_eq_append, hbefore] at hthrough
  exact List.append_right_injective _ hthrough

theorem completedGreedyThrough_isPrefix (word : Erdos260.GapWord)
    (ell : ℕ) (hell : 0 < ell)
    (i : Fin (completedGreedyBlocks word ell).length) :
    (completedGreedyThrough word ell i).IsPrefix word := by
  have hvalid := Erdos260.GapWord.greedyDecompose_valid word
    (3 * ell) (by positivity)
  have htake :
      ((completedGreedyBlocks word ell).take (i + 1)).IsPrefix
        (completedGreedyBlocks word ell) := List.take_prefix _ _
  obtain ⟨tailBlocks, htailBlocks⟩ := htake
  refine ⟨tailBlocks.flatten ++
      (word.greedyDecompose (3 * ell)).remainder, ?_⟩
  unfold completedGreedyThrough completedGreedyPrefix
  rw [← List.append_assoc, ← List.flatten_append, htailBlocks]
  simpa only [completedGreedyBlocks] using hvalid.1

/-- Flattened prefix lengths are strictly increasing when every component is
nonempty. -/
theorem length_flatten_take_strict {α : Type*} (blocks : List (List α))
    (hnonempty : ∀ block ∈ blocks, block ≠ [])
    {i j : ℕ} (hj : j ≤ blocks.length) (hij : i < j) :
    (blocks.take i).flatten.length < (blocks.take j).flatten.length := by
  induction blocks generalizing i j with
  | nil => simp at hj; omega
  | cons block blocks ih =>
      have hblock : block ≠ [] := hnonempty block (by simp)
      have hblockPos : 0 < block.length := List.length_pos_iff.mpr hblock
      have htail : ∀ tail ∈ blocks, tail ≠ [] := by
        intro tail htail
        exact hnonempty tail (by simp [htail])
      cases j with
      | zero => omega
      | succ j =>
          cases i with
          | zero =>
              simp only [List.take_zero, List.flatten_nil, List.length_nil,
                List.take_succ_cons, List.flatten_cons, List.length_append]
              omega
          | succ i =>
              have hjTail : j ≤ blocks.length := by simp at hj; omega
              have hijTail : i < j := by omega
              have hrec := ih htail hjTail hijTail
              simp only [List.take_succ_cons, List.flatten_cons,
                List.length_append]
              omega

/-- A list of nonempty blocks cannot have more blocks than entries in its
flattening. -/
theorem length_le_flatten_length_of_ne_nil {α : Type*}
    (blocks : List (List α))
    (hnonempty : ∀ block ∈ blocks, block ≠ []) :
    blocks.length ≤ blocks.flatten.length := by
  induction blocks with
  | nil => simp
  | cons block blocks ih =>
      have hblock : block ≠ [] := hnonempty block (by simp)
      have htail : ∀ tail ∈ blocks, tail ≠ [] := by
        intro tail htail
        exact hnonempty tail (by simp [htail])
      have hblockLength : 0 < block.length := List.length_pos_iff.mpr hblock
      have hrec := ih htail
      simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega

/-- The number of completed greedy blocks is bounded by the ambient word
length. -/
theorem completedGreedyBlocks_length_le (word : Erdos260.GapWord)
    (ell : ℕ) (hell : 0 < ell) :
    (completedGreedyBlocks word ell).length ≤ word.length := by
  have hvalid := Erdos260.GapWord.greedyDecompose_valid word
    (3 * ell) (by positivity)
  have hnonempty : ∀ block ∈ completedGreedyBlocks word ell,
      block ≠ [] := by
    intro block hblock
    exact (hvalid.2.1 block (by
      simpa only [completedGreedyBlocks] using hblock)).1
  have hblocks := length_le_flatten_length_of_ne_nil
    (completedGreedyBlocks word ell) hnonempty
  have htotal : (completedGreedyBlocks word ell).flatten.length +
      (word.greedyDecompose (3 * ell)).remainder.length = word.length := by
    simpa only [completedGreedyBlocks, List.length_append] using
      congrArg List.length hvalid.1
  exact hblocks.trans (by omega)

theorem completedGreedyThrough_length_injective (word : Erdos260.GapWord)
    (ell : ℕ) (hell : 0 < ell) :
    Function.Injective fun i : Fin (completedGreedyBlocks word ell).length =>
      (completedGreedyThrough word ell i).length := by
  have hvalid := Erdos260.GapWord.greedyDecompose_valid word
    (3 * ell) (by positivity)
  have hnonempty : ∀ block ∈ completedGreedyBlocks word ell,
      block ≠ [] := by
    intro block hblock
    exact (hvalid.2.1 block (by
      simpa only [completedGreedyBlocks] using hblock)).1
  intro i j hij
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstrict := length_flatten_take_strict
      (completedGreedyBlocks word ell) hnonempty
      (j := j.1 + 1) (by omega) (by omega : i.1 + 1 < j.1 + 1)
    exact (ne_of_lt hstrict) hij
  · have hstrict := length_flatten_take_strict
      (completedGreedyBlocks word ell) hnonempty
      (j := i.1 + 1) (by omega) (by omega : j.1 + 1 < i.1 + 1)
    exact (ne_of_gt hstrict) hij

theorem completedGreedyBlock_span_bounds {word : Erdos260.GapWord}
    {ell : ℕ} (hell : 0 < ell)
    (hcap : ∀ g ∈ word, g ≤ ell)
    (i : Fin (completedGreedyBlocks word ell).length) :
    3 * ell ≤ Erdos260.GapWord.span (completedGreedyBlock word ell i) ∧
      Erdos260.GapWord.span (completedGreedyBlock word ell i) ≤ 4 * ell := by
  have hvalid := Erdos260.GapWord.greedyDecompose_valid word
    (3 * ell) (by positivity)
  have hmem := completedGreedyBlock_mem word ell i
  have hgreedy : Erdos260.GapWord.IsGreedyBlock (3 * ell)
      (completedGreedyBlock word ell i) := by
    exact hvalid.2.1 _ (by simpa [completedGreedyBlocks] using hmem)
  have hblockCap : ∀ g ∈ completedGreedyBlock word ell i, g ≤ ell := by
    intro g hg
    apply hcap g
    rw [← hvalid.1]
    simp only [List.mem_append, List.mem_flatten]
    left
    exact ⟨completedGreedyBlock word ell i,
      by simpa [completedGreedyBlocks] using hmem, hg⟩
  exact greedyBlock_three_four_span hgreedy hblockCap

theorem sum_completedGreedyBlock_span (word : Erdos260.GapWord)
    (ell : ℕ) :
    ∑ i : Fin (completedGreedyBlocks word ell).length,
        Erdos260.GapWord.span (completedGreedyBlock word ell i) =
      ((completedGreedyBlocks word ell).map
        Erdos260.GapWord.span).sum := by
  simp [completedGreedyBlock]

/-- Word remaining strictly after one completed block, with the final greedy
remainder retained. -/
def completedBlockAfter (blocks : List Erdos260.GapWord)
    (remainder : Erdos260.GapWord) (i : Fin blocks.length) :
    Erdos260.GapWord :=
  (blocks.drop (i.1 + 1)).flatten ++ remainder

/-- Total span of all completed blocks whose remaining word has span at most
`F`.  This deliberately includes non-retained blocks, so it is an upper bound
for every shallow retained census. -/
def shallowCompletedBlockSpan (blocks : List Erdos260.GapWord)
    (remainder : Erdos260.GapWord) (F : ℕ) : ℕ :=
  ∑ i : Fin blocks.length,
    if Erdos260.GapWord.span (completedBlockAfter blocks remainder i) ≤ F then
      Erdos260.GapWord.span (blocks.get i)
    else 0

theorem completedBlockAfter_span_le_total
    (blocks : List Erdos260.GapWord) (remainder : Erdos260.GapWord)
    (i : Fin blocks.length) :
    Erdos260.GapWord.span (completedBlockAfter blocks remainder i) ≤
      Erdos260.GapWord.span (blocks.flatten ++ remainder) := by
  have hsplit : (blocks.take (i.1 + 1)).flatten ++
      (blocks.drop (i.1 + 1)).flatten = blocks.flatten := by
    rw [← List.flatten_append, List.take_append_drop]
  unfold completedBlockAfter Erdos260.GapWord.span
  rw [← hsplit]
  simp only [List.sum_append]
  omega

theorem shallowCompletedBlockSpan_eq_total_of_le
    (blocks : List Erdos260.GapWord) (remainder : Erdos260.GapWord)
    (F : ℕ)
    (htotal : Erdos260.GapWord.span (blocks.flatten ++ remainder) ≤ F) :
    shallowCompletedBlockSpan blocks remainder F =
      ∑ i : Fin blocks.length, Erdos260.GapWord.span (blocks.get i) := by
  unfold shallowCompletedBlockSpan
  apply Finset.sum_congr rfl
  intro i _hi
  rw [if_pos ((completedBlockAfter_span_le_total blocks remainder i).trans
    htotal)]

theorem shallowCompletedBlockSpan_cons
    (block : Erdos260.GapWord) (blocks : List Erdos260.GapWord)
    (remainder : Erdos260.GapWord) (F : ℕ) :
    shallowCompletedBlockSpan (block :: blocks) remainder F =
      (if Erdos260.GapWord.span (blocks.flatten ++ remainder) ≤ F then
        Erdos260.GapWord.span block else 0) +
        shallowCompletedBlockSpan blocks remainder F := by
  simp [shallowCompletedBlockSpan, Fin.sum_univ_succ,
    completedBlockAfter]

/-- Shallow completed blocks form a terminal suffix.  If every completed
block has span at most `H`, their total shallow span is at most `F + H`. -/
theorem shallowCompletedBlockSpan_le
    (blocks : List Erdos260.GapWord) (remainder : Erdos260.GapWord)
    (F H : ℕ)
    (hblock : ∀ block ∈ blocks,
      Erdos260.GapWord.span block ≤ H) :
    shallowCompletedBlockSpan blocks remainder F ≤ F + H := by
  induction blocks with
  | nil => simp [shallowCompletedBlockSpan]
  | cons block blocks ih =>
      rw [shallowCompletedBlockSpan_cons]
      by_cases htail :
          Erdos260.GapWord.span (blocks.flatten ++ remainder) ≤ F
      · rw [if_pos htail,
          shallowCompletedBlockSpan_eq_total_of_le blocks remainder F htail]
        have hhead : Erdos260.GapWord.span block ≤ H :=
          hblock block (by simp)
        have hsum :
            (∑ i : Fin blocks.length,
              Erdos260.GapWord.span (blocks.get i)) ≤
              Erdos260.GapWord.span (blocks.flatten ++ remainder) := by
          have heq : (∑ i : Fin blocks.length,
              Erdos260.GapWord.span (blocks.get i)) =
              Erdos260.GapWord.span blocks.flatten := by
            simp [Erdos260.GapWord.span]
          rw [heq]
          simp only [Erdos260.GapWord.span, List.sum_append]
          omega
        omega
      · rw [if_neg htail, zero_add]
        apply ih
        intro tailBlock htailBlock
        exact hblock tailBlock (by simp [htailBlock])

theorem sum_completedGreedyBlock_length_le (word : Erdos260.GapWord)
    (ell : ℕ) (hell : 0 < ell) :
    (∑ i : Fin (completedGreedyBlocks word ell).length,
        (completedGreedyBlock word ell i).length) ≤ word.length := by
  have hvalid := Erdos260.GapWord.greedyDecompose_valid word
    (3 * ell) (by positivity)
  have hlength := congrArg List.length hvalid.1
  have hsum :
      ((completedGreedyBlocks word ell).map List.length).sum +
          (word.greedyDecompose (3 * ell)).remainder.length = word.length := by
    simpa [completedGreedyBlocks] using hlength
  have hfin :
      (∑ i : Fin (completedGreedyBlocks word ell).length,
          (completedGreedyBlock word ell i).length) =
        ((completedGreedyBlocks word ell).map List.length).sum := by
    simp [completedGreedyBlock]
  rw [hfin]
  omega

theorem retained_add_discardedGreedyBlockSpan
    (word : Erdos260.GapWord) (ell Z : ℕ) :
    retainedGreedyBlockSpan word ell Z +
        discardedGreedyBlockSpan word ell Z =
      ∑ i : Fin (completedGreedyBlocks word ell).length,
        Erdos260.GapWord.span (completedGreedyBlock word ell i) := by
  classical
  unfold retainedGreedyBlockSpan discardedGreedyBlockSpan
    retainedGreedyBlockIndices discardedGreedyBlockIndices
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset
        (Fin (completedGreedyBlocks word ell).length)))
      (p := fun i =>
        (completedGreedyBlock word ell i).length ≤ 16 * ell / Z)
      (f := fun i =>
        Erdos260.GapWord.span (completedGreedyBlock word ell i)))

/-- Blocks rejected by the gap-count filter consume at most one quarter of
an interior word whose dyadic mean-gap lower band is `Z`. -/
theorem discardedGreedyBlockSpan_four_le {word : Erdos260.GapWord}
    {ell Z : ℕ} (hell : 0 < ell) (hZ : 0 < Z)
    (hcap : ∀ g ∈ word, g ≤ ell)
    (hmean : Z * word.length ≤ Erdos260.GapWord.span word) :
    4 * discardedGreedyBlockSpan word ell Z ≤
      Erdos260.GapWord.span word := by
  classical
  let bad := discardedGreedyBlockIndices word ell Z
  have hterm (i : Fin (completedGreedyBlocks word ell).length)
      (hi : i ∈ bad) :
      4 * Erdos260.GapWord.span (completedGreedyBlock word ell i) ≤
        Z * (completedGreedyBlock word ell i).length := by
    have hibad : 16 * ell / Z <
        (completedGreedyBlock word ell i).length := by
      simpa only [bad, discardedGreedyBlockIndices, Finset.mem_filter,
        Finset.mem_univ, true_and] using hi
    have hmul : 16 * ell <
        (completedGreedyBlock word ell i).length * Z :=
      (Nat.div_lt_iff_lt_mul hZ).mp hibad
    have hspan := (completedGreedyBlock_span_bounds hell hcap i).2
    nlinarith
  have hbadSubset : bad ⊆
      (Finset.univ : Finset
        (Fin (completedGreedyBlocks word ell).length)) := by
    exact Finset.subset_univ _
  have hlength := sum_completedGreedyBlock_length_le word ell hell
  calc
    4 * discardedGreedyBlockSpan word ell Z =
        ∑ i ∈ bad,
          4 * Erdos260.GapWord.span
            (completedGreedyBlock word ell i) := by
      simp [discardedGreedyBlockSpan, bad, Finset.mul_sum]
    _ ≤ ∑ i ∈ bad,
          Z * (completedGreedyBlock word ell i).length := by
      exact Finset.sum_le_sum hterm
    _ ≤ ∑ i : Fin (completedGreedyBlocks word ell).length,
          Z * (completedGreedyBlock word ell i).length := by
      exact Finset.sum_le_sum_of_subset hbadSubset
    _ = Z * ∑ i : Fin (completedGreedyBlocks word ell).length,
          (completedGreedyBlock word ell i).length := by
      rw [Finset.mul_sum]
    _ ≤ Z * word.length := Nat.mul_le_mul_left Z hlength
    _ ≤ Erdos260.GapWord.span word := hmean

/-- Completed blocks surviving the deterministic gap-count filter cover a
fixed fraction of every sufficiently long actual interior word. -/
theorem retainedGreedyBlock_cover {word : Erdos260.GapWord}
    {ell Z : ℕ} (hell : 0 < ell) (hZ : 0 < Z)
    (hcap : ∀ g ∈ word, g ≤ ell)
    (hmean : Z * word.length ≤ Erdos260.GapWord.span word)
    (hlong : 24 * ell ≤ Erdos260.GapWord.span word) :
    Erdos260.GapWord.span word ≤
      4 * retainedGreedyBlockSpan word ell Z := by
  have hvalid := Erdos260.GapWord.greedyDecompose_valid word
    (3 * ell) (by positivity)
  have hspan := greedyDecompose_completed_add_remainder_span
    word (3 * ell) (by positivity)
  have htotal :
      ∑ i : Fin (completedGreedyBlocks word ell).length,
          Erdos260.GapWord.span (completedGreedyBlock word ell i) +
        (word.greedyDecompose (3 * ell)).remainder.span = word.span := by
    rw [sum_completedGreedyBlock_span]
    simpa only [completedGreedyBlocks] using hspan
  have hpartition := retained_add_discardedGreedyBlockSpan word ell Z
  have hdecomp : word.span ≤
      0 + (word.greedyDecompose (3 * ell)).remainder.span +
        discardedGreedyBlockSpan word ell Z +
        retainedGreedyBlockSpan word ell Z := by
    omega
  have hincomplete :
      8 * (word.greedyDecompose (3 * ell)).remainder.span ≤ word.span := by
    have hrem := hvalid.2.2
    omega
  exact retainedBlock_cover hdecomp (by simp) hincomplete
    (discardedGreedyBlockSpan_four_le hell hZ hcap hmean)

/-- Candidate retained block words in a fixed `(ell,Z)` band. -/
def retainedBlockWords (ell Z : ℕ) : Finset Erdos260.GapWord :=
  (boundedPositiveGapWords (4 * ell) (16 * ell / Z)).filter fun w =>
    3 * ell ≤ Erdos260.GapWord.span w

theorem mem_retainedBlockWords_iff {ell Z : ℕ} {w : Erdos260.GapWord} :
    w ∈ retainedBlockWords ell Z ↔
      Erdos260.GapWord.Positive w ∧
        3 * ell ≤ Erdos260.GapWord.span w ∧
        Erdos260.GapWord.span w ≤ 4 * ell ∧
        w.length ≤ 16 * ell / Z := by
  simp only [retainedBlockWords, Finset.mem_filter,
    mem_boundedPositiveGapWords_iff]
  constructor
  · rintro ⟨⟨hpositive, hupper, hlength⟩, hlower⟩
    exact ⟨hpositive, hlower, hupper, hlength⟩
  · rintro ⟨hpositive, hlower, hupper, hlength⟩
    exact ⟨⟨hpositive, hupper, hlength⟩, hlower⟩

/-- The canonical `3 log_b(4D)` block length automatically supplies the
Farey-separation inequality used in block-state recovery. -/
theorem retainedBlockWord_short_separation {b D Z : ℕ}
    (hb : 2 ≤ b) (hD : 0 < D) (word : Erdos260.GapWord)
    (hword : word ∈
      retainedBlockWords (logarithmicBlockScale b 4 D) Z) :
    1 / ((b - 1 : ℝ) * (b : ℝ) ^ Erdos260.GapWord.span word) <
      1 / (4 * (D : ℝ) ^ 2) := by
  let ell := logarithmicBlockScale b 4 D
  have hspan : 3 * ell ≤ Erdos260.GapWord.span word := by
    simpa only [ell] using (mem_retainedBlockWords_iff.mp hword).2.1
  have hclog : 4 * D ≤ b ^ ell := by
    exact Nat.le_pow_clog (by omega : 1 < b) (4 * D)
  have hcube : (4 * D) ^ 3 ≤ b ^ Erdos260.GapWord.span word := by
    calc
      (4 * D) ^ 3 ≤ (b ^ ell) ^ 3 := Nat.pow_le_pow_left hclog 3
      _ = b ^ (ell * 3) := by rw [pow_mul]
      _ = b ^ (3 * ell) := by rw [Nat.mul_comm]
      _ ≤ b ^ Erdos260.GapWord.span word :=
        Nat.pow_le_pow_right (by omega) hspan
  have hsmall : 4 * D ^ 2 < (4 * D) ^ 3 := by
    calc
      4 * D ^ 2 ≤ 16 * D ^ 2 :=
        Nat.mul_le_mul_right (D ^ 2) (by omega)
      _ = (4 * D) ^ 2 := by ring
      _ < (4 * D) ^ 3 :=
        pow_lt_pow_right₀ (by omega : 1 < 4 * D) (by omega)
  have hmul : b ^ Erdos260.GapWord.span word ≤
      (b - 1) * b ^ Erdos260.GapWord.span word := by
    simpa only [one_mul] using Nat.mul_le_mul_right
      (b ^ Erdos260.GapWord.span word) (by omega : 1 ≤ b - 1)
  have hdenNat : 4 * D ^ 2 <
      (b - 1) * b ^ Erdos260.GapWord.span word :=
    hsmall.trans_le (hcube.trans hmul)
  have hdenCast : ((4 * D ^ 2 : ℕ) : ℝ) <
      (((b - 1) * b ^ Erdos260.GapWord.span word : ℕ) : ℝ) := by
    exact_mod_cast hdenNat
  have hdenReal : 4 * (D : ℝ) ^ 2 <
      (b - 1 : ℝ) * (b : ℝ) ^ Erdos260.GapWord.span word := by
    simpa only [Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_one,
      Nat.cast_sub (by omega : 1 ≤ b)] using hdenCast
  exact one_div_lt_one_div_of_lt (by positivity) hdenReal

/-- Every block selected by the canonical actual-word filter belongs to the
finite retained-word census. -/
theorem completedGreedyBlock_mem_retainedBlockWords
    {word : Erdos260.GapWord} {ell Z : ℕ}
    (hell : 0 < ell)
    (hpositive : Erdos260.GapWord.Positive word)
    (hcap : ∀ g ∈ word, g ≤ ell)
    {i : Fin (completedGreedyBlocks word ell).length}
    (hi : i ∈ retainedGreedyBlockIndices word ell Z) :
    completedGreedyBlock word ell i ∈ retainedBlockWords ell Z := by
  rw [mem_retainedBlockWords_iff]
  have hspan := completedGreedyBlock_span_bounds hell hcap i
  have hlength : (completedGreedyBlock word ell i).length ≤
      16 * ell / Z := by
    simpa only [retainedGreedyBlockIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] using hi
  have hblockPositive :
      Erdos260.GapWord.Positive (completedGreedyBlock word ell i) := by
    intro g hg
    apply hpositive g
    have hvalid := Erdos260.GapWord.greedyDecompose_valid word
      (3 * ell) (by positivity)
    rw [← hvalid.1]
    simp only [List.mem_append, List.mem_flatten]
    left
    exact ⟨completedGreedyBlock word ell i,
      by simpa [completedGreedyBlocks] using
        completedGreedyBlock_mem word ell i, hg⟩
  exact ⟨hblockPositive, hspan.1, hspan.2, hlength⟩

theorem retainedBlockWords_card_le (ell Z : ℕ) :
    (retainedBlockWords ell Z).card ≤
      ∑ r ∈ Finset.Icc 0 (16 * ell / Z), (4 * ell).choose r := by
  exact (Finset.card_filter_le _ _).trans
    (boundedPositiveGapWords_card_le (4 * ell) (16 * ell / Z))

/-- Proof-bearing combinatorial portion used later in the full theorem
`lem:blocks`. -/
theorem lem_blocks_census (ell Z : ℕ) :
    (∀ w ∈ retainedBlockWords ell Z,
      3 * ell ≤ Erdos260.GapWord.span w ∧
        Erdos260.GapWord.span w ≤ 4 * ell ∧
        w.length ≤ 16 * ell / Z) ∧
      (retainedBlockWords ell Z).card ≤
        ∑ r ∈ Finset.Icc 0 (16 * ell / Z), (4 * ell).choose r := by
  constructor
  · intro w hw
    exact (mem_retainedBlockWords_iff.mp hw).2
  · exact retainedBlockWords_card_le ell Z

/-- Manuscript label `lem:blocks`, exposing the proof-bearing finite census.
Exact state recovery for each word and denominator band is supplied by
`blockState_unique` below. -/
theorem lem_blocks (ell Z : ℕ) :
    (∀ w ∈ retainedBlockWords ell Z,
      3 * ell ≤ Erdos260.GapWord.span w ∧
        Erdos260.GapWord.span w ≤ 4 * ell ∧
        w.length ≤ 16 * ell / Z) ∧
      (retainedBlockWords ell Z).card ≤
        ∑ r ∈ Finset.Icc 0 (16 * ell / Z), (4 * ell).choose r :=
  lem_blocks_census ell Z

/-- Formula label `eq:blockentropy` before substituting `ell = O(log D)`.
This is the exact entropy expression that tends to a zero power as
`Z → ∞`. -/
theorem retainedBlockWords_entropy (ell Z : ℕ) (hell : 0 < ell)
    (α : ℝ) (hα0 : 0 < α) (hαhalf : α ≤ 1 / 2)
    (hratio : ((16 * ell / Z + 1 : ℕ) : ℝ) ≤
      α * (4 * ell + 1 : ℕ)) :
    ((retainedBlockWords ell Z).card : ℝ) ≤
      ((4 * ell + 1 : ℕ) : ℝ) ^ 2 *
        Real.rpow 2
          (((4 * ell + 1 : ℕ) : ℝ) * Erdos260.binaryEntropy α) := by
  let H := 4 * ell
  let rMax := 16 * ell / Z
  have hHtwo : 2 ≤ H + 1 := by dsimp [H]; omega
  have hcomp := Erdos260.lem_composition_entropy
    (H + 1) (rMax + 1) α hHtwo hα0 hαhalf (by
      simpa [H, rMax] using hratio)
  have hcardNat := retainedBlockWords_card_le ell Z
  have hcardReal :
      ((retainedBlockWords ell Z).card : ℝ) ≤
        ((∑ r ∈ Finset.Icc 0 rMax, H.choose r : ℕ) : ℝ) := by
    exact_mod_cast (by simpa [H, rMax] using hcardNat)
  calc
    ((retainedBlockWords ell Z).card : ℝ) ≤
        ((∑ r ∈ Finset.Icc 0 rMax, H.choose r : ℕ) : ℝ) := hcardReal
    _ = ((∑ q ∈ Finset.Icc 1 (rMax + 1),
          H.choose (q - 1) : ℕ) : ℝ) := by
      rw [Erdos260.sum_choose_Icc_zero_eq_shift]
    _ ≤ (((H + 1 : ℕ) : ℝ) ^ 2 *
        Real.rpow 2
          (((H + 1 : ℕ) : ℝ) * Erdos260.binaryEntropy α)) := by
      simpa [H] using hcomp
    _ = _ := by simp [H]

/-- Formula label `eq:blockentropy`. -/
theorem eq_blockentropy (ell Z : ℕ) (hell : 0 < ell)
    (α : ℝ) (hα0 : 0 < α) (hαhalf : α ≤ 1 / 2)
    (hratio : ((16 * ell / Z + 1 : ℕ) : ℝ) ≤
      α * (4 * ell + 1 : ℕ)) :
    ((retainedBlockWords ell Z).card : ℝ) ≤
      ((4 * ell + 1 : ℕ) : ℝ) ^ 2 *
        Real.rpow 2
          (((4 * ell + 1 : ℕ) : ℝ) * Erdos260.binaryEntropy α) :=
  retainedBlockWords_entropy ell Z hell α hα0 hαhalf hratio

/-! ## Exact recovery of a block state -/

/-- Common words act affinely with multiplier `b^span`; polynomial
corrections cancel in differences. -/
theorem topStateAlong_sub (b : ℕ) (gaps : Erdos260.GapWord) (μ ν : ℝ) :
    topStateAlong b gaps μ - topStateAlong b gaps ν =
      (b : ℝ) ^ Erdos260.GapWord.span gaps * (μ - ν) := by
  induction gaps generalizing μ ν with
  | nil => simp [Erdos260.GapWord.span]
  | cons g gs ih =>
      simp only [topStateAlong_cons, Erdos260.GapWord.span, List.sum_cons,
        pow_add]
      rw [ih]
      simp only [Erdos260.GapWord.span]
      ring

theorem interiorState_abs_sub_lt {b : ℕ} (hb : 2 ≤ b) {μ ν : ℝ}
    (hμ : InteriorState b μ) (hν : InteriorState b ν) :
    |μ - ν| < 1 / (b - 1 : ℝ) := by
  have hbReal : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbminus : (0 : ℝ) < b - 1 := by linarith
  have hμpos : 0 < μ := pos_of_mul_pos_right hμ.1 hbminus.le
  have hνpos : 0 < ν := pos_of_mul_pos_right hν.1 hbminus.le
  have hμupper : μ < 1 / (b - 1 : ℝ) :=
    (lt_div_iff₀ hbminus).mpr (by simpa [mul_comm] using hμ.2)
  have hνupper : ν < 1 / (b - 1 : ℝ) :=
    (lt_div_iff₀ hbminus).mpr (by simpa [mul_comm] using hν.2)
  rw [abs_lt]
  constructor
  · linarith
  · linarith

/-- A common word contracts the possible starting interval of two interior
trajectories by the full factor `b^span`. -/
theorem interior_start_distance_lt {b : ℕ} (hb : 2 ≤ b)
    (gaps : Erdos260.GapWord) {μ ν : ℝ}
    (hμend : InteriorState b (topStateAlong b gaps μ))
    (hνend : InteriorState b (topStateAlong b gaps ν)) :
    |μ - ν| <
      1 / ((b - 1 : ℝ) * (b : ℝ) ^ Erdos260.GapWord.span gaps) := by
  have hpow : (0 : ℝ) < (b : ℝ) ^ Erdos260.GapWord.span gaps := by positivity
  have hend := interiorState_abs_sub_lt hb hμend hνend
  have hdiff := congrArg abs (topStateAlong_sub b gaps μ ν)
  rw [abs_mul, abs_of_pos hpow] at hdiff
  rw [hdiff] at hend
  have hbReal : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbminus : (0 : ℝ) < b - 1 := by linarith
  have hid :
      1 / ((b - 1 : ℝ) * (b : ℝ) ^ Erdos260.GapWord.span gaps) =
        (1 / (b - 1 : ℝ)) / ((b : ℝ) ^ Erdos260.GapWord.span gaps) := by
    field_simp
  rw [hid]
  apply (lt_div_iff₀ hpow).mpr
  simpa [mul_comm] using hend

/-- Farey separation makes the exact starting (and hence ending) state a
function of the block word and denominator band. -/
theorem blockState_unique {b D : ℕ} (hb : 2 ≤ b)
    (gaps : Erdos260.GapWord)
    (a c : ℤ) (q r : ℕ)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hqD : q < 2 * D) (hrD : r < 2 * D)
    (haEnd : InteriorState b
      (topStateAlong b gaps (((a : ℚ) / q : ℚ) : ℝ)))
    (hcEnd : InteriorState b
      (topStateAlong b gaps (((c : ℚ) / r : ℚ) : ℝ)))
    (hshort :
      1 / ((b - 1 : ℝ) * (b : ℝ) ^ Erdos260.GapWord.span gaps) <
        1 / (4 * (D : ℝ) ^ 2)) :
    (a : ℚ) / q = (c : ℚ) / r := by
  by_contra hne
  have hfarey := Erdos260.lem_farey a c q r D hq hr hqD hrD hne
  have hclose := interior_start_distance_lt hb gaps haEnd hcEnd
  have hcast :
      |((((a : ℚ) / q : ℚ) : ℝ) - (((c : ℚ) / r : ℚ) : ℝ))| =
        |(a : ℝ) / q - (c : ℝ) / r| := by
    norm_num
  rw [hcast] at hclose
  linarith

/-- Graph-level wrapper for block-state recovery.  Two certified graphs whose
starting state denominators lie in the same band and whose common block ends
in the interior have exactly the same rational starting state. -/
theorem PolynomialGraph.normalizedTopState_eq_of_commonInteriorBlock
    {d b Q Dband : ℕ} (hb : 2 ≤ b)
    (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d)
    (hA : (Q : ℚ) * (w.coeff d : ℚ) ≠ 0)
    (left right : PolynomialGraph d) (gaps : Erdos260.GapWord)
    (hleftBand : (left.normalizedTopState Q w).den < 2 * Dband)
    (hrightBand : (right.normalizedTopState Q w).den < 2 * Dband)
    (hleftEnd : InteriorState b
      ((((left.transformWord b Q w hwdeg gaps).normalizedTopState
        Q w : ℚ) : ℝ)))
    (hrightEnd : InteriorState b
      ((((right.transformWord b Q w hwdeg gaps).normalizedTopState
        Q w : ℚ) : ℝ)))
    (hshort :
      1 / ((b - 1 : ℝ) * (b : ℝ) ^ Erdos260.GapWord.span gaps) <
        1 / (4 * (Dband : ℝ) ^ 2)) :
    left.normalizedTopState Q w = right.normalizedTopState Q w := by
  let μ := left.normalizedTopState Q w
  let ν := right.normalizedTopState Q w
  have hleftEnd' : InteriorState b
      (topStateAlong b gaps ((μ : ℚ) : ℝ)) := by
    have hrat := left.normalizedTopState_transformWord b Q w hwdeg hA gaps
    have hcast := topStateAlongRat_cast b gaps μ
    rw [hrat, hcast] at hleftEnd
    exact hleftEnd
  have hrightEnd' : InteriorState b
      (topStateAlong b gaps ((ν : ℚ) : ℝ)) := by
    have hrat := right.normalizedTopState_transformWord b Q w hwdeg hA gaps
    have hcast := topStateAlongRat_cast b gaps ν
    rw [hrat, hcast] at hrightEnd
    exact hrightEnd
  have hunique := blockState_unique hb gaps μ.num ν.num μ.den ν.den
    (by exact μ.den_pos) (by exact ν.den_pos)
    (by simpa only [μ] using hleftBand)
    (by simpa only [ν] using hrightBand)
    (by simpa only [μ.num_div_den] using hleftEnd')
    (by simpa only [ν.num_div_den] using hrightEnd') hshort
  simpa only [μ.num_div_den, ν.num_div_den] using hunique

/-! ## Divisibility versus size -/

theorem int_eq_zero_of_pow_dvd_of_cast_abs_lt {b F : ℕ}
    {z : ℤ} (hdiv : (b : ℤ) ^ F ∣ z)
    (hlt : |(z : ℝ)| < (b : ℝ) ^ F) : z = 0 := by
  by_contra hz
  have hdiv_nat : b ^ F ∣ z.natAbs := by
    rw [← Int.natCast_dvd_natCast]
    have hdiv' : (b : ℤ) ^ F ∣ (z.natAbs : ℤ) := Int.dvd_natAbs.mpr hdiv
    simpa only [Int.natCast_pow] using hdiv'
  have hle : b ^ F ≤ z.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hz) hdiv_nat
  have hlt_real : (z.natAbs : ℝ) < ((b ^ F : ℕ) : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_pow] using hlt
  have hlt_nat : z.natAbs < b ^ F := by exact_mod_cast hlt_real
  exact (not_lt_of_ge hle) hlt_nat

/-! ## Difference certificates for locked graphs -/

/-- Real image of a certified rational graph. -/
def PolynomialGraph.realPoly {d : ℕ} (G : PolynomialGraph d) : Polynomial ℝ :=
  G.poly.map (algebraMap ℚ ℝ)

theorem PolynomialGraph.realPoly_degree_le {d : ℕ} (G : PolynomialGraph d) :
    G.realPoly.natDegree ≤ d :=
  (Polynomial.natDegree_map_le (f := algebraMap ℚ ℝ) (p := G.poly)).trans
    G.degree_le

/-- An interior normalized top state is nonzero, hence the ambient
degree-`d` graph really has degree `d`.  This is derived from the state and
is not recorded as an extra graph hypothesis. -/
theorem PolynomialGraph.natDegree_eq_of_interiorState {d b Q : ℕ}
    (G : PolynomialGraph d) (hb : 2 ≤ b) (w : Polynomial ℤ)
    (hstate : InteriorState b
      (((G.normalizedTopState Q w : ℚ) : ℝ))) :
    G.poly.natDegree = d := by
  have hbReal : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbminus : (0 : ℝ) < b - 1 := by linarith
  have hμpos : (0 : ℝ) <
      ((G.normalizedTopState Q w : ℚ) : ℝ) :=
    pos_of_mul_pos_right hstate.1 hbminus.le
  have hcoeff : G.poly.coeff d ≠ 0 := by
    intro hzero
    have hstateZero : G.normalizedTopState Q w = 0 := by
      simp [PolynomialGraph.normalizedTopState, topState, hzero]
    rw [hstateZero] at hμpos
    norm_num at hμpos
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero G.degree_le hcoeff

theorem PolynomialGraph.realPoly_degree_eq_of_interiorState {d b Q : ℕ}
    (G : PolynomialGraph d) (hb : 2 ≤ b) (w : Polynomial ℤ)
    (hstate : InteriorState b
      (((G.normalizedTopState Q w : ℚ) : ℝ))) :
    G.realPoly.natDegree = d := by
  have hdegree := G.natDegree_eq_of_interiorState hb w hstate
  rw [PolynomialGraph.realPoly,
    Polynomial.natDegree_map_eq_of_injective Rat.cast_injective, hdegree]

/-- An integer polynomial witnessing a common scale for the difference of two
real graphs. -/
structure IntegralDifferenceCertificate (P Q : Polynomial ℝ) where
  scale : ℕ
  scale_pos : 0 < scale
  integralPoly : Polynomial ℤ
  certificate :
    integralPoly.map (algebraMap ℤ ℝ) = (scale : ℝ) • (P - Q)

namespace IntegralDifferenceCertificate

theorem eval_identity {P Q : Polynomial ℝ}
    (C : IntegralDifferenceCertificate P Q) (n : ℤ) :
    ((C.integralPoly.eval n : ℤ) : ℝ) =
      (C.scale : ℝ) * (P.eval (n : ℝ) - Q.eval (n : ℝ)) := by
  have h := congrArg (fun R : Polynomial ℝ => R.eval (n : ℝ)) C.certificate
  have hcert :
      (C.integralPoly.map (algebraMap ℤ ℝ)).eval (n : ℝ) =
        (C.scale : ℝ) * (P.eval (n : ℝ) - Q.eval (n : ℝ)) := by
    simpa only [Polynomial.eval_smul, Polynomial.eval_sub, smul_eq_mul,
      Int.cast_natCast] using h
  calc
    ((C.integralPoly.eval n : ℤ) : ℝ) =
        (C.integralPoly.map (algebraMap ℤ ℝ)).eval (n : ℝ) := by
      exact (Polynomial.eval_map_apply (p := C.integralPoly)
        (f := algebraMap ℤ ℝ) n).symm
    _ = _ := hcert

end IntegralDifferenceCertificate

/-! ## Leading-coefficient denominator band -/

/-- Dividing a rational number by a positive integer cannot remove any prime
factor from its reduced denominator. -/
theorem rat_den_dvd_den_div_nat (x : ℚ) {k : ℕ} (hk : 0 < k) :
    x.den ∣ (x / (k : ℚ)).den := by
  let y : ℚ := x / (k : ℚ)
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hy : y * (k : ℚ) = x := by
    dsimp [y]
    exact div_mul_cancel₀ x hkq
  have hden := Rat.mul_den_dvd y (k : ℚ)
  simpa only [hy, Rat.den_natCast, mul_one] using hden

/-- Arithmetic denominator estimate used in the high-frequency cell count.
If `(r,q)=1`, then the reduced denominator of `Ar/(qk)` is at least
`q/|A|`.  The application takes `k=d!`. -/
theorem leadingMonomial_den_lower {A r : ℤ} {q k : ℕ}
    (hA : A ≠ 0) (hq : 0 < q) (hk : 0 < k)
    (hrq : Nat.Coprime r.natAbs q) :
    q / A.natAbs ≤
      ((((A * r : ℤ) : ℚ) / (q : ℚ)) / (k : ℚ)).den := by
  let g : ℕ := Nat.gcd q (A.natAbs * r.natAbs)
  have hgq : g ∣ q := by
    exact Nat.gcd_dvd_left _ _
  have hgar : g ∣ A.natAbs * r.natAbs := by
    exact Nat.gcd_dvd_right _ _
  have hrg : Nat.Coprime r.natAbs g :=
    Nat.Coprime.of_dvd_right hgq hrq
  have hga : g ∣ A.natAbs :=
    hrg.symm.dvd_of_dvd_mul_right hgar
  have hApos : 0 < A.natAbs := Int.natAbs_pos.mpr hA
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hq
  have hgle : g ≤ A.natAbs := Nat.le_of_dvd hApos hga
  let y : ℚ := ((A * r : ℤ) : ℚ) / (q : ℚ)
  have hyDivInt : y = Rat.divInt (A * r) (q : ℤ) := by
    rw [Rat.divInt_eq_div]
    rfl
  have hdenY : y.den = q / g := by
    rw [hyDivInt, Rat.den_divInt]
    have hqInt : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    rw [if_neg hqInt]
    rw [Int.gcd_eq_natAbs_gcd_natAbs]
    simp only [Int.natAbs_natCast, Int.natAbs_mul, g]
  have hlowerY : q / A.natAbs ≤ y.den := by
    rw [hdenY]
    exact Nat.div_le_div_left hgle hgpos
  have hdiv : y.den ∣ (y / (k : ℚ)).den :=
    rat_den_dvd_den_div_nat y hk
  have hdenle : y.den ≤ (y / (k : ℚ)).den :=
    Nat.le_of_dvd (Rat.den_pos _) hdiv
  exact hlowerY.trans (by simpa only [y] using hdenle)

/-- The reduced denominator of the leading monomial coefficient of an
interior graph is bounded below by the reduced state denominator divided by
the fixed integral top scale. -/
theorem PolynomialGraph.leadingCoeff_den_lower_of_interiorState
    {d b Q : ℕ} (G : PolynomialGraph d) (hb : 2 ≤ b)
    (hQ : 0 < Q) (w : Polynomial ℤ) (hw : 0 < w.coeff d)
    (hstate : InteriorState b
      (((G.normalizedTopState Q w : ℚ) : ℝ))) :
    (G.normalizedTopState Q w).den /
        (Q * (w.coeff d).natAbs) ≤ G.poly.leadingCoeff.den := by
  let μ : ℚ := G.normalizedTopState Q w
  let A : ℤ := (Q : ℤ) * w.coeff d
  have hA : A ≠ 0 := by
    dsimp only [A]
    exact mul_ne_zero (by exact_mod_cast hQ.ne') hw.ne'
  have hdegree : G.poly.natDegree = d :=
    G.natDegree_eq_of_interiorState hb w hstate
  have hAq : (Q : ℚ) * (w.coeff d : ℚ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hQ.ne') (by exact_mod_cast hw.ne')
  have htop :
      (Q : ℚ) * (w.coeff d : ℚ) * μ = G.poly.coeff d := by
    dsimp only [μ, PolynomialGraph.normalizedTopState, topState]
    field_simp
  have hfrac :
      (((A * μ.num : ℤ) : ℚ) / (μ.den : ℚ)) =
        G.poly.leadingCoeff := by
    calc
      (((A * μ.num : ℤ) : ℚ) / (μ.den : ℚ)) =
          ((Q : ℚ) * (w.coeff d : ℚ)) *
            ((μ.num : ℚ) / (μ.den : ℚ)) := by
        dsimp only [A]
        push_cast
        ring
      _ = ((Q : ℚ) * (w.coeff d : ℚ)) * μ := by
        rw [μ.num_div_den]
      _ = G.poly.coeff d := htop
      _ = G.poly.leadingCoeff := by
        rw [← Polynomial.coeff_natDegree, hdegree]
  have hlower := leadingMonomial_den_lower
    (A := A) (r := μ.num) (q := μ.den) (k := 1)
    hA μ.den_pos (by omega) μ.reduced
  have hAabs : A.natAbs = Q * (w.coeff d).natAbs := by
    dsimp only [A]
    rw [Int.natAbs_mul, Int.natAbs_natCast]
  rw [hAabs] at hlower
  simpa only [Nat.cast_one, div_one, hfrac] using hlower

/-- Integer-valued samples of a graph in one natural interval form a subset
of the canonical integral fibre. -/
theorem PolynomialGraph.samples_subset_integralFiber {d A H : ℕ}
    (G : PolynomialGraph d) (samples : Finset ℕ)
    (hsamples : ∀ n ∈ samples, A ≤ n ∧ n ≤ A + H)
    (hvalues : ∀ n ∈ samples, ∃ z : ℤ,
      G.poly.eval (n : ℚ) = (z : ℚ)) :
    samples ⊆ integralFiber G.poly A H := by
  intro n hn
  rw [mem_integralFiber_iff]
  exact ⟨(hsamples n hn).1, (hsamples n hn).2,
    hvalues n hn⟩

/-- Integral-fibre count for an interior graph, with the state denominator
lower bound substituted explicitly. -/
theorem PolynomialGraph.interiorSamples_card_bound
    {d b Q A H : ℕ} (hd : 0 < d)
    (G : PolynomialGraph d) (hb : 2 ≤ b) (hQ : 0 < Q)
    (w : Polynomial ℤ) (hw : 0 < w.coeff d)
    (hstate : InteriorState b
      (((G.normalizedTopState Q w : ℚ) : ℝ)))
    (samples : Finset ℕ)
    (hsamples : ∀ n ∈ samples, A ≤ n ∧ n ≤ A + H)
    (hvalues : ∀ n ∈ samples, ∃ z : ℤ,
      G.poly.eval (n : ℚ) = (z : ℚ))
    (hquot : 0 < (G.normalizedTopState Q w).den /
      (Q * (w.coeff d).natAbs)) :
    (samples.card : ℝ) ≤ d + d * H /
      (((((G.normalizedTopState Q w).den /
        (Q * (w.coeff d).natAbs) : ℕ) : ℝ)) ^
          ((vandermondeExponent d : ℝ)⁻¹)) := by
  let q0 := G.poly.leadingCoeff.den
  let qlower := (G.normalizedTopState Q w).den /
    (Q * (w.coeff d).natAbs)
  have hdegree : G.poly.natDegree = d :=
    G.natDegree_eq_of_interiorState hb w hstate
  have hsubset := G.samples_subset_integralFiber samples hsamples hvalues
  have hcardNat : samples.card ≤ (integralFiber G.poly A H).card :=
    Finset.card_le_card hsubset
  have hcardReal : (samples.card : ℝ) ≤
      ((integralFiber G.poly A H).card : ℝ) := by exact_mod_cast hcardNat
  have hfibre := integralFiber_card_bound hd G.poly hdegree A H
  have hqLower : qlower ≤ q0 := by
    exact G.leadingCoeff_den_lower_of_interiorState hb hQ w hw hstate
  have hqLowerReal : (qlower : ℝ) ≤ q0 := by exact_mod_cast hqLower
  have hscaleLower :
      (qlower : ℝ) ^ ((vandermondeExponent d : ℝ)⁻¹) ≤
        leadingDenominatorScale G.poly d := by
    unfold leadingDenominatorScale
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hqLowerReal (by positivity)
  have hleftPos : (0 : ℝ) <
      (qlower : ℝ) ^ ((vandermondeExponent d : ℝ)⁻¹) := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast hquot) _
  have hscalePos := leadingDenominatorScale_pos G.poly d
  have hdivision :
      (d : ℝ) * H / leadingDenominatorScale G.poly d ≤
        (d : ℝ) * H /
          ((qlower : ℝ) ^ ((vandermondeExponent d : ℝ)⁻¹)) := by
    apply (div_le_div_iff₀ hscalePos hleftPos).2
    exact mul_le_mul_of_nonneg_left hscaleLower (by positivity)
  exact hcardReal.trans (hfibre.trans (by
    linarith))

/-- The product of two graph denominators gives a genuine integral difference
certificate. -/
def polynomialGraphDifferenceCertificate {d : ℕ}
    (G H : PolynomialGraph d) :
    IntegralDifferenceCertificate G.realPoly H.realPoly where
  scale := G.denominator * H.denominator
  scale_pos := Nat.mul_pos G.denominator_pos H.denominator_pos
  integralPoly :=
    (H.denominator : ℤ) • G.integralPoly -
      (G.denominator : ℤ) • H.integralPoly
  certificate := by
    ext n
    have hGq := congrArg (fun P : Polynomial ℚ => P.coeff n) G.certificate
    have hHq := congrArg (fun P : Polynomial ℚ => P.coeff n) H.certificate
    simp only [Polynomial.coeff_map, Polynomial.coeff_smul, smul_eq_mul]
      at hGq hHq
    have hGr :
        (G.integralPoly.coeff n : ℝ) =
          (G.denominator : ℝ) * (G.poly.coeff n : ℝ) := by
      exact_mod_cast hGq
    have hHr :
        (H.integralPoly.coeff n : ℝ) =
          (H.denominator : ℝ) * (H.poly.coeff n : ℝ) := by
      exact_mod_cast hHq
    simp only [Polynomial.coeff_map, Polynomial.coeff_sub,
      Polynomial.coeff_smul, smul_eq_mul, PolynomialGraph.realPoly]
    push_cast
    change
      (H.denominator : ℝ) * (G.integralPoly.coeff n : ℝ) -
          (G.denominator : ℝ) * (H.integralPoly.coeff n : ℝ) =
        (G.denominator : ℝ) * (H.denominator : ℝ) *
          ((G.poly.coeff n : ℝ) - (H.poly.coeff n : ℝ))
    rw [hGr, hHr]
    ring

/-- Formula label `eq:graphden` for a difference graph: two individual
`W^s` certificates combine to a `W^(2s)` certificate. -/
theorem polynomialGraphDifference_scale_le {d W : ℕ}
    (G H : PolynomialGraph d)
    (hG : G.denominator ≤ W ^ vandermondeExponent d)
    (hH : H.denominator ≤ W ^ vandermondeExponent d) :
    (polynomialGraphDifferenceCertificate G H).scale ≤
      W ^ (2 * vandermondeExponent d) := by
  change G.denominator * H.denominator ≤ _
  calc
    G.denominator * H.denominator ≤
        W ^ vandermondeExponent d * W ^ vandermondeExponent d :=
      Nat.mul_le_mul hG hH
    _ = W ^ (2 * vandermondeExponent d) := by
      rw [← pow_add]
      congr 1
      omega

/-- Evaluation form of `eq:divisiblegraphs` for the automatically constructed
difference certificate after a common continuation. -/
theorem transformedDifference_eval_dvd {d : ℕ}
    (G H : PolynomialGraph d) (b Q : ℕ) (w : Polynomial ℤ)
    (hwdeg : w.natDegree ≤ d) (gaps : Erdos260.GapWord) (n : ℤ) :
    (b : ℤ) ^ Erdos260.GapWord.span gaps ∣
      (polynomialGraphDifferenceCertificate
        (G.transformWord b Q w hwdeg gaps)
        (H.transformWord b Q w hwdeg gaps)).integralPoly.eval n := by
  obtain ⟨K, hfactor⟩ :=
    G.exists_differenceIntegral_transformWord_pow_factor H b Q w hwdeg gaps
  change (b : ℤ) ^ Erdos260.GapWord.span gaps ∣
    (PolynomialGraph.differenceIntegral
      (G.transformWord b Q w hwdeg gaps)
      (H.transformWord b Q w hwdeg gaps)).eval n
  rw [hfactor, Polynomial.eval_smul, smul_eq_mul]
  exact dvd_mul_right _ _

/-- Formula label `eq:divisiblegraphs`. -/
theorem eq_divisiblegraphs {d : ℕ}
    (G H : PolynomialGraph d) (b Q : ℕ) (w : Polynomial ℤ)
    (hwdeg : w.natDegree ≤ d) (gaps : Erdos260.GapWord) (n : ℤ) :
    (b : ℤ) ^ Erdos260.GapWord.span gaps ∣
      (polynomialGraphDifferenceCertificate
        (G.transformWord b Q w hwdeg gaps)
        (H.transformWord b Q w hwdeg gaps)).integralPoly.eval n :=
  transformedDifference_eval_dvd G H b Q w hwdeg gaps n

/-- Explicit sampling envelope used in the coalescence inequality. -/
def samplingEnvelope (d H : ℕ) (samples : Finset ℕ) (Y : ℝ) : ℝ :=
  samplingConstant d * Y * (1 + (H : ℝ) / samples.card) ^ d

/-- The sampling envelope is nonnegative whenever its height bound is. -/
theorem samplingEnvelope_nonneg (d H : ℕ) (samples : Finset ℕ)
    {Y : ℝ} (hY : 0 ≤ Y) :
    0 ≤ samplingEnvelope d H samples Y := by
  unfold samplingEnvelope
  exact mul_nonneg
    (mul_nonneg (samplingConstant_pos d).le hY)
    (pow_nonneg
      (add_nonneg zero_le_one
        (div_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg samples.card))) d)

/-- Replacing an actual high-frequency sample count by a uniform lower
cutoff only enlarges the sampling envelope. -/
theorem samplingEnvelope_le_of_card_ge {d H U : ℕ}
    (samples : Finset ℕ) {Y : ℝ} (hY : 0 ≤ Y)
    (hU : 0 < U) (hcard : U ≤ samples.card) :
    samplingEnvelope d H samples Y ≤
      samplingConstant d * Y * (1 + (H : ℝ) / U) ^ d := by
  have hcardPos : 0 < samples.card := hU.trans_le hcard
  have hdiv : (H : ℝ) / samples.card ≤ (H : ℝ) / U := by
    apply div_le_div_of_nonneg_left (by positivity)
    · exact_mod_cast hU
    · exact_mod_cast hcard
  unfold samplingEnvelope
  gcongr
  exact mul_nonneg (samplingConstant_pos d).le hY

/-- High-frequency coalescence: two degree-`d` graphs with sufficiently many
bounded samples, a common integer difference certificate, and `b^F`
divisibility throughout the sample interval must coincide once the explicit
sampling envelope is smaller than `b^F`.

This is the proof-bearing core of `lem:coalescence` and
`eq:divisiblegraphs`. -/
theorem highFrequency_coalescence {d A H b F : ℕ}
    (hH : d ≤ H) (_hb : 2 ≤ b)
    (P Q : Polynomial ℝ) (hPdeg : P.natDegree ≤ d)
    (hQdeg : Q.natDegree ≤ d)
    (samplesP samplesQ : Finset ℕ)
    (hcardP : 2 * d + 1 ≤ samplesP.card)
    (hcardQ : 2 * d + 1 ≤ samplesQ.card)
    (hsamplesP : ∀ n ∈ samplesP, A ≤ n ∧ n ≤ A + H)
    (hsamplesQ : ∀ n ∈ samplesQ, A ≤ n ∧ n ≤ A + H)
    {YP YQ : ℝ} (hYP : 0 ≤ YP) (hYQ : 0 ≤ YQ)
    (hvaluesP : ∀ n ∈ samplesP, |P.eval (n : ℝ)| ≤ YP)
    (hvaluesQ : ∀ n ∈ samplesQ, |Q.eval (n : ℝ)| ≤ YQ)
    (C : IntegralDifferenceCertificate P Q)
    (hdiv : ∀ n : ℕ, A ≤ n → n ≤ A + H →
      (b : ℤ) ^ F ∣ C.integralPoly.eval (n : ℤ))
    (hsmall :
      (C.scale : ℝ) *
          (samplingEnvelope d H samplesP YP +
            samplingEnvelope d H samplesQ YQ) <
        (b : ℝ) ^ F) :
    P = Q := by
  have heval_eq (i : Fin (d + 1)) :
      P.eval ((A + (i : ℕ) : ℕ) : ℝ) =
        Q.eval ((A + (i : ℕ) : ℕ) : ℝ) := by
    let n : ℕ := A + (i : ℕ)
    have hi : (i : ℕ) ≤ d := Nat.le_of_lt_succ i.isLt
    have hnlow : A ≤ n := by simp only [n, Nat.le_add_right]
    have hnhigh : n ≤ A + H := by dsimp [n]; omega
    have hzbounds : (A : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ A + H := by
      constructor <;> exact_mod_cast (by assumption)
    have hPbound : |P.eval (n : ℝ)| ≤ samplingEnvelope d H samplesP YP := by
      exact polynomial_sampling_finset P hPdeg samplesP hcardP hsamplesP
        hYP hvaluesP hzbounds
    have hQbound : |Q.eval (n : ℝ)| ≤ samplingEnvelope d H samplesQ YQ := by
      exact polynomial_sampling_finset Q hQdeg samplesQ hcardQ hsamplesQ
        hYQ hvaluesQ hzbounds
    have hdiff : |P.eval (n : ℝ) - Q.eval (n : ℝ)| ≤
        samplingEnvelope d H samplesP YP +
          samplingEnvelope d H samplesQ YQ := by
      exact (abs_sub _ _).trans (add_le_add hPbound hQbound)
    have hcert := C.eval_identity (n : ℤ)
    have hcert_nat :
        ((C.integralPoly.eval (n : ℤ) : ℤ) : ℝ) =
          (C.scale : ℝ) * (P.eval (n : ℝ) - Q.eval (n : ℝ)) := by
      simpa only [Int.cast_natCast] using hcert
    have hscaled :
        |((C.integralPoly.eval (n : ℤ) : ℤ) : ℝ)| < (b : ℝ) ^ F := by
      rw [hcert_nat, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ C.scale)]
      exact (mul_le_mul_of_nonneg_left hdiff (by positivity)).trans_lt hsmall
    have hint_zero : C.integralPoly.eval (n : ℤ) = 0 :=
      int_eq_zero_of_pow_dvd_of_cast_abs_lt
        (hdiv n hnlow hnhigh) hscaled
    have hscale_ne : (C.scale : ℝ) ≠ 0 := by
      exact_mod_cast C.scale_pos.ne'
    have hdiff_zero : P.eval (n : ℝ) - Q.eval (n : ℝ) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hscale_ne
      rw [← hcert_nat, hint_zero]
      norm_num
    exact sub_eq_zero.mp hdiff_zero
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
    (s := (Finset.univ : Finset (Fin (d + 1))))
    (v := fun i : Fin (d + 1) => (A + (i : ℕ) : ℝ))
  · intro i _ j _ hij
    change (A : ℝ) + (i : ℝ) = (A : ℝ) + (j : ℝ) at hij
    have hvalReal : (i : ℝ) = (j : ℝ) := add_left_cancel hij
    exact Fin.ext (by exact_mod_cast hvalReal)
  · by_cases hPzero : P = 0
    · simp [hPzero]
    · rw [Finset.card_fin]
      exact (Polynomial.natDegree_lt_iff_degree_lt hPzero).mp
        (hPdeg.trans_lt (Nat.lt_succ_self d))
  · by_cases hQzero : Q = 0
    · simp [hQzero]
    · rw [Finset.card_fin]
      exact (Polynomial.natDegree_lt_iff_degree_lt hQzero).mp
        (hQdeg.trans_lt (Nat.lt_succ_self d))
  · intro i hi
    simpa only [Nat.cast_add] using heval_eq i

/-- Manuscript lemma `lem:coalescence` with its graph certificate and
`b^F` divisibility generated internally from the two locked graphs and their
common continuation. -/
theorem lem_coalescence {d A Hlen b F Q : ℕ}
    (hH : d ≤ Hlen) (hb : 2 ≤ b)
    (G₁ G₂ : PolynomialGraph d)
    (w : Polynomial ℤ) (hwdeg : w.natDegree ≤ d)
    (gaps : Erdos260.GapWord)
    (hspan : Erdos260.GapWord.span gaps = F)
    (samples₁ samples₂ : Finset ℕ)
    (hcard₁ : 2 * d + 1 ≤ samples₁.card)
    (hcard₂ : 2 * d + 1 ≤ samples₂.card)
    (hsamples₁ : ∀ n ∈ samples₁, A ≤ n ∧ n ≤ A + Hlen)
    (hsamples₂ : ∀ n ∈ samples₂, A ≤ n ∧ n ≤ A + Hlen)
    {Y₁ Y₂ : ℝ} (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂)
    (hvalues₁ : ∀ n ∈ samples₁,
      |((G₁.transformWord b Q w hwdeg gaps).realPoly).eval (n : ℝ)| ≤ Y₁)
    (hvalues₂ : ∀ n ∈ samples₂,
      |((G₂.transformWord b Q w hwdeg gaps).realPoly).eval (n : ℝ)| ≤ Y₂)
    (hsmall :
      ((polynomialGraphDifferenceCertificate
        (G₁.transformWord b Q w hwdeg gaps)
        (G₂.transformWord b Q w hwdeg gaps)).scale : ℝ) *
          (samplingEnvelope d Hlen samples₁ Y₁ +
            samplingEnvelope d Hlen samples₂ Y₂) <
        (b : ℝ) ^ F) :
    G₁.poly = G₂.poly := by
  let T₁ := G₁.transformWord b Q w hwdeg gaps
  let T₂ := G₂.transformWord b Q w hwdeg gaps
  let C := polynomialGraphDifferenceCertificate T₁ T₂
  have hdiv : ∀ n : ℕ, A ≤ n → n ≤ A + Hlen →
      (b : ℤ) ^ F ∣ C.integralPoly.eval (n : ℤ) := by
    intro n hnlow hnhigh
    rw [← hspan]
    exact transformedDifference_eval_dvd G₁ G₂ b Q w hwdeg gaps n
  have hreal : T₁.realPoly = T₂.realPoly :=
    highFrequency_coalescence hH hb T₁.realPoly T₂.realPoly
      T₁.realPoly_degree_le T₂.realPoly_degree_le
      samples₁ samples₂ hcard₁ hcard₂ hsamples₁ hsamples₂
      hY₁ hY₂ hvalues₁ hvalues₂ C hdiv (by simpa [C, T₁, T₂] using hsmall)
  have hpoly : T₁.poly = T₂.poly := by
    apply Polynomial.map_injective (algebraMap ℚ ℝ) Rat.cast_injective
    exact hreal
  exact G₁.transformWord_poly_injective hb w hwdeg gaps G₂ (by
    simpa [T₁, T₂] using hpoly)

/-! ## Actual stabilized interior branches of locked window fibres -/

/-- Occurrences in a locked prefix fibre with the requested amount of genuine
interior span after the locking prefix. -/
noncomputable def interiorEligibleIndices (D : CarrySeries)
    (N W m bound : ℕ) (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ) : Finset ℕ :=
  (realizedPrefixIndices D N W m bound pfx).filter fun k =>
    threshold < interiorSpanAlong D.base
      (postLockingWord D.positiveEnumeration k m bound)
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))

/-- Denominator absorption data chosen once for the locked graph, hence shared
by all actual occurrences in its prefix fibre. -/
noncomputable def lockedTopStateAbsorption (D : CarrySeries)
    (G : PolynomialGraph D.weight.natDegree) :
    InteriorNumeratorOrbit.TopStateAbsorptionData D.base
      (G.normalizedTopState D.denominator D.weight) :=
  InteriorNumeratorOrbit.chosenTopStateAbsorption D.base D.base_ge_two
    (G.normalizedTopState D.denominator D.weight)

noncomputable def actualInteriorTrajectory (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    Erdos260.GapWord :=
  interiorTrajectory D.base
    (postLockingWord D.positiveEnumeration k.1 m bound)
    (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))

noncomputable def actualInteriorAbsorptionPrefix (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    Erdos260.GapWord :=
  denominatorAbsorptionPrefix
    (actualInteriorTrajectory D pfx G threshold k)
    (lockedTopStateAbsorption D G).exponent

noncomputable def actualStabilizedInteriorWord (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    Erdos260.GapWord :=
  denominatorStabilizedSuffix
    (actualInteriorTrajectory D pfx G threshold k)
    (lockedTopStateAbsorption D G).exponent

noncomputable def actualStabilizedInteriorGraph (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    PolynomialGraph D.weight.natDegree :=
  G.transformWord D.base D.denominator D.weight le_rfl
    (actualInteriorAbsorptionPrefix D pfx G threshold k)

/-- The genuine long interior branch produces its stabilized coprime
numerator orbit without any orbit or recurrence supplied by the caller. -/
noncomputable def actualInteriorOrbit (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    InteriorNumeratorOrbit D.base
      ((actualStabilizedInteriorGraph D pfx G threshold k).normalizedTopState
        D.denominator D.weight).den := by
  let post := postLockingWord D.positiveEnumeration k.1 m bound
  let data := lockedTopStateAbsorption D G
  have hkRealized : k.1 ∈ realizedPrefixIndices D N W m bound pfx :=
    (Finset.mem_filter.mp k.2).1
  have hspan : threshold < interiorSpanAlong D.base post
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)) := by
    simpa only [post] using (Finset.mem_filter.mp k.2).2
  have hpositive : Erdos260.GapWord.Positive post :=
    postLockingWord_positive D.positiveEnumeration k.1 m bound
  have hcap : ∀ g ∈ post, g ≤ cap :=
    postLockingWord_gap_le D hgeom (Finset.mem_filter.mp hkRealized).1
  have hlong : data.exponent + cap < interiorSpanAlong D.base post
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)) := by
    have he := data.exponent_le_log
    omega
  have hA : (D.denominator : ℚ) *
      (D.weight.coeff D.weight.natDegree : ℚ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast D.denominator_pos.ne')
      (by exact_mod_cast hw.ne')
  have O := InteriorNumeratorOrbit.ofLongInteriorTrajectory G D.base
    D.denominator data.exponent
    data.coprimePart cap D.base_ge_two D.weight le_rfl hA post
    hpositive hcap data.coprime_base data.residual_den_dvd hlong
  simpa only [post, data, actualStabilizedInteriorGraph,
    actualInteriorAbsorptionPrefix, actualInteriorTrajectory,
    lockedTopStateAbsorption] using O

@[simp]
theorem actualInteriorOrbit_gaps (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    (actualInteriorOrbit D hw hgeom pfx G threshold hthreshold k).gaps =
      actualStabilizedInteriorWord D pfx G threshold k := by
  rfl

/-- The actual all-interior trajectory inherits positivity from the support
enumeration. -/
theorem actualInteriorTrajectory_positive (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    Erdos260.GapWord.Positive
      (actualInteriorTrajectory D pfx G threshold k) := by
  exact interiorTrajectory_positive
    (postLockingWord_positive D.positiveEnumeration k.1 m bound) _

/-- Every gap retained by the actual all-interior trajectory satisfies the
window geometry cap. -/
theorem actualInteriorTrajectory_gap_le (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    ∀ g ∈ actualInteriorTrajectory D pfx G threshold k, g ≤ cap := by
  intro g hg
  have hkRealized : k.1 ∈ realizedPrefixIndices D N W m bound pfx :=
    (Finset.mem_filter.mp k.2).1
  have hpost := postLockingWord_gap_le D hgeom
    (Finset.mem_filter.mp hkRealized).1
  apply hpost g
  exact (interiorTrajectory_isPrefix D.base
    (postLockingWord D.positiveEnumeration k.1 m bound)
    (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))).mem hg

/-- Actual all-interior trajectories in one locked prefix fibre are
comparable, because every positive interior successor gap is unique. -/
theorem actualInteriorTrajectory_prefix_or_prefix (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (left right : ↥(interiorEligibleIndices
      D N W m bound pfx G threshold)) :
    (actualInteriorTrajectory D pfx G threshold left).IsPrefix
        (actualInteriorTrajectory D pfx G threshold right) ∨
      (actualInteriorTrajectory D pfx G threshold right).IsPrefix
        (actualInteriorTrajectory D pfx G threshold left) := by
  exact interiorTrajectory_prefix_or_prefix D.base_ge_two
    (postLockingWord D.positiveEnumeration left.1 m bound)
    (postLockingWord D.positiveEnumeration right.1 m bound)
    (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
    (postLockingWord_positive D.positiveEnumeration left.1 m bound)
    (postLockingWord_positive D.positiveEnumeration right.1 m bound)

/-- Every eligible trajectory reaches the graph's canonical denominator
absorption exponent under the explicit threshold budget. -/
theorem lockedAbsorptionExponent_lt_actualInteriorTrajectory_span
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    (lockedTopStateAbsorption D G).exponent <
      Erdos260.GapWord.span
        (actualInteriorTrajectory D pfx G threshold k) := by
  let post := postLockingWord D.positiveEnumeration k.1 m bound
  let μ : ℝ :=
    (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
  let trajectory := actualInteriorTrajectory D pfx G threshold k
  have hkRealized : k.1 ∈ realizedPrefixIndices D N W m bound pfx :=
    (Finset.mem_filter.mp k.2).1
  have hinterior : threshold < interiorSpanAlong D.base post μ := by
    simpa only [post, μ] using (Finset.mem_filter.mp k.2).2
  have hloss := interiorSpanAlong_le_trajectory_add_cap D.base_ge_two
    (postLockingWord_positive D.positiveEnumeration k.1 m bound)
    (postLockingWord_gap_le D hgeom (Finset.mem_filter.mp hkRealized).1) μ
  have he : (lockedTopStateAbsorption D G).exponent ≤
      Nat.log 2 (G.normalizedTopState D.denominator D.weight).den :=
    (lockedTopStateAbsorption D G).exponent_le_log
  change interiorSpanAlong D.base post μ ≤
      Erdos260.GapWord.span trajectory + cap at hloss
  change (lockedTopStateAbsorption D G).exponent <
    Erdos260.GapWord.span trajectory
  omega

/-- Denominator absorption is a common, graph-determined prefix throughout
one sufficiently long locked interior fibre. -/
theorem actualInteriorAbsorptionPrefix_eq (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (left right : ↥(interiorEligibleIndices
      D N W m bound pfx G threshold)) :
    actualInteriorAbsorptionPrefix D pfx G threshold left =
      actualInteriorAbsorptionPrefix D pfx G threshold right := by
  let leftTrajectory := actualInteriorTrajectory D pfx G threshold left
  let rightTrajectory := actualInteriorTrajectory D pfx G threshold right
  let e := (lockedTopStateAbsorption D G).exponent
  have hleftCross : e < Erdos260.GapWord.span leftTrajectory := by
    simpa only [leftTrajectory, e] using
      lockedAbsorptionExponent_lt_actualInteriorTrajectory_span
        D hgeom pfx G threshold hthreshold left
  have hrightCross : e < Erdos260.GapWord.span rightTrajectory := by
    simpa only [rightTrajectory, e] using
      lockedAbsorptionExponent_lt_actualInteriorTrajectory_span
        D hgeom pfx G threshold hthreshold right
  have hleftNe : leftTrajectory ≠ [] := by
    intro hzero
    rw [hzero] at hleftCross
    simp [Erdos260.GapWord.span] at hleftCross
  have hrightNe : rightTrajectory ≠ [] := by
    intro hzero
    rw [hzero] at hrightCross
    simp [Erdos260.GapWord.span] at hrightCross
  rcases actualInteriorTrajectory_prefix_or_prefix
      D pfx G threshold left right with hpref | hpref
  · simpa only [actualInteriorAbsorptionPrefix, denominatorAbsorptionPrefix,
      leftTrajectory, rightTrajectory, e] using
      firstPrefixAtLeast_eq_of_prefix hpref hleftNe hleftCross.le
  · symm
    simpa only [actualInteriorAbsorptionPrefix, denominatorAbsorptionPrefix,
      leftTrajectory, rightTrajectory, e] using
      firstPrefixAtLeast_eq_of_prefix hpref hrightNe hrightCross.le

theorem actualStabilizedInteriorGraph_eq (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (left right : ↥(interiorEligibleIndices
      D N W m bound pfx G threshold)) :
    actualStabilizedInteriorGraph D pfx G threshold left =
      actualStabilizedInteriorGraph D pfx G threshold right := by
  unfold actualStabilizedInteriorGraph
  rw [actualInteriorAbsorptionPrefix_eq D hgeom pfx G threshold
    hthreshold left right]

/-- Stabilized words in one locked fibre remain comparable after the common
denominator-absorption prefix is removed. -/
theorem actualStabilizedInteriorWord_prefix_or_prefix (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (left right : ↥(interiorEligibleIndices
      D N W m bound pfx G threshold)) :
    (actualStabilizedInteriorWord D pfx G threshold left).IsPrefix
        (actualStabilizedInteriorWord D pfx G threshold right) ∨
      (actualStabilizedInteriorWord D pfx G threshold right).IsPrefix
        (actualStabilizedInteriorWord D pfx G threshold left) := by
  have habsorb := actualInteriorAbsorptionPrefix_eq
    D hgeom pfx G threshold hthreshold left right
  rcases actualInteriorTrajectory_prefix_or_prefix
      D pfx G threshold left right with hpref | hpref
  · left
    change (actualInteriorTrajectory D pfx G threshold left).drop
          (actualInteriorAbsorptionPrefix D pfx G threshold left).length <+:
        (actualInteriorTrajectory D pfx G threshold right).drop
          (actualInteriorAbsorptionPrefix D pfx G threshold right).length
    rw [← habsorb]
    exact hpref.drop _
  · right
    change (actualInteriorTrajectory D pfx G threshold right).drop
          (actualInteriorAbsorptionPrefix D pfx G threshold right).length <+:
        (actualInteriorTrajectory D pfx G threshold left).drop
          (actualInteriorAbsorptionPrefix D pfx G threshold left).length
    rw [habsorb]
    exact hpref.drop _

theorem actualStabilizedInteriorWord_positive (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    Erdos260.GapWord.Positive
      (actualStabilizedInteriorWord D pfx G threshold k) := by
  exact denominatorStabilizedSuffix_positive
    (actualInteriorTrajectory_positive D pfx G threshold k) _

theorem actualStabilizedInteriorWord_gap_le (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    ∀ g ∈ actualStabilizedInteriorWord D pfx G threshold k, g ≤ cap := by
  intro g hg
  apply actualInteriorTrajectory_gap_le D hgeom pfx G threshold k g
  exact List.mem_of_mem_drop hg

theorem actualStabilizedInteriorWord_length_le (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    (actualStabilizedInteriorWord D pfx G threshold k).length ≤ m := by
  calc
    (actualStabilizedInteriorWord D pfx G threshold k).length ≤
        (actualInteriorTrajectory D pfx G threshold k).length := by
      simp [actualStabilizedInteriorWord, denominatorStabilizedSuffix]
    _ ≤ (postLockingWord D.positiveEnumeration k.1 m bound).length :=
      (interiorTrajectory_isPrefix D.base
        (postLockingWord D.positiveEnumeration k.1 m bound)
        (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))).length_le
    _ ≤ m := postLockingWord_length_le D.positiveEnumeration k.1 m bound

/-- After paying one transition gap and the denominator-absorption overshoot,
the stabilized word retains every explicitly budgeted amount of interior
span. -/
theorem actualStabilizedInteriorWord_span_gt (D : CarrySeries)
    {N W m cap bound reserve : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den +
          2 * cap + reserve ≤ threshold)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    reserve < Erdos260.GapWord.span
      (actualStabilizedInteriorWord D pfx G threshold k) := by
  let post := postLockingWord D.positiveEnumeration k.1 m bound
  let μ : ℝ :=
    (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
  let trajectory := interiorTrajectory D.base post μ
  let data := lockedTopStateAbsorption D G
  let pre := denominatorAbsorptionPrefix trajectory data.exponent
  let suffix := denominatorStabilizedSuffix trajectory data.exponent
  have hkRealized : k.1 ∈ realizedPrefixIndices D N W m bound pfx :=
    (Finset.mem_filter.mp k.2).1
  have hspan : threshold < interiorSpanAlong D.base post μ := by
    simpa only [post, μ] using (Finset.mem_filter.mp k.2).2
  have hpostPositive : Erdos260.GapWord.Positive post :=
    postLockingWord_positive D.positiveEnumeration k.1 m bound
  have hpostCap : ∀ g ∈ post, g ≤ cap :=
    postLockingWord_gap_le D hgeom (Finset.mem_filter.mp hkRealized).1
  have hloss := interiorSpanAlong_le_trajectory_add_cap D.base_ge_two
    hpostPositive hpostCap μ
  have htrajectoryCap : ∀ g ∈ trajectory, g ≤ cap := by
    intro g hg
    apply hpostCap g
    exact (interiorTrajectory_isPrefix D.base post μ).mem hg
  have hpre : Erdos260.GapWord.span pre ≤ data.exponent + cap := by
    exact denominatorAbsorptionPrefix_span_le_add trajectory data.exponent cap
      htrajectoryCap
  have hsplit : Erdos260.GapWord.span pre +
      Erdos260.GapWord.span suffix =
        Erdos260.GapWord.span trajectory := by
    have h := congrArg Erdos260.GapWord.span
      (denominatorAbsorptionPrefix_append_suffix trajectory data.exponent)
    simpa only [pre, suffix, Erdos260.GapWord.span, List.sum_append] using h
  have he : data.exponent ≤ Nat.log 2
      (G.normalizedTopState D.denominator D.weight).den :=
    data.exponent_le_log
  change reserve < Erdos260.GapWord.span suffix
  change interiorSpanAlong D.base post μ ≤
      Erdos260.GapWord.span trajectory + cap at hloss
  omega

/-- Removing the canonical denominator-absorption prefix loses at most its
logarithmic span and two bounded-gap overshoots.  Thus the original interior
span is controlled by the stabilized word used by the global census. -/
theorem actualInteriorSpan_le_stabilizedSpan_add (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    interiorSpanAlong D.base
        (postLockingWord D.positiveEnumeration k.1 m bound)
        (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ)) ≤
      Erdos260.GapWord.span
          (actualStabilizedInteriorWord D pfx G threshold k) +
        Nat.log 2 (G.normalizedTopState D.denominator D.weight).den +
          2 * cap := by
  let post := postLockingWord D.positiveEnumeration k.1 m bound
  let μ : ℝ :=
    (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
  let trajectory := interiorTrajectory D.base post μ
  let data := lockedTopStateAbsorption D G
  let pre := denominatorAbsorptionPrefix trajectory data.exponent
  let suffix := denominatorStabilizedSuffix trajectory data.exponent
  have hkRealized : k.1 ∈ realizedPrefixIndices D N W m bound pfx :=
    (Finset.mem_filter.mp k.2).1
  have hpostPositive : Erdos260.GapWord.Positive post :=
    postLockingWord_positive D.positiveEnumeration k.1 m bound
  have hpostCap : ∀ g ∈ post, g ≤ cap :=
    postLockingWord_gap_le D hgeom (Finset.mem_filter.mp hkRealized).1
  have hloss := interiorSpanAlong_le_trajectory_add_cap D.base_ge_two
    hpostPositive hpostCap μ
  have htrajectoryCap : ∀ g ∈ trajectory, g ≤ cap := by
    intro g hg
    apply hpostCap g
    exact (interiorTrajectory_isPrefix D.base post μ).mem hg
  have hpre : Erdos260.GapWord.span pre ≤ data.exponent + cap := by
    exact denominatorAbsorptionPrefix_span_le_add trajectory data.exponent cap
      htrajectoryCap
  have hsplit : Erdos260.GapWord.span pre +
      Erdos260.GapWord.span suffix =
        Erdos260.GapWord.span trajectory := by
    have h := congrArg Erdos260.GapWord.span
      (denominatorAbsorptionPrefix_append_suffix trajectory data.exponent)
    simpa only [pre, suffix, Erdos260.GapWord.span,
      List.sum_append] using h
  have he : data.exponent ≤ Nat.log 2
      (G.normalizedTopState D.denominator D.weight).den :=
    data.exponent_le_log
  change interiorSpanAlong D.base post μ ≤
      Erdos260.GapWord.span suffix +
        Nat.log 2 (G.normalizedTopState D.denominator D.weight).den +
          2 * cap
  change interiorSpanAlong D.base post μ ≤
      Erdos260.GapWord.span trajectory + cap at hloss
  omega

/-- The real stabilized branch, with its canonical denominator and mean-gap
bands, has the deterministic retained-block cover used in the interior
census. -/
theorem actualStabilizedInteriorWord_retained_cover (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold))
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + 2 * cap +
          24 * logarithmicBlockScale D.base 4
            (dyadicFloorBand
              ((actualStabilizedInteriorGraph D pfx G threshold k).normalizedTopState
                D.denominator D.weight).den) ≤ threshold) :
    let word := actualStabilizedInteriorWord D pfx G threshold k
    let q := ((actualStabilizedInteriorGraph D pfx G threshold k).normalizedTopState
      D.denominator D.weight).den
    let ell := logarithmicBlockScale D.base 4 (dyadicFloorBand q)
    let Z := meanGapBand word.span word.length
    word.span ≤ 4 * retainedGreedyBlockSpan word ell Z := by
  dsimp only
  let word := actualStabilizedInteriorWord D pfx G threshold k
  let q := ((actualStabilizedInteriorGraph D pfx G threshold k).normalizedTopState
    D.denominator D.weight).den
  let ell := logarithmicBlockScale D.base 4 (dyadicFloorBand q)
  let Z := meanGapBand word.span word.length
  have hthresholdOrbit : Nat.log 2
      (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold := by
    omega
  let O := actualInteriorOrbit D hw hgeom pfx G threshold hthresholdOrbit k
  have hOgaps : O.gaps = word := by
    dsimp only [O, word]
    exact actualInteriorOrbit_gaps D hw hgeom pfx G threshold
      hthresholdOrbit k
  have hDpos : 0 < dyadicFloorBand q := dyadicFloorBand_pos q
  have hell : 0 < ell := by
    exact logarithmicBlockScale_four_pos O.base_ge_two hDpos
  have hgap : ∀ g ∈ word, g ≤ ell := by
    have h := O.gap_le_logarithmicBlockScale
    rw [hOgaps] at h
    simpa only [ell, q] using h
  have hlong : 24 * ell ≤ word.span := by
    have h := actualStabilizedInteriorWord_span_gt D hgeom pfx G threshold
      hthreshold k
    simpa only [word] using h.le
  have hpositive : Erdos260.GapWord.Positive word := by
    simpa only [word] using
      (actualStabilizedInteriorWord_positive D pfx G threshold k)
  have hne : word ≠ [] := by
    intro hempty
    rw [hempty] at hlong
    simp [Erdos260.GapWord.span] at hlong
    omega
  have hlengthPos : 0 < word.length := List.length_pos_iff.mpr hne
  have hlengthSpan : word.length ≤ word.span := by
    exact List.length_le_sum_of_one_le word hpositive
  have hmean : Z * word.length ≤ word.span := by
    simpa only [Z] using
      (meanGapBand_span_bounds hlengthPos hlengthSpan).1
  exact retainedGreedyBlock_cover hell (meanGapBand_pos _ _) hgap hmean hlong

noncomputable def actualInteriorDenominator (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) : ℕ :=
  ((actualStabilizedInteriorGraph D pfx G threshold k).normalizedTopState
    D.denominator D.weight).den

theorem actualInteriorDenominator_eq (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (left right : ↥(interiorEligibleIndices
      D N W m bound pfx G threshold)) :
    actualInteriorDenominator D pfx G threshold left =
      actualInteriorDenominator D pfx G threshold right := by
  unfold actualInteriorDenominator
  rw [actualStabilizedInteriorGraph_eq D hgeom pfx G threshold
    hthreshold left right]

theorem actualInteriorDenominator_coprime_base (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    Nat.Coprime D.base (actualInteriorDenominator D pfx G threshold k) := by
  let trajectory := actualInteriorTrajectory D pfx G threshold k
  let data := lockedTopStateAbsorption D G
  let pre := actualInteriorAbsorptionPrefix D pfx G threshold k
  have htrajectorySpan : data.exponent ≤ Erdos260.GapWord.span trajectory := by
    exact (lockedAbsorptionExponent_lt_actualInteriorTrajectory_span
      D hgeom pfx G threshold hthreshold k).le
  have hpreSpan : data.exponent ≤ Erdos260.GapWord.span pre := by
    exact denominatorAbsorptionPrefix_span_ge trajectory data.exponent
      htrajectorySpan
  have hA : (D.denominator : ℚ) *
      (D.weight.coeff D.weight.natDegree : ℚ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast D.denominator_pos.ne')
      (by exact_mod_cast hw.ne')
  have hstate := G.normalizedTopState_transformWord D.base D.denominator
    D.weight le_rfl hA pre
  have hcop := topStateAlongRat_den_coprime_of_absorbed_prefix
    D.base data.exponent data.coprimePart
    (G.normalizedTopState D.denominator D.weight) pre hpreSpan
    data.coprime_base data.residual_den_dvd
  unfold actualInteriorDenominator actualStabilizedInteriorGraph
  rw [hstate]
  exact hcop

/-- Absorbing the base-primary part never enlarges the stabilized reduced
denominator.  The bound is quantitative because the absorption data use the
canonical coprime factor of the initial denominator. -/
theorem actualInteriorDenominator_le_initial (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    actualInteriorDenominator D pfx G threshold k ≤
      (G.normalizedTopState D.denominator D.weight).den := by
  let trajectory := actualInteriorTrajectory D pfx G threshold k
  let data := lockedTopStateAbsorption D G
  let pre := actualInteriorAbsorptionPrefix D pfx G threshold k
  have htrajectorySpan : data.exponent ≤ Erdos260.GapWord.span trajectory := by
    exact (lockedAbsorptionExponent_lt_actualInteriorTrajectory_span
      D hgeom pfx G threshold hthreshold k).le
  have hpreSpan : data.exponent ≤ Erdos260.GapWord.span pre := by
    exact denominatorAbsorptionPrefix_span_ge trajectory data.exponent
      htrajectorySpan
  have hA : (D.denominator : ℚ) *
      (D.weight.coeff D.weight.natDegree : ℚ) ≠ 0 := by
    have hlead : D.weight.coeff D.weight.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr D.weight_ne_zero
    exact mul_ne_zero (by exact_mod_cast D.denominator_pos.ne')
      (by exact_mod_cast hlead)
  have hstate := G.normalizedTopState_transformWord D.base D.denominator
    D.weight le_rfl hA pre
  have hdenDvd :
      (topStateAlongRat D.base pre
        (G.normalizedTopState D.denominator D.weight)).den ∣
          data.coprimePart :=
    topStateAlongRat_den_dvd_of_absorbed_prefix
      D.base data.exponent data.coprimePart
        (G.normalizedTopState D.denominator D.weight) pre hpreSpan
          data.residual_den_dvd
  have hdenLe :
      (topStateAlongRat D.base pre
        (G.normalizedTopState D.denominator D.weight)).den ≤
          data.coprimePart :=
    Nat.le_of_dvd data.coprimePart_pos hdenDvd
  unfold actualInteriorDenominator actualStabilizedInteriorGraph
  rw [hstate]
  exact hdenLe.trans data.coprimePart_le_den

noncomputable def actualInteriorBlockScale (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) : ℕ :=
  logarithmicBlockScale D.base 4
    (dyadicFloorBand (actualInteriorDenominator D pfx G threshold k))

theorem actualInteriorBlockScale_eq (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (left right : ↥(interiorEligibleIndices
      D N W m bound pfx G threshold)) :
    actualInteriorBlockScale D pfx G threshold left =
      actualInteriorBlockScale D pfx G threshold right := by
  unfold actualInteriorBlockScale
  rw [actualInteriorDenominator_eq D hgeom pfx G threshold
    hthreshold left right]

theorem actualInteriorBlockScale_pos (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    0 < actualInteriorBlockScale D pfx G threshold k := by
  exact logarithmicBlockScale_four_pos D.base_ge_two (dyadicFloorBand_pos _)

/-- A bound for the initial normalized denominator propagates to the actual
stabilized logarithmic block scale. -/
theorem actualInteriorBlockScale_le_of_state_den_le (D : CarrySeries)
    {N W m cap bound threshold Qcap : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree)
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (hstate : (G.normalizedTopState D.denominator D.weight).den ≤ Qcap)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    actualInteriorBlockScale D pfx G threshold k ≤
      logarithmicBlockScale D.base 4 Qcap := by
  have hactual := actualInteriorDenominator_le_initial
    D hgeom pfx G threshold hthreshold k
  have hdenPos : 0 < actualInteriorDenominator D pfx G threshold k :=
    Rat.den_pos _
  unfold actualInteriorBlockScale logarithmicBlockScale
  apply Nat.clog_mono_right
  gcongr
  exact (dyadicFloorBand_le hdenPos).trans (hactual.trans hstate)

theorem actualStabilizedInteriorWord_gap_le_blockScale (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    ∀ g ∈ actualStabilizedInteriorWord D pfx G threshold k,
      g ≤ actualInteriorBlockScale D pfx G threshold k := by
  let O := actualInteriorOrbit D hw hgeom pfx G threshold hthreshold k
  have hOgaps : O.gaps =
      actualStabilizedInteriorWord D pfx G threshold k := by
    exact actualInteriorOrbit_gaps D hw hgeom pfx G threshold hthreshold k
  have h := O.gap_le_logarithmicBlockScale
  rw [hOgaps] at h
  simpa only [actualInteriorBlockScale, actualInteriorDenominator, O] using h

theorem actualInteriorDenominator_gt_one (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    1 < actualInteriorDenominator D pfx G threshold k := by
  let O := actualInteriorOrbit D hw hgeom pfx G threshold hthreshold k
  simpa only [O, actualInteriorDenominator] using O.denominator_gt_one

theorem actualInteriorDenominator_band (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) :
    dyadicFloorBand (actualInteriorDenominator D pfx G threshold k) ≤
        actualInteriorDenominator D pfx G threshold k ∧
      actualInteriorDenominator D pfx G threshold k <
        2 * dyadicFloorBand
          (actualInteriorDenominator D pfx G threshold k) := by
  have hq : 0 < actualInteriorDenominator D pfx G threshold k :=
    Nat.zero_lt_one.trans
      (actualInteriorDenominator_gt_one D hw hgeom pfx G threshold
        hthreshold k)
  exact ⟨dyadicFloorBand_le hq,
    dyadicFloorBand_lt_two_mul _⟩

noncomputable def actualInteriorMeanGapBand (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold)) : ℕ :=
  let word := actualStabilizedInteriorWord D pfx G threshold k
  meanGapBand word.span word.length

/-- Total span of the actual retained greedy blocks over one locked interior
fibre. -/
noncomputable def actualInteriorRetainedMass (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ) : ℕ :=
  ∑ k : ↥(interiorEligibleIndices D N W m bound pfx G threshold),
    retainedGreedyBlockSpan
      (actualStabilizedInteriorWord D pfx G threshold k)
      (actualInteriorBlockScale D pfx G threshold k)
      (actualInteriorMeanGapBand D pfx G threshold k)

/-- Summed actual form of `eq:cover` for one locked prefix fibre. -/
theorem actualInteriorEligible_stabilizedSpan_le_retainedMass
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (hthreshold : ∀ k : ↥(interiorEligibleIndices D N W m bound pfx G threshold),
      Nat.log 2 (G.normalizedTopState D.denominator D.weight).den +
          2 * cap + 24 * actualInteriorBlockScale D pfx G threshold k ≤
        threshold) :
    (∑ k : ↥(interiorEligibleIndices D N W m bound pfx G threshold),
        Erdos260.GapWord.span
          (actualStabilizedInteriorWord D pfx G threshold k)) ≤
      4 * actualInteriorRetainedMass D (N := N) (W := W) (m := m)
        (bound := bound) pfx G threshold := by
  rw [actualInteriorRetainedMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _hk
  simpa only [actualInteriorBlockScale, actualInteriorMeanGapBand,
    actualInteriorDenominator] using
    (actualStabilizedInteriorWord_retained_cover D hw hgeom pfx G threshold k
      (hthreshold k))

/-! ## Actual retained block sources -/

/-- Enumeration index of the endpoint of a canonical completed block in an
actual stabilized interior word. -/
noncomputable def actualInteriorBlockEndpointIndex (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold ell : ℕ)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold))
    (i : Fin (completedGreedyBlocks
      (actualStabilizedInteriorWord D pfx G threshold k) ell).length) : ℕ :=
  k.1 + (lockingPrefix D.positiveEnumeration k.1 m bound).length +
    (actualInteriorAbsorptionPrefix D pfx G threshold k).length +
    (completedGreedyThrough
      (actualStabilizedInteriorWord D pfx G threshold k) ell i).length

theorem actualInteriorBlockEndpointIndex_start_le (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold ell : ℕ)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold))
    (i : Fin (completedGreedyBlocks
      (actualStabilizedInteriorWord D pfx G threshold k) ell).length) :
    k.1 ≤ actualInteriorBlockEndpointIndex D pfx G threshold ell k i := by
  unfold actualInteriorBlockEndpointIndex
  omega

/-- The actual block endpoint lies among the next `m` support indices.  This
is the proof-bearing offset used by `eq:sourcemap`. -/
theorem actualInteriorBlockEndpointIndex_sub_le (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold ell : ℕ)
    (hell : 0 < ell)
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold))
    (i : Fin (completedGreedyBlocks
      (actualStabilizedInteriorWord D pfx G threshold k) ell).length) :
    actualInteriorBlockEndpointIndex D pfx G threshold ell k i - k.1 ≤ m := by
  let lock := lockingPrefix D.positiveEnumeration k.1 m bound
  let post := postLockingWord D.positiveEnumeration k.1 m bound
  let trajectory := actualInteriorTrajectory D pfx G threshold k
  let pre := actualInteriorAbsorptionPrefix D pfx G threshold k
  let word := actualStabilizedInteriorWord D pfx G threshold k
  let through := completedGreedyThrough word ell i
  have hlock : lock.length + post.length = m := by
    have h := congrArg List.length
      (lockingPrefix_append_postLockingWord D.positiveEnumeration k.1 m bound)
    simpa only [lock, post, List.length_append,
      forwardGapWord_length] using h
  have habsorb : pre.length + word.length = trajectory.length := by
    have h := congrArg List.length
      (denominatorAbsorptionPrefix_append_suffix trajectory
        (lockedTopStateAbsorption D G).exponent)
    simpa only [pre, word, trajectory, actualInteriorAbsorptionPrefix,
      actualStabilizedInteriorWord, actualInteriorTrajectory,
      List.length_append] using h
  have htrajectory : trajectory.length ≤ post.length := by
    exact (interiorTrajectory_isPrefix D.base post
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))).length_le
  have hthrough : through.length ≤ word.length :=
    (completedGreedyThrough_isPrefix word ell hell i).length_le
  unfold actualInteriorBlockEndpointIndex
  dsimp only [lock, post, trajectory, pre, word, through] at *
  omega

/-- A genuine retained block occurrence.  Its fields are only the actual
anchor, the deterministic block position, and membership in the canonical
retained set; no injectivity statement is stored. -/
structure ActualInteriorBlockSource (D : CarrySeries)
    (N W m bound : ℕ) (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ)
    (ell Z : ↥(interiorEligibleIndices D N W m bound pfx G threshold) → ℕ) where
  anchor : ↥(interiorEligibleIndices D N W m bound pfx G threshold)
  blockIndex : Fin (completedGreedyBlocks
    (actualStabilizedInteriorWord D pfx G threshold anchor) (ell anchor)).length
  retained : blockIndex ∈ retainedGreedyBlockIndices
    (actualStabilizedInteriorWord D pfx G threshold anchor)
    (ell anchor) (Z anchor)

noncomputable def actualInteriorBlockSourceEndpointIndex (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    {ell Z : ↥(interiorEligibleIndices D N W m bound pfx G threshold) → ℕ}
    (source : ActualInteriorBlockSource D N W m bound pfx G threshold ell Z) : ℕ :=
  actualInteriorBlockEndpointIndex D pfx G threshold (ell source.anchor)
    source.anchor source.blockIndex

/-- Actual version of the endpoint/offset map in the manuscript. -/
noncomputable def actualInteriorBlockSourceMap (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    {ell Z : ↥(interiorEligibleIndices D N W m bound pfx G threshold) → ℕ}
    (source : ActualInteriorBlockSource D N W m bound pfx G threshold ell Z) :
    ℕ × ℕ :=
  (D.positiveEnumeration.a (actualInteriorBlockSourceEndpointIndex D source),
    actualInteriorBlockSourceEndpointIndex D source - source.anchor.1)

theorem actualInteriorBlockSourceMap_injective (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    {ell Z : ↥(interiorEligibleIndices D N W m bound pfx G threshold) → ℕ}
    (hell : ∀ k, 0 < ell k) :
    Function.Injective
      (actualInteriorBlockSourceMap D (N := N) (W := W) (m := m)
        (bound := bound) (pfx := pfx) (G := G) (threshold := threshold)
        (ell := ell) (Z := Z)) := by
  rintro ⟨leftAnchor, leftIndex, leftRetained⟩
    ⟨rightAnchor, rightIndex, rightRetained⟩ hmap
  let leftEndpoint := actualInteriorBlockEndpointIndex D pfx G threshold
    (ell leftAnchor) leftAnchor leftIndex
  let rightEndpoint := actualInteriorBlockEndpointIndex D pfx G threshold
    (ell rightAnchor) rightAnchor rightIndex
  change (D.positiveEnumeration.a leftEndpoint,
      leftEndpoint - leftAnchor.1) =
    (D.positiveEnumeration.a rightEndpoint,
      rightEndpoint - rightAnchor.1) at hmap
  have hendpointValue := (Prod.mk.inj hmap).1
  have hendpoint : leftEndpoint = rightEndpoint :=
    D.positiveEnumeration.strictMono.injective hendpointValue
  have hoffset := (Prod.mk.inj hmap).2
  have hleftStart : leftAnchor.1 ≤ leftEndpoint :=
    actualInteriorBlockEndpointIndex_start_le D pfx G threshold
      (ell leftAnchor) leftAnchor leftIndex
  have hrightStart : rightAnchor.1 ≤ rightEndpoint :=
    actualInteriorBlockEndpointIndex_start_le D pfx G threshold
      (ell rightAnchor) rightAnchor rightIndex
  have hanchorValue : leftAnchor.1 = rightAnchor.1 := by
    rw [hendpoint] at hoffset hleftStart
    omega
  have hanchor : leftAnchor = rightAnchor := Subtype.ext hanchorValue
  subst rightAnchor
  have hthrough :
      (completedGreedyThrough
        (actualStabilizedInteriorWord D pfx G threshold leftAnchor)
        (ell leftAnchor) leftIndex).length =
      (completedGreedyThrough
        (actualStabilizedInteriorWord D pfx G threshold leftAnchor)
        (ell leftAnchor) rightIndex).length := by
    dsimp only [leftEndpoint, rightEndpoint,
      actualInteriorBlockEndpointIndex] at hendpoint
    omega
  have hindex : leftIndex = rightIndex :=
    completedGreedyThrough_length_injective
      (actualStabilizedInteriorWord D pfx G threshold leftAnchor)
      (ell leftAnchor) (hell leftAnchor) hthrough
  subst rightIndex
  rfl

noncomputable def actualInteriorBlockSourceEquiv (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    {ell Z : ↥(interiorEligibleIndices D N W m bound pfx G threshold) → ℕ} :
    ActualInteriorBlockSource D N W m bound pfx G threshold ell Z ≃
      Σ k : ↥(interiorEligibleIndices D N W m bound pfx G threshold),
        ↥(retainedGreedyBlockIndices
          (actualStabilizedInteriorWord D pfx G threshold k)
          (ell k) (Z k)) where
  toFun source :=
    ⟨source.anchor, ⟨source.blockIndex, source.retained⟩⟩
  invFun source :=
    ⟨source.1, source.2.1, source.2.2⟩
  left_inv source := by cases source; rfl
  right_inv source := by rcases source with ⟨anchor, ⟨index, retained⟩⟩; rfl

noncomputable instance actualInteriorBlockSourceFintype (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    {ell Z : ↥(interiorEligibleIndices D N W m bound pfx G threshold) → ℕ} :
    Fintype (ActualInteriorBlockSource D N W m bound pfx G threshold ell Z) :=
  Fintype.ofEquiv
    (Σ k : ↥(interiorEligibleIndices D N W m bound pfx G threshold),
      ↥(retainedGreedyBlockIndices
        (actualStabilizedInteriorWord D pfx G threshold k)
        (ell k) (Z k)))
    (actualInteriorBlockSourceEquiv D).symm

abbrev CanonicalActualInteriorBlockSource (D : CarrySeries)
    (N W m bound : ℕ) (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ) :=
  ActualInteriorBlockSource D N W m bound pfx G threshold
    (fun k => actualInteriorBlockScale D pfx G threshold k)
    (fun k => actualInteriorMeanGapBand D pfx G threshold k)

noncomputable def canonicalActualInteriorBlockSourceSpan (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource D N W m bound pfx G threshold) :
    ℕ :=
  Erdos260.GapWord.span (completedGreedyBlock
    (actualStabilizedInteriorWord D pfx G threshold source.anchor)
    (actualInteriorBlockScale D pfx G threshold source.anchor)
    source.blockIndex)

/-- Reindexing the real source type recovers exactly the retained block mass;
there is no multiplicity hidden in this conversion. -/
theorem canonicalActualInteriorBlockSourceSpan_sum (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ) :
    (∑ source : CanonicalActualInteriorBlockSource
        D N W m bound pfx G threshold,
      canonicalActualInteriorBlockSourceSpan D source) =
      actualInteriorRetainedMass D (N := N) (W := W) (m := m)
        (bound := bound) pfx G threshold := by
  let e := actualInteriorBlockSourceEquiv D
    (N := N) (W := W) (m := m) (bound := bound)
    (pfx := pfx) (G := G) (threshold := threshold)
    (ell := fun k => actualInteriorBlockScale D pfx G threshold k)
    (Z := fun k => actualInteriorMeanGapBand D pfx G threshold k)
  rw [Fintype.sum_equiv e
    (fun source => canonicalActualInteriorBlockSourceSpan D source)
    (fun code => Erdos260.GapWord.span (completedGreedyBlock
      (actualStabilizedInteriorWord D pfx G threshold code.1)
      (actualInteriorBlockScale D pfx G threshold code.1) code.2.1))
    (by intro source; rfl)]
  rw [Fintype.sum_sigma]
  simp only [actualInteriorRetainedMass, retainedGreedyBlockSpan]
  apply Finset.sum_congr rfl
  intro k _hk
  exact (Finset.sum_subtype
    (retainedGreedyBlockIndices
      (actualStabilizedInteriorWord D pfx G threshold k)
      (actualInteriorBlockScale D pfx G threshold k)
      (actualInteriorMeanGapBand D pfx G threshold k))
    (by simp)
    (fun i => Erdos260.GapWord.span (completedGreedyBlock
      (actualStabilizedInteriorWord D pfx G threshold k)
      (actualInteriorBlockScale D pfx G threshold k) i))).symm

theorem canonicalActualInteriorBlockSourceMap_injective (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ} :
    Function.Injective
      (actualInteriorBlockSourceMap D (N := N) (W := W) (m := m)
        (bound := bound) (pfx := pfx) (G := G) (threshold := threshold)
        (ell := fun k => actualInteriorBlockScale D pfx G threshold k)
        (Z := fun k => actualInteriorMeanGapBand D pfx G threshold k)) :=
  actualInteriorBlockSourceMap_injective D fun k =>
    actualInteriorBlockScale_pos D pfx G threshold k

theorem canonicalActualInteriorBlockSource_offset_le (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    actualInteriorBlockSourceEndpointIndex D source - source.anchor.1 ≤ m := by
  exact actualInteriorBlockEndpointIndex_sub_le D pfx G threshold
    (actualInteriorBlockScale D pfx G threshold source.anchor)
    (actualInteriorBlockScale_pos D pfx G threshold source.anchor)
    source.anchor source.blockIndex

theorem canonicalActualInteriorBlockSource_endpoint_mem (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    D.positiveEnumeration.a (actualInteriorBlockSourceEndpointIndex D source) ∈
      Finset.Ioc N (N + W + m * cap) := by
  let endpoint := actualInteriorBlockSourceEndpointIndex D source
  let offset := endpoint - source.anchor.1
  have hstart : source.anchor.1 ≤ endpoint :=
    actualInteriorBlockEndpointIndex_start_le D pfx G threshold
      (actualInteriorBlockScale D pfx G threshold source.anchor)
      source.anchor source.blockIndex
  have hoffset : offset ≤ m := by
    exact canonicalActualInteriorBlockSource_offset_le D source
  have hanchorRealized : source.anchor.1 ∈
      realizedPrefixIndices D N W m bound pfx :=
    (Finset.mem_filter.mp source.anchor.2).1
  have hanchorWindow : source.anchor.1 ∈
      windowIndices D.positiveEnumeration N W :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hanchorRealized).1).1
  have hanchorIco := Finset.mem_Ico.mp hanchorWindow
  have hanchorLower : N < D.positiveEnumeration.a source.anchor.1 :=
    (Erdos260.firstIndexAbove_spec D.positiveEnumeration N).trans_le
      (D.positiveEnumeration.strictMono.monotone hanchorIco.1)
  have hendpointLower : N < D.positiveEnumeration.a endpoint :=
    hanchorLower.trans_le
      (D.positiveEnumeration.strictMono.monotone hstart)
  have hendpointEq : source.anchor.1 + offset = endpoint := by
    dsimp only [offset]
    exact Nat.add_sub_of_le hstart
  have hendpointUpper := WindowGeometry.future_point_le
    D.positiveEnumeration hgeom hanchorWindow hoffset
  rw [hendpointEq] at hendpointUpper
  exact Finset.mem_Ioc.mpr ⟨hendpointLower, hendpointUpper⟩

/-- Coarse finite source count obtained solely from the proved actual
endpoint/offset injection.  Later cell fibres replace the coarse endpoint
interval by their sharper polynomial-fibre sets. -/
theorem canonicalActualInteriorBlockSource_card_le (D : CarrySeries)
    {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold : ℕ) :
    Fintype.card (CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) ≤
        (W + m * cap) * (m + 1) := by
  classical
  let Source := CanonicalActualInteriorBlockSource
    D N W m bound pfx G threshold
  let endpoints := Finset.Ioc N (N + W + m * cap)
  let encode : Source → ↥endpoints × Fin (m + 1) := fun source =>
    (⟨D.positiveEnumeration.a
        (actualInteriorBlockSourceEndpointIndex D source),
      canonicalActualInteriorBlockSource_endpoint_mem D hgeom source⟩,
    ⟨actualInteriorBlockSourceEndpointIndex D source - source.anchor.1,
      Nat.lt_succ_iff.mpr
        (canonicalActualInteriorBlockSource_offset_le D source)⟩)
  have hencode : Function.Injective encode := by
    intro left right heq
    apply canonicalActualInteriorBlockSourceMap_injective D
    exact Prod.ext
      (congrArg Subtype.val (Prod.mk.inj heq).1)
      (congrArg Fin.val (Prod.mk.inj heq).2)
  have hcard := Fintype.card_le_of_injective encode hencode
  calc
    Fintype.card Source ≤ Fintype.card (↥endpoints × Fin (m + 1)) := hcard
    _ = endpoints.card * (m + 1) := by simp
    _ = (W + m * cap) * (m + 1) := by
      simp [endpoints]
      omega

/-- The canonical retained block word carried by an actual source. -/
noncomputable def canonicalActualInteriorBlockWord (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) : Erdos260.GapWord :=
  completedGreedyBlock
    (actualStabilizedInteriorWord D pfx G threshold source.anchor)
    (actualInteriorBlockScale D pfx G threshold source.anchor)
    source.blockIndex

theorem canonicalActualInteriorBlockWord_mem_retainedWords
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    canonicalActualInteriorBlockWord D source ∈
      retainedBlockWords
        (actualInteriorBlockScale D pfx G threshold source.anchor)
        (actualInteriorMeanGapBand D pfx G threshold source.anchor) := by
  let word := actualStabilizedInteriorWord D pfx G threshold source.anchor
  let ell := actualInteriorBlockScale D pfx G threshold source.anchor
  let Z := actualInteriorMeanGapBand D pfx G threshold source.anchor
  let O := actualInteriorOrbit D hw hgeom pfx G threshold
    hthreshold source.anchor
  have hOgaps : O.gaps = word := by
    dsimp only [O, word]
    exact actualInteriorOrbit_gaps D hw hgeom pfx G threshold
      hthreshold source.anchor
  have hcap : ∀ g ∈ word, g ≤ ell := by
    have h := O.gap_le_logarithmicBlockScale
    rw [hOgaps] at h
    simpa only [ell, O, actualInteriorBlockScale,
      actualInteriorDenominator] using h
  simpa only [canonicalActualInteriorBlockWord, word, ell, Z] using
    completedGreedyBlock_mem_retainedBlockWords
      (actualInteriorBlockScale_pos D pfx G threshold source.anchor)
      (actualStabilizedInteriorWord_positive D pfx G threshold source.anchor)
      hcap source.retained

/-- Remaining stabilized interior gaps strictly after the source block. -/
noncomputable def canonicalActualInteriorAfterBlock (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) : Erdos260.GapWord :=
  (actualStabilizedInteriorWord D pfx G threshold source.anchor).drop
    (completedGreedyThrough
      (actualStabilizedInteriorWord D pfx G threshold source.anchor)
      (actualInteriorBlockScale D pfx G threshold source.anchor)
      source.blockIndex).length

theorem canonicalActualInteriorThrough_append_afterBlock
    (D : CarrySeries) {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    completedGreedyThrough
        (actualStabilizedInteriorWord D pfx G threshold source.anchor)
        (actualInteriorBlockScale D pfx G threshold source.anchor)
        source.blockIndex ++
      canonicalActualInteriorAfterBlock D source =
        actualStabilizedInteriorWord D pfx G threshold source.anchor := by
  let word := actualStabilizedInteriorWord D pfx G threshold source.anchor
  let ell := actualInteriorBlockScale D pfx G threshold source.anchor
  let through := completedGreedyThrough word ell source.blockIndex
  have hpref := completedGreedyThrough_isPrefix word ell
    (actualInteriorBlockScale_pos D pfx G threshold source.anchor)
    source.blockIndex
  simpa only [word, ell, through, canonicalActualInteriorAfterBlock] using
    (List.prefix_append_drop hpref).symm

/-- The actual unused suffix agrees with the suffix of the canonical greedy
block list, including the final incomplete remainder. -/
theorem canonicalActualInteriorAfterBlock_eq_completedBlockAfter
    (D : CarrySeries) {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    canonicalActualInteriorAfterBlock D source =
      completedBlockAfter
        (completedGreedyBlocks
          (actualStabilizedInteriorWord D pfx G threshold source.anchor)
          (actualInteriorBlockScale D pfx G threshold source.anchor))
        (Erdos260.GapWord.greedyDecompose
          (actualStabilizedInteriorWord D pfx G threshold source.anchor)
            (3 * actualInteriorBlockScale D pfx G threshold source.anchor)).remainder
        source.blockIndex := by
  let word := actualStabilizedInteriorWord D pfx G threshold source.anchor
  let ell := actualInteriorBlockScale D pfx G threshold source.anchor
  let blocks := completedGreedyBlocks word ell
  let remainder := (word.greedyDecompose (3 * ell)).remainder
  let through := completedGreedyThrough word ell source.blockIndex
  let after := canonicalActualInteriorAfterBlock D source
  let tail := completedBlockAfter blocks remainder source.blockIndex
  have hell : 0 < ell := by
    simpa only [ell] using
      actualInteriorBlockScale_pos D pfx G threshold source.anchor
  have hactual : through ++ after = word := by
    simpa only [through, after, word, ell] using
      canonicalActualInteriorThrough_append_afterBlock D source
  have hvalid := Erdos260.GapWord.greedyDecompose_valid word
    (3 * ell) (Nat.mul_pos (by omega) hell)
  have hcanonical : through ++ tail = word := by
    dsimp only [through, tail, completedGreedyThrough,
      completedGreedyPrefix, completedBlockAfter, blocks, remainder,
      completedGreedyBlocks]
    rw [← List.append_assoc, ← List.flatten_append, List.take_append_drop]
    exact hvalid.1
  have heq : through ++ after = through ++ tail :=
    hactual.trans hcanonical.symm
  exact List.append_right_injective through heq

/-- A retained source is deep at scale `F` if more than `F` units of genuine
interior span remain after its block endpoint. -/
def CanonicalActualInteriorBlockSource.Deep (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) (F : ℕ) : Prop :=
  F < Erdos260.GapWord.span (canonicalActualInteriorAfterBlock D source)

/-- Retained mass whose block endpoint still has more than `F` units of
genuine interior continuation. -/
noncomputable def actualInteriorDeepRetainedMass (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold F : ℕ) : ℕ := by
  classical
  exact ∑ source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold,
    if source.Deep D F then
      canonicalActualInteriorBlockSourceSpan D source
    else 0

/-- Complementary retained mass lost at the terminal shallow suffix. -/
noncomputable def actualInteriorShallowRetainedMass (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold F : ℕ) : ℕ := by
  classical
  exact ∑ source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold,
    if ¬ source.Deep D F then
      canonicalActualInteriorBlockSourceSpan D source
    else 0

theorem actualInteriorRetainedMass_eq_deep_add_shallow
    (D : CarrySeries) {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold F : ℕ) :
    actualInteriorRetainedMass D (N := N) (W := W) (m := m)
        (bound := bound) pfx G threshold =
      actualInteriorDeepRetainedMass D (N := N) (W := W) (m := m)
          (bound := bound) pfx G threshold F +
        actualInteriorShallowRetainedMass D (N := N) (W := W) (m := m)
          (bound := bound) pfx G threshold F := by
  classical
  rw [← canonicalActualInteriorBlockSourceSpan_sum]
  unfold actualInteriorDeepRetainedMass actualInteriorShallowRetainedMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro source _hsource
  by_cases hdeep : source.Deep D F <;> simp [hdeep]

/-- The mass discarded for insufficient continuation is bounded by one
terminal suffix per eligible window. -/
theorem actualInteriorShallowRetainedMass_le
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold F : ℕ)
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold) :
    actualInteriorShallowRetainedMass D (N := N) (W := W) (m := m)
        (bound := bound) pfx G threshold F ≤
      Finset.univ.sum (fun k : ↥(interiorEligibleIndices
          D N W m bound pfx G threshold) =>
        F + 4 * actualInteriorBlockScale D (N := N) (W := W) (m := m)
          (bound := bound) pfx G threshold k) := by
  classical
  let e := actualInteriorBlockSourceEquiv D
    (N := N) (W := W) (m := m) (bound := bound)
    (pfx := pfx) (G := G) (threshold := threshold)
    (ell := fun k => actualInteriorBlockScale D pfx G threshold k)
    (Z := fun k => actualInteriorMeanGapBand D pfx G threshold k)
  unfold actualInteriorShallowRetainedMass
  rw [Fintype.sum_equiv e
    (fun source => if ¬ CanonicalActualInteriorBlockSource.Deep D source F then
      canonicalActualInteriorBlockSourceSpan D source else 0)
    (fun code =>
      let source : CanonicalActualInteriorBlockSource
          D N W m bound pfx G threshold :=
        ⟨code.1, code.2.1, code.2.2⟩
      if ¬ CanonicalActualInteriorBlockSource.Deep D source F then
        canonicalActualInteriorBlockSourceSpan D source else 0)
    (by intro source; rfl)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro k _hk
  let word := actualStabilizedInteriorWord D pfx G threshold k
  let ell := actualInteriorBlockScale D pfx G threshold k
  let Z := actualInteriorMeanGapBand D pfx G threshold k
  let blocks := completedGreedyBlocks word ell
  let remainder := (word.greedyDecompose (3 * ell)).remainder
  let retained := retainedGreedyBlockIndices word ell Z
  let genericTerm : Fin blocks.length → ℕ := fun i =>
    if Erdos260.GapWord.span
        (completedBlockAfter blocks remainder i) ≤ F then
      Erdos260.GapWord.span (blocks.get i)
    else 0
  have hsourceTerm (i : ↥retained) :
      (let source : CanonicalActualInteriorBlockSource
          D N W m bound pfx G threshold :=
        ⟨k, i.1, i.2⟩
       if ¬ CanonicalActualInteriorBlockSource.Deep D source F then
         canonicalActualInteriorBlockSourceSpan D source else 0) =
        genericTerm i.1 := by
    let source : CanonicalActualInteriorBlockSource
        D N W m bound pfx G threshold := ⟨k, i.1, i.2⟩
    have hafter := canonicalActualInteriorAfterBlock_eq_completedBlockAfter
      D source
    change (if ¬ CanonicalActualInteriorBlockSource.Deep D source F then
        canonicalActualInteriorBlockSourceSpan D source else 0) =
      genericTerm i.1
    unfold CanonicalActualInteriorBlockSource.Deep
      canonicalActualInteriorBlockSourceSpan
    rw [hafter]
    simp only [not_lt]
    rfl
  calc
    (∑ i : ↥retained,
        (let source : CanonicalActualInteriorBlockSource
            D N W m bound pfx G threshold :=
          ⟨k, i.1, i.2⟩
          if ¬ CanonicalActualInteriorBlockSource.Deep D source F then
           canonicalActualInteriorBlockSourceSpan D source else 0)) =
        ∑ i : ↥retained, genericTerm i.1 := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact hsourceTerm i
    _ ≤ ∑ i : Fin blocks.length, genericTerm i := by
      rw [← Finset.sum_subtype retained (by simp) genericTerm]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ retained)
    _ = shallowCompletedBlockSpan blocks remainder F := by
      rfl
    _ ≤ F + 4 * ell := by
      apply shallowCompletedBlockSpan_le
      intro block hblock
      have hell : 0 < ell := by
        simpa only [ell] using
          actualInteriorBlockScale_pos D pfx G threshold k
      have hvalid := Erdos260.GapWord.greedyDecompose_valid word
        (3 * ell) (Nat.mul_pos (by omega) hell)
      have hgreedy : Erdos260.GapWord.IsGreedyBlock (3 * ell) block :=
        hvalid.2.1 block (by
          simpa only [blocks, completedGreedyBlocks] using hblock)
      have hcapWord := actualStabilizedInteriorWord_gap_le_blockScale
        D hw hgeom pfx G threshold hthreshold k
      have hcapBlock : ∀ g ∈ block, g ≤ ell := by
        intro g hg
        apply hcapWord g
        change g ∈ word
        rw [← hvalid.1]
        simp only [List.mem_append, List.mem_flatten]
        left
        exact ⟨block, by
          simpa only [blocks, completedGreedyBlocks] using hblock, hg⟩
      exact (greedyBlock_three_four_span hgreedy hcapBlock).2
    _ = F + 4 * actualInteriorBlockScale D pfx G threshold k := rfl

/-- Deep-source form of the actual cover: after the canonical entropy loss,
the only additional cost is one explicit terminal suffix per eligible
window. -/
theorem actualInteriorEligible_stabilizedSpan_le_deepMass_add_terminal
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold F : ℕ)
    (hbaseThreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (hcoverThreshold : ∀ k : ↥(interiorEligibleIndices
        D N W m bound pfx G threshold),
      Nat.log 2 (G.normalizedTopState D.denominator D.weight).den +
          2 * cap + 24 * actualInteriorBlockScale D pfx G threshold k ≤
        threshold) :
    (∑ k : ↥(interiorEligibleIndices D N W m bound pfx G threshold),
        Erdos260.GapWord.span
          (actualStabilizedInteriorWord D pfx G threshold k)) ≤
      4 * actualInteriorDeepRetainedMass D
          (N := N) (W := W) (m := m) (bound := bound)
          pfx G threshold F +
        4 * Finset.univ.sum (fun k : ↥(interiorEligibleIndices
            D N W m bound pfx G threshold) =>
          F + 4 * actualInteriorBlockScale D (N := N) (W := W) (m := m)
            (bound := bound) pfx G threshold k) := by
  have hcover := actualInteriorEligible_stabilizedSpan_le_retainedMass
    D hw hgeom pfx G threshold hcoverThreshold
  rw [actualInteriorRetainedMass_eq_deep_add_shallow
    D pfx G threshold F] at hcover
  have hshallow := actualInteriorShallowRetainedMass_le
    D (N := N) (W := W) (m := m) (cap := cap) (bound := bound)
      hw hgeom pfx G threshold F hbaseThreshold
  omega

/-- Canonical common-frequency word selected after a deep block endpoint. -/
noncomputable def canonicalActualInteriorFutureWord (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
  (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) (F : ℕ) : Erdos260.GapWord :=
  (canonicalActualInteriorAfterBlock D source).firstPrefixAbove F

theorem canonicalActualInteriorFutureWord_bounds
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold F : ℕ}
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold)
    (hdeep : source.Deep D F) :
    Erdos260.GapWord.Positive
        (canonicalActualInteriorFutureWord D source F) ∧
      F < Erdos260.GapWord.span
        (canonicalActualInteriorFutureWord D source F) ∧
      Erdos260.GapWord.span
          (canonicalActualInteriorFutureWord D source F) ≤
        F + actualInteriorBlockScale D pfx G threshold source.anchor ∧
      (canonicalActualInteriorFutureWord D source F).IsPrefix
        (canonicalActualInteriorAfterBlock D source) := by
  let after := canonicalActualInteriorAfterBlock D source
  let future := canonicalActualInteriorFutureWord D source F
  let ell := actualInteriorBlockScale D pfx G threshold source.anchor
  have hpositiveAfter : Erdos260.GapWord.Positive after := by
    intro g hg
    apply actualStabilizedInteriorWord_positive
      D pfx G threshold source.anchor g
    exact List.mem_of_mem_drop hg
  have hcapAfter : ∀ g ∈ after, g ≤ ell := by
    intro g hg
    apply actualStabilizedInteriorWord_gap_le_blockScale
      D hw hgeom pfx G threshold hthreshold source.anchor g
    exact List.mem_of_mem_drop hg
  have hcross : F < Erdos260.GapWord.span after := hdeep
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Erdos260.GapWord.firstPrefixAbove_positive after F hpositiveAfter
  · simpa only [future, canonicalActualInteriorFutureWord] using
      Erdos260.GapWord.lt_span_firstPrefixAbove_of_lt_span after F hcross
  · simpa only [future, canonicalActualInteriorFutureWord, ell] using
      Erdos260.GapWord.span_firstPrefixAbove_le_add after F ell hcapAfter
  · exact Erdos260.GapWord.firstPrefixAbove_isPrefix after F

/-- Completed stabilized word strictly before the source block. -/
noncomputable def canonicalActualInteriorBeforeBlock (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) : Erdos260.GapWord :=
  completedGreedyPrefix
    (actualStabilizedInteriorWord D pfx G threshold source.anchor)
    (actualInteriorBlockScale D pfx G threshold source.anchor)
    source.blockIndex

/-- Actual continuation from the locked graph to the start of a retained
block. -/
noncomputable def canonicalActualInteriorBlockStartContinuation
    (D : CarrySeries) {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) : Erdos260.GapWord :=
  actualInteriorAbsorptionPrefix D pfx G threshold source.anchor ++
    canonicalActualInteriorBeforeBlock D source

/-- Exact polynomial graph at the start of the source block. -/
noncomputable def canonicalActualInteriorBlockStartGraph (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    PolynomialGraph D.weight.natDegree :=
  G.transformWord D.base D.denominator D.weight le_rfl
    (canonicalActualInteriorBlockStartContinuation D source)

theorem canonicalActualInteriorBlockStartGraph_eq_stabilized_transform
    (D : CarrySeries) {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    canonicalActualInteriorBlockStartGraph D source =
      (actualStabilizedInteriorGraph D pfx G threshold source.anchor).transformWord
        D.base D.denominator D.weight le_rfl
        (canonicalActualInteriorBeforeBlock D source) := by
  unfold canonicalActualInteriorBlockStartGraph
    canonicalActualInteriorBlockStartContinuation
    actualStabilizedInteriorGraph
  rw [G.transformWord_append]

/-- Actual continuation from the locked graph to the endpoint of a retained
block: denominator absorption followed by the canonical completed prefix. -/
noncomputable def canonicalActualInteriorBlockContinuation (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) : Erdos260.GapWord :=
  actualInteriorAbsorptionPrefix D pfx G threshold source.anchor ++
    completedGreedyThrough
      (actualStabilizedInteriorWord D pfx G threshold source.anchor)
      (actualInteriorBlockScale D pfx G threshold source.anchor)
      source.blockIndex

noncomputable def canonicalActualInteriorBlockEndGraph (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    PolynomialGraph D.weight.natDegree :=
  G.transformWord D.base D.denominator D.weight le_rfl
    (canonicalActualInteriorBlockContinuation D source)

theorem canonicalActualInteriorBlockContinuation_eq_start_append_block
    (D : CarrySeries) {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    canonicalActualInteriorBlockContinuation D source =
      canonicalActualInteriorBlockStartContinuation D source ++
        canonicalActualInteriorBlockWord D source := by
  unfold canonicalActualInteriorBlockContinuation
    canonicalActualInteriorBlockStartContinuation
    canonicalActualInteriorBeforeBlock canonicalActualInteriorBlockWord
  rw [completedGreedyThrough_eq_append, List.append_assoc]

theorem canonicalActualInteriorBlockEndGraph_eq_transform_start
    (D : CarrySeries) {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    canonicalActualInteriorBlockEndGraph D source =
      (canonicalActualInteriorBlockStartGraph D source).transformWord
        D.base D.denominator D.weight le_rfl
        (canonicalActualInteriorBlockWord D source) := by
  unfold canonicalActualInteriorBlockEndGraph
    canonicalActualInteriorBlockStartGraph
  rw [canonicalActualInteriorBlockContinuation_eq_start_append_block,
    G.transformWord_append]

/-- Inside one locked prefix fibre, the greedy block position determines the
entire continuation from the locked graph to that block endpoint. -/
theorem canonicalActualInteriorBlockContinuation_eq_of_position
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (left right : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold)
    (hindex : left.blockIndex.1 = right.blockIndex.1) :
    canonicalActualInteriorBlockContinuation D left =
      canonicalActualInteriorBlockContinuation D right := by
  have hell := actualInteriorBlockScale_eq
    D hgeom pfx G threshold hthreshold left.anchor right.anchor
  have habsorb := actualInteriorAbsorptionPrefix_eq
    D hgeom pfx G threshold hthreshold left.anchor right.anchor
  let rightIndex : Fin (completedGreedyBlocks
      (actualStabilizedInteriorWord D pfx G threshold right.anchor)
      (actualInteriorBlockScale D pfx G threshold left.anchor)).length := by
    refine ⟨right.blockIndex.1, ?_⟩
    rw [hell]
    exact right.blockIndex.isLt
  have hrightIndex : rightIndex.1 = right.blockIndex.1 := by
    rfl
  have hindex' : left.blockIndex.1 = rightIndex.1 :=
    hindex.trans hrightIndex.symm
  rcases actualStabilizedInteriorWord_prefix_or_prefix
      D hgeom pfx G threshold hthreshold left.anchor right.anchor with
      hpref | hpref
  · have hthrough := completedGreedyThrough_eq_of_prefix
      hpref left.blockIndex rightIndex hindex'
    have hthrough' : completedGreedyThrough
          (actualStabilizedInteriorWord D pfx G threshold left.anchor)
          (actualInteriorBlockScale D pfx G threshold left.anchor)
          left.blockIndex =
        completedGreedyThrough
          (actualStabilizedInteriorWord D pfx G threshold right.anchor)
          (actualInteriorBlockScale D pfx G threshold right.anchor)
          right.blockIndex := by
      calc
        _ = completedGreedyThrough
            (actualStabilizedInteriorWord D pfx G threshold right.anchor)
            (actualInteriorBlockScale D pfx G threshold left.anchor)
            rightIndex := hthrough
        _ = _ := by
          simp only [completedGreedyThrough, rightIndex, hell]
    unfold canonicalActualInteriorBlockContinuation
    rw [habsorb]
    exact congrArg (fun word =>
      actualInteriorAbsorptionPrefix D pfx G threshold right.anchor ++ word)
        hthrough'
  · have hthrough := completedGreedyThrough_eq_of_prefix
      hpref rightIndex left.blockIndex hindex'.symm
    have hthrough' : completedGreedyThrough
          (actualStabilizedInteriorWord D pfx G threshold left.anchor)
          (actualInteriorBlockScale D pfx G threshold left.anchor)
          left.blockIndex =
        completedGreedyThrough
          (actualStabilizedInteriorWord D pfx G threshold right.anchor)
          (actualInteriorBlockScale D pfx G threshold right.anchor)
          right.blockIndex := by
      calc
        _ = completedGreedyThrough
            (actualStabilizedInteriorWord D pfx G threshold right.anchor)
            (actualInteriorBlockScale D pfx G threshold left.anchor)
            rightIndex := hthrough.symm
        _ = _ := by
          simp only [completedGreedyThrough, rightIndex, hell]
    unfold canonicalActualInteriorBlockContinuation
    rw [habsorb]
    exact congrArg (fun word =>
      actualInteriorAbsorptionPrefix D pfx G threshold right.anchor ++ word)
        hthrough'

/-- The same position also determines the exact retained block word. -/
theorem canonicalActualInteriorBlockWord_eq_of_position
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (left right : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold)
    (hindex : left.blockIndex.1 = right.blockIndex.1) :
    canonicalActualInteriorBlockWord D left =
      canonicalActualInteriorBlockWord D right := by
  have hell := actualInteriorBlockScale_eq
    D hgeom pfx G threshold hthreshold left.anchor right.anchor
  let rightIndex : Fin (completedGreedyBlocks
      (actualStabilizedInteriorWord D pfx G threshold right.anchor)
      (actualInteriorBlockScale D pfx G threshold left.anchor)).length := by
    refine ⟨right.blockIndex.1, ?_⟩
    rw [hell]
    exact right.blockIndex.isLt
  have hrightIndex : rightIndex.1 = right.blockIndex.1 := by
    rfl
  have hindex' : left.blockIndex.1 = rightIndex.1 :=
    hindex.trans hrightIndex.symm
  rcases actualStabilizedInteriorWord_prefix_or_prefix
      D hgeom pfx G threshold hthreshold left.anchor right.anchor with
      hpref | hpref
  · have hblock := completedGreedyBlock_eq_of_prefix
      hpref left.blockIndex rightIndex hindex'
    have hblock' : completedGreedyBlock
          (actualStabilizedInteriorWord D pfx G threshold left.anchor)
          (actualInteriorBlockScale D pfx G threshold left.anchor)
          left.blockIndex =
        completedGreedyBlock
          (actualStabilizedInteriorWord D pfx G threshold right.anchor)
          (actualInteriorBlockScale D pfx G threshold right.anchor)
          right.blockIndex := by
      calc
        _ = completedGreedyBlock
            (actualStabilizedInteriorWord D pfx G threshold right.anchor)
            (actualInteriorBlockScale D pfx G threshold left.anchor)
            rightIndex := hblock
        _ = _ := by
          simp only [completedGreedyBlock, rightIndex, hell]
    simpa only [canonicalActualInteriorBlockWord] using hblock'
  · have hblock := completedGreedyBlock_eq_of_prefix
      hpref rightIndex left.blockIndex hindex'.symm
    have hblock' : completedGreedyBlock
          (actualStabilizedInteriorWord D pfx G threshold left.anchor)
          (actualInteriorBlockScale D pfx G threshold left.anchor)
          left.blockIndex =
        completedGreedyBlock
          (actualStabilizedInteriorWord D pfx G threshold right.anchor)
          (actualInteriorBlockScale D pfx G threshold right.anchor)
          right.blockIndex := by
      calc
        _ = completedGreedyBlock
            (actualStabilizedInteriorWord D pfx G threshold right.anchor)
            (actualInteriorBlockScale D pfx G threshold left.anchor)
            rightIndex := hblock.symm
        _ = _ := by
          simp only [completedGreedyBlock, rightIndex, hell]
    simpa only [canonicalActualInteriorBlockWord] using hblock'

/-- Consequently the exact polynomial graph at the block endpoint is a
function of the locked prefix and the greedy block position. -/
theorem canonicalActualInteriorBlockEndGraph_eq_of_position
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (left right : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold)
    (hindex : left.blockIndex.1 = right.blockIndex.1) :
    canonicalActualInteriorBlockEndGraph D left =
      canonicalActualInteriorBlockEndGraph D right := by
  unfold canonicalActualInteriorBlockEndGraph
  rw [canonicalActualInteriorBlockContinuation_eq_of_position
    D hgeom hthreshold left right hindex]

/-- The locked-to-end continuation followed by the unused suffix is exactly
the whole genuine all-interior trajectory. -/
theorem canonicalActualInteriorBlockContinuation_append_afterBlock
    (D : CarrySeries) {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    canonicalActualInteriorBlockContinuation D source ++
      canonicalActualInteriorAfterBlock D source =
        actualInteriorTrajectory D pfx G threshold source.anchor := by
  let pre := actualInteriorAbsorptionPrefix D pfx G threshold source.anchor
  let word := actualStabilizedInteriorWord D pfx G threshold source.anchor
  let through := completedGreedyThrough word
    (actualInteriorBlockScale D pfx G threshold source.anchor)
    source.blockIndex
  let after := canonicalActualInteriorAfterBlock D source
  let trajectory := actualInteriorTrajectory D pfx G threshold source.anchor
  have hthroughAfter : through ++ after = word := by
    simpa only [through, after, word] using
      canonicalActualInteriorThrough_append_afterBlock D source
  have habsorb : pre ++ word = trajectory := by
    simpa only [pre, word, trajectory, actualInteriorAbsorptionPrefix,
      actualStabilizedInteriorWord, actualInteriorTrajectory] using
      denominatorAbsorptionPrefix_append_suffix trajectory
        (lockedTopStateAbsorption D G).exponent
  change (pre ++ through) ++ after = trajectory
  rw [List.append_assoc, hthroughAfter, habsorb]

theorem canonicalActualInteriorStableWord_ne (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    actualStabilizedInteriorWord D pfx G threshold source.anchor ≠ [] := by
  let word := actualStabilizedInteriorWord D pfx G threshold source.anchor
  let ell := actualInteriorBlockScale D pfx G threshold source.anchor
  have hblocks : 0 < (completedGreedyBlocks word ell).length := by
    exact lt_of_le_of_lt (Nat.zero_le source.blockIndex.1)
      source.blockIndex.isLt
  intro hempty
  have hempty' : word = [] := by simpa only [word] using hempty
  rw [hempty'] at hblocks
  simp [completedGreedyBlocks, Erdos260.GapWord.greedyDecompose] at hblocks
  simp [Erdos260.GapWord.greedyDecomposeAux] at hblocks

theorem canonicalActualInteriorBlockStartContinuation_isPrefix_trajectory
    (D : CarrySeries) {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    (canonicalActualInteriorBlockStartContinuation D source).IsPrefix
      (actualInteriorTrajectory D pfx G threshold source.anchor) := by
  let trajectory := actualInteriorTrajectory D pfx G threshold source.anchor
  let pre := actualInteriorAbsorptionPrefix D pfx G threshold source.anchor
  let word := actualStabilizedInteriorWord D pfx G threshold source.anchor
  let before := canonicalActualInteriorBeforeBlock D source
  let through := completedGreedyThrough word
    (actualInteriorBlockScale D pfx G threshold source.anchor)
    source.blockIndex
  have hthrough : through.IsPrefix word :=
    completedGreedyThrough_isPrefix word
      (actualInteriorBlockScale D pfx G threshold source.anchor)
      (actualInteriorBlockScale_pos D pfx G threshold source.anchor)
      source.blockIndex
  have hbeforeThrough : before.IsPrefix through := by
    refine ⟨canonicalActualInteriorBlockWord D source, ?_⟩
    simpa only [before, through, canonicalActualInteriorBeforeBlock,
      canonicalActualInteriorBlockWord] using
      (completedGreedyThrough_eq_append word
        (actualInteriorBlockScale D pfx G threshold source.anchor)
        source.blockIndex).symm
  have hbefore : before.IsPrefix word := hbeforeThrough.trans hthrough
  obtain ⟨tail, htail⟩ := hbefore
  refine ⟨tail, ?_⟩
  change (pre ++ before) ++ tail = trajectory
  rw [List.append_assoc, htail]
  simpa only [pre, word, trajectory, actualInteriorAbsorptionPrefix,
    actualStabilizedInteriorWord, actualInteriorTrajectory] using
    denominatorAbsorptionPrefix_append_suffix trajectory
      (lockedTopStateAbsorption D G).exponent

/-- Every actual prefix of an all-interior trajectory transforms the locked
graph to another graph whose normalized top state is interior. -/
theorem transformActualInteriorTrajectoryPrefix_interiorState
    (D : CarrySeries) (hw : 0 < D.weight.coeff D.weight.natDegree)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (k : ↥(interiorEligibleIndices D N W m bound pfx G threshold))
    (continuation : Erdos260.GapWord)
    (hcontinuation : continuation.IsPrefix
      (actualInteriorTrajectory D pfx G threshold k))
    (htrajectoryNe : actualInteriorTrajectory D pfx G threshold k ≠ []) :
    InteriorState D.base
      ((((G.transformWord D.base D.denominator D.weight le_rfl
        continuation).normalizedTopState D.denominator D.weight : ℚ) : ℝ)) := by
  let post := postLockingWord D.positiveEnumeration k.1 m bound
  let μ : ℝ :=
    (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
  let trajectory := actualInteriorTrajectory D pfx G threshold k
  have hstart : InteriorState D.base μ := by
    exact interiorTrajectory_start htrajectoryNe
  have hlength : continuation.length ≤ trajectory.length :=
    hcontinuation.length_le
  have htake : trajectory.take continuation.length = continuation := by
    exact List.prefix_iff_eq_take.mp hcontinuation |>.symm
  have hreal := interiorTrajectory_state post hstart continuation.length hlength
  change InteriorState D.base
    (topStateAlong D.base (trajectory.take continuation.length) μ) at hreal
  rw [htake] at hreal
  have hA : (D.denominator : ℚ) *
      (D.weight.coeff D.weight.natDegree : ℚ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast D.denominator_pos.ne')
      (by exact_mod_cast hw.ne')
  have hrat := G.normalizedTopState_transformWord D.base D.denominator
    D.weight le_rfl hA continuation
  have hcast := topStateAlongRat_cast D.base continuation
    (G.normalizedTopState D.denominator D.weight)
  rw [← hrat] at hcast
  rw [hcast]
  exact hreal

theorem canonicalActualInteriorBlockStartGraph_interiorState
    (D : CarrySeries) {N W m bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    InteriorState D.base
      ((((canonicalActualInteriorBlockStartGraph D source).normalizedTopState
        D.denominator D.weight : ℚ) : ℝ)) := by
  apply transformActualInteriorTrajectoryPrefix_interiorState D hw
    source.anchor (canonicalActualInteriorBlockStartContinuation D source)
    (canonicalActualInteriorBlockStartContinuation_isPrefix_trajectory D source)
  intro hempty
  apply canonicalActualInteriorStableWord_ne D source
  unfold actualStabilizedInteriorWord denominatorStabilizedSuffix
  rw [hempty]
  rfl

theorem canonicalActualInteriorBlockStartGraph_state_den
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    ((canonicalActualInteriorBlockStartGraph D source).normalizedTopState
      D.denominator D.weight).den =
        actualInteriorDenominator D pfx G threshold source.anchor := by
  let stable := actualStabilizedInteriorGraph
    D pfx G threshold source.anchor
  let before := canonicalActualInteriorBeforeBlock D source
  have hcop : Nat.Coprime D.base
      (stable.normalizedTopState D.denominator D.weight).den := by
    simpa only [stable, actualInteriorDenominator] using
      actualInteriorDenominator_coprime_base D hw hgeom pfx G threshold
        hthreshold source.anchor
  have hden := topStateAlongRat_den_eq D.base before
    (stable.normalizedTopState D.denominator D.weight) hcop
  have hA : (D.denominator : ℚ) *
      (D.weight.coeff D.weight.natDegree : ℚ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast D.denominator_pos.ne')
      (by exact_mod_cast hw.ne')
  have hstate := stable.normalizedTopState_transformWord D.base D.denominator
    D.weight le_rfl hA before
  rw [canonicalActualInteriorBlockStartGraph_eq_stabilized_transform]
  rw [hstate, hden]
  rfl

theorem canonicalActualInteriorBlockContinuation_isPrefix_post
    (D : CarrySeries) {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    (canonicalActualInteriorBlockContinuation D source).IsPrefix
      (postLockingWord D.positiveEnumeration source.anchor.1 m bound) := by
  let post := postLockingWord D.positiveEnumeration source.anchor.1 m bound
  let trajectory := actualInteriorTrajectory D pfx G threshold source.anchor
  let pre := actualInteriorAbsorptionPrefix D pfx G threshold source.anchor
  let word := actualStabilizedInteriorWord D pfx G threshold source.anchor
  let through := completedGreedyThrough word
    (actualInteriorBlockScale D pfx G threshold source.anchor)
    source.blockIndex
  have hthrough : through.IsPrefix word :=
    completedGreedyThrough_isPrefix word
      (actualInteriorBlockScale D pfx G threshold source.anchor)
      (actualInteriorBlockScale_pos D pfx G threshold source.anchor)
      source.blockIndex
  obtain ⟨afterThrough, hafterThrough⟩ := hthrough
  have habsorb : pre ++ word = trajectory := by
    simpa only [pre, word, trajectory, actualInteriorAbsorptionPrefix,
      actualStabilizedInteriorWord, actualInteriorTrajectory] using
      (denominatorAbsorptionPrefix_append_suffix trajectory
        (lockedTopStateAbsorption D G).exponent)
  have hcontinuation : (pre ++ through).IsPrefix trajectory := by
    refine ⟨afterThrough, ?_⟩
    rw [List.append_assoc, hafterThrough, habsorb]
  have htrajectory : trajectory.IsPrefix post := by
    exact interiorTrajectory_isPrefix D.base post
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
  exact hcontinuation.trans htrajectory

/-- Splitting the canonical gap word after a prescribed number of gaps does
not require importing the legacy interior census. -/
theorem enumerationGapWord_append {S : Set ℕ}
    (e : Erdos260.SupportEnumeration S) (i r n : ℕ) :
    Erdos260.enumerationGapWord e i (r + n) =
      Erdos260.enumerationGapWord e i r ++
        Erdos260.enumerationGapWord e (i + r) n := by
  induction r generalizing i with
  | zero => simp [Erdos260.enumerationGapWord]
  | succ r ih =>
      rw [show r + 1 + n = (r + n) + 1 by omega,
        Erdos260.enumerationGapWord_succ,
        Erdos260.enumerationGapWord_succ, ih]
      congr 1
      simp [Nat.add_comm, Nat.add_left_comm]

theorem prefix_forwardGapWord_eq_enumerationGapWord {S : Set ℕ}
    (e : Erdos260.SupportEnumeration S) (k m : ℕ)
    (word : Erdos260.GapWord)
    (hword : word.IsPrefix (forwardGapWord e k m)) :
    word = Erdos260.enumerationGapWord e k word.length := by
  have hlen : word.length ≤ m := by
    simpa only [forwardGapWord_length] using hword.length_le
  have hcanonical :
      (Erdos260.enumerationGapWord e k word.length).IsPrefix
        (Erdos260.enumerationGapWord e k m) := by
    rw [show m = word.length + (m - word.length) by omega,
      enumerationGapWord_append]
    exact List.prefix_append _ _
  have hwordTake := List.prefix_iff_eq_take.mp hword
  have hcanonicalTake := List.prefix_iff_eq_take.mp hcanonical
  have hcanonicalLength :
      (Erdos260.enumerationGapWord e k word.length).length = word.length := by
    simp [Erdos260.enumerationGapWord]
  calc
    word = (forwardGapWord e k m).take word.length := hwordTake
    _ = (Erdos260.enumerationGapWord e k m).take word.length := rfl
    _ = (Erdos260.enumerationGapWord e k m).take
        (Erdos260.enumerationGapWord e k word.length).length := by
      rw [hcanonicalLength]
    _ = Erdos260.enumerationGapWord e k word.length := hcanonicalTake.symm

theorem canonicalActualInteriorBlockEndpoint_coordinate (D : CarrySeries)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    D.positiveEnumeration.a source.anchor.1 +
        Erdos260.GapWord.span
          (lockingPrefix D.positiveEnumeration source.anchor.1 m bound) +
        Erdos260.GapWord.span
          (canonicalActualInteriorBlockContinuation D source) =
      D.positiveEnumeration.a
        (actualInteriorBlockSourceEndpointIndex D source) := by
  let lock := lockingPrefix D.positiveEnumeration source.anchor.1 m bound
  let continuation := canonicalActualInteriorBlockContinuation D source
  let full := lock ++ continuation
  have hcontinuation :=
    canonicalActualInteriorBlockContinuation_isPrefix_post D source
  obtain ⟨tail, htail⟩ := hcontinuation
  have hfull : full.IsPrefix
      (forwardGapWord D.positiveEnumeration source.anchor.1 m) := by
    refine ⟨tail, ?_⟩
    dsimp only [full]
    rw [List.append_assoc, htail,
      lockingPrefix_append_postLockingWord]
  have hcanonical := prefix_forwardGapWord_eq_enumerationGapWord
    D.positiveEnumeration source.anchor.1 m full hfull
  have hspan := Erdos260.enumerationGapWord_span D.positiveEnumeration
    source.anchor.1 full.length
  have hmono : D.positiveEnumeration.a source.anchor.1 ≤
      D.positiveEnumeration.a (source.anchor.1 + full.length) :=
    D.positiveEnumeration.strictMono.monotone (Nat.le_add_right _ _)
  have hendpoint : source.anchor.1 + full.length =
      actualInteriorBlockSourceEndpointIndex D source := by
    unfold actualInteriorBlockSourceEndpointIndex
      actualInteriorBlockEndpointIndex
    simp only [full, lock, continuation,
      canonicalActualInteriorBlockContinuation, List.length_append]
    omega
  have hfullSpan :
      Erdos260.GapWord.span full =
        D.positiveEnumeration.a (source.anchor.1 + full.length) -
          D.positiveEnumeration.a source.anchor.1 := by
    calc
      Erdos260.GapWord.span full =
          Erdos260.GapWord.span
            (Erdos260.enumerationGapWord D.positiveEnumeration
              source.anchor.1 full.length) := congrArg Erdos260.GapWord.span hcanonical
      _ = D.positiveEnumeration.a (source.anchor.1 + full.length) -
          D.positiveEnumeration.a source.anchor.1 := hspan
  calc
    D.positiveEnumeration.a source.anchor.1 +
          Erdos260.GapWord.span lock +
          Erdos260.GapWord.span continuation =
        D.positiveEnumeration.a source.anchor.1 +
          Erdos260.GapWord.span full := by
      simp only [full, Erdos260.GapWord.span, List.sum_append]
      omega
    _ = D.positiveEnumeration.a source.anchor.1 +
        (D.positiveEnumeration.a (source.anchor.1 + full.length) -
          D.positiveEnumeration.a source.anchor.1) := by
      rw [hfullSpan]
    _ = D.positiveEnumeration.a (source.anchor.1 + full.length) :=
      Nat.add_sub_of_le hmono
    _ = D.positiveEnumeration.a
        (actualInteriorBlockSourceEndpointIndex D source) := by rw [hendpoint]

/-- A locked graph evaluated along the genuine continuation reaches the
actual carry point at the canonical retained-block endpoint. -/
theorem canonicalActualInteriorBlockEndGraph_eval_carry
    (D : CarrySeries) {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (hfit : ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
      G.poly.eval ((x + Erdos260.GapWord.span pfx : ℕ) : ℚ) =
        (D.carry (x + Erdos260.GapWord.span pfx) : ℚ))
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    (canonicalActualInteriorBlockEndGraph D source).poly.eval
        (D.positiveEnumeration.a
          (actualInteriorBlockSourceEndpointIndex D source) : ℚ) =
      (D.carry (D.positiveEnumeration.a
        (actualInteriorBlockSourceEndpointIndex D source)) : ℚ) := by
  let lock := lockingPrefix D.positiveEnumeration source.anchor.1 m bound
  let continuation := canonicalActualInteriorBlockContinuation D source
  have hkRealized : source.anchor.1 ∈
      realizedPrefixIndices D N W m bound pfx :=
    (Finset.mem_filter.mp source.anchor.2).1
  have hpfx : lock = pfx := by
    exact (Finset.mem_filter.mp hkRealized).2
  have hanchor : D.positiveEnumeration.a source.anchor.1 ∈
      realizedPrefixAnchors D N W m bound pfx := by
    rw [realizedPrefixAnchors, Finset.mem_image]
    exact ⟨source.anchor.1, hkRealized, rfl⟩
  have hstart :
      G.poly.eval
          (((D.positiveEnumeration.a source.anchor.1 +
            Erdos260.GapWord.span lock : ℕ)) : ℚ) =
        (D.carry (D.positiveEnumeration.a source.anchor.1 +
          Erdos260.GapWord.span lock) : ℚ) := by
    simpa only [hpfx] using
      hfit (D.positiveEnumeration.a source.anchor.1) hanchor
  have hactual : D.GapWordAt
      (D.positiveEnumeration.a source.anchor.1 +
        Erdos260.GapWord.span lock) continuation := by
    exact CarrySeries.GapWordAt.prefix
      (canonicalActualInteriorBlockContinuation_isPrefix_post D source)
      (postLockingWord_gapWordAt D source.anchor.1 m bound)
  have hcontinued := G.transformWord_eval_carry D hstart hactual
  have hcoordinate := canonicalActualInteriorBlockEndpoint_coordinate D source
  change
    (G.transformWord D.base D.denominator D.weight le_rfl continuation).poly.eval
        (D.positiveEnumeration.a
          (actualInteriorBlockSourceEndpointIndex D source) : ℚ) =
      (D.carry (D.positiveEnumeration.a
        (actualInteriorBlockSourceEndpointIndex D source)) : ℚ)
  rw [← hcoordinate]
  simpa only [Nat.cast_add, add_assoc, lock, continuation] using hcontinued

/-- The unused stabilized suffix is the genuine support-gap word beginning
at the canonical block endpoint. -/
theorem canonicalActualInteriorAfterBlock_gapWordAt
    (D : CarrySeries) {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    D.GapWordAt
      (D.positiveEnumeration.a
        (actualInteriorBlockSourceEndpointIndex D source))
      (canonicalActualInteriorAfterBlock D source) := by
  let lock := lockingPrefix D.positiveEnumeration source.anchor.1 m bound
  let post := postLockingWord D.positiveEnumeration source.anchor.1 m bound
  let trajectory := actualInteriorTrajectory D pfx G threshold source.anchor
  let pre := actualInteriorAbsorptionPrefix D pfx G threshold source.anchor
  let word := actualStabilizedInteriorWord D pfx G threshold source.anchor
  let through := completedGreedyThrough word
    (actualInteriorBlockScale D pfx G threshold source.anchor)
    source.blockIndex
  let continuation := canonicalActualInteriorBlockContinuation D source
  let after := canonicalActualInteriorAfterBlock D source
  have htrajectoryPost : trajectory.IsPrefix post := by
    exact interiorTrajectory_isPrefix D.base post
      (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
  have htrajectoryAt : D.GapWordAt
      (D.positiveEnumeration.a source.anchor.1 + Erdos260.GapWord.span lock)
      trajectory := CarrySeries.GapWordAt.prefix htrajectoryPost
        (postLockingWord_gapWordAt D source.anchor.1 m bound)
  have hthroughAfter : through ++ after = word := by
    simpa only [through, after, word] using
      canonicalActualInteriorThrough_append_afterBlock D source
  have habsorb : pre ++ word = trajectory := by
    simpa only [pre, word, trajectory, actualInteriorAbsorptionPrefix,
      actualStabilizedInteriorWord, actualInteriorTrajectory] using
      denominatorAbsorptionPrefix_append_suffix trajectory
        (lockedTopStateAbsorption D G).exponent
  have hcombined : continuation ++ after = trajectory := by
    change (pre ++ through) ++ after = trajectory
    rw [List.append_assoc, hthroughAfter, habsorb]
  have hcombinedAt : D.GapWordAt
      (D.positiveEnumeration.a source.anchor.1 + Erdos260.GapWord.span lock)
      (continuation ++ after) := by
    rw [hcombined]
    exact htrajectoryAt
  have htail :=
    (CarrySeries.GapWordAt.append_iff continuation after).mp hcombinedAt |>.2
  have hcoordinate := canonicalActualInteriorBlockEndpoint_coordinate D source
  rw [← hcoordinate]
  simpa only [lock, continuation, after, add_assoc] using htail

theorem canonicalActualInteriorFutureWord_gapWordAt
    (D : CarrySeries) {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold F : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    D.GapWordAt
      (D.positiveEnumeration.a
        (actualInteriorBlockSourceEndpointIndex D source))
      (canonicalActualInteriorFutureWord D source F) := by
  exact CarrySeries.GapWordAt.prefix
    (Erdos260.GapWord.firstPrefixAbove_isPrefix
      (canonicalActualInteriorAfterBlock D source) F)
    (canonicalActualInteriorAfterBlock_gapWordAt D source)

/-- Continuing a retained block-end graph along its actual future word again
lands on the genuine carry graph. -/
theorem canonicalActualInteriorFutureGraph_eval_carry
    (D : CarrySeries) {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold F : ℕ}
    (hfit : ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
      G.poly.eval ((x + Erdos260.GapWord.span pfx : ℕ) : ℚ) =
        (D.carry (x + Erdos260.GapWord.span pfx) : ℚ))
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    let endpoint := D.positiveEnumeration.a
      (actualInteriorBlockSourceEndpointIndex D source)
    let future := canonicalActualInteriorFutureWord D source F
    (((canonicalActualInteriorBlockEndGraph D source).transformWord
      D.base D.denominator D.weight le_rfl future).poly.eval
        ((endpoint + Erdos260.GapWord.span future : ℕ) : ℚ)) =
      (D.carry (endpoint + Erdos260.GapWord.span future) : ℚ) := by
  let endpoint := D.positiveEnumeration.a
    (actualInteriorBlockSourceEndpointIndex D source)
  let future := canonicalActualInteriorFutureWord D source F
  have hstart := canonicalActualInteriorBlockEndGraph_eval_carry
    D hfit source
  have hword := canonicalActualInteriorFutureWord_gapWordAt
    D (F := F) source
  simpa only [endpoint, future] using
    (canonicalActualInteriorBlockEndGraph D source).transformWord_eval_carry
      D hstart hword

/-- A deep future sample remains in one explicit common polynomial-size
coordinate interval. -/
theorem canonicalActualInteriorFutureTerminal_bounds
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold F : ℕ}
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold)
    (hdeep : source.Deep D F) :
    let endpoint := D.positiveEnumeration.a
      (actualInteriorBlockSourceEndpointIndex D source)
    let future := canonicalActualInteriorFutureWord D source F
    N < endpoint + Erdos260.GapWord.span future ∧
      endpoint + Erdos260.GapWord.span future ≤
        N + W + m * cap + F +
          actualInteriorBlockScale D pfx G threshold source.anchor := by
  let endpoint := D.positiveEnumeration.a
    (actualInteriorBlockSourceEndpointIndex D source)
  let future := canonicalActualInteriorFutureWord D source F
  have hendpoint := Finset.mem_Ioc.mp
    (canonicalActualInteriorBlockSource_endpoint_mem D hgeom source)
  have hfuture := canonicalActualInteriorFutureWord_bounds
    D hw hgeom hthreshold source hdeep
  dsimp only [endpoint, future]
  constructor
  · exact hendpoint.1.trans_le (Nat.le_add_right _ _)
  · have hadd := Nat.add_le_add hendpoint.2 hfuture.2.2.1
    simpa only [Nat.add_assoc] using hadd

/-- Polynomial carry height at a deep future sample. -/
theorem canonicalActualInteriorFutureTerminal_carry_bound
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hpositiveFrom : D.positiveFrom ≤ N)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold F : ℕ}
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold)
    (hdeep : source.Deep D F) :
    let endpoint := D.positiveEnumeration.a
      (actualInteriorBlockSourceEndpointIndex D source)
    let future := canonicalActualInteriorFutureWord D source F
    (D.carry (endpoint + Erdos260.GapWord.span future)).natAbs ≤
      D.heightNatConstant *
        (N + W + m * cap + F +
          actualInteriorBlockScale D pfx G threshold source.anchor + 1) ^
            D.weight.natDegree := by
  let endpoint := D.positiveEnumeration.a
    (actualInteriorBlockSourceEndpointIndex D source)
  let future := canonicalActualInteriorFutureWord D source F
  let terminal := endpoint + Erdos260.GapWord.span future
  have hbounds := canonicalActualInteriorFutureTerminal_bounds
    D hw hgeom hthreshold source hdeep
  have hbounds' : N < terminal ∧ terminal ≤
      N + W + m * cap + F +
        actualInteriorBlockScale D pfx G threshold source.anchor := by
    simpa only [endpoint, future, terminal] using hbounds
  have hcarry := D.carry_natAbs_le (hpositiveFrom.trans hbounds'.1.le)
  have hpow : (terminal + 1) ^ D.weight.natDegree ≤
      (N + W + m * cap + F +
        actualInteriorBlockScale D pfx G threshold source.anchor + 1) ^
          D.weight.natDegree :=
    Nat.pow_le_pow_left (Nat.add_le_add_right hbounds'.2 1) _
  have hscaled := Nat.mul_le_mul_left D.heightNatConstant hpow
  simpa only [endpoint, future, terminal] using hcarry.trans hscaled

theorem canonicalActualInteriorBlockEndGraph_interiorState
    (D : CarrySeries) {N W m bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    InteriorState D.base
      ((((canonicalActualInteriorBlockEndGraph D source).normalizedTopState
        D.denominator D.weight : ℚ) : ℝ)) := by
  let post := postLockingWord D.positiveEnumeration source.anchor.1 m bound
  let μ : ℝ :=
    (((G.normalizedTopState D.denominator D.weight : ℚ) : ℝ))
  let trajectory := actualInteriorTrajectory D pfx G threshold source.anchor
  let continuation := canonicalActualInteriorBlockContinuation D source
  have hcontinuation : continuation.IsPrefix trajectory := by
    let pre := actualInteriorAbsorptionPrefix D pfx G threshold source.anchor
    let word := actualStabilizedInteriorWord D pfx G threshold source.anchor
    let through := completedGreedyThrough word
      (actualInteriorBlockScale D pfx G threshold source.anchor)
      source.blockIndex
    have hthrough : through.IsPrefix word :=
      completedGreedyThrough_isPrefix word
        (actualInteriorBlockScale D pfx G threshold source.anchor)
        (actualInteriorBlockScale_pos D pfx G threshold source.anchor)
        source.blockIndex
    obtain ⟨afterThrough, hafterThrough⟩ := hthrough
    refine ⟨afterThrough, ?_⟩
    have habsorb := denominatorAbsorptionPrefix_append_suffix trajectory
      (lockedTopStateAbsorption D G).exponent
    change (pre ++ through) ++ afterThrough = trajectory
    rw [List.append_assoc, hafterThrough]
    simpa only [pre, word, trajectory, actualInteriorAbsorptionPrefix,
      actualStabilizedInteriorWord, actualInteriorTrajectory] using habsorb
  have hwordNe : actualStabilizedInteriorWord D pfx G threshold source.anchor ≠
      [] := by
    let word := actualStabilizedInteriorWord D pfx G threshold source.anchor
    let ell := actualInteriorBlockScale D pfx G threshold source.anchor
    have hblocks : 0 < (completedGreedyBlocks word ell).length := by
      exact lt_of_le_of_lt (Nat.zero_le source.blockIndex.1)
        source.blockIndex.isLt
    intro hempty
    have hempty' : word = [] := by simpa only [word] using hempty
    rw [hempty'] at hblocks
    simp [completedGreedyBlocks, Erdos260.GapWord.greedyDecompose] at hblocks
    simp [Erdos260.GapWord.greedyDecomposeAux] at hblocks
  have htrajectoryNe : trajectory ≠ [] := by
    intro hempty
    apply hwordNe
    unfold actualStabilizedInteriorWord denominatorStabilizedSuffix
    have hempty' : actualInteriorTrajectory D pfx G threshold source.anchor =
        [] := by simpa only [trajectory] using hempty
    rw [hempty']
    rfl
  have hstart : InteriorState D.base μ := by
    exact interiorTrajectory_start htrajectoryNe
  have hlength : continuation.length ≤ trajectory.length :=
    hcontinuation.length_le
  have htake : trajectory.take continuation.length = continuation := by
    exact List.prefix_iff_eq_take.mp hcontinuation |>.symm
  have hreal := interiorTrajectory_state post hstart continuation.length hlength
  change InteriorState D.base
    (topStateAlong D.base (trajectory.take continuation.length) μ) at hreal
  rw [htake] at hreal
  have hA : (D.denominator : ℚ) *
      (D.weight.coeff D.weight.natDegree : ℚ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast D.denominator_pos.ne')
      (by exact_mod_cast hw.ne')
  have hrat := G.normalizedTopState_transformWord D.base D.denominator
    D.weight le_rfl hA continuation
  have hcast := topStateAlongRat_cast D.base continuation
    (G.normalizedTopState D.denominator D.weight)
  rw [← hrat] at hcast
  change InteriorState D.base
    ((((G.transformWord D.base D.denominator D.weight le_rfl continuation).normalizedTopState
      D.denominator D.weight : ℚ) : ℝ))
  rw [hcast]
  exact hreal

/-- The unused word after an actual retained block is the canonical interior
trajectory from the exact rational state of its block-end graph.  Thus its
future depends only on that state, not on the occurrence used to expose it. -/
theorem canonicalActualInteriorAfterBlock_eq_interiorTrajectory
    (D : CarrySeries) (hw : 0 < D.weight.coeff D.weight.natDegree)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    interiorTrajectory D.base (canonicalActualInteriorAfterBlock D source)
        (((((canonicalActualInteriorBlockEndGraph D source).normalizedTopState
          D.denominator D.weight : ℚ) : ℝ))) =
      canonicalActualInteriorAfterBlock D source := by
  let continuation := canonicalActualInteriorBlockContinuation D source
  let after := canonicalActualInteriorAfterBlock D source
  let trajectory := actualInteriorTrajectory D pfx G threshold source.anchor
  let endGraph := canonicalActualInteriorBlockEndGraph D source
  apply interiorTrajectory_eq_self_of_prefix_states
  intro i hi
  have htakePrefix : (after.take i).IsPrefix after := List.take_prefix i after
  obtain ⟨tail, htail⟩ := htakePrefix
  have hcombinedPrefix : (continuation ++ after.take i).IsPrefix trajectory := by
    refine ⟨tail, ?_⟩
    rw [List.append_assoc, htail]
    simpa only [continuation, after, trajectory] using
      canonicalActualInteriorBlockContinuation_append_afterBlock D source
  have htrajectoryNe : trajectory ≠ [] := by
    intro hempty
    apply canonicalActualInteriorStableWord_ne D source
    unfold actualStabilizedInteriorWord denominatorStabilizedSuffix
    have hempty' : actualInteriorTrajectory D pfx G threshold source.anchor =
        [] := by simpa only [trajectory] using hempty
    rw [hempty']
    rfl
  have hstate := transformActualInteriorTrajectoryPrefix_interiorState
    D hw source.anchor (continuation ++ after.take i) hcombinedPrefix htrajectoryNe
  have hstateEnd : InteriorState D.base
      (↑((endGraph.transformWord D.base D.denominator D.weight le_rfl
        (after.take i)).normalizedTopState D.denominator D.weight)) := by
    change InteriorState D.base
      (↑(((G.transformWord D.base D.denominator D.weight le_rfl
          continuation).transformWord D.base D.denominator D.weight le_rfl
          (after.take i)).normalizedTopState D.denominator D.weight))
    rw [← G.transformWord_append]
    exact hstate
  have hA : (D.denominator : ℚ) *
      (D.weight.coeff D.weight.natDegree : ℚ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast D.denominator_pos.ne')
      (by exact_mod_cast hw.ne')
  have hrat := endGraph.normalizedTopState_transformWord D.base
    D.denominator D.weight le_rfl hA (after.take i)
  have hcast := topStateAlongRat_cast D.base (after.take i)
    (endGraph.normalizedTopState D.denominator D.weight)
  rw [← hrat] at hcast
  rw [← hcast]
  exact hstateEnd

/-- The coprime denominator of the stabilized state is preserved through an
actual retained block. -/
theorem canonicalActualInteriorBlockEndGraph_state_den
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold : ℕ}
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    ((canonicalActualInteriorBlockEndGraph D source).normalizedTopState
      D.denominator D.weight).den =
        actualInteriorDenominator D pfx G threshold source.anchor := by
  let startGraph := canonicalActualInteriorBlockStartGraph D source
  let block := canonicalActualInteriorBlockWord D source
  have hstartDen := canonicalActualInteriorBlockStartGraph_state_den
    D hw hgeom hthreshold source
  have hcopActual := actualInteriorDenominator_coprime_base
    D hw hgeom pfx G threshold hthreshold source.anchor
  have hcopStart : Nat.Coprime D.base
      (startGraph.normalizedTopState D.denominator D.weight).den := by
    simpa only [startGraph, hstartDen] using hcopActual
  have hden := topStateAlongRat_den_eq D.base block
    (startGraph.normalizedTopState D.denominator D.weight) hcopStart
  have hA : (D.denominator : ℚ) *
      (D.weight.coeff D.weight.natDegree : ℚ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast D.denominator_pos.ne')
      (by exact_mod_cast hw.ne')
  have hstate := startGraph.normalizedTopState_transformWord
    D.base D.denominator D.weight le_rfl hA block
  rw [canonicalActualInteriorBlockEndGraph_eq_transform_start, hstate,
    hden, hstartDen]

/-- Every selected deep future ends at another strictly interior state. -/
theorem canonicalActualInteriorFutureGraph_interiorState
    (D : CarrySeries) (hw : 0 < D.weight.coeff D.weight.natDegree)
    {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold F : ℕ}
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    InteriorState D.base
      (((((canonicalActualInteriorBlockEndGraph D source).transformWord
        D.base D.denominator D.weight le_rfl
          (canonicalActualInteriorFutureWord D source F)).normalizedTopState
            D.denominator D.weight : ℚ) : ℝ)) := by
  let endGraph := canonicalActualInteriorBlockEndGraph D source
  let after := canonicalActualInteriorAfterBlock D source
  let future := canonicalActualInteriorFutureWord D source F
  let μ : ℝ := ((endGraph.normalizedTopState
    D.denominator D.weight : ℚ) : ℝ)
  have hcanonical : interiorTrajectory D.base after μ = after := by
    simpa only [endGraph, after, μ] using
      canonicalActualInteriorAfterBlock_eq_interiorTrajectory D hw source
  have hstart : InteriorState D.base μ := by
    simpa only [endGraph, μ] using
      canonicalActualInteriorBlockEndGraph_interiorState D hw source
  have hprefix : future.IsPrefix after := by
    exact Erdos260.GapWord.firstPrefixAbove_isPrefix after F
  have hlength : future.length ≤
      (interiorTrajectory D.base after μ).length := by
    rw [hcanonical]
    exact hprefix.length_le
  have hstate := interiorTrajectory_state after hstart future.length hlength
  have htake : (interiorTrajectory D.base after μ).take future.length =
      future := by
    rw [hcanonical]
    exact List.prefix_iff_eq_take.mp hprefix |>.symm
  change InteriorState D.base
    (topStateAlong D.base
      ((interiorTrajectory D.base after μ).take future.length) μ) at hstate
  rw [htake] at hstate
  have hA : (D.denominator : ℚ) *
      (D.weight.coeff D.weight.natDegree : ℚ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast D.denominator_pos.ne')
      (by exact_mod_cast hw.ne')
  have hrat := endGraph.normalizedTopState_transformWord D.base
    D.denominator D.weight le_rfl hA future
  have hcast := topStateAlongRat_cast D.base future
    (endGraph.normalizedTopState D.denominator D.weight)
  rw [← hrat] at hcast
  simpa only [endGraph, future] using hcast ▸ hstate

/-- The coprime denominator is also preserved through the selected deep
future word. -/
theorem canonicalActualInteriorFutureGraph_state_den
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold F : ℕ}
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    (((canonicalActualInteriorBlockEndGraph D source).transformWord
      D.base D.denominator D.weight le_rfl
        (canonicalActualInteriorFutureWord D source F)).normalizedTopState
          D.denominator D.weight).den =
      actualInteriorDenominator D pfx G threshold source.anchor := by
  let endGraph := canonicalActualInteriorBlockEndGraph D source
  let future := canonicalActualInteriorFutureWord D source F
  have hendDen := canonicalActualInteriorBlockEndGraph_state_den
    D hw hgeom hthreshold source
  have hcopActual := actualInteriorDenominator_coprime_base
    D hw hgeom pfx G threshold hthreshold source.anchor
  have hcopEnd : Nat.Coprime D.base
      (endGraph.normalizedTopState D.denominator D.weight).den := by
    simpa only [endGraph, hendDen] using hcopActual
  have hden := topStateAlongRat_den_eq D.base future
    (endGraph.normalizedTopState D.denominator D.weight) hcopEnd
  have hA : (D.denominator : ℚ) *
      (D.weight.coeff D.weight.natDegree : ℚ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast D.denominator_pos.ne')
      (by exact_mod_cast hw.ne')
  have hstate := endGraph.normalizedTopState_transformWord D.base
    D.denominator D.weight le_rfl hA future
  simp only [endGraph, future, hstate, hden, hendDen]

/-- A block word together with its dyadic denominator band determines the
exact rational state at the start of every actual retained occurrence. -/
theorem canonicalActualInteriorBlockStartState_eq_of_code
    (D : CarrySeries) {N W m cap bound threshold : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    {leftPrefix rightPrefix : Erdos260.GapWord}
    {leftGraph rightGraph : PolynomialGraph D.weight.natDegree}
    (hleftThreshold : Nat.log 2
        (leftGraph.normalizedTopState D.denominator D.weight).den + cap ≤
          threshold)
    (hrightThreshold : Nat.log 2
        (rightGraph.normalizedTopState D.denominator D.weight).den + cap ≤
          threshold)
    (left : CanonicalActualInteriorBlockSource
      D N W m bound leftPrefix leftGraph threshold)
    (right : CanonicalActualInteriorBlockSource
      D N W m bound rightPrefix rightGraph threshold)
    (hword : canonicalActualInteriorBlockWord D left =
      canonicalActualInteriorBlockWord D right)
    (hband : dyadicFloorBand
        (actualInteriorDenominator D leftPrefix leftGraph threshold left.anchor) =
      dyadicFloorBand
        (actualInteriorDenominator D rightPrefix rightGraph threshold right.anchor))
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span (canonicalActualInteriorBlockWord D left)) <
        1 / (4 * (dyadicFloorBand
          (actualInteriorDenominator D leftPrefix leftGraph threshold
            left.anchor) : ℝ) ^ 2)) :
    (canonicalActualInteriorBlockStartGraph D left).normalizedTopState
        D.denominator D.weight =
      (canonicalActualInteriorBlockStartGraph D right).normalizedTopState
        D.denominator D.weight := by
  let Dband := dyadicFloorBand
    (actualInteriorDenominator D leftPrefix leftGraph threshold left.anchor)
  have hleftDen := canonicalActualInteriorBlockStartGraph_state_den
    D hw hgeom hleftThreshold left
  have hrightDen := canonicalActualInteriorBlockStartGraph_state_den
    D hw hgeom hrightThreshold right
  have hleftBand :=
    (actualInteriorDenominator_band D hw hgeom leftPrefix leftGraph threshold
      hleftThreshold left.anchor).2
  have hrightBandRaw :=
    (actualInteriorDenominator_band D hw hgeom rightPrefix rightGraph threshold
      hrightThreshold right.anchor).2
  have hrightBand :
      ((canonicalActualInteriorBlockStartGraph D right).normalizedTopState
          D.denominator D.weight).den < 2 * Dband := by
    rw [hrightDen]
    simpa only [Dband, hband] using hrightBandRaw
  have hleftBand' :
      ((canonicalActualInteriorBlockStartGraph D left).normalizedTopState
          D.denominator D.weight).den < 2 * Dband := by
    rw [hleftDen]
    simpa only [Dband] using hleftBand
  have hleftEnd : InteriorState D.base
      (((((canonicalActualInteriorBlockStartGraph D left).transformWord
        D.base D.denominator D.weight le_rfl
          (canonicalActualInteriorBlockWord D left)).normalizedTopState
            D.denominator D.weight : ℚ) : ℝ)) := by
    rw [← canonicalActualInteriorBlockEndGraph_eq_transform_start]
    exact canonicalActualInteriorBlockEndGraph_interiorState D hw left
  have hrightEnd : InteriorState D.base
      (((((canonicalActualInteriorBlockStartGraph D right).transformWord
        D.base D.denominator D.weight le_rfl
          (canonicalActualInteriorBlockWord D left)).normalizedTopState
            D.denominator D.weight : ℚ) : ℝ)) := by
    rw [hword]
    rw [← canonicalActualInteriorBlockEndGraph_eq_transform_start]
    exact canonicalActualInteriorBlockEndGraph_interiorState D hw right
  have hA : (D.denominator : ℚ) *
      (D.weight.coeff D.weight.natDegree : ℚ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast D.denominator_pos.ne')
      (by exact_mod_cast hw.ne')
  exact PolynomialGraph.normalizedTopState_eq_of_commonInteriorBlock
    D.base_ge_two D.weight le_rfl hA
    (canonicalActualInteriorBlockStartGraph D left)
    (canonicalActualInteriorBlockStartGraph D right)
    (canonicalActualInteriorBlockWord D left)
    hleftBand' hrightBand hleftEnd hrightEnd (by simpa only [Dband] using hshort)

/-- The same block code also determines the exact normalized state after the
block. -/
theorem canonicalActualInteriorBlockEndState_eq_of_code
    (D : CarrySeries) {N W m cap bound threshold : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    {leftPrefix rightPrefix : Erdos260.GapWord}
    {leftGraph rightGraph : PolynomialGraph D.weight.natDegree}
    (hleftThreshold : Nat.log 2
        (leftGraph.normalizedTopState D.denominator D.weight).den + cap ≤
          threshold)
    (hrightThreshold : Nat.log 2
        (rightGraph.normalizedTopState D.denominator D.weight).den + cap ≤
          threshold)
    (left : CanonicalActualInteriorBlockSource
      D N W m bound leftPrefix leftGraph threshold)
    (right : CanonicalActualInteriorBlockSource
      D N W m bound rightPrefix rightGraph threshold)
    (hword : canonicalActualInteriorBlockWord D left =
      canonicalActualInteriorBlockWord D right)
    (hband : dyadicFloorBand
        (actualInteriorDenominator D leftPrefix leftGraph threshold left.anchor) =
      dyadicFloorBand
        (actualInteriorDenominator D rightPrefix rightGraph threshold right.anchor))
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span (canonicalActualInteriorBlockWord D left)) <
        1 / (4 * (dyadicFloorBand
          (actualInteriorDenominator D leftPrefix leftGraph threshold
            left.anchor) : ℝ) ^ 2)) :
    (canonicalActualInteriorBlockEndGraph D left).normalizedTopState
        D.denominator D.weight =
      (canonicalActualInteriorBlockEndGraph D right).normalizedTopState
        D.denominator D.weight := by
  have hstart := canonicalActualInteriorBlockStartState_eq_of_code
    D hw hgeom hleftThreshold hrightThreshold left right hword hband hshort
  have hA : (D.denominator : ℚ) *
      (D.weight.coeff D.weight.natDegree : ℚ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast D.denominator_pos.ne')
      (by exact_mod_cast hw.ne')
  rw [canonicalActualInteriorBlockEndGraph_eq_transform_start,
    canonicalActualInteriorBlockEndGraph_eq_transform_start]
  have hleftTransform := PolynomialGraph.normalizedTopState_transformWord
    (canonicalActualInteriorBlockStartGraph D left) D.base D.denominator
      D.weight le_rfl hA (canonicalActualInteriorBlockWord D left)
  have hrightTransform := PolynomialGraph.normalizedTopState_transformWord
    (canonicalActualInteriorBlockStartGraph D right) D.base D.denominator
      D.weight le_rfl hA (canonicalActualInteriorBlockWord D right)
  rw [hleftTransform, hrightTransform, hword, hstart]

/-- Deep retained sources with the same block and denominator-band code have
the same canonical high-frequency future word. -/
theorem canonicalActualInteriorFutureWord_eq_of_code
    (D : CarrySeries) {N W m cap bound threshold F : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    {leftPrefix rightPrefix : Erdos260.GapWord}
    {leftGraph rightGraph : PolynomialGraph D.weight.natDegree}
    (hleftThreshold : Nat.log 2
        (leftGraph.normalizedTopState D.denominator D.weight).den + cap ≤
          threshold)
    (hrightThreshold : Nat.log 2
        (rightGraph.normalizedTopState D.denominator D.weight).den + cap ≤
          threshold)
    (left : CanonicalActualInteriorBlockSource
      D N W m bound leftPrefix leftGraph threshold)
    (right : CanonicalActualInteriorBlockSource
      D N W m bound rightPrefix rightGraph threshold)
    (hleftDeep : left.Deep D F) (hrightDeep : right.Deep D F)
    (hword : canonicalActualInteriorBlockWord D left =
      canonicalActualInteriorBlockWord D right)
    (hband : dyadicFloorBand
        (actualInteriorDenominator D leftPrefix leftGraph threshold left.anchor) =
      dyadicFloorBand
        (actualInteriorDenominator D rightPrefix rightGraph threshold right.anchor))
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span (canonicalActualInteriorBlockWord D left)) <
        1 / (4 * (dyadicFloorBand
          (actualInteriorDenominator D leftPrefix leftGraph threshold
            left.anchor) : ℝ) ^ 2)) :
    canonicalActualInteriorFutureWord D left F =
      canonicalActualInteriorFutureWord D right F := by
  let leftAfter := canonicalActualInteriorAfterBlock D left
  let rightAfter := canonicalActualInteriorAfterBlock D right
  let μ : ℝ := ((PolynomialGraph.normalizedTopState
    (canonicalActualInteriorBlockEndGraph D left)
      D.denominator D.weight : ℚ) : ℝ)
  have hstateRat := canonicalActualInteriorBlockEndState_eq_of_code
    D hw hgeom hleftThreshold hrightThreshold left right hword hband hshort
  have hstateReal : μ = ((PolynomialGraph.normalizedTopState
      (canonicalActualInteriorBlockEndGraph D right)
        D.denominator D.weight : ℚ) : ℝ) := by
    dsimp only [μ]
    exact congrArg (fun q : ℚ => (q : ℝ)) hstateRat
  have hleftCanonical : interiorTrajectory D.base leftAfter μ = leftAfter := by
    simpa only [leftAfter, μ] using
      canonicalActualInteriorAfterBlock_eq_interiorTrajectory D hw left
  have hrightCanonical : interiorTrajectory D.base rightAfter μ = rightAfter := by
    rw [hstateReal]
    simpa only [rightAfter] using
      canonicalActualInteriorAfterBlock_eq_interiorTrajectory D hw right
  have hleftPositive : Erdos260.GapWord.Positive leftAfter := by
    intro g hg
    apply actualStabilizedInteriorWord_positive
      D leftPrefix leftGraph threshold left.anchor g
    exact List.mem_of_mem_drop hg
  have hrightPositive : Erdos260.GapWord.Positive rightAfter := by
    intro g hg
    apply actualStabilizedInteriorWord_positive
      D rightPrefix rightGraph threshold right.anchor g
    exact List.mem_of_mem_drop hg
  have hpref := interiorTrajectory_prefix_or_prefix D.base_ge_two
    leftAfter rightAfter μ hleftPositive hrightPositive
  rw [hleftCanonical, hrightCanonical] at hpref
  unfold canonicalActualInteriorFutureWord
  rcases hpref with hpref | hpref
  · exact firstPrefixAbove_eq_of_prefix hpref hleftDeep
  · exact (firstPrefixAbove_eq_of_prefix hpref hrightDeep).symm

/-! ## Actual high-frequency cells -/

/-- All deep retained occurrences in one locked fibre that have the same
block code, denominator band, and exact block-end polynomial as a chosen
representative. -/
noncomputable def canonicalActualInteriorGraphSources (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold F : ℕ)
    (representative : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    Finset (CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) := by
  classical
  exact Finset.univ.filter fun source =>
      source.Deep D F ∧
        canonicalActualInteriorBlockWord D source =
          canonicalActualInteriorBlockWord D representative ∧
        dyadicFloorBand
            (actualInteriorDenominator D pfx G threshold source.anchor) =
          dyadicFloorBand
            (actualInteriorDenominator D pfx G threshold representative.anchor) ∧
        (canonicalActualInteriorBlockEndGraph D source).poly =
          (canonicalActualInteriorBlockEndGraph D representative).poly

/-- Distinct terminal coordinates exposed by one actual block-end graph after
the representative's common deep continuation. -/
noncomputable def canonicalActualInteriorTerminalSamples (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold F : ℕ)
    (representative : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) : Finset ℕ :=
  (canonicalActualInteriorGraphSources D pfx G threshold F representative).image
    fun source =>
      D.positiveEnumeration.a (actualInteriorBlockSourceEndpointIndex D source) +
        Erdos260.GapWord.span
          (canonicalActualInteriorFutureWord D representative F)

/-- The actual endpoint/offset injection bounds an exact-graph cell by its
distinct terminal samples times the proved `(m+1)` offset fibre. -/
theorem canonicalActualInteriorGraphSources_card_le_terminalSamples_mul
    (D : CarrySeries) {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold F : ℕ}
    (representative : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) :
    (canonicalActualInteriorGraphSources
      D pfx G threshold F representative).card ≤
      (canonicalActualInteriorTerminalSamples
        D pfx G threshold F representative).card * (m + 1) := by
  classical
  let sources := canonicalActualInteriorGraphSources
    D pfx G threshold F representative
  let samples := canonicalActualInteriorTerminalSamples
    D pfx G threshold F representative
  let futureSpan := Erdos260.GapWord.span
    (canonicalActualInteriorFutureWord D representative F)
  let encode : (↥sources) → ↥samples × Fin (m + 1) := fun source =>
    (⟨D.positiveEnumeration.a
        (actualInteriorBlockSourceEndpointIndex D source.1) + futureSpan,
      by
        dsimp only [samples, futureSpan]
        rw [canonicalActualInteriorTerminalSamples, Finset.mem_image]
        exact ⟨source.1, source.2, rfl⟩⟩,
    ⟨actualInteriorBlockSourceEndpointIndex D source.1 - source.1.anchor.1,
      Nat.lt_succ_iff.mpr
        (canonicalActualInteriorBlockSource_offset_le D source.1)⟩)
  have hencode : Function.Injective encode := by
    intro left right heq
    apply Subtype.ext
    apply canonicalActualInteriorBlockSourceMap_injective D
    have hterminal := congrArg Subtype.val (Prod.mk.inj heq).1
    have hoffset := congrArg Fin.val (Prod.mk.inj heq).2
    apply Prod.ext
    · change D.positiveEnumeration.a
          (actualInteriorBlockSourceEndpointIndex D left.1) + futureSpan =
        D.positiveEnumeration.a
          (actualInteriorBlockSourceEndpointIndex D right.1) + futureSpan
          at hterminal
      exact Nat.add_right_cancel hterminal
    · exact hoffset
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa only [sources, samples, Fintype.card_prod,
    Fintype.card_coe, Fintype.card_fin] using hcard

theorem mem_canonicalActualInteriorGraphSources_iff
    (D : CarrySeries) {N W m bound : ℕ} {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold F : ℕ}
    {representative source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold} :
    source ∈ canonicalActualInteriorGraphSources
        D pfx G threshold F representative ↔
      source.Deep D F ∧
        canonicalActualInteriorBlockWord D source =
          canonicalActualInteriorBlockWord D representative ∧
        dyadicFloorBand
            (actualInteriorDenominator D pfx G threshold source.anchor) =
          dyadicFloorBand
            (actualInteriorDenominator D pfx G threshold representative.anchor) ∧
        (canonicalActualInteriorBlockEndGraph D source).poly =
          (canonicalActualInteriorBlockEndGraph D representative).poly := by
  simp [canonicalActualInteriorGraphSources]

/-- Membership in one exact-graph cell supplies the common canonical future
word, with no continuation stored in the source object. -/
theorem canonicalActualInteriorGraphSource_future_eq
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold F : ℕ}
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (representative : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold)
    (hrepresentativeDeep : representative.Deep D F)
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span
            (canonicalActualInteriorBlockWord D representative)) <
        1 / (4 * (dyadicFloorBand
          (actualInteriorDenominator D pfx G threshold
            representative.anchor) : ℝ) ^ 2))
    {source : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold}
    (hsourceMem : source ∈ canonicalActualInteriorGraphSources
      D pfx G threshold F representative) :
    canonicalActualInteriorFutureWord D source F =
      canonicalActualInteriorFutureWord D representative F := by
  have hsource :=
    (mem_canonicalActualInteriorGraphSources_iff D).mp hsourceMem
  have hshortSource :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span
            (canonicalActualInteriorBlockWord D source)) <
        1 / (4 * (dyadicFloorBand
          (actualInteriorDenominator D pfx G threshold source.anchor) : ℝ) ^ 2) := by
    simpa only [hsource.2.1, hsource.2.2.1] using hshort
  exact canonicalActualInteriorFutureWord_eq_of_code
    D hw hgeom hthreshold hthreshold source representative
      hsource.1 hrepresentativeDeep hsource.2.1 hsource.2.2.1 hshortSource

/-- Every terminal sample in one graph cell lies in a common explicit
interval; its upper endpoint uses only the representative code. -/
theorem canonicalActualInteriorTerminalSample_bounds
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold F : ℕ}
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (representative : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold)
    (hrepresentativeDeep : representative.Deep D F)
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span
            (canonicalActualInteriorBlockWord D representative)) <
        1 / (4 * (dyadicFloorBand
          (actualInteriorDenominator D pfx G threshold
            representative.anchor) : ℝ) ^ 2))
    {n : ℕ}
    (hn : n ∈ canonicalActualInteriorTerminalSamples
      D pfx G threshold F representative) :
    N < n ∧ n ≤ N + W + m * cap + F +
      actualInteriorBlockScale D pfx G threshold representative.anchor := by
  classical
  rw [canonicalActualInteriorTerminalSamples, Finset.mem_image] at hn
  obtain ⟨source, hsourceMem, rfl⟩ := hn
  have hsource :=
    (mem_canonicalActualInteriorGraphSources_iff D).mp hsourceMem
  have hfuture := canonicalActualInteriorGraphSource_future_eq
    D hw hgeom hthreshold representative hrepresentativeDeep hshort hsourceMem
  have hbounds := canonicalActualInteriorFutureTerminal_bounds
    D hw hgeom hthreshold source hsource.1
  have hscale : actualInteriorBlockScale D pfx G threshold source.anchor =
      actualInteriorBlockScale D pfx G threshold representative.anchor := by
    unfold actualInteriorBlockScale
    rw [hsource.2.2.1]
  simpa only [hfuture, hscale] using hbounds

/-- Uniform natural carry-height bound on every sample in one actual graph
cell. -/
theorem canonicalActualInteriorTerminalSample_carry_bound
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hpositiveFrom : D.positiveFrom ≤ N)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold F : ℕ}
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (representative : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold)
    (hrepresentativeDeep : representative.Deep D F)
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span
            (canonicalActualInteriorBlockWord D representative)) <
        1 / (4 * (dyadicFloorBand
          (actualInteriorDenominator D pfx G threshold
            representative.anchor) : ℝ) ^ 2))
    {n : ℕ}
    (hn : n ∈ canonicalActualInteriorTerminalSamples
      D pfx G threshold F representative) :
    (D.carry n).natAbs ≤ D.heightNatConstant *
      (N + W + m * cap + F +
        actualInteriorBlockScale D pfx G threshold representative.anchor + 1) ^
          D.weight.natDegree := by
  have hbounds := canonicalActualInteriorTerminalSample_bounds
    D hw hgeom hthreshold representative hrepresentativeDeep hshort hn
  have hcarry := D.carry_natAbs_le (hpositiveFrom.trans hbounds.1.le)
  have hpow : (n + 1) ^ D.weight.natDegree ≤
      (N + W + m * cap + F +
        actualInteriorBlockScale D pfx G threshold representative.anchor + 1) ^
          D.weight.natDegree :=
    Nat.pow_le_pow_left (Nat.add_le_add_right hbounds.2 1) _
  exact hcarry.trans (Nat.mul_le_mul_left D.heightNatConstant hpow)

/-- Every coordinate in an actual graph sample set is a genuine carry value
of the representative graph after its common continuation. -/
theorem canonicalActualInteriorTerminalSample_eval
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold F : ℕ}
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (hfit : ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
      G.poly.eval ((x + Erdos260.GapWord.span pfx : ℕ) : ℚ) =
        (D.carry (x + Erdos260.GapWord.span pfx) : ℚ))
    (representative : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold)
    (hrepresentativeDeep : representative.Deep D F)
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span
            (canonicalActualInteriorBlockWord D representative)) <
        1 / (4 * (dyadicFloorBand
          (actualInteriorDenominator D pfx G threshold
            representative.anchor) : ℝ) ^ 2))
    {n : ℕ}
    (hn : n ∈ canonicalActualInteriorTerminalSamples
      D pfx G threshold F representative) :
    (((canonicalActualInteriorBlockEndGraph D representative).transformWord
      D.base D.denominator D.weight le_rfl
        (canonicalActualInteriorFutureWord D representative F)).poly.eval
          (n : ℚ)) = (D.carry n : ℚ) := by
  classical
  rw [canonicalActualInteriorTerminalSamples, Finset.mem_image] at hn
  obtain ⟨source, hsourceMem, rfl⟩ := hn
  have hsource :=
    (mem_canonicalActualInteriorGraphSources_iff D).mp hsourceMem
  have hfuture := canonicalActualInteriorGraphSource_future_eq
    D hw hgeom hthreshold representative hrepresentativeDeep hshort hsourceMem
  have hsourceEval := canonicalActualInteriorFutureGraph_eval_carry
    D hfit (F := F) source
  have hpoly := PolynomialGraph.transformWord_poly_eq_of_poly_eq
    hsource.2.2.2.symm D.base D.denominator D.weight le_rfl
      (canonicalActualInteriorFutureWord D representative F)
  rw [hpoly]
  simpa only [hfuture] using hsourceEval

/-- Real-polynomial evaluation bound required by the sampling lemma, now
discharged from genuine carry samples. -/
theorem canonicalActualInteriorTerminalSample_real_bound
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hpositiveFrom : D.positiveFrom ≤ N)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold F : ℕ}
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (hfit : ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
      G.poly.eval ((x + Erdos260.GapWord.span pfx : ℕ) : ℚ) =
        (D.carry (x + Erdos260.GapWord.span pfx) : ℚ))
    (representative : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold)
    (hrepresentativeDeep : representative.Deep D F)
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span
            (canonicalActualInteriorBlockWord D representative)) <
        1 / (4 * (dyadicFloorBand
          (actualInteriorDenominator D pfx G threshold
            representative.anchor) : ℝ) ^ 2))
    {n : ℕ}
    (hn : n ∈ canonicalActualInteriorTerminalSamples
      D pfx G threshold F representative) :
    |(((canonicalActualInteriorBlockEndGraph D representative).transformWord
      D.base D.denominator D.weight le_rfl
        (canonicalActualInteriorFutureWord D representative F)).realPoly.eval
          (n : ℝ))| ≤
      (D.heightNatConstant *
        (N + W + m * cap + F +
          actualInteriorBlockScale D pfx G threshold representative.anchor + 1) ^
            D.weight.natDegree : ℕ) := by
  let T := (canonicalActualInteriorBlockEndGraph D representative).transformWord
    D.base D.denominator D.weight le_rfl
      (canonicalActualInteriorFutureWord D representative F)
  have hq := canonicalActualInteriorTerminalSample_eval
    D hw hgeom hthreshold hfit representative hrepresentativeDeep hshort hn
  have hmap : T.realPoly.eval (n : ℝ) =
      ((T.poly.eval (n : ℚ) : ℚ) : ℝ) := by
    unfold PolynomialGraph.realPoly
    simpa using Polynomial.eval_map_apply
      (p := T.poly) (f := algebraMap ℚ ℝ) (n : ℚ)
  have hcarry := canonicalActualInteriorTerminalSample_carry_bound
    D hw hgeom hpositiveFrom hthreshold representative
      hrepresentativeDeep hshort hn
  rw [show ((D.heightNatConstant *
        (N + W + m * cap + F +
          actualInteriorBlockScale D pfx G threshold representative.anchor + 1) ^
            D.weight.natDegree : ℕ) : ℝ) =
      (D.heightNatConstant *
        (N + W + m * cap + F +
          actualInteriorBlockScale D pfx G threshold representative.anchor + 1) ^
            D.weight.natDegree : ℕ) by rfl]
  rw [show (((canonicalActualInteriorBlockEndGraph D representative).transformWord
      D.base D.denominator D.weight le_rfl
        (canonicalActualInteriorFutureWord D representative F)).realPoly.eval
          (n : ℝ)) = T.realPoly.eval (n : ℝ) by rfl]
  rw [hmap]
  change |(((T.poly.eval (n : ℚ) : ℚ) : ℝ))| ≤ _
  rw [show T.poly.eval (n : ℚ) = (D.carry n : ℚ) by simpa only [T] using hq]
  have habsCast : |(((D.carry n : ℚ) : ℚ) : ℝ)| =
      ((D.carry n).natAbs : ℝ) := by norm_num
  rw [habsCast]
  exact_mod_cast hcarry

/-- Common interval length used by the two actual high-frequency sample
sets. -/
def actualInteriorSampleIntervalLength
    (W m cap F ell : ℕ) : ℕ :=
  W + m * cap + F + ell

/-- Uniform real sampling height written as a natural number. -/
def CarrySeries.actualInteriorSampleHeight (D : CarrySeries)
    (N H : ℕ) : ℕ :=
  D.heightNatConstant * (N + H + 1) ^ D.weight.natDegree

/-- The uniform carry-height envelope is monotone in the sampled interval
length. -/
theorem CarrySeries.actualInteriorSampleHeight_mono (D : CarrySeries)
    {N H K : ℕ} (hHK : H ≤ K) :
    D.actualInteriorSampleHeight N H ≤ D.actualInteriorSampleHeight N K := by
  unfold CarrySeries.actualInteriorSampleHeight
  gcongr

/-- Integral-fibre bound for the actual terminal sample set of one exact
block-end graph. -/
theorem canonicalActualInteriorTerminalSamples_card_bound
    (D : CarrySeries) {N W m cap bound : ℕ}
    (hd : 0 < D.weight.natDegree)
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    {pfx : Erdos260.GapWord}
    {G : PolynomialGraph D.weight.natDegree} {threshold F : ℕ}
    (hthreshold : Nat.log 2
        (G.normalizedTopState D.denominator D.weight).den + cap ≤ threshold)
    (hfit : ∀ x ∈ realizedPrefixAnchors D N W m bound pfx,
      G.poly.eval ((x + Erdos260.GapWord.span pfx : ℕ) : ℚ) =
        (D.carry (x + Erdos260.GapWord.span pfx) : ℚ))
    (representative : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold)
    (hrepresentativeDeep : representative.Deep D F)
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span
            (canonicalActualInteriorBlockWord D representative)) <
        1 / (4 * (dyadicFloorBand
          (actualInteriorDenominator D pfx G threshold
            representative.anchor) : ℝ) ^ 2))
    (hquot : 0 <
      actualInteriorDenominator D pfx G threshold representative.anchor /
        (D.denominator *
          (D.weight.coeff D.weight.natDegree).natAbs)) :
    let Hlen := actualInteriorSampleIntervalLength W m cap F
      (actualInteriorBlockScale D pfx G threshold representative.anchor)
    let samples := canonicalActualInteriorTerminalSamples
      D pfx G threshold F representative
    (samples.card : ℝ) ≤ D.weight.natDegree +
      D.weight.natDegree * Hlen /
        (((actualInteriorDenominator D pfx G threshold
            representative.anchor /
          (D.denominator *
            (D.weight.coeff D.weight.natDegree).natAbs) : ℕ) : ℝ)) ^
              ((vandermondeExponent D.weight.natDegree : ℝ)⁻¹) := by
  let future := canonicalActualInteriorFutureWord D representative F
  let T := (canonicalActualInteriorBlockEndGraph D representative).transformWord
    D.base D.denominator D.weight le_rfl future
  let Hlen := actualInteriorSampleIntervalLength W m cap F
    (actualInteriorBlockScale D pfx G threshold representative.anchor)
  let samples := canonicalActualInteriorTerminalSamples
    D pfx G threshold F representative
  have hstate : InteriorState D.base
      (((T.normalizedTopState D.denominator D.weight : ℚ) : ℝ)) := by
    simpa only [T, future] using
      canonicalActualInteriorFutureGraph_interiorState D hw representative
  have hden : (T.normalizedTopState D.denominator D.weight).den =
      actualInteriorDenominator D pfx G threshold representative.anchor := by
    simpa only [T, future] using
      canonicalActualInteriorFutureGraph_state_den
        D hw hgeom hthreshold representative
  have hsamples : ∀ n ∈ samples, N ≤ n ∧ n ≤ N + Hlen := by
    intro n hn
    have hbounds := canonicalActualInteriorTerminalSample_bounds
      D hw hgeom hthreshold representative hrepresentativeDeep hshort hn
    exact ⟨hbounds.1.le, by
      simpa only [Hlen, actualInteriorSampleIntervalLength,
        Nat.add_assoc] using hbounds.2⟩
  have hvalues : ∀ n ∈ samples, ∃ z : ℤ,
      T.poly.eval (n : ℚ) = (z : ℚ) := by
    intro n hn
    refine ⟨D.carry n, ?_⟩
    simpa only [T, future] using
      canonicalActualInteriorTerminalSample_eval
        D hw hgeom hthreshold hfit representative
          hrepresentativeDeep hshort hn
  have hquotT : 0 < (T.normalizedTopState
      D.denominator D.weight).den /
        (D.denominator *
          (D.weight.coeff D.weight.natDegree).natAbs) := by
    simpa only [hden] using hquot
  have hbound := T.interiorSamples_card_bound hd D.base_ge_two
    D.denominator_pos D.weight hw hstate samples hsamples hvalues hquotT
  simpa only [Hlen, samples, hden] using hbound

/-- An exact block-end graph is high frequency when its proved terminal image
contains enough distinct samples for degree-`d` interpolation. -/
def ActualInteriorGraphHighFrequency (D : CarrySeries)
    {N W m bound : ℕ} (pfx : Erdos260.GapWord)
    (G : PolynomialGraph D.weight.natDegree) (threshold F : ℕ)
    (representative : CanonicalActualInteriorBlockSource
      D N W m bound pfx G threshold) : Prop :=
  2 * D.weight.natDegree + 1 ≤
    (canonicalActualInteriorTerminalSamples
      D pfx G threshold F representative).card

/-- The explicit exponential-versus-polynomial inequality used by actual
high-frequency coalescence.  Its formulation contains the real graph
certificates and the actual finite sample sets. -/
noncomputable def ActualInteriorCoalescenceSmall (D : CarrySeries)
    {N W m cap bound threshold F : ℕ}
    {leftPrefix rightPrefix : Erdos260.GapWord}
    {leftGraph rightGraph : PolynomialGraph D.weight.natDegree}
    (left : CanonicalActualInteriorBlockSource
      D N W m bound leftPrefix leftGraph threshold)
    (right : CanonicalActualInteriorBlockSource
      D N W m bound rightPrefix rightGraph threshold) : Prop :=
  let future := canonicalActualInteriorFutureWord D left F
  let Hlen := actualInteriorSampleIntervalLength W m cap F
    (actualInteriorBlockScale D leftPrefix leftGraph threshold left.anchor)
  let Y := D.actualInteriorSampleHeight N Hlen
  let samplesLeft := canonicalActualInteriorTerminalSamples
    D leftPrefix leftGraph threshold F left
  let samplesRight := canonicalActualInteriorTerminalSamples
    D rightPrefix rightGraph threshold F right
  ((polynomialGraphDifferenceCertificate
    ((canonicalActualInteriorBlockEndGraph D left).transformWord
      D.base D.denominator D.weight le_rfl future)
    ((canonicalActualInteriorBlockEndGraph D right).transformWord
      D.base D.denominator D.weight le_rfl future)).scale : ℝ) *
      (samplingEnvelope D.weight.natDegree Hlen samplesLeft (Y : ℝ) +
        samplingEnvelope D.weight.natDegree Hlen samplesRight (Y : ℝ)) <
    (D.base : ℝ) ^ Erdos260.GapWord.span future

/-- Actual high-frequency coalescence.  The sample sets, their carry values,
their common continuation, and their interval bounds are all generated from
real retained sources.  Only the final explicit size inequality and the
finite high-frequency cardinal hypotheses remain for the asymptotic layer. -/
theorem actualHighFrequencyBlockGraphs_coalesce
    (D : CarrySeries) {N W m cap bound threshold F : ℕ}
    (hw : 0 < D.weight.coeff D.weight.natDegree)
    (hgeom : WindowGeometry D.positiveEnumeration N W m cap)
    (hpositiveFrom : D.positiveFrom ≤ N)
    {leftPrefix rightPrefix : Erdos260.GapWord}
    {leftGraph rightGraph : PolynomialGraph D.weight.natDegree}
    (hleftThreshold : Nat.log 2
        (leftGraph.normalizedTopState D.denominator D.weight).den + cap ≤
          threshold)
    (hrightThreshold : Nat.log 2
        (rightGraph.normalizedTopState D.denominator D.weight).den + cap ≤
          threshold)
    (hleftFit : ∀ x ∈ realizedPrefixAnchors
        D N W m bound leftPrefix,
      leftGraph.poly.eval
          ((x + Erdos260.GapWord.span leftPrefix : ℕ) : ℚ) =
        (D.carry (x + Erdos260.GapWord.span leftPrefix) : ℚ))
    (hrightFit : ∀ x ∈ realizedPrefixAnchors
        D N W m bound rightPrefix,
      rightGraph.poly.eval
          ((x + Erdos260.GapWord.span rightPrefix : ℕ) : ℚ) =
        (D.carry (x + Erdos260.GapWord.span rightPrefix) : ℚ))
    (left : CanonicalActualInteriorBlockSource
      D N W m bound leftPrefix leftGraph threshold)
    (right : CanonicalActualInteriorBlockSource
      D N W m bound rightPrefix rightGraph threshold)
    (hleftDeep : left.Deep D F) (hrightDeep : right.Deep D F)
    (hword : canonicalActualInteriorBlockWord D left =
      canonicalActualInteriorBlockWord D right)
    (hband : dyadicFloorBand
        (actualInteriorDenominator D leftPrefix leftGraph threshold left.anchor) =
      dyadicFloorBand
        (actualInteriorDenominator D rightPrefix rightGraph threshold right.anchor))
    (hshort :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span (canonicalActualInteriorBlockWord D left)) <
        1 / (4 * (dyadicFloorBand
          (actualInteriorDenominator D leftPrefix leftGraph threshold
            left.anchor) : ℝ) ^ 2))
    (hinterval : D.weight.natDegree ≤
      actualInteriorSampleIntervalLength W m cap F
        (actualInteriorBlockScale D leftPrefix leftGraph threshold left.anchor))
    (hleftFrequency : ActualInteriorGraphHighFrequency
      D leftPrefix leftGraph threshold F left)
    (hrightFrequency : ActualInteriorGraphHighFrequency
      D rightPrefix rightGraph threshold F right)
    (hsmall : ActualInteriorCoalescenceSmall
      D (cap := cap) (F := F) left right) :
    (canonicalActualInteriorBlockEndGraph D left).poly =
      (canonicalActualInteriorBlockEndGraph D right).poly := by
  let future := canonicalActualInteriorFutureWord D left F
  let Hlen := actualInteriorSampleIntervalLength W m cap F
    (actualInteriorBlockScale D leftPrefix leftGraph threshold left.anchor)
  let Y := D.actualInteriorSampleHeight N Hlen
  let samplesLeft := canonicalActualInteriorTerminalSamples
    D leftPrefix leftGraph threshold F left
  let samplesRight := canonicalActualInteriorTerminalSamples
    D rightPrefix rightGraph threshold F right
  have hscale : actualInteriorBlockScale
      D rightPrefix rightGraph threshold right.anchor =
    actualInteriorBlockScale
      D leftPrefix leftGraph threshold left.anchor := by
    unfold actualInteriorBlockScale
    rw [← hband]
  have hfuture := canonicalActualInteriorFutureWord_eq_of_code
    D hw hgeom hleftThreshold hrightThreshold left right
      hleftDeep hrightDeep hword hband hshort
  have hshortRight :
      1 / ((D.base - 1 : ℝ) * (D.base : ℝ) ^
          Erdos260.GapWord.span (canonicalActualInteriorBlockWord D right)) <
        1 / (4 * (dyadicFloorBand
          (actualInteriorDenominator D rightPrefix rightGraph threshold
            right.anchor) : ℝ) ^ 2) := by
    simpa only [← hword, ← hband] using hshort
  have hsamplesLeft : ∀ n ∈ samplesLeft,
      N ≤ n ∧ n ≤ N + Hlen := by
    intro n hn
    have hbounds := canonicalActualInteriorTerminalSample_bounds
      D hw hgeom hleftThreshold left hleftDeep hshort hn
    exact ⟨hbounds.1.le, by simpa only [Hlen,
      actualInteriorSampleIntervalLength, Nat.add_assoc] using hbounds.2⟩
  have hsamplesRight : ∀ n ∈ samplesRight,
      N ≤ n ∧ n ≤ N + Hlen := by
    intro n hn
    have hbounds := canonicalActualInteriorTerminalSample_bounds
      D hw hgeom hrightThreshold right hrightDeep hshortRight hn
    refine ⟨hbounds.1.le, ?_⟩
    simpa only [Hlen, actualInteriorSampleIntervalLength, hscale,
      Nat.add_assoc] using hbounds.2
  have hvaluesLeft : ∀ n ∈ samplesLeft,
      |(((canonicalActualInteriorBlockEndGraph D left).transformWord
        D.base D.denominator D.weight le_rfl future).realPoly.eval (n : ℝ))| ≤
          (Y : ℝ) := by
    intro n hn
    simpa only [future, Y, Hlen, CarrySeries.actualInteriorSampleHeight,
      actualInteriorSampleIntervalLength, Nat.add_assoc] using
      canonicalActualInteriorTerminalSample_real_bound
        D hw hgeom hpositiveFrom hleftThreshold hleftFit left
          hleftDeep hshort hn
  have hvaluesRight : ∀ n ∈ samplesRight,
      |(((canonicalActualInteriorBlockEndGraph D right).transformWord
        D.base D.denominator D.weight le_rfl future).realPoly.eval (n : ℝ))| ≤
          (Y : ℝ) := by
    intro n hn
    have hbound := canonicalActualInteriorTerminalSample_real_bound
      D hw hgeom hpositiveFrom hrightThreshold hrightFit right
        hrightDeep hshortRight hn
    simpa only [future, hfuture, Y, Hlen,
      CarrySeries.actualInteriorSampleHeight,
      actualInteriorSampleIntervalLength, hscale, Nat.add_assoc] using hbound
  apply lem_coalescence (A := N) (Hlen := Hlen) (b := D.base)
    (F := Erdos260.GapWord.span future) (Q := D.denominator)
    (Y₁ := (Y : ℝ)) (Y₂ := (Y : ℝ))
    (by simpa only [Hlen] using hinterval) D.base_ge_two
    (canonicalActualInteriorBlockEndGraph D left)
    (canonicalActualInteriorBlockEndGraph D right)
    D.weight le_rfl future rfl samplesLeft samplesRight
  · simpa only [samplesLeft, ActualInteriorGraphHighFrequency] using
      hleftFrequency
  · simpa only [samplesRight, ActualInteriorGraphHighFrequency] using
      hrightFrequency
  · exact hsamplesLeft
  · exact hsamplesRight
  · positivity
  · positivity
  · exact hvaluesLeft
  · exact hvaluesRight
  · simpa only [ActualInteriorCoalescenceSmall, future, Hlen, Y,
      samplesLeft, samplesRight] using hsmall

/-! ## A real source object and its proved source map -/

/-- A retained window/block source.  The block is required to be the output of
the canonical partition function, but injectivity is not stored as a field. -/
structure WindowBlockSource (Block : Type*)
    (canonicalBlock : ℕ → ℕ → Block) (m : ℕ) where
  windowStart : ℕ
  endpointIndex : ℕ
  start_le_endpoint : windowStart ≤ endpointIndex
  offset_le : endpointIndex - windowStart ≤ m
  block : Block
  block_eq : block = canonicalBlock windowStart endpointIndex

/-- The source map from `eq:sourcemap`: endpoint coordinate together with the
within-window offset. -/
def windowBlockSourceMap {Block : Type*} {canonicalBlock : ℕ → ℕ → Block}
    {m : ℕ} (endpoint : ℕ → ℕ)
    (source : WindowBlockSource Block canonicalBlock m) : ℕ × ℕ :=
  (endpoint source.endpointIndex,
    source.endpointIndex - source.windowStart)

/-- The source map is injective whenever support endpoints have unique
indices.  The proof recovers endpoint index, offset, window start, and finally
the canonical block in that order. -/
theorem windowBlockSourceMap_injective {Block : Type*}
    {canonicalBlock : ℕ → ℕ → Block} {m : ℕ}
    (endpoint : ℕ → ℕ) (hendpoint : Function.Injective endpoint) :
    Function.Injective
      (windowBlockSourceMap (Block := Block)
        (canonicalBlock := canonicalBlock) (m := m) endpoint) := by
  intro left right hmap
  have hend : left.endpointIndex = right.endpointIndex :=
    hendpoint (Prod.mk.inj hmap).1
  have hoffset :
      left.endpointIndex - left.windowStart =
        right.endpointIndex - right.windowStart := (Prod.mk.inj hmap).2
  have hstart : left.windowStart = right.windowStart := by
    have hleft := left.start_le_endpoint
    have hright := right.start_le_endpoint
    rw [← hend] at hoffset hright
    omega
  have hblock : left.block = right.block := by
    rw [left.block_eq, right.block_eq, hstart, hend]
  cases left
  cases right
  simp_all

/-- A cell label attached canonically to a retained window--block source. -/
structure InteriorCellSource (Block Cell : Type*)
    (canonicalBlock : ℕ → ℕ → Block)
    (canonicalCell : ℕ → ℕ → Cell) (m : ℕ) where
  source : WindowBlockSource Block canonicalBlock m
  cell : Cell
  cell_eq : cell = canonicalCell source.windowStart source.endpointIndex

/-- Cell, endpoint coordinate, and within-window offset. -/
def interiorCellSourceMap {Block Cell : Type*}
    {canonicalBlock : ℕ → ℕ → Block}
    {canonicalCell : ℕ → ℕ → Cell} {m : ℕ}
    (endpoint : ℕ → ℕ)
    (source : InteriorCellSource Block Cell canonicalBlock canonicalCell m) :
    Cell × ℕ × ℕ :=
  (source.cell, endpoint source.source.endpointIndex,
    source.source.endpointIndex - source.source.windowStart)

/-- Formula label `eq:sourcemap`, now including the cell coordinate used by
both low- and high-frequency counts. -/
theorem interiorCellSourceMap_injective {Block Cell : Type*}
    {canonicalBlock : ℕ → ℕ → Block}
    {canonicalCell : ℕ → ℕ → Cell} {m : ℕ}
    (endpoint : ℕ → ℕ) (hendpoint : Function.Injective endpoint) :
    Function.Injective
      (interiorCellSourceMap (Block := Block) (Cell := Cell)
        (canonicalBlock := canonicalBlock) (canonicalCell := canonicalCell)
        (m := m) endpoint) := by
  intro left right hmap
  have htail :
      (endpoint left.source.endpointIndex,
          left.source.endpointIndex - left.source.windowStart) =
        (endpoint right.source.endpointIndex,
          right.source.endpointIndex - right.source.windowStart) :=
    (Prod.mk.inj hmap).2
  have hsource : left.source = right.source :=
    windowBlockSourceMap_injective endpoint hendpoint htail
  have hcell : left.cell = right.cell := (Prod.mk.inj hmap).1
  cases left
  cases right
  simp_all

/-- Formula label `eq:sourcemap`. -/
theorem eq_sourcemap {Block Cell : Type*}
    {canonicalBlock : ℕ → ℕ → Block}
    {canonicalCell : ℕ → ℕ → Cell} {m : ℕ}
    (endpoint : ℕ → ℕ) (hendpoint : Function.Injective endpoint) :
    Function.Injective
      (interiorCellSourceMap (Block := Block) (Cell := Cell)
        (canonicalBlock := canonicalBlock) (canonicalCell := canonicalCell)
        (m := m) endpoint) :=
  interiorCellSourceMap_injective endpoint hendpoint

/-- Finite source census in one cell family.  The `(m+1)` fibre factor comes
from the proved offset bound, not from an assumed finite fibre. -/
theorem interiorCellSource_card_le {Block Cell : Type*}
    [Fintype Cell]
    {canonicalBlock : ℕ → ℕ → Block}
    {canonicalCell : ℕ → ℕ → Cell} {m : ℕ}
    (endpoint : ℕ → ℕ) (hendpoint : Function.Injective endpoint)
    (sources : Finset
      (InteriorCellSource Block Cell canonicalBlock canonicalCell m))
    (endpoints : Finset ℕ)
    (hendpoint_mem : ∀ s ∈ sources, endpoint s.source.endpointIndex ∈ endpoints) :
    sources.card ≤ Fintype.card Cell * endpoints.card * (m + 1) := by
  classical
  let target := Cell × endpoints × Fin (m + 1)
  let encode : (↥sources) → target := fun s =>
    (s.1.cell,
      ⟨endpoint s.1.source.endpointIndex, hendpoint_mem s.1 s.2⟩,
      ⟨s.1.source.endpointIndex - s.1.source.windowStart,
        Nat.lt_succ_iff.mpr s.1.source.offset_le⟩)
  have hencode : Function.Injective encode := by
    intro left right heq
    apply Subtype.ext
    apply interiorCellSourceMap_injective endpoint hendpoint
    exact Prod.ext (Prod.mk.inj heq).1
      (Prod.ext
        (congrArg Subtype.val (Prod.mk.inj (Prod.mk.inj heq).2).1)
        (congrArg Fin.val (Prod.mk.inj (Prod.mk.inj heq).2).2))
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa [target, Fintype.card_prod, mul_assoc] using hcard

/-- Cell type used in `eq:cellcount`: prefix, completed-block position, and
dyadic band. -/
abbrev InteriorCell (Prefix : Type*) (m bands : ℕ) :=
  Prefix × Fin m × Fin bands

/-- Formula label `eq:cellcount` in exact finite-cardinal form. -/
theorem interiorCell_card (Prefix : Type*) [Fintype Prefix]
    (m bands : ℕ) :
    Fintype.card (InteriorCell Prefix m bands) =
      Fintype.card Prefix * m * bands := by
  simp [InteriorCell, Fintype.card_prod, mul_assoc]

/-- Formula label `eq:cellcount`. -/
theorem eq_cellcount (Prefix : Type*) [Fintype Prefix]
    (m bands : ℕ) :
    Fintype.card (InteriorCell Prefix m bands) =
      Fintype.card Prefix * m * bands :=
  interiorCell_card Prefix m bands

/-- Exact low-frequency mass bound obtained from the cell/source injection. -/
theorem lowFrequencyBlockMass_le {Block Cell : Type*}
    [Fintype Cell]
    {canonicalBlock : ℕ → ℕ → Block}
    {canonicalCell : ℕ → ℕ → Cell} {m : ℕ}
    (endpoint : ℕ → ℕ) (hendpoint : Function.Injective endpoint)
    (sources : Finset
      (InteriorCellSource Block Cell canonicalBlock canonicalCell m))
    (endpoints : Finset ℕ)
    (hendpoint_mem : ∀ s ∈ sources, endpoint s.source.endpointIndex ∈ endpoints)
    (blockSpan : Block → ℕ) {H : ℕ}
    (hspan : ∀ s ∈ sources, blockSpan s.source.block ≤ H) :
    ∑ s ∈ sources, blockSpan s.source.block ≤
      Fintype.card Cell * endpoints.card * (m + 1) * H := by
  calc
    ∑ s ∈ sources, blockSpan s.source.block ≤ ∑ _s ∈ sources, H := by
      gcongr with s hs
      exact hspan s hs
    _ = sources.card * H := by simp
    _ ≤ (Fintype.card Cell * endpoints.card * (m + 1)) * H := by
      gcongr
      exact interiorCellSource_card_le endpoint hendpoint sources endpoints
        hendpoint_mem
    _ = _ := rfl

/-! ## Finite interior proposition -/

def interiorCensusGraphKeys {Source Graph : Type*}
    [DecidableEq Source] [DecidableEq Graph]
    (sources : Finset Source) (graphOf : Source → Graph) : Finset Graph :=
  sources.image graphOf

/-- If an exact graph factors through a coarser cell label on a finite source
family, then the number of realized exact graphs is at most the number of
realized cells. -/
theorem image_card_le_image_card_of_factors
    {Source Graph Cell : Type*}
    [DecidableEq Source] [DecidableEq Graph] [DecidableEq Cell]
    (sources : Finset Source) (graphOf : Source → Graph)
    (cellOf : Source → Cell)
    (hfactor : ∀ left ∈ sources, ∀ right ∈ sources,
      cellOf left = cellOf right → graphOf left = graphOf right) :
    (sources.image graphOf).card ≤ (sources.image cellOf).card := by
  classical
  let graphs := sources.image graphOf
  let cells := sources.image cellOf
  let representative : ↥graphs → Source := fun graph =>
    Classical.choose (Finset.mem_image.mp graph.2)
  have hrepresentativeMem (graph : ↥graphs) :
      representative graph ∈ sources :=
    (Classical.choose_spec (Finset.mem_image.mp graph.2)).1
  have hrepresentativeGraph (graph : ↥graphs) :
      graphOf (representative graph) = graph.1 :=
    (Classical.choose_spec (Finset.mem_image.mp graph.2)).2
  let encode : ↥graphs → ↥cells := fun graph =>
    ⟨cellOf (representative graph),
      Finset.mem_image.mpr
        ⟨representative graph, hrepresentativeMem graph, rfl⟩⟩
  have hencode : Function.Injective encode := by
    intro left right heq
    apply Subtype.ext
    have hcell : cellOf (representative left) =
        cellOf (representative right) :=
      congrArg Subtype.val heq
    have hgraph := hfactor (representative left)
      (hrepresentativeMem left) (representative right)
      (hrepresentativeMem right) hcell
    calc
      left.1 = graphOf (representative left) :=
        (hrepresentativeGraph left).symm
      _ = graphOf (representative right) := hgraph
      _ = right.1 := hrepresentativeGraph right
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa only [graphs, cells, Fintype.card_coe] using hcard

def interiorCensusCodeKeys {Source Graph Code : Type*}
    [DecidableEq Source] [DecidableEq Graph] [DecidableEq Code]
    (sources : Finset Source) (graphOf : Source → Graph)
    (codeOf : Graph → Code) : Finset Code :=
  (interiorCensusGraphKeys sources graphOf).image codeOf

def interiorCensusSourceFibre {Source Graph : Type*}
    [DecidableEq Source] [DecidableEq Graph]
    (sources : Finset Source) (graphOf : Source → Graph) (graph : Graph) :
    Finset Source :=
  sources.filter fun source => graphOf source = graph

def interiorCensusEndpointFibre {Source Graph : Type*}
    [DecidableEq Source] [DecidableEq Graph]
    (sources : Finset Source) (graphOf : Source → Graph)
    (endpoint : Source → ℕ) (graph : Graph) : Finset ℕ :=
  (interiorCensusSourceFibre sources graphOf graph).image endpoint

def InteriorCensusHigh {Source Graph : Type*}
    [DecidableEq Source] [DecidableEq Graph]
    (sources : Finset Source) (graphOf : Source → Graph)
    (endpoint : Source → ℕ) (U : ℕ) (graph : Graph) : Prop :=
  U ≤ (interiorCensusEndpointFibre sources graphOf endpoint graph).card

instance instDecidableInteriorCensusHigh
    {Source Graph : Type*} [DecidableEq Source] [DecidableEq Graph]
    (sources : Finset Source) (graphOf : Source → Graph)
    (endpoint : Source → ℕ) (U : ℕ) (graph : Graph) :
    Decidable (InteriorCensusHigh sources graphOf endpoint U graph) := by
  unfold InteriorCensusHigh
  infer_instance

/-- The realized exact graphs whose endpoint fibres cross the high-frequency
threshold.  Keeping this set explicit prevents the entropy branch from
charging low-frequency codes a second time. -/
def interiorCensusHighGraphKeys {Source Graph : Type*}
    [DecidableEq Source] [DecidableEq Graph]
    (sources : Finset Source) (graphOf : Source → Graph)
    (endpoint : Source → ℕ) (U : ℕ) : Finset Graph :=
  (interiorCensusGraphKeys sources graphOf).filter
    (InteriorCensusHigh sources graphOf endpoint U)

/-- Codes actually represented by a high-frequency exact graph. -/
def interiorCensusHighCodeKeys {Source Graph Code : Type*}
    [DecidableEq Source] [DecidableEq Graph] [DecidableEq Code]
    (sources : Finset Source) (graphOf : Source → Graph)
    (codeOf : Graph → Code) (endpoint : Source → ℕ) (U : ℕ) :
    Finset Code :=
  (interiorCensusHighGraphKeys sources graphOf endpoint U).image codeOf

/-- The global endpoint/offset source map bounds every exact-graph fibre. -/
theorem interiorCensusSourceFibre_card_le
    {Source Graph : Type*} [DecidableEq Source] [DecidableEq Graph]
    (sources : Finset Source) (graphOf : Source → Graph)
    (endpoint : Source → ℕ) {m : ℕ} (offset : Source → Fin (m + 1))
    (hinjective : Function.Injective fun source =>
      (endpoint source, (offset source : ℕ))) (graph : Graph) :
    (interiorCensusSourceFibre sources graphOf graph).card ≤
      (interiorCensusEndpointFibre sources graphOf endpoint graph).card *
        (m + 1) := by
  classical
  let fibre := interiorCensusSourceFibre sources graphOf graph
  let endpoints := interiorCensusEndpointFibre sources graphOf endpoint graph
  let encode : ↥fibre → ↥endpoints × Fin (m + 1) := fun source =>
    (⟨endpoint source.1, by
      dsimp only [endpoints]
      rw [interiorCensusEndpointFibre, Finset.mem_image]
      exact ⟨source.1, source.2, rfl⟩⟩,
    offset source.1)
  have hencode : Function.Injective encode := by
    intro left right heq
    apply Subtype.ext
    apply hinjective
    exact Prod.ext
      (congrArg Subtype.val (Prod.mk.inj heq).1)
      (congrArg Fin.val (Prod.mk.inj heq).2)
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa only [fibre, endpoints, Fintype.card_prod,
    Fintype.card_coe, Fintype.card_fin] using hcard

/-- Manuscript proposition `prop:interior` in exact finite census form.

Low graph fibres are charged by `U` endpoint samples and the proved offset
fibre.  Pairwise coalescence makes `codeOf` injective on high graph fibres,
so their mass is charged once per word/band code. -/
theorem prop_interior
    {Source Graph Code : Type*}
    [DecidableEq Source] [DecidableEq Graph] [DecidableEq Code]
    (sources : Finset Source) (graphOf : Source → Graph)
    (codeOf : Graph → Code) (endpoint : Source → ℕ)
    {m : ℕ} (offset : Source → Fin (m + 1))
    (span : Source → ℕ) (blockCap endpointCap : Code → ℕ) (U : ℕ)
    (hinjective : Function.Injective fun source =>
      (endpoint source, (offset source : ℕ)))
    (hspan : ∀ source ∈ sources,
      span source ≤ blockCap (codeOf (graphOf source)))
    (hendpoint : ∀ graph ∈ interiorCensusGraphKeys sources graphOf,
      InteriorCensusHigh sources graphOf endpoint U graph →
        (interiorCensusEndpointFibre sources graphOf endpoint graph).card ≤
          endpointCap (codeOf graph))
    (hcoalescence : ∀ left ∈ interiorCensusGraphKeys sources graphOf,
      InteriorCensusHigh sources graphOf endpoint U left →
      ∀ right ∈ interiorCensusGraphKeys sources graphOf,
        InteriorCensusHigh sources graphOf endpoint U right →
        codeOf left = codeOf right → left = right) :
    ∑ source ∈ sources, span source ≤
      (∑ graph ∈ interiorCensusGraphKeys sources graphOf,
        if ¬ InteriorCensusHigh sources graphOf endpoint U graph then
          U * (m + 1) * blockCap (codeOf graph)
        else 0) +
      ∑ code ∈ interiorCensusHighCodeKeys
          sources graphOf codeOf endpoint U,
        endpointCap code * (m + 1) * blockCap code := by
  classical
  let graphs := interiorCensusGraphKeys sources graphOf
  let fibre := interiorCensusSourceFibre sources graphOf
  let endpoints := interiorCensusEndpointFibre sources graphOf endpoint
  let high := InteriorCensusHigh sources graphOf endpoint U
  let highGraphs := graphs.filter high
  let codes := highGraphs.image codeOf
  let lowTerm : Graph → ℕ := fun graph =>
    if ¬ high graph then U * (m + 1) * blockCap (codeOf graph) else 0
  let highTerm : Graph → ℕ := fun graph =>
    if high graph then
      endpointCap (codeOf graph) * (m + 1) * blockCap (codeOf graph)
    else 0
  have hmaps : ∀ source ∈ sources, graphOf source ∈ graphs := by
    intro source hsource
    exact Finset.mem_image.mpr ⟨source, hsource, rfl⟩
  have hpartition := Finset.sum_fiberwise_of_maps_to hmaps span
  have hcell (graph : Graph) (hgraph : graph ∈ graphs) :
      ∑ source ∈ fibre graph, span source ≤
        lowTerm graph + highTerm graph := by
    have hmass : ∑ source ∈ fibre graph, span source ≤
        (fibre graph).card * blockCap (codeOf graph) := by
      calc
        ∑ source ∈ fibre graph, span source ≤
            ∑ _source ∈ fibre graph, blockCap (codeOf graph) := by
          apply Finset.sum_le_sum
          intro source hsource
          have hmem := Finset.mem_filter.mp hsource
          have hs := hspan source hmem.1
          simpa only [hmem.2] using hs
        _ = (fibre graph).card * blockCap (codeOf graph) := by simp
    have hfibreCard := interiorCensusSourceFibre_card_le
      sources graphOf endpoint offset hinjective graph
    by_cases hhigh : high graph
    · have hend := hendpoint graph hgraph hhigh
      have hcard : (fibre graph).card ≤
          endpointCap (codeOf graph) * (m + 1) :=
        hfibreCard.trans (Nat.mul_le_mul_right (m + 1) hend)
      rw [show lowTerm graph = 0 by simp [lowTerm, hhigh],
        show highTerm graph = endpointCap (codeOf graph) * (m + 1) *
            blockCap (codeOf graph) by simp [highTerm, hhigh], zero_add]
      exact hmass.trans (Nat.mul_le_mul_right _ hcard)
    · have hend : (endpoints graph).card ≤ U := by
        have hnot : ¬ U ≤ (endpoints graph).card := by
          simpa only [high, endpoints, InteriorCensusHigh] using hhigh
        omega
      have hcard : (fibre graph).card ≤ U * (m + 1) :=
        hfibreCard.trans (Nat.mul_le_mul_right (m + 1) hend)
      rw [show lowTerm graph = U * (m + 1) * blockCap (codeOf graph) by
          simp [lowTerm, hhigh],
        show highTerm graph = 0 by simp [highTerm, hhigh], add_zero]
      exact hmass.trans (Nat.mul_le_mul_right _ hcard)
  have hcensus :
      ∑ source ∈ sources, span source ≤
        (∑ graph ∈ graphs, lowTerm graph) +
          ∑ graph ∈ graphs, highTerm graph := by
    rw [← hpartition]
    calc
      ∑ graph ∈ graphs, ∑ source ∈ sources with graphOf source = graph,
          span source ≤
          ∑ graph ∈ graphs, (lowTerm graph + highTerm graph) := by
        apply Finset.sum_le_sum
        intro graph hgraph
        simpa only [fibre, interiorCensusSourceFibre] using hcell graph hgraph
      _ = (∑ graph ∈ graphs, lowTerm graph) +
          ∑ graph ∈ graphs, highTerm graph := by
        rw [Finset.sum_add_distrib]
  have hhighMaps : ∀ graph ∈ highGraphs, codeOf graph ∈ codes := by
    intro graph hgraph
    exact Finset.mem_image.mpr ⟨graph, hgraph, rfl⟩
  have hhighFibreCard (code : Code) :
      (highGraphs.filter fun graph => codeOf graph = code).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro left hleft right hright
    have hleft' := Finset.mem_filter.mp hleft
    have hright' := Finset.mem_filter.mp hright
    have hleftHigh := Finset.mem_filter.mp hleft'.1
    have hrightHigh := Finset.mem_filter.mp hright'.1
    exact hcoalescence left hleftHigh.1 hleftHigh.2
      right hrightHigh.1 hrightHigh.2 (hleft'.2.trans hright'.2.symm)
  have hhighMass : ∑ graph ∈ graphs, highTerm graph ≤
      ∑ code ∈ codes,
        endpointCap code * (m + 1) * blockCap code := by
    have hrestrict : ∑ graph ∈ graphs, highTerm graph =
        ∑ graph ∈ highGraphs,
          endpointCap (codeOf graph) * (m + 1) * blockCap (codeOf graph) := by
      dsimp only [highTerm, highGraphs]
      rw [Finset.sum_filter]
    rw [hrestrict]
    have hfibre := Finset.sum_fiberwise_of_maps_to hhighMaps
      (fun graph => endpointCap (codeOf graph) * (m + 1) *
        blockCap (codeOf graph))
    rw [← hfibre]
    apply Finset.sum_le_sum
    intro code hcode
    have hcard := hhighFibreCard code
    let C := endpointCap code * (m + 1) * blockCap code
    calc
      ∑ graph ∈ highGraphs with codeOf graph = code,
          endpointCap (codeOf graph) * (m + 1) * blockCap (codeOf graph) =
          ∑ _graph ∈ highGraphs.filter (fun graph => codeOf graph = code),
            C := by
        apply Finset.sum_congr rfl
        intro graph hgraph
        rw [(Finset.mem_filter.mp hgraph).2]
      _ = (highGraphs.filter fun graph => codeOf graph = code).card * C := by
        simp
      _ ≤ 1 * C := by
        exact Nat.mul_le_mul_right _ hcard
      _ = endpointCap code * (m + 1) * blockCap code := by simp [C]
  simpa only [graphs, high, highGraphs, codes,
    interiorCensusHighCodeKeys, interiorCensusHighGraphKeys] using
      hcensus.trans (add_le_add (le_refl _) hhighMass)

end Erdos260.PolynomialWindow
