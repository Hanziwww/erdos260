import Erdos260.DirtyCrossingCylinderCore
import Erdos260.RationalSeparation

/-!
# §25.3 singular-square bound (D1): exact Diophantine characterization of the descent windows

Wave-19 (`DirtyCrossingCylinderCore`) reduced the §25.1 cylinder match to a two-field
`SingularSquareCertificate`, whose analytic heart is **(D1)** the singular-square bound

`|R| * 2 ^ n < D * q0`  with  `R = M * q0 - a * 2 ^ n`,  `D = 2 ^ n`,  `M = windowCylinderValue`,

i.e. the actual shell window value `M` (the `n`-bit integer of the descent-window digits) approximates
the residual centre `a / q0` to within `2 ^ (-n)`.  This file (NEW; it edits no existing file) attacks
(D1) directly and **sharply characterizes** it, building on `Residual.residual_fractional_approx`,
`RunCylinderBridge.cylinderIndex_ratCast`, and `RationalSeparation.rat_div_eq_of_abs_sub_lt_inv_mul`.

## What is genuinely PROVED here (no `sorry`/`axiom`/`admit`/`native_decide`)

* **The exact characterization (`singularSquareBound_iff_cylinder`).**  Writing
  `kν = cylinderIndex n (a / q0)` (`= (2 ^ n * a) / q0`), the bound (D1) holds **iff**

  `kν = M  ∨  (kν + 1 = M ∧ ¬ q0 ∣ 2 ^ n * a)`,

  i.e. (D1) is *exactly* the statement that the centre `a / q0` lies in the window's own depth-`n`
  cylinder `kν = M`, **or** in the carry-adjacent lower one `kν = M - 1` (and is not the dyadic left
  endpoint).  Proved by pure `ℤ`-arithmetic from `singularSquareBound_iff_natAbs` and the integer
  kernel `natAbs_qmul_sub_lt_iff`.  This *subsumes* wave-19's one-sided exclusion
  (`cylinderIndex_succ_ne_of_singularSquareBound`: (D1) excludes the *upper* neighbour `kν = M + 1`)
  and shows (D1) is **not** an independent analytic input beyond the cylinder match — it *is* the
  equal-or-carry containment, with the single carry branch routed by (D2) `NoLargeRun`.

* **The reduction is two-sided.**  `singularSquareBound_of_cylinderIndex_eq` (equal cylinder ⟹ (D1))
  and `cylinderIndex_eq_or_carry_of_singularSquareBound` ((D1) ⟹ equal-or-carry).  The general-`M`
  closed reduction `dyadicCylinder_center_of_singularSquareBound`: (D1) + the carry exclusion give
  `DyadicCylinder n M (a / q0)` for *any* `M` (wave-19 needed `M = windowCylinderValue`).

* **The genuine Diophantine obstruction (`not_singularSquareBound_of_residue_band`).**  When
  `q0 ≤ (M * q0) % 2 ^ n ≤ 2 ^ n - q0` (the forbidden middle residue band, nonempty exactly for
  `2 q0 ≤ 2 ^ n`), **no** numerator `a` satisfies (D1): the window cylinder contains no fraction
  `a / q0`.  This is the manuscript's "a depth-`n` cylinder has width `2 ^ (-n)` while denominator-`q0`
  fractions are spaced `1 / q0`, so for `q0 < 2 ^ n` a generic window cylinder contains no `a / q0`",
  here made exact: existence of a singular-square numerator is *equivalent* to the residue condition
  (`exists_singularSquareBound_iff`), with explicit witnesses in the admissible bands.

* **Centre uniqueness via rational separation (`singularSquare_center_unique`).**  If two small
  denominators `q0, q0'` with `2 q0 q0' ≤ 2 ^ n` both carry a (D1)-centre for the same window `M`,
  the centres coincide: `a / q0 = a' / q0'`.  This is the manuscript's "rational separation forces
  `η_{x,w} = η`" step, fed to `rat_div_eq_of_abs_sub_lt_inv_mul`.

* **Non-vacuity (`singularSquareBound_windowCylinderValue_orbit` / `_oneThird`).**  (D1) holds for the
  *actual* window value of any small-odd-denominator orbit word `dyadicDigit q0 a` (`a < q0`), since
  its window value *is* the cylinder index (wave-19 `windowCylinderValue_dyadicDigit_self`).  In
  particular (D1) is genuinely proved for the `1/3` run-obstruction windows — no constant/zero short.

## Audit verdict (the irreducible Diophantine remainder)

(D1) for the *actual* shell is **inter-reducible** with the §25.1 equal-or-carry cylinder containment
(this file proves the equivalence).  It is therefore **not** a second analytic fact beyond the cylinder
match: proving (D1) "from scratch" is *exactly* establishing that the actual descent-window mask point
`M / 2 ^ n` lands within `2 ^ (-n)` of the centre `a / q0` (manuscript eq. 25.1, the denominator-drop
defect bound `|R| ≪_Q X + p`).  That defect bound comes from the failing shell's near-periodic descent
structure (the actual sequence agrees with the rational periodic completion to descent depth `p - B`),
proved upstream via rational separation (§24.3); the rational-separation kernel is reproved here
(`singularSquare_center_unique`).  The single genuinely irreducible step left to the descent machinery
is therefore the **descent-depth agreement** `‖η − η_{x,w}‖ < 2 ^ (-(window depth))` that pins the
window into the centre's cylinder — a property of the descent-window *selection*, upstream of this file
and not a cylinder-geometry fact.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

/-! ## Part A — The singular-square bound predicate and its integer reduction -/

/-- **The (D1) singular-square bound** for a depth-`n` window of value `M`, residual centre `a / q0`.
This is exactly wave-19's `hbound` field (with `M = windowCylinderValue d s n`):
`|M * q0 - a * 2 ^ n| * 2 ^ n < 2 ^ n * q0`, i.e. `|M / 2 ^ n - a / q0| < 2 ^ (-n)`. -/
def SingularSquareBound (n M q0 a : ℕ) : Prop :=
  |(M : ℝ) * (q0 : ℝ) - (a : ℝ) * (2 : ℝ) ^ n| * 2 ^ n < (2 : ℝ) ^ n * (q0 : ℝ)

/-- **(D1) reduced to integer arithmetic.**  The real bound is equivalent to the integer statement
`|M * q0 - a * 2 ^ n| < q0`, phrased through `Int.natAbs`. -/
theorem singularSquareBound_iff_natAbs {n M q0 a : ℕ} (_hq0 : 0 < q0) :
    SingularSquareBound n M q0 a ↔ ((M : ℤ) * q0 - (a : ℤ) * 2 ^ n).natAbs < q0 := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hcast : (((M : ℤ) * q0 - (a : ℤ) * 2 ^ n : ℤ) : ℝ)
      = (M : ℝ) * (q0 : ℝ) - (a : ℝ) * (2 : ℝ) ^ n := by push_cast; ring
  have habs : |(M : ℝ) * (q0 : ℝ) - (a : ℝ) * (2 : ℝ) ^ n|
      = (((M : ℤ) * q0 - (a : ℤ) * 2 ^ n).natAbs : ℝ) := by
    rw [← hcast, Nat.cast_natAbs, Int.cast_abs]
  unfold SingularSquareBound
  rw [habs, mul_comm ((2 : ℝ) ^ n) (q0 : ℝ)]
  constructor
  · intro h
    have hlt : (((M : ℤ) * q0 - (a : ℤ) * 2 ^ n).natAbs : ℝ) < (q0 : ℝ) :=
      lt_of_mul_lt_mul_right h h2.le
    exact_mod_cast hlt
  · intro h
    have hlt : (((M : ℤ) * q0 - (a : ℤ) * 2 ^ n).natAbs : ℝ) < (q0 : ℝ) := by exact_mod_cast h
    exact mul_lt_mul_of_pos_right hlt h2

/-- **Integer kernel.**  For `0 ≤ ρ < q0`, the residual `q0 * D - ρ` has `natAbs < q0` exactly when
`D = 0` (equal cylinder) or `D = 1` with `ρ ≠ 0` (the carry-adjacent lower neighbour, not at the
dyadic endpoint).  All other `D` give `|q0 * D - ρ| ≥ q0`. -/
theorem natAbs_qmul_sub_lt_iff {q0 : ℕ} (hq0 : 0 < q0) (D : ℤ) {ρ : ℕ} (hρ : ρ < q0) :
    ((q0 : ℤ) * D - (ρ : ℤ)).natAbs < q0 ↔ D = 0 ∨ (D = 1 ∧ ρ ≠ 0) := by
  have hq0Z : (0 : ℤ) < q0 := by exact_mod_cast hq0
  constructor
  · intro h
    have hlt : |(q0 : ℤ) * D - (ρ : ℤ)| < (q0 : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast h
    rw [abs_lt] at hlt
    obtain ⟨hL, hR⟩ := hlt
    have hρ0 : (0 : ℤ) ≤ (ρ : ℤ) := Int.natCast_nonneg ρ
    have hρlt' : (ρ : ℤ) < q0 := by exact_mod_cast hρ
    have hD0 : 0 ≤ D := by
      by_contra hc
      have hle : D ≤ -1 := by have := not_le.mp hc; omega
      have hmul : (q0 : ℤ) * D ≤ (q0 : ℤ) * (-1) := mul_le_mul_of_nonneg_left hle hq0Z.le
      rw [mul_neg, mul_one] at hmul
      linarith
    have hD1 : D ≤ 1 := by
      by_contra hc
      have hge : 2 ≤ D := by have := not_le.mp hc; omega
      have hmul : (q0 : ℤ) * 2 ≤ (q0 : ℤ) * D := mul_le_mul_of_nonneg_left hge hq0Z.le
      linarith
    interval_cases D
    · exact Or.inl rfl
    · exact Or.inr ⟨rfl, by omega⟩
  · rintro (rfl | ⟨rfl, hρ0⟩)
    · omega
    · omega

/-! ## Part B — The exact characterization and the two-sided cylinder reduction -/

/--
**THE EXACT CHARACTERIZATION OF (D1).**

With `kν = cylinderIndex n (a / q0) = (2 ^ n * a) / q0`, the singular-square bound holds **iff**
`kν = M` (the centre lies in the window's own depth-`n` cylinder) **or** `kν + 1 = M` together with
`q0 ∤ 2 ^ n * a` (the centre lies in the carry-adjacent *lower* cylinder `M - 1` and is not its dyadic
left endpoint).  In particular (D1) is *precisely* the equal-or-carry containment — not an independent
analytic input.
-/
theorem singularSquareBound_iff_cylinder {n M q0 a : ℕ} (hq0 : 0 < q0) :
    SingularSquareBound n M q0 a ↔
      cylinderIndex n ((a : ℝ) / (q0 : ℝ)) = M ∨
        (cylinderIndex n ((a : ℝ) / (q0 : ℝ)) + 1 = M ∧ ¬ (q0 ∣ 2 ^ n * a)) := by
  rw [singularSquareBound_iff_natAbs hq0, cylinderIndex_ratCast]
  set kν := (2 ^ n * a) / q0 with hkν
  set ρ := (2 ^ n * a) % q0 with hρdef
  have hdm : q0 * kν + ρ = 2 ^ n * a := by rw [hkν, hρdef]; exact Nat.div_add_mod _ _
  have hρlt : ρ < q0 := by rw [hρdef]; exact Nat.mod_lt _ hq0
  have key : (M : ℤ) * q0 - (a : ℤ) * 2 ^ n = (q0 : ℤ) * ((M : ℤ) - (kν : ℤ)) - (ρ : ℤ) := by
    have hc : ((q0 * kν + ρ : ℕ) : ℤ) = ((2 ^ n * a : ℕ) : ℤ) := by exact_mod_cast hdm
    push_cast at hc
    linear_combination hc
  rw [key, natAbs_qmul_sub_lt_iff hq0 ((M : ℤ) - (kν : ℤ)) hρlt]
  have hdvd : ¬ (q0 ∣ 2 ^ n * a) ↔ ρ ≠ 0 := by rw [Nat.dvd_iff_mod_eq_zero, ← hρdef]
  rw [hdvd]
  constructor
  · rintro (h | ⟨h, hρ0⟩)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, hρ0⟩
  · rintro (h | ⟨h, hρ0⟩)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, hρ0⟩

/-- **Equal cylinder ⟹ (D1).**  If the centre `a / q0` lies in the window value's own depth-`n`
cylinder (`cylinderIndex n (a / q0) = M`, the §25.1 equal-cylinder match), then the singular-square
bound holds automatically.  So (D1) is *implied* by the desired cylinder match. -/
theorem singularSquareBound_of_cylinderIndex_eq {n M q0 a : ℕ} (hq0 : 0 < q0)
    (h : cylinderIndex n ((a : ℝ) / (q0 : ℝ)) = M) : SingularSquareBound n M q0 a :=
  (singularSquareBound_iff_cylinder hq0).mpr (Or.inl h)

/-- **(D1) ⟹ equal-or-carry-adjacent.**  The bound forces the centre into the window's cylinder or the
carry-adjacent lower neighbour `M - 1`.  Routing away the single carry branch (via (D2) `NoLargeRun`)
leaves the equal-cylinder match. -/
theorem cylinderIndex_eq_or_carry_of_singularSquareBound {n M q0 a : ℕ} (hq0 : 0 < q0)
    (h : SingularSquareBound n M q0 a) :
    cylinderIndex n ((a : ℝ) / (q0 : ℝ)) = M ∨ cylinderIndex n ((a : ℝ) / (q0 : ℝ)) + 1 = M := by
  rcases (singularSquareBound_iff_cylinder hq0).mp h with h' | ⟨h', _⟩
  · exact Or.inl h'
  · exact Or.inr h'

/-- **The upper adjacency is excluded by (D1) alone** (subsumes wave-19's
`cylinder_succ_excluded_of_singularSquare`, now for an arbitrary window value `M`): the centre cannot
sit one cylinder to the *right* of the window. -/
theorem cylinderIndex_succ_ne_of_singularSquareBound {n M q0 a : ℕ} (hq0 : 0 < q0)
    (h : SingularSquareBound n M q0 a) :
    cylinderIndex n ((a : ℝ) / (q0 : ℝ)) ≠ M + 1 := by
  rcases cylinderIndex_eq_or_carry_of_singularSquareBound hq0 h with h' | h' <;> omega

/--
**The carry-cylinder reduction, general `M` (CLOSED).**

For *any* window value `M` (not only `windowCylinderValue`), the singular-square bound (D1) together
with the carry exclusion `cylinderIndex n (a / q0) + 1 ≠ M` gives the equal-cylinder conclusion
`DyadicCylinder n M (a / q0)`.  This is the wave-19 reduction `dyadicCylinder_center_of_singularSquare`
recovered and generalized purely from the characterization — no `windowMaskPoint` input needed.
-/
theorem dyadicCylinder_center_of_singularSquareBound {n M q0 a : ℕ} (hq0 : 0 < q0)
    (h : SingularSquareBound n M q0 a)
    (hcarry : cylinderIndex n ((a : ℝ) / (q0 : ℝ)) + 1 ≠ M) :
    DyadicCylinder n M ((a : ℝ) / (q0 : ℝ)) := by
  rcases cylinderIndex_eq_or_carry_of_singularSquareBound hq0 h with heq | hcar
  · rw [← heq]; exact dyadicCylinder_cylinderIndex (by positivity)
  · exact absurd hcar hcarry

/-! ## Part C — The genuine Diophantine obstruction: existence ⟺ residue band -/

/--
**(D1) forces the residue band.**  If some numerator `a` satisfies the singular-square bound, then the
window residue `(M * q0) % 2 ^ n` lies in the admissible band `[0, q0) ∪ (2 ^ n - q0, 2 ^ n)`.  The
contrapositive is the manuscript obstruction: a *generic* window cylinder (residue in the forbidden
middle band) contains **no** fraction `a / q0`.  Pure `ℤ`-casework on `(M * q0)/2 ^ n - a`.
-/
theorem residue_lt_of_singularSquareBound {n M q0 a : ℕ} (hq0 : 0 < q0)
    (h : SingularSquareBound n M q0 a) :
    (M * q0) % 2 ^ n < q0 ∨ 2 ^ n - q0 < (M * q0) % 2 ^ n := by
  rw [singularSquareBound_iff_natAbs hq0] at h
  by_contra hcon
  rw [not_or, not_lt, not_lt] at hcon
  obtain ⟨hlo, hhi⟩ := hcon
  set t := (M * q0) / 2 ^ n with htdef
  set s := (M * q0) % 2 ^ n with hsdef
  have hdm : 2 ^ n * t + s = M * q0 := by rw [htdef, hsdef]; exact Nat.div_add_mod _ _
  have hPcast : ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := by push_cast; ring
  have hPq : 2 * q0 ≤ 2 ^ n := by omega
  have hrr : (M : ℤ) * q0 - (a : ℤ) * 2 ^ n = (2 : ℤ) ^ n * ((t : ℤ) - a) + (s : ℤ) := by
    have hc : ((2 ^ n * t + s : ℕ) : ℤ) = ((M * q0 : ℕ) : ℤ) := by exact_mod_cast hdm
    push_cast at hc
    linear_combination -hc
  rw [hrr] at h
  set e := (t : ℤ) - a with hedef
  have hsZlo : (q0 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hlo
  have hsZhi : (s : ℤ) ≤ (2 : ℤ) ^ n - q0 := by omega
  have hPqZ : 2 * (q0 : ℤ) ≤ (2 : ℤ) ^ n := by omega
  have hs0 : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
  have hge : (q0 : ℤ) ≤ |(2 : ℤ) ^ n * e + (s : ℤ)| := by
    rcases lt_trichotomy e 0 with he | he | he
    · have he1 : e ≤ -1 := by omega
      have hm : (2 : ℤ) ^ n * e ≤ (2 : ℤ) ^ n * (-1) := mul_le_mul_of_nonneg_left he1 (by positivity)
      rw [mul_neg, mul_one] at hm
      rw [le_abs]; right; linarith
    · rw [he, mul_zero, zero_add, abs_of_nonneg hs0]; exact hsZlo
    · have he1 : (1 : ℤ) ≤ e := by omega
      have hm : (2 : ℤ) ^ n * 1 ≤ (2 : ℤ) ^ n * e := mul_le_mul_of_nonneg_left he1 (by positivity)
      rw [mul_one] at hm
      rw [le_abs]; left; linarith
  rw [Int.abs_eq_natAbs] at hge
  have hfin : q0 ≤ ((2 : ℤ) ^ n * e + (s : ℤ)).natAbs := by exact_mod_cast hge
  omega

/-- **Witness in the lower band.**  If the window residue is `< q0`, the floor numerator
`a = (M * q0) / 2 ^ n` realises the singular-square bound (the centre lies in the window's own
cylinder). -/
theorem singularSquareBound_of_residue_lt {n M q0 : ℕ} (hq0 : 0 < q0)
    (hs : (M * q0) % 2 ^ n < q0) : SingularSquareBound n M q0 ((M * q0) / 2 ^ n) := by
  rw [singularSquareBound_iff_natAbs hq0]
  have hdm : 2 ^ n * ((M * q0) / 2 ^ n) + (M * q0) % 2 ^ n = M * q0 := Nat.div_add_mod _ _
  have hPcast : ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := by push_cast; ring
  have hval : (M : ℤ) * q0 - (((M * q0) / 2 ^ n : ℕ) : ℤ) * 2 ^ n = ((M * q0) % 2 ^ n : ℕ) := by
    have hnat : ((2 ^ n * ((M * q0) / 2 ^ n) + (M * q0) % 2 ^ n : ℕ) : ℤ) = ((M * q0 : ℕ) : ℤ) := by
      exact_mod_cast hdm
    rw [Nat.cast_add, Nat.cast_mul, hPcast, Nat.cast_mul] at hnat
    linear_combination -hnat
  rw [hval]
  omega

/-- **Witness in the upper band.**  If the window residue exceeds `2 ^ n - q0`, the numerator
`a = (M * q0) / 2 ^ n + 1` realises the singular-square bound (the centre lies just below the window
point, the carry-adjacent cylinder). -/
theorem singularSquareBound_of_residue_gt {n M q0 : ℕ} (hq0 : 0 < q0)
    (hs : 2 ^ n - q0 < (M * q0) % 2 ^ n) :
    SingularSquareBound n M q0 ((M * q0) / 2 ^ n + 1) := by
  rw [singularSquareBound_iff_natAbs hq0]
  have hdm : 2 ^ n * ((M * q0) / 2 ^ n) + (M * q0) % 2 ^ n = M * q0 := Nat.div_add_mod _ _
  have hslt : (M * q0) % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
  have hPcast : ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := by push_cast; ring
  have hval : (M : ℤ) * q0 - (((M * q0) / 2 ^ n + 1 : ℕ) : ℤ) * 2 ^ n
      = ((M * q0) % 2 ^ n : ℕ) - (2 : ℤ) ^ n := by
    have hnat : ((2 ^ n * ((M * q0) / 2 ^ n) + (M * q0) % 2 ^ n : ℕ) : ℤ) = ((M * q0 : ℕ) : ℤ) := by
      exact_mod_cast hdm
    rw [Nat.cast_add, Nat.cast_mul, hPcast, Nat.cast_mul] at hnat
    rw [Nat.cast_add, Nat.cast_one]
    linear_combination -hnat
  rw [hval]
  have hslt' : ((M * q0) % 2 ^ n : ℤ) < (2 : ℤ) ^ n := by exact_mod_cast hslt
  have hs0 : (0 : ℤ) ≤ ((M * q0) % 2 ^ n : ℤ) := Int.natCast_nonneg _
  have hsgt' : (2 : ℤ) ^ n - q0 < ((M * q0) % 2 ^ n : ℤ) := by
    by_cases hq2 : q0 ≤ 2 ^ n
    · have hcast : ((2 ^ n - q0 : ℕ) : ℤ) < ((M * q0) % 2 ^ n : ℤ) := by exact_mod_cast hs
      rw [Nat.cast_sub hq2, hPcast] at hcast
      linarith [hcast]
    · have hlt : (2 : ℤ) ^ n < (q0 : ℤ) := by rw [← hPcast]; exact_mod_cast (not_le.mp hq2)
      linarith [hs0]
  have hzlt : ((M * q0) % 2 ^ n : ℤ) - 2 ^ n < q0 := by
    have : (0 : ℤ) ≤ (q0 : ℤ) := Int.natCast_nonneg q0
    linarith [hslt']
  have hzgt : -(q0 : ℤ) < ((M * q0) % 2 ^ n : ℤ) - 2 ^ n := by linarith [hsgt']
  omega

/--
**THE OBSTRUCTION (singular squares are controlled).**

When the window residue `(M * q0) % 2 ^ n` lies in the forbidden middle band `[q0, 2 ^ n - q0]` (which
is nonempty exactly when `2 q0 ≤ 2 ^ n`, i.e. `q0` small relative to the cylinder depth), **no**
numerator `a` satisfies the singular-square bound: the depth-`n` window cylinder contains no fraction
`a / q0`.  This is the manuscript §25.3 Diophantine heart made exact.
-/
theorem not_singularSquareBound_of_residue_band {n M q0 a : ℕ} (hq0 : 0 < q0)
    (hlo : q0 ≤ (M * q0) % 2 ^ n) (hhi : (M * q0) % 2 ^ n ≤ 2 ^ n - q0) :
    ¬ SingularSquareBound n M q0 a := by
  intro h
  rcases residue_lt_of_singularSquareBound hq0 h with hc | hc <;> omega

/-- **Existence ⟺ residue band.**  A depth-`n` window of value `M` admits *some* singular-square
centre numerator iff its residue lies in the admissible band — the precise singular-square condition.
-/
theorem exists_singularSquareBound_iff {n M q0 : ℕ} (hq0 : 0 < q0) :
    (∃ a : ℕ, SingularSquareBound n M q0 a) ↔
      (M * q0) % 2 ^ n < q0 ∨ 2 ^ n - q0 < (M * q0) % 2 ^ n := by
  constructor
  · rintro ⟨a, ha⟩
    exact residue_lt_of_singularSquareBound hq0 ha
  · rintro (h | h)
    · exact ⟨(M * q0) / 2 ^ n, singularSquareBound_of_residue_lt hq0 h⟩
    · exact ⟨(M * q0) / 2 ^ n + 1, singularSquareBound_of_residue_gt hq0 h⟩

/-! ## Part D — Centre uniqueness via rational separation -/

/--
**The singular-square centre is unique (rational separation).**

If two small denominators `q0, q0'` with `2 q0 q0' ≤ 2 ^ n` both carry a (D1)-centre for the *same*
window value `M`, the centres coincide: `a / q0 = a' / q0'`.  Both centres lie within `2 ^ (-n)` of the
window mask point `M / 2 ^ n` (via `residual_fractional_approx`), so within `2 ^ (1-n) ≤ 1/(q0 q0')`
of each other, and `rat_div_eq_of_abs_sub_lt_inv_mul` (the §24.3 rational-separation kernel) forces
equality.
-/
theorem singularSquare_center_unique {n q0 q0' M a a' : ℕ}
    (hq0 : 0 < q0) (hq0' : 0 < q0') (hsep : 2 * q0 * q0' ≤ 2 ^ n)
    (h : SingularSquareBound n M q0 a) (h' : SingularSquareBound n M q0' a') :
    (a : ℝ) / (q0 : ℝ) = (a' : ℝ) / (q0' : ℝ) := by
  have hq0R : (0 : ℝ) < (q0 : ℝ) := by exact_mod_cast hq0
  have hq0R' : (0 : ℝ) < (q0' : ℝ) := by exact_mod_cast hq0'
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have happ : |(M : ℝ) / (2 : ℝ) ^ n - (a : ℝ) / (q0 : ℝ)| < 1 / (2 : ℝ) ^ n :=
    residual_fractional_approx h2 hq0R rfl h
  have happ' : |(M : ℝ) / (2 : ℝ) ^ n - (a' : ℝ) / (q0' : ℝ)| < 1 / (2 : ℝ) ^ n :=
    residual_fractional_approx h2 hq0R' rfl h'
  have hdist : |(a : ℝ) / (q0 : ℝ) - (a' : ℝ) / (q0' : ℝ)| < 1 / ((q0 : ℝ) * (q0' : ℝ)) := by
    have htri : |(a : ℝ) / (q0 : ℝ) - (a' : ℝ) / (q0' : ℝ)|
        ≤ |(a : ℝ) / (q0 : ℝ) - (M : ℝ) / (2 : ℝ) ^ n|
          + |(M : ℝ) / (2 : ℝ) ^ n - (a' : ℝ) / (q0' : ℝ)| := abs_sub_le _ _ _
    rw [abs_sub_comm ((a : ℝ) / (q0 : ℝ)) ((M : ℝ) / (2 : ℝ) ^ n)] at htri
    have hle : 2 / (2 : ℝ) ^ n ≤ 1 / ((q0 : ℝ) * (q0' : ℝ)) := by
      rw [div_le_div_iff₀ h2 (mul_pos hq0R hq0R')]
      have hsepR : (2 : ℝ) * (q0 : ℝ) * (q0' : ℝ) ≤ (2 : ℝ) ^ n := by
        have : ((2 * q0 * q0' : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hsep
        push_cast at this; linarith
      nlinarith [hsepR]
    have hsum : |(M : ℝ) / (2 : ℝ) ^ n - (a : ℝ) / (q0 : ℝ)|
        + |(M : ℝ) / (2 : ℝ) ^ n - (a' : ℝ) / (q0' : ℝ)| < 2 / (2 : ℝ) ^ n := by
      rw [show (2 : ℝ) / (2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n + 1 / (2 : ℝ) ^ n from by ring]
      linarith [happ, happ']
    linarith [htri, hsum, hle]
  have hlt : |((a : ℤ) : ℝ) / (q0 : ℝ) - ((a' : ℤ) : ℝ) / (q0' : ℝ)| < 1 / ((q0 : ℝ) * (q0' : ℝ)) := by
    push_cast; exact hdist
  have key := rat_div_eq_of_abs_sub_lt_inv_mul (P := (a : ℤ)) (A := (a' : ℤ)) (Q := q0) (B := q0')
    hq0 hq0' hlt
  push_cast at key
  exact key

/-! ## Part E — Non-vacuity: (D1) holds for the actual orbit-window values -/

/--
**(D1) is genuinely satisfied by the actual orbit windows.**  For a small-odd-denominator centre
`a / q0` (`a < q0`), the depth-`n` window value of its own dyadic-digit word `dyadicDigit q0 a` is its
cylinder index (wave-19 `windowCylinderValue_dyadicDigit_self`), so the singular-square bound holds.
This *proves* (D1) for the genuine orbit windows — no constant/all-zero shortcut.
-/
theorem singularSquareBound_windowCylinderValue_orbit {q0 a : ℕ} (hq0 : 0 < q0) (ha : a < q0)
    (n : ℕ) :
    SingularSquareBound n (windowCylinderValue (dyadicDigit q0 a) 0 n) q0 a :=
  singularSquareBound_of_cylinderIndex_eq hq0 (windowCylinderValue_dyadicDigit_self hq0 ha n).symm

/-- Concrete `1/3`-orbit instance: (D1) holds for the canonical run-obstruction windows. -/
theorem singularSquareBound_oneThird (n : ℕ) :
    SingularSquareBound n (windowCylinderValue (dyadicDigit 3 1) 0 n) 3 1 :=
  singularSquareBound_windowCylinderValue_orbit (by norm_num) (by norm_num) n

/-! ## Part F — Honest residual inventory -/

/-- The precise status of (D1) after this module. -/
def singularSquareBoundCoreResiduals : List String :=
  [ "CLOSED (the exact characterization) — singularSquareBound_iff_cylinder: with kν = cylinderIndex " ++
      "n (a/q₀), the singular-square bound |R|·2ⁿ < D·q₀ holds IFF kν = M ∨ (kν+1 = M ∧ q₀ ∤ 2ⁿ·a). " ++
      "So (D1) is EXACTLY the equal-or-carry-adjacent cylinder containment of the centre a/q₀ — not " ++
      "an independent analytic input. Subsumes wave-19's one-sided upper exclusion " ++
      "(cylinderIndex_succ_ne_of_singularSquareBound).",
    "CLOSED (two-sided reduction) — singularSquareBound_of_cylinderIndex_eq (equal cylinder ⟹ (D1)) " ++
      "and cylinderIndex_eq_or_carry_of_singularSquareBound ((D1) ⟹ equal-or-carry); the general-M " ++
      "carry-cylinder reduction dyadicCylinder_center_of_singularSquareBound gives DyadicCylinder n M " ++
      "(a/q₀) for ANY window value M from (D1) + the carry exclusion (wave-19 needed M = " ++
      "windowCylinderValue).",
    "CLOSED (the genuine obstruction) — not_singularSquareBound_of_residue_band / " ++
      "exists_singularSquareBound_iff: a depth-n window of value M admits a (D1)-centre IFF its " ++
      "residue (M·q₀) mod 2ⁿ lies in [0,q₀) ∪ (2ⁿ−q₀, 2ⁿ). In the forbidden middle band (nonempty " ++
      "for 2q₀ ≤ 2ⁿ) the window cylinder contains NO fraction a/q₀ — the manuscript §25.3 'generic " ++
      "cylinder is singular-square-free' made exact, with explicit witnesses in the admissible bands.",
    "CLOSED (rational separation) — singularSquare_center_unique: two small denominators q₀,q₀' with " ++
      "2q₀q₀' ≤ 2ⁿ carrying (D1)-centres for the same window M have a/q₀ = a'/q₀'. This is the " ++
      "manuscript §24.3 'rational separation forces η_{x,w} = η' step, via " ++
      "RationalSeparation.rat_div_eq_of_abs_sub_lt_inv_mul.",
    "NON-VACUOUS — singularSquareBound_windowCylinderValue_orbit / _oneThird: (D1) is genuinely " ++
      "PROVED for the actual orbit-window values (the window value of dyadicDigit q₀ a IS its " ++
      "cylinder index), e.g. the 1/3 run obstruction.",
    "RESIDUAL (the irreducible Diophantine remainder, CHARACTERIZED) — (D1) for the actual shell is " ++
      "INTER-REDUCIBLE with the §25.1 equal-or-carry cylinder containment (proved above). The single " ++
      "genuinely irreducible step is the descent-depth agreement ‖η − η_{x,w}‖ < 2^(−window depth) " ++
      "that lands the actual window mask point M/2ⁿ into the centre's cylinder (manuscript eq. 25.1 " ++
      "denominator-drop defect |R| ≪_Q X+p, from the failing shell's near-periodic descent). This is " ++
      "a property of the descent-window SELECTION, upstream of the cylinder geometry and not provable " ++
      "from it alone; the rational-separation kernel it relies on is reproved here." ]

theorem singularSquareBoundCoreResiduals_nonempty : singularSquareBoundCoreResiduals ≠ [] := by
  simp [singularSquareBoundCoreResiduals]

/-! ## Part G — Axiom-cleanliness audit -/

#print axioms singularSquareBound_iff_natAbs
#print axioms natAbs_qmul_sub_lt_iff
#print axioms singularSquareBound_iff_cylinder
#print axioms singularSquareBound_of_cylinderIndex_eq
#print axioms cylinderIndex_eq_or_carry_of_singularSquareBound
#print axioms cylinderIndex_succ_ne_of_singularSquareBound
#print axioms dyadicCylinder_center_of_singularSquareBound
#print axioms residue_lt_of_singularSquareBound
#print axioms not_singularSquareBound_of_residue_band
#print axioms exists_singularSquareBound_iff
#print axioms singularSquare_center_unique
#print axioms singularSquareBound_windowCylinderValue_orbit

end

end Erdos260
