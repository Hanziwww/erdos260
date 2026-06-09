import Mathlib
import Erdos260.IntegerCarry
import Erdos260.UnconditionalAssembly

/-!
# The integer-carry affine law and the odd reduced denominator of the Tower slope

`TowerLandingConstruction.lean` discharges Tower finiteness, the E.13 slope
closure, the recurrent cycle (Theorem E.6) and the Tower budget for an **odd**
slope modulus `q`, and `oddPartFibreDynamics` runs the whole construction on the
odd part `ordCompl[2](Q·H)` of the modulus.  The capstone
`UnconditionalAssembly.lean` then consumes the residual **affine-law slope atom**
`TowerSlopeAtom = (Q, H, Q ≠ 0, Odd H, 2 ≤ H)` and turns it into a
`TowerTransientFactoryData` via `towerOfSlope`.

This file supplies the genuinely arithmetic content that *justifies* that odd
modulus: the **integer-carry affine law** (manuscript E.5/E.8/E.13) and a
**2-adic valuation argument** proving that every recurrent slope has an **odd
reduced denominator**.  Concretely:

## The affine slope law (E.8/E.13)

* `affineStepQ g μ = 2^g · μ − 1` — the rational form of the E.13 slope map
  `μ ↦ 2^{g}·μ − 1`, exactly the integer carry recurrence
  `R_{N+1} = 2 R_N − a_N` normalised by the slope denominator.
* `affineStepQ_cast` — its real cast is the *very* recurrence used by
  `CarryFibreCycleData.slope_trans`, so the abstract rational law specialises to
  the manuscript real E.13 recurrence with no gap.

## The 2-adic descent (oddness of the reduced denominator)

* `padicValRat_affineStepQ_ge` — the ultrametric step inequality
  `min (g + v₂ μ) 0 ≤ v₂ (affineStepQ g μ)` for the 2-adic valuation `v₂`.
* `affineDenVal μ = min (v₂ μ) 0` is the monovariant (`= 0 ⇔ odd denominator`);
  `affineDenVal_mono` (non-increasing) and `affineDenVal_succ_eq_imp` (strict
  while even) capture that a gap `g ≥ 1` strictly lowers the 2-adic valuation of
  the slope denominator until it is **zero**.
* `cyclic_affineQ_den_odd` — **the headline**: on a recurrent slope cycle of the
  affine law (all slopes nonzero, all gaps `≥ 1`) every slope has **odd reduced
  denominator**.  The monovariant is constant around the cycle, hence forced to
  `0`.
* `carryCycle_den_odd` — the same conclusion for any `CarryFibreCycleData` whose
  real slopes are casts of rationals: *every recurrent carry-fibre cycle has odd
  reduced denominators*.  The gap positivity `g ≥ 1` is itself **derived** from
  the open-slope condition (`CarryFibreCycleData.gap_pos`).

## The carry-side 2-adic root and the connection to `TowerSlopeAtom`

* `integerCarry_padicValInt_zero_run` — the *mechanism* on `R_N` itself: across a
  run of `h` zero digits the carry doubles, so `v₂(R_{N+h}) = h + v₂(R_N)`; this
  growing 2-adic valuation of `R_N` is exactly what cancels the slope
  denominator's 2-part in the descent above.
* `den_odd_of_odd_modulus` — consistency with the existing construction: a slope
  `K/q` on an odd modulus `q` has odd reduced denominator, so
  `boundedSlopeDynamics`/`oddPartFibreDynamics` indeed operate on odd-denominator
  slopes, as the descent predicts.
* `towerSlopeAtomOfAPModuli` / `towerOfSlopeOfAPModuli` — **the reduction**: a
  `TowerSlopeAtom` (and hence the full `TowerTransientFactoryData`) is
  *constructed* from genuinely geometric AP-modulus data
  `(Q ≠ 0, h₁ ∣ 2^a − 1, h₂ ∣ 2^b − 1, 2 ≤ lcm h₁ h₂)`, with the previously
  *assumed* oddness field `Odd H` now a **theorem** (`apModulus_odd`).

## Honest status

The Tower slope atom is **REDUCED, not closed**.  The 2-adic descent and the
recurrent-cycle oddness theorem are unconditional (no `sorry`, no `axiom`); the
oddness field `Odd H` of `TowerSlopeAtom` is eliminated in favour of the
manuscript AP-modulus divisibility `h_Γ ∣ D_Γ = 2^{S_Γ} − 1`.  The genuinely
geometric residual that remains is the *identification* of the recurrent slope's
modulus data `(Q, h₁, h₂, a, b)` with the failing-shell carry geometry
(the AP subfibre parametrisation `B_{x_s} = B_{x_0} + s·K_Γ`, manuscript
E.2–E.5), which is **not** formalised here.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1. The affine slope law (manuscript E.8/E.13) -/

/--
**The E.13 slope map, rational form.**  `affineStepQ g μ = 2^g · μ − 1`.  This is
the integer-carry recurrence `R_{N+1} = 2 R_N − a_N` (over a gap of `g` doubling
steps, `R ↦ 2^g R − (carry adjustment)`) normalised by the fixed slope
denominator, i.e. the manuscript doubling-type map on slopes.
-/
def affineStepQ (g : ℕ) (μ : ℚ) : ℚ := 2 ^ g * μ - 1

/-- The real cast of `affineStepQ` is exactly the E.13 recurrence used by
`CarryFibreCycleData.slope_trans` (`μ(step) = 2^g·μ − 1` over `ℝ`). -/
theorem affineStepQ_cast (g : ℕ) (μ : ℚ) :
    ((affineStepQ g μ : ℚ) : ℝ) = 2 ^ g * (μ : ℝ) - 1 := by
  unfold affineStepQ
  push_cast
  ring

/-! ## 2. The 2-adic valuation descent of the slope denominator

We use the 2-adic valuation `padicValRat 2 μ ∈ ℤ`.  A nonzero rational `μ` has an
**odd reduced denominator** iff `0 ≤ padicValRat 2 μ`.  The affine step lowers the
denominator's 2-adic content, captured by the ultrametric inequality below. -/

/--
**Ultrametric step inequality.**  For nonzero `μ` with nonzero image, the 2-adic
valuation of `affineStepQ g μ = 2^g·μ − 1` is at least `min (g + v₂ μ) 0`.  This
is the integer-carry doubling (`v₂(2^g μ) = g + v₂ μ`) combined with the
ultrametric law for subtracting the unit `1`.
-/
theorem padicValRat_affineStepQ_ge (g : ℕ) (μ : ℚ) (hμ : μ ≠ 0)
    (hstep : affineStepQ g μ ≠ 0) :
    min ((g : ℤ) + padicValRat 2 μ) 0 ≤ padicValRat 2 (affineStepQ g μ) := by
  have h2g : ((2 : ℚ) ^ g) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h21 : padicValRat 2 (2 : ℚ) = 1 := by
    have h := padicValRat.self (p := 2) (by norm_num)
    simpa using h
  -- value of `2^g · μ`
  have hmul : padicValRat 2 ((2 : ℚ) ^ g * μ) = (g : ℤ) + padicValRat 2 μ := by
    rw [padicValRat.mul h2g hμ, padicValRat.pow (show (2 : ℚ) ≠ 0 by norm_num), h21]
    ring
  -- value of `-1`
  have hval_neg1 : padicValRat 2 (-1 : ℚ) = 0 := by
    have : (-1 : ℚ) = -(1 : ℚ) := by norm_num
    rw [this, padicValRat.neg, padicValRat.one]
  -- rewrite the step as a genuine sum and apply the ultrametric law
  have hsum : affineStepQ g μ = (2 : ℚ) ^ g * μ + (-1) := by
    unfold affineStepQ; ring
  have hne1 : (2 : ℚ) ^ g * μ + (-1) ≠ 0 := by rw [← hsum]; exact hstep
  have hult := padicValRat.min_le_padicValRat_add (p := 2) hne1
  rw [hmul, hval_neg1] at hult
  rw [hsum]
  exact hult

/-- The 2-adic denominator monovariant `min (v₂ μ) 0 ≤ 0`; it equals `0` exactly
when `μ` has odd reduced denominator. -/
def affineDenVal (μ : ℚ) : ℤ := min (padicValRat 2 μ) 0

/-- The monovariant is **non-increasing** along the affine step: a gap can only
reduce the 2-adic content of the slope denominator. -/
theorem affineDenVal_mono (g : ℕ) (μ : ℚ) (hμ : μ ≠ 0) (hstep : affineStepQ g μ ≠ 0) :
    affineDenVal μ ≤ affineDenVal (affineStepQ g μ) := by
  have hge := padicValRat_affineStepQ_ge g μ hμ hstep
  have hg0 : (0 : ℤ) ≤ (g : ℤ) := Int.natCast_nonneg g
  unfold affineDenVal
  omega

/--
**Strict descent while even.**  If a gap `g ≥ 1` leaves the monovariant *fixed*
(`affineDenVal μ = affineDenVal (affineStepQ g μ)`), then `μ` already had odd
reduced denominator (`0 ≤ v₂ μ`): an even denominator would strictly drop.
-/
theorem affineDenVal_succ_eq_imp (g : ℕ) (μ : ℚ) (hg : 1 ≤ g) (hμ : μ ≠ 0)
    (hstep : affineStepQ g μ ≠ 0)
    (heq : affineDenVal μ = affineDenVal (affineStepQ g μ)) :
    0 ≤ padicValRat 2 μ := by
  have hge := padicValRat_affineStepQ_ge g μ hμ hstep
  have hg' : (1 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hg
  unfold affineDenVal at heq
  omega

/-- **Odd reduced denominator from a nonnegative 2-adic valuation.**  If
`0 ≤ padicValRat 2 μ` then `μ.den` is odd (a 2-adic integer has odd denominator).
-/
theorem odd_den_of_nonneg_padicValRat {μ : ℚ} (h : 0 ≤ padicValRat 2 μ) :
    Odd μ.den := by
  rcases Nat.even_or_odd μ.den with he | ho
  · exfalso
    have hdvd : 2 ∣ μ.den := he.two_dvd
    have hden0 : μ.den ≠ 0 := μ.den_nz
    have h1 : 1 ≤ padicValNat 2 μ.den := one_le_padicValNat_of_dvd hden0 hdvd
    -- the numerator is coprime to the (even) denominator, so it is odd
    have hcop : Nat.gcd μ.num.natAbs μ.den = 1 := μ.reduced
    have hnum_not : ¬ (2 : ℤ) ∣ μ.num := by
      intro hd
      have h2nat : (2 : ℕ) ∣ μ.num.natAbs := by
        have := Int.natAbs_dvd_natAbs.mpr hd
        simpa using this
      have hg2 : (2 : ℕ) ∣ Nat.gcd μ.num.natAbs μ.den := Nat.dvd_gcd h2nat hdvd
      rw [hcop] at hg2
      exact absurd (Nat.dvd_one.mp hg2) (by norm_num)
    have hnum0 : padicValInt 2 μ.num = 0 := padicValInt.eq_zero_of_not_dvd hnum_not
    have hpv := padicValRat_def 2 μ
    rw [hnum0] at hpv
    simp only [Nat.cast_zero, zero_sub] at hpv
    omega
  · exact ho

/-! ## 3. The recurrent slope cycle has odd reduced denominators -/

/-- The cyclic successor on `Fin p` (the carry-fibre cycle edge `i ↦ (i+1) mod p`). -/
def affineCycSucc {p : ℕ} (hp : 0 < p) (i : Fin p) : Fin p :=
  ⟨(i.val + 1) % p, Nat.mod_lt _ hp⟩

/-- The cyclic successor is injective. -/
theorem affineCycSucc_injective {p : ℕ} (hp : 0 < p) :
    Function.Injective (affineCycSucc hp) := by
  intro a b hab
  unfold affineCycSucc at hab
  rw [Fin.mk.injEq] at hab
  have hmod : a.val ≡ b.val [MOD p] := Nat.ModEq.add_right_cancel' 1 hab
  have heq : a.val % p = b.val % p := hmod
  rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at heq
  exact Fin.ext heq

/-- The cyclic successor is a bijection of the finite cycle. -/
theorem affineCycSucc_bijective {p : ℕ} (hp : 0 < p) :
    Function.Bijective (affineCycSucc hp) :=
  Finite.injective_iff_bijective.mp (affineCycSucc_injective hp)

/--
**Headline: a recurrent slope cycle of the affine law has odd reduced
denominators.**

Let `μ : Fin p → ℚ` be a nonempty cyclic family of nonzero slopes with gaps
`g i ≥ 1`, obeying the E.13 affine law `μ (i+1) = affineStepQ (g i) (μ i)` on
every edge.  Then every slope `μ i` has odd reduced denominator.

The 2-adic monovariant `affineDenVal` is non-increasing on every edge, so it is
constant around the cycle; the strict-descent law then forces it to be `0`, i.e.
`0 ≤ v₂(μ i)`, i.e. `μ i` is a 2-adic integer with odd denominator.
-/
theorem cyclic_affineQ_den_odd {p : ℕ} (hp : 0 < p) (μ : Fin p → ℚ) (g : Fin p → ℕ)
    (hg : ∀ i, 1 ≤ g i) (hne : ∀ i, μ i ≠ 0)
    (hcyc : ∀ i : Fin p, μ (affineCycSucc hp i) = affineStepQ (g i) (μ i)) :
    ∀ i, Odd (μ i).den := by
  classical
  -- each image is nonzero
  have hstep : ∀ i, affineStepQ (g i) (μ i) ≠ 0 := by
    intro i; rw [← hcyc i]; exact hne (affineCycSucc hp i)
  -- the monovariant does not decrease along an edge
  have hmono : ∀ i, affineDenVal (μ i) ≤ affineDenVal (μ (affineCycSucc hp i)) := by
    intro i
    rw [hcyc i]
    exact affineDenVal_mono (g i) (μ i) (hne i) (hstep i)
  -- summed over the cycle, the edge map is a bijection, so the total is preserved
  have hsum : ∑ i, affineDenVal (μ i) = ∑ i, affineDenVal (μ (affineCycSucc hp i)) :=
    (Fintype.sum_bijective (affineCycSucc hp) (affineCycSucc_bijective hp)
      (fun i => affineDenVal (μ (affineCycSucc hp i))) (fun i => affineDenVal (μ i))
      (fun _ => rfl)).symm
  -- non-decreasing termwise with equal sums forces equality on every edge
  have heq : ∀ i ∈ (Finset.univ : Finset (Fin p)),
      affineDenVal (μ i) = affineDenVal (μ (affineCycSucc hp i)) :=
    (Finset.sum_eq_sum_iff_of_le (fun i _ => hmono i)).mp hsum
  intro i
  have heqi : affineDenVal (μ i) = affineDenVal (μ (affineCycSucc hp i)) :=
    heq i (Finset.mem_univ i)
  rw [hcyc i] at heqi
  exact odd_den_of_nonneg_padicValRat
    (affineDenVal_succ_eq_imp (g i) (μ i) (hg i) (hne i) (hstep i) heqi)

/-! ## 4. Connection to `CarryFibreCycleData` (the recurrent carry-fibre cycle) -/

/-- **Gap positivity is forced by open slopes.**  Since `0 < μ(step) = 2^g·μ − 1`
and `μ < 1`, a zero gap would give `μ(step) = μ − 1 < 0`, contradicting openness;
hence every carry-fibre cycle gap is `≥ 1`. -/
theorem CarryFibreCycleData.gap_pos (D : CarryFibreCycleData) (i : Fin D.n) :
    1 ≤ D.gap i := by
  rcases Nat.eq_zero_or_pos (D.gap i) with hg0 | hg
  · exfalso
    have htr := D.slope_trans i
    rw [hg0, pow_zero, one_mul] at htr
    linarith [htr, (D.slope_open ⟨(i.val + 1) % D.n, Nat.mod_lt _ D.hn⟩).1,
      (D.slope_open i).2]
  · exact hg

/--
**Every recurrent carry-fibre cycle has odd reduced denominators.**

If the real slopes of a `CarryFibreCycleData` are casts of rationals `μ i`
(`(μ i : ℝ) = D.slope i`), then each `μ i` has odd reduced denominator.  This is
the manuscript statement that the recurrent failing-shell slope `K/q` has odd
reduced denominator `q`, obtained by lifting the real E.13 recurrence
(`slope_trans`) to the rational affine law and running the 2-adic descent.
-/
theorem carryCycle_den_odd (D : CarryFibreCycleData) (μ : Fin D.n → ℚ)
    (hcast : ∀ i, (μ i : ℝ) = D.slope i) :
    ∀ i, Odd (μ i).den := by
  have hne : ∀ i, μ i ≠ 0 := by
    intro i hzero
    have hpos : (0 : ℝ) < D.slope i := (D.slope_open i).1
    rw [← hcast i, hzero] at hpos
    simp at hpos
  have hg : ∀ i, 1 ≤ D.gap i := fun i => D.gap_pos i
  have hcyc : ∀ i, μ (affineCycSucc D.hn i) = affineStepQ (D.gap i) (μ i) := by
    intro i
    have key : (μ (affineCycSucc D.hn i) : ℝ) = (affineStepQ (D.gap i) (μ i) : ℝ) := by
      rw [affineStepQ_cast, hcast i, hcast (affineCycSucc D.hn i)]
      exact D.slope_trans i
    exact_mod_cast key
  exact cyclic_affineQ_den_odd D.hn μ D.gap hg hne hcyc

/-! ## 5. The carry-side 2-adic root: `v₂(R_N)` grows across a zero run

The descent above is driven, at the level of the integer carry `R_N`
(`IntegerCarry.lean`), by the doubling identity `R_{N+h} = 2^h R_N` across a run
of zero digits: the 2-adic valuation of the carry grows by the run length, which
is precisely what cancels the slope denominator's 2-part. -/

/--
**2-adic valuation argument on `R_N`.**  Across a run of `h` zero digits after
position `N`, the integer carry doubles, so its 2-adic valuation grows by exactly
`h`: `v₂(R_{N+h}) = h + v₂(R_N)` (for `R_N ≠ 0`).
-/
theorem integerCarry_padicValInt_zero_run (Q : ℕ) (P : ℤ) (d : ℕ → ℕ) (N h : ℕ)
    (hR : integerCarry Q P d N ≠ 0)
    (hzero : ∀ j : ℕ, N < j → j ≤ N + h → d j = 0) :
    padicValInt 2 (integerCarry Q P d (N + h))
      = h + padicValInt 2 (integerCarry Q P d N) := by
  rw [integerCarry_add_of_zero_digits Q P d N h hzero]
  have h2 : ((2 : ℤ) ^ h) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [padicValInt.mul h2 hR]
  congr 1
  have hnat : ((2 : ℤ) ^ h).natAbs = 2 ^ h := by simp [Int.natAbs_pow]
  show padicValNat 2 ((2 : ℤ) ^ h).natAbs = h
  rw [hnat]
  exact padicValNat.prime_pow h

/-! ## 6. Consistency with the existing construction -/

/-- **A slope on an odd modulus has odd reduced denominator.**  Hence
`boundedSlopeDynamics`/`oddPartFibreDynamics`, which operate on an odd modulus
`q`, indeed carry odd-denominator slopes — consistent with `carryCycle_den_odd`.
-/
theorem den_odd_of_odd_modulus (K : ℤ) {q : ℕ} (hq : Odd q) :
    Odd (((K : ℚ) / (q : ℚ)).den) := by
  have hdvd : (((K : ℚ) / (q : ℚ)).den : ℤ) ∣ (q : ℤ) := by
    have hraw := Rat.den_dvd K (q : ℤ)
    rwa [Rat.divInt_eq_div, Int.cast_natCast] at hraw
  have hdvdN : ((K : ℚ) / (q : ℚ)).den ∣ q := by
    rwa [Int.natCast_dvd_natCast] at hdvd
  exact odd_of_dvd_odd hq hdvdN

/-! ## 7. Constructing the `TowerSlopeAtom` from AP-modulus geometry

The capstone atom `TowerSlopeAtom` carries `(Q, H, Q ≠ 0, Odd H, 2 ≤ H)`.  We
*construct* it from the genuinely geometric AP-modulus data, **proving** the
oddness field via `apModulus_odd` instead of assuming it. -/

/--
**`TowerSlopeAtom` from AP-modulus divisibility.**

Given a nonzero target denominator `Q`, two AP step moduli `h₁ ∣ 2^a − 1`,
`h₂ ∣ 2^b − 1` (manuscript `h_Γ ∣ D_Γ = 2^{S_Γ} − 1`), and the cycle
nontriviality `2 ≤ lcm h₁ h₂`, this builds a `TowerSlopeAtom` with `H = lcm h₁ h₂`
and `Odd H` discharged by `apModulus_odd` — the oddness field is now a *theorem*,
not a hypothesis.
-/
def towerSlopeAtomOfAPModuli
    (Q h₁ h₂ a b : ℕ) (hQ : Q ≠ 0) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hd₁ : h₁ ∣ 2 ^ a - 1) (hd₂ : h₂ ∣ 2 ^ b - 1)
    (hH2 : 2 ≤ Nat.lcm h₁ h₂) : TowerSlopeAtom where
  Q := Q
  H := Nat.lcm h₁ h₂
  hQ := hQ
  hH := apModulus_odd ha hb hd₁ hd₂
  hH2 := hH2

/--
**Tower transient factory data from AP-modulus geometry.**

Feeding `towerSlopeAtomOfAPModuli` through the proved `towerOfSlope` chain yields
the budget-respecting Phase-7 `TowerTransientFactoryData`, with finiteness, E.13
closure, the recurrent cycle and the Tower budget all already discharged by
`TowerLandingConstruction`, and the slope oddness now derived rather than assumed.
-/
def towerOfSlopeOfAPModuli
    (Q h₁ h₂ a b : ℕ) (hQ : Q ≠ 0) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hd₁ : h₁ ∣ 2 ^ a - 1) (hd₂ : h₂ ∣ 2 ^ b - 1)
    (hH2 : 2 ≤ Nat.lcm h₁ h₂) {X : ℝ} (hX : 0 ≤ X) :
    TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ X :=
  towerOfSlope (towerSlopeAtomOfAPModuli Q h₁ h₂ a b hQ ha hb hd₁ hd₂ hH2) hX

/-- **Non-vacuity.**  `Q = 1`, `h₁ = h₂ = 3 ∣ 2² − 1`, `lcm = 3 ≥ 2` builds a
genuine `TowerSlopeAtom` (slope modulus `3`, the `oneCycleExample` fixed point
`1/3`), with oddness proved. -/
theorem towerSlopeAtomOfAPModuli_nonvacuous :
    ∃ a : TowerSlopeAtom, a.H = 3 :=
  ⟨towerSlopeAtomOfAPModuli 1 3 3 2 2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num), by norm_num [towerSlopeAtomOfAPModuli]⟩

end

end Erdos260
