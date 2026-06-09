import Erdos260.RunObstructionRealization
import Erdos260.RunFactoryConstructor
import Erdos260.Residual

/-!
# Run §25.1 residual-cylinder provenance: deriving the §25.2 reduced data `(q₀, a, m)`

The sibling files `RunObstructionRealization.lean` and `RunFactoryConstructor.lean` reduced the
entire Run §25.1/§25.2 chain to *one* genuinely external datum: the **provenance** of a concrete
`(q₀, a, m)` for a given failing shell — that the run obstruction's mask point is a small-odd-
denominator rational `a/q₀` and that the window/denominator scale `4 q₀ ≤ m·ord_{q₀}(2)` holds.
Everything downstream of that datum (the periodicity `hold`, the four geometric realization fields,
the mean-low verdict, the L.4.2 one-step half-decrease, and the assembly into `RunFactoryData`) is
already PROVED there.

This file (NEW; it edits no existing file) attacks that last residual: it **derives** the §25.2
reduced data `(q₀, a, m)` from the §25.1 residual-cylinder geometry, reduced to its smallest honest
number-theoretic input.

## The genuine geometric input (STEP 3's "smallest input")

`ResidualCenter` bundles exactly the §25.1 output that the carry-tail / rational-prefix branch of
Lemma 25.1 leaves on the table: the residual cylinder's **center is a rational `ν/Qp`** with a small
denominator `Qp ≤ Q₀`, and it is **non-dyadic** — its denominator has a non-trivial odd part not
killed by the numerator (`¬ ordCompl[2] Qp ∣ ν`).  Non-dyadicity is precisely what distinguishes a
genuine run obstruction (a small-denominator *periodic* segment) from a clean dyadic cylinder; a
dyadic center would be routed to the clean/spike branches of §25.1, not to a run obstruction.

## What is genuinely CLOSED here (new content)

* `ResidualCenter.oddPart_odd` / `oddPart_pos` / `oddPart_le_den` — the 2-adic strip
  `q₀' = ordCompl[2] Qp` (the odd part of the denominator) is odd, positive, and `≤ Qp`.  This is
  the manuscript's "strip the 2-adic preperiod `q = 2^e q₀`".
* `ResidualCenter.q0_gt_one` / `q0_odd` / `q0_le_bound` / `coprime_a_q0` — the **§25.2 reduced
  data is DERIVED**: reducing `ν/q₀'` to lowest terms gives an odd denominator `q₀ > 1` with
  `q₀ ≤ Q₀` and a numerator `a` coprime to `q₀`.  These are exactly the `hq0/hodd/hcop` fields that
  `RunObstruction.ofMeanLowScale` consumes — no longer assumed, but produced from `ν/Qp`.
* `ResidualCenter.cross_mul` / `mask_eq_oddPart` — the **mask-point identity** `a/q₀ = ν/ordCompl[2] Qp`:
  the reduced odd-denominator fraction is exactly the 2-adic-stripped residual center.  This is the
  honest content of "the run obstruction's mask point *is* `a/q₀`".
* `ResidualCenter.scale` — the **scale `4 q₀ ≤ m·ord_{q₀}(2)` is DERIVED** with `m = 4 q₀` (using
  only `ord_{q₀}(2) ≥ 1`), so the canonical realization fires automatically.
* `ResidualCenter.toRunObstruction` / `toRunObstruction_halfDecrease` — the **actual run
  obstruction** built from `ν/Qp` through `RunObstruction.ofMeanLowScale`, with its L.4.2 one-step
  half-decrease firing on the genuine word `dyadicDigit q₀ a`.
* `ResidualCenter.provenance` — **the headline**: from a non-dyadic small-denominator center,
  `∃ (q₀ a m), Odd q₀ ∧ 1 < q₀ ∧ q₀ ≤ Q₀ ∧ Coprime a q₀ ∧ 0 < m ∧ 4 q₀ ≤ m·ord_{q₀}(2) ∧
  a/q₀ = ν/ordCompl[2] Qp`.  The full `(q₀, a, m)` provenance, derived.
* `ResidualCenter.provenance_of_cylinder_dichotomy` — the **tie to the proved §25.1 geometry**:
  feeding the genuine Lemma 25.1 hypotheses (eq 25.1 `M·Qp − ν·D = R` and the singular-square
  residual bound `|R|·2^{n₀} < D·Qp`) into the already-proved `residual_cylinder_dichotomy`, the
  mask point `M/D` sits in the same/adjacent depth-`n₀` cylinder as the center `ν/Qp`, **and** the
  reduced data yields a genuine run obstruction whose half-decrease fires.
* `ResidualCenter.toRunFactoryData` / `_runBound` — the provenance plugged straight into the
  capstone `RunFactoryData` via the proved `runFactoryDataOfScale`, meeting the Prop. I.5.2 budget
  `runMass ≤ cStar·ξ·X/6`.
* `residualCenterWitness` (`ν=1, Qp=3`) with `q0 = 3`, `a = 1`, a concrete non-vacuous instance.

## Honest status of the `(q₀, a, m)` provenance

**REDUCED to one geometric input, with the rest CLOSED.**  After this file:

* the §25.2 reduced data `(q₀, a)`, the scale `m`, the mask identity, the obstruction and its L.4.2
  half-decrease are **all DERIVED** from a single object `ResidualCenter` — the §25.1 residual
  cylinder center being a non-dyadic rational `ν/Qp` with `Qp ≤ Q₀`;
* the **one irreducible residual** is the binary-digit↔cylinder bridge: that the failing shell's
  *actual* mask word equals `dyadicDigit q₀ a`.  This is the very same bridge that Lemma 25.1's
  `lemma25_1_dyadicCylinderPrefix` documents as "outside this file" (the `hEqual`/`hAdjacent`
  carry-tail word primitives).  It is *not* re-assumed here; it is honestly the only thing between
  `provenance_of_cylinder_dichotomy` and a fully shell-internal identification.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

/-! ## Part A — the smallest genuine input and the 2-adic + gcd reduction -/

/-- Exact natural division: `x = g·k` with `g > 0` gives `x / g = k`. -/
private theorem natDiv_mul_left {x g k : ℕ} (hg : 0 < g) (h : x = g * k) : x / g = k := by
  rw [h]; exact Nat.mul_div_cancel_left k hg

/--
**The smallest genuine §25.1 geometric input: a non-dyadic small-denominator residual center.**

The carry-tail / rational-prefix branch of Lemma 25.1 deposits the residual mass onto a dyadic
cylinder whose center is a rational `num/den` with a small denominator `den ≤ bound`.  `hnondyadic`
records that this center is genuinely non-dyadic: the odd part `ordCompl[2] den` of the denominator
does not divide the numerator, i.e. `num/den` has a non-trivial odd denominator after 2-adic
stripping — exactly the case that produces a *periodic* small-denominator run segment rather than a
clean dyadic cylinder.
-/
structure ResidualCenter where
  /-- Numerator `ν` of the residual cylinder center. -/
  num : ℕ
  /-- Denominator `Qp` of the residual cylinder center (the §25.1 small denominator). -/
  den : ℕ
  /-- The §25.1 denominator bound `Q₀`. -/
  bound : ℕ
  /-- The denominator is positive. -/
  hden : 0 < den
  /-- The denominator is small: `Qp ≤ Q₀`. -/
  hbound : den ≤ bound
  /-- **Non-dyadicity**: the odd part of `Qp` does not divide `ν`, so `ν/Qp` is not dyadic. -/
  hnondyadic : ¬ (ordCompl[2] den ∣ num)

namespace ResidualCenter

variable (C : ResidualCenter)

/-- The 2-adic strip: the odd part `q₀' = ordCompl[2] Qp` of the denominator (manuscript
`q = 2^e q₀`). -/
def oddPart : ℕ := ordCompl[2] C.den

/-- The reduction factor `gcd(ν, q₀')`. -/
def gcdNum : ℕ := Nat.gcd C.num C.oddPart

/-- The §25.2 reduced odd denominator `q₀ = q₀' / gcd(ν, q₀')`. -/
def q0 : ℕ := C.oddPart / C.gcdNum

/-- The §25.2 reduced numerator `a = ν / gcd(ν, q₀')` (coprime to `q₀`). -/
def a : ℕ := C.num / C.gcdNum

/-- The period multiplier realizing the scale: `m = 4 q₀` (so `4 q₀ ≤ m·ord_{q₀}(2)` holds since
`ord ≥ 1`). -/
def scaleMult : ℕ := 4 * C.q0

theorem oddPart_pos : 0 < C.oddPart := Nat.ordCompl_pos 2 C.hden.ne'

theorem oddPart_odd : Odd C.oddPart := by
  have h := Nat.not_dvd_ordCompl Nat.prime_two C.hden.ne'
  rw [Nat.odd_iff]
  show ordCompl[2] C.den % 2 = 1
  omega

theorem oddPart_le_den : C.oddPart ≤ C.den := by
  show ordCompl[2] C.den ≤ C.den
  exact Nat.div_le_self _ _

theorem gcdNum_pos : 0 < C.gcdNum := Nat.gcd_pos_of_pos_right _ C.oddPart_pos

/-- The reduced denominator divides the odd part `q₀' = ordCompl[2] Qp`. -/
theorem q0_dvd_oddPart : C.q0 ∣ C.oddPart := by
  have hg_dvd : C.gcdNum ∣ C.oddPart := Nat.gcd_dvd_right _ _
  obtain ⟨kq, hkq⟩ := hg_dvd
  have hq : C.q0 = kq := natDiv_mul_left C.gcdNum_pos hkq
  exact ⟨C.gcdNum, by rw [hq, hkq]; ring⟩

/-- **Reduced denominator exceeds 1** — the genuine consequence of non-dyadicity: if the reduced
odd denominator were `1`, then `ν/Qp` would be dyadic (`q₀' ∣ ν`), contradicting `hnondyadic`. -/
theorem q0_gt_one : 1 < C.q0 := by
  have hg_dvd : C.gcdNum ∣ C.oddPart := Nat.gcd_dvd_right _ _
  obtain ⟨kq, hkq⟩ := hg_dvd
  have hq : C.q0 = kq := natDiv_mul_left C.gcdNum_pos hkq
  rw [hq]
  have hkq_pos : 0 < kq := by
    rcases Nat.eq_zero_or_pos kq with h0 | hp
    · rw [h0, Nat.mul_zero] at hkq
      have := C.oddPart_pos; omega
    · exact hp
  rcases Nat.lt_or_ge kq 2 with h | h
  · exfalso
    have hkq1 : kq = 1 := by omega
    have heq : C.oddPart = C.gcdNum := by rw [hkq, hkq1, Nat.mul_one]
    have hgnum : C.gcdNum ∣ C.num := Nat.gcd_dvd_left _ _
    have hodd_dvd : C.oddPart ∣ C.num := by rw [heq]; exact hgnum
    exact C.hnondyadic hodd_dvd
  · exact h

/-- **Reduced denominator is odd** — a divisor of the odd part `q₀'`. -/
theorem q0_odd : Odd C.q0 := by
  have hg_dvd : C.gcdNum ∣ C.oddPart := Nat.gcd_dvd_right _ _
  obtain ⟨kq, hkq⟩ := hg_dvd
  have hq : C.q0 = kq := natDiv_mul_left C.gcdNum_pos hkq
  have hfact : C.oddPart = C.gcdNum * C.q0 := by rw [hq]; exact hkq
  have hodd' : Odd C.oddPart := C.oddPart_odd
  rw [hfact] at hodd'
  exact (Nat.odd_mul.mp hodd').2

/-- **Reduced numerator is coprime to the reduced denominator** (lowest terms of `ν/q₀'`). -/
theorem coprime_a_q0 : Nat.Coprime C.a C.q0 := by
  have h := Nat.coprime_div_gcd_div_gcd (m := C.num) (n := C.oddPart) C.gcdNum_pos
  exact h

/-- **The small odd denominator stays bounded**: `q₀ ≤ Q₀` (since `q₀ ≤ q₀' ≤ Qp ≤ Q₀`). -/
theorem q0_le_bound : C.q0 ≤ C.bound := by
  have h1 : C.q0 ≤ C.oddPart := Nat.le_of_dvd C.oddPart_pos C.q0_dvd_oddPart
  exact le_trans (le_trans h1 C.oddPart_le_den) C.hbound

/-- **The mask-point cross-multiplication identity** `a · q₀' = ν · q₀`, i.e. `a/q₀ = ν/q₀'`. -/
theorem cross_mul : C.a * C.oddPart = C.num * C.q0 := by
  have hg_dvd_num : C.gcdNum ∣ C.num := Nat.gcd_dvd_left _ _
  have hg_dvd_odd : C.gcdNum ∣ C.oddPart := Nat.gcd_dvd_right _ _
  obtain ⟨ka, hka⟩ := hg_dvd_num
  obtain ⟨kq, hkq⟩ := hg_dvd_odd
  have ha : C.a = ka := natDiv_mul_left C.gcdNum_pos hka
  have hq : C.q0 = kq := natDiv_mul_left C.gcdNum_pos hkq
  rw [ha, hq, hka, hkq]; ring

/-- **The mask point IS `a/q₀`**: the reduced odd-denominator fraction equals the 2-adic-stripped
residual center `ν / ordCompl[2] Qp`. -/
theorem mask_eq_oddPart : (C.a : ℚ) / (C.q0 : ℚ) = (C.num : ℚ) / (C.oddPart : ℚ) := by
  have hq0 : (C.q0 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := C.q0_gt_one; omega)
  have hodd : (C.oddPart : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr C.oddPart_pos.ne'
  rw [div_eq_div_iff hq0 hodd]
  exact_mod_cast C.cross_mul

theorem order_pos : 0 < orderOf (2 : ZMod C.q0) :=
  orderOf_pos_iff.mpr (isOfFinOrder_two_zmod C.q0_gt_one C.q0_odd)

theorem scaleMult_pos : 0 < C.scaleMult := by
  show 0 < 4 * C.q0
  have := C.q0_gt_one; omega

/-- **The window/denominator scale `4 q₀ ≤ m·ord_{q₀}(2)` is DERIVED** with `m = 4 q₀`, using only
`ord_{q₀}(2) ≥ 1`. -/
theorem scale : 4 * C.q0 ≤ C.scaleMult * orderOf (2 : ZMod C.q0) := by
  show 4 * C.q0 ≤ 4 * C.q0 * orderOf (2 : ZMod C.q0)
  calc 4 * C.q0 = 4 * C.q0 * 1 := (Nat.mul_one _).symm
    _ ≤ 4 * C.q0 * orderOf (2 : ZMod C.q0) := Nat.mul_le_mul (le_refl _) C.order_pos

/-! ## Part B — the realized run obstruction from the residual center -/

/--
**The genuine run obstruction of the residual center.**

From the derived §25.2 reduced data (`q₀ > 1` odd, `a` coprime) and the derived scale
`4 q₀ ≤ m·ord_{q₀}(2)` (`m = 4 q₀`), the canonical realization `RunObstruction.ofMeanLowScale`
discharges the four geometric fields `hsize/hold/hbp_le_old/hoverlap` and the mean-low verdict
automatically.  This *is* the per-shell run obstruction, now constructed from `ν/Qp`.
-/
def toRunObstruction (u : ℕ) (weight : ℝ) : RunObstruction :=
  RunObstruction.ofMeanLowScale C.q0_gt_one C.q0_odd C.coprime_a_q0 C.scaleMult_pos C.scale u weight

@[simp] theorem toRunObstruction_q0 (u : ℕ) (weight : ℝ) :
    (C.toRunObstruction u weight).q0 = C.q0 := rfl

@[simp] theorem toRunObstruction_a (u : ℕ) (weight : ℝ) :
    (C.toRunObstruction u weight).a = C.a := rfl

/--
**The provenance fires the L.4.2 one-step half-decrease on the genuine word `dyadicDigit q₀ a`.**

A strictly shorter period `p'` with `2·p' ≤ m·ord_{q₀}(2)` — the manuscript's `wt(O_{i+1}) ≤ wt(O_i)/2`,
now resting on a `(q₀, a, m)` that was *derived* from the residual center `ν/Qp`.
-/
theorem toRunObstruction_halfDecrease (u : ℕ) (weight : ℝ) :
    ∃ p', PeriodicOn (dyadicDigit C.q0 C.a) u (2 * (C.scaleMult * orderOf (2 : ZMod C.q0))) p'
      ∧ 0 < p' ∧ 2 * p' ≤ C.scaleMult * orderOf (2 : ZMod C.q0) :=
  RunObstruction.ofMeanLowScale_halfDecrease C.q0_gt_one C.q0_odd C.coprime_a_q0
    C.scaleMult_pos C.scale u weight

/-! ## Part C — the headline provenance and the tie to the proved §25.1 geometry -/

/--
**Headline: the `(q₀, a, m)` provenance, DERIVED.**

From a non-dyadic small-denominator residual center `ν/Qp` (`Qp ≤ Q₀`), there exist the §25.2
reduced data `q₀` (odd, `> 1`, `≤ Q₀`) and `a` (coprime), and a positive period multiplier `m`
satisfying the scale `4 q₀ ≤ m·ord_{q₀}(2)`, with the mask-point identity `a/q₀ = ν/ordCompl[2] Qp`.
Everything `RunObstruction.ofMeanLowScale` / `runFactoryDataOfScale` consumes is produced here.
-/
theorem provenance :
    ∃ (q0 a m : ℕ),
      Odd q0 ∧ 1 < q0 ∧ q0 ≤ C.bound ∧ Nat.Coprime a q0 ∧ 0 < m ∧
        4 * q0 ≤ m * orderOf (2 : ZMod q0) ∧
        (a : ℚ) / (q0 : ℚ) = (C.num : ℚ) / (C.oddPart : ℚ) :=
  ⟨C.q0, C.a, C.scaleMult, C.q0_odd, C.q0_gt_one, C.q0_le_bound, C.coprime_a_q0,
    C.scaleMult_pos, C.scale, C.mask_eq_oddPart⟩

/--
**Tie to the proved Lemma 25.1 geometry.**

Feeding the genuine Lemma 25.1 hypotheses — eq (25.1) `M·Qp − ν·D = R` and the singular-square
residual bound `|R|·2^{n₀} < D·Qp` together with the two depth-`n₀` cylinder memberships — into the
already-proved `residual_cylinder_dichotomy`, the mask point `M/D` lies in the *same or adjacent*
depth-`n₀` dyadic cylinder as the residual center `ν/Qp`, **and** the reduced data of `ν/Qp` yields a
genuine run obstruction whose L.4.2 half-decrease fires on `dyadicDigit q₀ a`.

The only gap between this and a fully shell-internal identification is the binary-digit↔cylinder
bridge (that the mask word *is* `dyadicDigit q₀ a`), which Lemma 25.1 itself leaves open
(`lemma25_1_dyadicCylinderPrefix`'s `hEqual`/`hAdjacent` carry-tail primitives).
-/
theorem provenance_of_cylinder_dichotomy
    {M D R : ℝ} {n0 kM kν : ℕ}
    (hD : 0 < D)
    (hrel : M * (C.den : ℝ) - (C.num : ℝ) * D = R)
    (hRbound : |R| * 2 ^ n0 < D * (C.den : ℝ))
    (hcylM : DyadicCylinder n0 kM (M / D))
    (hcylν : DyadicCylinder n0 kν ((C.num : ℝ) / (C.den : ℝ)))
    (u : ℕ) (weight : ℝ) :
    (kM = kν ∨ kν = kM + 1 ∨ kM = kν + 1) ∧
      ∃ p', PeriodicOn (dyadicDigit C.q0 C.a) u
          (2 * (C.scaleMult * orderOf (2 : ZMod C.q0))) p'
        ∧ 0 < p' ∧ 2 * p' ≤ C.scaleMult * orderOf (2 : ZMod C.q0) := by
  have hQp : (0 : ℝ) < (C.den : ℝ) := by exact_mod_cast C.hden
  exact ⟨residual_cylinder_dichotomy hD hQp hrel hRbound hcylM hcylν,
    C.toRunObstruction_halfDecrease u weight⟩

/-! ## Part D — provenance into the capstone `RunFactoryData` -/

/--
**The provenance plugged into the capstone Run datum.**

Through the proved `runFactoryDataOfScale`, the derived `(q₀, a, m)` of the residual center builds a
full `RunFactoryData` (the datum the capstone `Erdos260MinimalAtoms` consumes).  The remaining
inputs are the genuinely shell-dependent analytic data `RunFactoryData` is *about*: the L.4.1
routing `D` and the per-shell budget `chain_capture / chainRoot_le / hSmall`.
-/
def toRunFactoryData {cStar xi X : ℝ} {α : Type*}
    (u : ℕ) (weight : ℝ) (D : RunRoutingData α) (len : ℕ) (hlen : 1 ≤ len)
    (smallError : ℝ) (hsmall_nonneg : 0 ≤ smallError) (twoNegcY Ij : ℝ)
    (chain_capture : D.toTri.chainMass ≤ ((C.scaleMult * orderOf (2 : ZMod C.q0) : ℕ) : ℝ))
    (chainRoot_le : 2 * ((C.scaleMult * orderOf (2 : ZMod C.q0) : ℕ) : ℝ) ≤ X * Ij * twoNegcY)
    (hSmall : D.towerBound + D.returnBound + D.densePackBound + X * Ij * twoNegcY + smallError
      ≤ cStar * xi * X / 6) :
    RunFactoryData cStar xi X :=
  runFactoryDataOfScale C.q0_gt_one C.q0_odd C.coprime_a_q0 C.scaleMult_pos C.scale u weight
    D len hlen smallError hsmall_nonneg twoNegcY Ij chain_capture chainRoot_le hSmall

/-- **The constructed Run datum meets the Prop. I.5.2 budget `runMass ≤ cStar·ξ·X/6`.** -/
theorem toRunFactoryData_runBound {cStar xi X : ℝ} {α : Type*}
    (u : ℕ) (weight : ℝ) (D : RunRoutingData α) (len : ℕ) (hlen : 1 ≤ len)
    (smallError : ℝ) (hsmall_nonneg : 0 ≤ smallError) (twoNegcY Ij : ℝ)
    (chain_capture : D.toTri.chainMass ≤ ((C.scaleMult * orderOf (2 : ZMod C.q0) : ℕ) : ℝ))
    (chainRoot_le : 2 * ((C.scaleMult * orderOf (2 : ZMod C.q0) : ℕ) : ℝ) ≤ X * Ij * twoNegcY)
    (hSmall : D.towerBound + D.returnBound + D.densePackBound + X * Ij * twoNegcY + smallError
      ≤ cStar * xi * X / 6) :
    (C.toRunFactoryData u weight D len hlen smallError hsmall_nonneg twoNegcY Ij
      chain_capture chainRoot_le hSmall).runMass ≤ cStar * xi * X / 6 :=
  runBound_of_factory _

end ResidualCenter

/-! ## Part E — concrete non-vacuity witness (`ν = 1, Qp = 3` ⟹ the `1/3` run obstruction) -/

/-- A concrete non-dyadic residual center `ν/Qp = 1/3` (odd denominator `3`, `¬ 3 ∣ 1`). -/
def residualCenterWitness : ResidualCenter where
  num := 1
  den := 3
  bound := 3
  hden := by norm_num
  hbound := le_refl 3
  hnondyadic := by
    have hfact : (3 : ℕ).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by decide)
    have h3 : ordCompl[2] (3 : ℕ) = 3 := by
      show (3 : ℕ) / 2 ^ ((3 : ℕ).factorization 2) = 3
      rw [hfact]; norm_num
    rw [h3]; decide

/-- The reduction computes the expected reduced denominator `q₀ = 3`. -/
theorem residualCenterWitness_q0 : residualCenterWitness.q0 = 3 := by
  have hfact : (3 : ℕ).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by decide)
  have h3 : ordCompl[2] (3 : ℕ) = 3 := by
    show (3 : ℕ) / 2 ^ ((3 : ℕ).factorization 2) = 3
    rw [hfact]; norm_num
  show ordCompl[2] (3 : ℕ) / Nat.gcd 1 (ordCompl[2] (3 : ℕ)) = 3
  rw [h3, Nat.gcd_one_left, Nat.div_one]

/-- The reduction computes the expected reduced numerator `a = 1`. -/
theorem residualCenterWitness_a : residualCenterWitness.a = 1 := by
  have hfact : (3 : ℕ).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by decide)
  have h3 : ordCompl[2] (3 : ℕ) = 3 := by
    show (3 : ℕ) / 2 ^ ((3 : ℕ).factorization 2) = 3
    rw [hfact]; norm_num
  show (1 : ℕ) / Nat.gcd 1 (ordCompl[2] (3 : ℕ)) = 1
  rw [h3, Nat.gcd_one_left, Nat.div_one]

/-- **The witness genuinely fires the L.4.2 half-decrease** on `dyadicDigit q₀ a` (non-vacuity of
the provenance on a real small-denominator word). -/
theorem residualCenterWitness_halfDecrease :
    ∃ p', PeriodicOn (dyadicDigit residualCenterWitness.q0 residualCenterWitness.a) 0
        (2 * (residualCenterWitness.scaleMult * orderOf (2 : ZMod residualCenterWitness.q0))) p'
      ∧ 0 < p' ∧ 2 * p' ≤ residualCenterWitness.scaleMult * orderOf (2 : ZMod residualCenterWitness.q0) :=
  residualCenterWitness.toRunObstruction_halfDecrease 0 0

theorem residualCenter_nonempty : Nonempty ResidualCenter := ⟨residualCenterWitness⟩

/-! ## Part F — residual inventory (honest) -/

/-- The honest status of the `(q₀, a, m)` provenance after this file. -/
def runProvenanceResiduals : List String :=
  [ "CLOSED (reduced data) — from a non-dyadic small-denominator residual center ν/Qp (Qp ≤ Q₀), " ++
      "the §25.2 reduced data q₀ odd > 1, a coprime, q₀ ≤ Q₀ is DERIVED by 2-adic stripping " ++
      "(ordCompl[2]) + gcd reduction: q0_odd, q0_gt_one, q0_le_bound, coprime_a_q0.",
    "CLOSED (scale) — the scale 4 q₀ ≤ m·ord_{q₀}(2) is DERIVED with m = 4 q₀ (ResidualCenter.scale), " ++
      "so ofMeanLowScale fires and the L.4.2 half-decrease holds on dyadicDigit q₀ a " ++
      "(toRunObstruction_halfDecrease).",
    "CLOSED (mask identity) — a/q₀ = ν/ordCompl[2] Qp (mask_eq_oddPart, cross_mul): the reduced " ++
      "odd-denominator fraction is the 2-adic-stripped residual center.",
    "REDUCED — the provenance rests on the single geometric input ResidualCenter (the §25.1 " ++
      "residual cylinder center is a non-dyadic rational ν/Qp with Qp ≤ Q₀); " ++
      "provenance_of_cylinder_dichotomy chains the proved residual_cylinder_dichotomy.",
    "IRREDUCIBLE — the binary-digit↔cylinder bridge: that the failing shell's actual mask WORD " ++
      "equals dyadicDigit q₀ a (the same primitive lemma25_1_dyadicCylinderPrefix leaves open)." ]

theorem runProvenanceResiduals_nonempty : runProvenanceResiduals ≠ [] := by
  simp [runProvenanceResiduals]

end

end Erdos260
