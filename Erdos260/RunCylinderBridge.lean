import Erdos260.Residual
import Erdos260.RunObstructionRealization
import Erdos260.RunProvenanceConstruction

/-!
# §25.1 binary-digit ↔ cylinder bridge: the mask word IS `dyadicDigit q₀ a`

`RunProvenanceConstruction.lean` reduced the entire Run §25.1/§25.2 provenance to **one** irreducible
residual: that the failing shell's *actual mask word* equals `dyadicDigit q₀ a`, the binary expansion
of the small-odd-denominator rational center `a/q₀`.  This is the very same primitive that
`Residual.lemma25_1_dyadicCylinderPrefix` documents as "outside this file" — its `hEqual`/`hAdjacent`
carry-tail word primitives.

This file (NEW; it edits no existing file) attacks that residual by genuinely **building** the
binary-digit ↔ cylinder bridge and proving the **equal-cylinder** identification.

## The genuine geometric object

For a real `x`, the *cylinder index* `cylinderIndex n x = ⌊2ⁿ·x⌋₊` is the integer `k` with
`DyadicCylinder n k x` (`dyadicCylinder_iff_bounds`, `cylinderIndex_eq_of_dyadicCylinder`), and the
*mask word* `binaryDigitWord x j = ⌊2ʲ⁺¹·x⌋₊ − 2·⌊2ʲ·x⌋₊` is the `(j+1)`-st binary digit of `x`.
The two are tied by `binaryDigitWord_eq_mod`: `binaryDigitWord x j = cylinderIndex (j+1) x % 2` — the
literal binary-digit ↔ cylinder identity.

## What is genuinely CLOSED here (the named residual, equal-cylinder case)

* `binaryDigitWord_ratCast` — **the center identification**: the mask word of the rational center
  `a/q₀` is *exactly* `dyadicDigit q₀ a` (a pure ℕ-arithmetic identity, every position, no hypothesis
  beyond `q₀ > 0`).  This is the honest content of "the mask point IS `a/q₀` whose digits are
  `dyadicDigit q₀ a`".
* `binaryDigitWord_eq_of_cylinderIndex_eq` — **the cylinder prefix bridge**: two reals sharing a
  depth-`n` dyadic cylinder have *identical* mask words on `[0, n)` (the manuscript's "the first `n`
  binary cylinders being equal forces exact agreement").  Proved from `Nat.floor_div_natCast`.
* `maskWord_eq_dyadicDigit_of_dyadicCylinder` — **THE BRIDGE, CLOSED**: if the mask point `M/D` lies
  in the *same* depth-`n` dyadic cylinder as the center `a/q₀`, then the mask word equals
  `dyadicDigit q₀ a` on the whole prefix `[0, n)`.  No carry-tail input.
* `rationalPrefixMatch_of_cylinderIndex_eq` — discharges Lemma 25.1's `hEqual` primitive for the
  concrete mask word: equal cylinders ⟹ `RationalPrefixMatch (binaryDigitWord (M/D)) n Qp`.
* `lemma25_1_dyadicCylinderPrefix_maskWord` — **plugs straight into the existing
  `Residual.lemma25_1_dyadicCylinderPrefix`**, supplying the `hEqual` argument as a *proof* (no longer
  an input); only the adjacent-cylinder carry-tail branch `hAdjacent` remains as input.
* `ResidualCenter.maskWord_eq_dyadicDigit` / `maskWord_eq_of_dyadicCylinder` /
  `provenance_maskWord_of_cylinder` — the bridge fed into the Run provenance: the run obstruction's
  word `dyadicDigit C.q0 C.a` *is* the mask word of the residual center, and (equal cylinder) *is* the
  failing shell's mask word — together with the already-proved L.4.2 half-decrease.
* `maskWord_oneThird` / `residualCenterWitness_maskWord` — the non-vacuity witness on `1/3`:
  `binaryDigitWord (1/3) = dyadicDigit 3 1`, and the full bridge fired on the `1/3` run obstruction.

## Honest status

* **CLOSED (equal cylinder)** — the named residual "the mask word equals `dyadicDigit q₀ a`" is
  PROVED in the equal-cylinder case: `maskWord_eq_dyadicDigit_of_dyadicCylinder`.  This is exactly the
  branch that feeds the *run obstruction* (Proposition 25.3 routes the equal/rational-prefix branch to
  the run output).  The Run provenance no longer needs the bridge as an external input in this case —
  it is `ResidualCenter.maskWord_eq_of_dyadicCylinder`.
* **REDUCED (adjacent cylinder)** — the remaining `hAdjacent` input of
  `lemma25_1_dyadicCylinderPrefix` is the genuine carry-tail word combinatorics: in an *adjacent*
  cylinder the mask word is a carry word `ξ0̄1⋯1` / `ξ1̄0⋯0` (binary of `kM` vs `kM±1`), and whether
  its carry tail exceeds `bound` (producing a dense/all-zero block) is a 2-adic valuation fact about
  `kM` that is genuinely shell-dependent.  This branch routes to the *non-run* dense/spike/clean
  outputs, not to the run obstruction.  It is precisely isolated as the lone remaining input.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## Part A — The cylinder index and the mask word -/

/-- The depth-`n` dyadic cylinder index of a real `x`: the integer `k = ⌊2ⁿ·x⌋₊` for which
`DyadicCylinder n k x` holds. -/
def cylinderIndex (n : ℕ) (x : ℝ) : ℕ := ⌊(2 : ℝ) ^ n * x⌋₊

/-- The `(j+1)`-st binary digit (mask word letter) of a real `x`:
`⌊2ʲ⁺¹·x⌋₊ − 2·⌊2ʲ·x⌋₊`. -/
def binaryDigitWord (x : ℝ) (j : ℕ) : ℕ := cylinderIndex (j + 1) x - 2 * cylinderIndex j x

/-- A depth-`n` dyadic cylinder membership is exactly the floor bounds `k ≤ 2ⁿ·x < k+1`. -/
theorem dyadicCylinder_iff_bounds {n k : ℕ} {x : ℝ} :
    DyadicCylinder n k x ↔ (k : ℝ) ≤ (2 : ℝ) ^ n * x ∧ (2 : ℝ) ^ n * x < (k : ℝ) + 1 := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  constructor
  · rintro ⟨h1, h2⟩
    rw [div_le_iff₀ hpow] at h1
    rw [lt_div_iff₀ hpow] at h2
    refine ⟨?_, ?_⟩
    · rw [mul_comm]; exact h1
    · rw [mul_comm]; push_cast at h2; linarith
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hpow, mul_comm x ((2 : ℝ) ^ n)]; exact h1
    · rw [lt_div_iff₀ hpow, mul_comm x ((2 : ℝ) ^ n)]; push_cast; linarith

/-- A dyadic cylinder pins down the cylinder index: `DyadicCylinder n k x ⟹ cylinderIndex n x = k`. -/
theorem cylinderIndex_eq_of_dyadicCylinder {n k : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (h : DyadicCylinder n k x) : cylinderIndex n x = k := by
  have hr : (0 : ℝ) ≤ (2 : ℝ) ^ n * x := by positivity
  rw [dyadicCylinder_iff_bounds] at h
  exact (Nat.floor_eq_iff hr).mpr h

/-- Conversely, every nonnegative real lies in its own cylinder index cylinder. -/
theorem dyadicCylinder_cylinderIndex {n : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    DyadicCylinder n (cylinderIndex n x) x := by
  have hr : (0 : ℝ) ≤ (2 : ℝ) ^ n * x := by positivity
  rw [dyadicCylinder_iff_bounds]
  exact (Nat.floor_eq_iff hr).mp rfl

/-- **The cylinder-index telescoping**: a shallower index is the deeper one divided by the depth
gap.  This is the engine of the prefix bridge, from `Nat.floor_div_natCast`. -/
theorem cylinderIndex_eq_add_div (m d : ℕ) (x : ℝ) :
    cylinderIndex m x = cylinderIndex (m + d) x / 2 ^ d := by
  have h2d : (2 : ℝ) ^ d ≠ 0 := by positivity
  unfold cylinderIndex
  rw [← Nat.floor_div_natCast]
  congr 1
  push_cast
  rw [eq_div_iff h2d, pow_add]
  ring

/-- Equal deep cylinder indices propagate to all shallower depths. -/
theorem cylinderIndex_eq_of_le {m n : ℕ} {x y : ℝ} (hmn : m ≤ n)
    (h : cylinderIndex n x = cylinderIndex n y) :
    cylinderIndex m x = cylinderIndex m y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [cylinderIndex_eq_add_div m d x, cylinderIndex_eq_add_div m d y, h]

/-- **The literal binary-digit ↔ cylinder identity**: the `j`-th mask letter is the parity of the
depth-`(j+1)` cylinder index. -/
theorem binaryDigitWord_eq_mod (x : ℝ) (j : ℕ) :
    binaryDigitWord x j = cylinderIndex (j + 1) x % 2 := by
  have hj1 : cylinderIndex j x = cylinderIndex (j + 1) x / 2 := by
    have h := cylinderIndex_eq_add_div j 1 x
    simpa using h
  unfold binaryDigitWord
  rw [hj1]
  have h := Nat.div_add_mod (cylinderIndex (j + 1) x) 2
  omega

/-- Every mask letter is a bit. -/
theorem binaryDigitWord_le_one (x : ℝ) (j : ℕ) : binaryDigitWord x j ≤ 1 := by
  rw [binaryDigitWord_eq_mod]; omega

/-- **The mask letter is literally a bit of the cylinder index.**  For `j < n`, the `j`-th mask
letter of `x` is bit `n−1−j` (MSB-first) of the depth-`n` cylinder index `k = cylinderIndex n x`.
So the mask word on `[0, n)` *is* the `n`-bit binary representation of the cylinder index — the
sharpest form of the binary-digit ↔ cylinder identity. -/
theorem binaryDigitWord_eq_cylinderBit {n j : ℕ} (hj : j < n) {x : ℝ} {k : ℕ}
    (hk : cylinderIndex n x = k) :
    binaryDigitWord x j = k / 2 ^ (n - 1 - j) % 2 := by
  rw [binaryDigitWord_eq_mod, cylinderIndex_eq_add_div (j + 1) (n - 1 - j) x,
    show (j + 1) + (n - 1 - j) = n by omega, hk]

/-- **The cylinder prefix bridge**: two reals in the same depth-`n` dyadic cylinder have identical
mask words on the whole prefix `[0, n)`.  (In the *adjacent*-cylinder case this fails precisely by a
binary carry: by `binaryDigitWord_eq_cylinderBit` the two prefixes are then the `n`-bit
representations of `k` and `k ± 1`, the manuscript's carry words `ξ0̄1⋯1` / `ξ1̄0⋯0`.) -/
theorem binaryDigitWord_eq_of_cylinderIndex_eq {n : ℕ} {x y : ℝ}
    (h : cylinderIndex n x = cylinderIndex n y) {j : ℕ} (hj : j < n) :
    binaryDigitWord x j = binaryDigitWord y j := by
  rw [binaryDigitWord_eq_mod, binaryDigitWord_eq_mod,
    cylinderIndex_eq_of_le (by omega : j + 1 ≤ n) h]

/-! ## Part B — The center identification: the mask word of `a/q₀` is `dyadicDigit q₀ a` -/

/-- The cylinder index of the rational `a/q₀` is the integer division `(2ⁿ·a)/q₀`. -/
theorem cylinderIndex_ratCast (q0 a j : ℕ) :
    cylinderIndex j ((a : ℝ) / (q0 : ℝ)) = (2 ^ j * a) / q0 := by
  unfold cylinderIndex
  have h : (2 : ℝ) ^ j * ((a : ℝ) / (q0 : ℝ)) = ((2 ^ j * a : ℕ) : ℝ) / ((q0 : ℕ) : ℝ) := by
    push_cast; ring
  rw [h, Nat.floor_div_eq_div]

/--
**The center identification (CLOSED).**

The mask word of the rational center `a/q₀` is *exactly* the §25.2 dyadic digit sequence
`dyadicDigit q₀ a`, at every position.  Pure ℕ-arithmetic from the binary-division recurrence
`2·rⱼ = εⱼ₊₁·q₀ + rⱼ₊₁`.
-/
theorem binaryDigitWord_ratCast {q0 : ℕ} (hq0 : 0 < q0) (a j : ℕ) :
    binaryDigitWord ((a : ℝ) / (q0 : ℝ)) j = dyadicDigit q0 a j := by
  unfold binaryDigitWord
  rw [cylinderIndex_ratCast q0 a (j + 1), cylinderIndex_ratCast q0 a j]
  simp only [dyadicDigit, dyadicResidue, binaryQuotient]
  set m := 2 ^ j * a with hm
  have h21 : 2 ^ (j + 1) * a = 2 * m := by rw [hm, pow_succ]; ring
  rw [h21]
  have hnum : 2 * m = 2 * (m % q0) + 2 * (m / q0) * q0 := by
    have h : q0 * (m / q0) + m % q0 = m := Nat.div_add_mod m q0
    calc 2 * m = 2 * (q0 * (m / q0) + m % q0) := by rw [h]
      _ = 2 * (m % q0) + 2 * (m / q0) * q0 := by ring
  have key : (2 * m) / q0 = (2 * (m % q0)) / q0 + 2 * (m / q0) := by
    rw [hnum, Nat.add_mul_div_right _ _ hq0]
  rw [key]; exact Nat.add_sub_cancel _ _

/-! ## Part C — The bridge and the discharge of Lemma 25.1's `hEqual` primitive -/

/--
**THE BRIDGE, CLOSED.**

If the mask point `M/D` (`= x`) lies in the *same* depth-`n` dyadic cylinder as the rational center
`a/q₀`, then the failing shell's mask word `binaryDigitWord x` equals the §25.2 word
`dyadicDigit q₀ a` on the whole prefix `[0, n)`.  This is the binary-digit ↔ cylinder bridge that
`lemma25_1_dyadicCylinderPrefix` left open, in its equal-cylinder case.
-/
theorem maskWord_eq_dyadicDigit_of_dyadicCylinder
    {q0 a : ℕ} (hq0 : 0 < q0) {x : ℝ} {n kM kν : ℕ}
    (hx : 0 ≤ x) (hk : kM = kν)
    (hcylx : DyadicCylinder n kM x)
    (hcylc : DyadicCylinder n kν ((a : ℝ) / (q0 : ℝ))) :
    ∀ j, j < n → binaryDigitWord x j = dyadicDigit q0 a j := by
  intro j hj
  have hkeq : cylinderIndex n x = cylinderIndex n ((a : ℝ) / (q0 : ℝ)) := by
    rw [cylinderIndex_eq_of_dyadicCylinder hx hcylx,
      cylinderIndex_eq_of_dyadicCylinder (by positivity) hcylc, hk]
  rw [binaryDigitWord_eq_of_cylinderIndex_eq hkeq hj, binaryDigitWord_ratCast hq0]

/-- The `hEqual` discharge for the concrete mask word: equal cylinder indices ⟹
`RationalPrefixMatch (binaryDigitWord x) n Qp` (denominator `q₀ ≤ Qp`, digits `dyadicDigit q₀ a`). -/
theorem rationalPrefixMatch_of_cylinderIndex_eq {q0 a Qp n : ℕ} (hq0 : 0 < q0) (hq0_le : q0 ≤ Qp)
    {x : ℝ} (hk : cylinderIndex n x = cylinderIndex n ((a : ℝ) / (q0 : ℝ))) :
    RationalPrefixMatch (binaryDigitWord x) n Qp := by
  refine ⟨dyadicDigit q0 a, q0, hq0, hq0_le, ?_, ?_⟩
  · intro i _
    have h := dyadicDigit_le_one hq0 a i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  · intro i hi
    rw [binaryDigitWord_eq_of_cylinderIndex_eq hk hi, binaryDigitWord_ratCast hq0]

/--
**Discharging Lemma 25.1's `hEqual` primitive (plugs into the existing `Residual` lemma).**

This is `Residual.lemma25_1_dyadicCylinderPrefix` specialized to the concrete mask word
`w = binaryDigitWord (M/D)`, with the `hEqual` carry-tail primitive supplied as a *proof* — the
equal-cylinder branch is now the proved bridge, not an input.  Only the adjacent-cylinder carry-tail
branch `hAdjacent` (routed to the non-run dense/spike/clean outputs) remains an input.

`hcenter : ν/Qp = a/q₀` records that the §25.1 residual center `ν/Qp` is the small-odd-denominator
rational `a/q₀` (the 2-adic-stripped center, automatic when `Qp` is odd).
-/
theorem lemma25_1_dyadicCylinderPrefix_maskWord
    {M D ν R : ℝ} {a q0 : ℕ} {p n0 kM kν : ℕ} {bound Qp : ℕ}
    (hq0 : 0 < q0) (hq0_le : q0 ≤ Qp)
    (hD : 0 < D) (hQp : 0 < Qp)
    (hM : 0 ≤ M / D)
    (hrel : M * (Qp : ℝ) - ν * D = R)
    (hRbound : |R| * 2 ^ n0 < D * (Qp : ℝ))
    (hcylM : DyadicCylinder n0 kM (M / D))
    (hcylν : DyadicCylinder n0 kν (ν / (Qp : ℝ)))
    (hcenter : ν / (Qp : ℝ) = (a : ℝ) / (q0 : ℝ))
    (hAdjacent : (kν = kM + 1 ∨ kM = kν + 1) →
      DenseAllOneBlock (binaryDigitWord (M / D)) p bound ∨
        AllZeroBlock (binaryDigitWord (M / D)) p bound) :
    DenseAllOneBlock (binaryDigitWord (M / D)) p bound ∨
      AllZeroBlock (binaryDigitWord (M / D)) p bound ∨
      RationalPrefixMatch (binaryDigitWord (M / D)) n0 Qp :=
  lemma25_1_dyadicCylinderPrefix hD hQp hrel hRbound hcylM hcylν
    (fun hk => by
      have hcylc : DyadicCylinder n0 kν ((a : ℝ) / (q0 : ℝ)) := hcenter ▸ hcylν
      have hkeq : cylinderIndex n0 (M / D) = cylinderIndex n0 ((a : ℝ) / (q0 : ℝ)) := by
        rw [cylinderIndex_eq_of_dyadicCylinder hM hcylM,
          cylinderIndex_eq_of_dyadicCylinder (by positivity) hcylc, hk]
      exact rationalPrefixMatch_of_cylinderIndex_eq hq0 hq0_le hkeq)
    hAdjacent

/-! ## Part D — Feeding the bridge into the Run provenance (`ResidualCenter`) -/

namespace ResidualCenter

variable (C : ResidualCenter)

/-- The reduced denominator is positive (consequence of `q₀ > 1`). -/
theorem q0_pos : 0 < C.q0 := by have := C.q0_gt_one; omega

/-- The real-valued mask-point identity `a/q₀ = ν/ordCompl[2] Qp` (the ℝ form of `mask_eq_oddPart`). -/
theorem maskReal_eq : (C.a : ℝ) / (C.q0 : ℝ) = (C.num : ℝ) / (C.oddPart : ℝ) := by
  have hq0 : (C.q0 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr C.q0_pos.ne'
  have hodd : (C.oddPart : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr C.oddPart_pos.ne'
  rw [div_eq_div_iff hq0 hodd]
  exact_mod_cast C.cross_mul

/--
**The run obstruction's word IS the mask word of the residual center (CLOSED).**

`dyadicDigit C.q0 C.a` — the word on which `ResidualCenter.toRunObstruction` fires the L.4.2
half-decrease — is *exactly* the binary expansion (mask word) of the small-odd-denominator center
`a/q₀ = ν/ordCompl[2] Qp`.  This is the honest content of "the run obstruction's mask point is
`a/q₀`".
-/
theorem maskWord_eq_dyadicDigit (j : ℕ) :
    binaryDigitWord ((C.a : ℝ) / (C.q0 : ℝ)) j = dyadicDigit C.q0 C.a j :=
  binaryDigitWord_ratCast C.q0_pos C.a j

/--
**The bridge fed into the Run provenance.**

If the failing shell's mask point `M/D` shares the depth-`n` dyadic cylinder of the residual center
`a/q₀`, then the actual mask word `binaryDigitWord (M/D)` equals the run obstruction's word
`dyadicDigit C.q0 C.a` on the prefix `[0, n)`.  The Run provenance no longer needs the
binary-digit ↔ cylinder bridge as an external input in this (equal-cylinder, run) case.
-/
theorem maskWord_eq_of_dyadicCylinder {M D : ℝ} {n kM kν : ℕ}
    (hM : 0 ≤ M / D) (hk : kM = kν)
    (hcylM : DyadicCylinder n kM (M / D))
    (hcylc : DyadicCylinder n kν ((C.a : ℝ) / (C.q0 : ℝ))) :
    ∀ j, j < n → binaryDigitWord (M / D) j = dyadicDigit C.q0 C.a j :=
  maskWord_eq_dyadicDigit_of_dyadicCylinder C.q0_pos hM hk hcylM hcylc

/--
**Headline: the §25.1 cylinder geometry + the closed bridge + the L.4.2 half-decrease.**

Feeding the genuine eq-(25.1) hypotheses for the stripped odd-denominator center `a/q₀`
(`M·q₀ − a·D = R` and the singular-square residual bound `|R|·2ⁿ⁰ < D·q₀`) into the already-proved
`residual_cylinder_dichotomy`, the mask point `M/D` sits in the *same or adjacent* depth-`n₀` cylinder
as the center.  In the **equal** case the actual mask word `binaryDigitWord (M/D)` IS the run
obstruction's word `dyadicDigit C.q0 C.a` on `[0, n₀)` (the closed bridge), **and** the obstruction's
L.4.2 one-step half-decrease fires on that word.
-/
theorem provenance_maskWord_of_cylinder
    {M D R : ℝ} {n0 kM kν : ℕ}
    (hD : 0 < D) (hM : 0 ≤ M / D)
    (hrel : M * (C.q0 : ℝ) - (C.a : ℝ) * D = R)
    (hRbound : |R| * 2 ^ n0 < D * (C.q0 : ℝ))
    (hcylM : DyadicCylinder n0 kM (M / D))
    (hcylc : DyadicCylinder n0 kν ((C.a : ℝ) / (C.q0 : ℝ)))
    (u : ℕ) (weight : ℝ) :
    (kM = kν ∨ kν = kM + 1 ∨ kM = kν + 1) ∧
      (kM = kν → ∀ j, j < n0 → binaryDigitWord (M / D) j = dyadicDigit C.q0 C.a j) ∧
      ∃ p', PeriodicOn (dyadicDigit C.q0 C.a) u
          (2 * (C.scaleMult * orderOf (2 : ZMod C.q0))) p'
        ∧ 0 < p' ∧ 2 * p' ≤ C.scaleMult * orderOf (2 : ZMod C.q0) := by
  have hq0R : (0 : ℝ) < (C.q0 : ℝ) := by exact_mod_cast C.q0_pos
  refine ⟨residual_cylinder_dichotomy hD hq0R hrel hRbound hcylM hcylc, ?_,
    C.toRunObstruction_halfDecrease u weight⟩
  intro hk j hj
  exact C.maskWord_eq_of_dyadicCylinder hM hk hcylM hcylc j hj

end ResidualCenter

/-! ## Part E — Concrete non-vacuity witness on `1/3` -/

/-- **The mask word of `1/3` is `dyadicDigit 3 1`** (the `1/3` run obstruction's word). -/
theorem maskWord_oneThird (j : ℕ) :
    binaryDigitWord ((1 : ℝ) / (3 : ℝ)) j = dyadicDigit 3 1 j := by
  have h := binaryDigitWord_ratCast (q0 := 3) (by norm_num) 1 j
  simpa using h

/-- The residual-center witness (`ν=1, Qp=3 ⟹ q₀=3, a=1`) has mask word `dyadicDigit 3 1`. -/
theorem residualCenterWitness_maskWord (j : ℕ) :
    binaryDigitWord ((residualCenterWitness.a : ℝ) / (residualCenterWitness.q0 : ℝ)) j
      = dyadicDigit residualCenterWitness.q0 residualCenterWitness.a j :=
  residualCenterWitness.maskWord_eq_dyadicDigit j

/-- **The bridge fired on `1/3`** (non-vacuity): the mask point `1/3` shares its own depth-`n`
cylinder, so its mask word equals `dyadicDigit 3 1` on `[0, n)`. -/
theorem maskWord_eq_dyadicDigit_oneThird (n : ℕ) :
    ∀ j, j < n → binaryDigitWord ((1 : ℝ) / 3) j = dyadicDigit 3 1 j := by
  have hx : (0 : ℝ) ≤ (1 : ℝ) / 3 := by norm_num
  have hc : ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = (1 : ℝ) / 3 := by norm_num
  have hcyl : DyadicCylinder n (cylinderIndex n ((1 : ℝ) / 3)) ((1 : ℝ) / 3) :=
    dyadicCylinder_cylinderIndex hx
  have hcylc : DyadicCylinder n (cylinderIndex n ((1 : ℝ) / 3)) (((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) := by
    rw [hc]; exact hcyl
  intro j hj
  have := maskWord_eq_dyadicDigit_of_dyadicCylinder (q0 := 3) (a := 1) (by norm_num)
    hx rfl hcyl hcylc j hj
  simpa using this

/-! ## Part F — Honest residual inventory -/

/-- The honest status of the §25.1 binary-digit ↔ cylinder bridge after this file. -/
def runCylinderBridgeResiduals : List String :=
  [ "CLOSED (center identification) — binaryDigitWord_ratCast: the mask word of the rational " ++
      "center a/q₀ is exactly dyadicDigit q₀ a at every position (pure ℕ arithmetic).",
    "CLOSED (cylinder prefix bridge) — binaryDigitWord_eq_of_cylinderIndex_eq: two reals in the " ++
      "same depth-n dyadic cylinder have identical mask words on [0,n) (from Nat.floor_div_natCast).",
    "CLOSED (THE BRIDGE, equal cylinder) — maskWord_eq_dyadicDigit_of_dyadicCylinder: if the mask " ++
      "point M/D shares the depth-n cylinder of a/q₀, the actual mask word equals dyadicDigit q₀ a " ++
      "on [0,n). This is the named residual, discharged; it feeds Lemma 25.1's hEqual " ++
      "(lemma25_1_dyadicCylinderPrefix_maskWord) and the Run provenance " ++
      "(ResidualCenter.maskWord_eq_of_dyadicCylinder).",
    "REDUCED (adjacent cylinder) — the lone remaining input hAdjacent of " ++
      "lemma25_1_dyadicCylinderPrefix is the carry-tail word combinatorics. By " ++
      "binaryDigitWord_eq_cylinderBit the mask prefix on [0,n) IS the n-bit binary representation " ++
      "of the cylinder index k; an adjacent cylinder gives the carry words ξ0̄1⋯1 / ξ1̄0⋯0 (binary " ++
      "of kM vs kM±1), and whether the carry tail exceeds bound is a shell-dependent 2-adic " ++
      "valuation fact about kM. This branch routes to the non-run dense/spike/clean outputs, not " ++
      "to the run obstruction." ]

theorem runCylinderBridgeResiduals_nonempty : runCylinderBridgeResiduals ≠ [] := by
  simp [runCylinderBridgeResiduals]

end

end Erdos260
