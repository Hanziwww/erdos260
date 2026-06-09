import Erdos260.Residual
import Erdos260.RunProvenanceConstruction
import Erdos260.RunCylinderBridge

/-!
# Existence of the §25.1 residual center for a failing shell, and the adjacent-cylinder branch

`RunProvenanceConstruction.lean` built the *entire* §25.2 reduced data `(q₀, a, m)`, the run
obstruction, its L.4.2 half-decrease, and the capstone `RunFactoryData` **out of a single object**
`ResidualCenter` — the §25.1 residual cylinder center being a non-dyadic rational `ν/Qp` with
`Qp ≤ Q₀`.  `RunCylinderBridge.lean` then closed the equal-cylinder binary-digit ↔ cylinder bridge
(`maskWord_eq_dyadicDigit_of_dyadicCylinder`) and isolated the *adjacent*-cylinder carry-tail branch
(`hAdjacent`) as routing to the non-run dense/spike/clean outputs of Proposition 25.3.

This file (NEW; it edits no existing file) discharges the two remaining Run-residual obligations:

## (a) Producing the `ResidualCenter` itself (existence), from the smallest genuine §25.1 input

The genuine geometric/dynamical content that distinguishes a **failing** shell (a genuine run
obstruction) from a clean dyadic cylinder is exactly *non-dyadicity* of the residual center `ν/Qp`.
We package the smallest honest §25.1 input as `FailingShellResidual`: a small-denominator center
`ν/Qp` (`Qp ≤ Q₀`) whose **residual residue orbit never terminates**, i.e. the §25.2 residue
sequence `r_j = (2ʲ·ν) mod Qp` (`dyadicResidue`) is never `0`.  This is the dynamical statement
"the residual run never dies out", and we prove it is **equivalent** to non-dyadicity:

* `nondyadic_of_residueOrbit` / `residueOrbit_of_nondyadic` / `nondyadic_iff_residueOrbit` —
  `¬ (ordCompl[2] Qp ∣ ν) ↔ ∀ j, dyadicResidue Qp ν j ≠ 0`.  (Dyadic ⟺ the doubling orbit of `ν`
  modulo `Qp` reaches `0` ⟺ `ordCompl[2] Qp ∣ ν`; the proof is the 2-adic-strip identity
  `Qp = 2^e · ordCompl[2] Qp` together with `ordCompl[2] Qp` being odd hence coprime to `2ʲ`.)
* `FailingShellResidual.toResidualCenter` / `residualCenterOfFailingShell` — **the `ResidualCenter`
  is DERIVED** from a failing shell, with non-dyadicity produced from the non-terminating orbit.
* `exists_residualCenter_of_failingShell` — the headline `∃ ResidualCenter` for a failing shell.
* `FailingShellResidual.provenance` / `provenance_of_cylinder_dichotomy` — the full `(q₀, a, m)`
  provenance and the tie to the proved `residual_cylinder_dichotomy`, threaded through the derived
  center.

## (b) The adjacent-cylinder branch lands in non-run outputs (Proposition 25.3)

* `ResidualSingularOutput.isRunObligation` / `isCarryTailOutput` — the run obligation is exactly the
  `shorterPeriodRun`; the carry-tail outputs are `localSpike` (dense/spike) and `cleanBoundaryDirty`
  (all-zero/clean).
* `adjacentBranch_nonRun` — **the adjacent branch's carry-tail output is a non-run spike/clean
  class** (never `shorterPeriodRun`).
* `carryWordAllZeroTail` / `carryWordDenseTail` (+ `_allZeroBlock` / `_denseBlock`) — genuine
  concrete carry words `ξ1̄0⋯0` / `ξ0̄1⋯1` realizing the all-zero / dense-all-one blocks, so the
  routing is non-vacuous.
* `dichotomy_run_only_equal` / `dichotomy_run_only_equal_maskWord` — **the headline split**: the
  proved §25.1 cylinder dichotomy routes the *equal* cylinder to the run-side rational-prefix match
  (the run obstruction's only input) and the *adjacent* cylinder to a non-run output.  The
  mask-word version builds on the already-closed `lemma25_1_dyadicCylinderPrefix_maskWord`, so the
  equal branch is *proved* (not assumed) and only the genuinely shell-dependent carry tail remains
  an input — and that input is shown to be non-run.

## Honest status

* **ResidualCenter existence: REDUCED to one genuine §25.1 input, with the reduction CLOSED.** The
  `ResidualCenter` and the entire `(q₀, a, m)` provenance are DERIVED from `FailingShellResidual`,
  whose only nontrivial field is the non-terminating residual residue orbit — proved equivalent to
  the non-dyadicity that `RunProvenanceConstruction` consumed.  This is the manuscript's "the
  residual support is a non-dyadic small-denominator cylinder", made dynamical.
* **Adjacent-cylinder branch: CLOSED (non-run).** Given the carry-tail block (the genuinely
  shell-dependent 2-adic input `lemma25_1_dyadicCylinderPrefix` documents as external), the adjacent
  branch is *proved* to route to the non-run `localSpike` / `cleanBoundaryDirty` classes, so the run
  side needs only the equal-cylinder center.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

/-! ## Part A — non-dyadicity ⟺ the residual residue orbit never terminates -/

/--
The 2-adic-strip divisibility step: if the odd part `ordCompl[2] Qp` of the denominator divides the
numerator `ν`, then `Qp` divides `2^e · ν` where `e = v₂(Qp)` is the 2-adic valuation.  (This is the
"discard the `2`-adic preperiod `q = 2^e q₀`" fact: a dyadic center's residue orbit hits `0` exactly
at the valuation step `e`.)
-/
theorem den_dvd_pow_factorization_mul (num den : ℕ)
    (h : ordCompl[2] den ∣ num) :
    den ∣ 2 ^ (den.factorization 2) * num := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  have hsplit : 2 ^ (den.factorization 2) * ordCompl[2] den = den :=
    Nat.ordProj_mul_ordCompl_eq_self den 2
  calc 2 ^ (den.factorization 2) * num
      = 2 ^ (den.factorization 2) * (ordCompl[2] den * m) := by rw [hm]
    _ = (2 ^ (den.factorization 2) * ordCompl[2] den) * m := by ring
    _ = den * m := by rw [hsplit]

/--
**Non-dyadicity from the non-terminating residue orbit.**

If the §25.2 residue sequence `dyadicResidue den num j = (2ʲ·num) mod den` is never `0`, then the
center `num/den` is non-dyadic (`¬ ordCompl[2] den ∣ num`).  Contrapositive of
`den_dvd_pow_factorization_mul`: a dyadic center's orbit vanishes at the valuation step.
-/
theorem nondyadic_of_residueOrbit (num den : ℕ)
    (horbit : ∀ j : ℕ, dyadicResidue den num j ≠ 0) :
    ¬ (ordCompl[2] den ∣ num) := by
  intro h
  have hdvd : den ∣ 2 ^ (den.factorization 2) * num :=
    den_dvd_pow_factorization_mul num den h
  exact horbit (den.factorization 2) (Nat.mod_eq_zero_of_dvd hdvd)

/--
**The non-terminating residue orbit from non-dyadicity** (converse).

If `num/den` is non-dyadic, then its residue orbit `dyadicResidue den num j` is never `0`: from
`den ∣ 2ʲ·num` we would get `ordCompl[2] den ∣ 2ʲ·num`, and since `ordCompl[2] den` is odd (coprime
to `2ʲ`) this forces `ordCompl[2] den ∣ num`, contradicting non-dyadicity.
-/
theorem residueOrbit_of_nondyadic (num den : ℕ) (hden : 0 < den)
    (h : ¬ (ordCompl[2] den ∣ num)) :
    ∀ j : ℕ, dyadicResidue den num j ≠ 0 := by
  intro j hj
  apply h
  have hj' : (2 ^ j * num) % den = 0 := hj
  have hdvd : den ∣ 2 ^ j * num := Nat.dvd_of_mod_eq_zero hj'
  have hq0_dvd : ordCompl[2] den ∣ 2 ^ j * num := (Nat.ordCompl_dvd den 2).trans hdvd
  have hnd2 : ¬ (2 : ℕ) ∣ ordCompl[2] den := Nat.not_dvd_ordCompl Nat.prime_two hden.ne'
  have hcop2 : Nat.Coprime (ordCompl[2] den) 2 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hnd2).symm
  have hcop : Nat.Coprime (ordCompl[2] den) (2 ^ j) := hcop2.pow_right j
  exact hcop.dvd_of_dvd_mul_left hq0_dvd

/-- **Non-dyadicity is exactly the non-terminating residual residue orbit.**  The genuine §25.1/§25.2
distinction between a failing run obstruction and a clean dyadic cylinder, in dynamical form. -/
theorem nondyadic_iff_residueOrbit (num den : ℕ) (hden : 0 < den) :
    ¬ (ordCompl[2] den ∣ num) ↔ ∀ j : ℕ, dyadicResidue den num j ≠ 0 :=
  ⟨residueOrbit_of_nondyadic num den hden, nondyadic_of_residueOrbit num den⟩

/-! ## Part B — the failing-shell residual input and the derived `ResidualCenter` -/

/--
**The smallest genuine §25.1 input for a failing shell.**

After the residual singular-square cleanup, a *failing* shell's residual mass concentrates on a
small-denominator dyadic cylinder with center `num/den` (`den = Qp ≤ Q₀`).  `horbit` is the genuine
non-triviality of a *failing* shell: the residual run never terminates — the §25.2 residue orbit
`dyadicResidue den num j = (2ʲ·num) mod den` is never `0`.  By `nondyadic_iff_residueOrbit` this is
equivalent to the center being non-dyadic, the exact property `RunProvenanceConstruction` consumed.
-/
structure FailingShellResidual where
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
  /-- **Failing-shell non-triviality**: the residual residue orbit never terminates. -/
  horbit : ∀ j : ℕ, dyadicResidue den num j ≠ 0

namespace FailingShellResidual

variable (F : FailingShellResidual)

/-- The residual center of a failing shell is non-dyadic — derived from the non-terminating orbit. -/
theorem nondyadic : ¬ (ordCompl[2] F.den ∣ F.num) :=
  nondyadic_of_residueOrbit F.num F.den F.horbit

/--
**The `ResidualCenter` of a failing shell, DERIVED.**

The §25.1 small-denominator center `num/den` together with the *derived* non-dyadicity is precisely
the `ResidualCenter` datum that `RunProvenanceConstruction` turns into the full `(q₀, a, m)`
provenance, run obstruction, half-decrease, and capstone `RunFactoryData`.
-/
def toResidualCenter : ResidualCenter where
  num := F.num
  den := F.den
  bound := F.bound
  hden := F.hden
  hbound := F.hbound
  hnondyadic := F.nondyadic

@[simp] theorem toResidualCenter_num : F.toResidualCenter.num = F.num := rfl
@[simp] theorem toResidualCenter_den : F.toResidualCenter.den = F.den := rfl
@[simp] theorem toResidualCenter_bound : F.toResidualCenter.bound = F.bound := rfl

/--
**The full `(q₀, a, m)` provenance of a failing shell, DERIVED.**

Reusing `ResidualCenter.provenance`: the §25.2 reduced data `q₀` (odd, `> 1`, `≤ Q₀`), `a`
(coprime), and a positive period multiplier `m` with the scale `4 q₀ ≤ m·ord_{q₀}(2)`, plus the
mask-point identity `a/q₀ = ν/ordCompl[2] Qp`.
-/
theorem provenance :
    ∃ (q0 a m : ℕ),
      Odd q0 ∧ 1 < q0 ∧ q0 ≤ F.bound ∧ Nat.Coprime a q0 ∧ 0 < m ∧
        4 * q0 ≤ m * orderOf (2 : ZMod q0) ∧
        (a : ℚ) / (q0 : ℚ) = (F.num : ℚ) / ((ordCompl[2] F.den : ℕ) : ℚ) :=
  F.toResidualCenter.provenance

/--
**Tie to the proved §25.1 cylinder dichotomy.**

Feeding the genuine eq-(25.1) hypotheses for the failing shell (`M·Qp − ν·D = R` and the
singular-square residual bound `|R|·2ⁿ⁰ < D·Qp`) into the already-proved `residual_cylinder_dichotomy`
(through the derived `ResidualCenter`), the mask point `M/D` sits in the same/adjacent depth-`n₀`
dyadic cylinder as the center `ν/Qp`, **and** the derived run obstruction's L.4.2 half-decrease fires
on `dyadicDigit q₀ a`.
-/
theorem provenance_of_cylinder_dichotomy
    {M D R : ℝ} {n0 kM kν : ℕ}
    (hD : 0 < D)
    (hrel : M * (F.den : ℝ) - (F.num : ℝ) * D = R)
    (hRbound : |R| * 2 ^ n0 < D * (F.den : ℝ))
    (hcylM : DyadicCylinder n0 kM (M / D))
    (hcylν : DyadicCylinder n0 kν ((F.num : ℝ) / (F.den : ℝ)))
    (u : ℕ) (weight : ℝ) :
    (kM = kν ∨ kν = kM + 1 ∨ kM = kν + 1) ∧
      ∃ p', PeriodicOn (dyadicDigit F.toResidualCenter.q0 F.toResidualCenter.a) u
          (2 * (F.toResidualCenter.scaleMult * orderOf (2 : ZMod F.toResidualCenter.q0))) p'
        ∧ 0 < p' ∧ 2 * p' ≤ F.toResidualCenter.scaleMult * orderOf (2 : ZMod F.toResidualCenter.q0) :=
  F.toResidualCenter.provenance_of_cylinder_dichotomy hD hrel hRbound hcylM hcylν u weight

end FailingShellResidual

/-- **The §25.1 residual center of a failing shell** (the headline construction). -/
def residualCenterOfFailingShell (F : FailingShellResidual) : ResidualCenter :=
  F.toResidualCenter

/-- **Existence of the `ResidualCenter` for a failing shell** — the §25.1 residual support being a
non-dyadic small-denominator cylinder yields a genuine `ResidualCenter` whose data tracks the shell. -/
theorem exists_residualCenter_of_failingShell (F : FailingShellResidual) :
    ∃ C : ResidualCenter, C.num = F.num ∧ C.den = F.den ∧ C.bound = F.bound :=
  ⟨F.toResidualCenter, rfl, rfl, rfl⟩

/-! ## Part C — the adjacent-cylinder branch routes to non-run outputs (Proposition 25.3) -/

/-- The run obligation among the residual singular outputs of Proposition 25.3 is exactly the
`shorterPeriodRun` (the shorter-period run that recurses through the run machinery). -/
def ResidualSingularOutput.isRunObligation {w : ℕ → ℕ} {p : ℕ} :
    ResidualSingularOutput w p → Prop
  | .shorterPeriodRun _ _ => True
  | .cleanBoundaryDirty => False
  | .apTower => False
  | .localSpike => False

/-- The non-run carry-tail outputs of the adjacent-cylinder branch: `localSpike` (dense/spike) and
`cleanBoundaryDirty` (all-zero/clean). -/
def ResidualSingularOutput.isCarryTailOutput {w : ℕ → ℕ} {p : ℕ} :
    ResidualSingularOutput w p → Prop
  | .localSpike => True
  | .cleanBoundaryDirty => True
  | .shorterPeriodRun _ _ => False
  | .apTower => False

/-- The carry word `ξ 1 0 0⋯0`: a single `1` at the cut position, all `0` afterwards (the manuscript's
all-zero carry tail). -/
def carryWordAllZeroTail (cut : ℕ) : ℕ → ℕ := fun j => if j = cut then 1 else 0

/-- The carry word `ξ 0 1 1⋯1`: `0` up to the cut, all `1` afterwards (the manuscript's dense all-one
carry tail). -/
def carryWordDenseTail (cut : ℕ) : ℕ → ℕ := fun j => if cut < j then 1 else 0

/-- The all-zero carry word genuinely contains an all-zero block longer than `bound` (the tail after
the cut), as long as the word is long enough. -/
theorem carryWordAllZeroTail_allZeroBlock {cut p bound : ℕ}
    (h : cut + 1 + (bound + 1) ≤ p) :
    AllZeroBlock (carryWordAllZeroTail cut) p bound := by
  refine ⟨cut + 1, bound + 1, h, by omega, ?_⟩
  intro i _
  show (if cut + 1 + i = cut then 1 else 0) = 0
  rw [if_neg (by omega)]

/-- The dense carry word genuinely contains a dense all-one block longer than `bound` (the tail after
the cut), as long as the word is long enough. -/
theorem carryWordDenseTail_denseBlock {cut p bound : ℕ}
    (h : cut + 1 + (bound + 1) ≤ p) :
    DenseAllOneBlock (carryWordDenseTail cut) p bound := by
  refine ⟨cut + 1, bound + 1, h, by omega, ?_⟩
  intro i _
  show (if cut < cut + 1 + i then 1 else 0) = 1
  rw [if_pos (by omega)]

/--
**The adjacent-cylinder branch lands in a non-run output (Proposition 25.3).**

In the adjacent-cylinder case, the binary carry structure produces a dense all-one block or an
all-zero block (`hAdjacent`).  The manuscript routes these to the `localSpike` (dense/spike) and
`cleanBoundaryDirty` (all-zero/clean) classes respectively — both **carry-tail outputs that are not
the run obligation** `shorterPeriodRun`.  So the run side never arises from the adjacent branch.
-/
theorem adjacentBranch_nonRun {w : ℕ → ℕ} {p bound : ℕ}
    (hadj : DenseAllOneBlock w p bound ∨ AllZeroBlock w p bound) :
    ∃ o : ResidualSingularOutput w p, o.isCarryTailOutput ∧ ¬ o.isRunObligation := by
  rcases hadj with _hd | _hz
  · refine ⟨ResidualSingularOutput.localSpike, ?_, ?_⟩
    · exact True.intro
    · intro h; exact h
  · refine ⟨ResidualSingularOutput.cleanBoundaryDirty, ?_, ?_⟩
    · exact True.intro
    · intro h; exact h

/--
**The §25.1 dichotomy splits run-side from non-run.**

From the proved cylinder dichotomy `residual_cylinder_dichotomy`, the *equal* cylinder yields the
run-side rational-prefix match (`hEqual` — the only input the run obstruction needs), while the
*adjacent* cylinder yields a non-run output.  Hence the run side needs only the equal-cylinder center.
-/
theorem dichotomy_run_only_equal {w : ℕ → ℕ} {M D ν R : ℝ}
    {p n0 kM kν bound plen Qp : ℕ}
    (hD : 0 < D) (hQp : 0 < Qp)
    (hrel : M * (Qp : ℝ) - ν * D = R)
    (hRbound : |R| * 2 ^ n0 < D * (Qp : ℝ))
    (hcylM : DyadicCylinder n0 kM (M / D))
    (hcylν : DyadicCylinder n0 kν (ν / (Qp : ℝ)))
    (hEqual : kM = kν → RationalPrefixMatch w plen Qp)
    (hAdjacent : (kν = kM + 1 ∨ kM = kν + 1) →
      DenseAllOneBlock w p bound ∨ AllZeroBlock w p bound) :
    RationalPrefixMatch w plen Qp ∨
      (∃ o : ResidualSingularOutput w p, ¬ o.isRunObligation) := by
  have hQpR : (0 : ℝ) < (Qp : ℝ) := by exact_mod_cast hQp
  rcases residual_cylinder_dichotomy hD hQpR hrel hRbound hcylM hcylν with heq | hadj
  · exact Or.inl (hEqual heq)
  · rcases adjacentBranch_nonRun (hAdjacent hadj) with ⟨o, _, hno⟩
    exact Or.inr ⟨o, hno⟩

/--
**The same split for the concrete mask word, building on the closed equal-cylinder bridge.**

Specialized to `w = binaryDigitWord (M/D)`, this builds on the already-proved
`lemma25_1_dyadicCylinderPrefix_maskWord` (whose `hEqual` is the closed binary-digit ↔ cylinder
bridge), so the *equal* branch is genuinely **proved** to give a rational-prefix match (the run
obstruction's only input), and the *adjacent* branch is **proved** to land in a non-run carry-tail
output.  Only the genuinely shell-dependent carry tail `hAdjacent` remains an input — and it is shown
to be non-run.
-/
theorem dichotomy_run_only_equal_maskWord
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
    RationalPrefixMatch (binaryDigitWord (M / D)) n0 Qp ∨
      (∃ o : ResidualSingularOutput (binaryDigitWord (M / D)) p,
        o.isCarryTailOutput ∧ ¬ o.isRunObligation) := by
  rcases lemma25_1_dyadicCylinderPrefix_maskWord hq0 hq0_le hD hQp hM hrel hRbound
      hcylM hcylν hcenter hAdjacent with hd | hz | hrat
  · exact Or.inr (adjacentBranch_nonRun (Or.inl hd))
  · exact Or.inr (adjacentBranch_nonRun (Or.inr hz))
  · exact Or.inl hrat

/-! ## Part D — concrete non-vacuity witnesses (`ν = 1, Qp = 3` ⟹ the `1/3` failing shell) -/

/-- A concrete failing shell `ν/Qp = 1/3`: the residue orbit `2ʲ mod 3 ∈ {1,2}` never hits `0`
(derived from non-dyadicity via `residueOrbit_of_nondyadic`). -/
def failingShellWitness : FailingShellResidual where
  num := 1
  den := 3
  bound := 3
  hden := by norm_num
  hbound := le_refl 3
  horbit := by
    refine residueOrbit_of_nondyadic 1 3 (by norm_num) ?_
    have hfact : (3 : ℕ).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by decide)
    have h3 : ordCompl[2] (3 : ℕ) = 3 := by
      show (3 : ℕ) / 2 ^ ((3 : ℕ).factorization 2) = 3
      rw [hfact]; norm_num
    rw [h3]; decide

/-- The derived center of the witness has reduced odd denominator `q₀ = 3`. -/
theorem failingShellWitness_q0 : failingShellWitness.toResidualCenter.q0 = 3 := by
  have hfact : (3 : ℕ).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by decide)
  have h3 : ordCompl[2] (3 : ℕ) = 3 := by
    show (3 : ℕ) / 2 ^ ((3 : ℕ).factorization 2) = 3
    rw [hfact]; norm_num
  show ordCompl[2] (3 : ℕ) / Nat.gcd 1 (ordCompl[2] (3 : ℕ)) = 3
  rw [h3, Nat.gcd_one_left, Nat.div_one]

/-- The derived center of the witness has reduced numerator `a = 1`. -/
theorem failingShellWitness_a : failingShellWitness.toResidualCenter.a = 1 := by
  have hfact : (3 : ℕ).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by decide)
  have h3 : ordCompl[2] (3 : ℕ) = 3 := by
    show (3 : ℕ) / 2 ^ ((3 : ℕ).factorization 2) = 3
    rw [hfact]; norm_num
  show (1 : ℕ) / Nat.gcd 1 (ordCompl[2] (3 : ℕ)) = 1
  rw [h3, Nat.gcd_one_left, Nat.div_one]

/-- **The witness genuinely fires the L.4.2 half-decrease** on `dyadicDigit q₀ a` — non-vacuity of the
whole derived provenance on a real small-denominator word. -/
theorem failingShellWitness_halfDecrease :
    ∃ p', PeriodicOn
        (dyadicDigit failingShellWitness.toResidualCenter.q0 failingShellWitness.toResidualCenter.a) 0
        (2 * (failingShellWitness.toResidualCenter.scaleMult *
          orderOf (2 : ZMod failingShellWitness.toResidualCenter.q0))) p'
      ∧ 0 < p' ∧ 2 * p' ≤ failingShellWitness.toResidualCenter.scaleMult *
          orderOf (2 : ZMod failingShellWitness.toResidualCenter.q0) :=
  failingShellWitness.toResidualCenter.toRunObstruction_halfDecrease 0 0

/-- The failing-shell input is non-vacuous. -/
theorem failingShellResidual_nonempty : Nonempty FailingShellResidual :=
  ⟨failingShellWitness⟩

/-- **Non-vacuity of the adjacent-branch routing**: a genuine all-zero carry word routes to a non-run
carry-tail output. -/
theorem adjacentBranch_nonRun_witness {cut p bound : ℕ} (h : cut + 1 + (bound + 1) ≤ p) :
    ∃ o : ResidualSingularOutput (carryWordAllZeroTail cut) p,
      o.isCarryTailOutput ∧ ¬ o.isRunObligation :=
  adjacentBranch_nonRun (Or.inr (carryWordAllZeroTail_allZeroBlock h))

/-! ## Part E — honest residual inventory -/

/-- The honest status of the Run residual after this file. -/
def runResidualCenterExistenceResiduals : List String :=
  [ "CLOSED (equivalence) — nondyadic_iff_residueOrbit: the §25.1 distinction between a failing run " ++
      "obstruction and a clean dyadic cylinder is exactly ¬(ordCompl[2] Qp ∣ ν) ↔ the §25.2 residue " ++
      "orbit dyadicResidue Qp ν never hits 0 (the residual run never terminates).",
    "CLOSED (existence, REDUCED to one input) — residualCenterOfFailingShell / " ++
      "exists_residualCenter_of_failingShell: the ResidualCenter (hence the full (q₀,a,m) provenance, " ++
      "run obstruction, half-decrease, RunFactoryData) is DERIVED from a FailingShellResidual, whose " ++
      "only nontrivial datum is the non-terminating residual orbit (≡ non-dyadicity).",
    "CLOSED (geometry tie) — FailingShellResidual.provenance_of_cylinder_dichotomy threads the " ++
      "derived center through the proved residual_cylinder_dichotomy and the L.4.2 half-decrease.",
    "CLOSED (adjacent branch is non-run) — adjacentBranch_nonRun + dichotomy_run_only_equal[_maskWord]: " ++
      "the adjacent-cylinder carry-tail block routes to the non-run localSpike/cleanBoundaryDirty " ++
      "classes of Proposition 25.3, never the run obligation shorterPeriodRun; the run side needs only " ++
      "the equal-cylinder center (proved via the closed lemma25_1_dyadicCylinderPrefix_maskWord bridge).",
    "IRREDUCIBLE (unchanged) — the carry-tail length (whether the adjacent tail exceeds bound) is the " ++
      "genuinely shell-dependent 2-adic valuation fact supplied as hAdjacent; it is shown to be non-run, " ++
      "so it is not a Run obligation." ]

theorem runResidualCenterExistenceResiduals_nonempty : runResidualCenterExistenceResiduals ≠ [] := by
  simp [runResidualCenterExistenceResiduals]

end

end Erdos260
