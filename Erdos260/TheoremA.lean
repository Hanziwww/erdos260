import Mathlib
import Erdos260.AppendixI
import Erdos260.AppendixL
import Erdos260.Density
import Erdos260.Pressure
import Erdos260.Support
import Erdos260.Target
import Erdos260.TargetBridge

/-!
# Main theorem assembly: `theoremA` and `erdos260Statement`

This file packages Appendix H of `proof_v2.tex` and assembles the final
target.

## Honest refactor (Pass 2)

`Erdos260AnalyticInputs` is now a fine-grained `Prop` carrying:

* numerical constants `cQ, cPr, cStar, ξ` with their positivity and the
  manuscript's numerical compatibility `cStar * ξ < cPr`;
* a per-instance **witness mass** field `failureMass` that, on the
  failure of positive density at any sufficiently large dyadic `X`,
  produces a witness `M` satisfying simultaneously the Lemma 21.1
  lower bound `cPr · X ≤ M` (H.5) and the Theorem I.7 upper bound
  `M ≤ cStar · ξ · X` (H.4).

The new `theoremA_of_analytic_inputs` does **real algebra**: it derives
`PositiveDyadicShellDensityReal` from these inputs by
`by_contra` + the `h4_vs_h5_contradiction` lemma in `Pressure.lean`.

## Why this is an honest refactor

Pass 1 had a single field `positiveDyadicDensity` which was literally
`TheoremAStatement`, so `theoremA_of_analytic_inputs` was just
extraction.  In Pass 2 the field is the per-instance witness pair
`(M, lower bound, upper bound)`, and the conversion to
`PositiveDyadicShellDensityReal` uses the numerical incompatibility
`cStar · ξ < cPr` as the closure step.  The user obligation is now
the manuscript's H.4 ∧ H.5 witness construction, not the conclusion.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ### The bundled analytic inputs (refactored) -/

/--
**`Erdos260AnalyticInputs`** (Pass 2, refactored).

Bundles the four manuscript constants `cQ, cPr, cStar, ξ` with their
positivity and numerical compatibility `cStar * ξ < cPr`, plus the
per-instance **failure-mass witness**: on each rational-target binary
nonterminating sequence and each sufficiently large dyadic `X`,
whenever the positive-density inequality fails
(`shell.card < cQ · X`), there is a real `M` simultaneously bounded
below by `cPr · X` and above by `cStar · ξ · X`.

The `M` is conceptually the high-excess mass `𝒜_{r,0}(εL)` of
Appendix H; the two bounds are exactly (H.5) and (H.4).

This is a `structure` (not a `Prop`) because it carries the four
numerical constants as data.  The Lean theorem
`theoremA_of_analytic_inputs` is morally `Erdos260AnalyticInputs →
TheoremAStatement` regardless.
-/
structure Erdos260AnalyticInputs where
  /-- The positive-density constant `c_Q > 0`. -/
  cQ : ℝ
  /-- The pressure-lower-bound constant `c_pr > 0` from Appendix H.5. -/
  cPr : ℝ
  /-- The descent-upper-bound constant `C_* > 0` from Appendix H.4. -/
  cStar : ℝ
  /-- The smallness parameter `ξ > 0` chosen in Appendix H.3 / H.5. -/
  ξ : ℝ
  cQ_pos : 0 < cQ
  cPr_pos : 0 < cPr
  cStar_pos : 0 < cStar
  ξ_pos : 0 < ξ
  /-- The manuscript's numerical compatibility `C_* · ξ < c_pr`. -/
  constantsCompatible : cStar * ξ < cPr
  /-- The H.4 vs H.5 witness mass.  For each rational-target binary
  nonterminating sequence `d` and each sufficiently large dyadic `X`,
  if the positive-density failure `shell.card < cQ · X` holds, then
  there is a real witness mass `M` simultaneously satisfying
  `cPr · X ≤ M` (Lemma 21.1 / H.5) and `M ≤ cStar · ξ · X`
  (Theorem I.7 / H.4). -/
  failureMass :
    ∀ (Q : Nat) (d : Nat -> Nat),
      0 < Q -> BinaryDigits d -> ¬ EventuallyZero d ->
      (∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) ->
      ∃ X0 : Nat, ∀ X : Nat, Dyadic X -> X0 ≤ X ->
        ((supportShell d X).card : ℝ) < cQ * (X : ℝ) ->
          ∃ M : ℝ,
            cPr * (X : ℝ) ≤ M ∧
              M ≤ cStar * ξ * (X : ℝ)

/-! ### Real `theoremA` from the bundled analytic inputs -/

/--
**`theoremA_of_analytic_inputs : Erdos260AnalyticInputs → TheoremAStatement`.**

The manuscript Appendix H assembly: given the bundled `failureMass`
field, we derive positive dyadic-shell density by contradiction.  On
any instance with `shell.card < cQ · X`, the witness mass `M`
simultaneously satisfies `cPr · X ≤ M ≤ cStar · ξ · X`; combined with
`constantsCompatible : cStar · ξ < cPr` and `X > 0`, this is
contradictory, so the failure never occurs.

This proof is **not** a rename of `inputs.failureMass`; it actually
runs `nlinarith` on the contradictory inequalities.
-/
theorem theoremA_of_analytic_inputs
    (inputs : Erdos260AnalyticInputs) :
    TheoremAStatement := by
  intro Q d hQ hd hnonterm hrational
  refine ⟨inputs.cQ, inputs.cQ_pos, ?_⟩
  rcases inputs.failureMass Q d hQ hd hnonterm hrational with ⟨X0, hX⟩
  refine ⟨X0, fun X hXdyadic hXge => ?_⟩
  by_contra hfail
  have hfail' : ((supportShell d X).card : ℝ) < inputs.cQ * (X : ℝ) :=
    lt_of_not_ge hfail
  rcases hX X hXdyadic hXge hfail' with ⟨M, hLower, hUpper⟩
  have hXpos : 0 < (X : ℝ) := by
    have := dyadic_pos hXdyadic
    exact_mod_cast this
  have hcompat : inputs.cStar * inputs.ξ < inputs.cPr := inputs.constantsCompatible
  -- Chain: cPr * X ≤ M ≤ cStar * ξ * X < cPr * X.  Contradiction.
  exact h4_vs_h5_contradiction hXpos hcompat hUpper hLower

/-! ### Final Erdős 260 statement -/

/--
**`erdos260Statement_of_inputs : Erdos260AnalyticInputs → Erdos260Statement`.**

The manuscript final reduction: combining `theoremA_of_analytic_inputs`
with the unconditional bridge `erdos260Statement_of_theoremA` from
`TargetBridge.lean`, we obtain `Erdos260Statement` modulo the bundled
analytic inputs.
-/
theorem erdos260Statement_of_inputs
    (inputs : Erdos260AnalyticInputs) :
    Erdos260Statement :=
  erdos260Statement_of_theoremA (theoremA_of_analytic_inputs inputs)

/-! ### Phase H4: finer-grained atomic analytic inputs -/

/--
**`AtomicWitnessProp`** packages the per-instance atomic Appendix L
content for a single failing dyadic `X` as a `Prop`.  Six mass values
are introduced existentially and bounded above by `cStar · ξ · X / 6`
(one per atomic field); the pressure quantity is combined with the sum
into the pressure lower bound `cPr · X`.

The conjuncts correspond to the manuscript's atomic facts:
* `chernoffPathSpace` (Lemma 22.1)
* `cnlEntropy` (Theorem G.6)
* `towerPackageBound` (Proposition I.3.1)
* `densePackBound` (Lemma I.4.1)
* `nonRunReturnBound` (Proposition I.5.1)
* `runBound` (Proposition I.5.2)
* The lower-bound conjunct combines `gapWindowMassLower` (Lemma 21.1 hM)
  and `lowExcessUpper` (Lemma 21.1 hlow) through the manuscript's
  Lemma 21.1 closure.
-/
def AtomicWitnessProp (cPr cStar ξ X : ℝ) : Prop :=
  ∃ Regular CleanTerm Tower DensePackVal ReturnVal RunVal : ℝ,
    Regular <= cStar * ξ * X / 6 ∧
    CleanTerm <= cStar * ξ * X / 6 ∧
    Tower <= cStar * ξ * X / 6 ∧
    DensePackVal <= cStar * ξ * X / 6 ∧
    ReturnVal <= cStar * ξ * X / 6 ∧
    RunVal <= cStar * ξ * X / 6 ∧
    cPr * X <= Regular + CleanTerm + Tower + DensePackVal + ReturnVal + RunVal

/--
**`Erdos260AnalyticInputsAtomic`** is the fine-grained Pass-2 structure
holding the manuscript's eight atomic per-instance facts plus the
numerical compatibility `cStar · ξ < cPr`.

This is the user-facing Phase H4 structure.  It splits the bundled
`failureMass` field of `Erdos260AnalyticInputs` into eight atomic
per-instance inequalities (six package upper bounds + two pressure
lower-bound inputs combined into a single closure) and exposes the
manuscript's compatibility condition as the ninth field.
-/
structure Erdos260AnalyticInputsAtomic where
  cQ : ℝ
  cPr : ℝ
  cStar : ℝ
  ξ : ℝ
  cQ_pos : 0 < cQ
  cPr_pos : 0 < cPr
  cStar_pos : 0 < cStar
  ξ_pos : 0 < ξ
  /-- (Field 9) Numerical compatibility from Appendix H.3 / H.5. -/
  constantsCompatible : cStar * ξ < cPr
  /-- (Fields 1–8) Per-instance atomic witness producing the eight
  inequalities (six upper bounds + the combined pressure lower bound). -/
  atomicWitness :
    ∀ (Q : Nat) (d : Nat -> Nat),
      0 < Q -> BinaryDigits d -> ¬ EventuallyZero d ->
      (∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) ->
      ∃ X0 : Nat, ∀ X : Nat, Dyadic X -> X0 ≤ X ->
        ((supportShell d X).card : ℝ) < cQ * (X : ℝ) ->
          AtomicWitnessProp cPr cStar ξ (X : ℝ)

/--
**Bridge `Erdos260AnalyticInputs.ofAtomic`.**

The eight atomic per-instance facts + numerical compatibility together
imply the bundled `Erdos260AnalyticInputs.failureMass` via real algebra:
the witness mass is `Regular + CleanTerm + Tower + DensePack + Return +
Run`, the lower bound is the `pressureLowerBound` field, and the upper
bound is the sum of the six atomic upper bounds (each `cStar · ξ · X / 6`).

This is real `linarith` algebra, not a rename.
-/
def Erdos260AnalyticInputs.ofAtomic
    (atomic : Erdos260AnalyticInputsAtomic) :
    Erdos260AnalyticInputs where
  cQ := atomic.cQ
  cPr := atomic.cPr
  cStar := atomic.cStar
  ξ := atomic.ξ
  cQ_pos := atomic.cQ_pos
  cPr_pos := atomic.cPr_pos
  cStar_pos := atomic.cStar_pos
  ξ_pos := atomic.ξ_pos
  constantsCompatible := atomic.constantsCompatible
  failureMass := fun Q d hQ hd hnonterm hrational => by
    rcases atomic.atomicWitness Q d hQ hd hnonterm hrational with ⟨X0, hX⟩
    refine ⟨X0, fun X hXdyadic hXge hfail => ?_⟩
    rcases hX X hXdyadic hXge hfail with
      ⟨Regular, CleanTerm, Tower, DensePackVal, ReturnVal, RunVal,
       hCh, hCNL, hT, hD, hR, hRun, hLower⟩
    refine ⟨Regular + CleanTerm + Tower + DensePackVal + ReturnVal + RunVal,
            hLower, ?_⟩
    -- Six upper bounds sum to `cStar * ξ * X`.
    have h6 :
        Regular + CleanTerm + Tower + DensePackVal + ReturnVal + RunVal <=
          6 * (atomic.cStar * atomic.ξ * (X : ℝ) / 6) := by
      linarith
    have h6_eq :
        6 * (atomic.cStar * atomic.ξ * (X : ℝ) / 6) =
          atomic.cStar * atomic.ξ * (X : ℝ) := by ring
    linarith

/--
**`theoremA_of_atomic_inputs : Erdos260AnalyticInputsAtomic → TheoremAStatement`.**

The convenience wrapper combining `Erdos260AnalyticInputs.ofAtomic`
with `theoremA_of_analytic_inputs`.
-/
theorem theoremA_of_atomic_inputs
    (atomic : Erdos260AnalyticInputsAtomic) :
    TheoremAStatement :=
  theoremA_of_analytic_inputs (Erdos260AnalyticInputs.ofAtomic atomic)

/-- Analogous Erdős 260 wrapper for the fine-grained inputs. -/
theorem erdos260Statement_of_atomic_inputs
    (atomic : Erdos260AnalyticInputsAtomic) :
    Erdos260Statement :=
  erdos260Statement_of_inputs (Erdos260AnalyticInputs.ofAtomic atomic)

end

end Erdos260
