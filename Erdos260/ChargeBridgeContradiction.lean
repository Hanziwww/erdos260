import Mathlib
import Erdos260.ChargeBridgeReduction
import Erdos260.AppendixI_PackageBounds

/-!
# v5 charge-bridge top-level contradiction (reduced / charge-bridge level)

This file is the **v5 analog of `atomicWitnessProp_false`** (in `Audit.lean`),
proved at the reduced charge-bridge level and carrying the new **old-residual**
term of the v5 recurrence I.11'.  It is the *contradiction engine* of the v5
repair: a density-failing dyadic shell would simultaneously satisfy

* the **pressure floor** `cPr·X ≤ highExcessMass`
  (`pressureLowerBound_from_carry` / `CarryDataFromFailure.highExcessMass_lower`,
  scaled from `cPr·X·(r+1)`);
* the **augmented charge bridge** `highExcessMass ≤ ClosurePhaseMass + oldResMass`
  (`RoutedHighExcessChargeDataOldRes.highExcess_le_phaseMass_add_oldRes`, the v5
  seven-class routing with the new old-residual class);
* the **phase budget** `ClosurePhaseMass ≤ cStar·ξ·X` (the six per-phase
  manuscript budgets `term_X ≤ cStar·ξ·X/6`, summed by `ClosurePhaseMass_le_budget`);
* the **L.6.5 old-residual smallness** `oldResMass ≤ C_Q·c_*·X` (the
  density-sensitive support estimate `oldRes_le_of_density`, the smallness carried
  by the low-density endpoint count `≈ c_*·X`).

Under the **v5 constant condition** `cStar·ξ + C_Q·c_* < cPr` (the analog of the
OLD `cStar·ξ < cPr`, now absorbing the old-residual constant `C_Q·c_*`; satisfiable
because `c_*` is chosen *last*, after all other constants), these are jointly
impossible for `X > 0`:

`cPr·X ≤ highExcessMass ≤ ClosurePhaseMass + oldResMass
       ≤ cStar·ξ·X + C_Q·c_*·X = (cStar·ξ + C_Q·c_*)·X < cPr·X`.

## Results

* `highExcessMass_oldRes_contradiction` — the clean algebraic engine: the five
  bundled real inequalities above, plus `X > 0`, are contradictory.  This is the
  v5 analog of `atomicWitnessProp_false`, *with* the old-residual summand.
* `RoutedHighExcessChargeDataOldRes.refutes_failingShell` — the capstone package:
  a v5 seven-class routing `RoutedHighExcessChargeDataOldRes`, together with the
  L.6.5 bound `oldResMass ≤ C_Q·c_*·X`, the pressure-nonnegativity `0 ≤ cPr`, and
  the constant condition, refutes the failing shell.  The phase budget is
  discharged internally from the bundled phase data (`ClosurePhaseMass_le_budget`)
  and the pressure floor from `CarryDataFromFailure.highExcessMass_lower`.
* `RoutedHighExcessChargeDataOldRes.refutes_failingShell_of_density` — the same
  capstone with the L.6.5 bound itself supplied in its Lemma-L.6.5 form via
  `oldRes_le_of_density`: a per-index multiplier×support bound `(Cres·Y)·(Csupp·Ij)`
  (the constant `C_Q`) and the low-density endpoint count `|K| ≤ c_*·X` (eq. L.22).

No `sorry`/`axiom`; the refutation is pure linear arithmetic over the four faithful
inputs, mirroring the structure of `atomicWitnessProp_false`.
-/

namespace Erdos260

open Finset

noncomputable section

/--
**v5 contradiction engine — the charge bridge cannot close (reduced level).**

The v5 analog of `atomicWitnessProp_false`, now carrying the old-residual summand.
Bundling the pressure floor `cPr·X ≤ highExcessVal`, the augmented charge bridge
`highExcessVal ≤ phaseMassVal + oldResVal`, the phase budget
`phaseMassVal ≤ cStar·ξ·X`, and the L.6.5 old-residual smallness
`oldResVal ≤ C_Q·c_*·X`, under the v5 constant condition
`cStar·ξ + C_Q·c_* < cPr` (and `X > 0`) yields a contradiction:

`cPr·X ≤ highExcessVal ≤ phaseMassVal + oldResVal
       ≤ cStar·ξ·X + C_Q·c_*·X = (cStar·ξ + C_Q·c_*)·X < cPr·X`.

This is exactly the v5 refutation of the failing shell: the extra `+ C_Q·OldRes`
term of recurrence I.11' is absorbed below the pressure floor once `c_*` is chosen
last, so the bridge still cannot close. -/
theorem highExcessMass_oldRes_contradiction
    {cPr cStar ξ cQ cStarSmall X highExcessVal phaseMassVal oldResVal : ℝ}
    (hX : 0 < X)
    (hLower : cPr * X ≤ highExcessVal)
    (hPhase : phaseMassVal ≤ cStar * ξ * X)
    (hOldRes : oldResVal ≤ cQ * cStarSmall * X)
    (hBridge : highExcessVal ≤ phaseMassVal + oldResVal)
    (hcompat : cStar * ξ + cQ * cStarSmall < cPr) :
    False := by
  have hsum_le : highExcessVal ≤ (cStar * ξ + cQ * cStarSmall) * X := by
    have hdistrib :
        (cStar * ξ + cQ * cStarSmall) * X = cStar * ξ * X + cQ * cStarSmall * X := by
      ring
    rw [hdistrib]
    linarith
  have hle : cPr * X ≤ (cStar * ξ + cQ * cStarSmall) * X := le_trans hLower hsum_le
  have hlt : (cStar * ξ + cQ * cStarSmall) * X < cPr * X :=
    mul_lt_mul_of_pos_right hcompat hX
  linarith

/--
**Capstone — a v5 seven-class routing refutes the failing shell.**

Given the v5 seven-class routing `RoutedHighExcessChargeDataOldRes` (which supplies
the augmented bridge `highExcessMass ≤ ClosurePhaseMass + oldResMass`), the L.6.5
old-residual bound `oldResMass ≤ C_Q·c_*·X`, the pressure-nonnegativity `0 ≤ cPr`,
and the v5 constant condition `cStar·ξ + C_Q·c_* < cPr`, the failing dyadic shell is
refuted (`False`).

Internally:
* the pressure floor `cPr·X ≤ highExcessMass` is the carry lower bound
  `CarryDataFromFailure.highExcessMass_lower` (`cPr·X·(r+1) ≤ highExcessMass`),
  scaled down by `r + 1 ≥ 1` using `0 ≤ cPr`;
* the phase budget `ClosurePhaseMass ≤ cStar·ξ·X` is the summed manuscript
  per-phase budget `ClosurePhaseMass_le_budget` on the bundled phase data;
* the augmented bridge is `data.highExcess_le_phaseMass_add_oldRes`.

These four faithful inputs feed `highExcessMass_oldRes_contradiction`. -/
theorem RoutedHighExcessChargeDataOldRes.refutes_failingShell
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell cPr}
    {oldResMass cQ cStarSmall : ℝ}
    (data : RoutedHighExcessChargeDataOldRes phases carryData oldResMass)
    (hcPr_nonneg : 0 ≤ cPr)
    (holdRes : oldResMass ≤ cQ * cStarSmall * (shell.X : ℝ))
    (hcompat : cStar * ξ + cQ * cStarSmall < cPr) :
    False := by
  have hX : 0 < (shell.X : ℝ) := shell.X_pos_real
  -- Pressure floor `cPr·X ≤ highExcessMass`, scaled from the `cPr·X·(r+1)` bound.
  have hscale :
      cPr * (shell.X : ℝ) ≤ cPr * (shell.X : ℝ) * ((carryData.r : ℝ) + 1) := by
    have hbase_nonneg : 0 ≤ cPr * (shell.X : ℝ) := mul_nonneg hcPr_nonneg (le_of_lt hX)
    have hone_le : (1 : ℝ) ≤ (carryData.r : ℝ) + 1 := by
      have hr : (0 : ℝ) ≤ (carryData.r : ℝ) := Nat.cast_nonneg _
      linarith
    calc
      cPr * (shell.X : ℝ) = cPr * (shell.X : ℝ) * 1 := by ring
      _ ≤ cPr * (shell.X : ℝ) * ((carryData.r : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hone_le hbase_nonneg
  have hLower :
      cPr * (shell.X : ℝ) ≤
        highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T :=
    le_trans hscale carryData.highExcessMass_lower
  -- Phase budget `ClosurePhaseMass ≤ cStar·ξ·X` from the bundled per-phase budgets.
  have hPhase :
      ClosurePhaseMass phases.toClosurePhaseData ≤ cStar * ξ * (shell.X : ℝ) :=
    ClosurePhaseMass_le_budget phases.toClosurePhaseData (le_of_lt hX)
  -- Augmented v5 charge bridge from the seven-class routing.
  have hBridge := data.highExcess_le_phaseMass_add_oldRes
  exact highExcessMass_oldRes_contradiction hX hLower hPhase holdRes hBridge hcompat

/--
**Capstone with the L.6.5 old-residual bound in its density form.**

The same refutation as `RoutedHighExcessChargeDataOldRes.refutes_failingShell`, but
with the L.6.5 old-residual smallness supplied via `oldRes_le_of_density` (Lemma
L.6.5 core) rather than as a single inequality.  The inputs are exactly the
manuscript's:

* `holdResMass` — the branch-level identification `oldResMass = ∑_{k ∈ K} oldResAt k`
  (Lemma L.6.4);
* `hpoint` — the per-index multiplier×support bound `oldResAt k ≤ (Cres·Y)·(Csupp·Ij)`
  (eqs. L.20 + L.21): linear in the floor `Y`, never an absolute constant;
* `hcard` — the low-density terminal-endpoint count `|K| ≤ c_*·X` (eq. L.22, under
  the contradictory density hypothesis `A_S(2X)−A_S(X) < c_*X`).

The product constant is `C_Q := (Cres·Y)·(Csupp·Ij)`, so the v5 constant condition
reads `cStar·ξ + (Cres·Y)·(Csupp·Ij)·c_* < cPr`.  This is where the smallness lives
entirely in the endpoint count, evading the K.1.2 ↔ L.6.1 contradiction. -/
theorem RoutedHighExcessChargeDataOldRes.refutes_failingShell_of_density
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell cPr}
    {oldResMass : ℝ}
    (data : RoutedHighExcessChargeDataOldRes phases carryData oldResMass)
    {K : Finset ℕ} {oldResAt : ℕ → ℝ}
    {Cres Y Csupp Ij cStarSmall : ℝ}
    (hcPr_nonneg : 0 ≤ cPr)
    (holdResMass : oldResMass = ∑ k ∈ K, oldResAt k)
    (hpoint : ∀ k ∈ K, oldResAt k ≤ (Cres * Y) * (Csupp * Ij))
    (hbound_nonneg : 0 ≤ (Cres * Y) * (Csupp * Ij))
    (hcard : (K.card : ℝ) ≤ cStarSmall * (shell.X : ℝ))
    (hcompat : cStar * ξ + ((Cres * Y) * (Csupp * Ij)) * cStarSmall < cPr) :
    False := by
  -- Lemma L.6.5: `oldResMass ≤ (c_*·X)·((Cres·Y)·(Csupp·Ij)) = C_Q·c_*·X`.
  have hdens := oldRes_le_of_density hpoint hbound_nonneg hcard
  have holdRes :
      oldResMass ≤ ((Cres * Y) * (Csupp * Ij)) * cStarSmall * (shell.X : ℝ) := by
    rw [holdResMass]
    calc
      (∑ k ∈ K, oldResAt k)
          ≤ (cStarSmall * (shell.X : ℝ)) * ((Cres * Y) * (Csupp * Ij)) := hdens
      _ = ((Cres * Y) * (Csupp * Ij)) * cStarSmall * (shell.X : ℝ) := by ring
  exact data.refutes_failingShell hcPr_nonneg holdRes hcompat

end

end Erdos260
