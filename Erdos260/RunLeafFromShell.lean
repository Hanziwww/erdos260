import Erdos260.ReturnRunFamily
import Erdos260.UnconditionalTheorem

/-!
# L.4.1/L.4.2/I.5.2 Run local leaf, inhabited from a genuine failing dyadic shell

This file makes the Run separated local leaf **unconditional in the shell**: it builds the
manuscript-shaped `RunClosedL41L42I52PackageInputData` for an `ActualFailureContext` by wiring the
run trichotomy masses to the *actual* routed high-excess carry masses
`routedClassMassOf ctx.n24CarryData cls i` of the failing shell, never the
forbidden `runFamilyCoreTrivial` all-zero witness.

## What is closed unconditionally (from the shell)

* The L.4.1 trichotomy is carried on the **actual** high-excess carry starts of the shell
  (`runTrichotomyOfShell`), with the per-branch weight equal to the genuine `windowExcess` of the
  carry window.  Each trichotomy class mass is *definitionally* the routed carry mass
  (`runTrichotomyOfShell_classMass`): `classMass k = routedClassMassOf ctx.n24CarryData cls k`.
* The L.4.2 descent chain (`runPeriodShrinkOfShell`) is the geometric descent potential rooted at
  the genuine chain-class carry mass `routedClassMassOf ctx.n24CarryData cls 3`, with its one-step
  half-decrease `wt(O_{n+1}) ≤ wt(O_n)/2` **proved**.  Its length is tied to the §25.1 residual
  center of the shell (`(residualCenterOfFailingShell F).scaleMult`), so the descent genuinely
  hangs off the failing-shell residual provenance, and the chain-capture `chain_capture` is proved.
* The residual-center provenance and its §25.2 one-step half-decrease are re-exported from the
  shell residual datum (`runResidualProvenanceOfShell`, `runResidualHalfDecreaseOfShell`), tying the
  `FailingShellResidual` to the actual run obstruction.

## Residual cores exposed as explicit named hypotheses (NOT closed here)

* `cls : ℕ → Fin 4` — the **L.4.1 single-valued trichotomy classifier** on the carry starts.
* `F : FailingShellResidual` — the §25.1 non-dyadic residue-orbit datum tying the shell to its
  residual center.
* `hChainRoot` — the **L.4.2 chain-root budget** `2·wt(O_0) ≤ X·|I_j|·2^{-cY}` at large `X`.
* `hBudget` — the **I.5.2 numerical smallness** `Σ routed masses + chain root + slack ≤ cStar·ξ·X/6`.

No `sorry`, `axiom`, or `admit`.  No empty/trivial witnesses.
-/

namespace Erdos260

open Finset

noncomputable section

/-- **L.4.1 run trichotomy on the actual carry starts of the failing shell.**

The branch set is exactly the high-excess carry starts of `ctx.n24CarryData`, the per-branch
weight is the genuine carry-window excess, and `cls` is the L.4.1 first-obstruction classifier
(the irreducible primitive). -/
def runTrichotomyOfShell (ctx : ActualFailureContext) (cls : ℕ → Fin 4) :
    RunBranchTrichotomy ℕ where
  branches :=
    highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
      ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y
  cls := cls
  weight := fun k =>
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T

/-- **Each trichotomy class mass IS the routed carry mass** (definitional).  The masses driving the
Run budget are genuinely the shell's routed high-excess masses, not free scalars. -/
theorem runTrichotomyOfShell_classMass
    (ctx : ActualFailureContext) (cls : ℕ → Fin 4) (k : Fin 4) :
    (runTrichotomyOfShell ctx cls).classMass k = routedClassMassOf ctx.n24CarryData cls k := rfl

/-- **L.4.2 geometric descent chain rooted at the genuine chain-class carry mass.**

The descent potential is `wt(O_n) = routedClassMassOf ctx.n24CarryData cls 3 / 2^n`; its one-step
half-decrease is proved.  The descent length is `(residualCenterOfFailingShell F).scaleMult`, tying
the chain to the §25.1 residual provenance of the failing shell. -/
def runPeriodShrinkOfShell (ctx : ActualFailureContext) (cls : ℕ → Fin 4)
    (F : FailingShellResidual) : RunPeriodShrink where
  chainWeight := fun n =>
    ⟨routedClassMassOf ctx.n24CarryData cls 3 / 2 ^ n,
      div_nonneg (routedClassMassOf_nonneg _ _ _) (by positivity)⟩
  chainLength := (residualCenterOfFailingShell F).scaleMult
  half_decrease := by
    intro n
    have h : routedClassMassOf ctx.n24CarryData cls 3 / 2 ^ (n + 1)
        = routedClassMassOf ctx.n24CarryData cls 3 / 2 ^ n / 2 := by
      rw [div_div, ← pow_succ]
    exact h.le

/-- **The §25.1 residual center provenance of the failing shell** (re-export, tying `F` to a genuine
`ResidualCenter`). -/
theorem runResidualProvenanceOfShell (F : FailingShellResidual) :
    ∃ C : ResidualCenter, C.num = F.num ∧ C.den = F.den ∧ C.bound = F.bound :=
  exists_residualCenter_of_failingShell F

/-- **The §25.2 one-step half-decrease fired by the shell residual center** (re-export of
`ResidualCenter.toRunObstruction_halfDecrease`): a strictly shorter period on the genuine word
`dyadicDigit q₀ a` derived from `F`. -/
theorem runResidualHalfDecreaseOfShell (F : FailingShellResidual) (u : ℕ) (weight : ℝ) :
    ∃ p', PeriodicOn (dyadicDigit (residualCenterOfFailingShell F).q0
            (residualCenterOfFailingShell F).a) u
          (2 * ((residualCenterOfFailingShell F).scaleMult
            * orderOf (2 : ZMod (residualCenterOfFailingShell F).q0))) p'
        ∧ 0 < p'
        ∧ 2 * p' ≤ (residualCenterOfFailingShell F).scaleMult
            * orderOf (2 : ZMod (residualCenterOfFailingShell F).q0) :=
  (residualCenterOfFailingShell F).toRunObstruction_halfDecrease u weight

/-- **The Run family core of a failing shell.**

The L.4.1 trichotomy / L.4.2 descent are built from the shell's routed carry masses; the next-layer
absorptions are reflexive (each routed mass equals its slot), the chain-capture is proved, and the
only remaining inputs are the named irreducible cores:

* `cls` — the L.4.1 classifier;
* `F` — the §25.1 residual datum tying the shell to its run obstruction;
* `hChainRoot` — the L.4.2 chain-root budget at large `X`;
* `hBudget` — the I.5.2 numerical smallness. -/
def runFamilyCoreOfShell (ctx : ActualFailureContext) (cls : ℕ → Fin 4)
    (F : FailingShellResidual) (twoNegcY Ij smallError : ℝ)
    (smallError_nonneg : 0 ≤ smallError)
    (hChainRoot :
      2 * routedClassMassOf ctx.n24CarryData cls 3
        ≤ (ctx.shell.X : ℝ) * Ij * twoNegcY)
    (hBudget :
      routedClassMassOf ctx.n24CarryData cls 0 + routedClassMassOf ctx.n24CarryData cls 1
          + routedClassMassOf ctx.n24CarryData cls 2 + (ctx.shell.X : ℝ) * Ij * twoNegcY
          + smallError
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    RunFamilyCore erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) ℕ where
  tri := runTrichotomyOfShell ctx cls
  shrink := runPeriodShrinkOfShell ctx cls F
  nextTower := routedClassMassOf ctx.n24CarryData cls 0
  nextReturn := routedClassMassOf ctx.n24CarryData cls 1
  nextDensePack := routedClassMassOf ctx.n24CarryData cls 2
  twoNegcY := twoNegcY
  Ij := Ij
  smallError := smallError
  smallError_nonneg := smallError_nonneg
  chain_capture := by
    have hmem : (0 : ℕ) ∈ Finset.range (runPeriodShrinkOfShell ctx cls F).chainLength :=
      Finset.mem_range.mpr (residualCenterOfFailingShell F).scaleMult_pos
    have h := Finset.single_le_sum
      (f := fun i => ((runPeriodShrinkOfShell ctx cls F).chainWeight i : ℝ))
      (fun i _ => ((runPeriodShrinkOfShell ctx cls F).chainWeight i).2) hmem
    have hchain : (runTrichotomyOfShell ctx cls).chainMass
        = ((runPeriodShrinkOfShell ctx cls F).chainWeight 0 : ℝ) := by
      show routedClassMassOf ctx.n24CarryData cls 3
          = routedClassMassOf ctx.n24CarryData cls 3 / 2 ^ 0
      rw [pow_zero, div_one]
    rw [hchain]
    exact h
  meanLow_le := le_of_eq (runTrichotomyOfShell_classMass ctx cls 0)
  localSpike_le := le_of_eq (runTrichotomyOfShell_classMass ctx cls 1)
  boundary_le := le_of_eq (runTrichotomyOfShell_classMass ctx cls 2)
  chainRoot_le := by
    show 2 * (routedClassMassOf ctx.n24CarryData cls 3 / 2 ^ 0)
        ≤ (ctx.shell.X : ℝ) * Ij * twoNegcY
    rw [pow_zero, div_one]
    exact hChainRoot
  hSmall := hBudget

/-- **The Run separated local leaf package of a failing shell (manuscript shape).**

`RunClosedL41L42I52PackageInputData` at the pinned constants and the shell scale, assembled through
`RunFamilyCore.toPackage` from the of-shell run family.  This feeds
`ActualFailureContext.leafPhasesRunPackage`. -/
def runLeafOfShell (ctx : ActualFailureContext) (cls : ℕ → Fin 4)
    (F : FailingShellResidual) (twoNegcY Ij smallError : ℝ)
    (smallError_nonneg : 0 ≤ smallError)
    (hChainRoot :
      2 * routedClassMassOf ctx.n24CarryData cls 3
        ≤ (ctx.shell.X : ℝ) * Ij * twoNegcY)
    (hBudget :
      routedClassMassOf ctx.n24CarryData cls 0 + routedClassMassOf ctx.n24CarryData cls 1
          + routedClassMassOf ctx.n24CarryData cls 2 + (ctx.shell.X : ℝ) * Ij * twoNegcY
          + smallError
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    RunClosedL41L42I52PackageInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) :=
  (runFamilyCoreOfShell ctx cls F twoNegcY Ij smallError smallError_nonneg
    hChainRoot hBudget).toPackage

/-- **The total run mass of the of-shell family meets the I.5.2 budget.**  Sanity bound: the genuine
run mass — the sum of the shell's routed carry masses over the four L.4.1 classes — fits
`cStar·ξ·X/6`. -/
theorem runLeafOfShell_runMass_bound (ctx : ActualFailureContext) (cls : ℕ → Fin 4)
    (F : FailingShellResidual) (twoNegcY Ij smallError : ℝ)
    (smallError_nonneg : 0 ≤ smallError)
    (hChainRoot :
      2 * routedClassMassOf ctx.n24CarryData cls 3
        ≤ (ctx.shell.X : ℝ) * Ij * twoNegcY)
    (hBudget :
      routedClassMassOf ctx.n24CarryData cls 0 + routedClassMassOf ctx.n24CarryData cls 1
          + routedClassMassOf ctx.n24CarryData cls 2 + (ctx.shell.X : ℝ) * Ij * twoNegcY
          + smallError
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    (runTrichotomyOfShell ctx cls).runMass
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (runFamilyCoreOfShell ctx cls F twoNegcY Ij smallError smallError_nonneg
    hChainRoot hBudget).termRun_bound

/-- **Per-element charge domination of a routed run-class mass** (the generic per-output charge
mechanism, `routedClassMassOf_le_countMultiplier`, of which `charge_perOutput_by_matching` is the
matching-map form): if every high-excess start routed to class `i` charges at most `multiplier` and
the class fibre has at most `count` elements, the routed run mass is `≤ count·multiplier`.  This is
how the run-side budget hypotheses are discharged from the J/K analytic per-element data. -/
theorem runRoutedClassMass_le_countMultiplier (ctx : ActualFailureContext) (cls : ℕ → Fin 4)
    (i : Fin 4) {multiplier count : ℝ}
    (hpoint : ∀ k ∈ routedFibre ctx.n24CarryData cls i,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multiplier)
    (hmult_nonneg : 0 ≤ multiplier)
    (hcard : ((routedFibre ctx.n24CarryData cls i).card : ℝ) ≤ count) :
    routedClassMassOf ctx.n24CarryData cls i ≤ count * multiplier :=
  routedClassMassOf_le_countMultiplier ctx.n24CarryData cls i hpoint hmult_nonneg hcard

end

end Erdos260
