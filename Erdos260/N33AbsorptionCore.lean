import Mathlib
import Erdos260.Erdos260ReducedToCoresV2

/-!
# N.3.3 absorption residuals: the L.6.2 paid-embedding core and the N.1.0/N.13/N.24 interfaces

This module attacks the residual fields of the strictly-smaller V2 residual surfaces
`Erdos260N2CoresV2` / `Erdos260N33CoresV2` (`Erdos260.Erdos260ReducedToCoresV2`).  It
closes the genuinely self-contained pieces of the **L.6.2 shell-paid bounded-class split**
and reduces the genuinely cross-phase comparisons to the *smallest named interface* that
builds green.

## The model-leaf shell-paid area is strictly positive (self-contained)

The Chernoff slot is the **fully unconditional** model leaf `chernoff22_1ALeafOfShell`
(four length-`2` gap words `{0,1}^2`, weight the integer-carry symbolic measure
`2^{-cost}`, multiplier `Y_sh = cost`).  Its shell-paid area
`∑_b wt₀(b)·Y_sh(b)` is the concrete sum `∑_{σ∈{0,1}²} (1/2)^{cost σ}·cost σ`, whose
`σ = (1,1)` term `(1/2)²·2 = 1/2` is already positive.  We prove

* `chernoffShellArea_pos` — `0 < chernoffShellArea ctx` (genuine, axiom-clean).

## The L.6.2 bounded-class split, with `paid_le` closed (self-contained)

Against the model leaf there is no *bounded* overlap constant `C_Q` (the toy area is a
fixed `O(1)` while the bounded class count scales with the shell), so `paid_le` and
`budget_le` are coupled through the single free multiplier `bddOverlap`.  Pinning it to the
**minimal** value `overlap := classMass_bdd / shellArea` makes `paid_le` hold by exact
cancellation (needing only `shellArea > 0`); the genuine cross-phase content collapses to the
*single* inequality `classMass_bdd · (c⋆·ξ·X/6) ≤ termTower · shellArea` (`budget_le`).

* `bddOverlapOfShell`, `bddOverlapOfShell_nonneg` — the pinned overlap and `overlap_nonneg`
  (self-contained);
* `bddPaidLe_ofShell` — `paid_le`, fully closed (self-contained, modulo `shellArea > 0`);
* `bddBudgetLe_ofShell` — `budget_le`, reduced to the single named cross-phase inequality.

## The N.1.0 / N.24 / N.13 comparisons (cross-phase named interfaces)

`hterm`, `hD..hbdd` (count-vs-mass against the *other* phases' assembled masses) and
`n2Window` (N.13 rolling-window budget vs. the run mass) are intrinsically cross-leaf — they
feed the central charge bridge.  They are carried as clearly-named hypotheses of the
assemblers `erdos260N2CoresV2_ofWindowBudget`, `erdos260N33CoresV2_ofInterfaces`, and
`erdos260IrreducibleCoresV2_ofInterfaces`, which inhabit the exact V2 residual surfaces.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset
open Erdos260.AppendixN

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-! ## §1 — the model-leaf shell-paid area and its strict positivity -/

/-- The §22.1A model leaf's shell-paid area `∑_b wt₀(b)·Y_sh(b)`, i.e. exactly the
right-hand factor appearing in the L.6.2 `paid_le` field of `Erdos260N33CoresV2`. -/
def chernoffShellArea (ctx : ActualFailureContext) : ℝ :=
  ∑ b ∈ (chernoff22_1ALeafOfShell ctx).stoppedTree.paths,
    (chernoff22_1ALeafOfShell ctx).wt0 b * (chernoff22_1ALeafOfShell ctx).Ysh b

/-- The shell-paid area unfolds to the concrete gap-word sum
`∑_{σ∈{0,1}²} carryThresholdMeasure Q σ 2 · cost σ`. -/
theorem chernoffShellArea_eq_model (ctx : ActualFailureContext) :
    chernoffShellArea ctx
      = ∑ σ ∈ modelPaths, carryThresholdMeasure ctx.shell.Q σ 2 * (modelNsh σ : ℝ) :=
  rfl

/-- **Self-contained.**  The model leaf's shell-paid area is strictly positive: every
term is nonnegative, and the `σ = (1,1)` term `(1/2)²·2 = 1/2` is positive. -/
theorem chernoffShellArea_pos (ctx : ActualFailureContext) :
    0 < chernoffShellArea ctx := by
  rw [chernoffShellArea_eq_model]
  refine Finset.sum_pos' (fun σ hσ => ?_) ⟨fun _ => 1, ?_, ?_⟩
  · -- every term is nonnegative
    refine mul_nonneg ?_ (Nat.cast_nonneg _)
    rw [carryThresholdMeasure_eq ctx.shell.Q σ (le_refl 2)]
    positivity
  · -- the constant word `(1,1)` is a genuine path
    rw [modelPaths, Fintype.mem_piFinset]
    intro i
    exact Finset.mem_range.2 (by norm_num)
  · -- its contribution is positive
    rw [carryThresholdMeasure_eq ctx.shell.Q (fun _ => 1) (le_refl 2)]
    refine mul_pos (by positivity) ?_
    have h2 : modelNsh (fun _ : Fin 2 => 1) = 2 := by
      simp [modelNsh, shellCost]
    rw [h2]; norm_num

/-- `chernoffShellArea ctx ≠ 0`. -/
theorem chernoffShellArea_ne_zero (ctx : ActualFailureContext) :
    chernoffShellArea ctx ≠ 0 :=
  (chernoffShellArea_pos ctx).ne'

/-! ## §2 — the bounded terminal class mass is a nonnegative count -/

/-- The bounded (Tower-routed) terminal class mass is nonnegative (it is the count of
carry start atoms routed to `𝔒_bdd`). -/
theorem classMassV4_bdd_nonneg (ctx : ActualFailureContext) :
    0 ≤ AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
      OutputClassV4.bdd := by
  rw [appendixN33ClassMass_eq_card]
  exact Nat.cast_nonneg _

/-! ## §3 — the pinned L.6.2 overlap and the closed `paid_le` / `overlap_nonneg` -/

/-- **The pinned L.6.2 bounded-overlap multiplier.**  The minimal overlap making the
truncation `paid_le` an exact identity: `overlap := classMass_bdd / shellArea`. -/
def bddOverlapOfShell (ctx : ActualFailureContext) : ℝ :=
  AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight OutputClassV4.bdd
    / chernoffShellArea ctx

/-- **`overlap_nonneg`, fully closed.**  A nonnegative count over a positive area. -/
theorem bddOverlapOfShell_nonneg (ctx : ActualFailureContext) :
    0 ≤ bddOverlapOfShell ctx :=
  div_nonneg (classMassV4_bdd_nonneg ctx) (chernoffShellArea_pos ctx).le

/-- **L.6.2 `paid_le`, fully closed (self-contained).**  With the pinned overlap
`classMass_bdd / shellArea`, the bounded class mass equals `overlap · shellArea` exactly
(`shellArea > 0`), so the truncation inequality holds by reflexivity. -/
theorem bddPaidLe_ofShell (ctx : ActualFailureContext) :
    AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight OutputClassV4.bdd
      ≤ bddOverlapOfShell ctx *
        (∑ b ∈ (chernoff22_1ALeafOfShell ctx).stoppedTree.paths,
          (chernoff22_1ALeafOfShell ctx).wt0 b * (chernoff22_1ALeafOfShell ctx).Ysh b) := by
  have hkey : bddOverlapOfShell ctx * chernoffShellArea ctx
      = AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
          OutputClassV4.bdd := by
    unfold bddOverlapOfShell
    exact div_mul_cancel₀ _ (chernoffShellArea_ne_zero ctx)
  show AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight OutputClassV4.bdd
      ≤ bddOverlapOfShell ctx * chernoffShellArea ctx
  exact hkey.ge

/-- **L.6.2 `budget_le`, reduced to the single named cross-phase inequality.**  With the
pinned overlap, `overlap · (c⋆·ξ·X/6) ≤ O_bdd` is *equivalent* (clearing the positive area)
to the genuine cross-phase comparison `classMass_bdd · (c⋆·ξ·X/6) ≤ O_bdd · shellArea`.
Instantiate `O_bdd := termTower (pcv.toPhaseCores.phases ctx).toClosurePhaseData`. -/
theorem bddBudgetLe_ofShell (ctx : ActualFailureContext) (O_bdd : ℝ)
    (Hbdd :
      AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight OutputClassV4.bdd
          * (erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6)
        ≤ O_bdd * chernoffShellArea ctx) :
    bddOverlapOfShell ctx
        * (erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6)
      ≤ O_bdd := by
  unfold bddOverlapOfShell
  rw [div_mul_eq_mul_div, div_le_iff₀ (chernoffShellArea_pos ctx)]
  exact Hbdd

/-! ## §4 — the N.2 residual surface from the N.13 window-budget interface -/

/-- **`Erdos260N2CoresV2`, assembled from the single N.13 comparison.**  The only residual
of the reduced N.2 surface is the rolling-window budget routing into the run-phase mass;
it is the genuine cross-phase comparison `windowBound ≤ run.runMass`. -/
def erdos260N2CoresV2_ofWindowBudget (pcv : Erdos260PhaseCoresV2)
    (hwin : ∀ ctx : ActualFailureContext,
      appendixN2WindowBound ctx ≤ (pcv.toPhaseCores.phases ctx).run.runMass) :
    Erdos260N2CoresV2 pcv where
  n2Window := hwin

/-! ## §5 — the N.3.3 residual surface from the minimal cross-phase interfaces -/

/-- **`Erdos260N33CoresV2`, assembled from the minimal cross-phase interfaces.**

The L.6.2 bounded-class block is closed up to one inequality: `bddOverlap` is pinned,
`overlap_nonneg` and `paid_le` are proved outright, and `budget_le` is reduced to the single
named comparison `hbddBudget`.  The N.1.0 terminal-mass domination `hterm`, the five N.24
class budgets `hD..hbdd` (count-vs-assembled-mass) remain the genuine cross-phase residuals,
exposed as named hypotheses in their concrete routed-atom-count form. -/
def erdos260N33CoresV2_ofInterfaces
    {pcv : Erdos260PhaseCoresV2} {n2v : Erdos260N2CoresV2 pcv}
    (hterm : ∀ ctx : ActualFailureContext,
      n2v.toN2Cores.termMass ctx ≤ ((appendixN33Atoms ctx).card : ℝ))
    (hD : ∀ ctx : ActualFailureContext,
      (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.densePack)).card : ℝ)
        ≤ termDensePack (pcv.toPhaseCores.phases ctx).toClosurePhaseData)
    (hP : ∀ ctx : ActualFailureContext,
      (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.progress)).card : ℝ)
        ≤ termChernoff (pcv.toPhaseCores.phases ctx).toClosurePhaseData)
    (hE : ∀ ctx : ActualFailureContext,
      (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.endpoint)).card : ℝ)
        ≤ termReturn (pcv.toPhaseCores.phases ctx).toClosurePhaseData)
    (hCNL : ∀ ctx : ActualFailureContext,
      (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.cnl)).card : ℝ)
        ≤ termCnl (pcv.toPhaseCores.phases ctx).toClosurePhaseData)
    (hbdd : ∀ ctx : ActualFailureContext,
      (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.bdd)).card : ℝ)
        ≤ termTower (pcv.toPhaseCores.phases ctx).toClosurePhaseData)
    (hbddBudget : ∀ ctx : ActualFailureContext,
      AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight OutputClassV4.bdd
          * (erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6)
        ≤ termTower (pcv.toPhaseCores.phases ctx).toClosurePhaseData
            * chernoffShellArea ctx) :
    Erdos260N33CoresV2 pcv n2v where
  hterm := hterm
  hD := hD
  hP := hP
  hE := hE
  hCNL := hCNL
  hbdd := hbdd
  bddOverlap := bddOverlapOfShell
  bddOverlapNonneg := bddOverlapOfShell_nonneg
  bddPaidLe := bddPaidLe_ofShell
  bddBudgetLe := fun ctx =>
    bddBudgetLe_ofShell ctx (termTower (pcv.toPhaseCores.phases ctx).toClosurePhaseData)
      (hbddBudget ctx)

/-! ## §6 — the full V2 irreducible residual surface from the named interfaces -/

/-- **`Erdos260IrreducibleCoresV2`, assembled from a phase-core package and the minimal
named cross-phase interfaces.**  Demonstrates that the reduced V2 surface is exactly
inhabited by: the phase cores `pcv`, the N.13 window comparison `hwin`, the N.1.0/N.24
count-vs-mass comparisons `hterm`/`hD..hbdd`, and the single L.6.2 budget comparison
`hbddBudget` (everything else of the L.6.2 split being closed in §3). -/
def erdos260IrreducibleCoresV2_ofInterfaces
    (pcv : Erdos260PhaseCoresV2)
    (hwin : ∀ ctx : ActualFailureContext,
      appendixN2WindowBound ctx ≤ (pcv.toPhaseCores.phases ctx).run.runMass)
    (hterm : ∀ ctx : ActualFailureContext,
      (erdos260N2CoresV2_ofWindowBudget pcv hwin).toN2Cores.termMass ctx
        ≤ ((appendixN33Atoms ctx).card : ℝ))
    (hD : ∀ ctx : ActualFailureContext,
      (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.densePack)).card : ℝ)
        ≤ termDensePack (pcv.toPhaseCores.phases ctx).toClosurePhaseData)
    (hP : ∀ ctx : ActualFailureContext,
      (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.progress)).card : ℝ)
        ≤ termChernoff (pcv.toPhaseCores.phases ctx).toClosurePhaseData)
    (hE : ∀ ctx : ActualFailureContext,
      (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.endpoint)).card : ℝ)
        ≤ termReturn (pcv.toPhaseCores.phases ctx).toClosurePhaseData)
    (hCNL : ∀ ctx : ActualFailureContext,
      (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.cnl)).card : ℝ)
        ≤ termCnl (pcv.toPhaseCores.phases ctx).toClosurePhaseData)
    (hbdd : ∀ ctx : ActualFailureContext,
      (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.bdd)).card : ℝ)
        ≤ termTower (pcv.toPhaseCores.phases ctx).toClosurePhaseData)
    (hbddBudget : ∀ ctx : ActualFailureContext,
      AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight OutputClassV4.bdd
          * (erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6)
        ≤ termTower (pcv.toPhaseCores.phases ctx).toClosurePhaseData
            * chernoffShellArea ctx) :
    Erdos260IrreducibleCoresV2 where
  phaseCores := pcv
  n2Cores := erdos260N2CoresV2_ofWindowBudget pcv hwin
  n33Cores :=
    erdos260N33CoresV2_ofInterfaces hterm hD hP hE hCNL hbdd hbddBudget

end

/-! ## Axiom audit -/

#print axioms chernoffShellArea_pos
#print axioms bddOverlapOfShell_nonneg
#print axioms bddPaidLe_ofShell
#print axioms bddBudgetLe_ofShell
#print axioms erdos260N2CoresV2_ofWindowBudget
#print axioms erdos260N33CoresV2_ofInterfaces
#print axioms erdos260IrreducibleCoresV2_ofInterfaces

end Erdos260
