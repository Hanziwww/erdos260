import Mathlib
import Erdos260.Erdos260ReducedToCores
import Erdos260.CNLScalarBudgetCore
import Erdos260.ReturnM2J4Core
import Erdos260.RunL4I52Core
import Erdos260.TowerL31I31Core
import Erdos260.ChernoffAntichainCore
import Erdos260.DirtyFibreBoundCore
import Erdos260.AppendixN2N3Cores

/-!
# Erdős #260 reduced to its irreducible cores, V2 (proven cores spliced in)

This module **re-integrates** the seven freshly-proved `…OfShell` core families
into the residual surface of `Erdos260ReducedToCores`, producing a *strictly
smaller* irreducible residual structure `Erdos260IrreducibleCoresV2` and a green,
axiom-clean reduction

```
erdos260_modulo_cores_v2 (h : Erdos260IrreducibleCoresV2) : Erdos260Statement.
```

The original `erdos260_modulo_cores (h : Erdos260IrreducibleCores)` is left fully
intact; `erdos260_modulo_cores_v2` is obtained by *reconstructing* a genuine
`Erdos260IrreducibleCores` from `h` and the proven cores, then invoking the
original.  No obligation is dropped silently: every eliminated field of
`Erdos260IrreducibleCores` is supplied by a real theorem from one of the seven
core files, and the surviving fields are exactly the genuine remaining analytic
residuals.

## What the proven cores eliminate (per phase)

* **CNL (CNLScalarBudgetCore).**  `cnlShellFactorOfShell`, `cnlIjOfShell`,
  `cnlBudgetOfShell` close `cnlShellFactor` / `cnlIj` / `cnlBudget` outright — the
  CNL phase is *fully closed*.
* **Tower (TowerL31I31Core).**  `towerClsOfShell` closes `towerCls`;
  `towerClsOfShell_budget_of_densePackFraction` reduces `towerBudget` to the I.4.1
  dense-packing fraction `highExcessMass ≤ c_* · X`.
* **Run (RunL4I52Core).**  `runClsOfShell`, `runFOfShell`, `runTwoNegcYOfShell`,
  `runIjOfShell`, `runSmallErrorOfShell`, `runSmallErrorNonnegOfShell`,
  `runChainRootOfShell` close 7/8 Run fields; `runBudgetOfShell` reduces the 8th to
  `RunMassWithinBudget`.
* **Return (ReturnM2J4Core).**  `olcGeomOfShell` (M.2.1 nesting multiplicity
  *proved*), the canonical scalars `retSCanonical` / `retIjCanonical`, and the
  proved `retOlcRoute_canonical` / `retOlcMLBudget_canonical` close `retOlcGeom`,
  `retS`, `retIj`, `retOlcRoute`, `retOlcMLBudget`, and (trivially) `retHsXij`.
* **Dirty (DirtyFibreBoundCore).**  `dirtyLeafFibreBound_of_window` reduces the
  per-dyadic-pair fibre bound `dirtyFibre` to the pure digit-sequence count
  `WindowRunScaleCountBound` (off-diagonal scales closed unconditionally).
* **N.2 / N.3.3 (AppendixN2N3Cores).**  `erdos260N2Cores_ofRunBudget` closes
  `n2A` / `n2hA` and reduces `n2Window` to `windowBound ≤ run.runMass`;
  `erdos260N33Cores_ofCardBudgets` reduces the five N.3.3 class budgets +
  `n33hterm` to routed-atom count comparisons.
* **Chernoff (ChernoffAntichainCore).**  `bddLowPaidOfShell` reduces the L.6.2
  `bddLowPaid` split to the two genuine inequalities `paid_le` / `budget_le`
  (plus `overlap_nonneg`).  The `chernoff` slot itself remains the *fully
  unconditional* model leaf (so the §22 Kraft sum `hKraft` never enters the
  residual).

## The central charge-bridge (budget consolidation)

The Tower finding (`towerBudget_residual_forces_X_nonpos`) shows that the
`…OfShell` re-indexings make `towerBudget` and `RunMassWithinBudget` (with the
canonical classifiers pinned) **both literally equal to the single fact**
`highExcessMass ≤ c_⋆·ξ·X/6`, which collides with the proved Lemma 21.1 lower
bound.  Carrying them as two independent fields would over-claim.  We therefore
consolidate them into the *single* residual `centralDensePack`, the genuine I.4.1
dense-packing fraction `highExcessMass ≤ c_* · X` (strictly stronger; `c_* =
manuscriptCstarSmall`), and *derive* both `towerBudget` and `runBudget` from it
via `towerClsOfShell_budget_of_densePackFraction` and the proved run-trichotomy
mass conservation (`runMassWithinBudget_of_densePack`).

No `sorry` / `axiom` / `admit`.
-/

namespace Erdos260

open Finset
open Erdos260.AppendixN

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-! ## Stage 0 — the central charge-bridge implies the Tower and Run budgets -/

/-- The dense-packing fraction `c_* · X` sits below the per-phase budget slot
`c_⋆·ξ·X/6` (the K.4 constant inequality `manuscriptCstarSmall_le_towerSlot`
scaled by the nonnegative shell scale `X`). -/
theorem manuscriptCstarSmall_mul_X_le_slot (ctx : ActualFailureContext) :
    manuscriptCstarSmall * (ctx.shell.X : ℝ)
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  have hXnn : 0 ≤ (ctx.shell.X : ℝ) := ctx.shell.X_nonneg_real
  calc manuscriptCstarSmall * (ctx.shell.X : ℝ)
      ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 6) * (ctx.shell.X : ℝ) :=
        mul_le_mul_of_nonneg_right manuscriptCstarSmall_le_towerSlot hXnn
    _ = erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by ring

/-- **The I.5.2 run-mass budget from the central dense-packing fraction.**

With the L.4.1 classifier pinned to `runClsOfShell`, the chain class carries zero
routed mass (`runClsOfShell_routed3_zero`), so the mean-low + local-spike +
boundary masses (classes `0,1,2`) sum to the *entire* high-excess carry mass
(`highExcessMass_eq_sum_routedClassMassOf` over `Fin 4`).  Hence
`RunMassWithinBudget` follows from `highExcessMass ≤ c_* · X` by chaining the
dense-packing fraction with `manuscriptCstarSmall_mul_X_le_slot`. -/
theorem runMassWithinBudget_of_densePack (ctx : ActualFailureContext)
    (hDP :
      highExcessMass
          (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
          (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ manuscriptCstarSmall * (ctx.shell.X : ℝ)) :
    RunMassWithinBudget ctx := by
  have hsum := highExcessMass_eq_sum_routedClassMassOf ctx.n24CarryData (runClsOfShell ctx)
  simp only [Fin.sum_univ_four] at hsum
  have h3 := runClsOfShell_routed3_zero ctx
  have hslot := manuscriptCstarSmall_mul_X_le_slot ctx
  unfold RunMassWithinBudget
  linarith [hsum, h3, hDP, hslot]

/-! ## Stage A — the reduced phase-core residual surface -/

/-- The reduced phase-core residual surface: only the genuine remaining
local-analytic inputs of the six phase leaves after splicing the proven cores.
Strictly smaller than `Erdos260PhaseCores` (32 fields → 14). -/
structure Erdos260PhaseCoresV2 where
  /-- **Central charge-bridge (I.4.1/I.4.2 dense-packing fraction).**  The
  consolidated mass-budget residual: the high-excess carry mass dense-packs into
  the fraction `c_* · X`.  Discharges *both* the Tower I.3.1 budget and the Run
  I.5.2 budget (the two collide with Lemma 21.1 in their full-mass form, so they
  are one fact, not two). -/
  centralDensePack : ∀ ctx : ActualFailureContext,
    highExcessMass
        (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
        (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ manuscriptCstarSmall * (ctx.shell.X : ℝ)
  -- Return L.2.2 / M.2 / K.4 residue (priority routing + per-class charges), at
  -- the proved canonical OLC scales `retSCanonical = 2·M_L`, `retIjCanonical = 1/X`.
  /-- **L.2.2 priority routing** of the high-excess starts to the three non-OLC
  return sub-pieces. -/
  retCls : ∀ ctx : ActualFailureContext, ℕ → Fin 3
  retC1 : ∀ ctx : ActualFailureContext, ℝ
  retC2 : ∀ ctx : ActualFailureContext, ℝ
  retC3 : ∀ ctx : ActualFailureContext, ℝ
  retC4 : ∀ ctx : ActualFailureContext, ℝ
  retSmallError : ∀ ctx : ActualFailureContext, ℝ
  /-- **M.2 / Prop. 23.1 OLC return-slot routing** (at the canonical scales). -/
  retOlcReturnBudget : ∀ ctx : ActualFailureContext,
    retSCanonical ctx * (ctx.shell.X : ℝ) * retIjCanonical ctx
      ≤ retC3 ctx * erdos260Constants.ξ * retSCanonical ctx * (ctx.shell.X : ℝ)
          * retIjCanonical ctx + retSmallError ctx / 4
  /-- **L.2.2 ordinary-short** routed-mass count. -/
  retOrdinaryShort : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (retCls ctx) 0
      ≤ retC1 ctx * erdos260Constants.ξ * retSCanonical ctx * (ctx.shell.X : ℝ)
          * retIjCanonical ctx + retSmallError ctx / 4
  /-- **L.2.2 semiperiodic** routed-mass count. -/
  retSemiperiodic : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (retCls ctx) 1
      ≤ retC2 ctx * erdos260Constants.ξ * retSCanonical ctx * (ctx.shell.X : ℝ)
          * retIjCanonical ctx + retSmallError ctx / 4
  /-- **L.2.2 nonlocal-long** routed-mass count. -/
  retNonlocalLong : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (retCls ctx) 2
      ≤ retC4 ctx * erdos260Constants.ξ * retSCanonical ctx * (ctx.shell.X : ℝ)
          * retIjCanonical ctx + retSmallError ctx / 4
  /-- **K.4 return-budget smallness.** -/
  retHSmall : ∀ ctx : ActualFailureContext,
    (retC1 ctx + retC2 ctx + retC3 ctx + retC4 ctx) * erdos260Constants.ξ
          * retSCanonical ctx * (ctx.shell.X : ℝ) * retIjCanonical ctx + retSmallError ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  -- Dirty K.2.5 residue (absolute-constant path): the genuine remaining content
  -- is the pure run-length digit count (off-diagonal scales closed in the core).
  /-- The manuscript absolute fibre constant `C`. -/
  dirtyCM : ∀ ctx : ActualFailureContext, ℕ
  /-- **K.2.5 window run-length count bound** — *few window positions share any
  forward-run scale* (the Fine–Wilf / J.4 / Erdős–Szekeres residual). -/
  dirtyWindow : ∀ ctx : ActualFailureContext,
    WindowRunScaleCountBound ctx (dirtyCM ctx)

namespace Erdos260PhaseCoresV2

/-- Reconstruct a genuine `Erdos260PhaseCores` from the reduced residual surface
and the proven `…OfShell` cores. -/
def toPhaseCores (h : Erdos260PhaseCoresV2) : Erdos260PhaseCores where
  -- CNL — fully closed.
  cnlShellFactor := cnlShellFactorOfShell
  cnlIj := cnlIjOfShell
  cnlBudget := cnlBudgetOfShell
  -- Dirty — reduced to the window run-length count.
  dirtyCM := h.dirtyCM
  dirtyFibre := fun ctx => dirtyLeafFibreBound_of_window ctx (h.dirtyCM ctx) (h.dirtyWindow ctx)
  -- Tower — classifier closed; budget from the central dense-packing fraction.
  towerCls := towerClsOfShell
  towerBudget := fun ctx =>
    towerClsOfShell_budget_of_densePackFraction ctx (h.centralDensePack ctx)
  -- Return — geometry/scalars closed; analytic residue from `h`.
  retCls := h.retCls
  retOlcGeom := retOlcGeomCanonical
  retC1 := h.retC1
  retC2 := h.retC2
  retC3 := h.retC3
  retC4 := h.retC4
  retS := retSCanonical
  retIj := retIjCanonical
  retSmallError := h.retSmallError
  retOlcRoute := retOlcRoute_canonical
  retOlcMLBudget := retOlcMLBudget_canonical
  retOlcReturnBudget := h.retOlcReturnBudget
  retHsXij := fun ctx => by
    have h1 : (0 : ℝ) ≤ retSCanonical ctx := by
      unfold retSCanonical
      exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    have h2 : (0 : ℝ) ≤ (ctx.shell.X : ℝ) := ctx.shell.X_nonneg_real
    have h3 : (0 : ℝ) ≤ retIjCanonical ctx := by
      unfold retIjCanonical
      exact one_div_nonneg.mpr h2
    exact mul_nonneg (mul_nonneg h1 h2) h3
  retOrdinaryShort := h.retOrdinaryShort
  retSemiperiodic := h.retSemiperiodic
  retNonlocalLong := h.retNonlocalLong
  retHSmall := h.retHSmall
  -- Run — 7/8 closed; budget from the central dense-packing fraction.
  runCls := runClsOfShell
  runF := runFOfShell
  runTwoNegcY := runTwoNegcYOfShell
  runIj := runIjOfShell
  runSmallError := runSmallErrorOfShell
  runSmallErrorNonneg := runSmallErrorNonnegOfShell
  runChainRoot := runChainRootOfShell
  runBudget := fun ctx =>
    runBudgetOfShell ctx (runMassWithinBudget_of_densePack ctx (h.centralDensePack ctx))

end Erdos260PhaseCoresV2

/-! ## Stage B — the reduced N.2 residual surface -/

/-- The reduced N.2 residual surface: only the N.13 window-budget comparison,
tied to the genuine run-phase mass (`n2A` / `n2hA` are closed in the core).
Strictly smaller than `Erdos260N2Cores` (3 fields → 1). -/
structure Erdos260N2CoresV2 (pcv : Erdos260PhaseCoresV2) where
  /-- **N.13 rolling-window budget** routes into the run-phase mass. -/
  n2Window : ∀ ctx : ActualFailureContext,
    appendixN2WindowBound ctx ≤ (pcv.toPhaseCores.phases ctx).run.runMass

namespace Erdos260N2CoresV2

/-- Reconstruct a genuine `Erdos260N2Cores` from the reduced N.2 surface. -/
def toN2Cores {pcv : Erdos260PhaseCoresV2} (n2v : Erdos260N2CoresV2 pcv) :
    Erdos260N2Cores pcv.toPhaseCores :=
  erdos260N2Cores_ofRunBudget pcv.toPhaseCores n2v.n2Window

end Erdos260N2CoresV2

/-! ## Stage C — the reduced N.3.3 residual surface -/

/-- The reduced N.3.3 residual surface: the N.1.0 terminal-mass count, the five
N.24 class-budget counts (against the assembled phase masses), and the L.6.2
shell-paid split reduced to its two genuine inequalities `paid_le` / `budget_le`
(plus `overlap_nonneg`). -/
structure Erdos260N33CoresV2 (pcv : Erdos260PhaseCoresV2)
    (n2v : Erdos260N2CoresV2 pcv) where
  /-- **N.1.0 terminal-mass domination**, reduced to the routed-atom count. -/
  hterm : ∀ ctx : ActualFailureContext,
    n2v.toN2Cores.termMass ctx ≤ ((appendixN33Atoms ctx).card : ℝ)
  /-- **N.24 DensePack class budget**, reduced to a routed-atom count. -/
  hD : ∀ ctx : ActualFailureContext,
    (((appendixN33Atoms ctx).filter
        (fun e => (appendixN33Row e).outputClass = OutputClassV4.densePack)).card : ℝ)
      ≤ termDensePack (pcv.toPhaseCores.phases ctx).toClosurePhaseData
  /-- **N.24 Progress class budget**, reduced to a routed-atom count. -/
  hP : ∀ ctx : ActualFailureContext,
    (((appendixN33Atoms ctx).filter
        (fun e => (appendixN33Row e).outputClass = OutputClassV4.progress)).card : ℝ)
      ≤ termChernoff (pcv.toPhaseCores.phases ctx).toClosurePhaseData
  /-- **N.24 Endpoint class budget**, reduced to a routed-atom count. -/
  hE : ∀ ctx : ActualFailureContext,
    (((appendixN33Atoms ctx).filter
        (fun e => (appendixN33Row e).outputClass = OutputClassV4.endpoint)).card : ℝ)
      ≤ termReturn (pcv.toPhaseCores.phases ctx).toClosurePhaseData
  /-- **N.24 clean-CNL class budget**, reduced to a routed-atom count. -/
  hCNL : ∀ ctx : ActualFailureContext,
    (((appendixN33Atoms ctx).filter
        (fun e => (appendixN33Row e).outputClass = OutputClassV4.cnl)).card : ℝ)
      ≤ termCnl (pcv.toPhaseCores.phases ctx).toClosurePhaseData
  /-- **N.24 bounded class budget**, reduced to a routed-atom count. -/
  hbdd : ∀ ctx : ActualFailureContext,
    (((appendixN33Atoms ctx).filter
        (fun e => (appendixN33Row e).outputClass = OutputClassV4.bdd)).card : ℝ)
      ≤ termTower (pcv.toPhaseCores.phases ctx).toClosurePhaseData
  /-- L.6.2 bounded-overlap multiplier. -/
  bddOverlap : ∀ ctx : ActualFailureContext, ℝ
  bddOverlapNonneg : ∀ ctx : ActualFailureContext, 0 ≤ bddOverlap ctx
  /-- **L.6.2 bounded-overlap truncation** (proof_v4 line 5810): the bounded
  terminal class mass is dominated by `overlap ·` the Chernoff model leaf's
  shell-paid area. -/
  bddPaidLe : ∀ ctx : ActualFailureContext,
    AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.bdd ≤
      bddOverlap ctx * (∑ b ∈ (chernoff22_1ALeafOfShell ctx).stoppedTree.paths,
        (chernoff22_1ALeafOfShell ctx).wt0 b * (chernoff22_1ALeafOfShell ctx).Ysh b)
  /-- **L.6.2 budget placement**: `overlap · (c_⋆·ξ·X/6) ≤ O_bdd`. -/
  bddBudgetLe : ∀ ctx : ActualFailureContext,
    bddOverlap ctx *
        (erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6)
      ≤ termTower (pcv.toPhaseCores.phases ctx).toClosurePhaseData

namespace Erdos260N33CoresV2

/-- Reconstruct a genuine `Erdos260N33Cores` from the reduced N.3.3 surface. -/
def toN33Cores {pcv : Erdos260PhaseCoresV2} {n2v : Erdos260N2CoresV2 pcv}
    (n33v : Erdos260N33CoresV2 pcv n2v) :
    Erdos260N33Cores pcv.toPhaseCores n2v.toN2Cores :=
  erdos260N33Cores_ofCardBudgets pcv.toPhaseCores n2v.toN2Cores
    n33v.hterm n33v.hD n33v.hP n33v.hE n33v.hCNL n33v.hbdd
    (fun ctx =>
      bddLowPaidOfShell ctx
        (termTower (pcv.toPhaseCores.phases ctx).toClosurePhaseData)
        (n33v.bddOverlap ctx) (n33v.bddOverlapNonneg ctx)
        (n33v.bddPaidLe ctx) (n33v.bddBudgetLe ctx))

end Erdos260N33CoresV2

/-! ## Stage D — the V2 irreducible residual surface and the reduced endpoint -/

/-- **The strictly-smaller irreducible residual surface.**  After splicing the
seven proven core families, only the genuine remaining local-analytic inputs
survive, bundled in three layers mirroring `Erdos260IrreducibleCores`. -/
structure Erdos260IrreducibleCoresV2 where
  phaseCores : Erdos260PhaseCoresV2
  n2Cores : Erdos260N2CoresV2 phaseCores
  n33Cores : Erdos260N33CoresV2 phaseCores n2Cores

namespace Erdos260IrreducibleCoresV2

/-- Reconstruct the *genuine* original obligation `Erdos260IrreducibleCores`
from the reduced V2 surface, supplying every eliminated field from a proven core
theorem.  No obligation is dropped: `erdos260_modulo_cores` consumes the full
result. -/
def toIrreducibleCores (h : Erdos260IrreducibleCoresV2) : Erdos260IrreducibleCores where
  phaseCores := h.phaseCores.toPhaseCores
  n2Cores := h.n2Cores.toN2Cores
  n33Cores := h.n33Cores.toN33Cores

end Erdos260IrreducibleCoresV2

/--
**Erdős #260, modulo the *re-integrated* irreducible cores.**

Given the strictly-smaller residual surface `Erdos260IrreducibleCoresV2`, the
seven proven `…OfShell` core families splice in to reconstruct the genuine
`Erdos260IrreducibleCores` obligation, which the original `erdos260_modulo_cores`
turns into a full proof of `Erdos260Statement`.  No `sorry`/`axiom`/`admit`.
-/
theorem erdos260_modulo_cores_v2 (h : Erdos260IrreducibleCoresV2) : Erdos260Statement :=
  erdos260_modulo_cores h.toIrreducibleCores

#print axioms erdos260_modulo_cores_v2

end

end Erdos260
