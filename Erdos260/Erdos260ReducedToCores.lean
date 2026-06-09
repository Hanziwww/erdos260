import Mathlib
import Erdos260.UnconditionalTheorem
import Erdos260.GlobalAppendixNChainCompressionCertificate
import Erdos260.ShellPaidChernoff22_1ALeafConstruction
import Erdos260.CNLLeafFromShell
import Erdos260.DirtyLeafFromShell
import Erdos260.TowerLeafFromShell
import Erdos260.RunLeafFromShell
import Erdos260.ReturnLeafFromShell
import Erdos260.AppendixN2LeafFromShell
import Erdos260.AppendixN33LeafFromShell

/-!
# Erdős #260 reduced to its irreducible local-analytic cores

This module wires the eight Phase-2 `…OfShell` leaf constructors into the actual
consumer surface `GlobalAssemblyActualExplicitPhaseClosedN2N3BddL6Inputs`
(`UnconditionalTheorem`) and reduces `Erdos260Statement` to a single explicit
bundle of genuine residual inputs `Erdos260IrreducibleCores`.

* the six phase leaves (Chernoff 22.1A, CNL L.1.2/G.35, Dirty K.2.5, Tower
  L.3/I.3, Return I.5.1/M.2/J.4/L.6, Run L.4.1/L.4.2/I.5.2) are assembled into
  the explicit six-phase factory package `actualProofV4LeafPhases`;
* the Chernoff slot uses the **fully unconditional** model leaf
  `chernoff22_1ALeafOfShell` (no `hKraft`);
* the N.2.1/N.2.2 variation leaf and the N.3.3 terminal-absorption leaf are
  bundled into the L.6-backed closed `ActualClosedN2N3BddL6Data` package, which
  drives the actual high-excess charge bridge.

No `sorry`/`axiom`/`admit`; the only remaining inputs are carried explicitly as
the fields of `Erdos260IrreducibleCores`.
-/

namespace Erdos260

open Erdos260.AppendixN

set_option linter.unusedVariables false

noncomputable section

/-! ## Stage A — the six-phase factory package from the phase leaves

`Erdos260PhaseCores` bundles exactly the residual inputs of the five non-trivial
phase leaves (Chernoff is fully unconditional and needs no residual). -/

/-- Residual inputs of the five non-trivial phase leaves. -/
structure Erdos260PhaseCores where
  -- CNL (L.1.2 / G.35 weighted-Kraft shell leaf)
  cnlShellFactor : ∀ ctx : ActualFailureContext, {x : ℝ // 0 ≤ x}
  cnlIj : ∀ ctx : ActualFailureContext, {x : ℝ // 0 ≤ x}
  cnlBudget : ∀ ctx : ActualFailureContext,
    (2 : ℝ) ^ cnlLeafShellM ctx * (cnlShellFactor ctx : ℝ) * (cnlIj ctx : ℝ) ≤
      erdos260Constants.cStar * erdos260Constants.ξ / 6
  -- Dirty (K.2.5 per-dyadic-pair fibre bound)
  dirtyCM : ∀ ctx : ActualFailureContext, ℕ
  dirtyFibre : ∀ ctx : ActualFailureContext, DirtyLeafFibreBound ctx (dirtyCM ctx)
  -- Tower (L.3.1 classifier + I.3.1 budget)
  towerCls : ∀ ctx : ActualFailureContext, ℕ → TowerExitClass
  towerBudget : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (towerCls ctx) TowerExitClass.run
        + routedClassMassOf ctx.n24CarryData (towerCls ctx) TowerExitClass.returnPkg
        + routedClassMassOf ctx.n24CarryData (towerCls ctx) TowerExitClass.densePack
        + routedClassMassOf ctx.n24CarryData (towerCls ctx) TowerExitClass.cnlTail
        + routedClassMassOf ctx.n24CarryData (towerCls ctx) TowerExitClass.other
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  -- Return (I.5.1/M.2/J.4/L.6 four-piece package)
  retCls : ∀ ctx : ActualFailureContext, ℕ → Fin 3
  retOlcGeom : ∀ ctx : ActualFailureContext, OLCEndpointMultiplicity ℕ ℕ
  retC1 : ∀ ctx : ActualFailureContext, ℝ
  retC2 : ∀ ctx : ActualFailureContext, ℝ
  retC3 : ∀ ctx : ActualFailureContext, ℝ
  retC4 : ∀ ctx : ActualFailureContext, ℝ
  retS : ∀ ctx : ActualFailureContext, ℝ
  retIj : ∀ ctx : ActualFailureContext, ℝ
  retSmallError : ∀ ctx : ActualFailureContext, ℝ
  retOlcRoute : ∀ ctx : ActualFailureContext,
    ((retOlcGeom ctx).baseSet.card : ℝ) ≤ (ctx.shell.X : ℝ) * retIj ctx
  retOlcMLBudget : ∀ ctx : ActualFailureContext,
    ((retOlcGeom ctx).multiplicityBound : ℝ) * (ctx.shell.X : ℝ) * retIj ctx
      ≤ retS ctx * (ctx.shell.X : ℝ) * retIj ctx / 2
  retOlcReturnBudget : ∀ ctx : ActualFailureContext,
    retS ctx * (ctx.shell.X : ℝ) * retIj ctx
      ≤ retC3 ctx * erdos260Constants.ξ * retS ctx * (ctx.shell.X : ℝ) * retIj ctx
          + retSmallError ctx / 4
  retHsXij : ∀ ctx : ActualFailureContext,
    0 ≤ retS ctx * (ctx.shell.X : ℝ) * retIj ctx
  retOrdinaryShort : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (retCls ctx) 0
      ≤ retC1 ctx * erdos260Constants.ξ * retS ctx * (ctx.shell.X : ℝ) * retIj ctx
          + retSmallError ctx / 4
  retSemiperiodic : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (retCls ctx) 1
      ≤ retC2 ctx * erdos260Constants.ξ * retS ctx * (ctx.shell.X : ℝ) * retIj ctx
          + retSmallError ctx / 4
  retNonlocalLong : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (retCls ctx) 2
      ≤ retC4 ctx * erdos260Constants.ξ * retS ctx * (ctx.shell.X : ℝ) * retIj ctx
          + retSmallError ctx / 4
  retHSmall : ∀ ctx : ActualFailureContext,
    (retC1 ctx + retC2 ctx + retC3 ctx + retC4 ctx) * erdos260Constants.ξ
          * retS ctx * (ctx.shell.X : ℝ) * retIj ctx + retSmallError ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  -- Run (L.4.1 classifier, §25.1 residue datum, L.4.2 chain root, I.5.2 budget)
  runCls : ∀ ctx : ActualFailureContext, ℕ → Fin 4
  runF : ∀ ctx : ActualFailureContext, FailingShellResidual
  runTwoNegcY : ∀ ctx : ActualFailureContext, ℝ
  runIj : ∀ ctx : ActualFailureContext, ℝ
  runSmallError : ∀ ctx : ActualFailureContext, ℝ
  runSmallErrorNonneg : ∀ ctx : ActualFailureContext, 0 ≤ runSmallError ctx
  runChainRoot : ∀ ctx : ActualFailureContext,
    2 * routedClassMassOf ctx.n24CarryData (runCls ctx) 3
      ≤ (ctx.shell.X : ℝ) * runIj ctx * runTwoNegcY ctx
  runBudget : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (runCls ctx) 0
        + routedClassMassOf ctx.n24CarryData (runCls ctx) 1
        + routedClassMassOf ctx.n24CarryData (runCls ctx) 2
        + (ctx.shell.X : ℝ) * runIj ctx * runTwoNegcY ctx + runSmallError ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6

namespace Erdos260PhaseCores

/-- The CNL weighted-Kraft shell leaf assembled from the residual inputs. -/
def cnlLeaf (pc : Erdos260PhaseCores) (ctx : ActualFailureContext) :
    CNLStandardWeightedKraftShellInputData ctx.shell
      erdos260Constants.cStar erdos260Constants.ξ :=
  cnlLeafOfShell ctx (pc.cnlShellFactor ctx) (pc.cnlIj ctx) (pc.cnlBudget ctx)

/-- The Tower separated local leaf assembled from the residual inputs. -/
def towerLeaf (pc : Erdos260PhaseCores) (ctx : ActualFailureContext) :
    TowerClosedL31I31PackageInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  towerLeafOfShell ctx (pc.towerCls ctx) (pc.towerBudget ctx)

/-- The Return separated local leaf assembled from the residual inputs. -/
def returnLeaf (pc : Erdos260PhaseCores) (ctx : ActualFailureContext) :
    ReturnClosedI51M2J4L6PackageInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  returnLeafOfShell ctx (pc.retCls ctx) (pc.retOlcGeom ctx)
    (pc.retC1 ctx) (pc.retC2 ctx) (pc.retC3 ctx) (pc.retC4 ctx)
    (pc.retS ctx) (pc.retIj ctx) (pc.retSmallError ctx)
    (pc.retOlcRoute ctx) (pc.retOlcMLBudget ctx) (pc.retOlcReturnBudget ctx)
    (pc.retHsXij ctx) (pc.retOrdinaryShort ctx) (pc.retSemiperiodic ctx)
    (pc.retNonlocalLong ctx) (pc.retHSmall ctx)

/-- The Run separated local leaf assembled from the residual inputs. -/
def runLeaf (pc : Erdos260PhaseCores) (ctx : ActualFailureContext) :
    RunClosedL41L42I52PackageInputData erdos260Constants.cStar
      erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  runLeafOfShell ctx (pc.runCls ctx) (pc.runF ctx) (pc.runTwoNegcY ctx)
    (pc.runIj ctx) (pc.runSmallError ctx) (pc.runSmallErrorNonneg ctx)
    (pc.runChainRoot ctx) (pc.runBudget ctx)

/-- The Dirty K.2.5 leaf assembled from the residual inputs. -/
def dirtyLeaf (pc : Erdos260PhaseCores) (ctx : ActualFailureContext) :
    DirtyMultiplicityProofV4ShellFibreInputData ctx.shell :=
  dirtyLeafOfShell ctx (pc.dirtyCM ctx) (pc.dirtyFibre ctx)

/-- The explicit actual six-phase factory package assembled from all six phase
leaves (Chernoff supplied by the fully unconditional model leaf). -/
def phases (pc : Erdos260PhaseCores) (ctx : ActualFailureContext) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) :=
  actualProofV4LeafPhases ctx
    (chernoff22_1ALeafOfShell ctx)
    (pc.cnlLeaf ctx)
    (appendixNGapCanonicalYActualDensePackToGrounded ctx.shell ctx.hc0Small
      ctx.shell_startThreshold_le)
    ((pc.dirtyLeaf ctx).toDirtyMultiplicityData)
    ((pc.towerLeaf ctx).toTowerSeparatedLocalLeafInputData)
    ((pc.returnLeaf ctx).toReturnSeparatedLocalLeafInputData)
    ((pc.runLeaf ctx).toRunSeparatedLocalLeafInputData)

end Erdos260PhaseCores

/-! ## Stage B — the N.2.1/N.2.2 variation leaf

The variation leaf's run-phase budget `O_V` is pinned to `termRun phases`, the
genuine run-phase mass of the assembled six-phase package.  The only residual is
the N.13 rolling-window comparison `n2Window`. -/

/-- Residual inputs of the N.2 variation leaf, on top of the phase package. -/
structure Erdos260N2Cores (pc : Erdos260PhaseCores) where
  n2A : ∀ ctx : ActualFailureContext, Set ℝ
  n2hA : ∀ ctx : ActualFailureContext, MeasurableSet (n2A ctx)
  n2Window : ∀ ctx : ActualFailureContext,
    appendixN2WindowBound ctx ≤ termRun (pc.phases ctx).toClosurePhaseData

namespace Erdos260N2Cores

/-- The N.2.1/N.2.2 variation leaf with `O_V := termRun phases`. -/
def variation {pc : Erdos260PhaseCores} (n2 : Erdos260N2Cores pc)
    (ctx : ActualFailureContext) :
    AppendixNVariationClosedN21N22InputData ctx.n24CarryLocal ctx.hc0Small
      ctx.n24SupportCount_pos (termRun (pc.phases ctx).toClosurePhaseData) :=
  appendixN2LeafOfShell ctx (n2.n2A ctx) (n2.n2hA ctx)
    (termRun (pc.phases ctx).toClosurePhaseData) (n2.n2Window ctx)

/-- The C1-VD split terminal mass derived from the variation leaf — exactly the
`termMass` argument the N.3.3 leaf and the L.6-backed closed N.2/N.3 package
demand. -/
def termMass {pc : Erdos260PhaseCores} (n2 : Erdos260N2Cores pc)
    (ctx : ActualFailureContext) : ℝ :=
  (GroundedC1VDSplitData.ofVariation
    (n2.variation ctx).toVariationClassData.toVariationClassData).termMass

end Erdos260N2Cores

/-! ## Stage C — the N.3.3 terminal-absorption leaf and the closed N.2/N.3 package

The six class budgets of the N.3.3 leaf are pinned to the genuine phase masses
of the assembled six-phase package (`O_D = termDensePack`, `O_P = termChernoff`,
`O_E = termReturn`, `O_CNL = termCnl`, `O_bdd = termTower`), and the terminal
mass is the C1-VD split of the variation leaf.  The residuals are the N.1.0 /
N.24 class inequalities (`n33hterm`, `n33hD`, …, `n33hbdd`) and the single L.6.2
shell-paid bounded-class split `bddLowPaid`. -/

/-- Residual inputs of the N.3.3 terminal-absorption leaf and the L.6.2 split,
on top of the phase package and the N.2 variation leaf. -/
structure Erdos260N33Cores (pc : Erdos260PhaseCores) (n2 : Erdos260N2Cores pc) where
  n33hterm : ∀ ctx : ActualFailureContext,
    n2.termMass ctx ≤ ∑ O ∈ appendixN33Outputs ctx, appendixN33Weight O
  n33hD : ∀ ctx : ActualFailureContext,
    AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.densePack ≤ termDensePack (pc.phases ctx).toClosurePhaseData
  n33hP : ∀ ctx : ActualFailureContext,
    AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.progress ≤ termChernoff (pc.phases ctx).toClosurePhaseData
  n33hE : ∀ ctx : ActualFailureContext,
    AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.endpoint ≤ termReturn (pc.phases ctx).toClosurePhaseData
  n33hCNL : ∀ ctx : ActualFailureContext,
    AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.cnl ≤ termCnl (pc.phases ctx).toClosurePhaseData
  n33hbdd : ∀ ctx : ActualFailureContext,
    AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.bdd ≤ termTower (pc.phases ctx).toClosurePhaseData
  /-- The L.6.2 shell-paid low/paid split of the bounded (Tower-routed) terminal
  class against the unconditional Chernoff model leaf. -/
  bddLowPaid : ∀ ctx : ActualFailureContext,
    ShellPaidBddClassBoundData.LowPaidSplitData (chernoff22_1ALeafOfShell ctx)
      (appendixN33Outputs ctx) appendixN33Weight
      (termTower (pc.phases ctx).toClosurePhaseData)

namespace Erdos260N33Cores

/-- The fully separated N.3.3 terminal-absorption leaf. -/
def n33Leaf {pc : Erdos260PhaseCores} {n2 : Erdos260N2Cores pc}
    (n33 : Erdos260N33Cores pc n2) (ctx : ActualFailureContext) :
    ClassicalTerminalN33SeparatedLeafData (n2.termMass ctx)
      (termDensePack (pc.phases ctx).toClosurePhaseData)
      (termChernoff (pc.phases ctx).toClosurePhaseData)
      (termReturn (pc.phases ctx).toClosurePhaseData)
      (termCnl (pc.phases ctx).toClosurePhaseData)
      (termTower (pc.phases ctx).toClosurePhaseData) :=
  appendixN33LeafOfShell ctx (n2.termMass ctx)
    (termDensePack (pc.phases ctx).toClosurePhaseData)
    (termChernoff (pc.phases ctx).toClosurePhaseData)
    (termReturn (pc.phases ctx).toClosurePhaseData)
    (termCnl (pc.phases ctx).toClosurePhaseData)
    (termTower (pc.phases ctx).toClosurePhaseData)
    (n33.n33hterm ctx) (n33.n33hD ctx) (n33.n33hP ctx) (n33.n33hE ctx)
    (n33.n33hCNL ctx) (n33.n33hbdd ctx)

/-- The L.6-backed five-class terminal absorption package, assembled from the
separated N.3.3 leaf and the L.6.2 bounded-class split. -/
def terminalAbsorption {pc : Erdos260PhaseCores} {n2 : Erdos260N2Cores pc}
    (n33 : Erdos260N33Cores pc n2) (ctx : ActualFailureContext) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data
      (chernoff22_1ALeafOfShell ctx)
      (GroundedC1VDSplitData.ofVariation
        (n2.variation ctx).toVariationClassData.toVariationClassData).termMass
      (termDensePack (pc.phases ctx).toClosurePhaseData)
      (termChernoff (pc.phases ctx).toClosurePhaseData)
      (termReturn (pc.phases ctx).toClosurePhaseData)
      (termCnl (pc.phases ctx).toClosurePhaseData)
      (termTower (pc.phases ctx).toClosurePhaseData) :=
  (AppendixNRawTerminalLowPaidInputData.ofTerminalLeafAndLowPaid
    (n33.n33Leaf ctx).toClassicalTerminalN33LeafData
    (n33.bddLowPaid ctx)).toClassicalTableRoutedDirectFiveClassTerminalAbsorptionWithBddL6Data

/-- The L.6-backed closed N.2/N.3 package consumed by the explicit-phase actual
surface. -/
def n2n3 {pc : Erdos260PhaseCores} {n2 : Erdos260N2Cores pc}
    (n33 : Erdos260N33Cores pc n2) (ctx : ActualFailureContext) :
    ActualClosedN2N3BddL6Data ctx (chernoff22_1ALeafOfShell ctx)
      (termDensePack (pc.phases ctx).toClosurePhaseData)
      (termChernoff (pc.phases ctx).toClosurePhaseData)
      (termReturn (pc.phases ctx).toClosurePhaseData)
      (termCnl (pc.phases ctx).toClosurePhaseData)
      (termTower (pc.phases ctx).toClosurePhaseData)
      (termRun (pc.phases ctx).toClosurePhaseData) where
  variation := n2.variation ctx
  terminalAbsorption := n33.terminalAbsorption ctx

end Erdos260N33Cores

/-! ## Stage D — the irreducible residual surface and the reduced endpoint

`Erdos260IrreducibleCores` bundles exactly the genuine remaining local-analytic
residuals of the eight Phase-2 shell leaves.  `erdos260_modulo_cores` assembles
all eight leaves through the explicit-phase actual consumer surface and proves
`Erdos260Statement`. -/

/-- The irreducible residual surface: the genuine remaining local-analytic
inputs to the eight Phase-2 shell leaves, after pinning every cross-phase budget
to the assembled six-phase package masses. -/
structure Erdos260IrreducibleCores where
  phaseCores : Erdos260PhaseCores
  n2Cores : Erdos260N2Cores phaseCores
  n33Cores : Erdos260N33Cores phaseCores n2Cores

namespace Erdos260IrreducibleCores

/-- Project the irreducible residual surface onto the explicit-phase actual
consumer surface, with the Chernoff slot supplied by the fully unconditional
model leaf. -/
def toExplicitPhaseInputs (h : Erdos260IrreducibleCores) :
    GlobalAssemblyActualExplicitPhaseClosedN2N3BddL6Inputs where
  phases := fun ctx => h.phaseCores.phases ctx
  chernoff := fun ctx => chernoff22_1ALeafOfShell ctx
  n2n3 := fun ctx => h.n33Cores.n2n3 ctx

end Erdos260IrreducibleCores

/--
**Erdős #260, modulo the irreducible local-analytic cores.**

Given the genuine remaining residuals `Erdos260IrreducibleCores`, the eight
Phase-2 shell leaves assemble — through the explicit-phase actual consumer
surface `GlobalAssemblyActualExplicitPhaseClosedN2N3BddL6Inputs` — into a full
proof of `Erdos260Statement`.  No `sorry`/`axiom`/`admit`: the only inputs are
the explicit fields of `Erdos260IrreducibleCores`.
-/
theorem erdos260_modulo_cores (h : Erdos260IrreducibleCores) : Erdos260Statement :=
  erdos260_final_actual_explicitPhaseClosedN2N3BddL6 h.toExplicitPhaseInputs

#print axioms erdos260_modulo_cores

end

end Erdos260

