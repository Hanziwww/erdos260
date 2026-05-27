import Mathlib
import Erdos260.AppendixG_CNL
import Erdos260.AppendixG_Chernoff
import Erdos260.AppendixK1_DensePack
import Erdos260.AppendixL2_Return
import Erdos260.AppendixL3_Tower
import Erdos260.AppendixL4_Run
import Erdos260.Constants
import Erdos260.PressureLower
import Erdos260.TheoremA

/-!
# Phase 10: assembly of `Erdos260AnalyticInputsAtomic`

This file performs the final closure step.  It bundles the per-phase
witness producers (Phases 1--9) into a single `Erdos260FailureCertificate`
structure that, when inhabited for every failing dyadic shell, yields
a real Lean instance of `Erdos260AnalyticInputsAtomic`.

## Closure logic

The `AtomicWitnessProp` packaged in [Erdos260.TheoremA] requires six
reals summing to at least `cPr · X`, each individually bounded by
`cStar · ξ · X / 6`.  Phases 4--9 provide the six bounds; Phases 2--3
provide the lower bound through Lemma 21.1.  The numerical
compatibility `cStar · ξ < cPr` (Phase 1) is what forces the failure
hypothesis to be vacuous.

The remaining external content is the **manuscript Appendix H certificate**:
for every rational-target binary nonterminating sequence and every
sufficiently large dyadic `X` at which the positive-density failure
hypothesis is assumed, the per-phase witness data must exist.  The
manuscript constructs these from the carry recurrence, the CNL ladder,
the refined tower, the dense-marker greedy cover, the synchronizing-set
counting, and the run trichotomy.

In this file we package the residual as `Erdos260ClosureCertificate`
and provide `Erdos260AnalyticInputsAtomic.ofCertificate` that converts
it into the atomic input bundle.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ### The closure certificate -/

/--
**Per-failure closure certificate.**

For a fixed `cStar, ξ, X`, this structure packages the six per-phase
witness data bundles together with the certificate of the lower-bound
conjunct: the sum of the six produced witnesses must be at least `cPr · X`.

The six manuscript witnesses are exactly those constructed by Phases 4--9.
The lower bound comes from Phases 2--3 (via `lemma21_1_pressureLowerBound`
in `Pressure.lean`).
-/
structure Erdos260PerFailureCertificate (cPr cStar ξ X : ℝ) where
  /-- Phase 4: Chernoff path-space data producing `Regular`. -/
  chernoff : ChernoffPathData cStar ξ X
  /-- Phase 5: CNL Kraft entropy data producing `CleanTerm`. -/
  cnl : CNLEntropyData cStar ξ X
  /-- Phase 7: tower package data producing `Tower`. -/
  tower : TowerPackageData cStar ξ X
  /-- Phase 6: dense-pack data producing `DensePackVal`. -/
  densePack : DensePackData cStar ξ X
  /-- Phase 8: return package data producing `ReturnVal`. -/
  returnPkg : ReturnPackageData cStar ξ X
  /-- Phase 9: run package data producing `RunVal`. -/
  run : RunPackageData cStar ξ X
  /--
  Manuscript pressure lower bound (Phases 2--3 via Lemma 21.1):
  the sum of the six witness reals is at least `cPr · X`.

  The six witnesses are the ones produced by `chernoffPathSpace`,
  `cnlEntropy`, `towerPackageBound`, `densePackBound`,
  `nonRunReturnBound`, `runBound` respectively.
  -/
  pressureLowerBound :
    cPr * X <=
      weightedMass
          (highCostSet chernoff.paths chernoff.cost chernoff.Y)
          chernoff.weight +
        (cleanCNLKraftSum cnl.paths cnl.BNDHeight cnl.c *
          cnl.shellFactor * X * cnl.Ij) +
        (∑ b ∈ tower.entryExitSet, tower.chargedWeight b) +
        (densePack.densePackPoints.card : ℝ) +
        (returnPkg.ordinaryShort + returnPkg.semiperiodic +
          returnPkg.olc + returnPkg.nonlocalLong) +
        run.runMass

/-! ### Phase 10 main construction -/

/--
**Phase 10: `AtomicWitnessProp` from a per-failure certificate.**

Given a per-failure certificate, we discharge `AtomicWitnessProp` by
producing six reals from Phases 4--9 and using the certificate's
pressure lower bound.
-/
theorem atomicWitnessProp_of_perFailure
    {cPr cStar ξ X : ℝ}
    (cert : Erdos260PerFailureCertificate cPr cStar ξ X) :
    AtomicWitnessProp cPr cStar ξ X := by
  classical
  haveI : DecidableEq cert.chernoff.α := cert.chernoff.decEq
  refine ⟨
    weightedMass
      (highCostSet cert.chernoff.paths cert.chernoff.cost cert.chernoff.Y)
      cert.chernoff.weight,
    cleanCNLKraftSum cert.cnl.paths cert.cnl.BNDHeight cert.cnl.c *
      cert.cnl.shellFactor * X * cert.cnl.Ij,
    ∑ b ∈ cert.tower.entryExitSet, cert.tower.chargedWeight b,
    (cert.densePack.densePackPoints.card : ℝ),
    cert.returnPkg.ordinaryShort + cert.returnPkg.semiperiodic +
      cert.returnPkg.olc + cert.returnPkg.nonlocalLong,
    cert.run.runMass,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Regular ≤ cStar ξ X / 6
    have hChernoff :
        weightedMass
            (highCostSet cert.chernoff.paths cert.chernoff.cost cert.chernoff.Y)
            cert.chernoff.weight <=
          cert.chernoff.root * cert.chernoff.A ^ cert.chernoff.m /
            cert.chernoff.z ^ cert.chernoff.Y :=
      shellChernoff_bound_of_moment_bound (paths := cert.chernoff.paths)
        (weight := cert.chernoff.weight) (cost := cert.chernoff.cost)
        (Y := cert.chernoff.Y) (m := cert.chernoff.m) (z := cert.chernoff.z)
        (root := cert.chernoff.root) (A := cert.chernoff.A)
        cert.chernoff.weight_nonneg cert.chernoff.z_ge_one
        cert.chernoff.moment_bound
    exact hChernoff.trans cert.chernoff.manuscript_bound
  · -- CleanTerm ≤ cStar ξ X / 6
    calc cleanCNLKraftSum cert.cnl.paths cert.cnl.BNDHeight cert.cnl.c *
            cert.cnl.shellFactor * X * cert.cnl.Ij
        <= cert.cnl.CQ ^ cert.cnl.M * cert.cnl.shellFactor * X * cert.cnl.Ij :=
          cert.cnl.manuscript_dominates
      _ <= cStar * ξ * X / 6 := cert.cnl.manuscript_bound
  · -- Tower ≤ cStar ξ X / 6
    have hTower :=
      propositionI3_1_towerOutput cert.tower.hSummable
    exact hTower.trans cert.tower.hSmall
  · -- DensePackVal ≤ cStar ξ X / 6
    have hK13 :=
      corollaryK1_3_densePackUnderFailure
        (densePackPoints := cert.densePack.densePackPoints)
        (markersCard := cert.densePack.markersCard)
        (spread := cert.densePack.spread)
        (cStar := cert.densePack.cStarSmall) (X := X)
        cert.densePack.hcover cert.densePack.hcount
    exact hK13.trans cert.densePack.hsmall
  · -- ReturnVal ≤ cStar ξ X / 6
    have hReturn :=
      proposition23_1_returnPackagesLowerClean
        cert.returnPkg.hOrdinaryShort cert.returnPkg.hSemiperiodic
        cert.returnPkg.hOLC cert.returnPkg.hNonlocalLong
    exact hReturn.trans cert.returnPkg.hSmall
  · -- RunVal ≤ cStar ξ X / 6
    have hRun := propositionI5_2_runOutput cert.run.hRun
    exact hRun.trans cert.run.hSmall
  · -- cPr * X ≤ sum
    exact cert.pressureLowerBound

/-! ### Bundle: closure certificate over all failing instances -/

/--
**Global closure certificate.**

For every rational-target binary nonterminating sequence `(Q, d)`,
provides an `X₀` beyond which every failing dyadic `X` admits the
per-failure certificate.

This is the *complete* residual external content that, once supplied,
makes `Erdos260AnalyticInputsAtomic` real.
-/
structure Erdos260ClosureCertificate where
  cQ : ℝ
  cPr : ℝ
  cStar : ℝ
  ξ : ℝ
  cQ_pos : 0 < cQ
  cPr_pos : 0 < cPr
  cStar_pos : 0 < cStar
  ξ_pos : 0 < ξ
  constantsCompatible : cStar * ξ < cPr
  /-- Per-instance starting threshold beyond which the failure
  certificates exist (data, since the certificate itself is `Type`). -/
  startThreshold :
    ∀ (Q : Nat) (d : Nat -> Nat),
      0 < Q -> BinaryDigits d -> ¬ EventuallyZero d ->
      (∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) ->
        Nat
  /-- For every failing dyadic `X ≥ startThreshold Q d`, the
  per-failure certificate exists.  This is the residual manuscript
  content. -/
  perFailure :
    ∀ (Q : Nat) (d : Nat -> Nat)
      (hQ : 0 < Q) (hd : BinaryDigits d)
      (hnonterm : ¬ EventuallyZero d)
      (hrational :
        ∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)),
      ∀ X : Nat, Dyadic X ->
        startThreshold Q d hQ hd hnonterm hrational ≤ X ->
        ((supportShell d X).card : ℝ) < cQ * (X : ℝ) ->
          Erdos260PerFailureCertificate cPr cStar ξ (X : ℝ)

/--
**`Erdos260AnalyticInputsAtomic` from the global closure certificate.**

Conversion: the global certificate yields the atomic input bundle by
applying `atomicWitnessProp_of_perFailure` instance-by-instance.
-/
def Erdos260AnalyticInputsAtomic.ofCertificate
    (cert : Erdos260ClosureCertificate) :
    Erdos260AnalyticInputsAtomic where
  cQ := cert.cQ
  cPr := cert.cPr
  cStar := cert.cStar
  ξ := cert.ξ
  cQ_pos := cert.cQ_pos
  cPr_pos := cert.cPr_pos
  cStar_pos := cert.cStar_pos
  ξ_pos := cert.ξ_pos
  constantsCompatible := cert.constantsCompatible
  atomicWitness := by
    intro Q d hQ hd hnonterm hrational
    refine ⟨cert.startThreshold Q d hQ hd hnonterm hrational,
            fun X hXdyadic hXge hfail => ?_⟩
    exact atomicWitnessProp_of_perFailure
      (cert.perFailure Q d hQ hd hnonterm hrational X hXdyadic hXge hfail)

/-! ### Final unconditional theorems modulo the manuscript certificate -/

/--
**Theorem A from the closure certificate.**

This is `theoremA_of_atomic_inputs` (real algebra in `TheoremA.lean`)
composed with `Erdos260AnalyticInputsAtomic.ofCertificate`.
-/
theorem theoremA_of_closureCertificate
    (cert : Erdos260ClosureCertificate) :
    TheoremAStatement :=
  theoremA_of_atomic_inputs (Erdos260AnalyticInputsAtomic.ofCertificate cert)

/--
**Erdős 260 statement from the closure certificate.**

This is `erdos260Statement_of_atomic_inputs` (real algebra in `TheoremA.lean`)
composed with `Erdos260AnalyticInputsAtomic.ofCertificate`.
-/
theorem erdos260Statement_of_closureCertificate
    (cert : Erdos260ClosureCertificate) :
    Erdos260Statement :=
  erdos260Statement_of_atomic_inputs (Erdos260AnalyticInputsAtomic.ofCertificate cert)

end

end Erdos260
