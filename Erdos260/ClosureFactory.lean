import Mathlib
import Erdos260.Erdos260Closure

/-!
# Closure factory layer

This file exposes the residual manuscript obligation in a slightly more
operational form than `Erdos260ClosureCertificate`.

`Erdos260ClosureCertificate` is the canonical final interface: for every
large failing dyadic shell it returns an `Erdos260PerFailureCertificate`.
During the remaining formalization it is useful to split that per-failure
certificate into the six phase-data producers plus the single pressure
lower-bound conjunct.  The structures below are a lossless refactoring of
that obligation: they add no mathematical assumptions beyond the fields
they explicitly expose, and they provide constructors back to the canonical
certificate interface.
-/

namespace Erdos260

open Finset

noncomputable section

/--
The six phase-data bundles for a single failing dyadic shell, before they
are assembled into `Erdos260PerFailureCertificate`.

The fields correspond to Phases 4--9 in the closure plan.  The pressure
lower bound is kept in a separate structure below so that the carry/pressure
work can be developed independently from the package upper bounds.
-/
structure ClosurePhaseData (cStar ξ X : ℝ) where
  chernoff : ChernoffPathData cStar ξ X
  cnl : CNLEntropyData cStar ξ X
  tower : TowerPackageData cStar ξ X
  densePack : DensePackData cStar ξ X
  returnPkg : ReturnPackageData cStar ξ X
  run : RunPackageData cStar ξ X

/-- The total mass appearing in the per-failure pressure lower bound. -/
def ClosurePhaseMass {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) : ℝ :=
  weightedMass
      (highCostSet data.chernoff.paths data.chernoff.cost data.chernoff.Y)
      data.chernoff.weight +
    (cleanCNLKraftSum data.cnl.paths data.cnl.BNDHeight data.cnl.c *
      data.cnl.shellFactor * X * data.cnl.Ij) +
    (∑ b ∈ data.tower.entryExitSet, data.tower.chargedWeight b) +
    (data.densePack.densePackPoints.card : ℝ) +
    (data.returnPkg.ordinaryShort + data.returnPkg.semiperiodic +
      data.returnPkg.olc + data.returnPkg.nonlocalLong) +
    data.run.runMass

/--
The pressure lower-bound obligation for a fixed choice of phase data.

This is the exact lower-bound field required by
`Erdos260PerFailureCertificate`, stated against `ClosurePhaseData` so that
the carry/pressure formalization has a focused target.
-/
def ClosurePressureLowerBound
    (cPr : ℝ) {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) : Prop :=
  cPr * X <= ClosurePhaseMass data

/--
A single-instance factory: phase data plus the pressure lower bound.

This is definitionally equivalent to a per-failure certificate, but the split
fields make the remaining formalization milestones visible in Lean.
-/
structure PerFailureFactory (cPr cStar ξ X : ℝ) where
  phaseData : ClosurePhaseData cStar ξ X
  pressureLowerBound : ClosurePressureLowerBound cPr phaseData

/-- Assemble a single-instance factory into the canonical certificate. -/
def PerFailureFactory.toCertificate
    {cPr cStar ξ X : ℝ}
    (factory : PerFailureFactory cPr cStar ξ X) :
    Erdos260PerFailureCertificate cPr cStar ξ X where
  chernoff := factory.phaseData.chernoff
  cnl := factory.phaseData.cnl
  tower := factory.phaseData.tower
  densePack := factory.phaseData.densePack
  returnPkg := factory.phaseData.returnPkg
  run := factory.phaseData.run
  pressureLowerBound := factory.pressureLowerBound

/--
Global factory form of the manuscript closure obligation.

The `perFailure` field has the same quantifiers as
`Erdos260ClosureCertificate.perFailure`, but returns the split
`PerFailureFactory`.  The theorem `GlobalClosureFactory.toCertificate`
below converts it back to the canonical user-facing certificate.
-/
structure GlobalClosureFactory where
  constants : Erdos260Constants
  startThreshold :
    ∀ (Q : Nat) (d : Nat -> Nat),
      0 < Q -> BinaryDigits d -> ¬ EventuallyZero d ->
      (∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) ->
        Nat
  /-- **Round Α2**: failure hypothesis uses `c0` (strict) rather than `cQ`. -/
  perFailure :
    ∀ (Q : Nat) (d : Nat -> Nat)
      (hQ : 0 < Q) (hd : BinaryDigits d)
      (hnonterm : ¬ EventuallyZero d)
      (hrational :
        ∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)),
      ∀ X : Nat, Dyadic X ->
        startThreshold Q d hQ hd hnonterm hrational ≤ X ->
        ((supportShell d X).card : ℝ) < constants.c0 * (X : ℝ) ->
          PerFailureFactory constants.cPr constants.cStar constants.ξ (X : ℝ)

/-- Convert the split global factory into the canonical closure certificate. -/
def GlobalClosureFactory.toCertificate
    (factory : GlobalClosureFactory) :
    Erdos260ClosureCertificate where
  cQ := factory.constants.cQ
  c0 := factory.constants.c0
  cPr := factory.constants.cPr
  cStar := factory.constants.cStar
  ξ := factory.constants.ξ
  cQ_pos := factory.constants.cQ_pos
  c0_pos := factory.constants.c0_pos
  c0_le_cQ := factory.constants.c0_le_cQ
  cPr_pos := factory.constants.cPr_pos
  cStar_pos := factory.constants.cStar_pos
  ξ_pos := factory.constants.ξ_pos
  constantsCompatible := factory.constants.constantsCompatible
  startThreshold := factory.startThreshold
  perFailure := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfail
    exact (factory.perFailure Q d hQ hd hnonterm hrational X hXdyadic hXge hfail).toCertificate

end

end Erdos260
