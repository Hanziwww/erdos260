import Erdos260.UnconditionalAssembly
import Erdos260.UnconditionalAssemblyTight
import Erdos260.CNLConstantCompat
import Erdos260.ChargeMultiplierClosure
import Erdos260.PressureFloorConstruction
import Erdos260.PkgExposesConstruction
import Erdos260.TowerAPModulusConstruction
import Erdos260.RunProvenanceConstruction

/-!
# Re-tightened capstone, round 2: consolidating the four research-core reductions

`UnconditionalAssemblyTight.lean` reduced Erdős #260 to `Erdos260MinimalAtoms'`
(round 1).  Four new research-core modules push into the genuine mathematics and
shrink the trust surface further.  This file (NEW; the **most-downstream** node) is
their consolidation into `Erdos260MinimalAtoms''` and the top theorem
`erdos260_reduced_minimal''`.

It is downstream of all four research modules and of round 1; it edits nothing
upstream.  `erdos260_reduced_minimal''` reuses the existing `erdos260_reduced_minimal`
plumbing verbatim (via `Erdos260MinimalAtoms''.toMinimalAtoms`).  To avoid the Tower
granularity mismatch (round 1's `towerAP` field is `TowerAPModuli`, while the new
recurrent-cycle builder yields a `TowerSlopeAtom` directly) the target is
`Erdos260MinimalAtoms` (round 0's structure), into which all four new builders' outputs
slot cleanly, with round 1's CNL reduction carried over via `cnlProvider_ofUnconditional`.

## What was genuinely discharged this round (honest)

* **Pressure floor (Lemma 21.1) analytic core — CLOSED.**  `PressureFloorConstruction`
  *constructs* `CarryDataFromFailure` (which carries the floor `cPr·X ≤ highExcessMass`
  as `highExcessMass_lower`) from structural shell-window side-conditions only, via
  `carryDataPinned` (the numerical allocation `hAlloc` is now proved).  The `carryData`
  atom is REDUCED to the structural inputs `(L, B, X=2^L, 4Q≤2^B, B+25≤L, K≥L+1, 1≤supportCount)`.
* **`pkg_exposes` — CLOSED structurally.**  `PkgExposesConstruction.StructuralPkgGeometry`
  supplies `pkg_exposes` as a *theorem* (`toObstructionGeometry`), under the manuscript-J.5
  definition `PKG-available := six-package disjunction`.  The charge atom's geometry input
  is REDUCED to the free `label`/`cleanAvail` data — no coverage hypothesis.
* **Tower AP-modulus arithmetic — CLOSED.**  `TowerAPModulusConstruction` builds the
  `TowerSlopeAtom` from a recurrent `CarryFibreCycleData` (`towerSlopeAtomOfRecurrentCycle`):
  oddness is `carryCycle_den_odd` (2-adic descent) and the Mersenne period `H ∣ 2^{φ(H)}−1`
  is automatic.  The `towerAP` atom is REDUCED to the recurrent-cycle datum.
* **Run `(q₀,a,m)` provenance — CLOSED to one input.**  `RunProvenanceConstruction.ResidualCenter`
  derives `(q₀,a,m)`, the scale, and the L.4.2 half-decrease from a single non-dyadic
  small-denominator center `ν/Qp`; `toRunFactoryData` builds `RunFactoryData`.  The `run`
  atom is REDUCED to the `ResidualCenter` datum + the per-shell routing/budget.

## Genuinely irreducible after this round (the remaining trust surface)

* the additive AP-subfibre shell geometry (E.2–E.4): producing the recurrent-cycle datum
  from a failing shell's `integerCarry` (the `TowerRecurrentCycle` input);
* the §25.1 binary-digit↔cylinder bridge (the `ResidualCenter` input — that the actual mask
  word equals `dyadicDigit q₀ a`);
* the per-shell charge count/pointwise/routing data (the J.1.1/N.24/I.9 charging — 0/7
  multipliers follow from proved budgets) and the J.5 PKG-definitional faithfulness inside
  `StructuralPkgGeometry`;
* the structural shell-window side-conditions of the pressure floor;
* the still-untouched per-shell Chernoff / DensePack / Return factory data and the CNL
  bridge/budget inputs.

No `sorry`, `admit`, or new `axiom`.  `#print axioms erdos260_reduced_minimal''` is the
three standard logical axioms only.
-/

namespace Erdos260

noncomputable section

/-! ## 1. Pressure floor: the structural shell-window datum (replacing the carry-data atom) -/

/--
**Per-shell structural shell-window datum (manuscript Lemma 21.1, asymptotic regime).**

The structural side-conditions to which `PressureFloorConstruction` reduces the
`carryData` atom: a dyadic exponent `L` (`X = 2^L`), a `Q`-gap exponent `B`
(`4Q ≤ 2^B`), the sufficiently-large-scale qualifier `B + 25 ≤ L`, shell richness
`L + 1 ≤ |supportShell|`, and at least one hit `1 ≤ supportCount`.  The numerical
allocation `hAlloc` — the genuine analytic input of Lemma 21.1 — is **proved**
(`hAlloc_manuscript_strict`), so no analytic inequality remains hidden.
-/
structure ShellWindowInputs (shell : FailingDyadicShell) where
  L : ℕ
  B : ℕ
  hX_eq : shell.X = 2 ^ L
  hB : shell.Q * 4 ≤ 2 ^ B
  hL : B + 25 ≤ L
  hKr : L + 1 ≤ (supportShell shell.d shell.X).card
  h_supportCount_pos : 1 ≤ supportCount shell.d shell.X

/-- Construct the Lemma 21.1 carry data (carrying the pressure floor) from the
structural shell-window datum, via `carryDataPinned`. -/
def ShellWindowInputs.build {shell : FailingDyadicShell} (w : ShellWindowInputs shell) :
    CarryDataFromFailure shell erdos260Constants.cPr :=
  carryDataPinned shell w.L w.B w.hX_eq w.hB w.hL w.hKr w.h_supportCount_pos

/-! ## 2. Tower: the recurrent carry-fibre cycle datum (replacing the AP-modulus atom) -/

/--
**Per-shell Tower recurrent-cycle datum (manuscript E.2–E.6).**

The genuinely geometric residual after `TowerAPModulusConstruction`: a recurrent
`CarryFibreCycleData` `D` with rational slopes `μ` (`hcast : (μ i : ℝ) = D.slope i`),
a chosen cycle vertex `i`, and a nonzero target denominator `Q`.  The slope modulus
oddness (`carryCycle_den_odd`), the Mersenne period (`odd_dvd_two_pow_totient_sub_one`),
the E.13 closure, the recurrent cycle and the Tower budget are all theorems; only the
realization of this cycle datum from the failing-shell `integerCarry` (E.2–E.4) remains.
-/
structure TowerRecurrentCycle where
  D : CarryFibreCycleData
  μ : Fin D.n → ℚ
  hcast : ∀ i, (μ i : ℝ) = D.slope i
  i : Fin D.n
  Q : ℕ
  hQ : Q ≠ 0

/-- Build the `TowerSlopeAtom` from the recurrent-cycle datum, via
`towerSlopeAtomOfRecurrentCycle` (oddness + Mersenne period derived). -/
def TowerRecurrentCycle.toSlopeAtom (t : TowerRecurrentCycle) : TowerSlopeAtom :=
  towerSlopeAtomOfRecurrentCycle t.D t.μ t.hcast t.i t.Q t.hQ

/-! ## 3. Run: the residual-center provenance datum (replacing the §25.2 scale atom) -/

/--
**Per-shell Run residual-center provenance datum (manuscript §25.1/§25.2).**

The reduced Run input after `RunProvenanceConstruction`: a single non-dyadic
small-denominator residual center `C : ResidualCenter` (the §25.1 geometric output,
`ν/Qp` with `Qp ≤ Q₀`, non-dyadic) — from which the §25.2 reduced data `(q₀,a,m)`, the
scale, and the L.4.2 half-decrease are all *derived* — together with the genuinely
shell-dependent analytic data `RunFactoryData` is about: the L.4.1 routing
`D : RunRoutingData α` and the per-shell budget (`chain_capture`, `chainRoot_le`, `hSmall`).
-/
structure RunProvenanceData (X : ℝ) where
  C : ResidualCenter
  α : Type
  u : ℕ
  weight : ℝ
  D : RunRoutingData α
  len : ℕ
  hlen : 1 ≤ len
  smallError : ℝ
  hsmall_nonneg : 0 ≤ smallError
  twoNegcY : ℝ
  Ij : ℝ
  chain_capture : D.toTri.chainMass ≤ ((C.scaleMult * orderOf (2 : ZMod C.q0) : ℕ) : ℝ)
  chainRoot_le : 2 * ((C.scaleMult * orderOf (2 : ZMod C.q0) : ℕ) : ℝ) ≤ X * Ij * twoNegcY
  hSmall :
    D.towerBound + D.returnBound + D.densePackBound + X * Ij * twoNegcY + smallError
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * X / 6

/-- Build the `RunFactoryData` from the residual-center provenance datum, via
`ResidualCenter.toRunFactoryData` (the §25.2 reduced data + half-decrease embedded). -/
def RunProvenanceData.build {X : ℝ} (r : RunProvenanceData X) :
    RunFactoryData erdos260Constants.cStar erdos260Constants.ξ X :=
  r.C.toRunFactoryData r.u r.weight r.D r.len r.hlen r.smallError r.hsmall_nonneg
    r.twoNegcY r.Ij r.chain_capture r.chainRoot_le r.hSmall

/-! ## 4. Charge: the structural-PKG fibre datum (replacing the `pkg_exposes` assumption) -/

/--
**Per-shell charge structural-PKG fibre datum (manuscript J.1.1 + J.5 + N.24 + L.6.5).**

The reduced charge input after `PkgExposesConstruction` + `ChargeMultiplierClosure`: a
`StructuralPkgGeometry` `P` whose `pkg_exposes` is a *theorem* (so the coverage primitive
is no longer assumed — only the free `label`/`cleanAvail` data + J.5 definitional
faithfulness remain), the per-fibre count×multiplier data for the separable classes
`0,1,3,6`, the Lemma N.3.1 compression data for the joint `2+4+5` class, and the L.6.5
old-residual smallness.  The routing is `P.toObstructionGeometry.toRouting config`.  The
five per-class multipliers are derived by `ofGeomFibre`; none is *closed* (no multiplier
follows from a proved phase budget).
-/
structure ShellChargeStructuralInput
    {shell : FailingDyadicShell}
    (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr) where
  /-- The v5 branch-level old-residual mass `OldRes_{s,j}(Y)` (Lemma L.6.4). -/
  oldResMass : ℝ
  /-- The structural PKG geometry — its `pkg_exposes` is the PROVED
  `StructuralPkgGeometry.pkg_exposes` (J.5 definition), not an assumed coverage field. -/
  P : StructuralPkgGeometry
  /-- The per-start lift-state configuration. -/
  config : ℕ → LiftState
  -- Class 0 (Chernoff) count×multiplier data.
  multChernoff : ℝ
  countChernoff : ℝ
  hpoint0 : ∀ k ∈ routedFibre carryData (P.toObstructionGeometry.toRouting config).classify 0,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ multChernoff
  hnn0 : 0 ≤ multChernoff
  hcard0 :
    ((routedFibre carryData (P.toObstructionGeometry.toRouting config).classify 0).card : ℝ)
      ≤ countChernoff
  hbud0 : countChernoff * multChernoff ≤ termChernoff phases.toClosurePhaseData
  -- Class 1 (clean-CNL) count×multiplier data.
  multCnl : ℝ
  countCnl : ℝ
  hpoint1 : ∀ k ∈ routedFibre carryData (P.toObstructionGeometry.toRouting config).classify 1,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ multCnl
  hnn1 : 0 ≤ multCnl
  hcard1 :
    ((routedFibre carryData (P.toObstructionGeometry.toRouting config).classify 1).card : ℝ)
      ≤ countCnl
  hbud1 : countCnl * multCnl ≤ termCnl phases.toClosurePhaseData
  -- Class 3 (DensePack) count×multiplier data.
  multDP : ℝ
  countDP : ℝ
  hpoint3 : ∀ k ∈ routedFibre carryData (P.toObstructionGeometry.toRouting config).classify 3,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ multDP
  hnn3 : 0 ≤ multDP
  hcard3 :
    ((routedFibre carryData (P.toObstructionGeometry.toRouting config).classify 3).card : ℝ)
      ≤ countDP
  hbud3 : countDP * multDP ≤ termDensePack phases.toClosurePhaseData
  -- Classes 2+4+5 (joint Tower+Return+Run) via the proved Lemma N.3.1 compression.
  β : Type
  σ : Type
  [decσ : DecidableEq σ]
  comp : AppendixN.TerminalOutputData β σ
  hRouteToOutput :
    routedClassMassOf carryData (P.toObstructionGeometry.toRouting config).classify 2
        + routedClassMassOf carryData (P.toObstructionGeometry.toRouting config).classify 4
        + routedClassMassOf carryData (P.toObstructionGeometry.toRouting config).classify 5
      ≤ ∑ b ∈ comp.branches, comp.wtO b
  hAbsorb :
    comp.CQ * (comp.YO * ∑ ζ ∈ comp.ground, comp.fibreMass ζ)
      ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
          + termRun phases.toClosurePhaseData
  -- Class 6 (old-residual) count×multiplier data.
  multOR : ℝ
  countOR : ℝ
  hpoint6 : ∀ k ∈ routedFibre carryData (P.toObstructionGeometry.toRouting config).classify 6,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ multOR
  hnn6 : 0 ≤ multOR
  hcard6 :
    ((routedFibre carryData (P.toObstructionGeometry.toRouting config).classify 6).card : ℝ)
      ≤ countOR
  hbud6 : countOR * multOR ≤ oldResMass
  /-- **Lemma L.6.5** — the old-residual mass is density-small `OldRes ≤ 1·c_*·X`. -/
  hsmall : oldResMass ≤ 1 * manuscriptCstarSmall * (shell.X : ℝ)

/-- Build the `ShellRoutedChargeAtom` from the structural-PKG fibre datum: the routing is
`P.toObstructionGeometry.toRouting config` (coverage = the PROVED `pkg_exposes`), the five
multipliers are derived by `ofGeomFibre`, and the L.6.5 smallness wraps it via
`ofRoutingCharge`. -/
def ShellChargeStructuralInput.build
    {shell : FailingDyadicShell}
    {phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell erdos260Constants.cPr}
    (inp : ShellChargeStructuralInput phases carryData) :
    ShellRoutedChargeAtom phases carryData 1 manuscriptCstarSmall :=
  letI := inp.decσ
  ShellRoutedChargeAtom.ofRoutingCharge
    (CarryPriorityRoutingCharge.ofGeomFibre phases carryData
      inp.P.toObstructionGeometry inp.config
      inp.hpoint0 inp.hnn0 inp.hcard0 inp.hbud0
      inp.hpoint1 inp.hnn1 inp.hcard1 inp.hbud1
      inp.hpoint3 inp.hnn3 inp.hcard3 inp.hbud3
      inp.comp inp.hRouteToOutput inp.hAbsorb
      inp.hpoint6 inp.hnn6 inp.hcard6 inp.hbud6)
    inp.hsmall

/-! ## 5. The round-2 re-tightened minimal atoms -/

/--
**The round-2 re-tightened minimal residual atoms for Erdős #260 (v5).**

`Erdos260MinimalAtoms` with four fields replaced by their finer, research-proved inputs,
and the CNL field carried over at round-1 granularity:

* `carryWindow` (was `carryData`) — structural shell-window inputs; pressure-floor analytic
  core CLOSED;
* `cnlInput` (was `cnl`) — per-shell `CNLUnconditionalKraftInput` (round 1); Kraft sub-field
  derived;
* `towerCycle` (was `towerSlope`) — recurrent carry-fibre cycle datum; AP-modulus arithmetic
  CLOSED;
* `runProvenance` (was `run`) — `ResidualCenter` provenance datum; `(q₀,a,m)` CLOSED to one input;
* `chargeStructural` (was `charge`) — `StructuralPkgGeometry` fibre datum; `pkg_exposes` CLOSED.

The untouched fields `chernoff`, `densePack`, `returnPkg` remain genuinely per-shell factory
data (not addressed this round).
-/
structure Erdos260MinimalAtoms'' where
  /-- **REDUCED** — per-failure structural shell-window inputs; the pressure floor is built. -/
  carryWindow :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → ShellWindowInputs shell
  /-- Per-failure Chernoff high-cost path data (untouched). -/
  chernoff :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- **REDUCED (round 1)** — per-failure unconditional CNL Kraft input. -/
  cnlInput :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        CNLUnconditionalKraftInput erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : ℝ)
  /-- Per-failure DensePack factory data (untouched). -/
  densePack :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- **REDUCED** — per-failure Tower recurrent-cycle datum; `Odd H` + Mersenne period derived. -/
  towerCycle :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → TowerRecurrentCycle
  /-- Per-failure return-package factory data (untouched). -/
  returnPkg :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- **REDUCED** — per-failure Run residual-center provenance datum; `(q₀,a,m)` derived. -/
  runProvenance :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → RunProvenanceData (shell.X : ℝ)
  /-- **Phase-mass nonnegativity (manuscript §I / J.1.1 charging).** The per-shell Return
  and Run phase masses are physically nonnegative; discharges the `phases.trtNonneg`
  restriction of `chargeStructural` for the genuine phase data. -/
  returnRunMassNonneg :
    ∀ (shell : FailingDyadicShell) (hcQ : shell.cQ = erdos260Constants.cQ),
      0 ≤ (returnPkg shell hcQ).massSum + ((runProvenance shell hcQ).build).runMass
  /-- **REDUCED** — per-failure charge structural-PKG fibre datum; `pkg_exposes` proved.
  **Restricted to TRT-nonnegative phase data** (`phases.trtNonneg`). -/
  chargeStructural :
    ∀ (shell : FailingDyadicShell)
      (_hcQ : shell.cQ = erdos260Constants.cQ)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
      (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
      (_hphases : phases.trtNonneg),
        ShellChargeStructuralInput phases carryData

/--
**Expand the round-2 atoms back into `Erdos260MinimalAtoms`.**

The four reduced fields are run through their research-proved builders (`carryDataPinned`,
`towerSlopeAtomOfRecurrentCycle`, `ResidualCenter.toRunFactoryData`,
`StructuralPkgGeometry.toObstructionGeometry` + `ofGeomFibre`); the CNL field through
`cnlProvider_ofUnconditional` (round 1); the three untouched fields are forwarded.
-/
def Erdos260MinimalAtoms''.toMinimalAtoms (m : Erdos260MinimalAtoms'') :
    Erdos260MinimalAtoms where
  carryData := fun shell hcQ _hlarge => (m.carryWindow shell hcQ).build
  chernoff := m.chernoff
  cnl := cnlProvider_ofUnconditional m.cnlInput
  densePack := m.densePack
  towerSlope := fun shell hcQ => (m.towerCycle shell hcQ).toSlopeAtom
  returnPkg := m.returnPkg
  run := fun shell hcQ => (m.runProvenance shell hcQ).build
  returnRunMassNonneg := m.returnRunMassNonneg
  charge := fun shell hcQ phases carryData hphases =>
    (m.chargeStructural shell hcQ phases carryData hphases).build

/--
**Erdős #260 reduced to the round-2 minimal residual atoms (the capstone, round 2).**

Identical conclusion to `erdos260_reduced` / `erdos260_reduced_minimal` /
`erdos260_reduced_minimal'`, conditional on the further-tightened `Erdos260MinimalAtoms''`:
the pressure-floor analytic core, `pkg_exposes`, the Tower AP-modulus arithmetic, and the
Run `(q₀,a,m)` provenance are all discharged.  Proved by expanding to `Erdos260MinimalAtoms`
and reusing `erdos260_reduced_minimal`.

**Honest scope.** This is conditional, NOT unconditional.  The remaining trust surface is:
the additive AP-subfibre shell geometry (E.2–E.4, the `TowerRecurrentCycle` realization),
the §25.1 binary-digit↔cylinder bridge (the `ResidualCenter` realization), the per-shell
charge count/pointwise/routing data with the J.5 PKG-definitional faithfulness, the
structural shell-window side-conditions, and the untouched Chernoff/DensePack/Return
per-shell factory data + CNL bridge/budget inputs.
-/
theorem erdos260_reduced_minimal'' (m : Erdos260MinimalAtoms'') : Erdos260Statement :=
  erdos260_reduced_minimal m.toMinimalAtoms

end

end Erdos260
