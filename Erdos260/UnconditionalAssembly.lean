import Mathlib
import Erdos260.GlobalClosureAssembly
import Erdos260.CarryRouting
import Erdos260.ChargeBridgeContradiction
import Erdos260.ResidualScalarBudgets
import Erdos260.TowerLandingConstruction
import Erdos260.TowerFamily

/-!
# Capstone: the v5 reduction chain assembled to a single residual-atoms theorem

This file is the **capstone** of the Erdős #260 formalization.  It bundles the
entire v5 reduction chain into one top-level theorem `erdos260_reduced` that
derives the manuscript conclusion `Erdos260Statement` from a single explicit
structure `Erdos260ResidualAtoms` enumerating exactly the residual atomic
hypotheses that remain between the current development and an unconditional
proof.  **It does not claim the result unconditionally**; it makes the precise
remaining distance machine-checked.

## The reduction chain that is fully discharged here

`erdos260_reduced` composes the already-proved layers, contributing no new
analytic content of its own:

* the algebraic/combinatorial reduction `Erdos260Statement ⟵ GlobalAssemblyCoreInputs`
  (`erdos260Statement_of_globalAssemblyCoreInputs`, the existing conditional
  endpoint `erdos260_final_core`), which closes the global-threshold,
  per-failure-assembly, manuscript-closure, and Tendsto→support bridges;
* the v5 **augmented charge bridge** `highExcessMass ≤ ClosurePhaseMass + oldResMass`
  from the J.1.1 seven-class first-obstruction priority routing
  (`CarryPriorityRoutingCharge.toRoutedHighExcessChargeDataOldRes`);
* the v5 **contradiction engine** `refutes_failingShell`: the pressure floor
  `cPr·X ≤ highExcessMass` (carry lower bound), the summed manuscript per-phase
  budget `ClosurePhaseMass ≤ cStar·ξ·X` (`ClosurePhaseMass_le_budget`, which
  internally discharges the six budgets `termChernoff_le_budget … termRun_le_budget`),
  the augmented bridge, and the L.6.5 old-residual smallness `oldResMass ≤ C_Q·c_*·X`
  jointly refute every failing dyadic shell under the v5 constant condition
  `cStar·ξ + C_Q·c_* < cPr`.

The `highExcessCharge` provider — the single deepest field of the existing
`GlobalAssemblyCoreInputs` and the central charge bridge — is here **not taken as
a black box**.  It is built from the explicit charge-bridge atoms below by running
the contradiction engine: a failing shell yields `False`, from which the bridge
`HighExcessChargeData` follows vacuously.  This faithfully encodes the manuscript
argument "no low-density shell exists" at the charge-bridge layer.

## The residual atoms (the precise remaining hypotheses)

`Erdos260ResidualAtoms` bundles EXACTLY:

1. The two manuscript smallness constants `cQ` (the L.6.5 product constant
   `C_Q = (Cres·Y)(Csupp·Ij)`) and `cStarSmall` (the failure density `c_*`),
   together with the **final constant condition**
   `constantCondition : cStar·ξ + cQ·cStarSmall < cPr` (manuscript: choose `c_*`
   last, after all other constants).
2. The seven per-shell phase/carry construction providers
   (`carryData`, `chernoff`, `cnl`, `densePack`, `tower`, `returnPkg`, `run`) —
   identical to the seven data fields of `GlobalAssemblyCoreInputs`.  Each
   per-class factory datum carries its own deep leaves (Tower
   `CarryFibreDynamics`/finiteness, CNL `sym_injOn`, geomDetect `pkg_labeled`,
   Run realization, the Return envelope `M_L·X|I| ≤ s·X|I|/2`, …) **and its
   manuscript per-phase budget** `term_X ≤ cStar·ξ·X/6`, the latter consumed
   automatically inside the contradiction engine.
3. The per-shell **charge atom** `charge`: for every failing shell with its phase
   and carry data, a `CarryPriorityRoutingCharge` (the genuinely-constructed J.1.1
   routing together with the seven per-class mass multipliers — Chernoff `0`,
   clean-CNL `1`, DensePack `3`, the joint Tower+Return+Run TRT bound `2+4+5`, and
   the old-residual class `6`) plus the **L.6.5 old-residual smallness**
   `oldResMass ≤ cQ·cStarSmall·X`.

No `sorry`, no `axiom`, no new analytic step is introduced.  `erdos260_reduced`
is axiom-clean modulo the three standard Mathlib logical axioms
(`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace Erdos260

noncomputable section

/--
**Per-shell charge-bridge witness (the v5 routing + L.6.5 atom).**

For a single failing dyadic shell with its phase data `phases` and carry data
`carryData`, this bundles the two genuinely-residual pieces of the central charge
bridge:

* `routingCharge` — the J.1.1 first-obstruction seven-class priority routing
  (`CarryPriorityRoutingCharge`), which discharges the augmented bridge
  `highExcessMass ≤ ClosurePhaseMass + oldResMass`.  Its routing is constructed
  from the obstruction profile; its five per-class mass multipliers (Chernoff,
  clean-CNL, DensePack, the joint Tower+Return+Run TRT bound, and the old-residual
  class) are the deep L.2 / N.3.3 / N.24 / L.6.4 family-dynamics inputs.
* `oldRes_le` — the Lemma L.6.5 old-residual smallness `oldResMass ≤ C_Q·c_*·X`,
  the density-sensitive endpoint-count estimate that keeps the extra `+OldRes`
  term of recurrence I.11' below the pressure floor.
-/
structure ShellRoutedChargeAtom
    {shell : FailingDyadicShell}
    (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
    (cQ cStarSmall : ℝ) where
  /-- The v5 branch-level old-residual mass `OldRes_{s,j}(Y)` (Lemma L.6.4). -/
  oldResMass : ℝ
  /-- The J.1.1 seven-class priority routing with its per-class mass bounds. -/
  routingCharge : CarryPriorityRoutingCharge phases carryData oldResMass
  /-- **Lemma L.6.5** — the old-residual mass is density-small: `OldRes ≤ C_Q·c_*·X`. -/
  oldRes_le : oldResMass ≤ cQ * cStarSmall * (shell.X : ℝ)

/--
**The minimal residual atoms for Erdős #260 (v5).**

A single structure enumerating exactly the atomic hypotheses on which the
capstone theorem `erdos260_reduced` is conditional.  Inhabiting this structure is
precisely the remaining distance to an unconditional proof; every other step of
the v5 reduction chain is discharged in `erdos260_reduced` with no new analytic
content.
-/
structure Erdos260ResidualAtoms where
  /-- The L.6.5 product constant `C_Q = (Cres·Y)(Csupp·Ij)` (linear in the active
  floor, never an absolute constant — the K.1.2-consistent multiplier). -/
  cQ : ℝ
  /-- The failure density constant `c_*` (chosen last in the constant order). -/
  cStarSmall : ℝ
  /-- **The final constant condition** `cStar·ξ + C_Q·c_* < cPr` (the v5 analog of
  the old `cStar·ξ < cPr`, now absorbing the old-residual constant). -/
  constantCondition :
    erdos260Constants.cStar * erdos260Constants.ξ + cQ * cStarSmall
      < erdos260Constants.cPr
  /-- Per-failure carry data (Lemma 21.1 pressure side). -/
  carryData :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ -> shell.aboveCarryThreshold ->
        CarryDataFromFailure shell erdos260Constants.cPr
  /-- Per-failure Chernoff high-cost path data (carries its 22.1 budget). -/
  chernoff :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- Per-failure clean-CNL cluster encoding data (carries its G.6 Kraft budget). -/
  cnl :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- Per-failure DensePack factory data (carries its I.4.1/K.1.3 budget). -/
  densePack :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- Per-failure transient-tower factory data (carries its I.3.1 budget). -/
  tower :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- Per-failure return-package factory data (carries its I.5.1 budget). -/
  returnPkg :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- Per-failure run-package factory data (carries its I.5.2 budget). -/
  run :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        RunFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- **Phase-mass nonnegativity (manuscript §I / J.1.1 charging).** The per-shell
  Return and Run phase masses are physically nonnegative.  This honest manuscript fact
  discharges the charge atom's TRT-nonnegativity domain restriction `phases.trtNonneg`
  for the genuine phase data built from `returnPkg`/`run`. -/
  returnRunMassNonneg :
    ∀ (shell : FailingDyadicShell) (hcQ : shell.cQ = erdos260Constants.cQ),
      0 ≤ (returnPkg shell hcQ).massSum + (run shell hcQ).runMass
  /-- The per-shell charge-bridge atom: the J.1.1 routing + per-class mass bounds
  (`CarryPriorityRoutingCharge`) and the L.6.5 old-residual smallness.  **Restricted to
  TRT-nonnegative phase data** (`phases.trtNonneg`): the atom's `hTRT` bound forces
  `0 ≤ termTower+termReturn+termRun`, so it is uninhabitable for negative-mass phases;
  the restriction excludes exactly those physically-meaningless configurations. -/
  charge :
    ∀ (shell : FailingDyadicShell)
      (_hcQ : shell.cQ = erdos260Constants.cQ)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
      (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
      (_hphases : phases.trtNonneg),
        ShellRoutedChargeAtom phases carryData cQ cStarSmall

/--
**The charge-bridge provider built from the residual atoms.**

For every failing dyadic shell, the seven-class routing atom and the L.6.5
smallness atom feed the v5 contradiction engine `refutes_failingShell`, deriving
`False` (the failing shell cannot exist), whence the central charge bridge
`HighExcessChargeData` holds vacuously.  This is the faithful charge-bridge-layer
encoding of "no low-density shell exists".
-/
def Erdos260ResidualAtoms.highExcessCharge
    (atoms : Erdos260ResidualAtoms)
    (shell : FailingDyadicShell)
    (hcQ : shell.cQ = erdos260Constants.cQ)
    (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
    (hphases : phases.trtNonneg) :
    HighExcessChargeData phases carryData :=
  let w := atoms.charge shell hcQ phases carryData hphases
  (RoutedHighExcessChargeDataOldRes.refutes_failingShell
      w.routingCharge.toRoutedHighExcessChargeDataOldRes
      (le_of_lt erdos260Constants.cPr_pos)
      w.oldRes_le
      atoms.constantCondition).elim

/--
**Assemble the residual atoms into the eight-provider core interface.**

The seven phase/carry providers are forwarded unchanged; the eighth (the deepest)
provider `highExcessCharge` is the one built above from the charge-bridge atoms.
-/
def Erdos260ResidualAtoms.toGlobalAssemblyCoreInputs
    (atoms : Erdos260ResidualAtoms) :
    GlobalAssemblyCoreInputs where
  carryData := atoms.carryData
  chernoff := atoms.chernoff
  cnl := atoms.cnl
  densePack := atoms.densePack
  tower := atoms.tower
  returnPkg := atoms.returnPkg
  run := atoms.run
  returnRunMassNonneg := atoms.returnRunMassNonneg
  highExcessCharge := fun shell hcQ phases carryData hphases =>
    atoms.highExcessCharge shell hcQ phases carryData hphases

/--
**Erdős #260 reduced to the minimal residual atoms (the capstone).**

From `Erdos260ResidualAtoms` — the explicit, minimal list of still-assumed atomic
hypotheses — the manuscript conclusion `Erdos260Statement` follows: every
strictly-increasing integer exponent sequence with superlinear growth produces an
irrational weighted binary series.

The proof runs the v5 seven-class routing through `refutes_failingShell` to build
the central charge bridge, then composes the existing conditional endpoint
`erdos260Statement_of_globalAssemblyCoreInputs`.  No `sorry`, no `axiom`, no new
analytic content; this theorem is **conditional on `Erdos260ResidualAtoms`** and
makes the exact remaining distance to unconditional machine-checked.
-/
theorem erdos260_reduced (atoms : Erdos260ResidualAtoms) : Erdos260Statement :=
  erdos260Statement_of_globalAssemblyCoreInputs atoms.toGlobalAssemblyCoreInputs

/-! ## Tightened minimal atoms

Five sibling modules now PROVE or REDUCE several residual atoms.  We wire in the
two that admit a *clean provider-level discharge*, shrinking the hypothesis list:

* **constant condition (Target 3, `ResidualScalarBudgets`)** — the v5 closure
  condition `cStar·ξ + C_Q·c_* < cPr` is no longer a hypothesis.  At the pinned
  failure density `c_* = manuscriptCstarSmall = κ·ξ/64` and the conservative
  cluster constant `C_Q = 1`, `manuscript_closure_pressure` proves it outright.
* **Tower provider (`TowerLandingConstruction`)** — the deep `TowerTransientFactoryData`
  provider is replaced by the **affine-law slope atom** `TowerSlopeAtom`
  (`Q, H` with `H` an odd AP modulus `≥ 2`).  `oddPartFibreDynamics` builds a
  genuine `CarryFibreDynamics` (finiteness + E.13 closure *proved*, no assumed
  finiteness) on the odd part of `Q·H`, and `towerFamilyOfDynamics /
  toTowerTransientFactoryData` produce the budget-respecting factory datum.

The remaining sibling reductions are kept as *finer evidence* but cannot be
wired to a whole-provider discharge here without enlarging constants or missing
constructors (reported honestly):

* **CNL (`CNLFibreBound`)** — the clean Kraft bound is unconditional, but in the
  shape `cleanCNLKraftSum … ≤ (Fintype.card CNLTransition)·C_Q^M`.  The provider
  field `CNLClusterEncodingData.kraftSum_le` demands `≤ C_Q^M` with no `O(1)`
  prefactor, so the model-card constant cannot be folded into `C_Q^M` without an
  `M`-dependent enlargement of `C_Q` — the constant-compatibility caveat.  The
  `cnl` provider therefore stays an atom (now known to be backed, up to that
  `O(1)` factor, by `CNLFibreBound`).
* **Run (`RunObstructionRealization`)** — discharges the L.4.2 half-decrease and
  the realization fields of `MeanLowRunWindow`, but there is no clean constructor
  `RunObstruction → RunFactoryData` (the provider is the higher L.4 package).  The
  `run` provider stays an atom.
* **geomDetect (`GeomMarkerCoverage`)** — `pkg_marked ⟺ pkg_exposes`, reducing the
  routing's coverage primitive to the single geometric fact `pkg_exposes`.  This
  lives *inside* the routing of the `charge` atom (whose deep per-class mass
  multipliers remain); the `charge` atom stays as is.
-/

/--
**Tower landing residual reduced to the affine-law (slope `= K/q`) data.**

The bounded-denominator slope modulus of the manuscript E.5–E.13 carry recurrence:
a target denominator `Q ≠ 0` and an AP slope modulus `H` that is odd and `≥ 2`
(oddness is itself the proved `apModulus_odd`; `H ∣ 2^a − 1`).  This is the *only*
Tower input that remains after `TowerLandingConstruction` discharges finiteness,
E.13 closure, the recurrent cycle (Theorem E.6), and the Tower budget.
-/
structure TowerSlopeAtom where
  /-- Target denominator (the rational `η = P/Q` denominator); no parity needed. -/
  Q : ℕ
  /-- AP slope modulus `H = lcm(h_Γ, h_Δ)`, odd by `apModulus_odd`. -/
  H : ℕ
  /-- `Q ≠ 0`. -/
  hQ : Q ≠ 0
  /-- `H` is odd (proved in general via `apModulus_odd`). -/
  hH : Odd H
  /-- `H ≥ 2` (a nontrivial cycle). -/
  hH2 : 2 ≤ H

/--
**Tower transient factory data, constructed from the affine-law slope atom.**

`oddPartFibreDynamics` turns the slope atom into a genuine `CarryFibreDynamics` on
the odd part of `Q·H` (finite by construction, E.13-closed), and the proved
`towerFamilyOfDynamics`/`toTowerTransientFactoryData` chain yields the
budget-respecting Phase-7 tower datum.  The budget positivity
`0 ≤ cStar·ξ·X/6` is discharged from the pinned constants' positivity.
-/
def towerOfSlope (a : TowerSlopeAtom) {X : ℝ} (hX : 0 ≤ X) :
    TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ X :=
  (towerFamilyOfDynamics (cStar := erdos260Constants.cStar) (xi := erdos260Constants.ξ)
      (X := X) (oddPartFibreDynamics a.Q a.H a.hQ a.hH a.hH2)
      (div_nonneg
        (mul_nonneg
          (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le) hX)
        (by norm_num))).toTowerTransientFactoryData

/--
**The tightened minimal residual atoms for Erdős #260 (v5).**

`Erdos260ResidualAtoms` with the discharged atoms removed:

* the constant condition `cStar·ξ + C_Q·c_* < cPr` is GONE (proved, pinned);
* the Tower provider is replaced by the affine-law `towerSlope` atom.

The remaining fields are the genuinely-irreducible inputs (see the section
doc-comment for the honest CNL/Run/geom status).
-/
structure Erdos260MinimalAtoms where
  /-- Per-failure carry data (Lemma 21.1 pressure side). -/
  carryData :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ -> shell.aboveCarryThreshold ->
        CarryDataFromFailure shell erdos260Constants.cPr
  /-- Per-failure Chernoff high-cost path data (carries its 22.1 budget). -/
  chernoff :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- Per-failure clean-CNL cluster encoding data.  Its Kraft sub-bound is now
  backed by `CNLFibreBound` up to the `O(1)` model-card constant (caveat above). -/
  cnl :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- Per-failure DensePack factory data (carries its I.4.1/K.1.3 budget). -/
  densePack :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- **Tower (REDUCED)** — only the affine-law slope modulus `(Q, H)` remains;
  the factory datum is built by `towerOfSlope` via `TowerLandingConstruction`. -/
  towerSlope :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ -> TowerSlopeAtom
  /-- Per-failure return-package factory data (carries its I.5.1 budget). -/
  returnPkg :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- Per-failure run-package factory data.  Its L.4.2 half-decrease + realization
  fields are backed by `RunObstructionRealization` (no provider constructor; caveat). -/
  run :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        RunFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- **Phase-mass nonnegativity (manuscript §I / J.1.1 charging).** The per-shell
  Return and Run phase masses are physically nonnegative; discharges the charge atom's
  `phases.trtNonneg` domain restriction for the genuine phase data. -/
  returnRunMassNonneg :
    ∀ (shell : FailingDyadicShell) (hcQ : shell.cQ = erdos260Constants.cQ),
      0 ≤ (returnPkg shell hcQ).massSum + (run shell hcQ).runMass
  /-- The per-shell charge atom, with the constants pinned to the proved values
  `C_Q = 1`, `c_* = manuscriptCstarSmall`: the J.1.1 routing (whose coverage is
  `GeomMarkerCoverage`'s `pkg_exposes`) + the per-class mass multipliers + the
  L.6.5 smallness `oldResMass ≤ manuscriptCstarSmall · X`.  **Restricted to TRT-nonnegative
  phase data** (`phases.trtNonneg`): the atom is uninhabitable for negative-mass phases,
  so the restriction excludes exactly the physically-meaningless configurations. -/
  charge :
    ∀ (shell : FailingDyadicShell)
      (_hcQ : shell.cQ = erdos260Constants.cQ)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
      (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
      (_hphases : phases.trtNonneg),
        ShellRoutedChargeAtom phases carryData 1 manuscriptCstarSmall

/--
**Expand the tightened minimal atoms back into the residual atoms.**

The constant condition is discharged by `manuscript_closure_pressure` (Target 3),
and the Tower provider is reconstructed from the affine-law slope atom by
`towerOfSlope`.  Every other field is forwarded.
-/
def Erdos260MinimalAtoms.toResidualAtoms (m : Erdos260MinimalAtoms) :
    Erdos260ResidualAtoms where
  cQ := 1
  cStarSmall := manuscriptCstarSmall
  constantCondition := manuscript_closure_pressure
  carryData := m.carryData
  chernoff := m.chernoff
  cnl := m.cnl
  densePack := m.densePack
  tower := fun shell hcQ => towerOfSlope (m.towerSlope shell hcQ) shell.X_nonneg_real
  returnPkg := m.returnPkg
  run := m.run
  returnRunMassNonneg := m.returnRunMassNonneg
  charge := m.charge

/--
**Erdős #260 reduced to the tightened minimal residual atoms (the capstone).**

Identical conclusion to `erdos260_reduced`, but conditional on the *smaller*
`Erdos260MinimalAtoms`: the v5 constant condition has been discharged at the
pinned constants, and the Tower provider has been reduced to its affine-law slope
core.  Proved by expanding to `Erdos260ResidualAtoms` and reusing `erdos260_reduced`.

**Honest scope.** This is conditional, NOT unconditional.  The genuinely
irreducible residual is: the carry/Chernoff/CNL/DensePack/Return/Run per-shell
factory data, the affine-law Tower slope `(Q,H)`, and the per-shell charge atom
(the J.1.1 per-class mass multipliers + the L.6.5 smallness).  See the section
doc-comment for the CNL `O(1)`-constant caveat and the Run/geom status.
-/
theorem erdos260_reduced_minimal (m : Erdos260MinimalAtoms) : Erdos260Statement :=
  erdos260_reduced m.toResidualAtoms

end

end Erdos260
