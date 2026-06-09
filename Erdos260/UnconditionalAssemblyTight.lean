import Erdos260.UnconditionalAssembly
import Erdos260.CNLConstantCompat
import Erdos260.TowerSlopeAffineLaw
import Erdos260.RunFactoryConstructor
import Erdos260.ChargeMultiplierClosure

/-!
# Re-tightened capstone: consolidating the four new leaf reductions

`UnconditionalAssembly.lean` reduced Erdős #260 to `Erdos260MinimalAtoms` and proved
`erdos260_reduced_minimal : Erdos260MinimalAtoms → Erdos260Statement`.  Four sibling
modules have since PROVED or REDUCED several of those atoms.  This file (NEW; it edits
no existing file) consolidates them into a further-tightened structure
`Erdos260MinimalAtoms'` and the top theorem `erdos260_reduced_minimal'`.

## Why a new downstream file (not an edit of `UnconditionalAssembly.lean`)

Two of the four new modules **import** `UnconditionalAssembly`:
`TowerSlopeAffineLaw` consumes `TowerSlopeAtom`/`towerOfSlope`, and
`ChargeMultiplierClosure` consumes `ShellRoutedChargeAtom`.  Using their decls
(`towerSlopeAtomOfAPModuli`, `CarryPriorityRoutingCharge.ofGeomFibre`) from inside
`UnconditionalAssembly` would be a **circular import**.  Consolidating downstream,
where all four modules are available, is the only cycle-free way to wire them in.
`erdos260_reduced_minimal'` reuses the existing `erdos260_reduced_minimal` plumbing
verbatim (via `Erdos260MinimalAtoms'.toMinimalAtoms`).

## What was genuinely discharged this round (honest)

* **CNL Kraft sub-field — CLOSED.**  `CNLConstantCompat.cnlProvider_ofUnconditional`
  inhabits the `cnl` provider from per-shell `CNLUnconditionalKraftInput`, whose
  `kraftSum_le` is *derived* from the unconditional `CNLFibreBound` bound (the `O(1)`
  prefactor folded into the free field `CQ := (B·C_Q₀^M)^(1/M)`).  **Caveat:** the
  `cnl` atom is *not* fully closed — the per-shell faithful bridge labelling
  (`hE`/`hwin`/`hpos`), the additive BND height `hheight`, and the shell-budget
  calibration `hbudget` remain genuine per-shell inputs.
* **Tower `Odd H` — ELIMINATED.**  `TowerSlopeAffineLaw.towerSlopeAtomOfAPModuli`
  builds the `TowerSlopeAtom` from AP-modulus data `(Q, h₁, h₂, a, b)` with `Odd H`
  now a *theorem* (`apModulus_odd`), via the unconditional 2-adic descent
  `carryCycle_den_odd`.  Residual = the per-shell AP-modulus parametrization.

## What is REDUCED but still per-shell (honest)

* **Run — REDUCED.**  `RunFactoryConstructor.runFactoryDataOfScale` builds the `run`
  provider from the single §25.2 scale `4·q₀ ≤ m·ord_{q₀}(2)` (the L.4.2 half-decrease
  is now embedded, not assumed) plus the L.4.1 routing and per-shell budget.  Residual
  = the per-shell `(q₀,a,m)` provenance + routing + budget.
* **charge — REDUCED to `pkg_exposes` + per-shell data.**
  `ChargeMultiplierClosure.ofGeomFibre` builds the routing charge from the geometric
  routing `G.toRouting config` (coverage primitive = `pkg_exposes`) and the per-fibre
  count×multiplier / N.3.1-compression data.  **Honest finding (that worker):** 0/7
  per-class multipliers follow from the proved phase budgets (budgets bound the phase
  TERM; multipliers bound routed carry MASS — orthogonal J.1.1/N.24/I.9 charging), and
  `pkg_exposes` is genuinely IRREDUCIBLE.

## Genuinely irreducible after this round

`pkg_exposes` (the geometric primitive that a PKG verdict exposes a real charge class);
the per-shell carry data incl. the Lemma 21.1 pressure floor; the per-shell charge
count/pointwise/routing data (the J.1.1/N.24 charging); the Tower AP-modulus
parametrization; the Run `(q₀,a,m)` provenance; and the Chernoff/DensePack/Return
per-shell factory data (untouched this round).

No `sorry`, `axiom`, or `admit`.  `#print axioms erdos260_reduced_minimal'` is the
three standard logical axioms only.
-/

namespace Erdos260

noncomputable section

/-! ## 1. Tower: the AP-modulus datum (replacing the `Odd H` assumption) -/

/--
**Per-shell Tower AP-modulus datum (manuscript E.2–E.5).**

The genuinely geometric residual after `TowerSlopeAffineLaw`: a nonzero target
denominator `Q`, two AP step moduli `h₁ ∣ 2^a − 1`, `h₂ ∣ 2^b − 1` (the manuscript
`h_Γ ∣ D_Γ = 2^{S_Γ} − 1`), and the cycle nontriviality `2 ≤ lcm h₁ h₂`.  The
oddness of the slope modulus `H = lcm h₁ h₂` is **no longer assumed** — it is the
theorem `apModulus_odd`, fired inside `towerSlopeAtomOfAPModuli`.
-/
structure TowerAPModuli where
  Q : ℕ
  h₁ : ℕ
  h₂ : ℕ
  a : ℕ
  b : ℕ
  hQ : Q ≠ 0
  ha : 1 ≤ a
  hb : 1 ≤ b
  hd₁ : h₁ ∣ 2 ^ a - 1
  hd₂ : h₂ ∣ 2 ^ b - 1
  hH2 : 2 ≤ Nat.lcm h₁ h₂

/-- Build the `TowerSlopeAtom` from the AP-modulus datum, with `Odd H` proved. -/
def TowerAPModuli.toSlopeAtom (d : TowerAPModuli) : TowerSlopeAtom :=
  towerSlopeAtomOfAPModuli d.Q d.h₁ d.h₂ d.a d.b d.hQ d.ha d.hb d.hd₁ d.hd₂ d.hH2

/-! ## 2. Run: the §25.2 scale datum (embedding the proved half-decrease) -/

/--
**Per-shell Run scale datum (manuscript §25.2 + L.4.1/L.4.2).**

The reduced Run input after `RunFactoryConstructor`: the §25.2 reduced data
(`q₀ > 1` odd, `a` coprime) and the *single* scale `4·q₀ ≤ m·ord_{q₀}(2)` — the sole
input to the now-PROVED one-step half-decrease and the four geometric realization
fields — together with the genuinely shell-dependent analytic data `RunFactoryData`
is about: the L.4.1 routing `D : RunRoutingData α` and the per-shell budget
(`chain_capture`, `chainRoot_le`, `hSmall`).
-/
structure RunScaleData (X : ℝ) where
  α : Type
  q0 : ℕ
  a : ℕ
  m : ℕ
  hq0 : 1 < q0
  hodd : Odd q0
  hcop : Nat.Coprime a q0
  hm : 0 < m
  hscale : 4 * q0 ≤ m * orderOf (2 : ZMod q0)
  u : ℕ
  weight : ℝ
  D : RunRoutingData α
  len : ℕ
  hlen : 1 ≤ len
  smallError : ℝ
  hsmall_nonneg : 0 ≤ smallError
  twoNegcY : ℝ
  Ij : ℝ
  chain_capture : D.toTri.chainMass ≤ ((m * orderOf (2 : ZMod q0) : ℕ) : ℝ)
  chainRoot_le : 2 * ((m * orderOf (2 : ZMod q0) : ℕ) : ℝ) ≤ X * Ij * twoNegcY
  hSmall :
    D.towerBound + D.returnBound + D.densePackBound + X * Ij * twoNegcY + smallError
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * X / 6

/-- Build the `RunFactoryData` from the scale datum, with the §25.2 half-decrease
embedded by `runFactoryDataOfScale`. -/
def RunScaleData.build {X : ℝ} (d : RunScaleData X) :
    RunFactoryData erdos260Constants.cStar erdos260Constants.ξ X :=
  runFactoryDataOfScale d.hq0 d.hodd d.hcop d.hm d.hscale d.u d.weight d.D d.len d.hlen
    d.smallError d.hsmall_nonneg d.twoNegcY d.Ij d.chain_capture d.chainRoot_le d.hSmall

/-! ## 3. Charge: the geometric-routing fibre datum (coverage = `pkg_exposes`) -/

/--
**Per-shell charge geometric-fibre datum (manuscript J.1.1 + N.24 + L.6.5).**

The reduced charge input after `ChargeMultiplierClosure`: a `CNLObstructionGeometry`
`G` (whose coverage primitive is the irreducible `pkg_exposes`) and a `config`, the
per-fibre count×multiplier data for the separable classes `0,1,3,6` (a per-fibre
window-excess bound — the K.1.2/L.20 residual multiplier linear in `Y` — a fibre
count, and the identification `count·mult ≤ termX`), the Lemma N.3.1 compression data
for the joint `2+4+5` class, and the Lemma L.6.5 old-residual smallness.  The five
per-class multipliers are derived from this data by `ofGeomFibre`; none is *closed*
(no multiplier follows from a proved phase budget).
-/
structure ShellChargeGeomFibreInput
    {shell : FailingDyadicShell}
    (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell erdos260Constants.cPr) where
  /-- The v5 branch-level old-residual mass `OldRes_{s,j}(Y)` (Lemma L.6.4). -/
  oldResMass : ℝ
  /-- The obstruction geometry — its `pkg_exposes` field is the irreducible coverage
  primitive (`GeomMarkerCoverage`: `pkg_marked ⟺ pkg_exposes`). -/
  G : CNLObstructionGeometry
  /-- The per-start lift-state configuration. -/
  config : ℕ → LiftState
  -- Class 0 (Chernoff) count×multiplier data.
  multChernoff : ℝ
  countChernoff : ℝ
  hpoint0 : ∀ k ∈ routedFibre carryData (G.toRouting config).classify 0,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ multChernoff
  hnn0 : 0 ≤ multChernoff
  hcard0 : ((routedFibre carryData (G.toRouting config).classify 0).card : ℝ) ≤ countChernoff
  hbud0 : countChernoff * multChernoff ≤ termChernoff phases.toClosurePhaseData
  -- Class 1 (clean-CNL) count×multiplier data.
  multCnl : ℝ
  countCnl : ℝ
  hpoint1 : ∀ k ∈ routedFibre carryData (G.toRouting config).classify 1,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ multCnl
  hnn1 : 0 ≤ multCnl
  hcard1 : ((routedFibre carryData (G.toRouting config).classify 1).card : ℝ) ≤ countCnl
  hbud1 : countCnl * multCnl ≤ termCnl phases.toClosurePhaseData
  -- Class 3 (DensePack) count×multiplier data.
  multDP : ℝ
  countDP : ℝ
  hpoint3 : ∀ k ∈ routedFibre carryData (G.toRouting config).classify 3,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ multDP
  hnn3 : 0 ≤ multDP
  hcard3 : ((routedFibre carryData (G.toRouting config).classify 3).card : ℝ) ≤ countDP
  hbud3 : countDP * multDP ≤ termDensePack phases.toClosurePhaseData
  -- Classes 2+4+5 (joint Tower+Return+Run) via the proved Lemma N.3.1 compression.
  β : Type
  σ : Type
  [decσ : DecidableEq σ]
  comp : AppendixN.TerminalOutputData β σ
  hRouteToOutput :
    routedClassMassOf carryData (G.toRouting config).classify 2
        + routedClassMassOf carryData (G.toRouting config).classify 4
        + routedClassMassOf carryData (G.toRouting config).classify 5
      ≤ ∑ b ∈ comp.branches, comp.wtO b
  hAbsorb :
    comp.CQ * (comp.YO * ∑ ζ ∈ comp.ground, comp.fibreMass ζ)
      ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
          + termRun phases.toClosurePhaseData
  -- Class 6 (old-residual) count×multiplier data.
  multOR : ℝ
  countOR : ℝ
  hpoint6 : ∀ k ∈ routedFibre carryData (G.toRouting config).classify 6,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ multOR
  hnn6 : 0 ≤ multOR
  hcard6 : ((routedFibre carryData (G.toRouting config).classify 6).card : ℝ) ≤ countOR
  hbud6 : countOR * multOR ≤ oldResMass
  /-- **Lemma L.6.5** — the old-residual mass is density-small `OldRes ≤ 1·c_*·X`. -/
  hsmall : oldResMass ≤ 1 * manuscriptCstarSmall * (shell.X : ℝ)

/-- Build the `ShellRoutedChargeAtom` from the geometric-fibre datum: the routing is
`G.toRouting config` (coverage = `pkg_exposes`), the five multipliers are derived by
`ofGeomFibre`, and the L.6.5 smallness wraps it via `ofRoutingCharge`. -/
def ShellChargeGeomFibreInput.build
    {shell : FailingDyadicShell}
    {phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell erdos260Constants.cPr}
    (inp : ShellChargeGeomFibreInput phases carryData) :
    ShellRoutedChargeAtom phases carryData 1 manuscriptCstarSmall :=
  letI := inp.decσ
  ShellRoutedChargeAtom.ofRoutingCharge
    (CarryPriorityRoutingCharge.ofGeomFibre phases carryData inp.G inp.config
      inp.hpoint0 inp.hnn0 inp.hcard0 inp.hbud0
      inp.hpoint1 inp.hnn1 inp.hcard1 inp.hbud1
      inp.hpoint3 inp.hnn3 inp.hcard3 inp.hbud3
      inp.comp inp.hRouteToOutput inp.hAbsorb
      inp.hpoint6 inp.hnn6 inp.hcard6 inp.hbud6)
    inp.hsmall

/-! ## 4. The re-tightened minimal atoms -/

/--
**The re-tightened minimal residual atoms for Erdős #260 (v5, round 2).**

`Erdos260MinimalAtoms` with four fields replaced by their smaller, sibling-proved
inputs:

* `cnlInput` (was `cnl`) — per-shell `CNLUnconditionalKraftInput`; the Kraft
  sub-obligation is *derived* (CNL Kraft sub-field CLOSED);
* `towerAP` (was `towerSlope`) — per-shell `TowerAPModuli`; `Odd H` ELIMINATED;
* `runScale` (was `run`) — per-shell `RunScaleData`; the L.4.2 half-decrease embedded;
* `chargeGeom` (was `charge`) — per-shell `ShellChargeGeomFibreInput`; routing
  coverage reduced to `pkg_exposes` + fibre data.

The untouched fields `carryData`, `chernoff`, `densePack`, `returnPkg` remain
genuinely per-shell factory data (not addressed this round).
-/
structure Erdos260MinimalAtoms' where
  /-- **IRREDUCIBLE** — per-failure carry data (Lemma 21.1 pressure floor). -/
  carryData :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        CarryDataFromFailure shell erdos260Constants.cPr
  /-- Per-failure Chernoff high-cost path data (untouched this round). -/
  chernoff :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- **REDUCED** — per-failure unconditional CNL Kraft input; `kraftSum_le` derived. -/
  cnlInput :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        CNLUnconditionalKraftInput erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : ℝ)
  /-- Per-failure DensePack factory data (untouched this round). -/
  densePack :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- **REDUCED** — per-failure Tower AP-modulus datum; `Odd H` now a theorem. -/
  towerAP :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → TowerAPModuli
  /-- Per-failure return-package factory data (untouched this round). -/
  returnPkg :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- **REDUCED** — per-failure Run §25.2 scale datum; half-decrease embedded. -/
  runScale :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → RunScaleData (shell.X : ℝ)
  /-- **Phase-mass nonnegativity (manuscript §I / J.1.1 charging).** The per-shell Return
  and Run phase masses are physically nonnegative; discharges the `phases.trtNonneg`
  restriction of `chargeGeom` for the genuine phase data built from `returnPkg`/`runScale`. -/
  returnRunMassNonneg :
    ∀ (shell : FailingDyadicShell) (hcQ : shell.cQ = erdos260Constants.cQ),
      0 ≤ (returnPkg shell hcQ).massSum + ((runScale shell hcQ).build).runMass
  /-- **REDUCED** — per-failure charge geometric-fibre datum; coverage = `pkg_exposes`.
  **Restricted to TRT-nonnegative phase data** (`phases.trtNonneg`). -/
  chargeGeom :
    ∀ (shell : FailingDyadicShell)
      (_hcQ : shell.cQ = erdos260Constants.cQ)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
      (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
      (_hphases : phases.trtNonneg),
        ShellChargeGeomFibreInput phases carryData

/--
**Expand the re-tightened atoms back into `Erdos260MinimalAtoms`.**

The four reduced fields are run through their sibling-proved builders
(`cnlProvider_ofUnconditional`, `TowerAPModuli.toSlopeAtom`, `RunScaleData.build`,
`ShellChargeGeomFibreInput.build`); the four untouched fields are forwarded.
-/
def Erdos260MinimalAtoms'.toMinimalAtoms (m : Erdos260MinimalAtoms') :
    Erdos260MinimalAtoms where
  carryData := fun shell hcQ _hlarge => m.carryData shell hcQ
  chernoff := m.chernoff
  cnl := cnlProvider_ofUnconditional m.cnlInput
  densePack := m.densePack
  towerSlope := fun shell hcQ => (m.towerAP shell hcQ).toSlopeAtom
  returnPkg := m.returnPkg
  run := fun shell hcQ => (m.runScale shell hcQ).build
  returnRunMassNonneg := m.returnRunMassNonneg
  charge := fun shell hcQ phases carryData hphases =>
    (m.chargeGeom shell hcQ phases carryData hphases).build

/--
**Erdős #260 reduced to the re-tightened minimal residual atoms (the capstone, round 2).**

Identical conclusion to `erdos260_reduced` / `erdos260_reduced_minimal`, conditional on
the smaller `Erdos260MinimalAtoms'`: the CNL Kraft sub-field is discharged, the Tower
`Odd H` is eliminated, the Run half-decrease is embedded, and the charge routing's
coverage is reduced to `pkg_exposes`.  Proved by expanding to `Erdos260MinimalAtoms`
and reusing `erdos260_reduced_minimal`.

**Honest scope.** This is conditional, NOT unconditional.  The genuinely irreducible
residual is: the carry data (incl. the Lemma 21.1 pressure floor); the per-shell
Chernoff / DensePack / Return factory data and the per-shell CNL bridge/budget inputs;
the Tower AP-modulus parametrization; the Run `(q₀,a,m)` provenance; and the per-shell
charge fibre data with the irreducible geometric primitive `pkg_exposes`.
-/
theorem erdos260_reduced_minimal' (m : Erdos260MinimalAtoms') : Erdos260Statement :=
  erdos260_reduced_minimal m.toMinimalAtoms

end

end Erdos260
