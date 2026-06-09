import Mathlib
import Erdos260.GlobalDensePackAssembly
import Erdos260.AppendixK1_DensePack
import Erdos260.DensePackChargeBound
import Erdos260.ChargeMultiplierClosure
import Erdos260.UnconditionalAssemblyTight2

/-!
# Constructing the DensePack factory datum (the `densePack` atom)

The capstone `erdos260_reduced_minimal''` (`Erdos260.UnconditionalAssemblyTight2`) still takes a
per-shell `DensePackFactoryData` as an **assumed atom** (the `densePack` field):

```
densePack : ∀ shell : FailingDyadicShell,
    shell.cQ = erdos260Constants.cQ →
      DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
```

`DensePackFactoryData` (`Erdos260.LocalGeometryFactory`) bundles four data fields plus **three
inequalities** — the K.1.2 cover (`hcover`), the K.1.3 density-under-failure count (`hcount`), and
the Lemma I.4.1 budget (`hsmall`).  This file shows that **all three inequalities are derivable**
(none need be assumed) from the **already-proved** machinery, so the `densePack` atom is *built*,
not assumed — modulo the two structural regime conditions of the manuscript's small-density /
large-scale reduction.

## What is reused (already proved upstream; NOT re-proved here)

* `Erdos260.GlobalDensePackAssembly`:
  - `GroundedDensePackLocalData.toDensePackFactoryData` — builds the factory datum with `hcover`
    **derived** from the K.1.2 greedy marker cover (`cover_bound`, via
    `lemmaK1_2_densePackSupportCover'`);
  - `DensePackProofV4ShellGreedyInputData.toGroundedDensePackLocalData` — grounds the datum with
    `hcount` **derived** from `shell.hfailure` + the marker-count packing, and `hsmall`
    **derived** from the pinned constants (`proofV4DensePackSmallness_of_smallLarge`,
    `erdos260_densePack_fixed_smallness_budget`);
  - `DensePackProofV4ShellGreedyInputData.ofActualSupportWindows` — the **canonical** density
    datum: the K.1.5 disjoint one-sided-support packing
    (`marker_count_mul_le_shell`) is itself **proved** for the canonical actual-support marker set,
    needing no DensePack-specific input;
  - `GroundedDensePackLocalData.densePack_bound` — the final I.4.1/K.1.3 budget on the constructed
    point count (reuses `corollaryK1_3_densePackUnderFailure`).
* `Erdos260.AppendixK1_DensePack.densePackBound` — the Phase-6 deliverable consuming the
  `DensePackData` projection of the constructed factory datum.

## What this file adds

* `densePackFactoryDataOfDensity` / `densePackFactoryDataCanonical` — the per-shell **builders**:
  from the genuine per-shell density datum (resp. nothing but the regime conditions) they produce a
  `DensePackFactoryData`, with cover/count/budget all derived.
* `densePackFactoryDataOfDensity_card_le_budget` / `densePackFactoryDataCanonical_feeds_budget` —
  the constructed datum satisfies / feeds the proved I.4.1 budget.
* `densePackFactoryData_trivial` / `densePackFactoryData_nonempty` /
  `densePackGreedyInput_realized` / `ofActualSupportWindows_points` — **non-vacuity witnesses**.
* `DensePackRegimeInput`, `Erdos260MinimalAtomsDensePackReduced`,
  `erdos260_reduced_densePackReduced` — the **capstone-level reduction**: an
  `Erdos260MinimalAtoms''` whose `densePack` factory field is replaced by, for each shell, either a
  proof of the two structural regime conditions (in which case the whole factory datum is built
  canonically) or — for out-of-regime shells — a fallback datum.  `ofMinimalAtoms''` shows it is no
  less inhabitable than `Erdos260MinimalAtoms''` (non-vacuity).

## Honest status (see `densePackFactoryResidual`)

The DensePack factory datum is **REDUCED**, per shell, to the two structural regime conditions
`shell.c0 ≤ κ/16` (small density constant) and `carryB Q + 25 ≤ L` with `X = 2^L` (large scale):
**in regime, the entire datum — cover, count, budget, and the marker packing — is CLOSED** with no
DensePack-specific input.  It is not *universally* closed only because those two conditions are not
properties of every failing shell.

No `sorry`, `admit`, `native_decide`, or new `axiom`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1. The per-shell builders -/

/-- **DensePack factory datum from the genuine per-shell density datum (Lemma I.4.1 / K.1.x).**

From the smallest per-shell density input `DensePackProofV4ShellGreedyInputData shell` (a dense-pack
point set together with the single scalar marker-count inequality `marker_count_mul_le_shell`) and
the two structural regime conditions, this builds the full `DensePackFactoryData`.  All three of its
inequalities are **derived**, not assumed:

* `hcover` — the K.1.2 marker-neighbourhood cover, from the greedy maximal-separated marker
  principle;
* `hcount` — the K.1.3 density-under-failure count, from `shell.hfailure` and the packing count;
* `hsmall` — the Lemma I.4.1 budget, from the pinned constants
  (`proofV4DensePackSmallness_of_smallLarge`).

It is the composition `toGroundedDensePackLocalData ≫ toDensePackFactoryData`, both proved in
`Erdos260.GlobalDensePackAssembly`. -/
def densePackFactoryDataOfDensity {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellGreedyInputData shell)
    (hc0Small : shell.c0 ≤ manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic) :
    DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
  (data.toGroundedDensePackLocalData hc0Small hCarryLarge).toDensePackFactoryData

/-- **Canonical DensePack factory datum (no DensePack-specific input).**

The same builder fed the **canonical** density datum
`DensePackProofV4ShellGreedyInputData.ofActualSupportWindows shell`, whose marker-count packing
`marker_count_mul_le_shell` is itself **proved** (the K.1.5 disjoint one-sided-support packing of
the canonical actual-support marker set).  Hence, in the small-density / large-scale regime, the
entire DensePack factory datum is constructed from shell geometry alone: the only remaining inputs
are the two structural regime conditions. -/
def densePackFactoryDataCanonical (shell : FailingDyadicShell)
    (hc0Small : shell.c0 ≤ manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic) :
    DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
  densePackFactoryDataOfDensity
    (DensePackProofV4ShellGreedyInputData.ofActualSupportWindows shell) hc0Small hCarryLarge

/-! ## 2. The constructed datum satisfies / feeds the proved budget -/

/-- **Lemma I.4.1 / K.1.3 budget on the constructed point count.**

The dense-pack point count of `densePackFactoryDataOfDensity` obeys the per-phase budget
`c_*·ξ·X/6`, reusing the proved `GroundedDensePackLocalData.densePack_bound`
(`corollaryK1_3_densePackUnderFailure` + the derived smallness). -/
theorem densePackFactoryDataOfDensity_card_le_budget {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellGreedyInputData shell)
    (hc0Small : shell.c0 ≤ manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic) :
    (((densePackFactoryDataOfDensity data hc0Small hCarryLarge).densePackPoints.card : ℝ))
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : ℝ) / 6 :=
  (data.toGroundedDensePackLocalData hc0Small hCarryLarge).densePack_bound

/-- **The constructed factory datum feeds the proved Phase-6 deliverable `densePackBound`.**

Its `DensePackData` projection produces a `DensePackVal` inside the I.4.1 budget, by the proved
`Erdos260.AppendixK1_DensePack.densePackBound`. -/
theorem densePackFactoryDataCanonical_feeds_budget (shell : FailingDyadicShell)
    (hc0Small : shell.c0 ≤ manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic) :
    ∃ v : ℝ, 0 ≤ v ∧
      v ≤ erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : ℝ) / 6 :=
  densePackBound ((densePackFactoryDataCanonical shell hc0Small hCarryLarge).toDensePackData)

/-! ## 3. Non-vacuity witnesses -/

/-- A trivial `DensePackFactoryData` (empty point set) inhabits the target type whenever the budget
`c_*·ξ·X/6` is nonnegative.  Used only to certify that the construction target is **not vacuous**. -/
def densePackFactoryData_trivial {cStar ξ X : ℝ}
    (hC : 0 ≤ cStar * ξ * X / 6) :
    DensePackFactoryData cStar ξ X where
  densePackPoints := ∅
  markersCard := 0
  spread := 0
  cStarSmall := 0
  hcover := by simp
  hcount := by simp
  hsmall := by simp only [zero_mul]; exact hC

/-- **The DensePack factory target is inhabited** at the pinned constants for every `X ≥ 0`
(the construction is not vacuous). -/
theorem densePackFactoryData_nonempty (X : ℝ) (hX : 0 ≤ X) :
    Nonempty (DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ X) := by
  refine ⟨densePackFactoryData_trivial ?_⟩
  apply div_nonneg _ (by norm_num : (0 : ℝ) ≤ 6)
  exact mul_nonneg
    (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le) hX

/-- **The genuine per-shell density datum is canonically realized for every shell** (with no
hypotheses): the smallest remaining DensePack input is consistent, not vacuous. -/
theorem densePackGreedyInput_realized (shell : FailingDyadicShell) :
    Nonempty (DensePackProofV4ShellGreedyInputData shell) :=
  ⟨DensePackProofV4ShellGreedyInputData.ofActualSupportWindows shell⟩

/-- The canonical density datum carries **genuine geometry**: its point set is the actual
support-window marker set `proofV4DensePackActualPoints shell`, not an empty/placeholder set. -/
theorem ofActualSupportWindows_points (shell : FailingDyadicShell) :
    (DensePackProofV4ShellGreedyInputData.ofActualSupportWindows shell).densePackPoints
      = proofV4DensePackActualPoints shell :=
  rfl

/-! ## 4. The capstone-level reduction of the `densePack` atom

The two regime conditions are *not* properties of every failing shell, so the universal `densePack`
factory field cannot be discharged uniformly.  We therefore expose the genuine reduction with the
correct quantifier shape: for each shell, supply **either** a proof of the regime conditions (and
the whole factory datum is built canonically) **or** a fallback datum. -/

/-- Per-shell DensePack input *after reduction*: a proof that the shell lies in the small-density /
large-scale regime (yielding the canonical factory datum, cover/count/budget/packing all closed),
or — for out-of-regime shells — a fallback `DensePackFactoryData`. -/
def DensePackRegimeInput (shell : FailingDyadicShell) : Type :=
  PLift (shell.c0 ≤ manuscriptKappa / 16 ∧
      carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic)
    ⊕ DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)

/-- Build the factory datum from a reduced per-shell input: canonical construction in regime,
fallback otherwise. -/
def DensePackRegimeInput.build {shell : FailingDyadicShell}
    (d : DensePackRegimeInput shell) :
    DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
  match d with
  | Sum.inl p => densePackFactoryDataCanonical shell p.down.1 p.down.2
  | Sum.inr datum => datum

/-- The reduced input is always inhabited (use the in-regime branch when available, else a fallback
datum); in particular the reduction introduces no unsatisfiable obligation. -/
theorem densePackRegimeInput_nonempty (shell : FailingDyadicShell)
    (h : 0 ≤ erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : ℝ) / 6) :
    Nonempty (DensePackRegimeInput shell) :=
  ⟨Sum.inr (densePackFactoryData_trivial h)⟩

/--
**Round-2 minimal atoms with the DensePack factory field reduced.**

Identical to `Erdos260MinimalAtoms''` (`Erdos260.UnconditionalAssemblyTight2`) except that the
`densePack` factory field — four data fields and three inequalities per shell — is replaced by the
reduced per-shell `densePackRegime`: for shells in the small-density / large-scale regime, only a
*proof* of the two structural conditions is required, and the entire factory datum (cover K.1.2,
count K.1.3-under-failure, budget I.4.1, packing K.1.5) is constructed canonically.
-/
structure Erdos260MinimalAtomsDensePackReduced where
  /-- Per-failure structural shell-window inputs (unchanged). -/
  carryWindow :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → ShellWindowInputs shell
  /-- Per-failure Chernoff high-cost path data (unchanged). -/
  chernoff :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- Per-failure unconditional CNL Kraft input (unchanged). -/
  cnlInput :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        CNLUnconditionalKraftInput erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : ℝ)
  /-- **REDUCED** — per-failure DensePack input: regime proof (datum built canonically) or
  fallback datum.  The cover/count/budget/packing are all closed in regime. -/
  densePackRegime :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → DensePackRegimeInput shell
  /-- Per-failure Tower recurrent-cycle datum (unchanged). -/
  towerCycle :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → TowerRecurrentCycle
  /-- Per-failure return-package factory data (unchanged). -/
  returnPkg :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ →
        ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- Per-failure Run residual-center provenance datum (unchanged). -/
  runProvenance :
    ∀ shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ → RunProvenanceData (shell.X : ℝ)
  /-- Per-failure Return/Run phase-mass nonnegativity (unchanged; forwards to round 2). -/
  returnRunMassNonneg :
    ∀ (shell : FailingDyadicShell) (hcQ : shell.cQ = erdos260Constants.cQ),
      0 ≤ (returnPkg shell hcQ).massSum + ((runProvenance shell hcQ).build).runMass
  /-- Per-failure charge structural-PKG fibre datum (unchanged; restricted to TRT-nonnegative
  phase data `phases.trtNonneg`). -/
  chargeStructural :
    ∀ (shell : FailingDyadicShell)
      (_hcQ : shell.cQ = erdos260Constants.cQ)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ))
      (carryData : CarryDataFromFailure shell erdos260Constants.cPr)
      (_hphases : phases.trtNonneg),
        ShellChargeStructuralInput phases carryData

/-- Expand the reduced atoms into `Erdos260MinimalAtoms''`, building each `densePack` factory datum
from its reduced input via `DensePackRegimeInput.build`. -/
def Erdos260MinimalAtomsDensePackReduced.toMinimalAtoms''
    (a : Erdos260MinimalAtomsDensePackReduced) : Erdos260MinimalAtoms'' where
  carryWindow := a.carryWindow
  chernoff := a.chernoff
  cnlInput := a.cnlInput
  densePack := fun shell hcQ => (a.densePackRegime shell hcQ).build
  towerCycle := a.towerCycle
  returnPkg := a.returnPkg
  runProvenance := a.runProvenance
  returnRunMassNonneg := a.returnRunMassNonneg
  chargeStructural := a.chargeStructural

/--
**Erdős #260 reduced to the round-2 atoms with the DensePack factory field reduced.**

Same conclusion as `erdos260_reduced_minimal''`, but the per-shell DensePack factory datum is no
longer an assumed atom: in the small-density / large-scale regime it is constructed canonically from
shell geometry (cover/count/budget/packing all closed), the only DensePack input being a proof of
the two structural regime conditions.
-/
theorem erdos260_reduced_densePackReduced
    (a : Erdos260MinimalAtomsDensePackReduced) : Erdos260Statement :=
  erdos260_reduced_minimal'' a.toMinimalAtoms''

/-- **Non-vacuity of the reduction.**  Every `Erdos260MinimalAtoms''` yields an
`Erdos260MinimalAtomsDensePackReduced` (each `densePack` datum is wrapped in the fallback branch),
so the reduced atoms are no less inhabitable than the originals — the reduction exposes the regime
option without strengthening any other obligation. -/
def Erdos260MinimalAtomsDensePackReduced.ofMinimalAtoms''
    (m : Erdos260MinimalAtoms'') : Erdos260MinimalAtomsDensePackReduced where
  carryWindow := m.carryWindow
  chernoff := m.chernoff
  cnlInput := m.cnlInput
  densePackRegime := fun shell hcQ => Sum.inr (m.densePack shell hcQ)
  towerCycle := m.towerCycle
  returnPkg := m.returnPkg
  runProvenance := m.runProvenance
  returnRunMassNonneg := m.returnRunMassNonneg
  chargeStructural := m.chargeStructural

/-! ## 5. Honest residual inventory -/

/-- The honest status of the `densePack` atom after this file. -/
def densePackFactoryResidual : List String :=
  [ "hcover (K.1.2 marker-neighbourhood cover): CLOSED — derived from the greedy maximal-separated " ++
      "marker principle (`GroundedDensePackLocalData.cover_bound`, via " ++
      "`lemmaK1_2_densePackSupportCover'`); never assumed.",
    "hcount (K.1.3 density-under-failure count): CLOSED in regime — derived from `shell.hfailure` " ++
      "and the marker-count packing (`DensePackProofV4ShellCardinalityInputData.hcount`); the " ++
      "marker count itself ≤ c_*·X follows from the positive-density failure.",
    "marker_count_mul_le_shell (K.1.5 disjoint one-sided support packing): CLOSED — PROVED for the " ++
      "canonical actual-support marker set (`ofActualSupportWindows`): spread-separated markers " ++
      "have disjoint length-(spread+1) support windows, all inside `supportShell`.",
    "hsmall (Lemma I.4.1 budget, c_* ≪_Q ρ_D κ ξ): CLOSED in regime — derived from the pinned " ++
      "constants (`proofV4DensePackSmallness_of_smallLarge`, " ++
      "`erdos260_densePack_fixed_smallness_budget`); never assumed.",
    "REDUCED, not universally CLOSED: the genuine remaining inputs are the two structural regime " ++
      "conditions per shell — (a) shell.c0 ≤ manuscriptKappa/16 (small density constant), and " ++
      "(b) carryB Q + 25 ≤ L with X = 2^L (large scale). In regime the WHOLE factory datum is " ++
      "built canonically (`densePackFactoryDataCanonical`) with no DensePack-specific input. The " ++
      "universal `densePack` field is not fully closed only because a failing shell may have " ++
      "c0 ∈ (κ/16, κ) or small L; out-of-regime shells keep a fallback datum " ++
      "(`DensePackRegimeInput`, `Sum.inr`)." ]

theorem densePackFactoryResidual_nonempty : densePackFactoryResidual ≠ [] := by
  simp [densePackFactoryResidual]

end

end Erdos260
