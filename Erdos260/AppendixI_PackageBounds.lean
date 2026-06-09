import Mathlib
import Erdos260.AppendixI
import Erdos260.AppendixK1_DensePack
import Erdos260.AppendixI_PhaseMass
import Erdos260.ClosureFactory
import Erdos260.DensePack
import Erdos260.StoppedInduction
import Erdos260.CNLEntropy
import Erdos260.Return

/-!
# Appendix I package bounds: grounding the six per-phase comparisons

`Erdos260.absorbed_window_le_phaseMass_classes` (in `AppendixI_PhaseMass.lean`)
proves the central charge bridge `absorbedBound + windowBound ≤ ClosurePhaseMass`
from the N.3.3 five-class absorption, the N.2.2 window drop, and **six per-phase
comparisons** `𝔒_X ≤ term_X data` (one absorbed-class mass dominated by each of the
six `ClosurePhaseMass` terms).  In the abstract bridge those six comparisons are
opaque hypotheses.

This module **grounds** them in the faithful package lemmas, in two complementary
directions.

## What is faithful here

### A. Per-term manuscript budget bounds (`term_X data ≤ cStar · ξ · X / 6`)

Each of the six phase-mass terms is shown to fit the manuscript per-phase budget
`cStar · ξ · X / 6`, re-deriving the package estimate **directly on the
`ClosurePhaseMass` term** (the existing `chernoffPathSpace` / `cnlEntropy` /
`towerPackageBound` / `densePackBound` / `nonRunReturnBound` / `runBound`
lemmas expose either through a witness theorem or, for Return/Run, directly on
the concrete mass term):

* `termChernoff_le_budget` — Lemma 22.1 (`shellChernoff_bound_of_moment_bound`);
* `termCnl_le_budget`      — Theorem G.6 clean Kraft tail;
* `termTower_le_budget`    — Proposition I.3.1 (`propositionI3_1_towerOutput`);
* `termDensePack_le_budget`— **Lemma I.4.1 + K.1.3** (`corollaryK1_3_densePackUnderFailure`);
* `termReturn_le_budget`   — Proposition I.5.1 (`proposition23_1_returnPackagesLowerClean`);
* `termRun_le_budget`      — Proposition I.5.2 (`propositionI5_2_runOutput`).

Summed (`ClosurePhaseMass_le_budget`) these give `ClosurePhaseMass data ≤ cStar·ξ·X`.
`termDensePack_le_I4_1` additionally exhibits the literal **I.4.1 smallness chain**
`K.1.3 cover → lemmaI4_1_densePackSmallness → ξ·s·X` budget form.

### B. Per-class comparison groundings (`𝔒_X ≤ term_X data`)

By the N.3.3 priority partition each absorbed class is a sub-collection of the
matching phase family, so its mass is dominated by the phase-mass term via real
combinatorial monotonicity (no analytic input):

* `densePackClass_card_le_termDensePack` — K.1.1 endpoint-disjoint cover: an
  absorbed dense-marker subset `S ⊆ densePackPoints` has `S.card ≤ termDensePack`;
* `chernoffClass_mass_le_termChernoff` — the absorbed progress subfamily of the
  high-cost Chernoff paths has weighted mass `≤ termChernoff`
  (`weightedMass_mono_subset`);
* `towerClass_mass_le_termTower` — the absorbed bounded-scale subset of tower
  entry/exit branches has charged mass `≤ termTower`
  (`Finset.sum_le_sum_of_subset_of_nonneg`);
* `returnOLC_le_termReturn` — the OLC endpoint-leakage summand (Lemma I.4.2) is
  `≤ termReturn` once the other three return masses are nonnegative.

### C. The grounded bridge

`absorbed_window_le_phaseMass_grounded` (and its `phases.toClosurePhaseData`
specialization `habsorb_ofC1VDClosure_grounded`) re-prove the central charge
bridge with the DensePack, Chernoff, and Tower comparisons **discharged
internally** from the realizations in B.  Only the endpoint/CNL/window
comparisons (`𝔒_E ≤ termReturn`, `𝔒_CNL ≤ termCnl`, `𝔒_V ≤ termRun`) and the two
aggregate N.3.3 / N.2.2 splits remain as conditional analytic inputs.

## What stays conditional

The endpoint-leakage `𝔒_E`, clean-CNL `𝔒_CNL`, and variation-drop `𝔒_V`
comparisons (the genuinely analytic per-package upper bounds not realized as
finset sub-collections in the current data layer), together with the N.3.3
five-class accounting split and the N.2.2 window-drop split, remain explicit
hypotheses.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open MeasureTheory Finset

noncomputable section

/-! ## A. Per-term manuscript budget bounds

Each phase-mass term is dominated by the per-phase budget `cStar · ξ · X / 6`,
re-deriving the package estimate on the concrete `ClosurePhaseMass` term. -/

/-- **Chernoff term budget (Lemma 22.1).** The high-cost path mass `termChernoff`
fits `cStar · ξ · X / 6`, via the Chernoff tilt bound
`shellChernoff_bound_of_moment_bound` and the bundled `manuscript_bound`. -/
theorem termChernoff_le_budget {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) :
    termChernoff data ≤ cStar * ξ * X / 6 := by
  have hChernoff :
      weightedMass (highCostSet data.chernoff.paths data.chernoff.cost data.chernoff.Y)
          data.chernoff.weight
        ≤ data.chernoff.root * data.chernoff.A ^ data.chernoff.m / data.chernoff.z ^ data.chernoff.Y :=
    shellChernoff_bound_of_moment_bound data.chernoff.weight_nonneg data.chernoff.z_ge_one
      data.chernoff.moment_bound
  exact hChernoff.trans data.chernoff.manuscript_bound

/-- **CNL term budget (Theorem G.6).** The clean Kraft-weighted CNL tail `termCnl`
fits `cStar · ξ · X / 6`, via the derived `manuscript_dominates` theorem and the
bundled `manuscript_bound`. -/
theorem termCnl_le_budget {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X)
    (hX_nonneg : 0 <= X) :
    termCnl data ≤ cStar * ξ * X / 6 := by
  show cleanCNLKraftSum data.cnl.paths data.cnl.BNDHeight data.cnl.c *
      data.cnl.shellFactor * X * data.cnl.Ij ≤ cStar * ξ * X / 6
  exact (data.cnl.manuscript_dominates hX_nonneg).trans data.cnl.manuscript_bound

/-- **Tower term budget (Proposition I.3.1).** The charged tower entry/exit mass
`termTower` fits `cStar · ξ · X / 6`, via `propositionI3_1_towerOutput` and the
bundled `hSmall`. -/
theorem termTower_le_budget {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) :
    termTower data ≤ cStar * ξ * X / 6 := by
  show (∑ b ∈ data.tower.entryExitSet, data.tower.chargedWeight b) ≤ cStar * ξ * X / 6
  exact (propositionI3_1_towerOutput data.tower.hSummable).trans data.tower.hSmall

/-- **DensePack term budget (Lemma I.4.1 + K.1.3).** The dense-pack point count
`termDensePack` fits `cStar · ξ · X / 6`, via the K.1.3 cover under failure
(`corollaryK1_3_densePackUnderFailure`, on the bundled marker/count data) and the
bundled K.4 smallness `hsmall`. -/
theorem termDensePack_le_budget {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) :
    termDensePack data ≤ cStar * ξ * X / 6 := by
  show (data.densePack.densePackPoints.card : ℝ) ≤ cStar * ξ * X / 6
  have hK13 :
      (data.densePack.densePackPoints.card : ℝ) ≤
        data.densePack.cStarSmall * X * ((2 * data.densePack.spread + 1 : Nat) : ℝ) :=
    corollaryK1_3_densePackUnderFailure data.densePack.hcover data.densePack.hcount
  exact hK13.trans data.densePack.hsmall

/-- **Return term budget (Proposition I.5.1).** The four-piece non-run return mass
`termReturn` fits `cStar · ξ · X / 6`, via `proposition23_1_returnPackagesLowerClean`
and the bundled `hSmall`. -/
theorem termReturn_le_budget {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) :
    termReturn data ≤ cStar * ξ * X / 6 := by
  show data.returnPkg.ordinaryShort + data.returnPkg.semiperiodic +
      data.returnPkg.olc + data.returnPkg.nonlocalLong ≤ cStar * ξ * X / 6
  have hSum :=
    proposition23_1_returnPackagesLowerClean data.returnPkg.hOrdinaryShort
      data.returnPkg.hSemiperiodic data.returnPkg.hOLC data.returnPkg.hNonlocalLong
  exact hSum.trans data.returnPkg.hSmall

/-- **Run term budget (Proposition I.5.2).** The run mass `termRun` fits
`cStar · ξ · X / 6`, via `propositionI5_2_runOutput` and the bundled `hSmall`. -/
theorem termRun_le_budget {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) :
    termRun data ≤ cStar * ξ * X / 6 := by
  show data.run.runMass ≤ cStar * ξ * X / 6
  exact (propositionI5_2_runOutput data.run.hRun).trans data.run.hSmall

/--
**Aggregate phase-mass budget.**

Summing the six per-term budget bounds, the full `ClosurePhaseMass` fits the
manuscript per-failure budget `cStar · ξ · X`.  This is the faithful upper bound
dual to the pressure lower bound `cPr · X ≤ ClosurePhaseMass`
(`ClosurePressureLowerBound`); no analytic hypothesis is consumed.
-/
theorem ClosurePhaseMass_le_budget {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X)
    (hX_nonneg : 0 <= X) :
    ClosurePhaseMass data ≤ cStar * ξ * X := by
  rw [ClosurePhaseMass_eq_six_terms]
  have h1 := termChernoff_le_budget data
  have h2 := termCnl_le_budget data hX_nonneg
  have h3 := termTower_le_budget data
  have h4 := termDensePack_le_budget data
  have h5 := termReturn_le_budget data
  have h6 := termRun_le_budget data
  linarith

/--
**DensePack term, manuscript I.4.1 `ξ·s·X` form.**

The literal Lemma I.4.1 smallness chain on the DensePack phase term: the K.1.3
cover under failure (`corollaryK1_3_densePackUnderFailure`) supplies
`termDensePack ≤ cStarSmall · X · (2 spread + 1)`, and the I.4.1 rescaling
(`lemmaI4_1_densePackSmallness`) converts the K.4 smallness
`cStarSmall · (2 spread + 1) ≤ ξ · s` into the manuscript budget `ξ · s · X`.

The K.4 numerical smallness `hSmall` is the manuscript's "choose `c_* ≪ ρ_D κ ξ`"
step (the genuinely chosen constant), supplied as the named input.
-/
theorem termDensePack_le_I4_1 {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X)
    {s : ℝ}
    (hX_nonneg : 0 ≤ X)
    (hSmall :
      data.densePack.cStarSmall * ((2 * data.densePack.spread + 1 : Nat) : ℝ) ≤ ξ * s) :
    termDensePack data ≤ ξ * s * X := by
  have hK13 :
      termDensePack data ≤
        data.densePack.cStarSmall * X * ((2 * data.densePack.spread + 1 : Nat) : ℝ) :=
    corollaryK1_3_densePackUnderFailure data.densePack.hcover data.densePack.hcount
  have hspread_nonneg : (0 : ℝ) ≤ ((2 * data.densePack.spread + 1 : Nat) : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hI41 :=
    lemmaI4_1_densePackSmallness
      (DensePackMass := termDensePack data)
      (cStar := data.densePack.cStarSmall) (X := X)
      (spreadFactor := ((2 * data.densePack.spread + 1 : Nat) : ℝ))
      (s := s) (Ij := 1) (ξ := ξ)
      (by simpa using hK13) hspread_nonneg hX_nonneg (by norm_num)
      (by simpa using hSmall)
  simpa using hI41

/-! ## B. Per-class comparison groundings

Each absorbed class is a sub-collection of the matching phase family (N.3.3
priority partition), so its mass is dominated by the phase-mass term. -/

/-- **DensePack comparison (K.1.1 endpoint-disjoint cover).** Any absorbed
dense-marker subset `S ⊆ densePackPoints` has `(S.card : ℝ) ≤ termDensePack data`.
This realizes `𝔒_D ≤ termDensePack`; it is the K.1.1 cover principle
(`lemmaK1_1_endpointDisjointDensePackCover`), i.e. `Finset.card_le_card`. -/
theorem densePackClass_card_le_termDensePack {cStar ξ X : ℝ}
    (data : ClosurePhaseData cStar ξ X)
    {S : Finset Nat} (hS : S ⊆ data.densePack.densePackPoints) :
    (S.card : ℝ) ≤ termDensePack data := by
  show (S.card : ℝ) ≤ (data.densePack.densePackPoints.card : ℝ)
  exact_mod_cast Finset.card_le_card hS

/-- **Chernoff comparison (high-cost subfamily monotonicity).** Any absorbed
progress subfamily `S ⊆ highCostSet …` of the Chernoff high-cost paths has
`weightedMass S weight ≤ termChernoff data`.  This realizes `𝔒_P ≤ termChernoff`
via `weightedMass_mono_subset` and the bundled path-weight nonnegativity. -/
theorem chernoffClass_mass_le_termChernoff {cStar ξ X : ℝ}
    (data : ClosurePhaseData cStar ξ X)
    {S : Finset data.chernoff.α}
    (hS : S ⊆ highCostSet data.chernoff.paths data.chernoff.cost data.chernoff.Y) :
    weightedMass S data.chernoff.weight ≤ termChernoff data := by
  show weightedMass S data.chernoff.weight ≤
    weightedMass (highCostSet data.chernoff.paths data.chernoff.cost data.chernoff.Y)
      data.chernoff.weight
  refine weightedMass_mono_subset hS ?_
  intro p hp
  exact data.chernoff.weight_nonneg p (mem_highCostSet.1 hp).1

/-- **Tower comparison (entry/exit subset monotonicity).** Any absorbed
bounded-scale subset `S ⊆ entryExitSet` of the tower entry/exit branches has
charged mass `∑_{b ∈ S} chargedWeight b ≤ termTower data`.  This realizes
`𝔒_bdd ≤ termTower` via `Finset.sum_le_sum_of_subset_of_nonneg` and the bundled
charged-weight nonnegativity. -/
theorem towerClass_mass_le_termTower {cStar ξ X : ℝ}
    (data : ClosurePhaseData cStar ξ X)
    {S : Finset TowerExit} (hS : S ⊆ data.tower.entryExitSet) :
    (∑ b ∈ S, data.tower.chargedWeight b) ≤ termTower data := by
  show (∑ b ∈ S, data.tower.chargedWeight b) ≤
      ∑ b ∈ data.tower.entryExitSet, data.tower.chargedWeight b
  exact Finset.sum_le_sum_of_subset_of_nonneg hS
    (fun b hb _ => data.tower.chargedWeight_nonneg b hb)

/-- **Endpoint/OLC comparison (Lemma I.4.2 leakage summand).** The OLC
endpoint-leakage summand `olc` of the return package is `≤ termReturn data`, once
the other three return masses are nonnegative.  This realizes the endpoint class
`𝔒_E ≤ termReturn` with `𝔒_E` the I.4.2 ordinary-local-long return piece; the three
nonnegativity side conditions are the (mild) return-mass positivity. -/
theorem returnOLC_le_termReturn {cStar ξ X : ℝ}
    (data : ClosurePhaseData cStar ξ X)
    (hOrdinaryShort : 0 ≤ data.returnPkg.ordinaryShort)
    (hSemiperiodic : 0 ≤ data.returnPkg.semiperiodic)
    (hNonlocalLong : 0 ≤ data.returnPkg.nonlocalLong) :
    data.returnPkg.olc ≤ termReturn data := by
  show data.returnPkg.olc ≤ data.returnPkg.ordinaryShort + data.returnPkg.semiperiodic +
      data.returnPkg.olc + data.returnPkg.nonlocalLong
  linarith

/-! ## C. The grounded central charge bridge

`absorbed_window_le_phaseMass_classes` with the DensePack, Chernoff, and Tower
comparisons discharged from the section-B realizations. -/

/--
**Central charge bridge with DensePack / Chernoff / Tower comparisons grounded.**

A drop-in for `absorbed_window_le_phaseMass_classes` in which three of the six
per-phase comparisons are discharged internally from the faithful sub-collection
realizations:

* `𝔒_D := densePackClass.card` for an absorbed dense-marker subset
  `densePackClass ⊆ densePackPoints` (K.1.1);
* `𝔒_P := weightedMass chernoffClass weight` for an absorbed progress subfamily
  `chernoffClass ⊆ highCostSet …` (high-cost subfamily monotonicity);
* `𝔒_bdd := ∑_{b ∈ towerClass} chargedWeight b` for an absorbed bounded-scale
  subset `towerClass ⊆ entryExitSet` (N.3.2 subset monotonicity).

The endpoint (`O_E`), clean-CNL (`O_CNL`), and window-drop (`O_V`) comparisons
remain conditional, as do the N.3.3 five-class absorption split (`hAbsorbed`) and
the N.2.2 window-drop split (`hWindow`).
-/
theorem absorbed_window_le_phaseMass_grounded {cStar ξ X : ℝ}
    (data : ClosurePhaseData cStar ξ X)
    {absorbedBound windowBound : ℝ}
    {densePackClass : Finset Nat}
    (hDensePackClass : densePackClass ⊆ data.densePack.densePackPoints)
    {chernoffClass : Finset data.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet data.chernoff.paths data.chernoff.cost data.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ data.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass data.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, data.tower.chargedWeight b))
    (hWindow : windowBound ≤ O_V)
    (hE : O_E ≤ termReturn data)
    (hCNL : O_CNL ≤ termCnl data)
    (hV : O_V ≤ termRun data) :
    absorbedBound + windowBound ≤ ClosurePhaseMass data :=
  absorbed_window_le_phaseMass_classes data
    hAbsorbed hWindow
    (densePackClass_card_le_termDensePack data hDensePackClass)
    (chernoffClass_mass_le_termChernoff data hChernoffClass)
    hE hCNL
    (towerClass_mass_le_termTower data hTowerClass)
    hV

/--
**`habsorb` for `ofC1VDClosure`, with DensePack / Chernoff / Tower grounded.**

Specializes `absorbed_window_le_phaseMass_grounded` to `phases.toClosurePhaseData`,
producing the exact `habsorb` proposition consumed by
`HighExcessChargeData.ofC1VDClosure`, with the DensePack, Chernoff, and Tower
comparisons discharged from their faithful sub-collection realizations.
-/
theorem habsorb_ofC1VDClosure_grounded {cStar ξ X : ℝ}
    (phases : SixPhaseFactoryData cStar ξ X)
    {absorbedBound windowBound : ℝ}
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow : windowBound ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    absorbedBound + windowBound ≤ ClosurePhaseMass phases.toClosurePhaseData :=
  absorbed_window_le_phaseMass_grounded phases.toClosurePhaseData
    hDensePackClass hChernoffClass hTowerClass
    hAbsorbed hWindow hE hCNL hV

/--
**`habsorb` for bundled-window C1-VD closure, with DensePack / Chernoff /
Tower grounded.**
-/
theorem habsorb_ofC1VDClosure_grounded_windowDrop {cStar ξ X : ℝ}
    (phases : SixPhaseFactoryData cStar ξ X)
    (drop : AppendixN.WindowDropEstimateData)
    {absorbedBound : ℝ}
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow : drop.CQ * drop.Y * AppendixN.Vs drop.K drop.W ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    absorbedBound + drop.CQ * drop.Y * AppendixN.Vs drop.K drop.W ≤
      ClosurePhaseMass phases.toClosurePhaseData :=
  absorbed_window_le_phaseMass_grounded phases.toClosurePhaseData
    hDensePackClass hChernoffClass hTowerClass
    hAbsorbed hWindow hE hCNL hV

/--
**Grounded Phase-E central-charge data.**

This is the C1-VD closure constructor with the DensePack, Chernoff, and Tower
absorbed-class comparisons discharged internally from concrete subfamilies.
The remaining conditional inputs are exactly the deep v4 leaves: I.9 mass
identification, the C1-VD split, terminal absorption, variation-drop bound, and
the endpoint/CNL/run per-class comparisons.
-/
def HighExcessChargeData.ofC1VDClosure_grounded
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass varMass absorbedBound windowBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + varMass)
    (hterm : termMass ≤ absorbedBound)
    (hvar : varMass ≤ windowBound)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow : windowBound ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  HighExcessChargeData.ofC1VDClosure phases carryData
    totalMass termMass varMass absorbedBound windowBound
    hHighExcess_eq hsplit hterm hvar
    (habsorb_ofC1VDClosure_grounded phases
      hDensePackClass hChernoffClass hTowerClass
      hAbsorbed hWindow hE hCNL hV)

/--
**Grounded Phase-E central-charge data, with faithful I.9 reindexing
discharged.**
-/
def HighExcessChargeData.ofC1VDClosure_grounded_branchMass
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass varMass absorbedBound windowBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hBranchMass_eq :
      branchWeightedMass
          ((highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y).image
              (stoppedBranchOf carryData.a carryData.r))
          (windowExcessWeight carryData.T)
        = totalMass)
    (hsplit : totalMass = termMass + varMass)
    (hterm : termMass ≤ absorbedBound)
    (hvar : varMass ≤ windowBound)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow : windowBound ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  HighExcessChargeData.ofC1VDClosure_branchMass phases carryData
    totalMass termMass varMass absorbedBound windowBound
    hBranchMass_eq hsplit hterm hvar
    (habsorb_ofC1VDClosure_grounded phases
      hDensePackClass hChernoffClass hTowerClass
      hAbsorbed hWindow hE hCNL hV)

/--
**Grounded Phase-E central-charge data, bundled window-drop form.**

DensePack, Chernoff, and Tower class comparisons are discharged from concrete
subfamilies, while N.2.2 is consumed as a `WindowDropEstimateData` bundle.
-/
def HighExcessChargeData.ofC1VDClosure_grounded_windowDrop
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (drop : AppendixN.WindowDropEstimateData)
    (totalMass termMass absorbedBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + drop.varDrop)
    (hterm : termMass ≤ absorbedBound)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow : drop.CQ * drop.Y * AppendixN.Vs drop.K drop.W ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  HighExcessChargeData.ofC1VDClosure_windowDrop phases carryData drop
    totalMass termMass absorbedBound hHighExcess_eq hsplit hterm
    (habsorb_ofC1VDClosure_grounded_windowDrop phases drop
      hDensePackClass hChernoffClass hTowerClass
      hAbsorbed hWindow hE hCNL hV)

/--
**Grounded Phase-E central-charge data, bundled window-drop form, with faithful
I.9 reindexing discharged.**
-/
def HighExcessChargeData.ofC1VDClosure_grounded_windowDrop_branchMass
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (drop : AppendixN.WindowDropEstimateData)
    (totalMass termMass absorbedBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hBranchMass_eq :
      branchWeightedMass
          ((highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y).image
              (stoppedBranchOf carryData.a carryData.r))
          (windowExcessWeight carryData.T)
        = totalMass)
    (hsplit : totalMass = termMass + drop.varDrop)
    (hterm : termMass ≤ absorbedBound)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow : drop.CQ * drop.Y * AppendixN.Vs drop.K drop.W ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  HighExcessChargeData.ofC1VDClosure_windowDrop_branchMass phases carryData drop
    totalMass termMass absorbedBound hBranchMass_eq hsplit hterm
    (habsorb_ofC1VDClosure_grounded_windowDrop phases drop
      hDensePackClass hChernoffClass hTowerClass
      hAbsorbed hWindow hE hCNL hV)

/--
**Grounded Phase-E per-failure assembly.**

This carries `HighExcessChargeData.ofC1VDClosure_grounded` through the final
per-failure assembly constructor.
-/
def PerFailureAssemblyData.ofC1VDClosure_grounded
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass varMass absorbedBound windowBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + varMass)
    (hterm : termMass ≤ absorbedBound)
    (hvar : varMass ≤ windowBound)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow : windowBound ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_grounded phases carryData
      totalMass termMass varMass absorbedBound windowBound
      hDensePackClass hChernoffClass hTowerClass
      hHighExcess_eq hsplit hterm hvar hAbsorbed hWindow hE hCNL hV)

/--
**Grounded Phase-E per-failure assembly, with faithful I.9 reindexing
discharged.**
-/
def PerFailureAssemblyData.ofC1VDClosure_grounded_branchMass
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass varMass absorbedBound windowBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hBranchMass_eq :
      branchWeightedMass
          ((highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y).image
              (stoppedBranchOf carryData.a carryData.r))
          (windowExcessWeight carryData.T)
        = totalMass)
    (hsplit : totalMass = termMass + varMass)
    (hterm : termMass ≤ absorbedBound)
    (hvar : varMass ≤ windowBound)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow : windowBound ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_grounded_branchMass phases carryData
      totalMass termMass varMass absorbedBound windowBound
      hDensePackClass hChernoffClass hTowerClass
      hBranchMass_eq hsplit hterm hvar hAbsorbed hWindow hE hCNL hV)

/--
**Grounded Phase-E per-failure assembly, bundled window-drop form.**
-/
def PerFailureAssemblyData.ofC1VDClosure_grounded_windowDrop
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (drop : AppendixN.WindowDropEstimateData)
    (totalMass termMass absorbedBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + drop.varDrop)
    (hterm : termMass ≤ absorbedBound)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow : drop.CQ * drop.Y * AppendixN.Vs drop.K drop.W ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_grounded_windowDrop phases carryData drop
      totalMass termMass absorbedBound
      hDensePackClass hChernoffClass hTowerClass
      hHighExcess_eq hsplit hterm hAbsorbed hWindow hE hCNL hV)

/--
**Grounded Phase-E per-failure assembly, bundled window-drop form, with faithful
I.9 reindexing discharged.**
-/
def PerFailureAssemblyData.ofC1VDClosure_grounded_windowDrop_branchMass
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (drop : AppendixN.WindowDropEstimateData)
    (totalMass termMass absorbedBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hBranchMass_eq :
      branchWeightedMass
          ((highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y).image
              (stoppedBranchOf carryData.a carryData.r))
          (windowExcessWeight carryData.T)
        = totalMass)
    (hsplit : totalMass = termMass + drop.varDrop)
    (hterm : termMass ≤ absorbedBound)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow : drop.CQ * drop.Y * AppendixN.Vs drop.K drop.W ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_grounded_windowDrop_branchMass phases carryData drop
      totalMass termMass absorbedBound
      hDensePackClass hChernoffClass hTowerClass
      hBranchMass_eq hsplit hterm hAbsorbed hWindow hE hCNL hV)

/--
**Grounded Phase-E central-charge data from reduced-record N.2.1 density.**

This combines the reduced-record N.2.1/N.2.2 drop-density construction with the
grounded phase-mass bridge: DensePack, Chernoff, and Tower comparisons are
discharged from concrete subfamilies, while endpoint/CNL/run and the honest
I.9/N.24 leaves remain explicit.
-/
def HighExcessChargeData.ofC1VDClosure_grounded_lowerLabelRecordDensity
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (VarDrop Cmul Y : ℝ)
    (D : ℝ → AppendixN.FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropDensity : ℝ → ℝ)
    (dropMass : ℝ → Branch → ℕ → ℝ)
    (hdrop_nonneg : ∀ T b e, 0 ≤ dropMass T b e)
    (crossingIndic : ℝ → ℕ → ℝ)
    (hindic_nonneg : ∀ T e, 0 ≤ crossingIndic T e)
    (hlift_le : ∀ T b e, dropMass T b e ≤ crossingIndic T e)
    (support : ℝ → ℕ → Finset Branch)
    (hsupp : ∀ T e, support T e ⊆ branches)
    (hzero : ∀ T e, ∀ b ∈ branches, b ∉ support T e → dropMass T b e = 0)
    (hle : ∀ T e, (D T).loIdx e ≤ (D T).hiIdx e)
    (hinj : ∀ T (e : ℕ), ∀ b ∈ support T e, ∀ b' ∈ support T e,
        (D T).record e b = (D T).record e b' →
          (D T).startResidue b = (D T).startResidue b' → b = b')
    (K : Finset ℕ) (W : ℕ → ℝ) (A : Set ℝ)
    (totalMass termMass absorbedBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + VarDrop)
    (hterm : termMass ≤ absorbedBound)
    (hCmulY : 0 ≤ Cmul * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hdensity :
      ∀ T ∈ A, dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e)
    (hindic :
      ∀ T ∈ A, ∀ e, crossingIndic T e = AppendixN.crossingIndicator (T + Y) W e)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y * AppendixN.Vs K W ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  let drop :=
    AppendixN.WindowDropEstimateData.ofLowerLabelRecordPriorityOfRecordDensity
      VarDrop Cmul Y D branches dropDensity dropMass hdrop_nonneg crossingIndic
      hindic_nonneg hlift_le support hsupp hzero hle hinj K W A hCmulY hA
      hdrop_int hvar hdensity hindic
  HighExcessChargeData.ofC1VDClosure_grounded_windowDrop phases carryData drop
    totalMass termMass absorbedBound
    hDensePackClass hChernoffClass hTowerClass hHighExcess_eq
    (by simpa [drop,
      AppendixN.WindowDropEstimateData.ofLowerLabelRecordPriorityOfRecordDensity,
      AppendixN.WindowDropEstimateData.ofScaledDropDensityBound] using hsplit)
    hterm hAbsorbed
    (by simpa [drop,
      AppendixN.WindowDropEstimateData.ofLowerLabelRecordPriorityOfRecordDensity,
      AppendixN.WindowDropEstimateData.ofScaledDropDensityBound] using hWindow)
    hE hCNL hV

/--
**Grounded Phase-E per-failure assembly from reduced-record N.2.1 density.**
-/
def PerFailureAssemblyData.ofC1VDClosure_grounded_lowerLabelRecordDensity
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (VarDrop Cmul Y : ℝ)
    (D : ℝ → AppendixN.FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropDensity : ℝ → ℝ)
    (dropMass : ℝ → Branch → ℕ → ℝ)
    (hdrop_nonneg : ∀ T b e, 0 ≤ dropMass T b e)
    (crossingIndic : ℝ → ℕ → ℝ)
    (hindic_nonneg : ∀ T e, 0 ≤ crossingIndic T e)
    (hlift_le : ∀ T b e, dropMass T b e ≤ crossingIndic T e)
    (support : ℝ → ℕ → Finset Branch)
    (hsupp : ∀ T e, support T e ⊆ branches)
    (hzero : ∀ T e, ∀ b ∈ branches, b ∉ support T e → dropMass T b e = 0)
    (hle : ∀ T e, (D T).loIdx e ≤ (D T).hiIdx e)
    (hinj : ∀ T (e : ℕ), ∀ b ∈ support T e, ∀ b' ∈ support T e,
        (D T).record e b = (D T).record e b' →
          (D T).startResidue b = (D T).startResidue b' → b = b')
    (K : Finset ℕ) (W : ℕ → ℝ) (A : Set ℝ)
    (totalMass termMass absorbedBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + VarDrop)
    (hterm : termMass ≤ absorbedBound)
    (hCmulY : 0 ≤ Cmul * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hdensity :
      ∀ T ∈ A, dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e)
    (hindic :
      ∀ T ∈ A, ∀ e, crossingIndic T e = AppendixN.crossingIndicator (T + Y) W e)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y * AppendixN.Vs K W ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_grounded_lowerLabelRecordDensity
      phases carryData VarDrop Cmul Y D branches dropDensity dropMass hdrop_nonneg
      crossingIndic hindic_nonneg hlift_le support hsupp hzero hle hinj K W A
      totalMass termMass absorbedBound hDensePackClass hChernoffClass hTowerClass
      hHighExcess_eq hsplit hterm hCmulY hA hdrop_int hvar hdensity hindic
      hAbsorbed hWindow hE hCNL hV)

/--
**Grounded Phase-E central-charge data from reduced-record density, with
explicit N.13 variation bound.**
-/
def HighExcessChargeData.ofC1VDClosure_grounded_lowerLabelRecordDensity_explicitWindow
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (VarDrop Cmul Y M : ℝ)
    (D : ℝ → AppendixN.FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropDensity : ℝ → ℝ)
    (dropMass : ℝ → Branch → ℕ → ℝ)
    (hdrop_nonneg : ∀ T b e, 0 ≤ dropMass T b e)
    (crossingIndic : ℝ → ℕ → ℝ)
    (hindic_nonneg : ∀ T e, 0 ≤ crossingIndic T e)
    (hlift_le : ∀ T b e, dropMass T b e ≤ crossingIndic T e)
    (support : ℝ → ℕ → Finset Branch)
    (hsupp : ∀ T e, support T e ⊆ branches)
    (hzero : ∀ T e, ∀ b ∈ branches, b ∉ support T e → dropMass T b e = 0)
    (hle : ∀ T e, (D T).loIdx e ≤ (D T).hiIdx e)
    (hinj : ∀ T (e : ℕ), ∀ b ∈ support T e, ∀ b' ∈ support T e,
        (D T).record e b = (D T).record e b' →
          (D T).startResidue b = (D T).startResidue b' → b = b')
    (g : ℕ → ℝ) (s : ℕ) (K : Finset ℕ) (A : Set ℝ)
    (totalMass termMass absorbedBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + VarDrop)
    (hterm : termMass ≤ absorbedBound)
    (hCmulY : 0 ≤ Cmul * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hdensity :
      ∀ T ∈ A, dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e)
    (hindic :
      ∀ T ∈ A, ∀ e,
        crossingIndic T e = AppendixN.crossingIndicator (T + Y) (AppendixN.windowSum g s) e)
    (hg : ∀ n, 0 ≤ g n)
    (hKidx : ∀ k ∈ K, s ≤ k)
    (hMlo : ∀ k ∈ K, g (k - s) ≤ M)
    (hMhi : ∀ k ∈ K, g (k + 1) ≤ M)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * M * (K.card : ℝ)) ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData := by
  let Cfiber : ℝ := ((Q * Fintype.card Labels * Q : ℕ) : ℝ)
  have hCfiber : 0 ≤ Cfiber := by
    dsimp [Cfiber]
    exact_mod_cast Nat.zero_le (Q * Fintype.card Labels * Q)
  have htotal : 0 ≤ (Cmul * Cfiber) * Y := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using mul_nonneg hCfiber hCmulY
  have hWindowVs :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          AppendixN.Vs K (AppendixN.windowSum g s) ≤ O_V := by
    have hscaled :=
      AppendixN.scaled_windowTerm_le_explicit_windowBound
        (Cmul * Cfiber) Y M g s K htotal hg hKidx hMlo hMhi
    have hscaled' :
        (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
            AppendixN.Vs K (AppendixN.windowSum g s)
          ≤ (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
              (2 * M * (K.card : ℝ)) := by
      simpa [Cfiber] using hscaled
    exact hscaled'.trans hWindow
  exact
    HighExcessChargeData.ofC1VDClosure_grounded_lowerLabelRecordDensity
      phases carryData VarDrop Cmul Y D branches dropDensity dropMass hdrop_nonneg
      crossingIndic hindic_nonneg hlift_le support hsupp hzero hle hinj K
      (AppendixN.windowSum g s) A totalMass termMass absorbedBound
      hDensePackClass hChernoffClass hTowerClass hHighExcess_eq hsplit hterm
      hCmulY hA hdrop_int hvar hdensity hindic hAbsorbed hWindowVs hE hCNL hV

/--
**Grounded Phase-E per-failure assembly from reduced-record density, with
explicit N.13 variation bound.**
-/
def PerFailureAssemblyData.ofC1VDClosure_grounded_lowerLabelRecordDensity_explicitWindow
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (VarDrop Cmul Y M : ℝ)
    (D : ℝ → AppendixN.FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropDensity : ℝ → ℝ)
    (dropMass : ℝ → Branch → ℕ → ℝ)
    (hdrop_nonneg : ∀ T b e, 0 ≤ dropMass T b e)
    (crossingIndic : ℝ → ℕ → ℝ)
    (hindic_nonneg : ∀ T e, 0 ≤ crossingIndic T e)
    (hlift_le : ∀ T b e, dropMass T b e ≤ crossingIndic T e)
    (support : ℝ → ℕ → Finset Branch)
    (hsupp : ∀ T e, support T e ⊆ branches)
    (hzero : ∀ T e, ∀ b ∈ branches, b ∉ support T e → dropMass T b e = 0)
    (hle : ∀ T e, (D T).loIdx e ≤ (D T).hiIdx e)
    (hinj : ∀ T (e : ℕ), ∀ b ∈ support T e, ∀ b' ∈ support T e,
        (D T).record e b = (D T).record e b' →
          (D T).startResidue b = (D T).startResidue b' → b = b')
    (g : ℕ → ℝ) (s : ℕ) (K : Finset ℕ) (A : Set ℝ)
    (totalMass termMass absorbedBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + VarDrop)
    (hterm : termMass ≤ absorbedBound)
    (hCmulY : 0 ≤ Cmul * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hdensity :
      ∀ T ∈ A, dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e)
    (hindic :
      ∀ T ∈ A, ∀ e,
        crossingIndic T e = AppendixN.crossingIndicator (T + Y) (AppendixN.windowSum g s) e)
    (hg : ∀ n, 0 ≤ g n)
    (hKidx : ∀ k ∈ K, s ≤ k)
    (hMlo : ∀ k ∈ K, g (k - s) ≤ M)
    (hMhi : ∀ k ∈ K, g (k + 1) ≤ M)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * M * (K.card : ℝ)) ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_grounded_lowerLabelRecordDensity_explicitWindow
      phases carryData VarDrop Cmul Y M D branches dropDensity dropMass
      hdrop_nonneg crossingIndic hindic_nonneg hlift_le support hsupp hzero hle hinj
      g s K A totalMass termMass absorbedBound
      hDensePackClass hChernoffClass hTowerClass hHighExcess_eq hsplit hterm
      hCmulY hA hdrop_int hvar hdensity hindic hg hKidx hMlo hMhi
      hAbsorbed hWindow hE hCNL hV)

/--
**Grounded Phase-E central-charge data from reduced-record density for the real
hit-gap sequence.**

This is the grounded counterpart of
`HighExcessChargeData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity_hitGap`:
DensePack, Chernoff, and Tower comparisons are discharged from concrete
subfamilies, and the N.13 window variation is grounded in
`HitSequence.hitGap_le_of_shell_window`.
-/
def HighExcessChargeData.ofC1VDClosure_grounded_lowerLabelRecordDensity_hitGap
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    {Qden B X L : Nat} {P : Int} {d a : Nat → Nat}
    (hd : BinaryDigits d) (hseq : HitSequence d a)
    (hQden : 0 < Qden)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Qden : ℝ))
    (hX_eq : X = 2 ^ L) (hX_pos : 1 ≤ X)
    (hB : Qden * 4 ≤ 2 ^ B)
    {r : Nat} (hKr : r + 1 ≤ (supportShell d X).card)
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (VarDrop Cmul Y : ℝ)
    (D : ℝ → AppendixN.FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropDensity : ℝ → ℝ)
    (dropMass : ℝ → Branch → ℕ → ℝ)
    (hdrop_nonneg : ∀ T b e, 0 ≤ dropMass T b e)
    (crossingIndic : ℝ → ℕ → ℝ)
    (hindic_nonneg : ∀ T e, 0 ≤ crossingIndic T e)
    (hlift_le : ∀ T b e, dropMass T b e ≤ crossingIndic T e)
    (support : ℝ → ℕ → Finset Branch)
    (hsupp : ∀ T e, support T e ⊆ branches)
    (hzero : ∀ T e, ∀ b ∈ branches, b ∉ support T e → dropMass T b e = 0)
    (hle : ∀ T e, (D T).loIdx e ≤ (D T).hiIdx e)
    (hinj : ∀ T (e : ℕ), ∀ b ∈ support T e, ∀ b' ∈ support T e,
        (D T).record e b = (D T).record e b' →
          (D T).startResidue b = (D T).startResidue b' → b = b')
    (s : ℕ) (K : Finset ℕ) (A : Set ℝ)
    (totalMass termMass absorbedBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + VarDrop)
    (hterm : termMass ≤ absorbedBound)
    (hK : ∀ k ∈ K, s ≤ k)
    (hKwin : ∀ k ∈ K, k + 1 < hseq.firstIndexAbove X + r)
    (hCmulY : 0 ≤ Cmul * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hdensity :
      ∀ T ∈ A, dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e)
    (hindic :
      ∀ T ∈ A, ∀ e,
        crossingIndic T e =
          AppendixN.crossingIndicator (T + Y)
            (AppendixN.windowSum (fun n => (hitGap a n : ℝ)) s) e)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * ((L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  HighExcessChargeData.ofC1VDClosure_grounded_lowerLabelRecordDensity_explicitWindow
    phases carryData VarDrop Cmul Y ((L + B + 1 : ℕ) : ℝ) D branches
    dropDensity dropMass hdrop_nonneg crossingIndic hindic_nonneg hlift_le
    support hsupp hzero hle hinj (fun n => (hitGap a n : ℝ)) s K A
    totalMass termMass absorbedBound hDensePackClass hChernoffClass hTowerClass
    hHighExcess_eq hsplit hterm hCmulY hA hdrop_int hvar hdensity hindic
    (fun n => Nat.cast_nonneg _) hK
    (fun k hk => by
      have hlt : k - s < hseq.firstIndexAbove X + r := by
        have := hKwin k hk; omega
      have hbound := hseq.hitGap_le_of_shell_window hd hQden heta hX_eq hX_pos hB hKr hlt
      show (hitGap a (k - s) : ℝ) ≤ ((L + B + 1 : ℕ) : ℝ)
      exact_mod_cast hbound)
    (fun k hk => by
      have hbound := hseq.hitGap_le_of_shell_window hd hQden heta hX_eq hX_pos hB hKr
        (hKwin k hk)
      show (hitGap a (k + 1) : ℝ) ≤ ((L + B + 1 : ℕ) : ℝ)
      exact_mod_cast hbound)
    hAbsorbed hWindow hE hCNL hV

/--
**Grounded Phase-E per-failure assembly from reduced-record density for the
real hit-gap sequence.**
-/
def PerFailureAssemblyData.ofC1VDClosure_grounded_lowerLabelRecordDensity_hitGap
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    {Qden B X L : Nat} {P : Int} {d a : Nat → Nat}
    (hd : BinaryDigits d) (hseq : HitSequence d a)
    (hQden : 0 < Qden)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Qden : ℝ))
    (hX_eq : X = 2 ^ L) (hX_pos : 1 ≤ X)
    (hB : Qden * 4 ≤ 2 ^ B)
    {r : Nat} (hKr : r + 1 ≤ (supportShell d X).card)
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (VarDrop Cmul Y : ℝ)
    (D : ℝ → AppendixN.FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropDensity : ℝ → ℝ)
    (dropMass : ℝ → Branch → ℕ → ℝ)
    (hdrop_nonneg : ∀ T b e, 0 ≤ dropMass T b e)
    (crossingIndic : ℝ → ℕ → ℝ)
    (hindic_nonneg : ∀ T e, 0 ≤ crossingIndic T e)
    (hlift_le : ∀ T b e, dropMass T b e ≤ crossingIndic T e)
    (support : ℝ → ℕ → Finset Branch)
    (hsupp : ∀ T e, support T e ⊆ branches)
    (hzero : ∀ T e, ∀ b ∈ branches, b ∉ support T e → dropMass T b e = 0)
    (hle : ∀ T e, (D T).loIdx e ≤ (D T).hiIdx e)
    (hinj : ∀ T (e : ℕ), ∀ b ∈ support T e, ∀ b' ∈ support T e,
        (D T).record e b = (D T).record e b' →
          (D T).startResidue b = (D T).startResidue b' → b = b')
    (s : ℕ) (K : Finset ℕ) (A : Set ℝ)
    (totalMass termMass absorbedBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + VarDrop)
    (hterm : termMass ≤ absorbedBound)
    (hK : ∀ k ∈ K, s ≤ k)
    (hKwin : ∀ k ∈ K, k + 1 < hseq.firstIndexAbove X + r)
    (hCmulY : 0 ≤ Cmul * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hdensity :
      ∀ T ∈ A, dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e)
    (hindic :
      ∀ T ∈ A, ∀ e,
        crossingIndic T e =
          AppendixN.crossingIndicator (T + Y)
            (AppendixN.windowSum (fun n => (hitGap a n : ℝ)) s) e)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * ((L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_grounded_lowerLabelRecordDensity_hitGap
      hd hseq hQden heta hX_eq hX_pos hB hKr phases carryData VarDrop Cmul Y
      D branches dropDensity dropMass hdrop_nonneg crossingIndic hindic_nonneg
      hlift_le support hsupp hzero hle hinj s K A totalMass termMass absorbedBound
      hDensePackClass hChernoffClass hTowerClass hHighExcess_eq hsplit hterm
      hK hKwin hCmulY hA hdrop_int hvar hdensity hindic hAbsorbed hWindow
      hE hCNL hV)

/--
**Grounded Phase-E central-charge data from carry-packaged hit-gap data.**

This is the grounded counterpart of
`HighExcessChargeData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity_carryHitGap`:
the shell/carry fields supply the concrete hit sequence and shell-window
parameters, while the DensePack, Chernoff, and Tower comparisons are grounded in
their concrete classes.
-/
def HighExcessChargeData.ofC1VDClosure_grounded_lowerLabelRecordDensity_carryHitGap
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    {B : Nat} {P : Int}
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (hP :
      realWeightedValue (natBinaryAsReal shell.d) =
        (P : ℝ) / (shell.Q : ℝ))
    (hX_eq : shell.X = 2 ^ carryData.L)
    (hX_pos : 1 ≤ shell.X)
    (hB : shell.Q * 4 ≤ 2 ^ B)
    (hKr : carryData.r + 1 ≤ (supportShell shell.d shell.X).card)
    (VarDrop Cmul Y : ℝ)
    (D : ℝ → AppendixN.FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropDensity : ℝ → ℝ)
    (dropMass : ℝ → Branch → ℕ → ℝ)
    (hdrop_nonneg : ∀ T b e, 0 ≤ dropMass T b e)
    (crossingIndic : ℝ → ℕ → ℝ)
    (hindic_nonneg : ∀ T e, 0 ≤ crossingIndic T e)
    (hlift_le : ∀ T b e, dropMass T b e ≤ crossingIndic T e)
    (support : ℝ → ℕ → Finset Branch)
    (hsupp : ∀ T e, support T e ⊆ branches)
    (hzero : ∀ T e, ∀ b ∈ branches, b ∉ support T e → dropMass T b e = 0)
    (hle : ∀ T e, (D T).loIdx e ≤ (D T).hiIdx e)
    (hinj : ∀ T (e : ℕ), ∀ b ∈ support T e, ∀ b' ∈ support T e,
        (D T).record e b = (D T).record e b' →
          (D T).startResidue b = (D T).startResidue b' → b = b')
    (s : ℕ) (K : Finset ℕ) (A : Set ℝ)
    (totalMass termMass absorbedBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + VarDrop)
    (hterm : termMass ≤ absorbedBound)
    (hK : ∀ k ∈ K, s ≤ k)
    (hKwin : ∀ k ∈ K,
      k + 1 < carryData.carry.hits.firstIndexAbove shell.X + carryData.r)
    (hCmulY : 0 ≤ Cmul * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hdensity :
      ∀ T ∈ A, dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e)
    (hindic :
      ∀ T ∈ A, ∀ e,
        crossingIndic T e =
          AppendixN.crossingIndicator (T + Y)
            (AppendixN.windowSum (fun n => (hitGap carryData.a n : ℝ)) s) e)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData := by
  have hvarDrop :
      VarDrop
        ≤ (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
            (2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) :=
    AppendixN.varDrop_le_from_lowerLabelRecordPriorityOfRecord_density_carryHitGap
      carryData hP hX_eq hX_pos hB hKr VarDrop Cmul Y D branches dropDensity
      dropMass hdrop_nonneg crossingIndic hindic_nonneg hlift_le support hsupp
      hzero hle hinj s K A hK hKwin hCmulY hA hdrop_int hvar hdensity hindic
  exact
    HighExcessChargeData.ofC1VDClosure_grounded phases carryData
      totalMass termMass VarDrop absorbedBound
      ((Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
        (2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)))
      hDensePackClass hChernoffClass hTowerClass
      hHighExcess_eq hsplit hterm hvarDrop hAbsorbed hWindow hE hCNL hV

/--
**Grounded Phase-E central-charge data from carry-packaged hit-gap data, with
faithful I.9 reindexing discharged.**
-/
def HighExcessChargeData.ofC1VDClosure_grounded_lowerLabelRecordDensity_carryHitGap_branchMass
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    {B : Nat} {P : Int}
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (hP :
      realWeightedValue (natBinaryAsReal shell.d) =
        (P : ℝ) / (shell.Q : ℝ))
    (hX_eq : shell.X = 2 ^ carryData.L)
    (hX_pos : 1 ≤ shell.X)
    (hB : shell.Q * 4 ≤ 2 ^ B)
    (hKr : carryData.r + 1 ≤ (supportShell shell.d shell.X).card)
    (VarDrop Cmul Y : ℝ)
    (D : ℝ → AppendixN.FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropDensity : ℝ → ℝ)
    (dropMass : ℝ → Branch → ℕ → ℝ)
    (hdrop_nonneg : ∀ T b e, 0 ≤ dropMass T b e)
    (crossingIndic : ℝ → ℕ → ℝ)
    (hindic_nonneg : ∀ T e, 0 ≤ crossingIndic T e)
    (hlift_le : ∀ T b e, dropMass T b e ≤ crossingIndic T e)
    (support : ℝ → ℕ → Finset Branch)
    (hsupp : ∀ T e, support T e ⊆ branches)
    (hzero : ∀ T e, ∀ b ∈ branches, b ∉ support T e → dropMass T b e = 0)
    (hle : ∀ T e, (D T).loIdx e ≤ (D T).hiIdx e)
    (hinj : ∀ T (e : ℕ), ∀ b ∈ support T e, ∀ b' ∈ support T e,
        (D T).record e b = (D T).record e b' →
          (D T).startResidue b = (D T).startResidue b' → b = b')
    (s : ℕ) (K : Finset ℕ) (A : Set ℝ)
    (totalMass termMass absorbedBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hBranchMass_eq :
      branchWeightedMass
          ((highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y).image
              (stoppedBranchOf carryData.a carryData.r))
          (windowExcessWeight carryData.T)
        = totalMass)
    (hsplit : totalMass = termMass + VarDrop)
    (hterm : termMass ≤ absorbedBound)
    (hK : ∀ k ∈ K, s ≤ k)
    (hKwin : ∀ k ∈ K,
      k + 1 < carryData.carry.hits.firstIndexAbove shell.X + carryData.r)
    (hCmulY : 0 ≤ Cmul * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hdensity :
      ∀ T ∈ A, dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e)
    (hindic :
      ∀ T ∈ A, ∀ e,
        crossingIndic T e =
          AppendixN.crossingIndicator (T + Y)
            (AppendixN.windowSum (fun n => (hitGap carryData.a n : ℝ)) s) e)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData := by
  have hvarDrop :
      VarDrop
        ≤ (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
            (2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) :=
    AppendixN.varDrop_le_from_lowerLabelRecordPriorityOfRecord_density_carryHitGap
      carryData hP hX_eq hX_pos hB hKr VarDrop Cmul Y D branches dropDensity
      dropMass hdrop_nonneg crossingIndic hindic_nonneg hlift_le support hsupp
      hzero hle hinj s K A hK hKwin hCmulY hA hdrop_int hvar hdensity hindic
  exact
    HighExcessChargeData.ofC1VDClosure_grounded_branchMass phases carryData
      totalMass termMass VarDrop absorbedBound
      ((Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
        (2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)))
      hDensePackClass hChernoffClass hTowerClass
      hBranchMass_eq hsplit hterm hvarDrop hAbsorbed hWindow hE hCNL hV

/--
**Grounded Phase-E per-failure assembly from carry-packaged hit-gap data.**
-/
def PerFailureAssemblyData.ofC1VDClosure_grounded_lowerLabelRecordDensity_carryHitGap
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    {B : Nat} {P : Int}
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (hP :
      realWeightedValue (natBinaryAsReal shell.d) =
        (P : ℝ) / (shell.Q : ℝ))
    (hX_eq : shell.X = 2 ^ carryData.L)
    (hX_pos : 1 ≤ shell.X)
    (hB : shell.Q * 4 ≤ 2 ^ B)
    (hKr : carryData.r + 1 ≤ (supportShell shell.d shell.X).card)
    (VarDrop Cmul Y : ℝ)
    (D : ℝ → AppendixN.FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropDensity : ℝ → ℝ)
    (dropMass : ℝ → Branch → ℕ → ℝ)
    (hdrop_nonneg : ∀ T b e, 0 ≤ dropMass T b e)
    (crossingIndic : ℝ → ℕ → ℝ)
    (hindic_nonneg : ∀ T e, 0 ≤ crossingIndic T e)
    (hlift_le : ∀ T b e, dropMass T b e ≤ crossingIndic T e)
    (support : ℝ → ℕ → Finset Branch)
    (hsupp : ∀ T e, support T e ⊆ branches)
    (hzero : ∀ T e, ∀ b ∈ branches, b ∉ support T e → dropMass T b e = 0)
    (hle : ∀ T e, (D T).loIdx e ≤ (D T).hiIdx e)
    (hinj : ∀ T (e : ℕ), ∀ b ∈ support T e, ∀ b' ∈ support T e,
        (D T).record e b = (D T).record e b' →
          (D T).startResidue b = (D T).startResidue b' → b = b')
    (s : ℕ) (K : Finset ℕ) (A : Set ℝ)
    (totalMass termMass absorbedBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + VarDrop)
    (hterm : termMass ≤ absorbedBound)
    (hK : ∀ k ∈ K, s ≤ k)
    (hKwin : ∀ k ∈ K,
      k + 1 < carryData.carry.hits.firstIndexAbove shell.X + carryData.r)
    (hCmulY : 0 ≤ Cmul * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hdensity :
      ∀ T ∈ A, dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e)
    (hindic :
      ∀ T ∈ A, ∀ e,
        crossingIndic T e =
          AppendixN.crossingIndicator (T + Y)
            (AppendixN.windowSum (fun n => (hitGap carryData.a n : ℝ)) s) e)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_grounded_lowerLabelRecordDensity_carryHitGap
      phases carryData hP hX_eq hX_pos hB hKr VarDrop Cmul Y D branches
      dropDensity dropMass hdrop_nonneg crossingIndic hindic_nonneg hlift_le
      support hsupp hzero hle hinj s K A totalMass termMass absorbedBound
      hDensePackClass hChernoffClass hTowerClass hHighExcess_eq hsplit hterm
      hK hKwin hCmulY hA hdrop_int hvar hdensity hindic hAbsorbed hWindow
      hE hCNL hV)

/--
**Grounded Phase-E per-failure assembly from carry-packaged hit-gap data, with
faithful I.9 reindexing discharged.**
-/
def PerFailureAssemblyData.ofC1VDClosure_grounded_lowerLabelRecordDensity_carryHitGap_branchMass
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    {B : Nat} {P : Int}
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (hP :
      realWeightedValue (natBinaryAsReal shell.d) =
        (P : ℝ) / (shell.Q : ℝ))
    (hX_eq : shell.X = 2 ^ carryData.L)
    (hX_pos : 1 ≤ shell.X)
    (hB : shell.Q * 4 ≤ 2 ^ B)
    (hKr : carryData.r + 1 ≤ (supportShell shell.d shell.X).card)
    (VarDrop Cmul Y : ℝ)
    (D : ℝ → AppendixN.FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropDensity : ℝ → ℝ)
    (dropMass : ℝ → Branch → ℕ → ℝ)
    (hdrop_nonneg : ∀ T b e, 0 ≤ dropMass T b e)
    (crossingIndic : ℝ → ℕ → ℝ)
    (hindic_nonneg : ∀ T e, 0 ≤ crossingIndic T e)
    (hlift_le : ∀ T b e, dropMass T b e ≤ crossingIndic T e)
    (support : ℝ → ℕ → Finset Branch)
    (hsupp : ∀ T e, support T e ⊆ branches)
    (hzero : ∀ T e, ∀ b ∈ branches, b ∉ support T e → dropMass T b e = 0)
    (hle : ∀ T e, (D T).loIdx e ≤ (D T).hiIdx e)
    (hinj : ∀ T (e : ℕ), ∀ b ∈ support T e, ∀ b' ∈ support T e,
        (D T).record e b = (D T).record e b' →
          (D T).startResidue b = (D T).startResidue b' → b = b')
    (s : ℕ) (K : Finset ℕ) (A : Set ℝ)
    (totalMass termMass absorbedBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL O_V : ℝ}
    (hBranchMass_eq :
      branchWeightedMass
          ((highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y).image
              (stoppedBranchOf carryData.a carryData.r))
          (windowExcessWeight carryData.T)
        = totalMass)
    (hsplit : totalMass = termMass + VarDrop)
    (hterm : termMass ≤ absorbedBound)
    (hK : ∀ k ∈ K, s ≤ k)
    (hKwin : ∀ k ∈ K,
      k + 1 < carryData.carry.hits.firstIndexAbove shell.X + carryData.r)
    (hCmulY : 0 ≤ Cmul * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hdensity :
      ∀ T ∈ A, dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e)
    (hindic :
      ∀ T ∈ A, ∀ e,
        crossingIndic T e =
          AppendixN.crossingIndicator (T + Y)
            (AppendixN.windowSum (fun n => (hitGap carryData.a n : ℝ)) s) e)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) ≤ O_V)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_grounded_lowerLabelRecordDensity_carryHitGap_branchMass
      phases carryData hP hX_eq hX_pos hB hKr VarDrop Cmul Y D branches
      dropDensity dropMass hdrop_nonneg crossingIndic hindic_nonneg hlift_le
      support hsupp hzero hle hinj s K A totalMass termMass absorbedBound
      hDensePackClass hChernoffClass hTowerClass hBranchMass_eq hsplit hterm
      hK hKwin hCmulY hA hdrop_int hvar hdensity hindic hAbsorbed hWindow
      hE hCNL hV)

/--
**Table-routed no-drop central bridge with DensePack / Chernoff / Tower grounded.**

This is the grounded counterpart of
`absorbed_nonDrop_le_phaseMass_classes`: the table-routed variation-drop mass has
already vanished, so the bridge uses only the five non-drop classes.  DensePack,
Chernoff, and Tower comparisons are discharged from concrete subfamilies; the
endpoint/CNL comparisons and nonnegative run slack remain explicit inputs.
-/
theorem absorbed_nonDrop_le_phaseMass_grounded {cStar ξ X : ℝ}
    (data : ClosurePhaseData cStar ξ X)
    {absorbedBound : ℝ}
    {densePackClass : Finset Nat}
    (hDensePackClass : densePackClass ⊆ data.densePack.densePackPoints)
    {chernoffClass : Finset data.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet data.chernoff.paths data.chernoff.cost data.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ data.tower.entryExitSet)
    {O_E O_CNL : ℝ}
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass data.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, data.tower.chargedWeight b))
    (hE : O_E ≤ termReturn data)
    (hCNL : O_CNL ≤ termCnl data)
    (hRun_nonneg : 0 ≤ termRun data) :
    absorbedBound ≤ ClosurePhaseMass data :=
  absorbed_nonDrop_le_phaseMass_classes data
    hAbsorbed
    (densePackClass_card_le_termDensePack data hDensePackClass)
    (chernoffClass_mass_le_termChernoff data hChernoffClass)
    hE hCNL
    (towerClass_mass_le_termTower data hTowerClass)
    hRun_nonneg

/--
**`habsorb` for table-routed C1-VD closure, with DensePack / Chernoff / Tower grounded.**
-/
theorem habsorb_ofTableRoutedC1VDClosure_grounded {cStar ξ X : ℝ}
    (phases : SixPhaseFactoryData cStar ξ X)
    {absorbedBound : ℝ}
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL : ℝ}
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hRun_nonneg : 0 ≤ termRun phases.toClosurePhaseData) :
    absorbedBound ≤ ClosurePhaseMass phases.toClosurePhaseData :=
  absorbed_nonDrop_le_phaseMass_grounded phases.toClosurePhaseData
    hDensePackClass hChernoffClass hTowerClass
    hAbsorbed hE hCNL hRun_nonneg

/--
**Grounded table-routed Phase-E central-charge data.**

This constructor is the table-routed no-drop path with the DensePack, Chernoff,
and Tower comparisons discharged internally from concrete subfamilies.  Compared
with `HighExcessChargeData.ofC1VDClosure_grounded`, it removes the
variation-drop window inputs (`windowBound`, `O_V`, and `hV`) from this route.
-/
def HighExcessChargeData.ofTableRoutedC1VDClosure_grounded
    {sigma iota : Type*} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota)
    (row : iota → AppendixN.TerminalRow) (supp thr : iota → Nat)
    (weight : OutputObjectV4 → ℝ)
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass absorbedBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL : ℝ}
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit :
      totalMass =
        termMass +
          variationDropMass
            (E.atoms.image
              (fun omega =>
                OutputObjectV4.mk (row omega).outputClass (supp omega) (thr omega)))
            weight)
    (hterm : termMass ≤ absorbedBound)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hRun_nonneg : 0 ≤ termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  HighExcessChargeData.ofTableRoutedC1VDClosure E row supp thr weight phases carryData
    totalMass termMass absorbedBound hHighExcess_eq hsplit hterm
    (habsorb_ofTableRoutedC1VDClosure_grounded phases
      hDensePackClass hChernoffClass hTowerClass hAbsorbed hE hCNL hRun_nonneg)

/--
**Grounded table-routed Phase-E per-failure assembly.**
-/
def PerFailureAssemblyData.ofTableRoutedC1VDClosure_grounded
    {sigma iota : Type*} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota)
    (row : iota → AppendixN.TerminalRow) (supp thr : iota → Nat)
    (weight : OutputObjectV4 → ℝ)
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass absorbedBound : ℝ)
    {densePackClass : Finset Nat}
    (hDensePackClass :
      densePackClass ⊆ phases.toClosurePhaseData.densePack.densePackPoints)
    {chernoffClass : Finset phases.toClosurePhaseData.chernoff.α}
    (hChernoffClass :
      chernoffClass ⊆ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    {towerClass : Finset TowerExit}
    (hTowerClass : towerClass ⊆ phases.toClosurePhaseData.tower.entryExitSet)
    {O_E O_CNL : ℝ}
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit :
      totalMass =
        termMass +
          variationDropMass
            (E.atoms.image
              (fun omega =>
                OutputObjectV4.mk (row omega).outputClass (supp omega) (thr omega)))
            weight)
    (hterm : termMass ≤ absorbedBound)
    (hAbsorbed :
      absorbedBound ≤
        (densePackClass.card : ℝ)
          + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
          + O_E + O_CNL
          + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b))
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hRun_nonneg : 0 ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofTableRoutedC1VDClosure_grounded E row supp thr weight
      phases carryData totalMass termMass absorbedBound
      hDensePackClass hChernoffClass hTowerClass
      hHighExcess_eq hsplit hterm hAbsorbed hE hCNL hRun_nonneg)

end

end Erdos260
