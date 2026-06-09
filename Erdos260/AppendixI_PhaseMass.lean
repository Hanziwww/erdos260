import Mathlib
import Erdos260.ClosureFactory
import Erdos260.AppendixI
import Erdos260.PerFailureAssembly
import Erdos260.AppendixN_Closure
import Erdos260.AppendixN_FiberBound

/-!
# Appendix I phase-mass accounting: the central charge bridge as a faithful sum

This module refines the central-bridge domination
`absorbedBound + windowBound ≤ ClosurePhaseMass phaseData` — the `habsorb`
hypothesis consumed by `HighExcessChargeData.ofC1VDClosure` (eq. N.24 → I.9) — by
**decomposing `ClosurePhaseMass` into its six explicit phase-mass terms** and
proving the domination from per-term comparisons.

## What is faithful here

* `ClosurePhaseMass_eq_six_terms` — `ClosurePhaseMass` *is* the sum of the six
  phase-mass terms `termChernoff + termCnl + termTower + termDensePack +
  termReturn + termRun`.  This is a definitional identity (`rfl`); it is the
  exact 6-summand structure of the manuscript pressure lower bound.
* `sum_le_phaseMass_of_termBounds` — if six sub-masses are each dominated by the
  matching phase-mass term, their sum is dominated by `ClosurePhaseMass`.  Pure
  linear arithmetic over the summation identity.
* `absorbed_window_le_phaseMass` / `absorbed_window_le_phaseMass_classes` — the
  central bridge: the absorbed five-class mass `𝔒_D/P/E/CNL/bdd` (Lemma N.3.3)
  plus the vanishing variation-drop `𝔒_V` (Lemma N.2.2) dominate
  `ClosurePhaseMass`, proved by the **faithful linear combination** of the six
  per-term comparisons.

## What stays conditional

The six per-term comparisons — `𝔒_D ≤ termDensePack` (Lemma I.4.1),
`𝔒_{P∪E} ≤ termChernoff/termReturn` (Lemma I.4.2, OLC/endpoint leakage),
`𝔒_CNL ≤ termCnl` (clean Kraft CNL tail), `𝔒_bdd ≤ termTower` (Lemma N.3.2),
`𝔒_V ≤ termRun` (Lemma N.2.2) — and the N.3.3 / N.2.2 aggregate-accounting splits
are the genuine analytic content of Appendix I.9 / N.24, supplied here as explicit
hypotheses.  Only the summation and the linear combination are discharged.

The class → phase-term assignment follows the manuscript N.24 accounting (lines
~6602–6633): the terminal non-drop mass is routed by Lemma N.1.0 into the five
priority classes `𝔒_D, 𝔒_P, 𝔒_E, 𝔒_CNL, 𝔒_bdd`, and the window drop `𝔒_V` is
estimated separately (Lemma N.2.2).

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open MeasureTheory Finset

noncomputable section

/-! ## The six phase-mass terms

`ClosurePhaseMass` (see `Erdos260.ClosureFactory`) is the explicit real sum of the
six phase-data masses.  We name each summand so the central-bridge domination can
be expressed term-by-term. -/

/-- Phase-mass term 1 — **Chernoff / high-cost path mass** (`ChernoffPathData`):
the weighted mass of the high-cost path subfamily. -/
def termChernoff {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) : ℝ :=
  weightedMass
    (highCostSet data.chernoff.paths data.chernoff.cost data.chernoff.Y)
    data.chernoff.weight

/-- Phase-mass term 2 — **clean CNL Kraft tail** (`CNLEntropyData`):
the Kraft-weighted clean-CNL exponential tail `∑ 2^{-c·BND} · shellFactor · X · |I_j|`. -/
def termCnl {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) : ℝ :=
  cleanCNLKraftSum data.cnl.paths data.cnl.BNDHeight data.cnl.c *
    data.cnl.shellFactor * X * data.cnl.Ij

/-- Phase-mass term 3 — **tower entry/exit charged mass** (`TowerPackageData`):
the charged weight summed over the transient entry/exit set. -/
def termTower {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) : ℝ :=
  ∑ b ∈ data.tower.entryExitSet, data.tower.chargedWeight b

/-- Phase-mass term 4 — **DensePack point mass** (`DensePackData`):
the cardinality of the dense-pack marker set. -/
def termDensePack {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) : ℝ :=
  (data.densePack.densePackPoints.card : ℝ)

/-- Phase-mass term 5 — **Return package mass** (`ReturnPackageData`):
ordinary-short + semiperiodic + OLC + nonlocal-long return contributions. -/
def termReturn {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) : ℝ :=
  data.returnPkg.ordinaryShort + data.returnPkg.semiperiodic +
    data.returnPkg.olc + data.returnPkg.nonlocalLong

/-- Phase-mass term 6 — **Run package mass** (`RunPackageData`). -/
def termRun {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) : ℝ :=
  data.run.runMass

/-! ## Phase-mass nonnegativity (manuscript §I / J.1.1 charging)

The six phase-mass terms are *masses*.  `termTower` is a sum of nonnegative charged
weights and is therefore unconditionally nonnegative (`TowerPackageData.chargedWeight_nonneg`).
The Tower+Return+Run joint term `termTower + termReturn + termRun` is the right-hand side
of the charge atom's same-threshold (TRT) bound `hTRT`, whose left-hand side is a sum of
window-excess positive parts and hence nonnegative; so the charge atom is *only* inhabitable
for phase data with `0 ≤ termTower + termReturn + termRun`.  Physically the manuscript phase
masses `termReturn`, `termRun` are also nonnegative, so the joint term is always `≥ 0`; the
predicate `trtNonneg` records exactly the nonnegativity needed to admit the charge atom and
to exclude the physically-meaningless negative-mass phase data. -/

/-- **`termTower` is unconditionally nonnegative** — it is a finite sum of the nonnegative
charged weights `TowerPackageData.chargedWeight` (`chargedWeight_nonneg`). -/
theorem termTower_nonneg {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) :
    0 ≤ termTower data := by
  unfold termTower
  exact Finset.sum_nonneg fun b hb => data.tower.chargedWeight_nonneg b hb

/-- **Nonnegativity of the joint Tower+Return+Run phase term.**

`0 ≤ termTower + termReturn + termRun`.  This is exactly the condition the charge atom's
same-threshold bound `hTRT` forces (its left side, a sum of window-excess positive parts,
is `≥ 0`), so it is the natural domain restriction making the per-shell charge field a
total function — excluding the spurious negative-mass phase data while admitting every
genuine (physically nonnegative-mass) phase configuration. -/
def SixPhaseFactoryData.trtNonneg {cStar ξ X : ℝ}
    (phases : SixPhaseFactoryData cStar ξ X) : Prop :=
  0 ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
      + termRun phases.toClosurePhaseData

/-- The induced-phase Return term is definitionally the factory `massSum`. -/
@[simp] theorem termReturn_toClosurePhaseData_eq_massSum {cStar ξ X : ℝ}
    (phases : SixPhaseFactoryData cStar ξ X) :
    termReturn phases.toClosurePhaseData = phases.returnPkg.massSum := rfl

/-- The induced-phase Run term is definitionally the factory `runMass`. -/
@[simp] theorem termRun_toClosurePhaseData_eq_runMass {cStar ξ X : ℝ}
    (phases : SixPhaseFactoryData cStar ξ X) :
    termRun phases.toClosurePhaseData = phases.run.runMass := rfl

/-- **The TRT-nonnegativity holds for any phase data whose Return+Run masses are
nonnegative** (`termTower ≥ 0` is automatic).  This is the discharge used by the
per-shell charge consumers from the manuscript fact that the Return/Run phase masses
are physically nonnegative. -/
theorem SixPhaseFactoryData.trtNonneg_of_returnRun_nonneg {cStar ξ X : ℝ}
    (phases : SixPhaseFactoryData cStar ξ X)
    (h : 0 ≤ phases.returnPkg.massSum + phases.run.runMass) :
    phases.trtNonneg := by
  have hT : 0 ≤ termTower phases.toClosurePhaseData := termTower_nonneg _
  have hRR : termReturn phases.toClosurePhaseData + termRun phases.toClosurePhaseData
      = phases.returnPkg.massSum + phases.run.runMass := rfl
  unfold SixPhaseFactoryData.trtNonneg
  linarith

/-! ## Faithful summation identity -/

/--
**Faithful decomposition of `ClosurePhaseMass`.**

`ClosurePhaseMass data` is, by definition, the ordered sum of the six phase-mass
terms.  This is the exact 6-summand structure of the per-failure pressure lower
bound (`ClosureFactory.ClosurePhaseMass`); the proof is the definitional identity.
-/
theorem ClosurePhaseMass_eq_six_terms {cStar ξ X : ℝ}
    (data : ClosurePhaseData cStar ξ X) :
    ClosurePhaseMass data =
      termChernoff data + termCnl data + termTower data + termDensePack data
        + termReturn data + termRun data :=
  rfl

/--
**Per-term domination ⇒ aggregate domination (faithful summation).**

If six sub-masses are each dominated by the matching phase-mass term, then their
sum is dominated by `ClosurePhaseMass`.  This is pure linear arithmetic over the
summation identity `ClosurePhaseMass_eq_six_terms`; no analytic input is used.
-/
theorem sum_le_phaseMass_of_termBounds {cStar ξ X : ℝ}
    (data : ClosurePhaseData cStar ξ X)
    {mChernoff mCnl mTower mDensePack mReturn mRun : ℝ}
    (hChernoff : mChernoff ≤ termChernoff data)
    (hCnl : mCnl ≤ termCnl data)
    (hTower : mTower ≤ termTower data)
    (hDensePack : mDensePack ≤ termDensePack data)
    (hReturn : mReturn ≤ termReturn data)
    (hRun : mRun ≤ termRun data) :
    mChernoff + mCnl + mTower + mDensePack + mReturn + mRun ≤ ClosurePhaseMass data := by
  rw [ClosurePhaseMass_eq_six_terms]
  linarith

/-! ## The central charge bridge (eq. N.24 → I.9) -/

/--
**Central bridge, additive-split form (faithful summation).**

Given a faithful accounting split of the absorbed-plus-window bound into six
sub-masses, one matched to each phase-mass term, together with the six per-term
comparisons, the absorbed five-class mass plus the vanishing window drop is
dominated by `ClosurePhaseMass`.

The split `hsplit` and the six comparisons are the conditional analytic inputs
(Appendix I.9 / N.24); the conclusion is the faithful linear combination.
-/
theorem absorbed_window_le_phaseMass {cStar ξ X : ℝ}
    (data : ClosurePhaseData cStar ξ X)
    {absorbedBound windowBound : ℝ}
    {mChernoff mCnl mTower mDensePack mReturn mRun : ℝ}
    (hsplit : absorbedBound + windowBound =
      mChernoff + mCnl + mTower + mDensePack + mReturn + mRun)
    (hChernoff : mChernoff ≤ termChernoff data)
    (hCnl : mCnl ≤ termCnl data)
    (hTower : mTower ≤ termTower data)
    (hDensePack : mDensePack ≤ termDensePack data)
    (hReturn : mReturn ≤ termReturn data)
    (hRun : mRun ≤ termRun data) :
    absorbedBound + windowBound ≤ ClosurePhaseMass data := by
  rw [hsplit]
  exact sum_le_phaseMass_of_termBounds data hChernoff hCnl hTower hDensePack hReturn hRun

/--
**Central bridge, manuscript N.24 five-class + drop form (faithful summation).**

This is the manuscript-shaped statement of the bridge.  The absorbed terminal
non-drop mass is split by Lemma N.3.3 into the five priority output classes
`𝔒_D, 𝔒_P, 𝔒_E, 𝔒_CNL, 𝔒_bdd` (`hAbsorbed`), and the variation-drop class `𝔒_V`
is the window bound (`hWindow`, Lemma N.2.2).  The six per-class → phase-term
comparisons realize the N.24 routing (Lemma N.1.0):

* `𝔒_D  ≤ termDensePack` — fixed-layer DensePack estimate (Lemma I.4.1);
* `𝔒_P  ≤ termChernoff`  — progress leakage on the Chernoff high-cost paths;
* `𝔒_E  ≤ termReturn`    — endpoint / OLC leakage (Lemma I.4.2, return package);
* `𝔒_CNL ≤ termCnl`      — clean Kraft-weighted CNL tail;
* `𝔒_bdd ≤ termTower`    — bounded `O_Q(L)`-scale transient (Lemma N.3.2);
* `𝔒_V  ≤ termRun`       — separately-vanishing variation drop (Lemma N.2.2).

The two aggregate splits and the six comparisons are the conditional analytic
inputs; the conclusion `absorbedBound + windowBound ≤ ClosurePhaseMass` is the
faithful linear combination.
-/
theorem absorbed_window_le_phaseMass_classes {cStar ξ X : ℝ}
    (data : ClosurePhaseData cStar ξ X)
    {absorbedBound windowBound : ℝ}
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow : windowBound ≤ O_V)
    (hD : O_D ≤ termDensePack data)
    (hP : O_P ≤ termChernoff data)
    (hE : O_E ≤ termReturn data)
    (hCNL : O_CNL ≤ termCnl data)
    (hbdd : O_bdd ≤ termTower data)
    (hV : O_V ≤ termRun data) :
    absorbedBound + windowBound ≤ ClosurePhaseMass data := by
  rw [ClosurePhaseMass_eq_six_terms]
  linarith

/--
**Central bridge, table-routed non-drop form (faithful summation).**

For the N.5e table-routed path, the variation-drop ledger mass is already zero,
so the phase-mass bridge only has to absorb the five terminal non-drop classes.
The unused run phase stays available as nonnegative slack.  Thus this theorem
needs no `windowBound`, no `O_V`, and no `O_V ≤ termRun` comparison.
-/
theorem absorbed_nonDrop_le_phaseMass_classes {cStar xi X : ℝ}
    (data : ClosurePhaseData cStar xi X)
    {absorbedBound : ℝ}
    {O_D O_P O_E O_CNL O_bdd : ℝ}
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hD : O_D ≤ termDensePack data)
    (hP : O_P ≤ termChernoff data)
    (hE : O_E ≤ termReturn data)
    (hCNL : O_CNL ≤ termCnl data)
    (hbdd : O_bdd ≤ termTower data)
    (hRun_nonneg : 0 ≤ termRun data) :
    absorbedBound ≤ ClosurePhaseMass data := by
  rw [ClosurePhaseMass_eq_six_terms]
  linarith

/-! ## Discharging `HighExcessChargeData.ofC1VDClosure`'s `habsorb`

The lemmas above produce exactly the `habsorb` hypothesis of
`HighExcessChargeData.ofC1VDClosure`.  The two helpers below specialize them to
`phases.toClosurePhaseData` so the parent assembly can plug them straight in. -/

/--
**`habsorb` term, ready for `ofC1VDClosure`.**

This produces the exact proposition
`absorbedBound + windowBound ≤ ClosurePhaseMass phases.toClosurePhaseData`
required by `HighExcessChargeData.ofC1VDClosure` (and
`PerFailureAssemblyData.ofC1VDClosure`), built from the manuscript N.24 five-class
absorption + `𝔒_V` window drop and the six per-term comparisons. -/
theorem habsorb_ofC1VDClosure {cStar ξ X : ℝ}
    (phases : SixPhaseFactoryData cStar ξ X)
    {absorbedBound windowBound : ℝ}
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow : windowBound ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hP : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    absorbedBound + windowBound ≤ ClosurePhaseMass phases.toClosurePhaseData :=
  absorbed_window_le_phaseMass_classes phases.toClosurePhaseData
    hAbsorbed hWindow hD hP hE hCNL hbdd hV

/--
**`habsorb` term, bundled window-drop form.**

This is the phase-mass comparison needed by
`HighExcessChargeData.ofC1VDClosure_windowDrop`: the N.2.2 window contribution is
read directly from the `WindowDropEstimateData` bundle.
-/
theorem habsorb_ofC1VDClosure_windowDrop {cStar ξ X : ℝ}
    (phases : SixPhaseFactoryData cStar ξ X)
    (drop : AppendixN.WindowDropEstimateData)
    {absorbedBound : ℝ}
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow : drop.CQ * drop.Y * AppendixN.Vs drop.K drop.W ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hP : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    absorbedBound + drop.CQ * drop.Y * AppendixN.Vs drop.K drop.W ≤
      ClosurePhaseMass phases.toClosurePhaseData :=
  habsorb_ofC1VDClosure phases hAbsorbed hWindow hD hP hE hCNL hbdd hV

/--
**`habsorb` term, table-routed no-drop form.**

This produces the exact proposition
`absorbedBound ≤ ClosurePhaseMass phases.toClosurePhaseData` required by
`HighExcessChargeData.ofTableRoutedC1VDClosure`, using only the five non-drop
output classes and nonnegativity of the unused run phase.
-/
theorem habsorb_ofTableRoutedC1VDClosure {cStar xi X : ℝ}
    (phases : SixPhaseFactoryData cStar xi X)
    {absorbedBound : ℝ}
    {O_D O_P O_E O_CNL O_bdd : ℝ}
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hP : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hRun_nonneg : 0 ≤ termRun phases.toClosurePhaseData) :
    absorbedBound ≤ ClosurePhaseMass phases.toClosurePhaseData :=
  absorbed_nonDrop_le_phaseMass_classes phases.toClosurePhaseData
    hAbsorbed hD hP hE hCNL hbdd hRun_nonneg

/--
**Phase-E central-charge data via the six-term phase-mass accounting.**

A drop-in for `HighExcessChargeData.ofC1VDClosure` whose `habsorb` hypothesis is
replaced by the faithful six-term phase-mass accounting: the analytic content is
exposed as the N.3.3 five-class absorption (`hAbsorbed`), the N.2.2 window drop
(`hWindow`), and the six per-term comparisons, and the summation that builds
`habsorb` is discharged here.  The other inputs (`hHighExcess_eq`, `hsplit`,
`hterm`, `hvar`) are forwarded unchanged. -/
def HighExcessChargeData.ofC1VDClosure_phaseMass
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass varMass absorbedBound windowBound : ℝ)
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + varMass)
    (hterm : termMass ≤ absorbedBound)
    (hvar : varMass ≤ windowBound)
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow : windowBound ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hP : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  HighExcessChargeData.ofC1VDClosure phases carryData
    totalMass termMass varMass absorbedBound windowBound
    hHighExcess_eq hsplit hterm hvar
    (habsorb_ofC1VDClosure phases hAbsorbed hWindow hD hP hE hCNL hbdd hV)

/--
**Phase-E central-charge data via phase-mass accounting, with faithful I.9
reindexing discharged.**

The remaining I.9 input is only the ledger equality identifying the stopped
branch weighted mass with the composed TRT `totalMass`; the analytic
high-excess-to-branch reindexing is supplied by `StoppedTreeIndex`.
-/
def HighExcessChargeData.ofC1VDClosure_phaseMass_branchMass
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass varMass absorbedBound windowBound : ℝ)
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
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
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow : windowBound ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hP : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  HighExcessChargeData.ofC1VDClosure_branchMass phases carryData
    totalMass termMass varMass absorbedBound windowBound
    hBranchMass_eq hsplit hterm hvar
    (habsorb_ofC1VDClosure phases hAbsorbed hWindow hD hP hE hCNL hbdd hV)

/--
**Phase-E central-charge data via bundled N.2.2 and six-term phase accounting.**

This variant consumes a `WindowDropEstimateData` bundle directly, so the N.2.2
proof object produced by Appendix N.2 can be passed through N.24 into the central
charge bridge without unpacking it into a separate `varMass ≤ windowBound`
hypothesis.
-/
def HighExcessChargeData.ofC1VDClosure_phaseMass_windowDrop
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (drop : AppendixN.WindowDropEstimateData)
    (totalMass termMass absorbedBound : ℝ)
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + drop.varDrop)
    (hterm : termMass ≤ absorbedBound)
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow : drop.CQ * drop.Y * AppendixN.Vs drop.K drop.W ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hP : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  HighExcessChargeData.ofC1VDClosure_windowDrop phases carryData drop
    totalMass termMass absorbedBound hHighExcess_eq hsplit hterm
    (habsorb_ofC1VDClosure_windowDrop phases drop hAbsorbed hWindow
      hD hP hE hCNL hbdd hV)

/--
**Phase-E central-charge data via bundled N.2.2 and phase-mass accounting, with
faithful I.9 reindexing discharged.**
-/
def HighExcessChargeData.ofC1VDClosure_phaseMass_windowDrop_branchMass
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (drop : AppendixN.WindowDropEstimateData)
    (totalMass termMass absorbedBound : ℝ)
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
    (hBranchMass_eq :
      branchWeightedMass
          ((highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y).image
              (stoppedBranchOf carryData.a carryData.r))
          (windowExcessWeight carryData.T)
        = totalMass)
    (hsplit : totalMass = termMass + drop.varDrop)
    (hterm : termMass ≤ absorbedBound)
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow : drop.CQ * drop.Y * AppendixN.Vs drop.K drop.W ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hP : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  HighExcessChargeData.ofC1VDClosure_windowDrop_branchMass phases carryData drop
    totalMass termMass absorbedBound hBranchMass_eq hsplit hterm
    (habsorb_ofC1VDClosure_windowDrop phases drop hAbsorbed hWindow
      hD hP hE hCNL hbdd hV)

/--
**Phase-E per-failure assembly via bundled N.2.2 and six-term phase accounting.**
-/
def PerFailureAssemblyData.ofC1VDClosure_phaseMass_windowDrop
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (drop : AppendixN.WindowDropEstimateData)
    (totalMass termMass absorbedBound : ℝ)
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + drop.varDrop)
    (hterm : termMass ≤ absorbedBound)
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow : drop.CQ * drop.Y * AppendixN.Vs drop.K drop.W ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hP : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_phaseMass_windowDrop phases carryData drop
      totalMass termMass absorbedBound hHighExcess_eq hsplit hterm
      hAbsorbed hWindow hD hP hE hCNL hbdd hV)

/--
**Phase-E per-failure assembly via bundled N.2.2 and phase-mass accounting, with
faithful I.9 reindexing discharged.**
-/
def PerFailureAssemblyData.ofC1VDClosure_phaseMass_windowDrop_branchMass
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (drop : AppendixN.WindowDropEstimateData)
    (totalMass termMass absorbedBound : ℝ)
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
    (hBranchMass_eq :
      branchWeightedMass
          ((highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y).image
              (stoppedBranchOf carryData.a carryData.r))
          (windowExcessWeight carryData.T)
        = totalMass)
    (hsplit : totalMass = termMass + drop.varDrop)
    (hterm : termMass ≤ absorbedBound)
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow : drop.CQ * drop.Y * AppendixN.Vs drop.K drop.W ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hP : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_phaseMass_windowDrop_branchMass
      phases carryData drop totalMass termMass absorbedBound hBranchMass_eq
      hsplit hterm hAbsorbed hWindow hD hP hE hCNL hbdd hV)

/--
**Phase-E central-charge data from reduced-record N.2.1 density.**

This is the direct composition of the reduced-record N.2.1 fibre bound, the
N.2.2 drop-density integration bridge, the N.24 C1-VD split, and the six-term
phase-mass accounting.  The remaining hypotheses are the honest geometric /
analytic leaves: priority-atom coincidence, density integrability and residual
multiplier domination, I.9 mass identification, terminal absorption, and the
per-class phase comparisons.
-/
def HighExcessChargeData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity
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
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
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
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y * AppendixN.Vs K W ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hP : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  let drop :=
    AppendixN.WindowDropEstimateData.ofLowerLabelRecordPriorityOfRecordDensity
      VarDrop Cmul Y D branches dropDensity dropMass hdrop_nonneg crossingIndic
      hindic_nonneg hlift_le support hsupp hzero hle hinj K W A hCmulY hA
      hdrop_int hvar hdensity hindic
  HighExcessChargeData.ofC1VDClosure_phaseMass_windowDrop phases carryData drop
    totalMass termMass absorbedBound hHighExcess_eq
    (by simpa [drop,
      AppendixN.WindowDropEstimateData.ofLowerLabelRecordPriorityOfRecordDensity,
      AppendixN.WindowDropEstimateData.ofScaledDropDensityBound] using hsplit)
    hterm hAbsorbed
    (by simpa [drop,
      AppendixN.WindowDropEstimateData.ofLowerLabelRecordPriorityOfRecordDensity,
      AppendixN.WindowDropEstimateData.ofScaledDropDensityBound] using hWindow)
    hD hP hE hCNL hbdd hV

/--
**Phase-E per-failure assembly from reduced-record N.2.1 density.**
-/
def PerFailureAssemblyData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity
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
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
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
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y * AppendixN.Vs K W ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hP : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity
      phases carryData VarDrop Cmul Y D branches dropDensity dropMass hdrop_nonneg
      crossingIndic hindic_nonneg hlift_le support hsupp hzero hle hinj K W A
      totalMass termMass absorbedBound hHighExcess_eq hsplit hterm hCmulY hA
      hdrop_int hvar hdensity hindic hAbsorbed hWindow hD hP hE hCNL hbdd hV)

/--
**Phase-E central-charge data from reduced-record density, with explicit N.13
variation bound.**

The caller supplies the phase comparison only for the explicit
`2M|K|` window bound; the Lean proof derives the corresponding `Vs` comparison
using `scaled_windowTerm_le_explicit_windowBound`.
-/
def HighExcessChargeData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity_explicitWindow
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
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
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
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * M * (K.card : ℝ)) ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hP : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
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
    HighExcessChargeData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity
      phases carryData VarDrop Cmul Y D branches dropDensity dropMass hdrop_nonneg
      crossingIndic hindic_nonneg hlift_le support hsupp hzero hle hinj K
      (AppendixN.windowSum g s) A totalMass termMass absorbedBound
      hHighExcess_eq hsplit hterm hCmulY hA hdrop_int hvar hdensity hindic
      hAbsorbed hWindowVs hD hP hE hCNL hbdd hV

/--
**Phase-E per-failure assembly from reduced-record density, with explicit N.13
variation bound.**
-/
def PerFailureAssemblyData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity_explicitWindow
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
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
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
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * M * (K.card : ℝ)) ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hP : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity_explicitWindow
      phases carryData VarDrop Cmul Y M D branches dropDensity dropMass
      hdrop_nonneg crossingIndic hindic_nonneg hlift_le support hsupp hzero hle hinj
      g s K A totalMass termMass absorbedBound hHighExcess_eq hsplit hterm hCmulY
      hA hdrop_int hvar hdensity hindic hg hKidx hMlo hMhi
      hAbsorbed hWindow hD hP hE hCNL hbdd hV)

/--
**Phase-E central-charge data from reduced-record density for the real hit-gap
sequence.**

This is the hit-gap-specialized wrapper around the explicit-window constructor:
the local N.13 hypotheses are discharged by
`HitSequence.hitGap_le_of_shell_window`.
-/
def HighExcessChargeData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity_hitGap
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
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
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
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * ((L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hP : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  HighExcessChargeData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity_explicitWindow
    phases carryData VarDrop Cmul Y ((L + B + 1 : ℕ) : ℝ) D branches
    dropDensity dropMass hdrop_nonneg crossingIndic hindic_nonneg hlift_le
    support hsupp hzero hle hinj (fun n => (hitGap a n : ℝ)) s K A
    totalMass termMass absorbedBound hHighExcess_eq hsplit hterm hCmulY hA
    hdrop_int hvar hdensity hindic (fun n => Nat.cast_nonneg _)
    hK
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
    hAbsorbed hWindow hD hP hE hCNL hbdd hV

/--
**Phase-E per-failure assembly from reduced-record density for the real hit-gap
sequence.**
-/
def PerFailureAssemblyData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity_hitGap
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
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
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
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * ((L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hP : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity_hitGap
      hd hseq hQden heta hX_eq hX_pos hB hKr phases carryData VarDrop Cmul Y
      D branches dropDensity dropMass hdrop_nonneg crossingIndic hindic_nonneg
      hlift_le support hsupp hzero hle hinj s K A totalMass termMass absorbedBound
      hHighExcess_eq hsplit hterm hK hKwin hCmulY hA hdrop_int hvar hdensity hindic
      hAbsorbed hWindow hD hP hE hCNL hbdd hV)

/--
**Phase-E central-charge data from carry-packaged hit-gap data.**

This is the consumer-facing version of
`HighExcessChargeData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity_hitGap`:
the binary word, hit sequence, denominator, shell size, and recurrence length
are read from `shell` and `carryData`.
-/
def HighExcessChargeData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity_carryHitGap
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
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
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
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hPterm : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
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
    HighExcessChargeData.ofC1VDClosure_phaseMass phases carryData
      totalMass termMass VarDrop absorbedBound
      ((Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
        (2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)))
      hHighExcess_eq hsplit hterm hvarDrop hAbsorbed hWindow
      hD hPterm hE hCNL hbdd hV

/--
**Phase-E central-charge data from carry-packaged hit-gap data, with faithful
I.9 reindexing discharged.**
-/
def HighExcessChargeData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity_carryHitGap_branchMass
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
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
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
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hPterm : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
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
    HighExcessChargeData.ofC1VDClosure_phaseMass_branchMass phases carryData
      totalMass termMass VarDrop absorbedBound
      ((Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
        (2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)))
      hBranchMass_eq hsplit hterm hvarDrop hAbsorbed hWindow
      hD hPterm hE hCNL hbdd hV

/--
**Phase-E per-failure assembly from carry-packaged hit-gap data.**
-/
def PerFailureAssemblyData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity_carryHitGap
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
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
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
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hPterm : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity_carryHitGap
      phases carryData hP hX_eq hX_pos hB hKr VarDrop Cmul Y D branches
      dropDensity dropMass hdrop_nonneg crossingIndic hindic_nonneg hlift_le
      support hsupp hzero hle hinj s K A totalMass termMass absorbedBound
      hHighExcess_eq hsplit hterm hK hKwin hCmulY hA hdrop_int hvar hdensity
      hindic hAbsorbed hWindow hD hPterm hE hCNL hbdd hV)

/--
**Phase-E per-failure assembly from carry-packaged hit-gap data, with faithful
I.9 reindexing discharged.**
-/
def PerFailureAssemblyData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity_carryHitGap_branchMass
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
    {O_D O_P O_E O_CNL O_bdd O_V : ℝ}
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
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hWindow :
      (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) ≤ O_V)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hPterm : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hV : O_V ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_phaseMass_lowerLabelRecordDensity_carryHitGap_branchMass
      phases carryData hP hX_eq hX_pos hB hKr VarDrop Cmul Y D branches
      dropDensity dropMass hdrop_nonneg crossingIndic hindic_nonneg hlift_le
      support hsupp hzero hle hinj s K A totalMass termMass absorbedBound
      hBranchMass_eq hsplit hterm hK hKwin hCmulY hA hdrop_int hvar hdensity
      hindic hAbsorbed hWindow hD hPterm hE hCNL hbdd hV)

/--
**Phase-E table-routed central-charge data via five-class phase accounting.**

This is the table-routed counterpart of
`HighExcessChargeData.ofC1VDClosure_phaseMass`: the variation-drop branch has
already vanished in the ledger, so the phase-mass accounting exposes only the
five terminal non-drop class comparisons plus `0 ≤ termRun` slack.
-/
def HighExcessChargeData.ofTableRoutedC1VDClosure_phaseMass
    {sigma iota : Type*} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota)
    (row : iota → AppendixN.TerminalRow) (supp thr : iota → Nat)
    (weight : OutputObjectV4 → ℝ)
    {shell : FailingDyadicShell} {cPr cStar xi : ℝ}
    (phases : SixPhaseFactoryData cStar xi (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass absorbedBound : ℝ)
    {O_D O_P O_E O_CNL O_bdd : ℝ}
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
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hP : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hRun_nonneg : 0 ≤ termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  HighExcessChargeData.ofTableRoutedC1VDClosure E row supp thr weight phases carryData
    totalMass termMass absorbedBound hHighExcess_eq hsplit hterm
    (habsorb_ofTableRoutedC1VDClosure phases
      hAbsorbed hD hP hE hCNL hbdd hRun_nonneg)

/--
**Phase-E table-routed per-failure assembly via five-class phase accounting.**
-/
def PerFailureAssemblyData.ofTableRoutedC1VDClosure_phaseMass
    {sigma iota : Type*} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota)
    (row : iota → AppendixN.TerminalRow) (supp thr : iota → Nat)
    (weight : OutputObjectV4 → ℝ)
    {shell : FailingDyadicShell} {cPr cStar xi : ℝ}
    (phases : SixPhaseFactoryData cStar xi (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass absorbedBound : ℝ)
    {O_D O_P O_E O_CNL O_bdd : ℝ}
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
    (hAbsorbed : absorbedBound ≤ O_D + O_P + O_E + O_CNL + O_bdd)
    (hD : O_D ≤ termDensePack phases.toClosurePhaseData)
    (hP : O_P ≤ termChernoff phases.toClosurePhaseData)
    (hE : O_E ≤ termReturn phases.toClosurePhaseData)
    (hCNL : O_CNL ≤ termCnl phases.toClosurePhaseData)
    (hbdd : O_bdd ≤ termTower phases.toClosurePhaseData)
    (hRun_nonneg : 0 ≤ termRun phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar xi shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofTableRoutedC1VDClosure_phaseMass E row supp thr weight
      phases carryData totalMass termMass absorbedBound hHighExcess_eq hsplit hterm
      hAbsorbed hD hP hE hCNL hbdd hRun_nonneg)

/-! ## I.6 joint package closure against the phase-mass terms

Re-expressing Proposition I.6 (`AppendixI.propositionI6_jointPackageClosure`)
against the four "package" phase-mass terms (tower, return, run, DensePack): if
each is individually bounded by the joint-closure rate `C·ξ·s·X·|I_j| + ε/4`,
their sum obeys the I.6 joint estimate `(C_T+C_R+C_Run+C_D)·ξ·s·X·|I_j| + ε`. -/

/--
**I.6 joint package closure, phase-term form.**

The aggregate of the four package phase-mass terms `termTower + termReturn +
termRun + termDensePack` satisfies the manuscript I.6 joint estimate.  This is
exactly `propositionI6_jointPackageClosure` instantiated at the phase-mass terms;
the four per-package bounds are the I.3.1 / I.4.1 / I.5.1 / I.5.2 analytic inputs. -/
theorem phasePackageMass_le_jointClosure {cStar ξ X : ℝ}
    (data : ClosurePhaseData cStar ξ X)
    {CT CR CRun CD ζ s W Ij smallError : ℝ}
    (hT : termTower data ≤ CT * ζ * s * W * Ij + smallError / 4)
    (hR : termReturn data ≤ CR * ζ * s * W * Ij + smallError / 4)
    (hRun : termRun data ≤ CRun * ζ * s * W * Ij + smallError / 4)
    (hD : termDensePack data ≤ CD * ζ * s * W * Ij + smallError / 4) :
    termTower data + termReturn data + termRun data + termDensePack data ≤
      (CT + CR + CRun + CD) * ζ * s * W * Ij + smallError :=
  propositionI6_jointPackageClosure hT hR hRun hD

end

end Erdos260
