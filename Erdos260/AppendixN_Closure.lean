import Mathlib
import Erdos260.AppendixN_Compression
import Erdos260.AppendixI
import Erdos260.HighExcessChargeFactory
import Erdos260.StoppedTreeIndex

/-!
# Phase E wiring: C1-VD closure and finite descent → central charge bridge

This module wires the Appendix N C1-VD closure (Theorem `thm:trt-chain-compression`)
and the Appendix I.7–I.10 finite descent into the central charge bridge
`HighExcessChargeData.highExcess_le_phaseMass` — the P9 obligation
`highExcessMass ... ≤ ClosurePhaseMass phaseData`.

The manuscript's global recurrence (I.9) identifies the stopped high-excess mass
with the composed same-threshold Return–Run–Tower output mass, which the C1-VD
closure splits (Lemma N.1.0 / N.3.3) into the terminal non-drop mass — absorbed
into the five output classes `𝔒_D/P/E/CNL/bdd` — plus the separately-vanishing
variation-drop mass `𝔒_V` (Lemma N.2.2).  `HighExcessChargeData.ofC1VDClosure`
realizes this split via `AppendixN.trtClosure_outputMass_absorbed` and discharges
the P9 bridge from it; `PerFailureAssemblyData.ofC1VDClosure` then carries it all
the way to a per-failure assembly (hence to `GlobalAssemblyInputs.highExcessCharge`
and `erdos260_final`).

The *mechanism* (the C1-VD split + absorption) is now explicit Lean.  The
remaining inputs are the deep analytic content, kept as honest hypotheses: the
Appendix-I.9 identifications (`highExcessMass = composed-TRT mass`,
`absorbed + drop ≤ ClosurePhaseMass`) and the N.2.2 / N.3.3 per-class bounds.
This is the v4 replacement, as the closure mechanism, of the old same-threshold
compression route (`no_feedback_at_threshold_layer` / `finiteDescent_le`).

`HighExcessChargeData.ofFiniteDescent` gives the complementary **descent route**:
the faithful `M`-step telescoping descent `finiteDescent_le` (Appendix I.7–I.10)
yields `𝒜₀ ≤ ∑_{k<M} C_η^k · b k` from the per-level truncated recurrences
(Prop. I.2.1 / I.6) and the terminal nullification (I.10); identifying the
order-`0` high-excess mass with `𝒜₀` (I.9) and the geometric error sum with the
phase masses then discharges the same central bridge.  The descent *assembly* is
faithful (it is `finiteDescent_le`); the per-level recurrences, the terminal
nullification, and the two identifications are the conditional analytic leaves.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

noncomputable section

/--
**Phase E wiring (eq. N.24 / 2.3b → I.9): the C1-VD closure discharges the
central charge bridge.**

Given a failing shell's `carryData`, the six phase factories, and the C1-VD
output split, `AppendixN.trtClosure_outputMass_absorbed` yields
`highExcessMass ... ≤ ClosurePhaseMass`, hence a full `HighExcessChargeData`.

Conditional inputs (the deep manuscript content, supplied as hypotheses):
* `hHighExcess_eq` — I.9: the stopped high-excess mass equals the composed
  same-threshold TRT output mass `totalMass`;
* `hsplit` — the C1-VD output split `totalMass = termMass (non-drop) + varMass (𝔒_V)`;
* `hterm` — Lemma N.3.3 aggregate absorption `termMass ≤ absorbedBound`;
* `hvar` — Lemma N.2.2 window-drop `varMass ≤ windowBound`;
* `habsorb` — the absorbed five-class bound plus the vanishing drop dominate the
  phase masses: `absorbedBound + windowBound ≤ ClosurePhaseMass`.
-/
def HighExcessChargeData.ofC1VDClosure
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass varMass absorbedBound windowBound : ℝ)
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + varMass)
    (hterm : termMass ≤ absorbedBound)
    (hvar : varMass ≤ windowBound)
    (habsorb :
      absorbedBound + windowBound ≤ ClosurePhaseMass phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData where
  highExcess_le_phaseMass := by
    rw [hHighExcess_eq]
    exact (AppendixN.trtClosure_outputMass_absorbed hsplit hterm hvar).trans habsorb

/--
**Phase E wiring with the faithful I.9 branch reindexing discharged.**

This replaces the monolithic `hHighExcess_eq` input of
`HighExcessChargeData.ofC1VDClosure` by the remaining ledger identification:
the stopped-branch mass built from `carryData` equals the composed TRT
`totalMass`.  The analytic high-excess side is then supplied by
`CarryDataFromFailure.highExcessMass_eq_branchWeightedMass`.
-/
def HighExcessChargeData.ofC1VDClosure_branchMass
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass varMass absorbedBound windowBound : ℝ)
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
    (habsorb :
      absorbedBound + windowBound ≤ ClosurePhaseMass phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  HighExcessChargeData.ofC1VDClosure phases carryData
    totalMass termMass varMass absorbedBound windowBound
    (carryData.highExcessMass_eq_of_branchWeightedMass_eq hBranchMass_eq)
    hsplit hterm hvar habsorb

/--
**Phase E wiring, bundled window-drop form.**

This specializes `HighExcessChargeData.ofC1VDClosure` to the structured N.2.2
input produced by `WindowDropEstimateData`.  The C1-VD split identifies the
variation-drop summand with `drop.varDrop`; the window-drop proof is then read
from the bundle, rather than supplied as a separate `hvar`/`windowBound` pair.
-/
def HighExcessChargeData.ofC1VDClosure_windowDrop
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (drop : AppendixN.WindowDropEstimateData)
    (totalMass termMass absorbedBound : ℝ)
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + drop.varDrop)
    (hterm : termMass ≤ absorbedBound)
    (habsorb :
      absorbedBound + drop.CQ * drop.Y * AppendixN.Vs drop.K drop.W ≤
        ClosurePhaseMass phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData where
  highExcess_le_phaseMass := by
    rw [hHighExcess_eq]
    exact
      (AppendixN.trtClosure_windowDropEstimate_absorbed drop hsplit hterm).trans
        habsorb

/--
**Phase E wiring, bundled window-drop form, with faithful I.9 reindexing
discharged.**
-/
def HighExcessChargeData.ofC1VDClosure_windowDrop_branchMass
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (drop : AppendixN.WindowDropEstimateData)
    (totalMass termMass absorbedBound : ℝ)
    (hBranchMass_eq :
      branchWeightedMass
          ((highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y).image
              (stoppedBranchOf carryData.a carryData.r))
          (windowExcessWeight carryData.T)
        = totalMass)
    (hsplit : totalMass = termMass + drop.varDrop)
    (hterm : termMass ≤ absorbedBound)
    (habsorb :
      absorbedBound + drop.CQ * drop.Y * AppendixN.Vs drop.K drop.W ≤
        ClosurePhaseMass phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  HighExcessChargeData.ofC1VDClosure_windowDrop phases carryData drop
    totalMass termMass absorbedBound
    (carryData.highExcessMass_eq_of_branchWeightedMass_eq hBranchMass_eq)
    hsplit hterm habsorb

/--
**Phase E wiring, table-routed no-drop form.**

When the C1-VD output family is explicitly drawn from the N.5e terminal routing
table, the variation-drop ledger mass is zero by
`AppendixN.trtClosure_tableRouted_absorbed`.  This constructor therefore needs
only the I.9 identification, the terminal non-drop absorption bound, and the
comparison of that absorbed bound with `ClosurePhaseMass`.
-/
def HighExcessChargeData.ofTableRoutedC1VDClosure
    {sigma iota : Type*} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota)
    (row : iota → AppendixN.TerminalRow) (supp thr : iota → Nat)
    (weight : OutputObjectV4 → ℝ)
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass absorbedBound : ℝ)
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
    (habsorb : absorbedBound ≤ ClosurePhaseMass phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData where
  highExcess_le_phaseMass := by
    rw [hHighExcess_eq]
    exact
      (AppendixN.trtClosure_tableRouted_absorbed E row supp thr weight hsplit hterm).trans
        habsorb

/--
**Phase E wiring, table-routed no-drop form, with faithful I.9 reindexing
discharged.**
-/
def HighExcessChargeData.ofTableRoutedC1VDClosure_branchMass
    {sigma iota : Type*} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota)
    (row : iota → AppendixN.TerminalRow) (supp thr : iota → Nat)
    (weight : OutputObjectV4 → ℝ)
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass absorbedBound : ℝ)
    (hBranchMass_eq :
      branchWeightedMass
          ((highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y).image
              (stoppedBranchOf carryData.a carryData.r))
          (windowExcessWeight carryData.T)
        = totalMass)
    (hsplit :
      totalMass =
        termMass +
          variationDropMass
            (E.atoms.image
              (fun omega =>
                OutputObjectV4.mk (row omega).outputClass (supp omega) (thr omega)))
            weight)
    (hterm : termMass ≤ absorbedBound)
    (habsorb : absorbedBound ≤ ClosurePhaseMass phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  HighExcessChargeData.ofTableRoutedC1VDClosure E row supp thr weight phases carryData
    totalMass termMass absorbedBound
    (carryData.highExcessMass_eq_of_branchWeightedMass_eq hBranchMass_eq)
    hsplit hterm habsorb

/--
**Phase E wiring, full chain.**  The C1-VD closure carried all the way to a
per-failure assembly: `C1-VD split → HighExcessChargeData → PerFailureAssemblyData`.
Composed through `GlobalClosureAssembly`, this is the v4 route by which the
Appendix N closure feeds `GlobalAssemblyInputs.highExcessCharge` and the final
target `erdos260_final` (modulo the conditional I.9 / N.2.2 / N.3.3 inputs). -/
def PerFailureAssemblyData.ofC1VDClosure
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass varMass absorbedBound windowBound : ℝ)
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + varMass)
    (hterm : termMass ≤ absorbedBound)
    (hvar : varMass ≤ windowBound)
    (habsorb :
      absorbedBound + windowBound ≤ ClosurePhaseMass phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure phases carryData
      totalMass termMass varMass absorbedBound windowBound
      hHighExcess_eq hsplit hterm hvar habsorb)

/--
**Phase E wiring, full chain, with faithful I.9 reindexing discharged.**
-/
def PerFailureAssemblyData.ofC1VDClosure_branchMass
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass varMass absorbedBound windowBound : ℝ)
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
    (habsorb :
      absorbedBound + windowBound ≤ ClosurePhaseMass phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_branchMass phases carryData
      totalMass termMass varMass absorbedBound windowBound hBranchMass_eq
      hsplit hterm hvar habsorb)

/--
**Phase E wiring, full chain, bundled window-drop form.**
-/
def PerFailureAssemblyData.ofC1VDClosure_windowDrop
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (drop : AppendixN.WindowDropEstimateData)
    (totalMass termMass absorbedBound : ℝ)
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = totalMass)
    (hsplit : totalMass = termMass + drop.varDrop)
    (hterm : termMass ≤ absorbedBound)
    (habsorb :
      absorbedBound + drop.CQ * drop.Y * AppendixN.Vs drop.K drop.W ≤
        ClosurePhaseMass phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_windowDrop phases carryData drop
      totalMass termMass absorbedBound hHighExcess_eq hsplit hterm habsorb)

/--
**Phase E wiring, full chain, bundled window-drop form, with faithful I.9
reindexing discharged.**
-/
def PerFailureAssemblyData.ofC1VDClosure_windowDrop_branchMass
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (drop : AppendixN.WindowDropEstimateData)
    (totalMass termMass absorbedBound : ℝ)
    (hBranchMass_eq :
      branchWeightedMass
          ((highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y).image
              (stoppedBranchOf carryData.a carryData.r))
          (windowExcessWeight carryData.T)
        = totalMass)
    (hsplit : totalMass = termMass + drop.varDrop)
    (hterm : termMass ≤ absorbedBound)
    (habsorb :
      absorbedBound + drop.CQ * drop.Y * AppendixN.Vs drop.K drop.W ≤
        ClosurePhaseMass phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofC1VDClosure_windowDrop_branchMass phases carryData drop
      totalMass termMass absorbedBound hBranchMass_eq hsplit hterm habsorb)

/--
**Phase E wiring, full chain, table-routed no-drop form.**  This is the
per-failure assembly constructor corresponding to
`HighExcessChargeData.ofTableRoutedC1VDClosure`.
-/
def PerFailureAssemblyData.ofTableRoutedC1VDClosure
    {sigma iota : Type*} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota)
    (row : iota → AppendixN.TerminalRow) (supp thr : iota → Nat)
    (weight : OutputObjectV4 → ℝ)
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass absorbedBound : ℝ)
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
    (habsorb : absorbedBound ≤ ClosurePhaseMass phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofTableRoutedC1VDClosure E row supp thr weight phases carryData
      totalMass termMass absorbedBound hHighExcess_eq hsplit hterm habsorb)

/--
**Phase E wiring, full chain, table-routed no-drop form, with faithful I.9
reindexing discharged.**
-/
def PerFailureAssemblyData.ofTableRoutedC1VDClosure_branchMass
    {sigma iota : Type*} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota)
    (row : iota → AppendixN.TerminalRow) (supp thr : iota → Nat)
    (weight : OutputObjectV4 → ℝ)
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (totalMass termMass absorbedBound : ℝ)
    (hBranchMass_eq :
      branchWeightedMass
          ((highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y).image
              (stoppedBranchOf carryData.a carryData.r))
          (windowExcessWeight carryData.T)
        = totalMass)
    (hsplit :
      totalMass =
        termMass +
          variationDropMass
            (E.atoms.image
              (fun omega =>
                OutputObjectV4.mk (row omega).outputClass (supp omega) (thr omega)))
            weight)
    (hterm : termMass ≤ absorbedBound)
    (habsorb : absorbedBound ≤ ClosurePhaseMass phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofTableRoutedC1VDClosure_branchMass E row supp thr weight
      phases carryData totalMass termMass absorbedBound hBranchMass_eq hsplit hterm habsorb)

/--
**Phase E wiring (Appendix I.7–I.10 descent route): finite descent discharges the
central charge bridge.**

The faithful `M`-step telescoping descent `finiteDescent_le` yields
`𝒜 0 ≤ ∑_{k<M} C_η^k · b k`; identifying the order-`0` high-excess mass with
`𝒜 0` (I.9) and bounding the geometric error sum by the phase masses gives the
central bridge `highExcessMass ... ≤ ClosurePhaseMass`, hence a full
`HighExcessChargeData`.

Conditional inputs (the deep manuscript content, supplied as hypotheses):
* `hstep` — the per-level truncated charged recurrence
  `𝒜 k ≤ C_η · 𝒜 (k+1) + b k` (Prop. I.2.1 substituted with the I.6 joint
  package closure);
* `hterminal` — I.10 terminal nullification `𝒜 M ≤ 0`;
* `hHighExcess_eq` — I.9: the order-`0` high-excess mass equals `𝒜 0`;
* `hSum_le` — the geometric error sum is dominated by the six phase masses
  `∑_{k<M} C_η^k · b k ≤ ClosurePhaseMass`.

The descent *assembly* itself is unconditional (`finiteDescent_le`). -/
def HighExcessChargeData.ofFiniteDescent
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (𝒜 b : ℕ → ℝ) (Cη : ℝ) (M : ℕ)
    (hCη_nonneg : 0 ≤ Cη)
    (hstep : ∀ k, 𝒜 k ≤ Cη * 𝒜 (k + 1) + b k)
    (hterminal : 𝒜 M ≤ 0)
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = 𝒜 0)
    (hSum_le :
      (∑ k ∈ Finset.range M, Cη ^ k * b k) ≤
        ClosurePhaseMass phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData where
  highExcess_le_phaseMass := by
    rw [hHighExcess_eq]
    exact (finiteDescent_le hCη_nonneg hstep hterminal).trans hSum_le

/--
**Phase E wiring, full chain (descent route).**  The I.7–I.10 finite descent
carried all the way to a per-failure assembly, complementing
`PerFailureAssemblyData.ofC1VDClosure`. -/
def PerFailureAssemblyData.ofFiniteDescent
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (𝒜 b : ℕ → ℝ) (Cη : ℝ) (M : ℕ)
    (hCη_nonneg : 0 ≤ Cη)
    (hstep : ∀ k, 𝒜 k ≤ Cη * 𝒜 (k + 1) + b k)
    (hterminal : 𝒜 M ≤ 0)
    (hHighExcess_eq :
      highExcessMass
          (highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T = 𝒜 0)
    (hSum_le :
      (∑ k ∈ Finset.range M, Cη ^ k * b k) ≤
        ClosurePhaseMass phases.toClosurePhaseData) :
    PerFailureAssemblyData cPr cStar ξ shell.X :=
  PerFailureAssemblyData.ofHighExcessCharge phases carryData
    (HighExcessChargeData.ofFiniteDescent phases carryData
      𝒜 b Cη M hCη_nonneg hstep hterminal hHighExcess_eq hSum_le)

end

end Erdos260
