import Mathlib
import Erdos260.ChargeBridgeReduction
import Erdos260.AppendixN_Compression
import Erdos260.AppendixI_PackageBounds

/-!
# Joint Tower+Return+Run (TRT) charge bound — the v5 `hTRT` charge-bridge contract

This module formalizes the **joint** Tower+Return+Run charge estimate that
discharges the single audit-corrected obligation of the v5 charge bridge: the
`hTRT` field of `RoutedHighExcessChargeDataTRT`
(`Erdos260.ChargeBridgeReduction`),

```
routedClassMass route 2 + routedClassMass route 4 + routedClassMass route 5
  ≤ termTower + termReturn + termRun.
```

## Why a *joint* bound (manuscript soundness audit)

The Return-endpoint (class 4), Run / variation-drop (class 5) and
bounded-Tower-exit (class 2) classes are **mutually recursive** — a Return charge
can re-enter a Tower, which can spawn a Run, which can again Return.  They are
therefore *never* bounded individually.  They are bounded only **jointly**, by the
Appendix-N *same-threshold* compression of Lemma N.24 / N.3.1, which collapses the
Tower ↔ Return ↔ Run recursion at one shared threshold: the combined TRT charge is
routed onto a single same-threshold terminal output family `O`, that family is
compressed **`C_Q`-to-one** by the proved Lemma N.3.1
(`AppendixN.TerminalOutputData.compression`), and the compressed mass is absorbed
into the three package terms by the Lemma N.3.3 / N.24 aggregate accounting.

## What is proved here (the summation/compression skeleton)

* `joint_le_of_compression_absorbed` — the three-step transitivity skeleton
  `joint ≤ output ≤ C_Q·wt(O) ≤ packages` (pure arithmetic; the proved N.3.1
  compression is slotted in as the middle step).
* `compressed_le_three_terms` — the N.24 / N.3.3 routing of the single compressed
  output mass into the three TRT package classes (`𝔒_bdd → Tower`, `𝔒_E → Return`,
  `𝔒_V → Run`), pure linear arithmetic.
* `routedTRT_le_packageTerms` — **the joint TRT bound**, with the proved Lemma
  N.3.1 compression `comp.compression` reused as the central step.  Reduces to the
  two clearly-labeled faithful inputs `hRouteToOutput` (the J.1.2 / N.1.0 charging
  of the joint TRT mass onto the same-threshold output family) and `hAbsorb` (the
  N.3.3 / N.24 absorption of the `C_Q`-compressed mass into the package terms).
* `routedTRT_le_packageTerms_aggregate` — the same with the absorption exposed in
  per-package form via `compressed_le_three_terms`.
* `routedTRT_le_packageTerms_split` — the N.24 *split* form, built on the reused
  closure bridge `AppendixN.trtClosure_outputMass_absorbed`: the joint TRT mass
  splits into a terminal non-drop part (absorbed via N.3.1 into Tower+Return) and a
  variation-drop part (the Run window-drop `𝔒_V`).
* `RoutedHighExcessChargeDataTRT.ofCompression` /
  `RoutedHighExcessChargeDataTRT.ofCompressionAggregate` — assemble the full v5
  TRT charge-bridge contract from the three separable bounds plus the joint
  compression primitives.
* `HighExcessChargeData.ofTRTCompression` — the capstone, discharging the central
  bridge `highExcessMass ≤ ClosurePhaseMass` end-to-end through the joint TRT
  compression.

## The TRT phase budget

* `termTRT_le_half_budget_of_bounds` — from the three per-package budgets
  (each `≤ cStar·ξ·X/6`), the joint package term obeys
  `termTower + termReturn + termRun ≤ cStar·ξ·X/2`.
* `termTRT_le_half_budget` / `termTRT_toClosurePhaseData_le_half_budget` — the same
  with the three budgets discharged internally from the supplied package data via
  the proved `termTower_le_budget` / `termReturn_le_budget` / `termRun_le_budget`
  (`Erdos260.AppendixI_PackageBounds`).

## Faithful primitives that remain as inputs

The deep analytic content is exposed, never assumed away:

* `comp : AppendixN.TerminalOutputData` — the **combined same-threshold terminal
  output family** of the three packages (the per-package output families bundle);
  its `C_Q`-to-one compression `comp.compression` is the **proved** Lemma N.3.1
  reused here, not a hypothesis.
* `hRouteToOutput` — the joint TRT charge is dominated by the combined terminal
  output weight (Def. J.1.2 / Lemma N.1.0 terminal routing).
* `hAbsorb` (or the per-class `hBdd`/`hEndpoint`/`hVarDrop` + `hN24`) — the
  `C_Q`-compressed output mass is absorbed into `termTower + termReturn + termRun`
  (Lemma N.3.3 / N.24 aggregate accounting: `𝔒_bdd → Tower` N.3.2, `𝔒_E → Return`
  I.4.2, `𝔒_V → Run` N.2.2).
* the three *separable* per-class bounds `hChernoff` / `hCnl` / `hDensePack`.

No `sorry`, `axiom`, or `admit`; only the summation, the compression transitivity,
and the package-budget arithmetic are discharged here.  This file adds no new
definitions to `Erdos260.lean` or `Erdos260.ChargeBridgeReduction`; it only
*constructs* the existing `RoutedHighExcessChargeDataTRT` / `HighExcessChargeData`
contracts.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## The compression skeleton (three-step transitivity)

The joint TRT mass is bounded in three faithful steps, each a manuscript pillar:

1. **route → output** (`hRoute`): the joint TRT charge is routed onto the combined
   same-threshold terminal output family (Def. J.1.2 / Lemma N.1.0);
2. **N.3.1 compression** (`hComp`): the output family is compressed `C_Q`-to-one
   (`AppendixN.TerminalOutputData.compression`, the proved Lemma N.3.1);
3. **N.3.3 / N.24 absorption** (`hAbsorb`): the compressed mass is absorbed into the
   three package terms.
-/

/--
**Compression transitivity skeleton.**

`joint ≤ output`, `output ≤ compressed`, `compressed ≤ packages` ⟹ `joint ≤ packages`.
This is the summation skeleton of the joint TRT bound: the middle inequality is
the proved Lemma N.3.1 `C_Q`-to-one compression, the outer two are the faithful
routing / absorption inputs.  Pure transitivity; no analytic content.
-/
theorem joint_le_of_compression_absorbed
    {jointMass outputMass compressedBound packageBound : ℝ}
    (hRoute : jointMass ≤ outputMass)
    (hComp : outputMass ≤ compressedBound)
    (hAbsorb : compressedBound ≤ packageBound) :
    jointMass ≤ packageBound :=
  hRoute.trans (hComp.trans hAbsorb)

/--
**N.24 / N.3.3 routing of the compressed output mass into the three TRT classes.**

The single `C_Q`-compressed same-threshold output weight is routed by Lemma N.24
into the three Tower+Return+Run output classes — `𝔒_bdd` (bounded-scale transient,
Lemma N.3.2), `𝔒_E` (endpoint / OLC leakage, Lemma I.4.2), and `𝔒_V` (window
variation drop, Lemma N.2.2) — and each is dominated by the matching package term
`tTower` / `tReturn` / `tRun`.  Their aggregate dominates the compressed mass.
This is the faithful linear combination behind `AppendixN.aggregateAbsorption`,
restricted to the three TRT classes.
-/
theorem compressed_le_three_terms
    {compressedMass compBdd compEndpoint compVarDrop tTower tReturn tRun : ℝ}
    (hN24 : compressedMass ≤ compBdd + compEndpoint + compVarDrop)
    (hBdd : compBdd ≤ tTower)
    (hEndpoint : compEndpoint ≤ tReturn)
    (hVarDrop : compVarDrop ≤ tRun) :
    compressedMass ≤ tTower + tReturn + tRun := by
  linarith

/-! ## The joint TRT bound via the N.3.1 same-threshold compression -/

/--
**Joint Tower+Return+Run charge bound (Lemma N.24 / N.3.1, faithful).**

The combined TRT charge mass `routedClassMass route 2 + route 4 + route 5` is
dominated by the sum of the three package terms `termTower + termReturn + termRun`.

The proof slots the **proved** Lemma N.3.1 `C_Q`-to-one compression
(`comp.compression`) as the central step of `joint_le_of_compression_absorbed`,
between the two faithful inputs:

* `hRouteToOutput` — the joint TRT charge is bounded by the combined same-threshold
  terminal output weight `∑_b wt_O(b)` (Def. J.1.2 / Lemma N.1.0: every live TRT
  reinsertion is charged to a terminal output of the shared-threshold family `O`,
  the mechanism that collapses the Tower ↔ Return ↔ Run recursion);
* `hAbsorb` — the `C_Q`-compressed output weight `C_Q·wt(O)` is absorbed into
  `termTower + termReturn + termRun` (Lemma N.3.3 / N.24 aggregate accounting).

This is exactly the `hTRT` field of `RoutedHighExcessChargeDataTRT`; the three
classes are never summed individually, matching the manuscript audit.
-/
theorem routedTRT_le_packageTerms
    {β σ : Type*} [DecidableEq σ]
    (comp : AppendixN.TerminalOutputData β σ)
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (route : Nat → Fin 6)
    (hRouteToOutput :
      routedClassMass carryData route 2 + routedClassMass carryData route 4
          + routedClassMass carryData route 5
        ≤ ∑ b ∈ comp.branches, comp.wtO b)
    (hAbsorb :
      comp.CQ * (comp.YO * ∑ ζ ∈ comp.ground, comp.fibreMass ζ)
        ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
            + termRun phases.toClosurePhaseData) :
    routedClassMass carryData route 2 + routedClassMass carryData route 4
        + routedClassMass carryData route 5
      ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
          + termRun phases.toClosurePhaseData :=
  joint_le_of_compression_absorbed hRouteToOutput comp.compression hAbsorb

/--
**Joint TRT charge bound, per-package aggregate form (Lemma N.24 / N.3.1 / N.3.3).**

The same joint bound as `routedTRT_le_packageTerms`, but with the absorption input
exposed in the per-package N.24 form: the `C_Q`-compressed output mass is routed
into the three classes `compBdd → Tower`, `compEndpoint → Return`,
`compVarDrop → Run` (`hN24`), each dominated by the matching package term
(`hBdd` / `hEndpoint` / `hVarDrop`).
-/
theorem routedTRT_le_packageTerms_aggregate
    {β σ : Type*} [DecidableEq σ]
    (comp : AppendixN.TerminalOutputData β σ)
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (route : Nat → Fin 6)
    {compBdd compEndpoint compVarDrop : ℝ}
    (hRouteToOutput :
      routedClassMass carryData route 2 + routedClassMass carryData route 4
          + routedClassMass carryData route 5
        ≤ ∑ b ∈ comp.branches, comp.wtO b)
    (hN24 :
      comp.CQ * (comp.YO * ∑ ζ ∈ comp.ground, comp.fibreMass ζ)
        ≤ compBdd + compEndpoint + compVarDrop)
    (hBdd : compBdd ≤ termTower phases.toClosurePhaseData)
    (hEndpoint : compEndpoint ≤ termReturn phases.toClosurePhaseData)
    (hVarDrop : compVarDrop ≤ termRun phases.toClosurePhaseData) :
    routedClassMass carryData route 2 + routedClassMass carryData route 4
        + routedClassMass carryData route 5
      ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
          + termRun phases.toClosurePhaseData :=
  routedTRT_le_packageTerms comp phases carryData route hRouteToOutput
    (compressed_le_three_terms hN24 hBdd hEndpoint hVarDrop)

/--
**Joint TRT charge bound, N.24 split form (reuses `trtClosure_outputMass_absorbed`).**

The manuscript C1-VD split (eq. N.24): the joint TRT charge mass splits into a
*terminal non-drop* part (`termMass`) and a *variation-drop* part (`varMass`,
the Run window-drop `𝔒_V`).  The terminal part is compressed `C_Q`-to-one by the
proved Lemma N.3.1 and absorbed into `absorbedBound` (the Tower+Return absorption),
the drop part is bounded by `windowBound`, and the closure bridge
`AppendixN.trtClosure_outputMass_absorbed` sums the two; the combined bound is then
dominated by `termTower + termReturn + termRun` via `hAbsorbWindow`.
-/
theorem routedTRT_le_packageTerms_split
    {β σ : Type*} [DecidableEq σ]
    (comp : AppendixN.TerminalOutputData β σ)
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (route : Nat → Fin 6)
    {termMass varMass absorbedBound windowBound : ℝ}
    (hsplit :
      routedClassMass carryData route 2 + routedClassMass carryData route 4
          + routedClassMass carryData route 5
        = termMass + varMass)
    (htermToOutput : termMass ≤ ∑ b ∈ comp.branches, comp.wtO b)
    (hcompAbsorb :
      comp.CQ * (comp.YO * ∑ ζ ∈ comp.ground, comp.fibreMass ζ) ≤ absorbedBound)
    (hvar : varMass ≤ windowBound)
    (hAbsorbWindow :
      absorbedBound + windowBound
        ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
            + termRun phases.toClosurePhaseData) :
    routedClassMass carryData route 2 + routedClassMass carryData route 4
        + routedClassMass carryData route 5
      ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
          + termRun phases.toClosurePhaseData := by
  have hterm : termMass ≤ absorbedBound :=
    (htermToOutput.trans comp.compression).trans hcompAbsorb
  exact (AppendixN.trtClosure_outputMass_absorbed hsplit hterm hvar).trans hAbsorbWindow

/-! ## Building the v5 `RoutedHighExcessChargeDataTRT` contract -/

/--
**v5 TRT charge-bridge contract from the joint compression primitives.**

Assembles `RoutedHighExcessChargeDataTRT` (the audit-corrected charge-bridge
reduction of `Erdos260.ChargeBridgeReduction`) from the three *separable*
per-class bounds (`hChernoff` / `hCnl` / `hDensePack`) and the joint TRT
compression primitives, with the joint `hTRT` field discharged by
`routedTRT_le_packageTerms`.
-/
def RoutedHighExcessChargeDataTRT.ofCompression
    {β σ : Type*} [DecidableEq σ]
    (comp : AppendixN.TerminalOutputData β σ)
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (route : Nat → Fin 6)
    (hChernoff :
      routedClassMass carryData route 0 ≤ termChernoff phases.toClosurePhaseData)
    (hCnl : routedClassMass carryData route 1 ≤ termCnl phases.toClosurePhaseData)
    (hDensePack :
      routedClassMass carryData route 3 ≤ termDensePack phases.toClosurePhaseData)
    (hRouteToOutput :
      routedClassMass carryData route 2 + routedClassMass carryData route 4
          + routedClassMass carryData route 5
        ≤ ∑ b ∈ comp.branches, comp.wtO b)
    (hAbsorb :
      comp.CQ * (comp.YO * ∑ ζ ∈ comp.ground, comp.fibreMass ζ)
        ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
            + termRun phases.toClosurePhaseData) :
    RoutedHighExcessChargeDataTRT phases carryData where
  route := route
  hChernoff := hChernoff
  hCnl := hCnl
  hDensePack := hDensePack
  hTRT := routedTRT_le_packageTerms comp phases carryData route hRouteToOutput hAbsorb

/--
**v5 TRT charge-bridge contract, per-package aggregate form.**

As `RoutedHighExcessChargeDataTRT.ofCompression`, but the joint absorption is
supplied in the per-package N.24 form (`hN24` routing into `compBdd`/`compEndpoint`/
`compVarDrop`, each dominated by the matching package term).
-/
def RoutedHighExcessChargeDataTRT.ofCompressionAggregate
    {β σ : Type*} [DecidableEq σ]
    (comp : AppendixN.TerminalOutputData β σ)
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (route : Nat → Fin 6)
    {compBdd compEndpoint compVarDrop : ℝ}
    (hChernoff :
      routedClassMass carryData route 0 ≤ termChernoff phases.toClosurePhaseData)
    (hCnl : routedClassMass carryData route 1 ≤ termCnl phases.toClosurePhaseData)
    (hDensePack :
      routedClassMass carryData route 3 ≤ termDensePack phases.toClosurePhaseData)
    (hRouteToOutput :
      routedClassMass carryData route 2 + routedClassMass carryData route 4
          + routedClassMass carryData route 5
        ≤ ∑ b ∈ comp.branches, comp.wtO b)
    (hN24 :
      comp.CQ * (comp.YO * ∑ ζ ∈ comp.ground, comp.fibreMass ζ)
        ≤ compBdd + compEndpoint + compVarDrop)
    (hBdd : compBdd ≤ termTower phases.toClosurePhaseData)
    (hEndpoint : compEndpoint ≤ termReturn phases.toClosurePhaseData)
    (hVarDrop : compVarDrop ≤ termRun phases.toClosurePhaseData) :
    RoutedHighExcessChargeDataTRT phases carryData where
  route := route
  hChernoff := hChernoff
  hCnl := hCnl
  hDensePack := hDensePack
  hTRT :=
    routedTRT_le_packageTerms_aggregate comp phases carryData route hRouteToOutput
      hN24 hBdd hEndpoint hVarDrop

/--
**Capstone — central charge bridge via the joint TRT compression.**

Discharges the central bridge `highExcessMass ≤ ClosurePhaseMass` end-to-end,
through the v5 six-class routing whose Tower+Return+Run obligation is the
joint Lemma N.24 / N.3.1 compression.  This is `ofCompression` followed by the
faithful summation `RoutedHighExcessChargeDataTRT.toHighExcessChargeData`.
-/
def HighExcessChargeData.ofTRTCompression
    {β σ : Type*} [DecidableEq σ]
    (comp : AppendixN.TerminalOutputData β σ)
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (route : Nat → Fin 6)
    (hChernoff :
      routedClassMass carryData route 0 ≤ termChernoff phases.toClosurePhaseData)
    (hCnl : routedClassMass carryData route 1 ≤ termCnl phases.toClosurePhaseData)
    (hDensePack :
      routedClassMass carryData route 3 ≤ termDensePack phases.toClosurePhaseData)
    (hRouteToOutput :
      routedClassMass carryData route 2 + routedClassMass carryData route 4
          + routedClassMass carryData route 5
        ≤ ∑ b ∈ comp.branches, comp.wtO b)
    (hAbsorb :
      comp.CQ * (comp.YO * ∑ ζ ∈ comp.ground, comp.fibreMass ζ)
        ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
            + termRun phases.toClosurePhaseData) :
    HighExcessChargeData phases carryData :=
  (RoutedHighExcessChargeDataTRT.ofCompression comp phases carryData route
    hChernoff hCnl hDensePack hRouteToOutput hAbsorb).toHighExcessChargeData

/-! ## The TRT phase budget `termTower + termReturn + termRun ≤ cStar·ξ·X/2` -/

/--
**TRT phase budget from the three per-package budgets.**

Each of the three package phase-mass terms fits the manuscript per-phase budget
`cStar·ξ·X/6` (Propositions I.3.1 / I.5.1 / I.5.2 after the K.4 smallness chain);
summing the three gives the joint TRT budget `cStar·ξ·X/2` (= `3·(cStar·ξ·X/6)`).
Pure arithmetic.
-/
theorem termTRT_le_half_budget_of_bounds {cStar ξ X : ℝ}
    (data : ClosurePhaseData cStar ξ X)
    (hTower : termTower data ≤ cStar * ξ * X / 6)
    (hReturn : termReturn data ≤ cStar * ξ * X / 6)
    (hRun : termRun data ≤ cStar * ξ * X / 6) :
    termTower data + termReturn data + termRun data ≤ cStar * ξ * X / 2 := by
  linarith

/--
**TRT phase budget, package-data form.**

With the per-failure package data supplied (bundled in `ClosurePhaseData`), the
three per-package budgets are discharged internally by the proved
`termTower_le_budget` / `termReturn_le_budget` / `termRun_le_budget`
(`Erdos260.AppendixI_PackageBounds`, Propositions I.3.1 / I.5.1 / I.5.2), giving
`termTower + termReturn + termRun ≤ cStar·ξ·X/2` with no extra hypothesis.
-/
theorem termTRT_le_half_budget {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) :
    termTower data + termReturn data + termRun data ≤ cStar * ξ * X / 2 :=
  termTRT_le_half_budget_of_bounds data
    (termTower_le_budget data) (termReturn_le_budget data) (termRun_le_budget data)

/--
**TRT phase budget for the six-phase factory form.**

The `cStar·ξ·X/2` budget on the three package terms as they appear in the
charge-bridge routing `RoutedHighExcessChargeDataTRT phases carryData`, ready to
combine with the joint `hTRT` bound at the per-failure pressure floor.
-/
theorem termTRT_toClosurePhaseData_le_half_budget {cStar ξ X : ℝ}
    (phases : SixPhaseFactoryData cStar ξ X) :
    termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
        + termRun phases.toClosurePhaseData
      ≤ cStar * ξ * X / 2 :=
  termTRT_le_half_budget phases.toClosurePhaseData

end

end Erdos260
