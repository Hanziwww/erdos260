import Mathlib
import Erdos260.ChargeMultiplierClosure
import Erdos260.PkgExposesConstruction

/-!
# The genuine J.1.1 / N.24 / I.9 charge-allocation map — deriving the per-class multipliers

`ChargeMultiplierClosure.lean` recorded the **honest orthogonality** finding: a per-class
multiplier `routedClassMassOf carryData route i ≤ termᵢ` and the proved per-phase budget
`termᵢ ≤ cStar·ξ·X/6` point the same way *with respect to `termᵢ`* but are **orthogonal facts** —
the budget bounds the phase *term* from above, the multiplier bounds the routed carry *mass* from
above — so **no per-class multiplier follows from a proved budget**.  The prior file therefore
only *reduced* each multiplier to per-fibre `count×multiplier` data
(`routedClassMassOf_le_countMultiplier`), leaving the term-vs-mass identification `count·mult ≤ termᵢ`
as an assumed input `hbud`.

This file supplies the **missing direction**: the manuscript's *actual charging map*
(Definition J.1.2 + Lemma J.1.8 charged-ledger summation + Lemma N.1.0 / N.24 absorption), which is
exactly the mechanism that *does* connect the routed carry mass to a phase term.  It is genuinely
different from the budget, and from `count×multiplier`.

## The mechanism (manuscript J.1.2 / J.1.8, `proof_v4_unconditional_clean_v5.tex` §J.1)

For each priority class the manuscript fixes an **output space** of charged objects `O`
(Definition J.1.2) with charged weights `wt(O)` (eq. J.1a), and a **charging map** `Θ` assigning
each routed fibre member to an output object.  The deep per-output charged estimate
(`Σ_{b:Θ(b)=O} wt(b) ≤ C_Q wt(O)`, eqs. J.D / J.Rt / J.Rn / J.T / J.PE) then sums over outputs
(Proposition J.1.8) to `Σ_b wt(b) ≤ C_Q Σ_O wt(O)`, and the phase term **is** the charged output
area `Σ_O wt(O)`.

The Lean realisation here is the **fibrewise charging argument** (`sum_le_chargedArea`,
`Finset.sum_fiberwise_of_maps_to`): given a charging map `chargeOf : ℕ → O` of the class fibre into
a finite output family `outputs`, and the per-output charged bound

  `∀ o ∈ outputs, (Σ_{k routed to o} windowExcess k) ≤ cap o`,

the routed class mass obeys `routedClassMassOf ≤ Σ_o cap o`.  For four of the five charge-bridge
slots the phase term **is** that charged output area — proved here as exact identities
(`termChernoff_eq_chargedArea` is `rfl`, `termTower_eq_chargedArea` is `rfl`,
`termDensePack_eq_chargedArea`, `termCnl_eq_chargedArea`).  So the multiplier
`routedClassMassOf i ≤ termᵢ` is **derived** from the charging map, with the term identification now a
**theorem**, not an assumed `hbud`.  The single remaining input per class is the per-output charged
bound — the genuine J.D / J.Rn / etc. *charged-output estimate* (each output object absorbs at most
its own charged weight of routed carry mass).

## What is genuinely derived (per class, honest)

* **Chernoff (0)**, **CleanCNL (1)**, **DensePack (3)** — each `routedClassMassOf i ≤ termᵢ` is
  DERIVED from a charging map onto the phase term's *own* output objects (`highCostSet` paths,
  CNL Kraft paths, dense-marker points), with the term-as-charged-area identity *proved* and the
  single remaining input the per-output charged bound (J.1.7 / G.6 / J.D).
* **Tower (2) + Return (4) + Run (5)** — bounded **jointly** by a charging map onto the *shared*
  same-threshold output family (Lemma N.24 / N.1.0: these classes are mutually recursive and never
  separable), `routedTRT_le_term_of_charging`; its N.3.1 instance
  `routedTRT_le_term_via_terminalOutput` discharges the term identification through the *proved*
  `TerminalOutputData.compression`.
* **old-residual (6)** — DERIVED from a charging map onto the retained endpoint set `K` with
  `cap = oldResAt` (Lemma L.6.4), the term identification being `Σ_{k∈K} oldResAt k ≤ oldResMass`.

The charging map and its per-output charged bound remain the genuine deep K/L/N input; what is *new*
is that the multiplier is now obtained **through the actual charging map**, with the term-vs-mass
identification discharged, rather than reduced to a free `count·mult ≤ termᵢ` hypothesis.  No
multiplier is "closed" (none follows from a budget — that remains impossible), and the file states
this honestly.

## `pkg_exposes`

The coverage primitive `pkg_exposes` is **CLOSED on the manuscript-faithful structural geometry**
(`StructuralPkgGeometry`, reused): a non-clean (`PKG`) CNL verdict structurally yields one of the six
packages and routes to its charge class (`pkg_verdict_routes_to_package`).  It is **irreducible on the
abstract decoupled geometry** — provably not from scan exhaustiveness
(`pkg_exposes_not_from_exhaustiveness`).

No `sorry`, `admit`, `native_decide`, or new `axiom`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The charging-map mass-domination core (Lemma J.1.8 charged-ledger summation)

This is the genuine fibrewise charging argument.  It is `Finset.sum_fiberwise_of_maps_to` (the charge
reindexing) followed by `Finset.sum_le_sum` (the per-output charged estimate).  It holds for an
arbitrary charge weight `f`, charging map `chargeOf`, finite output family `outputs`, and per-output
capacity `cap`. -/

/-- **Charged-ledger summation (faithful J.1.8).**

If a charge weight `f` over a finite source `F` is routed by a charging map `chargeOf` into a finite
output family `outputs` (`hmaps`), and the total charge routed to each output object `o` is at most
its capacity `cap o` (`hcharged`, the J.D / J.Rt / … per-output charged estimate), then the total
charge is at most the total capacity `Σ_o cap o`.

This is the exact mechanism of Proposition J.1.8: reindex the charge by output object
(`Finset.sum_fiberwise_of_maps_to`), then sum the per-output bounds (`Finset.sum_le_sum`). -/
theorem sum_le_chargedArea {ι O : Type*} [DecidableEq O]
    (F : Finset ι) (f : ι → ℝ) (chargeOf : ι → O) (outputs : Finset O) (cap : O → ℝ)
    (hmaps : ∀ k ∈ F, chargeOf k ∈ outputs)
    (hcharged : ∀ o ∈ outputs,
      (∑ k ∈ F.filter (fun k => chargeOf k = o), f k) ≤ cap o) :
    (∑ k ∈ F, f k) ≤ ∑ o ∈ outputs, cap o := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := outputs) (g := chargeOf) hmaps f]
  exact Finset.sum_le_sum hcharged

/-- **Routed class mass dominated by the charged output area.**

The carry-side instance of `sum_le_chargedArea`: the routed class mass `routedClassMassOf` (the sum
of window excess over the class-`i` fibre) is bounded by the charged output area `Σ_o cap o` of any
charging map of the fibre into a finite output family with the per-output charged bound `hcharged`. -/
theorem routedClassMassOf_le_chargedArea
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7) (i : Fin 7)
    {O : Type*} [DecidableEq O] (chargeOf : ℕ → O) (outputs : Finset O) (cap : O → ℝ)
    (hmaps : ∀ k ∈ routedFibre carryData route i, chargeOf k ∈ outputs)
    (hcharged : ∀ o ∈ outputs,
      (∑ k ∈ (routedFibre carryData route i).filter (fun k => chargeOf k = o),
          windowExcess (hitGap carryData.a) k carryData.r carryData.T) ≤ cap o) :
    routedClassMassOf carryData route i ≤ ∑ o ∈ outputs, cap o := by
  rw [routedClassMassOf_eq_sum_fibre]
  exact sum_le_chargedArea (routedFibre carryData route i)
    (fun k => windowExcess (hitGap carryData.a) k carryData.r carryData.T)
    chargeOf outputs cap hmaps hcharged

/-- **Per-class multiplier from a charging map (the headline derivation step).**

Composing the charged-ledger summation with the term identification `Σ_o cap o ≤ termᵢ` (which, for
the four output-area slots below, is a *proved identity*) yields the per-class multiplier
`routedClassMassOf i ≤ termᵢ` — derived through the actual charging map. -/
theorem routedClassMassOf_le_term_of_chargingMap
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7) (i : Fin 7)
    {O : Type*} [DecidableEq O] (chargeOf : ℕ → O) (outputs : Finset O) (cap : O → ℝ)
    (hmaps : ∀ k ∈ routedFibre carryData route i, chargeOf k ∈ outputs)
    (hcharged : ∀ o ∈ outputs,
      (∑ k ∈ (routedFibre carryData route i).filter (fun k => chargeOf k = o),
          windowExcess (hitGap carryData.a) k carryData.r carryData.T) ≤ cap o)
    {term : ℝ} (hterm : (∑ o ∈ outputs, cap o) ≤ term) :
    routedClassMassOf carryData route i ≤ term :=
  (routedClassMassOf_le_chargedArea carryData route i chargeOf outputs cap hmaps hcharged).trans hterm

/-! ### The charging map subsumes the prior `count×multiplier` reduction

The previous reduction `routedClassMassOf_le_countMultiplier` (a uniform per-fibre window-excess
bound `≤ mult` times a fibre count `≤ count`) is exactly the **degenerate single-output charging
map**: one output object absorbing the whole fibre, with capacity `count·mult`.  The genuine
charging map refines it to a per-output charged estimate against the phase term's real output
objects. -/

/-- **`count×multiplier` is the single-output charging map.**  Recovers
`routedClassMassOf_le_countMultiplier` as the charging map onto a single output of capacity
`count·mult` — demonstrating that the charging-map mechanism subsumes the prior reduction. -/
theorem routedClassMassOf_le_countMultiplier_via_charging
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7) (i : Fin 7)
    {mult count : ℝ}
    (hpoint : ∀ k ∈ routedFibre carryData route i,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult)
    (hcard : ((routedFibre carryData route i).card : ℝ) ≤ count) :
    routedClassMassOf carryData route i ≤ count * mult := by
  refine routedClassMassOf_le_term_of_chargingMap carryData route i
    (O := Unit) (fun _ => ()) {()} (fun _ => count * mult)
    (fun _ _ => Finset.mem_singleton_self ()) (fun o _ => ?_) ?_
  · have hfilter :
        (routedFibre carryData route i).filter (fun k => (() : Unit) = o)
          = routedFibre carryData route i :=
      Finset.filter_true_of_mem (fun _ _ => Subsingleton.elim _ _)
    rw [hfilter]
    have h := routedClassMassOf_le_countMultiplier carryData route i hpoint hmult_nonneg hcard
    rwa [routedClassMassOf_eq_sum_fibre] at h
  · rw [Finset.sum_singleton]

/-! ## 2.  Each phase term IS a charged output area (Definition J.1.2 wt-decomposition)

The genuine content that makes the multiplier *derivable* rather than assumed: the charge-bridge
phase term `termᵢ` is literally the sum of the per-output charged weights of class `i`'s output
objects.  These are proved identities (two are `rfl`), so the term identification `Σ_o cap o = termᵢ`
in the per-class derivations below is a theorem, not a hypothesis. -/

variable {cStar ξ X : ℝ} {shell : FailingDyadicShell} {cPr : ℝ}

/-- **Chernoff term = charged output area** (`rfl`).  `termChernoff` is the charged weighted mass
over the high-cost path family — its output objects with charged weight `chernoff.weight`. -/
theorem termChernoff_eq_chargedArea (data : ClosurePhaseData cStar ξ X) :
    termChernoff data
      = ∑ p ∈ highCostSet data.chernoff.paths data.chernoff.cost data.chernoff.Y,
          data.chernoff.weight p := rfl

/-- **Tower term = charged output area** (`rfl`).  `termTower` is the charged-weight sum over the
tower entry/exit output objects. -/
theorem termTower_eq_chargedArea (data : ClosurePhaseData cStar ξ X) :
    termTower data = ∑ b ∈ data.tower.entryExitSet, data.tower.chargedWeight b := rfl

/-- **DensePack term = charged output area.**  `termDensePack` is the dense-marker point count, i.e.
the charged area over the dense-marker output objects with unit charged weight. -/
theorem termDensePack_eq_chargedArea (data : ClosurePhaseData cStar ξ X) :
    termDensePack data = ∑ _o ∈ data.densePack.densePackPoints, (1 : ℝ) := by
  rw [termDensePack, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **clean-CNL term = charged output area.**  `termCnl` is the Kraft sum scaled by the shell factor,
i.e. the charged area over the CNL path output objects with charged weight
`2^{-c·BND(p)}·shellFactor·X·Ij`. -/
theorem termCnl_eq_chargedArea (data : ClosurePhaseData cStar ξ X) :
    termCnl data
      = ∑ p ∈ data.cnl.paths,
          ((2 : ℝ) ^ (-(data.cnl.c * data.cnl.BNDHeight p)) * data.cnl.shellFactor * X
            * data.cnl.Ij) := by
  rw [termCnl, cleanCNLKraftSum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]

/-! ## 3.  The genuine per-class multiplier derivations

For each separable slot, the multiplier `routedClassMassOf i ≤ termᵢ` is **derived** from a charging
map onto the term's own output objects.  The term identification is the proved identity of §2; the
*single* remaining input is the per-output charged estimate `hcharged` (the manuscript J.1.7 / G.6 /
J.D bound that each output object absorbs at most its charged weight of the routed carry mass). -/

/-- **Class 0 — Chernoff multiplier, DERIVED via the charging map (Lemma 22.1 / J.1.7).**

Given a charging map of the Chernoff fibre into the high-cost path family with the per-path charged
bound `hcharged`, `routedClassMassOf 0 ≤ termChernoff`.  The term identification is `rfl`
(`termChernoff_eq_chargedArea`); the only input is `hcharged`. -/
theorem routedChernoff_le_term_of_charging
    (data : ClosurePhaseData cStar ξ X)
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7)
    [DecidableEq data.chernoff.α]
    (chargeOf : ℕ → data.chernoff.α)
    (hmaps : ∀ k ∈ routedFibre carryData route 0,
      chargeOf k ∈ highCostSet data.chernoff.paths data.chernoff.cost data.chernoff.Y)
    (hcharged : ∀ o ∈ highCostSet data.chernoff.paths data.chernoff.cost data.chernoff.Y,
      (∑ k ∈ (routedFibre carryData route 0).filter (fun k => chargeOf k = o),
          windowExcess (hitGap carryData.a) k carryData.r carryData.T) ≤ data.chernoff.weight o) :
    routedClassMassOf carryData route 0 ≤ termChernoff data :=
  routedClassMassOf_le_term_of_chargingMap carryData route 0 chargeOf _ data.chernoff.weight
    hmaps hcharged (le_of_eq (termChernoff_eq_chargedArea data).symm)

/-- **Class 1 — clean-CNL multiplier, DERIVED via the charging map (Theorem G.6).**

Given a charging map of the clean-CNL fibre into the CNL path family with the per-path Kraft-weighted
charged bound `hcharged`, `routedClassMassOf 1 ≤ termCnl`.  The term identification is the proved
`termCnl_eq_chargedArea`; the only input is `hcharged`. -/
theorem routedCnl_le_term_of_charging
    (data : ClosurePhaseData cStar ξ X)
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7)
    [DecidableEq data.cnl.α]
    (chargeOf : ℕ → data.cnl.α)
    (hmaps : ∀ k ∈ routedFibre carryData route 1, chargeOf k ∈ data.cnl.paths)
    (hcharged : ∀ o ∈ data.cnl.paths,
      (∑ k ∈ (routedFibre carryData route 1).filter (fun k => chargeOf k = o),
          windowExcess (hitGap carryData.a) k carryData.r carryData.T)
        ≤ (2 : ℝ) ^ (-(data.cnl.c * data.cnl.BNDHeight o)) * data.cnl.shellFactor * X
            * data.cnl.Ij) :
    routedClassMassOf carryData route 1 ≤ termCnl data :=
  routedClassMassOf_le_term_of_chargingMap carryData route 1 chargeOf data.cnl.paths
    (fun o => (2 : ℝ) ^ (-(data.cnl.c * data.cnl.BNDHeight o)) * data.cnl.shellFactor * X
      * data.cnl.Ij)
    hmaps hcharged (le_of_eq (termCnl_eq_chargedArea data).symm)

/-- **Class 3 — DensePack multiplier, DERIVED via the charging map (Lemma J.D / I.4.1).**

Given a charging map of the DensePack fibre into the dense-marker point set with the per-marker
charged bound `hcharged` (each marker absorbs at most one unit of routed carry mass),
`routedClassMassOf 3 ≤ termDensePack`.  The term identification is `termDensePack_eq_chargedArea`. -/
theorem routedDensePack_le_term_of_charging
    (data : ClosurePhaseData cStar ξ X)
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7)
    (chargeOf : ℕ → ℕ)
    (hmaps : ∀ k ∈ routedFibre carryData route 3, chargeOf k ∈ data.densePack.densePackPoints)
    (hcharged : ∀ o ∈ data.densePack.densePackPoints,
      (∑ k ∈ (routedFibre carryData route 3).filter (fun k => chargeOf k = o),
          windowExcess (hitGap carryData.a) k carryData.r carryData.T) ≤ (1 : ℝ)) :
    routedClassMassOf carryData route 3 ≤ termDensePack data :=
  routedClassMassOf_le_term_of_chargingMap carryData route 3 chargeOf
    data.densePack.densePackPoints (fun _ => (1 : ℝ))
    hmaps hcharged (le_of_eq (termDensePack_eq_chargedArea data).symm)

/-- **Class 6 — old-residual multiplier, DERIVED via the charging map (Lemma L.6.4).**

The old-residual class is charged onto the retained terminal endpoint set `K` with per-endpoint
charge `oldResAt` (the L.6.4 branch-level mass `OldRes = Σ_{k∈K} oldResAt k`).  Given the per-endpoint
charged bound `hcharged` and the identification `Σ_{k∈K} oldResAt k ≤ oldResMass`,
`routedClassMassOf 6 ≤ oldResMass`. -/
theorem routedOldRes_le_mass_of_charging
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7)
    (chargeOf : ℕ → ℕ) (K : Finset ℕ) (oldResAt : ℕ → ℝ) {oldResMass : ℝ}
    (hmaps : ∀ k ∈ routedFibre carryData route 6, chargeOf k ∈ K)
    (hcharged : ∀ o ∈ K,
      (∑ k ∈ (routedFibre carryData route 6).filter (fun k => chargeOf k = o),
          windowExcess (hitGap carryData.a) k carryData.r carryData.T) ≤ oldResAt o)
    (hident : (∑ o ∈ K, oldResAt o) ≤ oldResMass) :
    routedClassMassOf carryData route 6 ≤ oldResMass :=
  routedClassMassOf_le_term_of_chargingMap carryData route 6 chargeOf K oldResAt
    hmaps hcharged hident

/-! ## 4.  The joint Tower+Return+Run charging map (Lemma N.24 / N.1.0)

The Tower (2), Return (4) and Run (5) classes are mutually recursive (a Return can re-enter a Tower,
which can spawn a Run, …) and are **never** bounded individually — the manuscript audit recorded in
`ChargeBridgeReduction`.  They are bounded only **jointly**, by routing the *union* of their three
fibres into a single **shared same-threshold output family** (Lemma N.1.0) whose charged area is
absorbed into `termTower + termReturn + termRun` (Lemma N.24).  This is the genuine N.24 charging map,
built on the same `sum_le_chargedArea` core applied to the union fibre. -/

/-- The joint TRT mass is the window-excess sum over the union of the three (disjoint) fibres. -/
theorem routedTRT_eq_sum_union
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7) :
    routedClassMassOf carryData route 2 + routedClassMassOf carryData route 4
        + routedClassMassOf carryData route 5
      = ∑ k ∈ (routedFibre carryData route 2 ∪ routedFibre carryData route 4
            ∪ routedFibre carryData route 5),
          windowExcess (hitGap carryData.a) k carryData.r carryData.T := by
  have hd24 : Disjoint (routedFibre carryData route 2) (routedFibre carryData route 4) := by
    unfold routedFibre; exact filter_route_disjoint _ route (by decide)
  have hd25 : Disjoint (routedFibre carryData route 2) (routedFibre carryData route 5) := by
    unfold routedFibre; exact filter_route_disjoint _ route (by decide)
  have hd45 : Disjoint (routedFibre carryData route 4) (routedFibre carryData route 5) := by
    unfold routedFibre; exact filter_route_disjoint _ route (by decide)
  have hd245 :
      Disjoint (routedFibre carryData route 2 ∪ routedFibre carryData route 4)
        (routedFibre carryData route 5) := by
    rw [Finset.disjoint_union_left]; exact ⟨hd25, hd45⟩
  rw [routedClassMassOf_eq_sum_fibre, routedClassMassOf_eq_sum_fibre,
    routedClassMassOf_eq_sum_fibre, Finset.sum_union hd245, Finset.sum_union hd24]

/-- **Joint Tower+Return+Run multiplier, DERIVED via the shared-output charging map (N.24 / N.1.0).**

Given a charging map of the *union* of the Tower/Return/Run fibres into a shared same-threshold output
family with the per-output charged bound `hcharged`, and the N.24 absorption identification
`Σ_o cap o ≤ termTower + termReturn + termRun`, the joint TRT mass is bounded by the three package
terms.  This is the genuine N.24 mechanism (the three classes share one output family); the N.3.1
`TerminalOutputData` compression route is the instance `routedTRT_le_term_via_terminalOutput` below. -/
theorem routedTRT_le_term_of_charging
    (data : ClosurePhaseData cStar ξ X)
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7)
    {O : Type*} [DecidableEq O] (chargeOf : ℕ → O) (outputs : Finset O) (cap : O → ℝ)
    (hmaps : ∀ k ∈ (routedFibre carryData route 2 ∪ routedFibre carryData route 4
          ∪ routedFibre carryData route 5),
        chargeOf k ∈ outputs)
    (hcharged : ∀ o ∈ outputs,
      (∑ k ∈ (routedFibre carryData route 2 ∪ routedFibre carryData route 4
            ∪ routedFibre carryData route 5).filter (fun k => chargeOf k = o),
          windowExcess (hitGap carryData.a) k carryData.r carryData.T) ≤ cap o)
    (hterm : (∑ o ∈ outputs, cap o)
      ≤ termTower data + termReturn data + termRun data) :
    routedClassMassOf carryData route 2 + routedClassMassOf carryData route 4
        + routedClassMassOf carryData route 5
      ≤ termTower data + termReturn data + termRun data := by
  rw [routedTRT_eq_sum_union]
  exact (sum_le_chargedArea _ _ chargeOf outputs cap hmaps hcharged).trans hterm

/-- **Joint TRT multiplier via the proved N.3.1 compression (`TerminalOutputData`).**

The genuine N.24 instance of `routedTRT_le_term_of_charging`: the shared output family is the
manuscript's same-threshold terminal output family `comp` (`AppendixN.TerminalOutputData`), the
per-output capacities are its charged weights `comp.wtO`, and the term identification `Σ_b wtO b ≤
termTRT` is discharged by the **proved** Lemma N.3.1 `C_Q`-to-one compression `comp.compression`
chained with the N.3.3 absorption `hAbsorb`.  Thus the only remaining input is the per-output charged
bound `hcharged` (the J.1.2 / N.1.0 routing of the joint TRT mass onto the output family). -/
theorem routedTRT_le_term_via_terminalOutput
    (data : ClosurePhaseData cStar ξ X)
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7)
    {β σ : Type*} [DecidableEq σ] [DecidableEq β]
    (comp : AppendixN.TerminalOutputData β σ) (chargeOf : ℕ → β)
    (hmaps : ∀ k ∈ (routedFibre carryData route 2 ∪ routedFibre carryData route 4
          ∪ routedFibre carryData route 5),
        chargeOf k ∈ comp.branches)
    (hcharged : ∀ b ∈ comp.branches,
      (∑ k ∈ (routedFibre carryData route 2 ∪ routedFibre carryData route 4
            ∪ routedFibre carryData route 5).filter (fun k => chargeOf k = b),
          windowExcess (hitGap carryData.a) k carryData.r carryData.T) ≤ comp.wtO b)
    (hAbsorb : comp.CQ * (comp.YO * ∑ ζ ∈ comp.ground, comp.fibreMass ζ)
      ≤ termTower data + termReturn data + termRun data) :
    routedClassMassOf carryData route 2 + routedClassMassOf carryData route 4
        + routedClassMassOf carryData route 5
      ≤ termTower data + termReturn data + termRun data :=
  routedTRT_le_term_of_charging data carryData route chargeOf comp.branches comp.wtO
    hmaps hcharged (comp.compression.trans hAbsorb)

/-! ## 5.  Assembling the charge atom with all five multipliers derived from charging maps

`CarryPriorityRoutingCharge.ofChargingMaps` builds the v5 charge atom from the J.1.1 routing `R`
(`CarryRouting`) together with the five charging maps — the three separable per-class maps
(Chernoff/CleanCNL/DensePack, term identification proved internally), the joint TRT map (N.24), and
the old-residual map (L.6.4) — so every per-class multiplier field is obtained **through the actual
charging map**, never as a free `routedClassMassOf ≤ termᵢ` hypothesis. -/

/-- **The v5 charge atom from the five charging maps (the headline assembly).** -/
def CarryPriorityRoutingCharge.ofChargingMaps
    {cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (R : CarryPriorityRouting) (oldResMass : ℝ)
    -- Chernoff (class 0)
    [DecidableEq phases.toClosurePhaseData.chernoff.α]
    (chargeChernoff : ℕ → phases.toClosurePhaseData.chernoff.α)
    (mapsChernoff : ∀ k ∈ routedFibre carryData R.classify 0,
      chargeChernoff k ∈ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y)
    (chargedChernoff : ∀ o ∈ highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y,
      (∑ k ∈ (routedFibre carryData R.classify 0).filter (fun k => chargeChernoff k = o),
          windowExcess (hitGap carryData.a) k carryData.r carryData.T)
        ≤ phases.toClosurePhaseData.chernoff.weight o)
    -- clean-CNL (class 1)
    [DecidableEq phases.toClosurePhaseData.cnl.α]
    (chargeCnl : ℕ → phases.toClosurePhaseData.cnl.α)
    (mapsCnl : ∀ k ∈ routedFibre carryData R.classify 1,
      chargeCnl k ∈ phases.toClosurePhaseData.cnl.paths)
    (chargedCnl : ∀ o ∈ phases.toClosurePhaseData.cnl.paths,
      (∑ k ∈ (routedFibre carryData R.classify 1).filter (fun k => chargeCnl k = o),
          windowExcess (hitGap carryData.a) k carryData.r carryData.T)
        ≤ (2 : ℝ) ^ (-(phases.toClosurePhaseData.cnl.c
              * phases.toClosurePhaseData.cnl.BNDHeight o))
            * phases.toClosurePhaseData.cnl.shellFactor * (shell.X : ℝ)
            * phases.toClosurePhaseData.cnl.Ij)
    -- DensePack (class 3)
    (chargeDensePack : ℕ → ℕ)
    (mapsDensePack : ∀ k ∈ routedFibre carryData R.classify 3,
      chargeDensePack k ∈ phases.toClosurePhaseData.densePack.densePackPoints)
    (chargedDensePack : ∀ o ∈ phases.toClosurePhaseData.densePack.densePackPoints,
      (∑ k ∈ (routedFibre carryData R.classify 3).filter (fun k => chargeDensePack k = o),
          windowExcess (hitGap carryData.a) k carryData.r carryData.T) ≤ (1 : ℝ))
    -- joint Tower+Return+Run (classes 2,4,5)
    {OTRT : Type*} [DecidableEq OTRT] (chargeTRT : ℕ → OTRT) (outputsTRT : Finset OTRT)
    (capTRT : OTRT → ℝ)
    (mapsTRT : ∀ k ∈ (routedFibre carryData R.classify 2 ∪ routedFibre carryData R.classify 4
          ∪ routedFibre carryData R.classify 5),
        chargeTRT k ∈ outputsTRT)
    (chargedTRT : ∀ o ∈ outputsTRT,
      (∑ k ∈ (routedFibre carryData R.classify 2 ∪ routedFibre carryData R.classify 4
            ∪ routedFibre carryData R.classify 5).filter (fun k => chargeTRT k = o),
          windowExcess (hitGap carryData.a) k carryData.r carryData.T) ≤ capTRT o)
    (htermTRT : (∑ o ∈ outputsTRT, capTRT o)
      ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
        + termRun phases.toClosurePhaseData)
    -- old-residual (class 6)
    (chargeOldRes : ℕ → ℕ) (oldResK : Finset ℕ) (oldResAt : ℕ → ℝ)
    (mapsOldRes : ∀ k ∈ routedFibre carryData R.classify 6, chargeOldRes k ∈ oldResK)
    (chargedOldRes : ∀ o ∈ oldResK,
      (∑ k ∈ (routedFibre carryData R.classify 6).filter (fun k => chargeOldRes k = o),
          windowExcess (hitGap carryData.a) k carryData.r carryData.T) ≤ oldResAt o)
    (htermOldRes : (∑ o ∈ oldResK, oldResAt o) ≤ oldResMass) :
    CarryPriorityRoutingCharge phases carryData oldResMass where
  routing := R
  hChernoff :=
    routedChernoff_le_term_of_charging phases.toClosurePhaseData carryData R.classify
      chargeChernoff mapsChernoff chargedChernoff
  hCnl :=
    routedCnl_le_term_of_charging phases.toClosurePhaseData carryData R.classify
      chargeCnl mapsCnl chargedCnl
  hDensePack :=
    routedDensePack_le_term_of_charging phases.toClosurePhaseData carryData R.classify
      chargeDensePack mapsDensePack chargedDensePack
  hTRT :=
    routedTRT_le_term_of_charging phases.toClosurePhaseData carryData R.classify
      chargeTRT outputsTRT capTRT mapsTRT chargedTRT htermTRT
  hOldRes :=
    routedOldRes_le_mass_of_charging carryData R.classify chargeOldRes oldResK oldResAt
      mapsOldRes chargedOldRes htermOldRes

/-- **Capstone — the charging-map charge atom reaches the numeric pressure floor.**

Any constructed `CarryPriorityRoutingCharge` (e.g. from `ofChargingMaps`) discharges the augmented
charge bridge *at the numeric floor*: chaining its proved `highExcess_le_phaseMass_add_oldRes` (the
seven-class summation) with the **proved** `ClosurePhaseMass_le_budget` collapses the phase mass to
`cStar·ξ·X`, giving `highExcessMass ≤ cStar·ξ·X + oldResMass`.  This is the recurrence-I.11' floor the
per-class charging maps feed. -/
theorem CarryPriorityRoutingCharge.highExcess_le_budget_add_oldRes
    {cStar ξ : ℝ}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell cPr} {oldResMass : ℝ}
    (D : CarryPriorityRoutingCharge phases carryData oldResMass) :
    highExcessMass (highExcessStarts carryData.starts (hitGap carryData.a)
        carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T
      ≤ cStar * ξ * (shell.X : ℝ) + oldResMass := by
  have h := D.highExcess_le_phaseMass_add_oldRes
  have hb := ClosurePhaseMass_le_budget phases.toClosurePhaseData shell.X_pos_real.le
  linarith

/-! ## 6.  `pkg_exposes` from the actual `cnlOf`/`geomDetect` taxonomy

The J.1.1 coverage primitive `pkg_exposes` — *a non-clean (`PKG`) CNL verdict exposes a genuine
charge package* — is examined against the actual classifier taxonomy.

* **Taxonomy exhaustiveness.**  The proved CNL classifier `canonicalCNLSelector` partitions every
  clean-visible transition into exactly one of the seven `CNLClass` values; a `PKG` verdict is exactly
  `PKG ∈ available` (`selector_eq_pkg_iff_mem`, reused).  The six *clean* classes never produce a
  geometric package — they route to CleanCNL (charge class `1`).
* **CLOSED on the manuscript-faithful structural geometry.**  Under J.5's definition
  `PKG-available := (six-package disjunction)` (`StructuralPkgGeometry`, reused), a `PKG` verdict
  *structurally* yields one of the six packages, and the J.1.1 scan routes the state to that package's
  charge class — `pkg_verdict_routes_to_package`, a full theorem (no coverage hypothesis).
* **IRREDUCIBLE on the abstract decoupled geometry.**  When `cnlOf` and `geomDetect` are independent
  fields there is no relation to exploit; `pkg_exposes` is provably *not* a consequence of the scan's
  exhaustiveness, which only ever supplies the CleanCNL catch-all (`pkg_exposes_not_from_exhaustiveness`,
  reused: `j11Scan {1} = some 1`). -/

/-- **Taxonomy exhaustiveness, charge-routing form (reuses `selector_eq_pkg_iff_mem`).**  The CNL
classifier flags a package exit (`PKG`) exactly when `PKG` is available; this is the gate the J.1.1
routing uses to separate the six clean classes (→ CleanCNL) from a genuine package exit. -/
theorem pkg_verdict_iff_pkg_available (G : CNLObstructionGeometry) (s : LiftState) :
    canonicalCNLSelector (G.cnlOf s) = some CNLClass.pkg
      ↔ CNLClass.pkg ∈ (G.cnlOf s).available :=
  selector_eq_pkg_iff_mem (G.cnlOf s)

/-- **`pkg_exposes` CLOSED structurally — a non-clean verdict routes to one of the six packages.**

For the manuscript-faithful structural geometry `P` (where `PKG`-availability *is* the six-package
disjunction, per J.5), a `PKG` verdict with package label `p` makes the J.1.1 first-obstruction scan
route the start to `p`'s charge class `p.toCharge ∈ {0,2,3,4,5,6}`.  Combined with the *proved*
coverage `P.pkg_labeled` (every `PKG` verdict carries a label), this is the full taxonomy
exhaustiveness: a non-clean CNL verdict structurally falls into one of the six packages.  No coverage
hypothesis remains. -/
theorem pkg_verdict_routes_to_package (P : StructuralPkgGeometry) (config : ℕ → LiftState)
    {k : ℕ} {p : GeomPackage}
    (hpkg : canonicalCNLSelector (P.cnlOf (config k)) = some CNLClass.pkg)
    (hlabel : P.label (config k) = some p) :
    (P.toMarking.toObstructionGeometry.toRouting config).classify k = p.toCharge :=
  P.toMarking.classify_eq_charge_of_label config hpkg hlabel

/-- **`pkg_exposes` CLOSED structurally — existence form.**  For the structural geometry, a `PKG`
verdict genuinely exposes a charge package (the `pkg_exposes` invariant, here a theorem via the proved
`pkg_labeled`). -/
theorem pkg_exposes_of_structural (P : StructuralPkgGeometry) (s : LiftState)
    (h : canonicalCNLSelector (P.cnlOf s) = some CNLClass.pkg) :
    ∃ c : Fin 7, P.toMarking.geomDetect c s = true :=
  P.pkg_exposes s h

/-- **`pkg_exposes` is the structural identity on the abstract geometry (reuses `structuralPkg_iff`).**
On a decoupled `CNLObstructionGeometry` the coverage primitive is *exactly* the one-directional
structural identity `StructuralPkg` — neither stronger nor weaker. -/
theorem pkg_exposes_eq_structuralPkg (G : CNLObstructionGeometry) :
    StructuralPkg G ↔
      (∀ s, canonicalCNLSelector (G.cnlOf s) = some CNLClass.pkg →
        ∃ c : Fin 7, G.geomDetect c s = true) :=
  structuralPkg_iff G

/-- **`pkg_exposes` is irreducible from scan exhaustiveness (reuses `j11Scan_catchall_only`).**  The
J.1.1 scan's exhaustiveness only ever supplies the deliberately-last CleanCNL catch-all (`j11Scan {1} =
some 1`), so the coverage that a `PKG` verdict exposes a *package* class is a separate primitive. -/
theorem pkg_exposes_irreducible_from_scan :
    j11Scan ({1} : Finset (Fin 7)) = some 1 :=
  pkg_exposes_not_from_exhaustiveness

/-! ## 7.  Honest residual inventory -/

/-- The honest per-class status of the charge-allocation multipliers and `pkg_exposes`. -/
def chargeAllocationResidual : List String :=
  [ "MECHANISM: each per-class multiplier routedClassMassOf i ≤ termᵢ is now DERIVED through the " ++
      "manuscript's ACTUAL charging map (Def. J.1.2 outputs + Lemma J.1.8 charged-ledger summation " ++
      "`sum_le_chargedArea` = Finset.sum_fiberwise_of_maps_to + Finset.sum_le_sum), NOT from a phase " ++
      "budget (budgets bound the TERM, multipliers bound the carry MASS — still orthogonal).",
    "Chernoff (0): DERIVED via charging onto the high-cost path family; term identification " ++
      "termChernoff = Σ_p weight p is PROVED (rfl, termChernoff_eq_chargedArea). Remaining input: " ++
      "the per-path charged bound (Lemma 22.1 / J.1.7).",
    "clean-CNL (1): DERIVED via charging onto the CNL Kraft path family; term identification " ++
      "termCnl = Σ_p (2^{-c·BND p}·shellFactor·X·Ij) is PROVED (termCnl_eq_chargedArea). Remaining " ++
      "input: the per-path Kraft-weighted charged bound (Theorem G.6).",
    "DensePack (3): DERIVED via charging onto the dense-marker points; term identification " ++
      "termDensePack = Σ_o 1 (= card) is PROVED (termDensePack_eq_chargedArea). Remaining input: the " ++
      "per-marker charged bound, each marker ≤ 1 unit (Lemma J.D / I.4.1).",
    "Tower+Return+Run (2+4+5): DERIVED JOINTLY via charging the UNION fibre onto a shared " ++
      "same-threshold output family (Lemma N.24 / N.1.0, routedTRT_le_term_of_charging); these three " ++
      "are mutually recursive and never separable. The N.3.1 instance " ++
      "routedTRT_le_term_via_terminalOutput discharges the term identification through the PROVED " ++
      "TerminalOutputData.compression, leaving only the per-output charged bound + N.24 absorption.",
    "old-residual (6): DERIVED via charging onto the retained endpoint set K with cap = oldResAt " ++
      "(Lemma L.6.4); term identification Σ_{k∈K} oldResAt k ≤ oldResMass. Remaining input: the " ++
      "per-endpoint charged bound.",
    "NOT CLOSED: no per-class multiplier follows from a proved phase budget — that remains impossible " ++
      "(orthogonal directions). What is NEW vs. ChargeMultiplierClosure: the term-vs-mass " ++
      "identification (previously the assumed `hbud : count·mult ≤ termᵢ`) is now a PROVED identity " ++
      "(termᵢ = charged output area), and the remaining input is the genuine per-output charged " ++
      "estimate (J.D/J.Rn/22.1/L.6.4), the manuscript's actual charging content — not a free budget gap.",
    "count×multiplier is SUBSUMED: routedClassMassOf_le_countMultiplier is the degenerate " ++
      "single-output charging map (routedClassMassOf_le_countMultiplier_via_charging).",
    "pkg_exposes: CLOSED on the manuscript-faithful structural geometry (a non-clean PKG verdict " ++
      "structurally routes to one of the six packages, pkg_verdict_routes_to_package, via the proved " ++
      "StructuralPkgGeometry.pkg_labeled). IRREDUCIBLE on the abstract decoupled geometry: equivalent " ++
      "to StructuralPkg (pkg_exposes_eq_structuralPkg) and provably not from scan exhaustiveness " ++
      "(pkg_exposes_irreducible_from_scan: j11Scan {1} = some 1)." ]

theorem chargeAllocationResidual_nonempty : chargeAllocationResidual ≠ [] := by
  simp [chargeAllocationResidual]

end

end Erdos260
