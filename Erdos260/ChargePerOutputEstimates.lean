import Mathlib
import Erdos260.ChargeAllocationConstruction
import Erdos260.ChernoffCNLChargeBound
import Erdos260.DensePackChargeBound
import Erdos260.TRTChargeBound
import Erdos260.OldResCountFromCarry

/-!
# Discharging the per-output charged estimates of the J.1.8 charging map

`ChargeAllocationConstruction.lean` derived every one of the seven per-class charge multipliers
`routedClassMassOf i ≤ termᵢ` **through the genuine J.1.8 charging map** (`sum_le_chargedArea` =
`Finset.sum_fiberwise_of_maps_to` + `Finset.sum_le_sum`), with the term-vs-mass identification a
proved identity, leaving as the **single input per class** the *per-output charged estimate*

  `hcharged : ∀ o ∈ outputs, (∑_{k : Θ(k)=o} windowExcess k) ≤ cap o`,

i.e. the manuscript's J.D / J.Rt / J.Rn / J.T / J.PE bound
`∑_{b:Θ_{𝔭}(b)=O} wt(b) ≤ C_𝔭(L) wt(O)` (proof_v4 §J.1.3–J.1.8, proved in Appendix L.2.1–L.2.6).

## The honest situation (confirmed against the manuscript)

The per-output charged estimate couples the **carry-side** routed window-excess mass to the
**output-side** charged weight `wt(O)`.  The proved phase cores bound the *output areas*
`∑_O wt(O)` (the term identifications):

* Chernoff (Lemma 22.1, `regular_shellChernoff_tail_le_budget`) bounds `∑_o weight o`;
* clean-CNL (Theorem G.6, `liftPathKraft_le`) bounds `∑_o 2^{-cH(o)}`;
* DensePack (Lemma J.D / K.1.x, `corollaryK1_3_densePackUnderFailure`) bounds the marker count
  `∑_o 1`;
* old-residual (Lemma L.6.4 / L.22, `oldRes_le_of_carryFailure`) bounds `∑_{k∈K} oldResAt k`;
* TRT (Lemma N.3.1, `TerminalOutputData.compression`) bounds `∑_b wtO b`.

**None of these is the per-output estimate** — they bound the *sum* of the output weights, not the
carry mass absorbed by each individual output.  Per-output absorption is the orthogonal Appendix-L
charging content (J.D/J.Rt/J.Rn/J.T/J.PE), exactly the orthogonality already recorded in
`ChargeMultiplierClosure`.  So **no per-output charged estimate follows from a phase core**, and we
do not pretend otherwise.

## What this file genuinely proves

* **`perOutput_charged_of_injOn`** — the *charged-ledger summation at per-output granularity*: for a
  **matching** (injective-on-the-fibre) charging map `Θ` with the **per-element charged domination**
  `windowExcess k ≤ cap(Θ k)` (the J.1b same-threshold containment `Ω(b,T) ⊆ Ω(Θ(b),T)` in
  per-branch form) and `cap ≥ 0`, the per-output charged estimate `∑_{k:Θ(k)=o} windowExcess k ≤
  cap o` **is a theorem** (`C_𝔭 = 1` case).  This *discharges* the `hcharged` input of every
  charging-map multiplier, reducing it to its smallest genuine form: the per-element/per-charge
  bound + matching.
* **`perOutput_charged_of_overlap`** — the faithful `C_Q`-multiplicity form
  `∑_{k:Θ(k)=o} windowExcess k ≤ C_Q · cap o` (the manuscript's J.D `≤ C_Q wt(O)`) from a
  bounded-overlap charging map (`#Θ⁻¹(o) ≤ C_Q`) + per-element domination — the per-output instance
  of the count×multiplier mechanism.
* The **per-class wrappers** `routed{Chernoff,Cnl,DensePack}_le_term_of_matching`,
  `routedTRT_le_term_via_terminalOutput_matching`, `routedOldRes_le_mass_of_matching` /
  `routedOldRes_le_density_of_matching` — each per-class multiplier `routedClassMassOf i ≤ termᵢ`
  with the `hcharged` summation **discharged** by the matching reduction, so the remaining input is
  only the per-element charged domination + matching (the genuine J.1b per-charge content).  For
  **old-residual** the term identification is additionally discharged from the **proved**
  OldResCountFromCarry core (`oldRes_le_of_carryFailure`); for **TRT** from the **proved** N.3.1
  compression (`comp.compression`).
* **`failingShellPkgGeometry` / `densePackFailureGeometry`** — the J.5 `StructuralPkgGeometry` for a
  failing dyadic shell's dense-density failure, with `pkg_exposes` **furnished as a theorem**
  (reusing the proved `StructuralPkgGeometry.pkg_exposes` / `pkg_verdict_routes_to_package`), and
  non-vacuity (genuine PKG-exit states routing to the DensePack charge `3`, and genuine clean
  states).

## Honest per-class verdict (see `chargePerOutputResidual`)

The per-output charged estimate is **not** derived from any phase core for any of the seven classes
(it is orthogonal Appendix-L content).  What is genuinely proved is that its **summation half** is
discharged from a matching charging map + per-element charged domination (the smallest genuine
remaining estimate), and that the **term half** is genuinely from the proved cores for old-residual
(L.6.4/L.22) and TRT (N.3.1).

No `sorry`, `admit`, `native_decide`, or new `axiom`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The per-output charged estimate from a matching charging map (J.1.8 at per-output level)

The genuine, fully-proved reduction: the per-output charged estimate
`∑_{k:Θ(k)=o} f k ≤ cap o` is a **theorem** whenever the charging map `Θ` is a *matching*
(injective on the source fibre `F`) and each charged element is dominated by its output's capacity
(`f k ≤ cap (Θ k)`).  This is the `C_𝔭 = 1` case of the manuscript per-output estimate
`∑_{b:Θ(b)=O} wt(b) ≤ C_𝔭 wt(O)`: under a matching, each output's preimage in the fibre is empty
or a singleton, so the charged sum is `0 ≤ cap o` or `f k ≤ cap(Θ k) = cap o`. -/

/-- **Per-output charged estimate from a matching (J.1.8, `C = 1`).**

For a charge weight `f` over a finite fibre `F`, a charging map `chargeOf` that is **injective on
`F`** (`hinj`, the *matching* property: each fibre member charges a distinct output), the
**per-element charged domination** `f k ≤ cap (chargeOf k)` (`hdom`, the J.1b per-branch
containment), and `cap ≥ 0` on the output family (`hcap_nonneg`), every output absorbs at most its
own capacity:

  `∀ o ∈ outputs, (∑_{k ∈ F, chargeOf k = o} f k) ≤ cap o`.

This is exactly the `hcharged` input demanded by the charging-map multipliers of
`ChargeAllocationConstruction`, now a **proved theorem** under matching + per-element domination. -/
theorem perOutput_charged_of_injOn {ι O : Type*} [DecidableEq O]
    (F : Finset ι) (f : ι → ℝ) (chargeOf : ι → O) (outputs : Finset O) (cap : O → ℝ)
    (hinj : ∀ x ∈ F, ∀ y ∈ F, chargeOf x = chargeOf y → x = y)
    (hdom : ∀ k ∈ F, f k ≤ cap (chargeOf k))
    (hcap_nonneg : ∀ o ∈ outputs, 0 ≤ cap o) :
    ∀ o ∈ outputs, (∑ k ∈ F.filter (fun k => chargeOf k = o), f k) ≤ cap o := by
  intro o ho
  rcases (F.filter (fun k => chargeOf k = o)).eq_empty_or_nonempty with h | h
  · rw [h, Finset.sum_empty]; exact hcap_nonneg o ho
  · obtain ⟨k, hk⟩ := h
    obtain ⟨hkF, hko⟩ := Finset.mem_filter.mp hk
    have hsingle : F.filter (fun k => chargeOf k = o) = {k} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hk, fun x hx => ?_⟩
      obtain ⟨hxF, hxo⟩ := Finset.mem_filter.mp hx
      exact hinj x hxF k hkF (hxo.trans hko.symm)
    rw [hsingle, Finset.sum_singleton]
    calc f k ≤ cap (chargeOf k) := hdom k hkF
      _ = cap o := by rw [hko]

/-- **Per-output charged estimate from a bounded-overlap charging map (faithful J.D `C_Q wt(O)`).**

The manuscript per-output estimate `∑_{b:Θ(b)=O} wt(b) ≤ C_Q wt(O)` (J.D / J.Rt / J.Rn / J.T / J.PE)
in its genuine `C_Q`-multiplicity form: if the charging map has **bounded overlap** — at most `CQ`
fibre members charge each output (`hoverlap`, `#Θ⁻¹(o) ≤ C_Q`, the routing multiplicity) — and each
charged element is dominated by its output's capacity (`hdom`), then each output absorbs at most
`C_Q · cap o`.  This is the per-output instance of the count×multiplier mechanism
(`densePackMass_le_of_density`): the absorbed mass is `(#Θ⁻¹(o)) · cap o ≤ C_Q · cap o`. -/
theorem perOutput_charged_of_overlap {ι O : Type*} [DecidableEq O]
    (F : Finset ι) (f : ι → ℝ) (chargeOf : ι → O) (outputs : Finset O) (cap : O → ℝ) (CQ : ℝ)
    (hdom : ∀ k ∈ F, f k ≤ cap (chargeOf k))
    (hcap_nonneg : ∀ o ∈ outputs, 0 ≤ cap o)
    (hoverlap : ∀ o ∈ outputs,
      ((F.filter (fun k => chargeOf k = o)).card : ℝ) ≤ CQ) :
    ∀ o ∈ outputs, (∑ k ∈ F.filter (fun k => chargeOf k = o), f k) ≤ CQ * cap o := by
  intro o ho
  have hbound : ∀ k ∈ F.filter (fun k => chargeOf k = o), f k ≤ cap o := by
    intro k hk
    obtain ⟨hkF, hko⟩ := Finset.mem_filter.mp hk
    calc f k ≤ cap (chargeOf k) := hdom k hkF
      _ = cap o := by rw [hko]
  calc (∑ k ∈ F.filter (fun k => chargeOf k = o), f k)
      ≤ ∑ _k ∈ F.filter (fun k => chargeOf k = o), cap o := Finset.sum_le_sum hbound
    _ = ((F.filter (fun k => chargeOf k = o)).card : ℝ) * cap o := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ CQ * cap o := mul_le_mul_of_nonneg_right (hoverlap o ho) (hcap_nonneg o ho)

/-- **Non-vacuity of the matching reduction (self-charging).**  The matching per-output estimate is
genuinely satisfiable: the identity (self-)charging map of *any* nonnegatively-weighted finite set
satisfies it.  Hence `perOutput_charged_of_injOn` is a non-vacuous discharge, not an empty
implication. -/
theorem perOutput_charged_of_injOn_self {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (f : ι → ℝ) (hf : ∀ k ∈ F, 0 ≤ f k) :
    ∀ o ∈ F, (∑ k ∈ F.filter (fun k => k = o), f k) ≤ f o := by
  have h := perOutput_charged_of_injOn F f (fun k => k) F f
    (fun _ _ _ _ hxy => hxy) (fun _ _ => le_refl _) hf
  simpa using h

/-- **The matching multiplier-from-charging, general form.**  Combining the matching per-output
discharge with the J.1.8 charged-ledger summation `routedClassMassOf_le_chargedArea`: a matching
charging map of the class-`i` fibre into a finite output family, with per-element charged domination
`windowExcess k ≤ cap(chargeOf k)`, gives `routedClassMassOf i ≤ ∑_o cap o` — the full multiplier
through the charging map, with **no** per-output input (only the per-element bound + matching). -/
theorem routedClassMassOf_le_chargedArea_of_matching
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7) (i : Fin 7)
    {O : Type*} [DecidableEq O] (chargeOf : ℕ → O) (outputs : Finset O) (cap : O → ℝ)
    (hmaps : ∀ k ∈ routedFibre carryData route i, chargeOf k ∈ outputs)
    (hinj : ∀ x ∈ routedFibre carryData route i, ∀ y ∈ routedFibre carryData route i,
      chargeOf x = chargeOf y → x = y)
    (hdom : ∀ k ∈ routedFibre carryData route i,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ cap (chargeOf k))
    (hcap_nonneg : ∀ o ∈ outputs, 0 ≤ cap o) :
    routedClassMassOf carryData route i ≤ ∑ o ∈ outputs, cap o :=
  routedClassMassOf_le_chargedArea carryData route i chargeOf outputs cap hmaps
    (perOutput_charged_of_injOn (routedFibre carryData route i)
      (fun k => windowExcess (hitGap carryData.a) k carryData.r carryData.T)
      chargeOf outputs cap hinj hdom hcap_nonneg)

/-- **The `C_Q`-overlap multiplier-from-charging (faithful J.1.8 + J.D form).**  The bounded-overlap
per-output discharge composed with the charged-ledger summation: `routedClassMassOf i ≤ C_Q · ∑_o
cap o`, the manuscript form in which the routing multiplicity `C_Q` is carried explicitly (and later
absorbed into the recurrence constants). -/
theorem routedClassMassOf_le_CQ_chargedArea_of_overlap
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7) (i : Fin 7)
    {O : Type*} [DecidableEq O] (chargeOf : ℕ → O) (outputs : Finset O) (cap : O → ℝ) (CQ : ℝ)
    (hmaps : ∀ k ∈ routedFibre carryData route i, chargeOf k ∈ outputs)
    (hdom : ∀ k ∈ routedFibre carryData route i,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ cap (chargeOf k))
    (hcap_nonneg : ∀ o ∈ outputs, 0 ≤ cap o)
    (hoverlap : ∀ o ∈ outputs,
      (((routedFibre carryData route i).filter (fun k => chargeOf k = o)).card : ℝ) ≤ CQ) :
    routedClassMassOf carryData route i ≤ CQ * ∑ o ∈ outputs, cap o := by
  have h := routedClassMassOf_le_chargedArea carryData route i chargeOf outputs
    (fun o => CQ * cap o) hmaps
    (perOutput_charged_of_overlap (routedFibre carryData route i)
      (fun k => windowExcess (hitGap carryData.a) k carryData.r carryData.T)
      chargeOf outputs cap CQ hdom hcap_nonneg hoverlap)
  rwa [← Finset.mul_sum] at h

/-! ## 2.  Per-class multipliers with the per-output summation discharged by matching

For each separable class the charging-map multiplier `routedClassMassOf i ≤ termᵢ` of
`ChargeAllocationConstruction` is reproved with its `hcharged` per-output **summation discharged**
by `perOutput_charged_of_injOn`, so the only remaining input is the per-element charged domination
`windowExcess k ≤ cap(chargeOf k)` (the J.1b/J.1.7/G.6/J.D per-charge bound) plus the matching
(injectivity) of the charging map.  The term identification is the proved identity of §2 of
`ChargeAllocationConstruction`. -/

/-- **Class 0 — Chernoff multiplier with the per-output summation PROVED (matching, Lemma 22.1 /
J.1.7).**

`routedClassMassOf 0 ≤ termChernoff` from a **matching** charging map of the Chernoff fibre into the
high-cost path family, with the per-path charged domination `windowExcess k ≤ weight(chargeOf k)`
(the J.1.7 per-path charged bound).  The per-output summation `hcharged` is discharged by
`perOutput_charged_of_injOn` (nonnegativity of `weight` from `data.chernoff.weight_nonneg`); the
term identification is the proved `termChernoff_eq_chargedArea`. -/
theorem routedChernoff_le_term_of_matching
    {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X)
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7)
    [DecidableEq data.chernoff.α]
    (chargeOf : ℕ → data.chernoff.α)
    (hmaps : ∀ k ∈ routedFibre carryData route 0,
      chargeOf k ∈ highCostSet data.chernoff.paths data.chernoff.cost data.chernoff.Y)
    (hinj : ∀ x ∈ routedFibre carryData route 0, ∀ y ∈ routedFibre carryData route 0,
      chargeOf x = chargeOf y → x = y)
    (hdom : ∀ k ∈ routedFibre carryData route 0,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T
        ≤ data.chernoff.weight (chargeOf k)) :
    routedClassMassOf carryData route 0 ≤ termChernoff data :=
  routedChernoff_le_term_of_charging data carryData route chargeOf hmaps
    (perOutput_charged_of_injOn (routedFibre carryData route 0)
      (fun k => windowExcess (hitGap carryData.a) k carryData.r carryData.T)
      chargeOf (highCostSet data.chernoff.paths data.chernoff.cost data.chernoff.Y)
      data.chernoff.weight hinj hdom
      (fun o ho => data.chernoff.weight_nonneg o (mem_highCostSet.mp ho).1))

/-- **Class 1 — clean-CNL multiplier with the per-output summation PROVED (matching, Theorem G.6).**

`routedClassMassOf 1 ≤ termCnl` from a **matching** charging map of the clean-CNL fibre into the CNL
Kraft path family, with the per-path charged domination
`windowExcess k ≤ 2^{-c·BND(chargeOf k)}·shellFactor·X·Ij` (the G.6 per-path Kraft-weighted charged
bound).  The per-output summation `hcharged` is discharged by `perOutput_charged_of_injOn`
(nonnegativity of the Kraft weight from `0 ≤ X` and the CNL data's `shellFactor_nonneg`,
`Ij_nonneg`); the term identification is the proved `termCnl_eq_chargedArea`. -/
theorem routedCnl_le_term_of_matching
    {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X) (hX : 0 ≤ X)
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7)
    [DecidableEq data.cnl.α]
    (chargeOf : ℕ → data.cnl.α)
    (hmaps : ∀ k ∈ routedFibre carryData route 1, chargeOf k ∈ data.cnl.paths)
    (hinj : ∀ x ∈ routedFibre carryData route 1, ∀ y ∈ routedFibre carryData route 1,
      chargeOf x = chargeOf y → x = y)
    (hdom : ∀ k ∈ routedFibre carryData route 1,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T
        ≤ (2 : ℝ) ^ (-(data.cnl.c * data.cnl.BNDHeight (chargeOf k))) * data.cnl.shellFactor * X
            * data.cnl.Ij) :
    routedClassMassOf carryData route 1 ≤ termCnl data :=
  routedCnl_le_term_of_charging data carryData route chargeOf hmaps
    (perOutput_charged_of_injOn (routedFibre carryData route 1)
      (fun k => windowExcess (hitGap carryData.a) k carryData.r carryData.T)
      chargeOf data.cnl.paths
      (fun o => (2 : ℝ) ^ (-(data.cnl.c * data.cnl.BNDHeight o)) * data.cnl.shellFactor * X
        * data.cnl.Ij)
      hinj hdom
      (fun o _ => by
        have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(data.cnl.c * data.cnl.BNDHeight o)) :=
          Real.rpow_nonneg (by norm_num) _
        exact mul_nonneg (mul_nonneg (mul_nonneg h2 data.cnl.shellFactor_nonneg) hX)
          data.cnl.Ij_nonneg))

/-- **Class 3 — DensePack multiplier with the per-output summation PROVED (matching, Lemma J.D).**

`routedClassMassOf 3 ≤ termDensePack` from a **matching** charging map of the DensePack fibre into
the dense-marker point set, with the per-marker charged domination `windowExcess k ≤ 1` (the J.D
statement that **each marker absorbs at most one unit** of routed carry mass).  The per-output
summation `hcharged` is discharged by `perOutput_charged_of_injOn` (cap `≡ 1 ≥ 0`); the term
identification is the proved `termDensePack_eq_chargedArea`. -/
theorem routedDensePack_le_term_of_matching
    {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X)
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7)
    (chargeOf : ℕ → ℕ)
    (hmaps : ∀ k ∈ routedFibre carryData route 3, chargeOf k ∈ data.densePack.densePackPoints)
    (hinj : ∀ x ∈ routedFibre carryData route 3, ∀ y ∈ routedFibre carryData route 3,
      chargeOf x = chargeOf y → x = y)
    (hdom : ∀ k ∈ routedFibre carryData route 3,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ (1 : ℝ)) :
    routedClassMassOf carryData route 3 ≤ termDensePack data :=
  routedDensePack_le_term_of_charging data carryData route chargeOf hmaps
    (perOutput_charged_of_injOn (routedFibre carryData route 3)
      (fun k => windowExcess (hitGap carryData.a) k carryData.r carryData.T)
      chargeOf data.densePack.densePackPoints (fun _ => (1 : ℝ)) hinj hdom
      (fun _ _ => by norm_num))

/-! ## 3.  old-residual (class 6): per-output by matching, term identification from the proved core -/

/-- **Class 6 — old-residual multiplier with the per-output summation PROVED (matching, Lemma L.6.4).**

`routedClassMassOf 6 ≤ oldResMass` from a **matching** charging map of the old-residual fibre into
the retained endpoint set `K` with per-endpoint capacity `oldResAt`, the per-endpoint charged
domination `windowExcess k ≤ oldResAt(chargeOf k)`, the charged-mass nonnegativity
`0 ≤ oldResAt o`, and the term identification `∑_{o∈K} oldResAt o ≤ oldResMass`.  The per-output
summation `hcharged` is discharged by `perOutput_charged_of_injOn`. -/
theorem routedOldRes_le_mass_of_matching
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7)
    (chargeOf : ℕ → ℕ) (K : Finset ℕ) (oldResAt : ℕ → ℝ) {oldResMass : ℝ}
    (hmaps : ∀ k ∈ routedFibre carryData route 6, chargeOf k ∈ K)
    (hinj : ∀ x ∈ routedFibre carryData route 6, ∀ y ∈ routedFibre carryData route 6,
      chargeOf x = chargeOf y → x = y)
    (hdom : ∀ k ∈ routedFibre carryData route 6,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ oldResAt (chargeOf k))
    (hAt_nonneg : ∀ o ∈ K, 0 ≤ oldResAt o)
    (hident : (∑ o ∈ K, oldResAt o) ≤ oldResMass) :
    routedClassMassOf carryData route 6 ≤ oldResMass :=
  routedOldRes_le_mass_of_charging carryData route chargeOf K oldResAt hmaps
    (perOutput_charged_of_injOn (routedFibre carryData route 6)
      (fun k => windowExcess (hitGap carryData.a) k carryData.r carryData.T)
      chargeOf K oldResAt hinj hdom hAt_nonneg)
    hident

/-- **Class 6 — old-residual multiplier, per-output by matching AND term by the proved core.**

The fully grounded old-residual multiplier: the per-output summation is discharged by matching
(`perOutput_charged_of_injOn`), and the term identification `∑_{o∈K} oldResAt o ≤ c₀·X·bound +
collar·bound` is discharged by the **proved** OldResCountFromCarry core `oldRes_le_of_carryFailure`
(Lemma L.6.4 / eq. L.22, the failure-bounded endpoint count).  Hence

  `routedClassMassOf 6 ≤ c₀·X·(C_res·Y·C_supp·Ij) + (2cW+1)·(C_res·Y·C_supp·Ij)`,

the v5 recurrence-I.11' old-residual floor, with the only inputs being the matching, the
per-endpoint charged domination + nonnegativity, the retained-index containment `K ⊆ window`, and
the L.20/L.21 per-index multiplier × support primitives. -/
theorem routedOldRes_le_density_of_matching
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7) (cW : ℕ)
    (chargeOf : ℕ → ℕ) {K : Finset ℕ} {oldResAt : ℕ → ℝ} {Cres Y Csupp Ij : ℝ}
    (hmaps : ∀ k ∈ routedFibre carryData route 6, chargeOf k ∈ K)
    (hinj : ∀ x ∈ routedFibre carryData route 6, ∀ y ∈ routedFibre carryData route 6,
      chargeOf x = chargeOf y → x = y)
    (hKsub : K ⊆ windowHitIndices carryData.a (shell.X - cW) (2 * shell.X + cW))
    (hpoint : ∀ k ∈ K, oldResAt k ≤ (Cres * Y) * (Csupp * Ij))
    (hbound_nonneg : 0 ≤ (Cres * Y) * (Csupp * Ij))
    (hAt_nonneg : ∀ o ∈ K, 0 ≤ oldResAt o)
    (hdom : ∀ k ∈ routedFibre carryData route 6,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ oldResAt (chargeOf k)) :
    routedClassMassOf carryData route 6
      ≤ shell.c0 * (shell.X : ℝ) * ((Cres * Y) * (Csupp * Ij))
        + (2 * (cW : ℝ) + 1) * ((Cres * Y) * (Csupp * Ij)) :=
  routedOldRes_le_mass_of_matching carryData route chargeOf K oldResAt hmaps hinj hdom hAt_nonneg
    (oldRes_le_of_carryFailure carryData cW hKsub hpoint hbound_nonneg)

/-! ## 4.  joint Tower+Return+Run (classes 2+4+5): per-output by matching, term by the proved N.3.1 -/

/-- **Joint TRT multiplier with the per-output summation PROVED (matching) + the proved N.3.1
compression.**

The joint Tower+Return+Run mass `routedClassMassOf 2 + routedClassMassOf 4 + routedClassMassOf 5 ≤
termTower + termReturn + termRun` from a **matching** charging map of the *union* of the three
fibres into the same-threshold terminal output family `comp.branches`, with the per-branch charged
domination `windowExcess k ≤ comp.wtO(chargeOf k)`, the charged-weight nonnegativity
`0 ≤ comp.wtO b`, and the N.3.3 absorption `hAbsorb`.  The per-output summation `hcharged` is
discharged by `perOutput_charged_of_injOn`; the term identification chains the **proved** Lemma
N.3.1 compression `comp.compression` with `hAbsorb`, inside
`routedTRT_le_term_via_terminalOutput`. -/
theorem routedTRT_le_term_via_terminalOutput_matching
    {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X)
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7)
    {β σ : Type*} [DecidableEq σ] [DecidableEq β]
    (comp : AppendixN.TerminalOutputData β σ) (chargeOf : ℕ → β)
    (hmaps : ∀ k ∈ (routedFibre carryData route 2 ∪ routedFibre carryData route 4
          ∪ routedFibre carryData route 5),
        chargeOf k ∈ comp.branches)
    (hinj : ∀ x ∈ (routedFibre carryData route 2 ∪ routedFibre carryData route 4
          ∪ routedFibre carryData route 5),
        ∀ y ∈ (routedFibre carryData route 2 ∪ routedFibre carryData route 4
          ∪ routedFibre carryData route 5),
        chargeOf x = chargeOf y → x = y)
    (hdom : ∀ k ∈ (routedFibre carryData route 2 ∪ routedFibre carryData route 4
          ∪ routedFibre carryData route 5),
        windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ comp.wtO (chargeOf k))
    (hwtO_nonneg : ∀ b ∈ comp.branches, 0 ≤ comp.wtO b)
    (hAbsorb : comp.CQ * (comp.YO * ∑ ζ ∈ comp.ground, comp.fibreMass ζ)
      ≤ termTower data + termReturn data + termRun data) :
    routedClassMassOf carryData route 2 + routedClassMassOf carryData route 4
        + routedClassMassOf carryData route 5
      ≤ termTower data + termReturn data + termRun data :=
  routedTRT_le_term_via_terminalOutput data carryData route comp chargeOf hmaps
    (perOutput_charged_of_injOn
      (routedFibre carryData route 2 ∪ routedFibre carryData route 4
        ∪ routedFibre carryData route 5)
      (fun k => windowExcess (hitGap carryData.a) k carryData.r carryData.T)
      chargeOf comp.branches comp.wtO hinj hdom hwtO_nonneg)
    hAbsorb

/-! ## 5.  The J.5 `StructuralPkgGeometry` for the failing shell — `pkg_exposes` furnished

The J.1.1 coverage primitive `pkg_exposes` (a non-clean `PKG` verdict exposes a genuine charge
package) is **supplied as a theorem** for the failing dyadic shell, via the manuscript-faithful J.5
structural geometry: under J.5's definition `PKG-available := (six-package disjunction)`, the
coverage residual is the proved `StructuralPkgGeometry.pkg_exposes` / `pkg_verdict_routes_to_package`
(`ChargeAllocationConstruction`).  The failing shell's dense-density failure is presented as a `PKG`
exit routing to the DensePack charge class `3`. -/

/-- **The J.5 structural package geometry for a failing shell (parameterised by its carry-word
package label).**  Built by `StructuralPkgGeometry.ofLabel`: the clean-ladder availability is the
`PKG`-free singleton `{TP}` everywhere (clean visibility), and `PKG` fires exactly where the
free carry-word geometry `lab` exposes a package.  For this geometry `pkg_exposes` is a theorem. -/
def failingShellPkgGeometry (lab : LiftState → Option GeomPackage) : StructuralPkgGeometry :=
  StructuralPkgGeometry.ofLabel lab

/-- **`pkg_exposes` furnished for the failing-shell geometry (theorem, not assumption).**  A `PKG`
verdict exposes one of the six geometric charge packages — the proved
`StructuralPkgGeometry.pkg_exposes`, no coverage hypothesis. -/
theorem failingShellPkgGeometry_pkg_exposes (lab : LiftState → Option GeomPackage) (s : LiftState)
    (h : canonicalCNLSelector ((failingShellPkgGeometry lab).cnlOf s) = some CNLClass.pkg) :
    ∃ c : Fin 7, (failingShellPkgGeometry lab).toMarking.geomDetect c s = true :=
  (failingShellPkgGeometry lab).pkg_exposes s h

/-- **The first-obstruction routing of a `PKG` exit, for the failing-shell geometry.**  A `PKG`
verdict with package label `p` makes the J.1.1 scan route the start to `p`'s charge class
`p.toCharge` — the proved `pkg_verdict_routes_to_package`. -/
theorem failingShellPkgGeometry_routes (lab : LiftState → Option GeomPackage)
    (config : ℕ → LiftState) {k : ℕ} {p : GeomPackage}
    (hpkg : canonicalCNLSelector ((failingShellPkgGeometry lab).cnlOf (config k))
      = some CNLClass.pkg)
    (hlabel : (failingShellPkgGeometry lab).label (config k) = some p) :
    ((failingShellPkgGeometry lab).toMarking.toObstructionGeometry.toRouting config).classify k
      = p.toCharge :=
  pkg_verdict_routes_to_package (failingShellPkgGeometry lab) config hpkg hlabel

/-- **Concrete failing-shell geometry: the dense-density failure as a `PKG`→DensePack exit.**  States
with `δ = 0` (the degenerate density layer of the failing shell) expose the DensePack package; all
other states are CNL-clean.  This realises the J.5 geometry for the failing shell with both branches
genuinely present. -/
def densePackFailureGeometry : StructuralPkgGeometry :=
  failingShellPkgGeometry (fun s => if s.δ = 0 then some GeomPackage.densePack else none)

/-- Non-vacuity (PKG branch): the `δ = 0` states are genuine `PKG` exits. -/
theorem densePackFailureGeometry_pkg_exit (s : LiftState) (h : s.δ = 0) :
    canonicalCNLSelector (densePackFailureGeometry.cnlOf s) = some CNLClass.pkg := by
  rw [StructuralPkgGeometry.selector_eq_pkg_iff]
  simp [densePackFailureGeometry, failingShellPkgGeometry, StructuralPkgGeometry.ofLabel, h]

/-- Non-vacuity (clean branch): the `δ ≠ 0` states are genuinely CNL-clean. -/
theorem densePackFailureGeometry_clean (s : LiftState) (h : s.δ ≠ 0) :
    canonicalCNLSelector (densePackFailureGeometry.cnlOf s) ≠ some CNLClass.pkg := by
  intro hpkg
  rw [StructuralPkgGeometry.selector_eq_pkg_iff] at hpkg
  simp [densePackFailureGeometry, failingShellPkgGeometry, StructuralPkgGeometry.ofLabel, h] at hpkg

/-- **`pkg_exposes` furnished concretely.**  A `δ = 0` failing-shell state exposes a charge package. -/
theorem densePackFailureGeometry_exposes (s : LiftState) (h : s.δ = 0) :
    ∃ c : Fin 7, densePackFailureGeometry.toMarking.geomDetect c s = true :=
  densePackFailureGeometry.pkg_exposes s (densePackFailureGeometry_pkg_exit s h)

/-- **The failing-shell dense-density `PKG` exit routes to the DensePack charge class `3`.**  The
J.1.1 first-obstruction scan of a `δ = 0` state routes it to `GeomPackage.densePack.toCharge = 3`,
discharged with no coverage hypothesis (the routing is the proved
`pkg_verdict_routes_to_package`). -/
theorem densePackFailureGeometry_routes_to_densePack (config : ℕ → LiftState) {k : ℕ}
    (h : (config k).δ = 0) :
    (densePackFailureGeometry.toMarking.toObstructionGeometry.toRouting config).classify k
      = (3 : Fin 7) := by
  have hlabel : densePackFailureGeometry.label (config k) = some GeomPackage.densePack := by
    simp [densePackFailureGeometry, failingShellPkgGeometry, StructuralPkgGeometry.ofLabel, h]
  have hroute := pkg_verdict_routes_to_package densePackFailureGeometry config
    (densePackFailureGeometry_pkg_exit (config k) h) hlabel
  exact hroute.trans rfl

/-! ## 6.  Honest per-class residual inventory -/

/-- The honest per-class status of the per-output charged estimates after this round. -/
def chargePerOutputResidual : List String :=
  [ "FRAMEWORK: the per-output charged estimate `∑_{k:Θ(k)=o} windowExcess k ≤ cap o` is the " ++
      "manuscript J.D/J.Rt/J.Rn/J.T/J.PE charging content (`∑_{b:Θ(b)=O} wt(b) ≤ C_𝔭 wt(O)`, " ++
      "proof_v4 §J.1.3-J.1.8, proved in Appendix L.2). It is ORTHOGONAL to every phase core: the " ++
      "cores bound the output AREA `∑_o cap o` (the term identification), NOT the carry mass each " ++
      "output absorbs. So NO per-output charged estimate follows from a phase core — confirmed, not " ++
      "claimed otherwise.",
    "PROVED (all 7 classes): the per-output SUMMATION half is discharged from a MATCHING " ++
      "(injective-on-fibre) charging map + per-element charged domination `windowExcess k ≤ " ++
      "cap(Θ k)` via `perOutput_charged_of_injOn` (the C=1 case of J.1.8 at per-output granularity). " ++
      "The faithful C_Q-multiplicity form `≤ C_Q·cap o` is `perOutput_charged_of_overlap`. This " ++
      "reduces `hcharged` to its smallest genuine form: per-element domination + matching.",
    "Chernoff (0): per-output NOT from the Lemma 22.1 core (orthogonal). Summation PROVED via " ++
      "matching (`routedChernoff_le_term_of_matching`); remaining input = per-path charged " ++
      "domination `windowExcess k ≤ weight(Θ k)` (J.1.7) + matching. Term identification proved (rfl).",
    "clean-CNL (1): per-output NOT from the Theorem G.6 core (orthogonal). Summation PROVED via " ++
      "matching (`routedCnl_le_term_of_matching`); remaining input = per-path Kraft charged " ++
      "domination (G.6) + matching + 0≤X. Term identification proved (`termCnl_eq_chargedArea`).",
    "DensePack (3): per-output NOT from the K.1.x core (orthogonal). Summation PROVED via matching " ++
      "(`routedDensePack_le_term_of_matching`); remaining input = per-marker domination " ++
      "`windowExcess k ≤ 1` (exactly J.D: each marker absorbs ≤ 1 unit) + matching. Term proved.",
    "Tower+Return+Run (2+4+5): per-output NOT from N.3.1 (orthogonal). Summation PROVED JOINTLY via " ++
      "matching onto the shared same-threshold output family " ++
      "(`routedTRT_le_term_via_terminalOutput_matching`); remaining input = per-branch domination " ++
      "`windowExcess k ≤ wtO(Θ k)` + matching + wtO nonneg + N.3.3 absorption. TERM-side IS from a " ++
      "core: the proved Lemma N.3.1 compression `comp.compression`.",
    "old-residual (6): per-output NOT from L.6.4/L.22 (orthogonal). Summation PROVED via matching " ++
      "(`routedOldRes_le_mass_of_matching`); remaining input = per-endpoint domination + matching + " ++
      "nonneg. TERM-side IS from a core: `routedOldRes_le_density_of_matching` discharges " ++
      "`∑_{o∈K} oldResAt o` by the PROVED `oldRes_le_of_carryFailure` (L.6.4/L.22 failure-bounded " ++
      "endpoint count), giving `routedClassMassOf 6 ≤ c₀·X·bound + collar·bound`.",
    "pkg_exposes: FURNISHED (not assumed) for the failing shell via the J.5 `StructuralPkgGeometry` " ++
      "(`failingShellPkgGeometry` / `densePackFailureGeometry`): a non-clean PKG verdict structurally " ++
      "exposes a package (`failingShellPkgGeometry_pkg_exposes`, the proved " ++
      "`StructuralPkgGeometry.pkg_exposes`) and the dense-density failure routes to the DensePack " ++
      "charge `3` (`densePackFailureGeometry_routes_to_densePack`). Non-vacuous: PKG-exit (δ=0) and " ++
      "clean (δ≠0) states both realised." ]

theorem chargePerOutputResidual_ne_nil : chargePerOutputResidual ≠ [] := by
  simp [chargePerOutputResidual]

/-- **Non-vacuity capstone.**  The matching per-output discharge fires on genuine data (the
self-charging instance) and the failing-shell `pkg_exposes` is furnished with both branches present
— so neither the per-output reductions nor the structural geometry is a vacuous construction. -/
theorem chargePerOutput_nonvacuous :
    (∀ (F : Finset ℕ) (f : ℕ → ℝ), (∀ k ∈ F, 0 ≤ f k) →
      ∀ o ∈ F, (∑ k ∈ F.filter (fun k => k = o), f k) ≤ f o)
    ∧ (∀ s : LiftState, s.δ = 0 →
        canonicalCNLSelector (densePackFailureGeometry.cnlOf s) = some CNLClass.pkg)
    ∧ (∀ s : LiftState, s.δ ≠ 0 →
        canonicalCNLSelector (densePackFailureGeometry.cnlOf s) ≠ some CNLClass.pkg) :=
  ⟨fun F f hf => perOutput_charged_of_injOn_self F f hf,
    densePackFailureGeometry_pkg_exit, densePackFailureGeometry_clean⟩

end

end Erdos260
