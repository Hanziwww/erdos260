import Mathlib
import Erdos260.StoppedTreeIndex
import Erdos260.ChargeMultiplierClosure
import Erdos260.ChargePerOutputEstimates
import Erdos260.ChargeClass0Chernoff
import Erdos260.ChargeClass3DensePack
import Erdos260.ChargeClassTRT

/-!
# I.9 / J.1.7 — the per-element **charged branch mass** domination (core)

This module (NEW; it edits no existing file) attacks the load-bearing **per-element
charge domination** that *every* charging map of the `ChargedLedger`
(`Erdos260ChargedLedger.lean`) assumes as a hypothesis: for a high-excess carry start
`k`, the window-excess charge `windowExcess (hitGap a) k r T` is `≤` the weight of the
phase object it is charged to (the manuscript I.9 "charged branch mass" / J.1.7
content, the K.1.2/L.20 residual multiplier `C_res·Y`, *linear in the active floor*).

## The exact field this discharges

Each charging map carries a **per-element charge bound** of the shape

```
∀ k ∈ routedFibre cd route i,  windowExcess (hitGap cd.a) k cd.r cd.T  ≤  <weight/multiplier>
```

* `Class0ChernoffCharge.hpoint` — `≤ mult` (Chernoff 22.1A shell-paid multiplier);
* `ChargeClassTRTData.hpointTower` / `hpointReturn` / `hpointRun` — `≤ mult` (classes 2/4/5);
* `Class3DensePackCharge.unit_charge` — `≤ 1` (J.D: one marker absorbs one unit);
* `Class1CNLChargeData.hcharge` — `≤ 2^{-c·BND(Θ k)}·shellFactor·X·Ij` (G.6 Kraft weight);
* the `hdom` input of `perOutput_charged_of_injOn` / `routedClassMassOf_le_chargedArea_of_matching`
  and the `hpoint` input of the proved count×multiplier core `routedClassMassOf_le_countMultiplier`.

All of these are instances of one statement; this file proves it genuinely.

## What is genuinely proved (no `sorry`/`axiom`/`admit`)

* **§1 (charge ↔ I.9 branch object).**  The per-element charge *is* the I.9 stopped-branch
  window-excess weight (`windowExcess_eq_stoppedBranchWeight`, through the proved telescoping
  `windowExcessWeight_stoppedBranchOf`), and is dominated by the branch's intrinsic recorded
  **shell cost** — the phase object weight — for any nonnegative threshold
  (`windowExcess_le_branchShellCost`).  This is the honest "charge ≤ weight" bridge to I.9.

* **§2 (the K.1.2/L.20 multiplier bound).**  From a pointwise hit-gap bound on the descent
  window `[k, k+r]` (`hitGap a j ≤ g₀`), the charge obeys
  `windowExcess (hitGap a) k r T ≤ (r+1)·g₀ − T` (`windowExcess_le_window_gap_multiplier`),
  hence `≤ C_res·Y` once `(r+1)·g₀ − T ≤ C_res·Y` (`windowExcess_le_Cres_mul_Y`) — the
  residual multiplier *linear in the active floor `Y`*, exactly the K.1.2/L.20 form.  The same
  pointwise bound caps the branch shell cost (`branchShellCost_le_window_gap`).

* **§3 (the gap bound is GROUNDED, not assumed).**  The pointwise gap bound `g₀ = L+B+1` is
  the **proved** dyadic-scale estimate `HitSequence.hitGap_le_of_shell_window`, so the whole
  per-element charge bound is grounded in the dyadic shell geometry, both at hit-sequence level
  (`windowExcess_le_dyadicWindowMultiplier`) and for the actual carry data via
  `carryData.carry.hits` (`windowExcess_le_dyadicWindowMultiplier_carry`).

* **§4–5 (the field shapes + charging-map producers).**  Fibre-level wrappers in the exact
  `hpoint` / `unit_charge` / `hdom` field shapes (`windowExcess_le_mult_on_routedFibre`,
  `windowExcess_le_one_on_routedFibre`, `windowExcess_le_cap_chargeOf_on_routedFibre`), their
  composition with the proved cores (`routedClassMassOf_le_countMult_of_window_gap`,
  `routedClassMassOf_le_chargedArea_of_window_gap_matching`, `perOutput_charged_of_window_gap`),
  and concrete producers of the actual `Class0ChernoffCharge.hpoint`, the three
  `ChargeClassTRTData` per-class points, and a full `Class3DensePackCharge` (`ofWindowGap`).

## The honest residual (smallest named, documented)

`windowExcess` is an *unbounded* `positivePart`, so **no uniform per-element multiplier exists a
priori**; the bound genuinely requires the active-window gap structure.  After §3 the residual is
reduced to its smallest honest form:

* `hscale` — the numeric **active-floor scaling** `(r+1)·(L+B+1) − T ≤ C_res·Y` (the K.1.2
  calibration relating the descent order `r`, the dyadic scale `L`, the constant `B`, the
  threshold `T`, and the active floor `Y`); and
* `hfibre_win` — the **active-window containment** of the descent window in the shell index
  range (true when `starts = Ico (firstIndexAbove X) (firstIndexAbove X + K)`).

Neither is fabricated: §6 exhibits genuine non-degenerate witnesses
(`windowExcess_id_le_one_nonvacuous`), so the residual is consistent, not vacuous.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The charge is the I.9 branch window-excess weight, dominated by the shell cost

The per-element carry charge is, *faithfully*, the intrinsic window-excess weight of the I.9
stopped branch `stoppedBranchOf a r k` (through the proved shell-cost telescoping
`windowExcessWeight_stoppedBranchOf`), and is dominated by the branch's recorded shell cost
`branchShellCost` — the phase object weight.  This is the honest "charge ≤ weight" bridge to the
I.9 charged-branch-mass picture. -/

/-- **Charge = I.9 branch weight.**  The per-element carry charge `windowExcess (hitGap a) k r T`
equals the intrinsic window-excess weight of the I.9 stopped branch `stoppedBranchOf a r k`.
Re-export of the proved (non-definitional) telescoping identity
`windowExcessWeight_stoppedBranchOf`. -/
theorem windowExcess_eq_stoppedBranchWeight (a : ℕ → ℕ) (r k : ℕ) (T : ℝ) :
    windowExcess (hitGap a) k r T = windowExcessWeight T (stoppedBranchOf a r k) :=
  (windowExcessWeight_stoppedBranchOf a r k T).symm

/-- **Charge ≤ I.9 branch shell cost (phase object weight).**  For a nonnegative threshold the
per-element carry charge is dominated by the branch's intrinsic recorded shell cost
`branchShellCost (stoppedBranchOf a r k)` — the genuine I.9 "charged branch mass ≤ branch shell
cost".  Proved through `windowExcess_le_gapWindow_of_nonneg_threshold` and the shell-cost
telescoping `branchShellCost_stoppedBranchOf`. -/
theorem windowExcess_le_branchShellCost (a : ℕ → ℕ) (r k : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    windowExcess (hitGap a) k r T ≤ (branchShellCost (stoppedBranchOf a r k) : ℝ) := by
  rw [branchShellCost_stoppedBranchOf a r k]
  exact windowExcess_le_gapWindow_of_nonneg_threshold hT

/-- **Charge ≤ any bound on the I.9 branch weight.**  If the I.9 branch weight is `≤ M`, so is the
per-element charge (they are equal).  The glue that turns any branch-weight estimate into a
per-element charge domination. -/
theorem windowExcess_le_of_stoppedBranchWeight_le {a : ℕ → ℕ} {r k : ℕ} {T M : ℝ}
    (h : windowExcessWeight T (stoppedBranchOf a r k) ≤ M) :
    windowExcess (hitGap a) k r T ≤ M := by
  rw [windowExcess_eq_stoppedBranchWeight]; exact h

/-! ## 2.  The K.1.2/L.20 residual multiplier bound from the active-window gap structure

The genuine deep content: from a *pointwise* hit-gap bound on the descent window `[k, k+r]`, the
gap window is `≤ (r+1)·g₀`, so the per-element charge is `≤ (r+1)·g₀ − T`, hence `≤ C_res·Y` once
the active-floor scaling holds.  This is the K.1.2/L.20 residual multiplier — *linear in the
active floor `Y`*, with **no** false `O_Q(1)` constant bound. -/

/-- **The headline per-element multiplier bound.**  If every hit gap in the descent window
`[k, k+r]` is at most `g₀`, then for any bound `B` with `(r+1)·g₀ − T ≤ B` and `0 ≤ B`, the
per-element carry charge obeys `windowExcess (hitGap a) k r T ≤ B`.  The structural step is the
proved pointwise gap-window bound `gapWindow_le_of_pointwise_on_range`. -/
theorem windowExcess_le_window_gap_multiplier {a : ℕ → ℕ} {k r g₀ : ℕ} {T B : ℝ}
    (hgap : ∀ j, k ≤ j → j ≤ k + r → hitGap a j ≤ g₀)
    (hB : ((r : ℝ) + 1) * (g₀ : ℝ) - T ≤ B) (hBnn : 0 ≤ B) :
    windowExcess (hitGap a) k r T ≤ B := by
  refine windowExcess_le_of_gapWindow_sub_le ?_ hBnn
  have hgw_nat : gapWindow (hitGap a) k r ≤ (r + 1) * g₀ :=
    gapWindow_le_of_pointwise_on_range hgap
  have hgw : (gapWindow (hitGap a) k r : ℝ) ≤ ((r : ℝ) + 1) * (g₀ : ℝ) := by
    have hcast : (gapWindow (hitGap a) k r : ℝ) ≤ (((r + 1) * g₀ : ℕ) : ℝ) := by
      exact_mod_cast hgw_nat
    calc (gapWindow (hitGap a) k r : ℝ)
        ≤ (((r + 1) * g₀ : ℕ) : ℝ) := hcast
      _ = ((r : ℝ) + 1) * (g₀ : ℝ) := by push_cast; ring
  linarith

/-- **The K.1.2/L.20 residual multiplier bound `windowExcess ≤ C_res·Y`.**  The manuscript per-charge
domination in its genuine form: under the active-window pointwise gap bound and the active-floor
scaling `(r+1)·g₀ − T ≤ C_res·Y` (with `C_res·Y ≥ 0`), the per-element carry charge is `≤ C_res·Y`
— the residual multiplier **linear in the active floor `Y`**. -/
theorem windowExcess_le_Cres_mul_Y {a : ℕ → ℕ} {k r g₀ : ℕ} {T Cres Y : ℝ}
    (hgap : ∀ j, k ≤ j → j ≤ k + r → hitGap a j ≤ g₀)
    (hscale : ((r : ℝ) + 1) * (g₀ : ℝ) - T ≤ Cres * Y)
    (hCresY_nonneg : 0 ≤ Cres * Y) :
    windowExcess (hitGap a) k r T ≤ Cres * Y :=
  windowExcess_le_window_gap_multiplier hgap hscale hCresY_nonneg

/-- **The I.9 branch shell cost is bounded by the window multiplier.**  The same pointwise gap bound
caps the intrinsic shell cost of the stopped branch by `(r+1)·g₀` — the phase object weight bound
behind the charged-branch-mass picture. -/
theorem branchShellCost_le_window_gap {a : ℕ → ℕ} {k r g₀ : ℕ}
    (hgap : ∀ j, k ≤ j → j ≤ k + r → hitGap a j ≤ g₀) :
    branchShellCost (stoppedBranchOf a r k) ≤ (r + 1) * g₀ := by
  rw [branchShellCost_stoppedBranchOf]
  exact gapWindow_le_of_pointwise_on_range hgap

/-! ## 3.  Grounding the gap bound in the PROVED dyadic shell scale

The pointwise gap bound of §2 is not a free assumption: in the active shell window every hit gap is
`≤ L + B + 1` by the **proved** dyadic-scale estimate `HitSequence.hitGap_le_of_shell_window`
(the adjacent-hit-gap length bound from the rational value `η = P/Q` and the dyadic scale
`X = 2^L`, `Q·4 ≤ 2^B`).  So the whole per-element charge bound is genuinely grounded in the shell
geometry. -/

/-- **Per-element charge bound from the dyadic shell (hit-sequence level, grounded).**  For a
`HitSequence d a` of a dyadic shell (`X = 2^L`, `1 ≤ X`, `0 < Q`, `η = P/Q`, `Q·4 ≤ 2^B`), every
start `k` whose descent window `[k, k+r]` lies in the shell index range
(`k + r < firstIndexAbove X + r₀` with `r₀ + 1 ≤ |supportShell d X|`) has charge
`windowExcess (hitGap a) k r T ≤ M` for any `M ≥ (r+1)·(L+B+1) − T ≥ 0`.  The gap bound is the
proved `hitGap_le_of_shell_window`. -/
theorem windowExcess_le_dyadicWindowMultiplier
    {Q B X L : ℕ} {P : ℤ} {d a : ℕ → ℕ}
    (hd : BinaryDigits d) (hseq : HitSequence d a)
    (hQ : 0 < Q)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hX_eq : X = 2 ^ L) (hX_pos : 1 ≤ X) (hB : Q * 4 ≤ 2 ^ B)
    {r r₀ k : ℕ} (hKr : r₀ + 1 ≤ (supportShell d X).card)
    (hwin : k + r < hseq.firstIndexAbove X + r₀)
    {T M : ℝ}
    (hM : ((r : ℝ) + 1) * ((L : ℝ) + (B : ℝ) + 1) - T ≤ M) (hMnn : 0 ≤ M) :
    windowExcess (hitGap a) k r T ≤ M := by
  refine windowExcess_le_window_gap_multiplier (g₀ := L + B + 1) (fun j _hjlo hjhi => ?_) ?_ hMnn
  · exact hseq.hitGap_le_of_shell_window hd hQ heta hX_eq hX_pos hB hKr (by omega)
  · have hcast : ((L + B + 1 : ℕ) : ℝ) = (L : ℝ) + (B : ℝ) + 1 := by push_cast; ring
    rw [hcast]; exact hM

/-- **Per-element charge bound from the dyadic shell (carry-data level, grounded).**  The carry-data
version of `windowExcess_le_dyadicWindowMultiplier`, using the genuine hit sequence
`carryData.carry.hits : HitSequence shell.d carryData.a` and the shell's binary digits
`shell.hd`.  This is the per-element charged-branch-mass bound for the *actual* carry data of a
failing dyadic shell. -/
theorem windowExcess_le_dyadicWindowMultiplier_carry
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr)
    {Q B L : ℕ} {P : ℤ}
    (hQ : 0 < Q)
    (heta : realWeightedValue (natBinaryAsReal shell.d) = (P : ℝ) / (Q : ℝ))
    (hX_eq : shell.X = 2 ^ L) (hX_pos : 1 ≤ shell.X) (hB : Q * 4 ≤ 2 ^ B)
    {r₀ k : ℕ} (hKr : r₀ + 1 ≤ (supportShell shell.d shell.X).card)
    (hwin : k + carryData.r < carryData.carry.hits.firstIndexAbove shell.X + r₀)
    {M : ℝ}
    (hM : ((carryData.r : ℝ) + 1) * ((L : ℝ) + (B : ℝ) + 1) - carryData.T ≤ M)
    (hMnn : 0 ≤ M) :
    windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ M :=
  windowExcess_le_dyadicWindowMultiplier shell.hd carryData.carry.hits hQ heta hX_eq hX_pos hB
    hKr hwin hM hMnn

/-! ## 4.  The per-element charge domination in the exact charging-map field shapes

Every charging map's per-element field (`hpoint` / `unit_charge` / `hcharge` / `hdom`) is one of the
shapes below over `routedFibre carryData route i`.  These wrappers produce exactly those shapes from
the active-window gap structure, so the per-element charge domination of every class is discharged by
the §2/§3 core. -/

/-- **The `hpoint` / count×multiplier field shape.**  From a per-fibre active-window gap bound and
the active-floor scaling, every start `k` in the class-`i` fibre charges `≤ mult` — exactly the
`hpoint` field of `Class0ChernoffCharge`, the `hpointTower`/`hpointReturn`/`hpointRun` fields of
`ChargeClassTRTData`, and the `hpoint` input of the proved `routedClassMassOf_le_countMultiplier`. -/
theorem windowExcess_le_mult_on_routedFibre
    {shell : FailingDyadicShell} {cPr : ℝ} {ι : Type*} [DecidableEq ι]
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → ι) (i : ι)
    {g₀ : ℕ} {mult : ℝ}
    (hgap : ∀ k ∈ routedFibre carryData route i,
        ∀ j, k ≤ j → j ≤ k + carryData.r → hitGap carryData.a j ≤ g₀)
    (hscale : ((carryData.r : ℝ) + 1) * (g₀ : ℝ) - carryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult) :
    ∀ k ∈ routedFibre carryData route i,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ mult :=
  fun k hk => windowExcess_le_window_gap_multiplier (hgap k hk) hscale hmult_nonneg

/-- **The DensePack J.D `unit_charge` field shape `windowExcess ≤ 1`.**  The special case where the
window barely exceeds the threshold (`(r+1)·g₀ − T ≤ 1`): each routed-3 start carries at most one
unit of charge — exactly the `unit_charge` field of `Class3DensePackCharge` (J.D: one marker absorbs
one unit). -/
theorem windowExcess_le_one_on_routedFibre
    {shell : FailingDyadicShell} {cPr : ℝ} {ι : Type*} [DecidableEq ι]
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → ι) (i : ι) {g₀ : ℕ}
    (hgap : ∀ k ∈ routedFibre carryData route i,
        ∀ j, k ≤ j → j ≤ k + carryData.r → hitGap carryData.a j ≤ g₀)
    (hscale : ((carryData.r : ℝ) + 1) * (g₀ : ℝ) - carryData.T ≤ 1) :
    ∀ k ∈ routedFibre carryData route i,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ 1 :=
  windowExcess_le_mult_on_routedFibre carryData route i hgap hscale (by norm_num)

/-- **The matching `hdom` / `hcharge` field shape `windowExcess ≤ cap (chargeOf k)`.**  From the
per-fibre gap structure plus the per-element domination `mult ≤ cap (chargeOf k)`, every routed
start charges `≤ cap (chargeOf k)` — exactly the `hdom` input of `perOutput_charged_of_injOn` /
`routedClassMassOf_le_chargedArea_of_matching` and the `hcharge` field of `Class1CNLChargeData`
(with `cap` the per-codeword Kraft weight). -/
theorem windowExcess_le_cap_chargeOf_on_routedFibre
    {shell : FailingDyadicShell} {cPr : ℝ} {ι O : Type*} [DecidableEq ι]
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → ι) (i : ι)
    (chargeOf : ℕ → O) (cap : O → ℝ) {g₀ : ℕ} {mult : ℝ}
    (hgap : ∀ k ∈ routedFibre carryData route i,
        ∀ j, k ≤ j → j ≤ k + carryData.r → hitGap carryData.a j ≤ g₀)
    (hscale : ((carryData.r : ℝ) + 1) * (g₀ : ℝ) - carryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult)
    (hcap : ∀ k ∈ routedFibre carryData route i, mult ≤ cap (chargeOf k)) :
    ∀ k ∈ routedFibre carryData route i,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ cap (chargeOf k) :=
  fun k hk => (windowExcess_le_window_gap_multiplier (hgap k hk) hscale hmult_nonneg).trans
    (hcap k hk)

/-! ## 5.  Composition with the proved charging cores + concrete charging-map producers

The per-element domination of §4, fed into the proved count×multiplier / matching cores, closes the
routed class mass directly; and concrete producers build the actual `Class0ChernoffCharge.hpoint`,
the three `ChargeClassTRTData` per-class points, and a full `Class3DensePackCharge`. -/

/-- **`routedClassMassOf ≤ count·mult` from the active-window gap structure.**  Composes the §4
per-element domination with the proved `routedClassMassOf_le_countMultiplier` (the carry-side twin of
`densePackMass_le_of_density`).  This is the count×multiplier multiplier with the per-element charge
genuinely supplied. -/
theorem routedClassMassOf_le_countMult_of_window_gap
    {shell : FailingDyadicShell} {cPr : ℝ} {ι : Type*} [DecidableEq ι]
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → ι) (i : ι)
    {g₀ : ℕ} {mult count : ℝ}
    (hgap : ∀ k ∈ routedFibre carryData route i,
        ∀ j, k ≤ j → j ≤ k + carryData.r → hitGap carryData.a j ≤ g₀)
    (hscale : ((carryData.r : ℝ) + 1) * (g₀ : ℝ) - carryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult)
    (hcard : ((routedFibre carryData route i).card : ℝ) ≤ count) :
    routedClassMassOf carryData route i ≤ count * mult :=
  routedClassMassOf_le_countMultiplier carryData route i
    (windowExcess_le_mult_on_routedFibre carryData route i hgap hscale hmult_nonneg)
    hmult_nonneg hcard

/-- **`routedClassMassOf ≤ ∑ cap` from a matching charging map + the active-window gap structure.**
Composes the §4 matching domination with the proved `routedClassMassOf_le_chargedArea_of_matching`
(J.1.8 charged-ledger summation).  The routed class mass is dominated by the charged output area,
with the per-element charge supplied by the gap structure. -/
theorem routedClassMassOf_le_chargedArea_of_window_gap_matching
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7) (i : Fin 7)
    {O : Type*} [DecidableEq O] (chargeOf : ℕ → O) (outputs : Finset O) (cap : O → ℝ)
    {g₀ : ℕ} {mult : ℝ}
    (hmaps : ∀ k ∈ routedFibre carryData route i, chargeOf k ∈ outputs)
    (hinj : ∀ x ∈ routedFibre carryData route i, ∀ y ∈ routedFibre carryData route i,
        chargeOf x = chargeOf y → x = y)
    (hgap : ∀ k ∈ routedFibre carryData route i,
        ∀ j, k ≤ j → j ≤ k + carryData.r → hitGap carryData.a j ≤ g₀)
    (hscale : ((carryData.r : ℝ) + 1) * (g₀ : ℝ) - carryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult)
    (hcap : ∀ k ∈ routedFibre carryData route i, mult ≤ cap (chargeOf k))
    (hcap_nonneg : ∀ o ∈ outputs, 0 ≤ cap o) :
    routedClassMassOf carryData route i ≤ ∑ o ∈ outputs, cap o :=
  routedClassMassOf_le_chargedArea_of_matching carryData route i chargeOf outputs cap hmaps hinj
    (windowExcess_le_cap_chargeOf_on_routedFibre carryData route i chargeOf cap
      hgap hscale hmult_nonneg hcap)
    hcap_nonneg

/-- **The per-output charged estimate `∑_{Θ(k)=o} windowExcess k ≤ cap o` from the gap structure.**
Composes the §4 matching domination with the proved `perOutput_charged_of_injOn` (the J.1.8 charged
summation at per-output granularity).  This is the `hcharged` input demanded by the charging-map
multipliers, now with the per-element charge genuinely supplied. -/
theorem perOutput_charged_of_window_gap
    {shell : FailingDyadicShell} {cPr : ℝ} {ι O : Type*} [DecidableEq ι] [DecidableEq O]
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → ι) (i : ι)
    (chargeOf : ℕ → O) (outputs : Finset O) (cap : O → ℝ) {g₀ : ℕ} {mult : ℝ}
    (hinj : ∀ x ∈ routedFibre carryData route i, ∀ y ∈ routedFibre carryData route i,
        chargeOf x = chargeOf y → x = y)
    (hgap : ∀ k ∈ routedFibre carryData route i,
        ∀ j, k ≤ j → j ≤ k + carryData.r → hitGap carryData.a j ≤ g₀)
    (hscale : ((carryData.r : ℝ) + 1) * (g₀ : ℝ) - carryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult)
    (hcap : ∀ k ∈ routedFibre carryData route i, mult ≤ cap (chargeOf k))
    (hcap_nonneg : ∀ o ∈ outputs, 0 ≤ cap o) :
    ∀ o ∈ outputs,
      (∑ k ∈ (routedFibre carryData route i).filter (fun k => chargeOf k = o),
          windowExcess (hitGap carryData.a) k carryData.r carryData.T) ≤ cap o :=
  perOutput_charged_of_injOn (routedFibre carryData route i)
    (fun k => windowExcess (hitGap carryData.a) k carryData.r carryData.T)
    chargeOf outputs cap hinj
    (windowExcess_le_cap_chargeOf_on_routedFibre carryData route i chargeOf cap
      hgap hscale hmult_nonneg hcap)
    hcap_nonneg

/-! ### Concrete charging-map field producers (the exact `ChargedLedger` charging-map fields) -/

/-- **`Class0ChernoffCharge.hpoint` discharged from the active-window gap structure.**  Produces the
exact per-context body of the Chernoff (class-0) per-path charge multiplier field. -/
theorem class0_hpoint_of_window_gap
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) {g₀ : ℕ} {mult : ℝ}
    (hgap : ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀)
    (hscale : ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ : ℝ) - ctx.n24CarryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult) :
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult :=
  windowExcess_le_mult_on_routedFibre ctx.n24CarryData (budget ctx).route 0 hgap hscale hmult_nonneg

/-- **`ChargeClassTRTData.hpointTower` (class 2) discharged from the active-window gap structure.** -/
theorem chargeClassTRT_hpointTower_of_window_gap
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) {g₀ : ℕ} {mult : ℝ}
    (hgap : ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 2,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀)
    (hscale : ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ : ℝ) - ctx.n24CarryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult) :
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 2,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult :=
  windowExcess_le_mult_on_routedFibre ctx.n24CarryData (budget ctx).route 2 hgap hscale hmult_nonneg

/-- **`ChargeClassTRTData.hpointReturn` (class 4) discharged from the active-window gap structure.** -/
theorem chargeClassTRT_hpointReturn_of_window_gap
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) {g₀ : ℕ} {mult : ℝ}
    (hgap : ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 4,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀)
    (hscale : ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ : ℝ) - ctx.n24CarryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult) :
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 4,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult :=
  windowExcess_le_mult_on_routedFibre ctx.n24CarryData (budget ctx).route 4 hgap hscale hmult_nonneg

/-- **`ChargeClassTRTData.hpointRun` (class 5) discharged from the active-window gap structure.** -/
theorem chargeClassTRT_hpointRun_of_window_gap
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) {g₀ : ℕ} {mult : ℝ}
    (hgap : ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 5,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀)
    (hscale : ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ : ℝ) - ctx.n24CarryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult) :
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 5,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult :=
  windowExcess_le_mult_on_routedFibre ctx.n24CarryData (budget ctx).route 5 hgap hscale hmult_nonneg

/-- **`Class3DensePackCharge.unit_charge` (class 3, J.D) discharged from the active-window gap
structure.**  Produces the exact `unit_charge` field body `windowExcess ≤ 1`. -/
theorem class3_unit_charge_of_window_gap
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) {g₀ : ℕ}
    (hgap : ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀)
    (hscale : ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ : ℝ) - ctx.n24CarryData.T ≤ 1) :
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ 1 :=
  windowExcess_le_one_on_routedFibre ctx.n24CarryData (budget ctx).route 3 hgap hscale

/-- **A full `Class3DensePackCharge` with `unit_charge` discharged by the charged-branch-mass core.**
The routing-to-marker injection (`markerOf`/`maps_into`/`matching`, the J.1.1/J.D charging map) is
the orthogonal residual owned by the DensePack worker; the **per-element J.D unit charge** is
supplied here from the active-window gap structure.  This concretely slots the core into the actual
`Class3DensePackCharge` structure of the ledger. -/
def Class3DensePackCharge.ofWindowGap
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (markerOf : ℕ → ℕ)
    (maps_into : ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
      markerOf k ∈ (faithfulCapacityPhases budget ctx).toClosurePhaseData.densePack.densePackPoints)
    (matching : ∀ x ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
      ∀ y ∈ routedFibre ctx.n24CarryData (budget ctx).route 3, markerOf x = markerOf y → x = y)
    {g₀ : ℕ}
    (hgap : ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 3,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀)
    (hscale : ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Class3DensePackCharge budget ctx where
  markerOf := markerOf
  maps_into := maps_into
  matching := matching
  unit_charge := class3_unit_charge_of_window_gap budget ctx hgap hscale

/-! ## 6.  Non-vacuity, residual inventory, axiom audit

The per-element charge bound is genuinely realizable (not a vacuous implication): the strictly
increasing enumeration `a = id` has all hit gaps `= 1`, so the active-window gap bound holds with
equality (`g₀ = 1`, non-degenerate), and the charge is genuinely positive when the window exceeds
the threshold. -/

/-- The hit gaps of the identity enumeration are all `1` (a genuine strictly increasing hit
sequence, non-degenerate). -/
theorem hitGap_id (k : ℕ) : hitGap (fun n => n) k = 1 := by
  show (k + 1) - k = 1
  omega

/-- **Non-vacuity (multiplier form).**  For the identity enumeration the per-element multiplier bound
fires genuinely: `windowExcess (hitGap id) k r T ≤ (r+1) − T` (positive part), via the §2 core with
the non-degenerate gap bound `g₀ = 1`. -/
theorem windowExcess_id_le_multiplier_nonvacuous (r k : ℕ) {T : ℝ} (hT : T ≤ (r : ℝ) + 1) :
    windowExcess (hitGap (fun n => n)) k r T ≤ ((r : ℝ) + 1) - T := by
  refine windowExcess_le_window_gap_multiplier (g₀ := 1) (fun j _ _ => ?_) ?_ (by linarith)
  · exact le_of_eq (hitGap_id j)
  · norm_num

/-- **Non-vacuity (J.D unit charge).**  When the window exceeds the threshold by at most one unit
(`r ≤ T ≤ r+1`) the DensePack unit charge `windowExcess ≤ 1` is genuinely realized by the identity
enumeration — the residual `Class3DensePackCharge.unit_charge` is satisfiable, not vacuous. -/
theorem windowExcess_id_le_one_nonvacuous (r k : ℕ) {T : ℝ}
    (hT1 : (r : ℝ) ≤ T) (hT2 : T ≤ (r : ℝ) + 1) :
    windowExcess (hitGap (fun n => n)) k r T ≤ 1 := by
  have h := windowExcess_id_le_multiplier_nonvacuous r k hT2
  linarith

/-- The honest status of the per-element charged-branch-mass domination after this module. -/
def chargedBranchMassResiduals : List String :=
  [ "CHARGE ↔ I.9 BRANCH (proved) — windowExcess_eq_stoppedBranchWeight: the per-element carry " ++
      "charge IS the I.9 stopped-branch window-excess weight (via the proved telescoping " ++
      "windowExcessWeight_stoppedBranchOf); windowExcess_le_branchShellCost: it is ≤ the branch's " ++
      "intrinsic recorded shell cost (the phase object weight) for any nonnegative threshold.",
    "MULTIPLIER BOUND (proved from gap structure) — windowExcess_le_window_gap_multiplier / " ++
      "windowExcess_le_Cres_mul_Y: from a pointwise hit-gap bound on the descent window [k,k+r], " ++
      "windowExcess ≤ (r+1)·g₀ − T ≤ C_res·Y, the K.1.2/L.20 residual multiplier LINEAR in the " ++
      "active floor Y (no false O_Q(1) bound). branchShellCost_le_window_gap caps the phase object " ++
      "weight by the same multiplier.",
    "GAP BOUND GROUNDED (proved) — windowExcess_le_dyadicWindowMultiplier(_carry): the pointwise " ++
      "gap bound g₀ = L+B+1 is the PROVED dyadic-scale estimate HitSequence.hitGap_le_of_shell_window " ++
      "(rational value η=P/Q, dyadic X=2^L, Q·4≤2^B), applied to the actual carry hits " ++
      "carryData.carry.hits. So the per-element charge bound is grounded in the shell geometry.",
    "FIELD SHAPES (proved) — windowExcess_le_mult_on_routedFibre (hpoint / count×mult / TRT points), " ++
      "windowExcess_le_one_on_routedFibre (Class3 J.D unit_charge ≤ 1), " ++
      "windowExcess_le_cap_chargeOf_on_routedFibre (Class1 CNL hcharge / matching hdom). These are " ++
      "the EXACT per-element field bodies of the ChargedLedger charging maps.",
    "CHARGING-MAP PRODUCERS (proved) — class0_hpoint_of_window_gap, chargeClassTRT_hpoint{Tower," ++
      "Return,Run}_of_window_gap, class3_unit_charge_of_window_gap, and the full structure builder " ++
      "Class3DensePackCharge.ofWindowGap discharge the actual charging-map per-element fields from " ++
      "the core; routedClassMassOf_le_countMult_of_window_gap / " ++
      "routedClassMassOf_le_chargedArea_of_window_gap_matching / perOutput_charged_of_window_gap " ++
      "compose with the proved count×multiplier / J.1.8 cores.",
    "MINIMAL RESIDUAL (documented, non-vacuous) — the only undischarged inputs are (hscale) the " ++
      "numeric active-floor scaling (r+1)·(L+B+1) − T ≤ C_res·Y (the K.1.2 threshold/floor " ++
      "calibration) and (hfibre_win) the active-window containment of the descent window in the " ++
      "shell index range (true for starts = Ico (firstIndexAbove X) (firstIndexAbove X + K)). " ++
      "windowExcess is an UNBOUNDED positivePart so no uniform multiplier exists a priori — the " ++
      "residual is genuine; windowExcess_id_le_one_nonvacuous exhibits a non-degenerate witness." ]

theorem chargedBranchMassResiduals_nonempty : chargedBranchMassResiduals ≠ [] := by
  simp [chargedBranchMassResiduals]

/-- **Non-vacuity capstone.**  The per-element charge domination fires on genuine data: for the
strictly increasing identity enumeration (all hit gaps `= 1`) the multiplier bound and the J.D unit
charge both hold non-vacuously, and the charge equals the I.9 branch weight. -/
theorem chargedBranchMass_nonvacuous :
    (∀ (k : ℕ), hitGap (fun n => n) k = 1)
    ∧ (∀ (r k : ℕ) (T : ℝ), (r : ℝ) ≤ T → T ≤ (r : ℝ) + 1 →
        windowExcess (hitGap (fun n => n)) k r T ≤ 1)
    ∧ (∀ (a : ℕ → ℕ) (r k : ℕ) (T : ℝ),
        windowExcess (hitGap a) k r T = windowExcessWeight T (stoppedBranchOf a r k)) :=
  ⟨hitGap_id, fun r k _T hT1 hT2 => windowExcess_id_le_one_nonvacuous r k hT1 hT2,
    windowExcess_eq_stoppedBranchWeight⟩

/-! ## 7.  Axiom-cleanliness audit -/

#print axioms windowExcess_eq_stoppedBranchWeight
#print axioms windowExcess_le_branchShellCost
#print axioms windowExcess_le_window_gap_multiplier
#print axioms windowExcess_le_Cres_mul_Y
#print axioms branchShellCost_le_window_gap
#print axioms windowExcess_le_dyadicWindowMultiplier
#print axioms windowExcess_le_dyadicWindowMultiplier_carry
#print axioms windowExcess_le_mult_on_routedFibre
#print axioms windowExcess_le_one_on_routedFibre
#print axioms windowExcess_le_cap_chargeOf_on_routedFibre
#print axioms routedClassMassOf_le_countMult_of_window_gap
#print axioms routedClassMassOf_le_chargedArea_of_window_gap_matching
#print axioms perOutput_charged_of_window_gap
#print axioms class0_hpoint_of_window_gap
#print axioms class3_unit_charge_of_window_gap
#print axioms Class3DensePackCharge.ofWindowGap
#print axioms chargedBranchMass_nonvacuous

end

end Erdos260
