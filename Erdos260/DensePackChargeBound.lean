import Mathlib
import Erdos260.AppendixI_PhaseMass
import Erdos260.DensePack

/-!
# DensePack charge bound (Lemma I.4.1 / K.1.5 / Corollary K.1.3)

This file connects the **already-proved** DensePack smallness estimate to the
charge-bridge phase-mass term `termDensePack` (`Erdos260.AppendixI_PhaseMass`),
the DensePack slot of the six-phase priority routing
(`Erdos260.ChargeBridgeReduction`).  It mirrors the count×multiplier mechanism of
the old-residual term (`oldRes_le_of_density`): a per-marker multiplier linear in
the active floor `Y` times a marker count made small by the positive-density
failure.

## What is already proved (reused here, NOT duplicated)

The DensePack count×multiplier estimate is manuscript Lemma I.4.1 (dense packing),
proved through Corollary K.1.3.  Its Lean core already exists:

* `corollaryK1_3_densePackUnderFailure` (`Erdos260.DensePack`) — under the
  positive-density failure `markersCard ≤ c_*·X`, the dense-pack point count is
  `≤ c_*·X·(2·spread+1)`: the marker count (small under failure, K.1.3) times the
  per-marker `O(L)`-neighbourhood multiplier `2·spread+1` (Lemma K.1.2 cover);
* `Erdos260.densePackBound` / `GroundedDensePackLocalData.densePack_bound`
  (`Erdos260.GlobalDensePackAssembly`) — the full chain to the per-phase budget
  `c_*·ξ·X/6` (eq. I.4), with the shell-level `L`-cancellation
  (`proofV4DensePackSmallness_of_smallLarge`) realizing the manuscript's
  `C_Q·(c_*/ρ_D)·X` constant.

## What this file adds

* `densePackMass_le_of_density` / `densePackMass_le_lowDensityWindow` — the exact
  DensePack twins of `oldRes_le_of_density` / `oldRes_le_lowDensityWindow`
  (`Erdos260.ChargeBridgeReduction`): the **same count×multiplier mechanism** in
  branch-sum form — the DensePack mass over the maximal disjoint marker family
  `D₀` is the marker count (`≤ c_*·X/(ρ_D L)` under failure, K.1.3) times the
  per-marker residual multiplier (`≤ C_Q·Y`, Def. K.1.2 / Lemma K.1.4), with the
  `O(rL)=o(X)` boundary band carried as an explicit collar term (the `+o(sX|I_j|)`
  of eq. I.3).
* `termDensePack_le_countMultiplier` — the **connecting lemma** (eq. I.3): the
  charge-bridge term `termDensePack` (the dense-pack point cardinality) obeys the
  count×multiplier bound, by reusing `corollaryK1_3_densePackUnderFailure`.
* `termDensePack_le_phaseBudget` — DensePack smallness at the fixed threshold
  layer (eq. I.4): `termDensePack ≤ c_*·ξ·X/6`, after the manuscript choice
  `c_* ≪_Q ρ_D κ ξ` (`data.densePack.hsmall`).
* `termDensePack_toClosurePhaseData_le_countMultiplier` /
  `termDensePack_toClosurePhaseData_le_phaseBudget` — the same bounds on the
  six-phase factory form `termDensePack phases.toClosurePhaseData`, ready to feed
  the DensePack slot of the charge bridge.

No `sorry`/`axiom`; only the count×multiplier arithmetic and the reuse of the
existing K.1.3 cover are used, exactly as in the old-residual section of
`Erdos260.ChargeBridgeReduction`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## The shared count×multiplier mechanism (DensePack twin of `oldRes_le_of_density`) -/

/-- **DensePack count×multiplier core (Lemma I.4.1, K.1.2 + K.1.3) — faithful primitive.**

The exact DensePack twin of `oldRes_le_of_density`
(`Erdos260.ChargeBridgeReduction`).  Model the branch-level DensePack mass as the
sum `∑_{m ∈ D₀} fiberMass m` over the greedy maximal disjoint dense-marker family
`D₀` (Lemma K.1.2).  On each selected marker:

* the per-marker contribution is `fiberMass m ≤ multiplier` — the residual mass on
  the marker's `O(L)`-neighbourhood window, kept **linear in the active floor `Y`**
  (`multiplier = C_Q·Y`, Definition K.1.2 / Lemma K.1.4; no false `O_Q(1)` bound);

and the number of selected markers obeys `|D₀| ≤ markerCount` (Lemma I.4.1 eq.,
`markerCount ≤ C·c_*·X/(ρ_D L)` under the positive-density failure
`A_S(2X)−A_S(X) ≤ c_*X`).  Hence the DensePack mass is `≤ markerCount · multiplier`.

**The smallness is carried entirely by the marker count `markerCount` (≈ `c_*X/(ρ_D L)`),
never by a per-marker constant bound** — the same mechanism used for the
old-residual term, evading any false `O_Q(1)` multiplier bound. -/
theorem densePackMass_le_of_density {D₀ : Finset ℕ} {fiberMass : ℕ → ℝ}
    {multiplier markerCount : ℝ}
    (hpoint : ∀ m ∈ D₀, fiberMass m ≤ multiplier)
    (hmult_nonneg : 0 ≤ multiplier)
    (hcard : (D₀.card : ℝ) ≤ markerCount) :
    (∑ m ∈ D₀, fiberMass m) ≤ markerCount * multiplier := by
  calc
    (∑ m ∈ D₀, fiberMass m) ≤ ∑ _m ∈ D₀, multiplier := Finset.sum_le_sum hpoint
    _ = (D₀.card : ℝ) * multiplier := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ markerCount * multiplier := mul_le_mul_of_nonneg_right hcard hmult_nonneg

/-- **Lemma I.4.1 with the `o(sX|I_j|)` boundary collar (DensePack twin of
`oldRes_le_lowDensityWindow`).**

Specializes `densePackMass_le_of_density` to the manuscript marker count
`|D₀| ≤ c_*·X + collar`, where `collar = O(rL) = O(L²) = o(X)` is the harmless
boundary band of the enlarged window `[X−CrL, 2X+CrL]` (which contributes
`o(sX|I_j|)` even without any density hypothesis, since the bands outside `[X,2X]`
have total length `o(X)`).  This yields the eq. I.3 split into the genuinely-small
main term `c_*·X·multiplier` and the `o(...)` collar term `collar·multiplier`. -/
theorem densePackMass_le_lowDensityWindow {D₀ : Finset ℕ} {fiberMass : ℕ → ℝ}
    {multiplier cStar X collar : ℝ}
    (hpoint : ∀ m ∈ D₀, fiberMass m ≤ multiplier)
    (hmult_nonneg : 0 ≤ multiplier)
    (hcard : (D₀.card : ℝ) ≤ cStar * X + collar) :
    (∑ m ∈ D₀, fiberMass m) ≤ cStar * X * multiplier + collar * multiplier := by
  have h := densePackMass_le_of_density hpoint hmult_nonneg hcard
  nlinarith [h]

/-! ## Connecting lemmas to the charge-bridge term `termDensePack` -/

/-- **Connecting lemma — Lemma I.4.1 eq. I.3 (count×multiplier) for `termDensePack`.**

The charge-bridge DensePack phase mass `termDensePack`
(`= (densePackPoints.card : ℝ)`, the DensePack slot of the priority routing in
`Erdos260.ChargeBridgeReduction`) is bounded by the marker count `≤ c_*·X` (the
density-failure hypothesis K.1.3, carried by `data.densePack.hcount`) times the
per-marker `O(L)`-neighbourhood multiplier `2·spread+1` (the Lemma K.1.2 cover,
carried by `data.densePack.hcover`).  Reuses `corollaryK1_3_densePackUnderFailure`
— the SAME count×multiplier mechanism as `oldRes_le_of_density`. -/
theorem termDensePack_le_countMultiplier {cStar ξ X : ℝ}
    (data : ClosurePhaseData cStar ξ X) :
    termDensePack data
      ≤ data.densePack.cStarSmall * X * ((2 * data.densePack.spread + 1 : ℕ) : ℝ) := by
  unfold termDensePack
  exact corollaryK1_3_densePackUnderFailure data.densePack.hcover data.densePack.hcount

/-- **DensePack smallness at the fixed threshold layer — Lemma I.4.1 eq. I.4.**

After the manuscript's `c_* ≪_Q ρ_D κ ξ` choice (recorded in
`data.densePack.hsmall`, which absorbs the `L`-cancelled count×multiplier below
the budget), the charge-bridge term obeys `termDensePack ≤ c_*·ξ·X/6`.  This is the
form consumed downstream of the charge bridge (the per-phase pressure floor). -/
theorem termDensePack_le_phaseBudget {cStar ξ X : ℝ}
    (data : ClosurePhaseData cStar ξ X) :
    termDensePack data ≤ cStar * ξ * X / 6 :=
  (termDensePack_le_countMultiplier data).trans data.densePack.hsmall

/-- **Six-phase factory count×multiplier form (eq. I.3).**

The eq. I.3 count×multiplier bound on `termDensePack phases.toClosurePhaseData`,
the DensePack phase-mass term as it appears in the six-phase routing
(`RoutedHighExcessChargeData` / `…TRT` / `…OldRes` in
`Erdos260.ChargeBridgeReduction`). -/
theorem termDensePack_toClosurePhaseData_le_countMultiplier {cStar ξ X : ℝ}
    (phases : SixPhaseFactoryData cStar ξ X) :
    termDensePack phases.toClosurePhaseData
      ≤ phases.densePack.cStarSmall * X *
          ((2 * phases.densePack.spread + 1 : ℕ) : ℝ) :=
  termDensePack_le_countMultiplier phases.toClosurePhaseData

/-- **DensePack smallness for the six-phase factory form — Lemma I.4.1 eq. I.4.**

The eq. I.4 bound `termDensePack phases.toClosurePhaseData ≤ c_*·ξ·X/6`, ready to
discharge the DensePack contribution to the per-failure pressure lower bound. -/
theorem termDensePack_toClosurePhaseData_le_phaseBudget {cStar ξ X : ℝ}
    (phases : SixPhaseFactoryData cStar ξ X) :
    termDensePack phases.toClosurePhaseData ≤ cStar * ξ * X / 6 :=
  termDensePack_le_phaseBudget phases.toClosurePhaseData

end

end Erdos260
