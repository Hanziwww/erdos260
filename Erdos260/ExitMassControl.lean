import Erdos260.Erdos260FrontierCapstone

/-!
# Exit-mass control at the five fixed data (`ExitMassControl`)

This module (NEW; it edits no existing file) settles the wave-18 "cheapest numeric
gap" — the pressure-relocation lever against the corrected per-class phase capacity
`(31/1536)·X` — and transcribes the manuscript's M.5/L.3 exit-mass control as the
single named structure `ExitMassControlCore`, with the full kill chain proved around
it.

## Part 1 — the 30% sharpening hunt: settled NEGATIVELY, with exact constants

The lever: the corrected ledger's count-shaped class row demands
`#fibre·Y ≤ (31/1536)·X` with `Y = L/64`.  Firing it at a pinned context (where the
fibre IS the full heavy set, `band2_fibre4_eq_highExcess` etc.) needs the heavy count
above `31·64·X/(1536·L) = (31/24)·X/L ≈ 1.2917·X/L`.  THE TRUE CHAIN:

* The heavy count is capped by the SUPPORT count — `#HE ≤ W` (`emc_heavyCard_le_W`,
  via `scc_starts_card`), and the failure cap is `W < (17/2²⁴)·X`
  (`scc_supportShell_lt`).  So `#HE·Y < (17/2²⁴)·X·(L/64) = 17·L·X/2³⁰`.
* `17·L/2³⁰ < 31/1536  ⟺  26112·L < 31·2³⁰  ⟺  L ≤ 1274739` — **THE DEAD-ZONE
  THEOREM** (`emc_countTimesY_lt_cap`, fibre form `emc_fibre_countTimesY_lt_cap`):
  for every `L ≤ 1274739` the count-shaped row `#HE·Y < (31/1536)·X` is a THEOREM —
  the lever target is identically false there, for EVERY routed fibre.  The needed
  heavy count `(31/24)·X/L` exceeds the TOTAL support cap `(17/2²⁴)·X` whenever
  `L < 31·2²⁴/408 = 1274739.45...`; no sharpening of the heavy-count floor (30% or
  any other amount) can fire it — there are not enough windows in the whole shell.
* `emc_fire_forces_deep`: a firing context must have `L ≥ 1274740` — EXACTLY the
  `DeepShellTailClosure` class-1 deep threshold `⌊31·2²⁴/408⌋ + 1` (sharpness:
  `emc_threshold_sharp`, `26112·1274739 < 31·2³⁰ < 26112·1274740`).
* **Where the ~1.3 factor lives**: the pins force `L ≥ 986894/986892` (the proved
  scale floors) but the lever fires only at `L ≥ 1274740`; the ratio
  `1274739.45/986894 = 1.2917 = (31/24)/(17·986894/2²⁴)` is the wave-18 "factor
  ~1.3".  It is STRUCTURAL: the same constant `31·2²⁴/408` is the class-1 deep-shell
  threshold.  On the pins' proved range `[986894, 1274739]` the lever is dead
  (`emc_band2_deadZone`, `emc_band3Wide_deadZone`, `emc_band4_deadZone`).

## Part 2 — the per-window deviation cap (`D0`) verdict: the prize is UNREACHABLE
below the deep threshold

The brief's hoped mechanism: a uniform per-heavy-window excess cap `D0` sharpens the
heavy-count floor to `(1/2)·X·(r+1)/D0`, and `D0 < 12·L·(r+1)/31 ≈ 0.387·L·(r+1)`
fires the lever.  PROVED OBSTRUCTION:

* `emc_uniformCap_floor`: ANY uniform cap `D0` on the heavy windows obeys
  `2²³·(r+1) < 17·D0` — the Lemma 21.1 pressure floor against the support cap forces
  the AVERAGE heavy-window excess above `(2²³/17)·(r+1) ≈ 493447·(r+1)`, i.e. above
  `≈ 0.5·L·(r+1)` at the pin frontier `L = 986894`.  No `D0 ≤ 0.38·L·(r+1)` exists —
  in-tree or otherwise: the bound is forced by the context itself.
* `emc_lever_fires_of_D0` (the lever, formalized): a uniform cap with
  `31·D0 < 12·L·(r+1)` DOES fire the count row (`(31/1536)·X < #HE·Y`) — the
  conditional mechanism is real.
* `emc_D0_fire_forces_deep`: combining the two, any such `D0` forces
  `L ≥ 1274740`.  The two constraints `D0 > (2²³/17)·(r+1)` and
  `D0 ≤ (12/31)·L·(r+1)` are compatible ONLY above the deep threshold — the same
  `31·2²³/204 = 31·2²⁴/408` again.  Below it the prize is provably nonexistent.

## Part 3 — the M.5/L.3 exit-mass control core and the kills

The manuscript routes the recurrent fixed data through L.3.1 (transient tower
excursions are charged to Run/Return/DensePack/Progress/Endpoint/CNL-tail), M.5.1
(low transient exits are CNL leaves: "splitting by the determined terminal label
does not multiply the number of lift-state codes") and I.3 ("clean deterministic
motion inside the simple cycle is not charged as tower area").  Its word-level
shadow at the five fixed data is the corrected per-class MASS cap at the three
recurrent classes — class 3 (densepack lane, the `(21,3)` pin), class 4 (return
lane, the `(3,1)` pin), class 5 (run lane, the band-4 trio):

* `ExitMassControlCore` (THE ONE NAMED STRUCTURE): `mass₃, mass₄, mass₅ ≤
  (31/1536)·X` demanded only at deep scales `X > 2^986891`.
* THE KILLS (PROVED): the relocated pressure floor `(1/2)·X·(r+1)` (resp.
  `(511/1024)·X·(r+1)`) sits entirely in the pinned class
  (`band2_pressure_in_class4`, `band3_pressure_in_class3`,
  `band4_pressure_in_class5`), and `(1/2)·X > (31/1536)·X` at every scale — so each
  per-class cap kills its pin OUTRIGHT (`emc_returnCap_kills_band2`,
  `emc_densePackCap_kills_band3`, `emc_runCap_kills_band4`); no scale hypothesis,
  no `r`-floor, no `Q`-bound is consumed.
* `deepOrbitPinVoiding_of_exitMassControl`: the core supplies the ENTIRE v18
  frontier field `deepOrbitPin : DeepOrbitPinVoiding`, hence `DeepFixedFamilyVoid`
  (`deepFixedFamilyVoid_of_exitMassControl`) and all three v17 voiding fields
  (`returnBand2Void_of_exitMassControl` etc.).
* NO FREE LUNCH, made exact (`exitMassControl_iff_split`): the core is EQUIVALENT
  to (the deep orbit-pin voiding) ∧ (the caps on pin-free deep contexts) — the
  M.5/L.3 control CONTAINS the open axis; its honest residual beyond the axis is
  the pin-free conjunct `ExitMassControlOffPin`.

## Honest summary

NO unconditional kill: the count-shaped lever is proved DEAD on the pins' entire
proved range `L ∈ [986894, 1274739]` and live only at `L ≥ 1274740`; the per-window
cap that would drive it is proved NONEXISTENT below the same threshold.  The
irreducible core is exactly `ExitMassControlCore` (per-class corrected mass caps at
the recurrent classes, deep scales only); supplying it kills all five pins through
the relocation floors and discharges the v18 `deepOrbitPin` frontier field.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## Part 0.  The corrected per-class capacity and the heavy set -/

/-- The corrected per-class phase capacity `(31/1536)·X` (the per-class share
`c⋆·ξ·X/6` of the corrected global phase budget). -/
def emcCap (ctx : ActualFailureContext) : ℝ :=
  31 / 1536 * (ctx.shell.X : ℝ)

/-- The capacity agrees with the in-tree corrected constant `c⋆·ξ/6`. -/
theorem emcCap_eq_corrected (ctx : ActualFailureContext) :
    emcCap ctx
      = erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  unfold emcCap
  rw [show erdos260Constants.cStar * erdos260Constants.ξ / 6 = (31 : ℝ) / 1536 from by
    rw [tfaCstarXi_eq]; norm_num]

/-- The heavy (high-excess) start set of the context — the carrier of the Lemma 21.1
pressure floor. -/
def emcHE (ctx : ActualFailureContext) : Finset ℕ :=
  highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
    ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y

/-- The heavy count is capped by the support count: `#HE ≤ W`. -/
theorem emc_heavyCard_le_W (ctx : ActualFailureContext) :
    (emcHE ctx).card ≤ (supportShell ctx.shell.d ctx.shell.X).card := by
  unfold emcHE
  rw [← scc_starts_card ctx]
  exact Finset.card_le_card (highExcessStarts_subset _ _ _ _ _)

/-- Every routed fibre sits inside the heavy set. -/
theorem emc_fibre_subset_heavy (ctx : ActualFailureContext) (i : Fin 7) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ⊆ emcHE ctx := by
  intro k hk
  have h := ((mem_routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i k).mp hk).1
  unfold emcHE
  exact h

/-! ## Part 1.  The dead-zone theorems: the count-shaped lever is closed below the
deep threshold `L = 1274740 = ⌊31·2²⁴/408⌋ + 1` -/

/-- **THE DEAD-ZONE THEOREM**: for every `L ≤ 1274739` the count-shaped corrected
class row HOLDS as a theorem on the full heavy set — `#HE·Y < (31/1536)·X`.  The
chain: `#HE ≤ W < (17/2²⁴)·X` and `Y = L/64`, so `#HE·Y < 17·L·X/2³⁰`, and
`17·1274739/2³⁰ < 31/1536`.  No heavy-count sharpening can fire the lever here: the
needed count `(31/24)·X/L` exceeds the TOTAL support cap. -/
theorem emc_countTimesY_lt_cap (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 1274739) :
    ((emcHE ctx).card : ℝ) * ctx.n24CarryData.Y < emcCap ctx := by
  have hW := scc_supportShell_lt ctx
  have hX := ctx.shell.X_pos_real
  have hcard : ((emcHE ctx).card : ℝ)
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card : ℝ) := by
    exact_mod_cast emc_heavyCard_le_W ctx
  have hLr : ((shellLadderDepth ctx : ℕ) : ℝ) ≤ 1274739 := by exact_mod_cast hL
  unfold emcCap
  rw [n24CarryData_Y_eq_div]
  have h1 : ((emcHE ctx).card : ℝ) * (((shellLadderDepth ctx : ℕ) : ℝ) / 64)
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card : ℝ)
          * (((shellLadderDepth ctx : ℕ) : ℝ) / 64) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  have h2 : ((supportShell ctx.shell.d ctx.shell.X).card : ℝ)
          * (((shellLadderDepth ctx : ℕ) : ℝ) / 64)
      ≤ 17 / 16777216 * (ctx.shell.X : ℝ)
          * (((shellLadderDepth ctx : ℕ) : ℝ) / 64) :=
    mul_le_mul_of_nonneg_right hW.le (by positivity)
  have h3 : 17 / 16777216 * (ctx.shell.X : ℝ)
          * (((shellLadderDepth ctx : ℕ) : ℝ) / 64)
      ≤ 17 / 16777216 * (ctx.shell.X : ℝ) * ((1274739 : ℝ) / 64) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have hc : (17 : ℝ) / 16777216 * (1274739 / 64) < 31 / 1536 := by norm_num
  have h4 := mul_lt_mul_of_pos_right hc hX
  nlinarith [h1, h2, h3, h4]

/-- The dead zone covers EVERY routed fibre: `#fibreᵢ·Y < (31/1536)·X` at
`L ≤ 1274739` — in particular the pinned classes 3/4/5, where the fibre IS the full
heavy set. -/
theorem emc_fibre_countTimesY_lt_cap (ctx : ActualFailureContext) (i : Fin 7)
    (hL : shellLadderDepth ctx ≤ 1274739) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i).card : ℝ)
        * ctx.n24CarryData.Y < emcCap ctx := by
  have h1 := emc_countTimesY_lt_cap ctx hL
  have hY0 : (0 : ℝ) ≤ ctx.n24CarryData.Y := by
    rw [n24CarryData_Y_eq_div]; positivity
  have hc : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i).card : ℝ)
      ≤ ((emcHE ctx).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (emc_fibre_subset_heavy ctx i)
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc hY0) h1

/-- **A firing context is deep**: `(31/1536)·X ≤ #HE·Y` forces `L ≥ 1274740` — the
EXACT `DeepShellTailClosure` class-1 deep threshold `⌊31·2²⁴/408⌋ + 1`. -/
theorem emc_fire_forces_deep (ctx : ActualFailureContext)
    (hfire : emcCap ctx ≤ ((emcHE ctx).card : ℝ) * ctx.n24CarryData.Y) :
    1274740 ≤ shellLadderDepth ctx := by
  by_contra hcon
  have hL : shellLadderDepth ctx ≤ 1274739 := by omega
  exact absurd hfire (not_le.mpr (emc_countTimesY_lt_cap ctx hL))

/-- The deep threshold is sharp: `26112·1274739 < 31·2³⁰ < 26112·1274740`
(`26112 = 1536·17`, `31·2³⁰/26112 = 31·2²⁴/408 = 1274739.45...`). -/
theorem emc_threshold_sharp :
    26112 * 1274739 < 31 * 2 ^ 30 ∧ 31 * 2 ^ 30 < 26112 * 1274740 := by
  norm_num

/-- **The band-2 pin dead zone**: at every band-2-pinned context the proved depth
floor is `L ≥ 986894`, and on the WHOLE range `L ≤ 1274739` the class-4 count row
holds — the lever has no purchase on the pin below the deep threshold (the wave-18
"factor ~1.3" is exactly `1274739.45/986894 = 1.2917`). -/
theorem emc_band2_deadZone (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2) (hL : shellLadderDepth ctx ≤ 1274739) :
    986894 ≤ shellLadderDepth ctx ∧
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).card : ℝ)
          * ctx.n24CarryData.Y < emcCap ctx :=
  ⟨orbitBandPinned2_L_floor ctx hpin, emc_fibre_countTimesY_lt_cap ctx 4 hL⟩

/-- **The wide band-3 pin dead zone**: depth floor `L ≥ 986894`; the class-3 count
row holds on `L ≤ 1274739`. -/
theorem emc_band3Wide_deadZone (ctx : ActualFailureContext)
    (hpin : Band3PinnedWide ctx) (hL : shellLadderDepth ctx ≤ 1274739) :
    986894 ≤ shellLadderDepth ctx ∧
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 3).card : ℝ)
          * ctx.n24CarryData.Y < emcCap ctx :=
  ⟨band3PinnedWide_L_floor ctx hpin, emc_fibre_countTimesY_lt_cap ctx 3 hL⟩

/-- **The band-4 pin dead zone**: depth floor `L ≥ 986892`; the class-5 count row
holds on `L ≤ 1274739`. -/
theorem emc_band4_deadZone (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4) (hL : shellLadderDepth ctx ≤ 1274739) :
    986892 ≤ shellLadderDepth ctx ∧
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
          * ctx.n24CarryData.Y < emcCap ctx :=
  ⟨orbitBandPinned4_L_floor ctx hpin, emc_fibre_countTimesY_lt_cap ctx 5 hL⟩

/-! ## Part 2.  The per-window deviation cap (`D0`) verdict -/

/-- **THE UNIFORM-CAP FLOOR** (the per-window deviation cap verdict, negative half):
ANY uniform cap `D0` on the heavy-window excesses obeys `2²³·(r+1) < 17·D0` — the
pressure floor `(1/2)·X·(r+1) ≤ Σ windowExcess ≤ #HE·D0 ≤ W·D0 < (17/2²⁴)·X·D0`
forces the average heavy-window excess above `(2²³/17)·(r+1) ≈ 493447·(r+1)`, i.e.
`≈ 0.5·L·(r+1)` at the pin frontier `L = 986894`.  The brief's hoped
`D0 ≤ 0.38·L·(r+1)` is PROVABLY NONEXISTENT there. -/
theorem emc_uniformCap_floor (ctx : ActualFailureContext) {D0 : ℝ}
    (hcap : ∀ k ∈ emcHE ctx,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ D0) :
    8388608 * ((ctx.n24CarryData.r : ℝ) + 1) < 17 * D0 := by
  unfold emcHE at hcap
  have hX := ctx.shell.X_pos_real
  have hr1 : (0 : ℝ) < (ctx.n24CarryData.r : ℝ) + 1 := by positivity
  have hpos : (0 : ℝ) < 1 / 2 * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1) :=
    mul_pos (mul_pos (by norm_num) hX) hr1
  have h1 : (1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ ∑ k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y,
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ctx.n24CarryData.T :=
    ctx.n24CarryData.highExcessMass_lower
  have h2 : (∑ k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y,
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ctx.n24CarryData.T)
      ≤ ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ)
          * D0 := by
    have h := Finset.sum_le_card_nsmul
      (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
      (fun k => windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ctx.n24CarryData.T) D0 hcap
    simpa [nsmul_eq_mul] using h
  have hcd : (0 : ℝ)
      < ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ)
          * D0 :=
    lt_of_lt_of_le hpos (le_trans h1 h2)
  have hD0 : (0 : ℝ) < D0 := by
    by_contra hcon
    have h : D0 ≤ 0 := not_lt.mp hcon
    have hge : (0 : ℝ)
        ≤ ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
              ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ) :=
      Nat.cast_nonneg _
    nlinarith [hcd, hge, h]
  have hcardn : (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
      ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card
      ≤ (supportShell ctx.shell.d ctx.shell.X).card := by
    rw [← scc_starts_card ctx]
    exact Finset.card_le_card (highExcessStarts_subset _ _ _ _ _)
  have hcW : ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
      ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ)
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card : ℝ) := by
    exact_mod_cast hcardn
  have hW := scc_supportShell_lt ctx
  have h3 := mul_le_mul_of_nonneg_right hcW hD0.le
  have h4 := mul_lt_mul_of_pos_right hW hD0
  have h5 : 1 / 2 * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      < 17 / 16777216 * (ctx.shell.X : ℝ) * D0 :=
    lt_of_le_of_lt (le_trans h1 (le_trans h2 h3)) h4
  by_contra hcon
  have hle : 17 * D0 ≤ 8388608 * ((ctx.n24CarryData.r : ℝ) + 1) := not_lt.mp hcon
  have h6 := mul_le_mul_of_nonneg_left hle hX.le
  nlinarith [h5, h6]

/-- **THE LEVER, FORMALIZED** (the conditional mechanism is real): a uniform
heavy-window cap `D0` with the firing margin `31·D0 < 12·L·(r+1)` DOES push the heavy
count above the corrected row — `(31/1536)·X < #HE·Y`.  (`#HE ≥ (1/2)·X·(r+1)/D0` from
the pressure floor; `Y = L/64`.) -/
theorem emc_lever_fires_of_D0 (ctx : ActualFailureContext) {D0 : ℝ}
    (hcap : ∀ k ∈ emcHE ctx,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ D0)
    (hfire : 31 * D0
        < 12 * ((shellLadderDepth ctx : ℕ) : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)) :
    emcCap ctx < ((emcHE ctx).card : ℝ) * ctx.n24CarryData.Y := by
  have hYeq := n24CarryData_Y_eq_div ctx
  unfold emcHE at hcap ⊢
  unfold emcCap
  have hX := ctx.shell.X_pos_real
  have hr1 : (0 : ℝ) < (ctx.n24CarryData.r : ℝ) + 1 := by positivity
  have hpos : (0 : ℝ) < 1 / 2 * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1) :=
    mul_pos (mul_pos (by norm_num) hX) hr1
  have h1 : (1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ ∑ k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y,
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ctx.n24CarryData.T :=
    ctx.n24CarryData.highExcessMass_lower
  have h2 : (∑ k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y,
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ctx.n24CarryData.T)
      ≤ ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ)
          * D0 := by
    have h := Finset.sum_le_card_nsmul
      (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
      (fun k => windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ctx.n24CarryData.T) D0 hcap
    simpa [nsmul_eq_mul] using h
  have h12 := le_trans h1 h2
  have hcd : (0 : ℝ)
      < ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ)
          * D0 :=
    lt_of_lt_of_le hpos h12
  have hcardpos : (0 : ℝ)
      < ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ) := by
    rcases Nat.eq_zero_or_pos (highExcessStarts ctx.n24CarryData.starts
        (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T
        ctx.n24CarryData.Y).card with h0 | h0
    · rw [h0] at hcd
      simp at hcd
    · exact_mod_cast h0
  have h7 := mul_lt_mul_of_pos_left hfire hcardpos
  have h8 : 31 / 2 * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      < 12 * ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ)
          * ((shellLadderDepth ctx : ℕ) : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1) := by
    nlinarith [h12, h7]
  have h9 : 31 / 2 * (ctx.shell.X : ℝ)
      < 12 * ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ)
          * ((shellLadderDepth ctx : ℕ) : ℝ) :=
    lt_of_mul_lt_mul_right h8 hr1.le
  have hfin : 31 / 1536 * (ctx.shell.X : ℝ)
      < ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ)
          * (((shellLadderDepth ctx : ℕ) : ℝ) / 64) := by
    linarith [h9]
  refine lt_of_lt_of_eq hfin ?_
  rw [hYeq]

/-- **THE `D0` DEAD ZONE**: any uniform heavy-window cap carrying the firing margin
`31·D0 ≤ 12·L·(r+1)` forces `L ≥ 1274740` — the per-window route can NEVER fire on
the pins' proved range `[986894, 1274739]`; the forced average `(2²³/17)·(r+1)`
crosses the firing threshold `(12/31)·L·(r+1)` exactly at `L = 31·2²³/204 =
31·2²⁴/408 = 1274739.45...`. -/
theorem emc_D0_fire_forces_deep (ctx : ActualFailureContext) {D0 : ℝ}
    (hcap : ∀ k ∈ emcHE ctx,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ D0)
    (hfire : 31 * D0
        ≤ 12 * ((shellLadderDepth ctx : ℕ) : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)) :
    1274740 ≤ shellLadderDepth ctx := by
  have h := emc_uniformCap_floor ctx hcap
  have hr1 : (0 : ℝ) < (ctx.n24CarryData.r : ℝ) + 1 := by positivity
  have h2 : (260046848 : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      < 204 * ((shellLadderDepth ctx : ℕ) : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1) := by
    nlinarith [h, hfire]
  have h3 : (260046848 : ℝ) < 204 * ((shellLadderDepth ctx : ℕ) : ℝ) :=
    lt_of_mul_lt_mul_right h2 hr1.le
  have h4 : (260046848 : ℕ) < 204 * shellLadderDepth ctx := by exact_mod_cast h3
  omega

/-! ## Part 3.  The M.5/L.3 exit-mass control core and the kills -/

/-- **The class-4 (return lane) corrected mass cap kills the band-2 pin OUTRIGHT, at
every scale**: the pin relocates the whole pressure floor into class 4
(`band2_pressure_in_class4`), and `(1/2)·X·(r+1) ≥ (1/2)·X > (31/1536)·X`. -/
theorem emc_returnCap_kills_band2 (ctx : ActualFailureContext)
    (hcap : routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ≤ emcCap ctx) :
    ¬ OrbitBandPinned ctx 2 := by
  intro hpin
  have h1 : (1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4 :=
    band2_pressure_in_class4 ctx hpin
  have hX := ctx.shell.X_pos_real
  have hr : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := Nat.cast_nonneg _
  unfold emcCap at hcap
  nlinarith [h1, hcap, hX, hr, mul_nonneg hX.le hr]

/-- **The class-3 (densepack lane) corrected mass cap kills the band-3 pin OUTRIGHT,
at every scale** (via `band3_pressure_in_class3`). -/
theorem emc_densePackCap_kills_band3 (ctx : ActualFailureContext)
    (hcap : routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3
      ≤ emcCap ctx) :
    ¬ OrbitBandPinned ctx 3 := by
  intro hpin
  have h1 : (1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3 :=
    band3_pressure_in_class3 ctx hpin
  have hX := ctx.shell.X_pos_real
  have hr : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := Nat.cast_nonneg _
  unfold emcCap at hcap
  nlinarith [h1, hcap, hX, hr, mul_nonneg hX.le hr]

/-- The class-3 cap kills the WIDE band-3 pin (the q-window guard is dropped). -/
theorem emc_densePackCap_kills_band3Wide (ctx : ActualFailureContext)
    (hcap : routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3
      ≤ emcCap ctx) :
    ¬ Band3PinnedWide ctx := fun hwide =>
  emc_densePackCap_kills_band3 ctx hcap hwide.1

/-- **The class-5 (run lane) corrected mass cap kills the band-4 pin OUTRIGHT, at
every scale**: the pin relocates `511/512` of the pressure floor into class 5
(`band4_pressure_in_class5`), and `(511/1024)·X > (31/1536)·X`. -/
theorem emc_runCap_kills_band4 (ctx : ActualFailureContext)
    (hcap : routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ emcCap ctx) :
    ¬ OrbitBandPinned ctx 4 := by
  intro hpin
  have h1 : 511 / 512 * ((1 / 2 : ℝ) * (ctx.shell.X : ℝ)
        * ((ctx.n24CarryData.r : ℝ) + 1))
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5 :=
    band4_pressure_in_class5 ctx hpin
  have hX := ctx.shell.X_pos_real
  have hr : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := Nat.cast_nonneg _
  unfold emcCap at hcap
  nlinarith [h1, hcap, hX, hr, mul_nonneg hX.le hr]

/-- **THE IRREDUCIBLE M.5/L.3 CORE** (the ONE named structure): the corrected
per-class MASS caps at the three recurrent classes — class 3 (densepack lane, the
`(21,3)` pin), class 4 (return lane, the `(3,1)` pin), class 5 (run lane, the band-4
trio) — demanded only at the deep scales `X > 2^986891` where the orbit-pin axis is
open.  This is the word-level shadow of the manuscript's exit-mass control: L.3.1
charges every transient excursion to the packages, M.5.1 makes low transient exits
CNL leaves, and I.3 leaves clean in-cycle motion uncharged, so the recurrent-class
routed mass is held below the per-class corrected capacity `(31/1536)·X`. -/
structure ExitMassControlCore : Prop where
  /-- DensePack lane (class 3): the corrected mass cap at deep scales. -/
  densePackMass : ∀ ctx : ActualFailureContext, 2 ^ 986891 < ctx.X →
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3 ≤ emcCap ctx
  /-- Return lane (class 4): the corrected mass cap at deep scales. -/
  returnMass : ∀ ctx : ActualFailureContext, 2 ^ 986891 < ctx.X →
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4 ≤ emcCap ctx
  /-- Run lane (class 5): the corrected mass cap at deep scales. -/
  runMass : ∀ ctx : ActualFailureContext, 2 ^ 986891 < ctx.X →
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5 ≤ emcCap ctx

/-- **THE CORE SUPPLIES THE WHOLE v18 FRONTIER FIELD**: `ExitMassControlCore` kills
all five fixed data at every deep context — `deepOrbitPin : DeepOrbitPinVoiding` is
discharged outright. -/
theorem deepOrbitPinVoiding_of_exitMassControl (h : ExitMassControlCore) :
    DeepOrbitPinVoiding := by
  intro ctx hX
  exact ⟨emc_returnCap_kills_band2 ctx (h.returnMass ctx hX),
    emc_densePackCap_kills_band3Wide ctx (h.densePackMass ctx hX),
    emc_runCap_kills_band4 ctx (h.runMass ctx hX)⟩

/-- The core supplies the wave-8 deep axis `DeepFixedFamilyVoid`. -/
theorem deepFixedFamilyVoid_of_exitMassControl (h : ExitMassControlCore) :
    DeepFixedFamilyVoid :=
  deepOrbitPinVoiding_iff_deepFixedFamilyVoid.mp
    (deepOrbitPinVoiding_of_exitMassControl h)

/-- The core supplies the full v17 `returnBand2Void` field. -/
theorem returnBand2Void_of_exitMassControl (h : ExitMassControlCore) :
    ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 2 :=
  returnBand2Void_of_deepOrbitPinVoiding (deepOrbitPinVoiding_of_exitMassControl h)

/-- The core supplies the full v17 `densePackBand3Void` field. -/
theorem densePackBand3Void_of_exitMassControl (h : ExitMassControlCore) :
    ∀ ctx : ActualFailureContext, ¬ Band3PinnedWide ctx :=
  densePackBand3Void_of_deepOrbitPinVoiding (deepOrbitPinVoiding_of_exitMassControl h)

/-- The core supplies the full v17 `runBand4Void` field. -/
theorem runBand4Void_of_exitMassControl (h : ExitMassControlCore) :
    ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 4 :=
  runBand4Void_of_deepOrbitPinVoiding (deepOrbitPinVoiding_of_exitMassControl h)

/-- The honest residual beyond the open axis: the corrected per-class caps demanded
only on PIN-FREE deep contexts. -/
def ExitMassControlOffPin : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 986891 < ctx.X →
    ¬ OrbitBandPinned ctx 2 → ¬ OrbitBandPinned ctx 3 → ¬ OrbitBandPinned ctx 4 →
    (routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3 ≤ emcCap ctx
      ∧ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4 ≤ emcCap ctx
      ∧ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5 ≤ emcCap ctx)

/-- **NO FREE LUNCH, made exact**: the M.5/L.3 core is EQUIVALENT to (the deep
orbit-pin voiding) ∧ (the caps on pin-free deep contexts) — the exit-mass control
CONTAINS the open axis; what it adds beyond the axis is exactly the pin-free
conjunct. -/
theorem exitMassControl_iff_split :
    ExitMassControlCore ↔ (DeepOrbitPinVoiding ∧ ExitMassControlOffPin) := by
  constructor
  · intro h
    refine ⟨deepOrbitPinVoiding_of_exitMassControl h, ?_⟩
    intro ctx hX _ _ _
    exact ⟨h.densePackMass ctx hX, h.returnMass ctx hX, h.runMass ctx hX⟩
  · rintro ⟨hvoid, hoff⟩
    have key : ∀ ctx : ActualFailureContext, 2 ^ 986891 < ctx.X →
        (routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3 ≤ emcCap ctx
          ∧ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4 ≤ emcCap ctx
          ∧ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
              ≤ emcCap ctx) := by
      intro ctx hX
      obtain ⟨h2, hw3, h4⟩ := hvoid ctx hX
      have h3 : ¬ OrbitBandPinned ctx 3 := fun hp =>
        hw3 ((band3PinnedWide_iff_orbitBandPinned3 ctx).mpr hp)
      exact hoff ctx hX h2 h3 h4
    exact ⟨fun ctx hX => (key ctx hX).1, fun ctx hX => (key ctx hX).2.1,
      fun ctx hX => (key ctx hX).2.2⟩

/-! ## Part 4.  Honest machine-readable status -/

/-- Machine-readable, honest status of the exit-mass control pass. -/
def exitMassControlStatus : List String :=
  [ "THE 30% SHARPENING HUNT - SETTLED NEGATIVELY (PROVED, exact constants).  The " ++
      "lever target is the count-shaped corrected class row #fibre*Y <= (31/1536)*X " ++
      "with Y = L/64; firing it needs the heavy count above (31/24)*X/L ~ 1.29*X/L.  " ++
      "But the heavy count is capped by the SUPPORT count #HE <= W < (17/2^24)*X " ++
      "(emc_heavyCard_le_W + scc_supportShell_lt), and 17*L/2^30 < 31/1536 for every " ++
      "L <= 1274739: emc_countTimesY_lt_cap / emc_fibre_countTimesY_lt_cap - the row " ++
      "HOLDS as a theorem on the whole band L <= 1274739, for every routed fibre.  " ++
      "The needed count exceeds the TOTAL number of windows in the shell; NO " ++
      "sharpening of the heavy-count floor (30% or any amount) can fire the lever " ++
      "below the deep threshold.",
    "WHERE THE ~1.3 FACTOR LIVES (exact): a firing context must have L >= 1274740 " ++
      "(emc_fire_forces_deep), sharp at 26112*1274739 < 31*2^30 < 26112*1274740 " ++
      "(emc_threshold_sharp; 31*2^30/26112 = 31*2^24/408 = 1274739.45...).  The pins " ++
      "force only L >= 986894 (bands 2/3) / 986892 (band 4); the ratio " ++
      "1274739.45/986894 = 1.2917 is the wave-18 'factor ~1.3', and it is " ++
      "STRUCTURAL: 31*2^24/408 is EXACTLY the DeepShellTailClosure class-1 deep " ++
      "threshold (class1Deep is demanded at L >= 1274740) - the count lever fires " ++
      "only where the deep class-1 lane already starts.  Dead zones per pin: " ++
      "emc_band2_deadZone / emc_band3Wide_deadZone / emc_band4_deadZone.",
    "PER-WINDOW DEVIATION CAP (D0) VERDICT - THE PRIZE IS UNREACHABLE BELOW THE " ++
      "DEEP THRESHOLD (PROVED).  emc_uniformCap_floor: ANY uniform cap D0 on the " ++
      "heavy-window excesses obeys 2^23*(r+1) < 17*D0 - the Lemma 21.1 pressure " ++
      "floor against the support cap forces the AVERAGE heavy-window excess above " ++
      "(2^23/17)*(r+1) ~ 493447*(r+1) ~ 0.50*L*(r+1) at the pin frontier L = " ++
      "986894.  The hoped D0 <= 0.38*L*(r+1) does not exist - not merely not " ++
      "in-tree, but contradicted by the context itself.  The lever mechanism IS " ++
      "real (emc_lever_fires_of_D0: a uniform cap with 31*D0 < 12*L*(r+1) pushes " ++
      "the count row over), but emc_D0_fire_forces_deep: the two constraints meet " ++
      "only at L >= 1274740 = the same 31*2^24/408 threshold.  The 2-periodicity " ++
      "machinery cannot help below it: any per-window bound it produced would " ++
      "still be a uniform cap and hit the same floor.",
    "THE TRUE ARITHMETIC CHAIN (verified in-tree): pressure floor (1/2)*X*(r+1) <= " ++
      "highExcessMass (n24CarryData.highExcessMass_lower); per-member ceiling " ++
      "windowExcess <= runDyadicMult <= (r+1)*(L+B+1) gives the heavy-count floor " ++
      "#HE >= X/(2(L+B+1)) (fde_highExcess_card_floor); the syndetic support " ++
      "floors X/(L+2) <= W (orbitBandPinned2/3_support_floor) floor the SUPPORT " ++
      "count, not the heavy count - and even a heavy count at the full support " ++
      "floor X/(L+2) would still miss the needed (31/24)*X/L by the same factor " ++
      "1.29.  The mass-shaped row needs NO sharpening at all: (1/2)*X*(r+1) > " ++
      "(31/1536)*X at every scale - the relocation floors already overwhelm the " ++
      "corrected capacity; the open question was never the floor but WHO PROVES " ++
      "THE CAP.",
    "THE M.5/L.3 TRANSCRIPTION (the manuscript mechanism, read at L.3.1/M.5.1/I.3 " ++
      "+-80 lines): L.3.1 charges every transient excursion from a recurrent tower " ++
      "SCC to Run/Return/DensePack/Progress/Endpoint/clean-CNL-tail (first-event " ++
      "routing, charged summability L.2.4); M.5.1 makes low transient exits CNL " ++
      "terminal leaves (the determined terminal label adds no lift-state codes); " ++
      "I.3 charges only first-entry/first-exit branches - clean in-cycle motion is " ++
      "uncharged.  Word-level shadow at the five fixed data: the recurrent-class " ++
      "routed mass is held below the per-class corrected capacity (31/1536)*X " ++
      "(emcCap, = cStar*xi/6*X by emcCap_eq_corrected).  THE ONE NAMED STRUCTURE: " ++
      "ExitMassControlCore - mass_3, mass_4, mass_5 <= (31/1536)*X demanded only " ++
      "at deep scales X > 2^986891.",
    "THE KILLS (PROVED, unconditional in scale): each per-class cap kills its pin " ++
      "OUTRIGHT - the pin relocates the whole pressure floor into its class " ++
      "(band2_pressure_in_class4 / band3_pressure_in_class3 / " ++
      "band4_pressure_in_class5) and (1/2)*X*(r+1) >= (1/2)*X > (31/1536)*X " ++
      "(resp. (511/1024)*X): emc_returnCap_kills_band2, " ++
      "emc_densePackCap_kills_band3(+Wide), emc_runCap_kills_band4.  No scale " ++
      "hypothesis, no r-floor, no Q-bound consumed.  Hence " ++
      "deepOrbitPinVoiding_of_exitMassControl: ExitMassControlCore supplies the " ++
      "ENTIRE v18 frontier field deepOrbitPin, the wave-8 axis " ++
      "(deepFixedFamilyVoid_of_exitMassControl) and all three v17 voiding fields " ++
      "(returnBand2Void/densePackBand3Void/runBand4Void_of_exitMassControl).",
    "NO FREE LUNCH, exact (exitMassControl_iff_split): ExitMassControlCore <-> " ++
      "DeepOrbitPinVoiding AND ExitMassControlOffPin (the caps on pin-free deep " ++
      "contexts).  The M.5/L.3 control CONTAINS the open axis - supplying it is " ++
      "never cheaper than voiding the pins - and its honest content beyond the " ++
      "axis is exactly the pin-free conjunct.  KILL VERDICT: none unconditional; " ++
      "the conditional kill is ExitMassControlCore (equivalently: prove the " ++
      "corrected mass caps at the three recurrent classes on deep shells).",
    "HYGIENE: additive only - ONE new module, no existing file edited, root " ++
      "import untouched; no sorry / admit / new axiom / native_decide; every key " ++
      "declaration passes #print axioms within [propext, Classical.choice, " ++
      "Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem exitMassControlStatus_nonempty : exitMassControlStatus ≠ [] := by
  simp [exitMassControlStatus]

/-! ## Part 5.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]` or
fewer. -/

#print axioms emcCap_eq_corrected
#print axioms emc_heavyCard_le_W
#print axioms emc_fibre_subset_heavy
#print axioms emc_countTimesY_lt_cap
#print axioms emc_fibre_countTimesY_lt_cap
#print axioms emc_fire_forces_deep
#print axioms emc_threshold_sharp
#print axioms emc_band2_deadZone
#print axioms emc_band3Wide_deadZone
#print axioms emc_band4_deadZone
#print axioms emc_uniformCap_floor
#print axioms emc_lever_fires_of_D0
#print axioms emc_D0_fire_forces_deep
#print axioms emc_returnCap_kills_band2
#print axioms emc_densePackCap_kills_band3
#print axioms emc_densePackCap_kills_band3Wide
#print axioms emc_runCap_kills_band4
#print axioms deepOrbitPinVoiding_of_exitMassControl
#print axioms deepFixedFamilyVoid_of_exitMassControl
#print axioms returnBand2Void_of_exitMassControl
#print axioms densePackBand3Void_of_exitMassControl
#print axioms runBand4Void_of_exitMassControl
#print axioms exitMassControl_iff_split
#print axioms exitMassControlStatus_nonempty

end

end Erdos260
