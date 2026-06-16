import Erdos260.Erdos260ConvergenceCapstone
import Erdos260.DensePackLandsShiftCore
import Erdos260.DensePackClass3CycleClosure
import Erdos260.FixedDataEndgame
import Erdos260.CNLMultiChargeUnconditional
import Erdos260.CNLScalarBudgetCore
import Erdos260.RhoDQPrecursorConsumerCore

/-!
# The K.1 landing closure (`K1LandingClosure`)

This module (NEW; it edits no existing file) attacks **the K.1 landing**: the wave-19
capstone's two densepack `b₃ > 0` fields (`Erdos260ConvergenceCapstone.lean`)

```
densePackCoverOffTable   :  |gdps| · ((r+1)·G₀ − (2L+1))  ≤  |actualPoints|     (guarded)
densePackDensityOffTable :  densePackEndpointDensity ctx                        (guarded)
```

with `gdps = genuineDensePackStarts ctx`, `G₀ = densePackDyadicG0 ctx = L + B + 1`
(`= proofV4DensePackSpread ctx.shell` definitionally) and
`actualPoints = proofV4DensePackActualPoints ctx.shell`.

## The two-sided anatomy (audited here, goal 1)

* An **actual point** `m` is a position of the ambient window `[0, 3X + spread]` whose
  one-sided support packet `[m, m + spread] ∩ supportShell d X` carries at least the
  manuscript floor `⌊ρ_D L⌋ = proofV4DensePackMinHits` shell hits
  (`mem_proofV4DensePackActualPoints`, `DensePackLandsShiftCore`).
* A **genuine start** `k` is a high-excess index (`windowExcess ≥ Y`: the descent window
  `[k, k+r]` of the hit sequence spans a LARGE spatial range) whose L.3.1 tower-exit class
  is `densePack` (`mem_genuineDensePackStarts`).
* The density field demands EXACTLY the actual-point filter predicate at each genuine
  start's terminal endpoint `k + r` — proved sharp here, budget-free:
  `densePackEndpointDensity_iff_endpoints_mem`.  So the density field IS the statement
  that the endpoint map `k ↦ k + r` LANDS in the actual-point set; the cover field then
  asks that landing to carry **multiplicity `W := (r+1)·G₀ − (2L+1)`** per start.

## What is PROVED here (no `sorry`/`axiom`/`admit`/`native_decide`)

1. **Width arithmetic** (`k1CoverWidth`): `W = 0 ↔ r = 0` (`k1CoverWidth_eq_zero_iff`;
   uses the largeness gate `B + 25 ≤ L`), `r ≥ 1 → 2B + 1 ≤ W` (`k1CoverWidth_lower_of_r_ge_one`),
   `r = 1 → W = 2B + 1` exactly (`k1CoverWidth_eq_of_r_eq_one`), and `r ≥ 1 → 7 ≤ W`
   (`k1CoverWidth_ge_seven_of_r_ge_one`, via `carryB Q ≥ 3`).
2. **UNCONDITIONAL `r = 0` closure of the cover field**: at `r = 0` the demanded width
   truncates to `0` in `ℕ`, so the cover body holds outright
   (`k1CoverBody_of_r_eq_zero`, numeral form `k1CoverBody_of_L_le` for all `L ≤ 15420`).
   `k1DensePackCoverOffTableField_of_deepStrata` rebuilds the EXACT v19 field from a
   supplier demanded only at `r ≥ 1`.
3. **The K.1.3/I.4 multiplicity-one SDR** (the manuscript first-stop owner `Φ = (·−r)`):
   the bare density already injects the genuine starts into the actual points,
   `|gdps| ≤ |actualPoints|` (`k1Count_le_actualPoints_of_density`) — and this is
   SHARPLY INSUFFICIENT for the cover at `r ≥ 1`, where the demand forces a supply of
   `≥ 7` points per start (`k1CoverBody_forces_supply`).
4. **The K.1.1 coarea cluster supply** (the area double-count, made exact): if the
   endpoint window's hits keep a top slack of `W` positions (`K1ClusterFloor`), then the
   whole block `[k+r+1−W, k+r]` of `W` consecutive positions consists of actual points
   (`k1PointBlock_subset_actualPoints`, `k1PointBlock_card` — the per-window supply is
   genuinely `W`, with the block floor `W ≤ k + r` DERIVED from density via the dyadic
   largeness `(L+2)(2L+1) ≤ 2^L`, `k1_poly_le_two_pow`).
5. **The SDR-with-multiplicity landing**: density + cluster floor + `W`-spacing of the
   genuine starts (`K1StartSpacing`) prove the cover body EXACTLY
   (`k1CoverBody_of_density_cluster_spacing`) — disjoint per-start blocks, summed by
   `Finset.card_biUnion`.  This is the honest in-tree transcription of the manuscript
   K.1.3′ marginal/Hall form (tex 4732-4752) at point-multiplicity `W`.
6. **Spacing supply from the certified cycles**: on any context whose slope orbit is
   `c`-periodic with AT MOST ONE band-3 residue (`|cycleBand3Residues ctx c| ≤ 1` — the
   `b₃ = 1` rows of `dscPairTable`), distinct genuine starts are `c`-spaced
   (`k1StartSpacing_of_singleResidue`); with `W ≤ c` this discharges the spacing atom.
   At `r = 1` the width is exactly `2B + 1`, so the regime is `2·carryB Q + 1 ≤ c`
   (`k1CoverBody_of_r_one_singleResidue`).
7. **The density field treatment**: the sharp endpoint-landing characterization
   (`densePackEndpointDensity_iff_endpoints_mem`), the extracted position constraint —
   density forces every genuine endpoint into the band `X − spread < k + r ≤ 2X`
   (`k1Density_endpoint_band`, the off-pin analogue of `band3_density_forces_subshell`) —
   and the vacuous-stratum closure (`densePackEndpointDensity_of_emptyStarts`).
8. **Wiring to the EXACT v19 field shapes**: `k1DensePackCoverOffTableField_of_deepStrata`,
   `k1DensePackCoverOffTableField_of_atoms`, `k1DensePackDensityOffTableField_of_landing` —
   additive suppliers for `densePackCoverOffTable` / `densePackDensityOffTable`, composable
   with the in-tree dispatchers `dscDensePackCoverFreeField_of_offTable` /
   `dscDensePackDensityField_of_offTable`.

## The named irreducible remainder

* **`K1ClusterFloor`** — the per-window hit-cluster floor: at every genuine start the
  endpoint window's hits sit in the bottom `spread + 1 − W` positions.  This is the
  per-window placement content of the manuscript per-start SDR floor (K.1.3, `ρ_D L`
  owned hits) that the bare cardinality floor `⌊ρ_D L⌋ ≤ |window|` does NOT pin down.
* **`K1StartSpacing`** — `W`-spacing of distinct genuine starts (the wave-19 spacing-hunt
  target); DISCHARGED on single-band-3-residue cycles with `c ≥ W` (item 6), open elsewhere.
* The pinned-vs-Q-correct `ρ_D` note: the actual-point filter is the PINNED floor
  `⌊(1/4)·L⌋`; the Q-correct `rhoDQ` floor is smaller
  (`proofV4DensePackMinHitsRhoDQ_le_pinned`), so the Q-correct density
  `densePackEndpointDensityRhoDQ` (projection `densePackEndpointDensityRhoDQ_of_pinned`)
  does NOT feed this landing — only the pinned density does.

Both atoms are jointly inhabited on the whole `r = 0` stratum
(`k1ClusterFloor_of_r_eq_zero`, `k1StartSpacing_of_r_eq_zero`) — no vacuity, no degeneracy.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The demanded per-start width `W = (r+1)·G₀ − (2L+1)` -/

/-- **The corrected K.1.2 per-start cover width** demanded by the v19 cover field:
`W = (r+1)·(L+B+1) − (2L+1)` in `ℕ` (truncated subtraction). -/
def k1CoverWidth (ctx : ActualFailureContext) : ℕ :=
  (ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx - (2 * shellLadderDepth ctx + 1)

/-- At `r = 0` the width truncates to `0`: `(L+B+1) ≤ 2L+1` from the largeness gate
`B + 25 ≤ L` (`shell_carryLarge`). -/
theorem k1CoverWidth_eq_zero_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) : k1CoverWidth ctx = 0 := by
  have hBL : carryB ctx.shell.Q + 25 ≤ shellLadderDepth ctx := ctx.shell_carryLarge
  have hG0 : densePackDyadicG0 ctx
      = shellLadderDepth ctx + carryB ctx.shell.Q + 1 := rfl
  unfold k1CoverWidth
  rw [hr, hG0]
  omega

/-- At `r ≥ 1` the width is at least `2B + 1` (the tex K.1.2-remark bound, exact). -/
theorem k1CoverWidth_lower_of_r_ge_one (ctx : ActualFailureContext)
    (hr : 1 ≤ ctx.n24CarryData.r) :
    2 * carryB ctx.shell.Q + 1 ≤ k1CoverWidth ctx := by
  have hG0 : densePackDyadicG0 ctx
      = shellLadderDepth ctx + carryB ctx.shell.Q + 1 := rfl
  have key : 2 * carryB ctx.shell.Q + 1 + (2 * shellLadderDepth ctx + 1)
      ≤ (ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx := by
    calc 2 * carryB ctx.shell.Q + 1 + (2 * shellLadderDepth ctx + 1)
        = 2 * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by ring
      _ ≤ (ctx.n24CarryData.r + 1)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) :=
          Nat.mul_le_mul (by omega) (le_refl _)
      _ = (ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx := by rw [hG0]
  exact Nat.le_sub_of_add_le key

/-- At `r = 1` the width is EXACTLY `2B + 1` — independent of `L`.  This pins the live
`r = 1` regime of the cover demand to the carry-denominator scale alone. -/
theorem k1CoverWidth_eq_of_r_eq_one (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 1) :
    k1CoverWidth ctx = 2 * carryB ctx.shell.Q + 1 := by
  have hG0 : densePackDyadicG0 ctx
      = shellLadderDepth ctx + carryB ctx.shell.Q + 1 := rfl
  unfold k1CoverWidth
  rw [hr, hG0]
  omega

/-- The carry-denominator scale is at least `3` (`Q ≥ 1` so `4 ≤ Q·4` and
`log₂(Q·4) ≥ 2`). -/
theorem k1_carryB_ge_three (ctx : ActualFailureContext) :
    3 ≤ carryB ctx.shell.Q := by
  have hQ : 1 ≤ ctx.shell.Q := ctx.shell.hQ
  have hlog : 2 ≤ Nat.log 2 (ctx.shell.Q * 4) := by
    apply Nat.le_log_of_pow_le Nat.one_lt_two
    calc (2 : ℕ) ^ 2 = 4 := by norm_num
      _ ≤ ctx.shell.Q * 4 := by omega
  unfold carryB
  omega

/-- At `r ≥ 1` the width is at least `7 = 2·3 + 1`. -/
theorem k1CoverWidth_ge_seven_of_r_ge_one (ctx : ActualFailureContext)
    (hr : 1 ≤ ctx.n24CarryData.r) : 7 ≤ k1CoverWidth ctx := by
  have h1 := k1CoverWidth_lower_of_r_ge_one ctx hr
  have h2 := k1_carryB_ge_three ctx
  omega

/-- **The sharp width dichotomy**: the demanded width vanishes iff `r = 0`. -/
theorem k1CoverWidth_eq_zero_iff (ctx : ActualFailureContext) :
    k1CoverWidth ctx = 0 ↔ ctx.n24CarryData.r = 0 := by
  constructor
  · intro h
    by_contra hr
    have h7 := k1CoverWidth_ge_seven_of_r_ge_one ctx (by omega)
    omega
  · exact k1CoverWidth_eq_zero_of_r_eq_zero ctx

/-! ## 2.  The UNCONDITIONAL `r = 0` closure of the cover body -/

/-- **The `r = 0` stratum of the v19 cover field closes unconditionally**: the demanded
width is `0` in `ℕ`, so the left side vanishes. -/
theorem k1CoverBody_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card := by
  have hW := k1CoverWidth_eq_zero_of_r_eq_zero ctx hr
  unfold k1CoverWidth at hW
  rw [hW, Nat.mul_zero]
  exact Nat.zero_le _

/-- Numeral form: the cover body holds outright on every shell with `L ≤ 15420`
(the whole `r = ⌊κL⌋ = 0` regime at the pinned `κ = 17/2¹⁸`). -/
theorem k1CoverBody_of_L_le (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 15420) :
    (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  k1CoverBody_of_r_eq_zero ctx (n24_r_eq_zero_of_L_le ctx hL)

/-! ## 3.  The density field anatomy: landing + position constraint

`densePackEndpointDensity` is EXACTLY the statement that each genuine start's terminal
endpoint `k + r` lies in the actual-point set — the budget-free sharp form of the
wave-14/15 `densePackLandsShift_iff_density`. -/

/-- **The sharp budget-free characterization of the density field**: density ↔ every
genuine endpoint `k + r` is an actual point.  Forward: `mem_actualPoints_of_density`
(range discharged from one hit); backward: project the filter's density conjunct. -/
theorem densePackEndpointDensity_iff_endpoints_mem (ctx : ActualFailureContext) :
    densePackEndpointDensity ctx
      ↔ ∀ k ∈ genuineDensePackStarts ctx,
          k + ctx.n24CarryData.r ∈ proofV4DensePackActualPoints ctx.shell := by
  constructor
  · intro h k hk
    exact mem_actualPoints_of_density ctx (h k hk)
  · intro h k hk
    have hm := h k hk
    rw [mem_proofV4DensePackActualPoints] at hm
    exact hm.2

/-- **The extracted position constraint** (the off-pin analogue of
`band3_density_forces_subshell`): the per-endpoint density forces the endpoint into the
band `X − spread < k + r ≤ 2X` — a non-empty window must reach into the shell `(X, 2X]`
from below. -/
theorem k1Density_endpoint_band (ctx : ActualFailureContext) {k : ℕ}
    (hdk : proofV4DensePackMinHits ctx.shell
      ≤ (proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)).card) :
    ctx.shell.X < k + ctx.n24CarryData.r + proofV4DensePackSpread ctx.shell
      ∧ k + ctx.n24CarryData.r ≤ 2 * ctx.shell.X := by
  have hpos : 0 < (proofV4DensePackSupportWindow ctx.shell
      (k + ctx.n24CarryData.r)).card :=
    lt_of_lt_of_le (proofV4DensePackMinHits_pos ctx) hdk
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hpos
  have hn' := Finset.mem_filter.mp hn
  obtain ⟨hX1, hX2, _⟩ := (mem_supportShell ctx.shell.d ctx.shell.X n).mp hn'.1
  obtain ⟨hmn, hns⟩ := hn'.2
  omega

/-- The density field as a whole forces ALL genuine endpoints into the shell band — the
demand's honest content as a satisfiable position constraint. -/
theorem k1DensityField_position_constraint (ctx : ActualFailureContext)
    (hd : densePackEndpointDensity ctx) :
    ∀ k ∈ genuineDensePackStarts ctx,
      ctx.shell.X < k + ctx.n24CarryData.r + proofV4DensePackSpread ctx.shell
        ∧ k + ctx.n24CarryData.r ≤ 2 * ctx.shell.X :=
  fun k hk => k1Density_endpoint_band ctx (hd k hk)

/-- The density field closes on the vacuous stratum (no genuine densePack start). -/
theorem densePackEndpointDensity_of_emptyStarts (ctx : ActualFailureContext)
    (h : genuineDensePackStarts ctx = ∅) : densePackEndpointDensity ctx := by
  intro k hk
  rw [h] at hk
  simp at hk

/-! ## 4.  The K.1.3/I.4 multiplicity-one SDR and its sharp insufficiency

The first-stop owner `Φ = (·−r)` (the manuscript K.1.3 single-owner retraction) makes the
endpoint map `k ↦ k + r` injective; density lands it in the actual points.  This gives the
K.1.1 count `|gdps| ≤ |actualPoints|` — but the cover demands width-`W` multiplicity, and
`W ≥ 7` whenever `r ≥ 1`. -/

/-- **The multiplicity-one SDR count, budget-free on the actual points**: under the bare
density, the genuine starts inject into the actual points via `k ↦ k + r`. -/
theorem k1Count_le_actualPoints_of_density (ctx : ActualFailureContext)
    (hd : densePackEndpointDensity ctx) :
    (genuineDensePackStarts ctx).card
      ≤ (proofV4DensePackActualPoints ctx.shell).card := by
  apply Finset.card_le_card_of_injOn (fun k => k + ctx.n24CarryData.r)
  · intro k hk
    exact mem_actualPoints_of_density ctx (hd k hk)
  · intro a _ b _ hab
    have hab' : a + ctx.n24CarryData.r = b + ctx.n24CarryData.r := hab
    omega

/-- **Sharp insufficiency of multiplicity one at `r ≥ 1`**: the cover body itself forces a
supply of at least `7` actual points per genuine start — so the bare injection
(`k1Count_le_actualPoints_of_density`) can never close any `r ≥ 1` stratum; per-start
multiplicity `≥ W` is genuinely required. -/
theorem k1CoverBody_forces_supply (ctx : ActualFailureContext)
    (hr : 1 ≤ ctx.n24CarryData.r)
    (hcover : (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card) :
    7 * (genuineDensePackStarts ctx).card
      ≤ (proofV4DensePackActualPoints ctx.shell).card := by
  have h7 : 7 ≤ (ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
      - (2 * shellLadderDepth ctx + 1) := by
    have h := k1CoverWidth_ge_seven_of_r_ge_one ctx hr
    unfold k1CoverWidth at h
    exact h
  calc 7 * (genuineDensePackStarts ctx).card
      = (genuineDensePackStarts ctx).card * 7 := Nat.mul_comm _ _
    _ ≤ (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1)) :=
        Nat.mul_le_mul (le_refl _) h7
    _ ≤ (proofV4DensePackActualPoints ctx.shell).card := hcover

/-! ## 5.  The K.1.1 coarea cluster supply: `W` actual points per start

The area double-count made exact: if the endpoint window's hits keep a top slack of `W`
positions, then EVERY position of the block `[k+r+1−W, k+r]` sees all the window's hits
inside its own window, so the whole block consists of actual points.  The block floor
`W ≤ k + r` is DERIVED from density via the dyadic largeness `(L+2)(2L+1) ≤ 2^L`. -/

/-- Dyadic largeness: `(n+2)·(2n+1) ≤ 2^n` for `n ≥ 28`. -/
theorem k1_poly_le_two_pow {n : ℕ} (hn : 28 ≤ n) :
    (n + 2) * (2 * n + 1) ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hstep : (n + 1 + 2) * (2 * (n + 1) + 1)
          ≤ 2 * ((n + 2) * (2 * n + 1)) := by nlinarith
      calc (n + 1 + 2) * (2 * (n + 1) + 1)
          ≤ 2 * ((n + 2) * (2 * n + 1)) := hstep
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul (le_refl 2) ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- **The block floor from density**: a dense endpoint sits above `X − spread`, and
`X = 2^L` dominates `(L+2)(2L+1) ≥ W + spread`, so `W ≤ k + r`.  (Uses `r ≤ L`
(`fde_r_le_L`), `B + 25 ≤ L` (`shell_carryLarge`), `L ≥ 28` (`shellLadderDepth_ge`).) -/
theorem k1CoverWidth_le_endpoint_of_density (ctx : ActualFailureContext) {k : ℕ}
    (hdk : proofV4DensePackMinHits ctx.shell
      ≤ (proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)).card) :
    k1CoverWidth ctx ≤ k + ctx.n24CarryData.r := by
  obtain ⟨hband, _⟩ := k1Density_endpoint_band ctx hdk
  have hX : ctx.shell.X = 2 ^ shellLadderDepth ctx :=
    Classical.choose_spec ctx.shell.hXdyadic
  have hL28 : 28 ≤ shellLadderDepth ctx := shellLadderDepth_ge ctx
  have hBL : carryB ctx.shell.Q + 25 ≤ shellLadderDepth ctx := ctx.shell_carryLarge
  have hrL : ctx.n24CarryData.r ≤ shellLadderDepth ctx := fde_r_le_L ctx
  have hG0 : densePackDyadicG0 ctx
      = shellLadderDepth ctx + carryB ctx.shell.Q + 1 := rfl
  have hspread : proofV4DensePackSpread ctx.shell
      = shellLadderDepth ctx + carryB ctx.shell.Q + 1 := rfl
  have hmul : (ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
      ≤ (shellLadderDepth ctx + 1) * (2 * shellLadderDepth ctx + 1) := by
    have hG0le : densePackDyadicG0 ctx ≤ 2 * shellLadderDepth ctx + 1 := by
      rw [hG0]; omega
    exact Nat.mul_le_mul (by omega) hG0le
  have hkey : k1CoverWidth ctx + (2 * shellLadderDepth ctx + 1)
      ≤ 2 ^ shellLadderDepth ctx := by
    calc k1CoverWidth ctx + (2 * shellLadderDepth ctx + 1)
        ≤ (ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            + (2 * shellLadderDepth ctx + 1) :=
          Nat.add_le_add_right (Nat.sub_le _ _) _
      _ ≤ (shellLadderDepth ctx + 1) * (2 * shellLadderDepth ctx + 1)
            + (2 * shellLadderDepth ctx + 1) := Nat.add_le_add_right hmul _
      _ = (shellLadderDepth ctx + 2) * (2 * shellLadderDepth ctx + 1) := by ring
      _ ≤ 2 ^ shellLadderDepth ctx := k1_poly_le_two_pow hL28
  rw [hX, hspread] at hband
  omega

/-- **THE NAMED PER-WINDOW ATOM (K.1.1 cluster floor).**  At every genuine start the
endpoint window's hits cluster into the bottom `spread + 1 − W` positions of the window:
every hit keeps top slack `W`, `n + W ≤ (k + r) + spread + 1`.  This is the per-window
placement content of the manuscript K.1.3 per-start floor (the `ρ_D L` owned hits) that
the bare cardinality floor does not pin down — the irreducible coarea remainder. -/
def K1ClusterFloor (ctx : ActualFailureContext) : Prop :=
  ∀ k ∈ genuineDensePackStarts ctx,
    ∀ n ∈ proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r),
      n + k1CoverWidth ctx
        ≤ k + ctx.n24CarryData.r + proofV4DensePackSpread ctx.shell + 1

/-- **THE NAMED SPACING ATOM (K.1.3 SDR spacing).**  Distinct genuine starts are spaced
at least `W` apart — the wave-19 spacing-hunt target, named exactly. -/
def K1StartSpacing (ctx : ActualFailureContext) : Prop :=
  ∀ k ∈ genuineDensePackStarts ctx, ∀ k' ∈ genuineDensePackStarts ctx,
    k < k' → k + k1CoverWidth ctx ≤ k'

/-- Both atoms hold trivially on the whole `r = 0` stratum (`W = 0`) — joint
inhabitation, no vacuity. -/
theorem k1ClusterFloor_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) : K1ClusterFloor ctx := by
  intro k hk n hn
  have hW := k1CoverWidth_eq_zero_of_r_eq_zero ctx hr
  have hn' := Finset.mem_filter.mp hn
  have hns := hn'.2.2
  omega

/-- The spacing atom on the `r = 0` stratum (`W = 0`). -/
theorem k1StartSpacing_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) : K1StartSpacing ctx := by
  intro k _ k' _ hlt
  have hW := k1CoverWidth_eq_zero_of_r_eq_zero ctx hr
  omega

/-- The per-start block of `W` consecutive positions ending at the endpoint `k + r`. -/
def k1PointBlock (ctx : ActualFailureContext) (k : ℕ) : Finset ℕ :=
  Finset.Icc (k + ctx.n24CarryData.r + 1 - k1CoverWidth ctx) (k + ctx.n24CarryData.r)

/-- The block supply is genuinely `W` (given the derived block floor). -/
theorem k1PointBlock_card (ctx : ActualFailureContext) {k : ℕ}
    (hWe : k1CoverWidth ctx ≤ k + ctx.n24CarryData.r) :
    (k1PointBlock ctx k).card = k1CoverWidth ctx := by
  rw [k1PointBlock, Nat.card_Icc]
  omega

/-- **The cluster supply** (the K.1.1 coarea double-count, exact form): under density and
the cluster floor, the WHOLE per-start block consists of actual points — each block
position `m` sees every window hit (`m ≤ k+r ≤ n` and `n ≤ m + spread` from the slack),
so its own window dominates the endpoint window's card. -/
theorem k1PointBlock_subset_actualPoints (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ genuineDensePackStarts ctx)
    (hd : densePackEndpointDensity ctx)
    (hcl : K1ClusterFloor ctx) :
    k1PointBlock ctx k ⊆ proofV4DensePackActualPoints ctx.shell := by
  intro m hm
  rw [k1PointBlock, Finset.mem_Icc] at hm
  have hdk := hd k hk
  have hWe : k1CoverWidth ctx ≤ k + ctx.n24CarryData.r :=
    k1CoverWidth_le_endpoint_of_density ctx hdk
  have hsub : proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)
      ⊆ proofV4DensePackSupportWindow ctx.shell m := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hcap := hcl k hk n hn
    have hlo := hn'.2.1
    have hhi := hn'.2.2
    refine Finset.mem_filter.mpr ⟨hn'.1, ?_, ?_⟩
    · omega
    · omega
  exact mem_actualPoints_of_density ctx
    (le_trans hdk (Finset.card_le_card hsub))

/-- Distinct `W`-spaced starts have disjoint blocks. -/
theorem k1PointBlock_disjoint (ctx : ActualFailureContext) {k k' : ℕ}
    (_hlt : k < k') (hsp : k + k1CoverWidth ctx ≤ k') :
    Disjoint (k1PointBlock ctx k) (k1PointBlock ctx k') := by
  rw [Finset.disjoint_left]
  intro m hm hm'
  rw [k1PointBlock, Finset.mem_Icc] at hm hm'
  omega

/-! ## 6.  The SDR-with-multiplicity landing: the cover body from the two atoms -/

/-- **THE K.1 LANDING (K.1.1 coarea + K.1.3′ SDR, exact `ℕ` form)**: density + the
per-window cluster floor + the `W`-spacing of genuine starts prove the v19 cover body —
each start supplies a block of `W` actual points, blocks are pairwise disjoint, and the
disjoint union counts `|gdps| · W ≤ |actualPoints|`. -/
theorem k1CoverBody_of_density_cluster_spacing (ctx : ActualFailureContext)
    (hd : densePackEndpointDensity ctx)
    (hcl : K1ClusterFloor ctx)
    (hsp : K1StartSpacing ctx) :
    (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card := by
  classical
  have hdisj : ∀ a ∈ genuineDensePackStarts ctx, ∀ b ∈ genuineDensePackStarts ctx,
      a ≠ b → Disjoint (k1PointBlock ctx a) (k1PointBlock ctx b) := by
    intro a ha b hb hab
    rcases Nat.lt_or_ge a b with h | h
    · exact k1PointBlock_disjoint ctx h (hsp a ha b hb h)
    · have h' : b < a := by omega
      exact (k1PointBlock_disjoint ctx h' (hsp b hb a ha h')).symm
  have hcards : ∀ k ∈ genuineDensePackStarts ctx,
      (k1PointBlock ctx k).card = k1CoverWidth ctx := fun k hk =>
    k1PointBlock_card ctx (k1CoverWidth_le_endpoint_of_density ctx (hd k hk))
  have h1 : ∑ k ∈ genuineDensePackStarts ctx, (k1PointBlock ctx k).card
      = (genuineDensePackStarts ctx).card * k1CoverWidth ctx := by
    rw [Finset.sum_congr rfl hcards, Finset.sum_const, smul_eq_mul]
  have hmain : (genuineDensePackStarts ctx).card * k1CoverWidth ctx
      ≤ (proofV4DensePackActualPoints ctx.shell).card := by
    calc (genuineDensePackStarts ctx).card * k1CoverWidth ctx
        = ∑ k ∈ genuineDensePackStarts ctx, (k1PointBlock ctx k).card := h1.symm
      _ = ((genuineDensePackStarts ctx).biUnion (k1PointBlock ctx)).card :=
          (Finset.card_biUnion hdisj).symm
      _ ≤ (proofV4DensePackActualPoints ctx.shell).card :=
          Finset.card_le_card (Finset.biUnion_subset.mpr
            (fun k hk => k1PointBlock_subset_actualPoints ctx hk hd hcl))
  exact hmain

/-! ## 7.  Discharging the spacing atom on single-band-3-residue cycles

On any context whose slope orbit is `c`-periodic with at most one band-3 residue (the
`b₃ ≤ 1` rows of `dscPairTable`), all genuine starts share ONE residue class mod `c`, so
distinct starts are `c`-spaced; `W ≤ c` then discharges `K1StartSpacing`. -/

/-- **Spacing from a single band-3 residue**: `c`-periodicity + `|cycleBand3Residues| ≤ 1`
+ `W ≤ c` give the `W`-spacing of genuine starts. -/
theorem k1StartSpacing_of_singleResidue (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hb3 : (cycleBand3Residues ctx c).card ≤ 1)
    (hcW : k1CoverWidth ctx ≤ c) :
    K1StartSpacing ctx := by
  intro k hk k' hk' hlt
  have h1 : 1 ≤ k := densePackStarts_start_pos ctx hk
  have hres : (k - 1) % c = (k' - 1) % c := by
    have hm := densePackStarts_residue_mem ctx hc hper hk
    have hm' := densePackStarts_residue_mem ctx hc hper hk'
    exact Finset.card_le_one.mp hb3 _ hm _ hm'
  have hdvd : c ∣ (k' - 1) - (k - 1) :=
    (Nat.modEq_iff_dvd' (by omega)).mp hres
  have hpos : 0 < (k' - 1) - (k - 1) := by omega
  have hge : c ≤ (k' - 1) - (k - 1) := Nat.le_of_dvd hpos hdvd
  omega

/-- **The `r = 1` per-pair regime, fully reduced**: on a `c`-periodic orbit with at most
one band-3 residue and `2·carryB Q + 1 ≤ c`, the cover body follows from density + the
cluster floor alone (the spacing atom is DISCHARGED; the width is exactly `2B + 1`). -/
theorem k1CoverBody_of_r_one_singleResidue (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 1) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hb3 : (cycleBand3Residues ctx c).card ≤ 1)
    (hcB : 2 * carryB ctx.shell.Q + 1 ≤ c)
    (hd : densePackEndpointDensity ctx)
    (hcl : K1ClusterFloor ctx) :
    (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card := by
  have hW := k1CoverWidth_eq_of_r_eq_one ctx hr
  exact k1CoverBody_of_density_cluster_spacing ctx hd hcl
    (k1StartSpacing_of_singleResidue ctx hc hper hb3 (by omega))

/-! ## 8.  Wiring to the EXACT v19 field shapes -/

/-- **The exact `densePackCoverOffTable` field from an `r ≥ 1` supplier**: the `r = 0`
stratum is closed unconditionally here, so the surface demand genuinely lives only on the
deep (`r ≥ 1`, i.e. `L ≥ 15421`) off-table strata. -/
theorem k1DensePackCoverOffTableField_of_deepStrata
    (hdeep : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card := by
  intro ctx h1 h2 h3 h4 h5
  rcases Nat.eq_zero_or_pos ctx.n24CarryData.r with hr | hr
  · exact k1CoverBody_of_r_eq_zero ctx hr
  · exact hdeep ctx h1 h2 h3 h4 h5 hr

/-- **The exact `densePackCoverOffTable` field from the two named atoms** (+ the density
family), all demanded only under the field's own guards. -/
theorem k1DensePackCoverOffTableField_of_atoms
    (hd : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → densePackEndpointDensity ctx)
    (hcl : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → K1ClusterFloor ctx)
    (hsp : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → K1StartSpacing ctx) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  fun ctx h1 h2 h3 h4 h5 =>
    k1CoverBody_of_density_cluster_spacing ctx
      (hd ctx h1 h2 h3 h4 h5) (hcl ctx h1 h2 h3 h4 h5) (hsp ctx h1 h2 h3 h4 h5)

/-- **The exact `densePackDensityOffTable` field from the endpoint landing** — the sharp
membership form, through `densePackEndpointDensity_iff_endpoints_mem`. -/
theorem k1DensePackDensityOffTableField_of_landing
    (h : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r ∈ proofV4DensePackActualPoints ctx.shell) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → densePackEndpointDensity ctx :=
  fun ctx h1 h2 h3 h4 =>
    (densePackEndpointDensity_iff_endpoints_mem ctx).mpr (h ctx h1 h2 h3 h4)

/-! ## 9.  Honest status inventory -/

/-- The precise per-item status of the K.1 landing after this module. -/
def k1LandingClosureStatus : List String :=
  [ "ANATOMY (proved sharp) — densePackEndpointDensity_iff_endpoints_mem: the v19 density " ++
      "field IS the statement that every genuine start's terminal endpoint k+r lies in " ++
      "proofV4DensePackActualPoints (the actual-point filter = ambient range + the pinned " ++
      "floor ⌊ρ_D·L⌋ ≤ |[m, m+spread] ∩ supportShell|; range derived from one hit).  " ++
      "Genuineness (high excess = LARGE window span) does NOT imply any per-window hit " ++
      "floor — the in-tree definitions support the SDR/landing route, not a floor-from-" ++
      "genuineness coarea shortcut.",
    "CLOSED UNCONDITIONALLY (the r = 0 stratum of densePackCoverOffTable) — " ++
      "k1CoverBody_of_r_eq_zero / k1CoverBody_of_L_le: the demanded width " ++
      "W = (r+1)(L+B+1) − (2L+1) truncates to 0 in ℕ at r = 0 (B + 25 ≤ L), so the cover " ++
      "body holds outright on every L ≤ 15420 shell; k1CoverWidth_eq_zero_iff is sharp " ++
      "(W = 0 ↔ r = 0; at r ≥ 1, W ≥ 2B+1 ≥ 7).  " ++
      "k1DensePackCoverOffTableField_of_deepStrata rebuilds the EXACT v19 field from an " ++
      "r ≥ 1 supplier.",
    "PROVED (multiplicity-one SDR, budget-free) — k1Count_le_actualPoints_of_density: " ++
      "density injects the genuine starts into the actual points via k ↦ k+r (the K.1.3 " ++
      "first-stop owner Φ = (·−r)).  SHARPLY INSUFFICIENT at r ≥ 1: the cover body itself " ++
      "forces ≥ 7 points per start (k1CoverBody_forces_supply) — per-start multiplicity " ++
      "≥ W is genuinely required, confirming the negative wave-19 spacing hunt.",
    "PROVED (the K.1.1 coarea cluster supply, exact) — k1PointBlock_subset_actualPoints / " ++
      "k1PointBlock_card: under density and the per-window cluster floor (hits keep top " ++
      "slack W), the block [k+r+1−W, k+r] of W consecutive positions consists of actual " ++
      "points; the block floor W ≤ k+r is DERIVED from density via (L+2)(2L+1) ≤ 2^L " ++
      "(k1_poly_le_two_pow, L ≥ 28).",
    "PROVED (the K.1 landing) — k1CoverBody_of_density_cluster_spacing: density + " ++
      "K1ClusterFloor + K1StartSpacing prove the EXACT v19 cover body (disjoint per-start " ++
      "blocks via Finset.card_biUnion) — the honest ℕ transcription of the manuscript " ++
      "K.1.3′ marginal/Hall SDR (tex 4732-4752) at point-multiplicity W.",
    "DISCHARGED (the spacing atom, on single-band-3-residue cycles) — " ++
      "k1StartSpacing_of_singleResidue: c-periodicity + |cycleBand3Residues| ≤ 1 (the " ++
      "b₃ = 1 rows of dscPairTable) confine all genuine starts to ONE residue class mod c, " ++
      "so distinct starts are c-spaced; W ≤ c closes it.  At r = 1 the width is EXACTLY " ++
      "2·carryB Q + 1 (k1CoverWidth_eq_of_r_eq_one), giving the per-pair regime " ++
      "2B + 1 ≤ c (k1CoverBody_of_r_one_singleResidue).  At r ≥ 2 the width grows ≈ rL " ++
      "and outruns every fixed table period — that stratum stays with the atoms.",
    "EXTRACTED (the density field position constraint) — k1Density_endpoint_band / " ++
      "k1DensityField_position_constraint: density forces every genuine endpoint into the " ++
      "band X − spread < k + r ≤ 2X (the off-pin analogue of " ++
      "band3_density_forces_subshell); vacuous stratum closed " ++
      "(densePackEndpointDensity_of_emptyStarts).",
    "NAMED REMAINDER (two atoms, jointly inhabited on all r = 0 shells — " ++
      "k1ClusterFloor_of_r_eq_zero / k1StartSpacing_of_r_eq_zero) — (i) K1ClusterFloor: " ++
      "the per-window hit-cluster floor (hits sit in the bottom spread+1−W positions of " ++
      "each genuine endpoint window) — the placement content of the manuscript per-start " ++
      "ρ_D·L owned-hit floor that the bare cardinality floor does not pin down; " ++
      "(ii) K1StartSpacing: W-spacing of distinct genuine starts — open off the " ++
      "single-residue cycles.  The density field itself (densePackEndpointDensity on the " ++
      "b₃ > 0 off-table data) remains the upstream open demand.",
    "ρ_D NOTE (Q-dependence) — the actual-point filter is the PINNED floor ⌊(1/4)L⌋; the " ++
      "Q-correct rhoDQ floor is smaller (proofV4DensePackMinHitsRhoDQ_le_pinned), so the " ++
      "Q-correct density densePackEndpointDensityRhoDQ (projection " ++
      "densePackEndpointDensityRhoDQ_of_pinned) does NOT feed this landing; only the " ++
      "pinned density lands in proofV4DensePackActualPoints." ]

theorem k1LandingClosureStatus_nonempty : k1LandingClosureStatus ≠ [] := by
  simp [k1LandingClosureStatus]

/-! ## 10.  Axiom-cleanliness audit -/

#print axioms k1CoverWidth_eq_zero_of_r_eq_zero
#print axioms k1CoverWidth_lower_of_r_ge_one
#print axioms k1CoverWidth_eq_of_r_eq_one
#print axioms k1CoverWidth_ge_seven_of_r_ge_one
#print axioms k1CoverWidth_eq_zero_iff
#print axioms k1CoverBody_of_r_eq_zero
#print axioms k1CoverBody_of_L_le
#print axioms densePackEndpointDensity_iff_endpoints_mem
#print axioms k1Density_endpoint_band
#print axioms k1DensityField_position_constraint
#print axioms densePackEndpointDensity_of_emptyStarts
#print axioms k1Count_le_actualPoints_of_density
#print axioms k1CoverBody_forces_supply
#print axioms k1_poly_le_two_pow
#print axioms k1CoverWidth_le_endpoint_of_density
#print axioms k1ClusterFloor_of_r_eq_zero
#print axioms k1StartSpacing_of_r_eq_zero
#print axioms k1PointBlock_card
#print axioms k1PointBlock_subset_actualPoints
#print axioms k1PointBlock_disjoint
#print axioms k1CoverBody_of_density_cluster_spacing
#print axioms k1StartSpacing_of_singleResidue
#print axioms k1CoverBody_of_r_one_singleResidue
#print axioms k1DensePackCoverOffTableField_of_deepStrata
#print axioms k1DensePackCoverOffTableField_of_atoms
#print axioms k1DensePackDensityOffTableField_of_landing
#print axioms k1LandingClosureStatus_nonempty

end

end Erdos260
