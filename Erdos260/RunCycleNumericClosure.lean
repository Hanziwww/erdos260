import Erdos260.Erdos260DatumCapstone

/-!
# Erdős 260 — Run / class-5 cycle-numeric closure: band-1 datum tables, the heavy
# band-4 sliding-window mass bound, and the strictly smaller settlement successor

The Run residual `RunNumericSettlementHyp` (`RunNumericSettlement.lean`) demands, on
`r ≥ 1` shells only, a period `c` with the FULL band-`{1,4}` cycle-density numeric
`c0 · (#class5CycleBand · ⌈W/c⌉) · runDyadicMult ≤ (c⋆ξ/12) · W`.  This module splits
the class-5 fibre along its two routing branches (`mem_class5Fibre_iff` /
`class5Fibre_band_pin`):

* the **band-1 branch** (`canonGap q K_k = 1`, i.e. `q < 2·K_k`) is counted by the
  band-1-ONLY cycle density `#class5Band1CycleBand · ⌈W/c⌉`
  (`class5Band1Fibre_card_le_cycleDensity`) — strictly sharper than the band-`{1,4}`
  count whenever the cycle carries band-4 residues;
* the **heavy band-4 branch** carries the gap floor `130L + 64 ≤ 64·gW(k)`, so the
  sliding-window telescoping engine (`slidingWindow_card_mul_le_span`,
  `ReturnClass4CycleClosure.lean`) bounds its population by the hit-position span:
  `#class5HeavyFibre · (130L+64) ≤ (r+1) · 64 · (a(i+W+r) − a(i))`
  (`class5HeavyFibre_card_mul_le_span`) — UNCONDITIONAL, no orbit hypothesis.

Total: `#fibre₅ ≤ #class5Band1CycleBand · ⌈W/c⌉ + #class5HeavyFibre`
(`class5Fibre_card_le_band1_add_heavy`).  Feeding the numeric through the exact
rounding lemmas (`class5HalfDensityRounding`, the real form of
`towerHalfDensity_rounding`; `class5HeavySpanRounding`) splits the Section 26 budget
`c⋆ξ/12 = c⋆ξ/24 + c⋆ξ/24` into ONE half-density band-1 scalar and ONE heavy-span
scalar per context (`runNumericIneq_of_band1_heavy_counted`).

## Datum enumeration (odd `q < 64`)

The divisor pin `(2K₀+1) ∣ q` (`class0_datum_dvd`, from `class1SlopeDatum_H_dvd`)
together with `2K₀ < q` confines the orbit datum on odd `q < 64` to EXACTLY sixty
pairs (`datum_low_window_pairs` / `datum_mid_window_pairs` / `datum_upper_window_pairs`
/ `datum_top_window_pairs`).  Each pair's recurrent cycle is computed mechanically
(`slopeOrbit_step_eval` tables, no `Nat.log` evaluation):

* **6 band-`{1,4}`-free pairs** — `(3,1), (21,3), (51,1), (51,8), (63,1), (63,4)` —
  close OUTRIGHT (`runNumericIneq_of_datum_*` via `runNumericIneq_of_cycle_band_free`;
  `Class5CycleNumericCloses` versions feed the settlement hypothesis with count `0`).
* **51 pairs with band-1 cycle elements** — per-pair band-1 counts `b1` are certified
  (`runCycle_*` tables) and the per-pair threshold
  `2·(b1 · c0 · runDyadicMult) ≤ (c⋆ξ/24)·c` (+ the heavy-span scalar) closes the
  context (`class5BandHeavy_of_datum_*`).
* **3 band-4-only pairs** — `(15,1), (15,2), (63,10)` — have `b1 = 0`: the band-1
  scalar holds for FREE and only the heavy-span scalar remains.

## The strictly smaller successor

`Class5BandHeavyNumericCloses ctx` (period + `c ≤ W` + the two scalars) implies the
capstone inequality (`runNumericIneq_of_bandHeavyCloses`).  The successor residual

`RunCycleNumericSettlementHyp := ∀ ctx, 1 ≤ r → Class5BandHeavyNumericCloses ctx ∨
Class5CycleNumericCloses ctx`

is implied by `RunNumericSettlementHyp` (`runCycleNumericSettlementHyp_of_settlement`)
and still settles the full capstone field verbatim (`runCycleNumericField_settled`,
mirroring `runNumericField_settled`) and the `RunClass5SplitBoundary` surface
(`runCycleSplitBoundary_settled`, mirroring `runSplitBoundary_settled` through
`runSplitOfNumeric`).  On band-4-carrying band-1-free cycles (`b1 = 0 < b4`, e.g. the
`(15,1)` family where the old full count is vacuous `b = c`) the new left disjunct is
strictly weaker than the old numeric — the heavy mass is paid by the PROVED
sliding-window span bound instead of the unprovable cycle count.

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  Band-window helpers -/

/-- A numerator below the band-1 window (`2K ≤ q`) has `canonGap ≠ 1` — the
contrapositive of the E.13 band-1 characterization `canonGap_eq_one_iff`. -/
theorem canonGap_ne_one_of_two_mul_le {q K : ℕ} (hK : 1 ≤ K) (h2 : 2 * K ≤ q) :
    canonGap q K ≠ 1 := by
  intro h1
  have := (canonGap_eq_one_iff hK).mp h1
  omega

/-! ## Part 2.  The band-1 cycle band and the heavy sub-fibre -/

/-- **The band-1-only cycle band**: the residue indices `j ∈ [1, c]` of one orbit
period whose band is `1` (the `run` window `q < 2K`) — the band-4 residues are NOT
counted here (they are charged to the heavy sliding-window mass instead). -/
def class5Band1CycleBand (ctx : ActualFailureContext) (c : ℕ) : Finset ℕ :=
  (Finset.Icc 1 c).filter (fun j =>
    canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 1)

theorem mem_class5Band1CycleBand (ctx : ActualFailureContext) {c j : ℕ} :
    j ∈ class5Band1CycleBand ctx c
      ↔ (1 ≤ j ∧ j ≤ c)
        ∧ canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 1 := by
  unfold class5Band1CycleBand
  rw [Finset.mem_filter, Finset.mem_Icc]

/-- Datum substitution for the band-1 cycle band (the per-pair tables are pure
`(q, K₀)` statements). -/
theorem class5Band1CycleBand_congr (ctx : ActualFailureContext) {qv Kv : ℕ}
    (hq : (class1SlopeDatum ctx).q = qv) (hK : (class1SlopeDatum ctx).K₀ = Kv)
    (c : ℕ) :
    class5Band1CycleBand ctx c
      = (Finset.Icc 1 c).filter (fun j => canonGap qv (slopeOrbit qv Kv j) = 1) := by
  unfold class5Band1CycleBand
  rw [hq, hK]

/-- **The heavy class-5 sub-fibre**: the class-5 starts carrying the band-4 heavy gap
floor `130L + 64 ≤ 64·gW(k)` (the `cnlTail` local-spike branch of
`mem_class5Fibre_iff`). -/
def class5HeavyFibre (ctx : ActualFailureContext) : Finset ℕ :=
  (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
    (fun k => 130 * shellLadderDepth ctx + 64
      ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r)

theorem mem_class5HeavyFibre (ctx : ActualFailureContext) {k : ℕ} :
    k ∈ class5HeavyFibre ctx
      ↔ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5
        ∧ 130 * shellLadderDepth ctx + 64
            ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r := by
  unfold class5HeavyFibre
  rw [Finset.mem_filter]

/-- The heavy gap floor consumed by the sliding-window engine. -/
def runHeavyFloor (ctx : ActualFailureContext) : ℕ :=
  130 * shellLadderDepth ctx + 64

theorem runHeavyFloor_pos (ctx : ActualFailureContext) : 1 ≤ runHeavyFloor ctx := by
  unfold runHeavyFloor
  omega

/-- The `64`-scaled hit-position span budget of the shell window, including the top
escape gaps — exactly the right side the sliding-window engine telescopes against. -/
def runHeavySpanBudget (ctx : ActualFailureContext) : ℕ :=
  (ctx.n24CarryData.r + 1)
    * (64 * (ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
        - ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)))

/-- **The heavy-span scalar numeric** — the heavy half of the split Section 26 budget:
`c0 · runDyadicMult · spanBudget ≤ (c⋆ξ/24) · W · (130L+64)`. -/
def RunHeavyNumeric (ctx : ActualFailureContext) : Prop :=
  erdos260Constants.c0 * runDyadicMult ctx * ((runHeavySpanBudget ctx : ℕ) : ℝ)
    ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24
      * ((supportShell ctx.d ctx.X).card : ℝ) * ((runHeavyFloor ctx : ℕ) : ℝ)

/-! ## Part 3.  The two count engines

The band-1 branch is counted by the cycle-density injection (the band-1-only sharpening
of `class5Fibre_card_le_cycleDensity`); the heavy branch by the sliding-window
telescoping engine. -/

private theorem run_window_residue_block_inj {c F k₁ k₂ : ℕ} (hc : 1 ≤ c)
    (h₁1 : 1 ≤ k₁) (h₁F : F ≤ k₁) (h₂F : F ≤ k₂) (hle : k₁ ≤ k₂)
    (hmod : (k₁ - 1) % c = (k₂ - 1) % c)
    (hdiv : (k₁ - F) / c = (k₂ - F) / c) :
    k₁ = k₂ := by
  have hdvd : c ∣ (k₂ - 1) - (k₁ - 1) := (Nat.modEq_iff_dvd' (by omega)).mp hmod
  obtain ⟨t, ht⟩ := hdvd
  have hk2F : k₂ - F = k₁ - F + c * t := by omega
  rw [hk2F, Nat.add_mul_div_left _ _ (show 0 < c by omega)] at hdiv
  have ht0 : t = 0 := by omega
  subst ht0
  rw [Nat.mul_zero] at ht
  omega

/-- **The band-1 cycle-density count bound**: for any orbit period `c` valid from index
`1`, the band-1 part of the class-5 fibre injects into (band-1 cycle residues) ×
(window blocks): `#fibre₅^{band-1} ≤ #class5Band1CycleBand · ⌈W/c⌉`. -/
theorem class5Band1Fibre_card_le_cycleDensity (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
        (fun k => canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 1)).card
      ≤ (class5Band1CycleBand ctx c).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) := by
  classical
  have hW1 : 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
    le_trans (Nat.le_add_left 1 ctx.n24CarryData.r) (cnlMulti_r_add_one_le_width ctx)
  have hmaps : ∀ k ∈ (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
      (fun k => canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 1),
      ((k - 1) % c + 1,
        (k - ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X) / c)
        ∈ (class5Band1CycleBand ctx c) ×ˢ
            Finset.range
              (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) := by
    intro k hk
    obtain ⟨hk5, hband⟩ := Finset.mem_filter.mp hk
    have hk1 : 1 ≤ k := n24_starts_pos ctx ((mem_class5Fibre_iff ctx k).mp hk5).1
    have hwin := class5Fibre_mem_window ctx hk5
    rw [Finset.mem_product]
    constructor
    · rw [mem_class5Band1CycleBand]
      have hmodlt : (k - 1) % c < c := Nat.mod_lt _ (by omega)
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have heq := slopeOrbit_eq_residue hc hper hk1
      rw [← heq]
      exact hband
    · rw [Finset.mem_range]
      have hdle : (k - ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X) / c
          ≤ ((supportShell ctx.shell.d ctx.shell.X).card - 1) / c :=
        Nat.div_le_div_right (by omega)
      have hceil : ((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c
          = ((supportShell ctx.shell.d ctx.shell.X).card - 1) / c + 1 := by
        have he : (supportShell ctx.shell.d ctx.shell.X).card + c - 1
            = ((supportShell ctx.shell.d ctx.shell.X).card - 1) + c := by omega
        rw [he, Nat.add_div_right _ (by omega)]
      omega
  have hinj : Set.InjOn (fun k : ℕ =>
      ((k - 1) % c + 1,
        (k - ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X) / c))
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
        (fun k => canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 1)) := by
    intro k₁ hk₁ k₂ hk₂ heq
    have hk₁' := Finset.mem_coe.mp hk₁
    have hk₂' := Finset.mem_coe.mp hk₂
    obtain ⟨h1mem, _⟩ := Finset.mem_filter.mp hk₁'
    obtain ⟨h2mem, _⟩ := Finset.mem_filter.mp hk₂'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hmod1, hdiv⟩ := heq
    have hmod : (k₁ - 1) % c = (k₂ - 1) % c := by omega
    have h1F := (class5Fibre_mem_window ctx h1mem).1
    have h2F := (class5Fibre_mem_window ctx h2mem).1
    have h11 : 1 ≤ k₁ := n24_starts_pos ctx ((mem_class5Fibre_iff ctx k₁).mp h1mem).1
    have h21 : 1 ≤ k₂ := n24_starts_pos ctx ((mem_class5Fibre_iff ctx k₂).mp h2mem).1
    rcases le_total k₁ k₂ with hle | hle
    · exact run_window_residue_block_inj hc h11 h1F h2F hle hmod hdiv
    · exact (run_window_residue_block_inj hc h21 h2F h1F hle hmod.symm hdiv.symm).symm
  calc ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
        (fun k => canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 1)).card
      ≤ ((class5Band1CycleBand ctx c) ×ˢ
          Finset.range
            (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (class5Band1CycleBand ctx c).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) := by
        rw [Finset.card_product, Finset.card_range]

/-- **The heavy-mass sliding-window bound** — UNCONDITIONAL, no orbit hypothesis:
`#class5HeavyFibre · (130L+64) ≤ (r+1) · 64 · (a(i+W+r) − a(i))`.  Heavy class-5
starts realize the gap floor `130L+64 ≤ 64·(a(k+r+1) − a(k))`, and floor-windows at
starts `≥ r+1` apart are disjoint, so the floors telescope against the total
hit-position span (`slidingWindow_card_mul_le_span`). -/
theorem class5HeavyFibre_card_mul_le_span (ctx : ActualFailureContext) :
    (class5HeavyFibre ctx).card * runHeavyFloor ctx ≤ runHeavySpanBudget ctx := by
  have hmono : Monotone ctx.n24CarryData.a := ctx.n24CarryData.carry.hits.strict.monotone
  have hmono64 : Monotone (fun j => 64 * ctx.n24CarryData.a j) :=
    fun x y hxy => Nat.mul_le_mul_left 64 (hmono hxy)
  have hsub : ∀ k ∈ class5HeavyFibre ctx,
      ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X ≤ k
        ∧ k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card :=
    fun k hk => class5Fibre_mem_window ctx ((mem_class5HeavyFibre ctx).mp hk).1
  have hfloor : ∀ k ∈ class5HeavyFibre ctx,
      runHeavyFloor ctx
        ≤ 64 * ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1)
          - 64 * ctx.n24CarryData.a k := by
    intro k hk
    have hfl := ((mem_class5HeavyFibre ctx).mp hk).2
    rw [ctx.n24CarryData.carry.hits.gapWindow_hitGap_eq] at hfl
    have hm : ctx.n24CarryData.a k ≤ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) :=
      hmono (by omega)
    unfold runHeavyFloor
    omega
  have hmaster : (class5HeavyFibre ctx).card * runHeavyFloor ctx
      ≤ (ctx.n24CarryData.r + 1)
        * (64 * ctx.n24CarryData.a
              (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
                + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          - 64 * ctx.n24CarryData.a
              (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)) :=
    slidingWindow_card_mul_le_span (fun j => 64 * ctx.n24CarryData.a j) hmono64 hsub hfloor
  have hfac : 64 * ctx.n24CarryData.a
        (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
      - 64 * ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
      = 64 * (ctx.n24CarryData.a
            (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          - ctx.n24CarryData.a
            (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)) := by
    have h := hmono (show ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        ≤ ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r by omega)
    omega
  rw [hfac] at hmaster
  unfold runHeavySpanBudget
  exact hmaster

/-- **The total class-5 count split**: every class-5 start reads band 1 on the orbit or
carries the heavy gap floor (`class5Fibre_band_pin`), so
`#fibre₅ ≤ #class5Band1CycleBand · ⌈W/c⌉ + #class5HeavyFibre`. -/
theorem class5Fibre_card_le_band1_add_heavy (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card
      ≤ (class5Band1CycleBand ctx c).card
          * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c)
        + (class5HeavyFibre ctx).card := by
  classical
  have hsub : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5
      ⊆ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
          (fun k => canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 1))
        ∪ class5HeavyFibre ctx := by
    intro k hk
    rcases class5Fibre_band_pin ctx hk with h1 | h4heavy
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk, h1⟩)
    · exact Finset.mem_union_right _ ((mem_class5HeavyFibre ctx).mpr ⟨hk, h4heavy.2⟩)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card
      ≤ (((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
          (fun k => canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 1))
        ∪ class5HeavyFibre ctx).card := Finset.card_le_card hsub
    _ ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).filter
          (fun k => canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 1)).card
        + (class5HeavyFibre ctx).card := Finset.card_union_le _ _
    _ ≤ (class5Band1CycleBand ctx c).card
          * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c)
        + (class5HeavyFibre ctx).card :=
        Nat.add_le_add_right (class5Band1Fibre_card_le_cycleDensity ctx hc hper) _

/-- The split count bound at SOME period `c ≤ q` — unconditional existence via
`class1Fibre_orbit_period_exists`. -/
theorem class5Fibre_card_le_band1_add_heavy_exists (ctx : ActualFailureContext) :
    ∃ c : ℕ, 1 ≤ c ∧ c ≤ (class1SlopeDatum ctx).q ∧
      (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card
        ≤ (class5Band1CycleBand ctx c).card
            * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c)
          + (class5HeavyFibre ctx).card := by
  obtain ⟨c, hc1, hcq, hper⟩ := class1Fibre_orbit_period_exists ctx
  exact ⟨c, hc1, hcq, class5Fibre_card_le_band1_add_heavy ctx hc1 hper⟩

/-! ## Part 4.  The exact roundings and the split-budget numeric engine -/

/-- **The exact rounding of the band-1 half-density scalar** (the real form of
`towerHalfDensity_rounding`): `2·(b·C·M) ≤ T·c` with the window at least one period
wide (`c ≤ W`) discharges `C·(b·⌈W/c⌉)·M ≤ T·W` — the ceiling loses at most one
period, absorbed by the factor-2 slack. -/
theorem class5HalfDensityRounding {C M T : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    {b c W : ℕ} (hc : 1 ≤ c) (hcW : c ≤ W)
    (hkey : 2 * ((b : ℝ) * (C * M)) ≤ T * (c : ℝ)) :
    C * ((b * ((W + c - 1) / c) : ℕ) : ℝ) * M ≤ T * (W : ℝ) := by
  have hWc : (b * ((W + c - 1) / c)) * c ≤ b * (2 * W) := by
    have hdivle : ((W + c - 1) / c) * c ≤ W + c - 1 := Nat.div_mul_le_self _ _
    have h2W : W + c - 1 ≤ 2 * W := by omega
    calc (b * ((W + c - 1) / c)) * c = b * (((W + c - 1) / c) * c) := by ring
      _ ≤ b * (W + c - 1) := Nat.mul_le_mul (Nat.le_refl b) hdivle
      _ ≤ b * (2 * W) := Nat.mul_le_mul (Nat.le_refl b) h2W
  have hWcR : ((b * ((W + c - 1) / c) : ℕ) : ℝ) * (c : ℝ) ≤ (b : ℝ) * (2 * (W : ℝ)) := by
    exact_mod_cast hWc
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hWnn : (0 : ℝ) ≤ (W : ℝ) := Nat.cast_nonneg _
  have hCM : (0 : ℝ) ≤ C * M := mul_nonneg hC hM
  have hchain : (C * ((b * ((W + c - 1) / c) : ℕ) : ℝ) * M) * (c : ℝ)
      ≤ (T * (W : ℝ)) * (c : ℝ) := by
    calc (C * ((b * ((W + c - 1) / c) : ℕ) : ℝ) * M) * (c : ℝ)
        = (C * M) * (((b * ((W + c - 1) / c) : ℕ) : ℝ) * (c : ℝ)) := by ring
      _ ≤ (C * M) * ((b : ℝ) * (2 * (W : ℝ))) := mul_le_mul_of_nonneg_left hWcR hCM
      _ = (2 * ((b : ℝ) * (C * M))) * (W : ℝ) := by ring
      _ ≤ (T * (c : ℝ)) * (W : ℝ) := mul_le_mul_of_nonneg_right hkey hWnn
      _ = (T * (W : ℝ)) * (c : ℝ) := by ring
  exact le_of_mul_le_mul_right hchain hcpos

/-- **The heavy-span rounding**: the proved mass bound `Nh·H ≤ S` plus the heavy-span
scalar `C·M·S ≤ T·W·H` discharge `C·Nh·M ≤ T·W` (divide by the positive floor `H`). -/
theorem class5HeavySpanRounding {C M T : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    {Nh H S W : ℕ} (hH : 1 ≤ H)
    (hmass : Nh * H ≤ S)
    (hkey : C * M * (S : ℝ) ≤ T * (W : ℝ) * (H : ℝ)) :
    C * (Nh : ℝ) * M ≤ T * (W : ℝ) := by
  have hmassR : (Nh : ℝ) * (H : ℝ) ≤ (S : ℝ) := by exact_mod_cast hmass
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hCM : (0 : ℝ) ≤ C * M := mul_nonneg hC hM
  have hchain : (C * (Nh : ℝ) * M) * (H : ℝ) ≤ (T * (W : ℝ)) * (H : ℝ) := by
    calc (C * (Nh : ℝ) * M) * (H : ℝ) = (C * M) * ((Nh : ℝ) * (H : ℝ)) := by ring
      _ ≤ (C * M) * (S : ℝ) := mul_le_mul_of_nonneg_left hmassR hCM
      _ ≤ T * (W : ℝ) * (H : ℝ) := hkey
      _ = (T * (W : ℝ)) * (H : ℝ) := by ring
  exact le_of_mul_le_mul_right hchain hHpos

/-- **The split-budget numeric engine**: a period `c ≤ W` with a certified band-1
cycle count `≤ b1`, the band-1 half-density scalar at budget `c⋆ξ/24`, and the
heavy-span scalar at budget `c⋆ξ/24` settle the capstone inequality — the two halves
re-assemble the full Section 26 budget `c⋆ξ/12`. -/
theorem runNumericIneq_of_band1_heavy_counted (ctx : ActualFailureContext) {c b1 : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hcW : c ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hcount : (class5Band1CycleBand ctx c).card ≤ b1)
    (hb1 : 2 * ((b1 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (c : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    RunNumericIneq ctx := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card
      ≤ b1 * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c)
        + (class5HeavyFibre ctx).card :=
    le_trans (class5Fibre_card_le_band1_add_heavy ctx hc hper)
      (Nat.add_le_add_right
        (Nat.mul_le_mul hcount (Nat.le_refl _)) _)
  refine class5_numeric_of_card_le ctx hcard ?_
  have hpart1 : erdos260Constants.c0
      * ((b1 * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) : ℕ) : ℝ)
      * runDyadicMult ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24
        * ((supportShell ctx.shell.d ctx.shell.X).card : ℝ) :=
    class5HalfDensityRounding erdos260Constants.c0_pos.le (runDyadicMult_nonneg ctx)
      hc hcW hb1
  have hheavy' : erdos260Constants.c0 * runDyadicMult ctx
      * ((runHeavySpanBudget ctx : ℕ) : ℝ)
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24
        * ((supportShell ctx.d ctx.X).card : ℝ) * ((runHeavyFloor ctx : ℕ) : ℝ) := hheavy
  have hpart2 : erdos260Constants.c0 * ((class5HeavyFibre ctx).card : ℝ)
      * runDyadicMult ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24
        * ((supportShell ctx.d ctx.X).card : ℝ) :=
    class5HeavySpanRounding erdos260Constants.c0_pos.le (runDyadicMult_nonneg ctx)
      (runHeavyFloor_pos ctx) (class5HeavyFibre_card_mul_le_span ctx) hheavy'
  rw [Nat.cast_add]
  calc erdos260Constants.c0
      * (((b1 * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) : ℕ) : ℝ)
        + ((class5HeavyFibre ctx).card : ℝ))
      * runDyadicMult ctx
      = erdos260Constants.c0
          * ((b1 * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) : ℕ) : ℝ)
          * runDyadicMult ctx
        + erdos260Constants.c0 * ((class5HeavyFibre ctx).card : ℝ)
          * runDyadicMult ctx := by ring
    _ ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24
          * ((supportShell ctx.d ctx.X).card : ℝ)
        + erdos260Constants.cStar * erdos260Constants.ξ / 24
          * ((supportShell ctx.d ctx.X).card : ℝ) := add_le_add hpart1 hpart2
    _ = erdos260Constants.cStar * erdos260Constants.ξ / 12
          * ((supportShell ctx.d ctx.X).card : ℝ) := by ring

/-- A band-`{1,4}`-free period yields `Class5CycleNumericCloses` outright: the
band-`{1,4}` cycle band is EMPTY, so the demanded numeric is `0 ≤ nonneg`. -/
theorem class5CycleNumericCloses_of_cycle_band_free (ctx : ActualFailureContext)
    {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 1
        ∧ canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 4) :
    Class5CycleNumericCloses ctx := by
  refine ⟨c, hc, hper, ?_⟩
  have hempty : class5CycleBand ctx c = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro j hj
    rw [mem_class5CycleBand] at hj
    obtain ⟨⟨hj1, hjc⟩, hor⟩ := hj
    obtain ⟨hne1, hne4⟩ := hband j hj1 hjc
    rcases hor with h | h
    · exact hne1 h
    · exact hne4 h
  rw [hempty]
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul]
  exact mul_nonneg
    (div_nonneg
      (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
      (by norm_num))
    (Nat.cast_nonneg _)

/-- The band-1 scalar holds for FREE at count `0` (the band-4-only pairs). -/
theorem run_b1_zero_scalar (x : ℝ) (c : ℕ) :
    2 * (((0 : ℕ) : ℝ) * x)
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (c : ℝ) := by
  have h0 : (0 : ℝ)
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (c : ℝ) :=
    mul_nonneg
      (div_nonneg
        (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
        (by norm_num))
      (Nat.cast_nonneg _)
  simpa using h0

/-! ## Part 5.  The per-context closure condition and the settlement successor -/

/-- **The split-budget per-context closure condition** — the successor of
`Class5CycleNumericCloses`: some orbit period `c ≤ W` whose band-1-ONLY cycle count
passes the half-density scalar at budget `c⋆ξ/24`, plus the heavy-span scalar at
budget `c⋆ξ/24`.  The band-4 cycle residues are NOT counted: their mass is paid by
the PROVED sliding-window bound `class5HeavyFibre_card_mul_le_span`. -/
def Class5BandHeavyNumericCloses (ctx : ActualFailureContext) : Prop :=
  ∃ c : ℕ, 1 ≤ c
    ∧ (∀ m, 1 ≤ m →
        slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
          = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    ∧ c ≤ (supportShell ctx.shell.d ctx.shell.X).card
    ∧ 2 * (((class5Band1CycleBand ctx c).card : ℝ)
          * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (c : ℝ)
    ∧ RunHeavyNumeric ctx

/-- `Class5BandHeavyNumericCloses ctx` settles the capstone inequality at `ctx`. -/
theorem runNumericIneq_of_bandHeavyCloses (ctx : ActualFailureContext)
    (h : Class5BandHeavyNumericCloses ctx) : RunNumericIneq ctx := by
  obtain ⟨c, hc, hper, hcW, hb1, hheavy⟩ := h
  exact runNumericIneq_of_band1_heavy_counted ctx hc hper hcW (Nat.le_refl _) hb1 hheavy

/-- Build the per-context closure from a CERTIFIED band-1 count bound (the per-pair
tables) plus the two scalars. -/
theorem class5BandHeavyCloses_of_period_count (ctx : ActualFailureContext) {c b1 : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hcW : c ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hcount : (class5Band1CycleBand ctx c).card ≤ b1)
    (hb1 : 2 * ((b1 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (c : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine ⟨c, hc, hper, hcW, ?_, hheavy⟩
  have hmono : ((class5Band1CycleBand ctx c).card : ℝ) ≤ (b1 : ℝ) := by
    exact_mod_cast hcount
  have hX : (0 : ℝ) ≤ erdos260Constants.c0 * runDyadicMult ctx :=
    mul_nonneg erdos260Constants.c0_pos.le (runDyadicMult_nonneg ctx)
  have hstep := mul_le_mul_of_nonneg_right hmono hX
  linarith

/-- **The settlement successor** — strictly smaller than `RunNumericSettlementHyp`:
each `r ≥ 1` context may be closed EITHER by the new split-budget condition (band-1
cycle count + heavy sliding-window mass) OR by the original full cycle-density
numeric. -/
def RunCycleNumericSettlementHyp : Prop :=
  ∀ ctx : ActualFailureContext, 1 ≤ ctx.n24CarryData.r →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx

/-- The original settlement hypothesis implies the successor (the weakening
witness). -/
theorem runCycleNumericSettlementHyp_of_settlement
    (h : RunNumericSettlementHyp) : RunCycleNumericSettlementHyp :=
  fun ctx hr => Or.inr (h ctx hr)

/-- **The full `runNumeric` field, settled from the successor** — verbatim the
`runNumeric` field type of `Erdos260CycleResidual`, mirroring
`runNumericField_settled`: `r = 0` is discharged unconditionally, `r ≥ 1` by either
disjunct. -/
theorem runCycleNumericField_settled (h : RunCycleNumericSettlementHyp) :
    ∀ ctx : ActualFailureContext,
      erdos260Constants.c0
          * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
          * runDyadicMult ctx
        ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
          * ((supportShell ctx.d ctx.X).card : ℝ) := by
  intro ctx
  rcases Nat.eq_zero_or_pos ctx.n24CarryData.r with hr | hr
  · exact runNumericIneq_of_r_eq_zero ctx hr
  · rcases h ctx hr with hcl | hcl
    · exact runNumericIneq_of_bandHeavyCloses ctx hcl
    · exact runNumericIneq_of_cycleNumericCloses ctx hcl

/-- **The capstone `RunClass5SplitBoundary` surface, settled from the successor** —
mirroring `runSplitBoundary_settled` through `runSplitOfNumeric`. -/
def runCycleSplitBoundary_settled (h : RunCycleNumericSettlementHyp) :
    ∀ ctx : ActualFailureContext, RunClass5SplitBoundary ctx :=
  runSplitOfNumeric (runCycleNumericField_settled h)

/-! ## Part 6.  The datum enumeration on odd `q < 64`

The divisor pin `(2K₀+1) ∣ q` with `1 ≤ K₀`, `2K₀ < q`, `q` odd confines the datum
to sixty explicit pairs across four windows; the mid (`17 ≤ q < 32`) and upper
(`32 ≤ q < 48`) windows are the proved `datum_mid_window_pairs` /
`datum_upper_window_pairs` of `ChernoffClass0DatumClosure`. -/

/-- The actual datum modulus is at least `3` (odd and `≥ 2`). -/
theorem runDatum_q_ge_three (ctx : ActualFailureContext) :
    3 ≤ (class1SlopeDatum ctx).q := by
  obtain ⟨t, ht⟩ := (class1SlopeDatum ctx).hq_odd
  have h2 := (class1SlopeDatum ctx).hq2
  omega

/-- **The low-window datum enumeration**: on `3 ≤ q < 16` the divisor pin admits
exactly ten pairs. -/
theorem datum_low_window_pairs {q K : ℕ} (hq_odd : Odd q) (hK1 : 1 ≤ K)
    (h2K : 2 * K < q) (hdvd : 2 * K + 1 ∣ q) (h3 : 3 ≤ q) (h16 : q < 16) :
    (q = 3 ∧ K = 1) ∨ (q = 5 ∧ K = 2) ∨ (q = 7 ∧ K = 3) ∨ (q = 9 ∧ K = 1)
    ∨ (q = 9 ∧ K = 4) ∨ (q = 11 ∧ K = 5) ∨ (q = 13 ∧ K = 6) ∨ (q = 15 ∧ K = 1)
    ∨ (q = 15 ∧ K = 2) ∨ (q = 15 ∧ K = 7) := by
  obtain ⟨s, hs⟩ := hdvd
  obtain ⟨t, ht⟩ := hq_odd
  have hK7 : K ≤ 7 := by omega
  have hq7 : q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 9 ∨ q = 11 ∨ q = 13 ∨ q = 15 := by omega
  rcases hq7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases K <;> ((try ring_nf at hs); first | (norm_num; done) | (exfalso; omega))

/-- **The top-window datum enumeration**: on `48 ≤ q < 64` the divisor pin admits
exactly nineteen pairs. -/
theorem datum_top_window_pairs {q K : ℕ} (hq_odd : Odd q) (hK1 : 1 ≤ K)
    (h2K : 2 * K < q) (hdvd : 2 * K + 1 ∣ q) (h48 : 48 ≤ q) (h64 : q < 64) :
    (q = 49 ∧ K = 3) ∨ (q = 49 ∧ K = 24) ∨ (q = 51 ∧ K = 1) ∨ (q = 51 ∧ K = 8)
    ∨ (q = 51 ∧ K = 25) ∨ (q = 53 ∧ K = 26) ∨ (q = 55 ∧ K = 2) ∨ (q = 55 ∧ K = 5)
    ∨ (q = 55 ∧ K = 27) ∨ (q = 57 ∧ K = 1) ∨ (q = 57 ∧ K = 9) ∨ (q = 57 ∧ K = 28)
    ∨ (q = 59 ∧ K = 29) ∨ (q = 61 ∧ K = 30) ∨ (q = 63 ∧ K = 1) ∨ (q = 63 ∧ K = 3)
    ∨ (q = 63 ∧ K = 4) ∨ (q = 63 ∧ K = 10) ∨ (q = 63 ∧ K = 31) := by
  obtain ⟨s, hs⟩ := hdvd
  obtain ⟨t, ht⟩ := hq_odd
  have hK31 : K ≤ 31 := by omega
  have hq8 : q = 49 ∨ q = 51 ∨ q = 53 ∨ q = 55 ∨ q = 57 ∨ q = 59 ∨ q = 61 ∨ q = 63 := by
    omega
  rcases hq8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases K <;> ((try ring_nf at hs); first | (norm_num; done) | (exfalso; omega))

/-! ## Part 7.  The per-pair orbit tables (mechanical `slopeOrbit_step_eval` chains)

Each cycle is verified step by step through the band bounds (no `Nat.log`
computation); the period is the first return to the index-`1` value; the band-1
count bound is read off the period block by the explicit residue subset. -/

/-- `(q, K₀) = (3, 1)`: period `1`, cycle `1`, bands `2` — band-`{1,4}`-free. -/
private theorem runCycle_3_1 :
    slopeOrbit 3 1 (1 + 1) = slopeOrbit 3 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 →
          canonGap 3 (slopeOrbit 3 1 j) ≠ 1
            ∧ canonGap 3 (slopeOrbit 3 1 j) ≠ 4 := by
  have e0 : slopeOrbit 3 1 0 = 1 := rfl
  have e1 : slopeOrbit 3 1 1 = 1 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 3 1 2 = 1 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 3 1 2 = slopeOrbit 3 1 1
    rw [e2, e1]
  · intro j hj1 hjc
    interval_cases j
    · rw [e1]
      exact ⟨canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num),
        canonGap_ne_four_of_band (Or.inl (by norm_num))⟩

/-- `(q, K₀) = (3, 1)` closes the capstone inequality OUTRIGHT (band-`{1,4}`-free cycle). -/
theorem runNumericIneq_of_datum_3_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 3) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    RunNumericIneq ctx := by
  refine runNumericIneq_of_cycle_band_free ctx (c := 1) (by norm_num) ?_ ?_
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_3_1.1
  · rw [hq, hK]
    exact runCycle_3_1.2

/-- `(q, K₀) = (3, 1)` settles `Class5CycleNumericCloses` unconditionally (count `0`). -/
theorem class5CycleNumericCloses_of_datum_3_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 3) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    Class5CycleNumericCloses ctx := by
  refine class5CycleNumericCloses_of_cycle_band_free ctx (c := 1) (by norm_num) ?_ ?_
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_3_1.1
  · rw [hq, hK]
    exact runCycle_3_1.2

/-- `(q, K₀) = (5, 2)`: period `2`, cycle `3 → 1`, bands `1, 3` — band-1 count `≤ 1`. -/
private theorem runCycle_5_2 :
    slopeOrbit 5 2 (1 + 2) = slopeOrbit 5 2 1
      ∧ ((Finset.Icc 1 2).filter
          (fun j => canonGap 5 (slopeOrbit 5 2 j) = 1)).card ≤ 1 := by
  have e0 : slopeOrbit 5 2 0 = 2 := rfl
  have e1 : slopeOrbit 5 2 1 = 3 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 5 2 2 = 1 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 5 2 3 = 3 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 5 2 3 = slopeOrbit 5 2 1
    rw [e3, e1]
  · have hsub : (Finset.Icc 1 2).filter
        (fun j => canonGap 5 (slopeOrbit 5 2 j) = 1) ⊆ ({1} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · exfalso
        rw [e2] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (5, 2)`: the per-pair threshold — period `2`, band-1
count `1`; the half-density scalar `2·(1·c0·runDyadicMult) ≤ (c⋆ξ/24)·2`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_5_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 5) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (hcW : 2 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((1 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (2 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 2) (b1 := 1)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_5_2.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_5_2.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (7, 3)`: period `2`, cycle `5 → 3`, bands `1, 2` — band-1 count `≤ 1`. -/
private theorem runCycle_7_3 :
    slopeOrbit 7 3 (1 + 2) = slopeOrbit 7 3 1
      ∧ ((Finset.Icc 1 2).filter
          (fun j => canonGap 7 (slopeOrbit 7 3 j) = 1)).card ≤ 1 := by
  have e0 : slopeOrbit 7 3 0 = 3 := rfl
  have e1 : slopeOrbit 7 3 1 = 5 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 7 3 2 = 3 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 7 3 3 = 5 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 7 3 3 = slopeOrbit 7 3 1
    rw [e3, e1]
  · have hsub : (Finset.Icc 1 2).filter
        (fun j => canonGap 7 (slopeOrbit 7 3 j) = 1) ⊆ ({1} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · exfalso
        rw [e2] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (7, 3)`: the per-pair threshold — period `2`, band-1
count `1`; the half-density scalar `2·(1·c0·runDyadicMult) ≤ (c⋆ξ/24)·2`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_7_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 7) (hK : (class1SlopeDatum ctx).K₀ = 3)
    (hcW : 2 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((1 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (2 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 2) (b1 := 1)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_7_3.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_7_3.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (9, 1)`: period `3`, cycle `7 → 5 → 1`, bands `1, 1, 4` — band-1 count `≤ 2`. -/
private theorem runCycle_9_1 :
    slopeOrbit 9 1 (1 + 3) = slopeOrbit 9 1 1
      ∧ ((Finset.Icc 1 3).filter
          (fun j => canonGap 9 (slopeOrbit 9 1 j) = 1)).card ≤ 2 := by
  have e0 : slopeOrbit 9 1 0 = 1 := rfl
  have e1 : slopeOrbit 9 1 1 = 7 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 9 1 2 = 5 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 9 1 3 = 1 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 9 1 4 = 7 :=
    slopeOrbit_step_eval 3 3 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 9 1 4 = slopeOrbit 9 1 1
    rw [e4, e1]
  · have hsub : (Finset.Icc 1 3).filter
        (fun j => canonGap 9 (slopeOrbit 9 1 j) = 1) ⊆ ({1, 2} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · exfalso
        rw [e3] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (9, 1)`: the per-pair threshold — period `3`, band-1
count `2`; the half-density scalar `2·(2·c0·runDyadicMult) ≤ (c⋆ξ/24)·3`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_9_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hcW : 3 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((2 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (3 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 3) (b1 := 2)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_9_1.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_9_1.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (9, 4)`: period `3`, cycle `7 → 5 → 1`, bands `1, 1, 4` — band-1 count `≤ 2`. -/
private theorem runCycle_9_4 :
    slopeOrbit 9 4 (1 + 3) = slopeOrbit 9 4 1
      ∧ ((Finset.Icc 1 3).filter
          (fun j => canonGap 9 (slopeOrbit 9 4 j) = 1)).card ≤ 2 := by
  have e0 : slopeOrbit 9 4 0 = 4 := rfl
  have e1 : slopeOrbit 9 4 1 = 7 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 9 4 2 = 5 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 9 4 3 = 1 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 9 4 4 = 7 :=
    slopeOrbit_step_eval 3 3 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 9 4 4 = slopeOrbit 9 4 1
    rw [e4, e1]
  · have hsub : (Finset.Icc 1 3).filter
        (fun j => canonGap 9 (slopeOrbit 9 4 j) = 1) ⊆ ({1, 2} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · exfalso
        rw [e3] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (9, 4)`: the per-pair threshold — period `3`, band-1
count `2`; the half-density scalar `2·(2·c0·runDyadicMult) ≤ (c⋆ξ/24)·3`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_9_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) (hK : (class1SlopeDatum ctx).K₀ = 4)
    (hcW : 3 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((2 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (3 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 3) (b1 := 2)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_9_4.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_9_4.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (11, 5)`: period `5`, cycle `9 → 7 → 3 → 1 → 5`, bands `1, 1, 2, 4, 2` — band-1 count `≤ 2`. -/
private theorem runCycle_11_5 :
    slopeOrbit 11 5 (1 + 5) = slopeOrbit 11 5 1
      ∧ ((Finset.Icc 1 5).filter
          (fun j => canonGap 11 (slopeOrbit 11 5 j) = 1)).card ≤ 2 := by
  have e0 : slopeOrbit 11 5 0 = 5 := rfl
  have e1 : slopeOrbit 11 5 1 = 9 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 11 5 2 = 7 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 11 5 3 = 3 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 11 5 4 = 1 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 11 5 5 = 5 :=
    slopeOrbit_step_eval 4 3 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 11 5 6 = 9 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 11 5 6 = slopeOrbit 11 5 1
    rw [e6, e1]
  · have hsub : (Finset.Icc 1 5).filter
        (fun j => canonGap 11 (slopeOrbit 11 5 j) = 1) ⊆ ({1, 2} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · exfalso
        rw [e3] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e4] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (11, 5)`: the per-pair threshold — period `5`, band-1
count `2`; the half-density scalar `2·(2·c0·runDyadicMult) ≤ (c⋆ξ/24)·5`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_11_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 11) (hK : (class1SlopeDatum ctx).K₀ = 5)
    (hcW : 5 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((2 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (5 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 5) (b1 := 2)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_11_5.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_11_5.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (13, 6)`: period `6`, cycle `11 → 9 → 5 → 7 → 1 → 3`, bands `1, 1, 2, 1, 4, 3` — band-1 count `≤ 3`. -/
private theorem runCycle_13_6 :
    slopeOrbit 13 6 (1 + 6) = slopeOrbit 13 6 1
      ∧ ((Finset.Icc 1 6).filter
          (fun j => canonGap 13 (slopeOrbit 13 6 j) = 1)).card ≤ 3 := by
  have e0 : slopeOrbit 13 6 0 = 6 := rfl
  have e1 : slopeOrbit 13 6 1 = 11 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 13 6 2 = 9 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 13 6 3 = 5 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 13 6 4 = 7 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 13 6 5 = 1 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 13 6 6 = 3 :=
    slopeOrbit_step_eval 5 3 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 13 6 7 = 11 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 13 6 7 = slopeOrbit 13 6 1
    rw [e7, e1]
  · have hsub : (Finset.Icc 1 6).filter
        (fun j => canonGap 13 (slopeOrbit 13 6 j) = 1) ⊆ ({1, 2, 4} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · exfalso
        rw [e3] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (13, 6)`: the per-pair threshold — period `6`, band-1
count `3`; the half-density scalar `2·(3·c0·runDyadicMult) ≤ (c⋆ξ/24)·6`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_13_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 13) (hK : (class1SlopeDatum ctx).K₀ = 6)
    (hcW : 6 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((3 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (6 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 6) (b1 := 3)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_13_6.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_13_6.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (15, 1)`: period `1`, cycle `1`, bands `4` — band-1 count `≤ 0`. -/
private theorem runCycle_15_1 :
    slopeOrbit 15 1 (1 + 1) = slopeOrbit 15 1 1
      ∧ ((Finset.Icc 1 1).filter
          (fun j => canonGap 15 (slopeOrbit 15 1 j) = 1)).card ≤ 0 := by
  have e0 : slopeOrbit 15 1 0 = 1 := rfl
  have e1 : slopeOrbit 15 1 1 = 1 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 15 1 2 = 1 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 15 1 2 = slopeOrbit 15 1 1
    rw [e2, e1]
  · have hsub : (Finset.Icc 1 1).filter
        (fun j => canonGap 15 (slopeOrbit 15 1 j) = 1) ⊆ (∅ : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exfalso
        rw [e1] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (15, 1)`: band-4-only cycle (`b1 = 0`) — the band-1 scalar
holds for FREE; only the heavy-span scalar remains. -/
theorem class5BandHeavy_of_datum_15_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hcW : 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 1) (b1 := 0)
    (by norm_num) ?_ hcW ?_ (run_b1_zero_scalar _ _) hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_15_1.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_15_1.2

/-- `(q, K₀) = (15, 2)`: period `1`, cycle `1`, bands `4` — band-1 count `≤ 0`. -/
private theorem runCycle_15_2 :
    slopeOrbit 15 2 (1 + 1) = slopeOrbit 15 2 1
      ∧ ((Finset.Icc 1 1).filter
          (fun j => canonGap 15 (slopeOrbit 15 2 j) = 1)).card ≤ 0 := by
  have e0 : slopeOrbit 15 2 0 = 2 := rfl
  have e1 : slopeOrbit 15 2 1 = 1 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 15 2 2 = 1 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 15 2 2 = slopeOrbit 15 2 1
    rw [e2, e1]
  · have hsub : (Finset.Icc 1 1).filter
        (fun j => canonGap 15 (slopeOrbit 15 2 j) = 1) ⊆ (∅ : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exfalso
        rw [e1] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (15, 2)`: band-4-only cycle (`b1 = 0`) — the band-1 scalar
holds for FREE; only the heavy-span scalar remains. -/
theorem class5BandHeavy_of_datum_15_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (hcW : 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 1) (b1 := 0)
    (by norm_num) ?_ hcW ?_ (run_b1_zero_scalar _ _) hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_15_2.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_15_2.2

/-- `(q, K₀) = (15, 7)`: period `3`, cycle `13 → 11 → 7`, bands `1, 1, 2` — band-1 count `≤ 2`. -/
private theorem runCycle_15_7 :
    slopeOrbit 15 7 (1 + 3) = slopeOrbit 15 7 1
      ∧ ((Finset.Icc 1 3).filter
          (fun j => canonGap 15 (slopeOrbit 15 7 j) = 1)).card ≤ 2 := by
  have e0 : slopeOrbit 15 7 0 = 7 := rfl
  have e1 : slopeOrbit 15 7 1 = 13 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 15 7 2 = 11 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 15 7 3 = 7 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 15 7 4 = 13 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 15 7 4 = slopeOrbit 15 7 1
    rw [e4, e1]
  · have hsub : (Finset.Icc 1 3).filter
        (fun j => canonGap 15 (slopeOrbit 15 7 j) = 1) ⊆ ({1, 2} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · exfalso
        rw [e3] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (15, 7)`: the per-pair threshold — period `3`, band-1
count `2`; the half-density scalar `2·(2·c0·runDyadicMult) ≤ (c⋆ξ/24)·3`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_15_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 7)
    (hcW : 3 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((2 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (3 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 3) (b1 := 2)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_15_7.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_15_7.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (17, 8)`: period `4`, cycle `15 → 13 → 9 → 1`, bands `1, 1, 1, 5` — band-1 count `≤ 3`. -/
private theorem runCycle_17_8 :
    slopeOrbit 17 8 (1 + 4) = slopeOrbit 17 8 1
      ∧ ((Finset.Icc 1 4).filter
          (fun j => canonGap 17 (slopeOrbit 17 8 j) = 1)).card ≤ 3 := by
  have e0 : slopeOrbit 17 8 0 = 8 := rfl
  have e1 : slopeOrbit 17 8 1 = 15 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 17 8 2 = 13 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 17 8 3 = 9 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 17 8 4 = 1 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 17 8 5 = 15 :=
    slopeOrbit_step_eval 4 4 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 17 8 5 = slopeOrbit 17 8 1
    rw [e5, e1]
  · have hsub : (Finset.Icc 1 4).filter
        (fun j => canonGap 17 (slopeOrbit 17 8 j) = 1) ⊆ ({1, 2, 3} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · exfalso
        rw [e4] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (17, 8)`: the per-pair threshold — period `4`, band-1
count `3`; the half-density scalar `2·(3·c0·runDyadicMult) ≤ (c⋆ξ/24)·4`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_17_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 17) (hK : (class1SlopeDatum ctx).K₀ = 8)
    (hcW : 4 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((3 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (4 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 4) (b1 := 3)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_17_8.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_17_8.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (19, 9)`: period `9`, cycle `17 → 15 → 11 → 3 → 5 → 1 → 13 → 7 → 9`, bands `1, 1, 1, 3, 2, 5, 1, 2, 2` — band-1 count `≤ 4`. -/
private theorem runCycle_19_9 :
    slopeOrbit 19 9 (1 + 9) = slopeOrbit 19 9 1
      ∧ ((Finset.Icc 1 9).filter
          (fun j => canonGap 19 (slopeOrbit 19 9 j) = 1)).card ≤ 4 := by
  have e0 : slopeOrbit 19 9 0 = 9 := rfl
  have e1 : slopeOrbit 19 9 1 = 17 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 19 9 2 = 15 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 19 9 3 = 11 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 19 9 4 = 3 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 19 9 5 = 5 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 19 9 6 = 1 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 19 9 7 = 13 :=
    slopeOrbit_step_eval 6 4 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 19 9 8 = 7 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 19 9 9 = 9 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 19 9 10 = 17 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 19 9 10 = slopeOrbit 19 9 1
    rw [e10, e1]
  · have hsub : (Finset.Icc 1 9).filter
        (fun j => canonGap 19 (slopeOrbit 19 9 j) = 1) ⊆ ({1, 2, 3, 7} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · exfalso
        rw [e4] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e8] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e9] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (19, 9)`: the per-pair threshold — period `9`, band-1
count `4`; the half-density scalar `2·(4·c0·runDyadicMult) ≤ (c⋆ξ/24)·9`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_19_9 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 19) (hK : (class1SlopeDatum ctx).K₀ = 9)
    (hcW : 9 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((4 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (9 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 9) (b1 := 4)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_19_9.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_19_9.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (21, 1)`: period `2`, cycle `11 → 1`, bands `1, 5` — band-1 count `≤ 1`. -/
private theorem runCycle_21_1 :
    slopeOrbit 21 1 (1 + 2) = slopeOrbit 21 1 1
      ∧ ((Finset.Icc 1 2).filter
          (fun j => canonGap 21 (slopeOrbit 21 1 j) = 1)).card ≤ 1 := by
  have e0 : slopeOrbit 21 1 0 = 1 := rfl
  have e1 : slopeOrbit 21 1 1 = 11 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 21 1 2 = 1 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 21 1 3 = 11 :=
    slopeOrbit_step_eval 2 4 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 21 1 3 = slopeOrbit 21 1 1
    rw [e3, e1]
  · have hsub : (Finset.Icc 1 2).filter
        (fun j => canonGap 21 (slopeOrbit 21 1 j) = 1) ⊆ ({1} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · exfalso
        rw [e2] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (21, 1)`: the per-pair threshold — period `2`, band-1
count `1`; the half-density scalar `2·(1·c0·runDyadicMult) ≤ (c⋆ξ/24)·2`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_21_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hcW : 2 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((1 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (2 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 2) (b1 := 1)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_21_1.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_21_1.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (21, 3)`: period `1`, cycle `3`, bands `3` — band-`{1,4}`-free. -/
private theorem runCycle_21_3 :
    slopeOrbit 21 3 (1 + 1) = slopeOrbit 21 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 →
          canonGap 21 (slopeOrbit 21 3 j) ≠ 1
            ∧ canonGap 21 (slopeOrbit 21 3 j) ≠ 4 := by
  have e0 : slopeOrbit 21 3 0 = 3 := rfl
  have e1 : slopeOrbit 21 3 1 = 3 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 21 3 2 = 3 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 21 3 2 = slopeOrbit 21 3 1
    rw [e2, e1]
  · intro j hj1 hjc
    interval_cases j
    · rw [e1]
      exact ⟨canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num),
        canonGap_ne_four_of_band (Or.inl (by norm_num))⟩

/-- `(q, K₀) = (21, 3)` closes the capstone inequality OUTRIGHT (band-`{1,4}`-free cycle). -/
theorem runNumericIneq_of_datum_21_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    RunNumericIneq ctx := by
  refine runNumericIneq_of_cycle_band_free ctx (c := 1) (by norm_num) ?_ ?_
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_21_3.1
  · rw [hq, hK]
    exact runCycle_21_3.2

/-- `(q, K₀) = (21, 3)` settles `Class5CycleNumericCloses` unconditionally (count `0`). -/
theorem class5CycleNumericCloses_of_datum_21_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    Class5CycleNumericCloses ctx := by
  refine class5CycleNumericCloses_of_cycle_band_free ctx (c := 1) (by norm_num) ?_ ?_
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_21_3.1
  · rw [hq, hK]
    exact runCycle_21_3.2

/-- `(q, K₀) = (21, 10)`: period `4`, cycle `19 → 17 → 13 → 5`, bands `1, 1, 1, 3` — band-1 count `≤ 3`. -/
private theorem runCycle_21_10 :
    slopeOrbit 21 10 (1 + 4) = slopeOrbit 21 10 1
      ∧ ((Finset.Icc 1 4).filter
          (fun j => canonGap 21 (slopeOrbit 21 10 j) = 1)).card ≤ 3 := by
  have e0 : slopeOrbit 21 10 0 = 10 := rfl
  have e1 : slopeOrbit 21 10 1 = 19 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 21 10 2 = 17 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 21 10 3 = 13 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 21 10 4 = 5 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 21 10 5 = 19 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 21 10 5 = slopeOrbit 21 10 1
    rw [e5, e1]
  · have hsub : (Finset.Icc 1 4).filter
        (fun j => canonGap 21 (slopeOrbit 21 10 j) = 1) ⊆ ({1, 2, 3} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · exfalso
        rw [e4] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (21, 10)`: the per-pair threshold — period `4`, band-1
count `3`; the half-density scalar `2·(3·c0·runDyadicMult) ≤ (c⋆ξ/24)·4`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_21_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 10)
    (hcW : 4 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((3 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (4 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 4) (b1 := 3)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_21_10.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_21_10.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (23, 11)`: period `7`, cycle `21 → 19 → 15 → 7 → 5 → 17 → 11`, bands `1, 1, 1, 2, 3, 1, 2` — band-1 count `≤ 4`. -/
private theorem runCycle_23_11 :
    slopeOrbit 23 11 (1 + 7) = slopeOrbit 23 11 1
      ∧ ((Finset.Icc 1 7).filter
          (fun j => canonGap 23 (slopeOrbit 23 11 j) = 1)).card ≤ 4 := by
  have e0 : slopeOrbit 23 11 0 = 11 := rfl
  have e1 : slopeOrbit 23 11 1 = 21 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 23 11 2 = 19 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 23 11 3 = 15 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 23 11 4 = 7 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 23 11 5 = 5 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 23 11 6 = 17 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 23 11 7 = 11 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 23 11 8 = 21 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 23 11 8 = slopeOrbit 23 11 1
    rw [e8, e1]
  · have hsub : (Finset.Icc 1 7).filter
        (fun j => canonGap 23 (slopeOrbit 23 11 j) = 1) ⊆ ({1, 2, 3, 6} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · exfalso
        rw [e4] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e7] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (23, 11)`: the per-pair threshold — period `7`, band-1
count `4`; the half-density scalar `2·(4·c0·runDyadicMult) ≤ (c⋆ξ/24)·7`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_23_11 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 23) (hK : (class1SlopeDatum ctx).K₀ = 11)
    (hcW : 7 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((4 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (7 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 7) (b1 := 4)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_23_11.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_23_11.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (25, 2)`: period `10`, cycle `7 → 3 → 23 → 21 → 17 → 9 → 11 → 19 → 13 → 1`, bands `2, 4, 1, 1, 1, 2, 2, 1, 1, 5` — band-1 count `≤ 5`. -/
private theorem runCycle_25_2 :
    slopeOrbit 25 2 (1 + 10) = slopeOrbit 25 2 1
      ∧ ((Finset.Icc 1 10).filter
          (fun j => canonGap 25 (slopeOrbit 25 2 j) = 1)).card ≤ 5 := by
  have e0 : slopeOrbit 25 2 0 = 2 := rfl
  have e1 : slopeOrbit 25 2 1 = 7 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 25 2 2 = 3 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 25 2 3 = 23 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 25 2 4 = 21 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 25 2 5 = 17 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 25 2 6 = 9 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 25 2 7 = 11 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 25 2 8 = 19 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 25 2 9 = 13 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 25 2 10 = 1 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 25 2 11 = 7 :=
    slopeOrbit_step_eval 10 4 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 25 2 11 = slopeOrbit 25 2 1
    rw [e11, e1]
  · have hsub : (Finset.Icc 1 10).filter
        (fun j => canonGap 25 (slopeOrbit 25 2 j) = 1) ⊆ ({3, 4, 5, 8, 9} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exfalso
        rw [e1] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e2] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · decide
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e7] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · exfalso
        rw [e10] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (25, 2)`: the per-pair threshold — period `10`, band-1
count `5`; the half-density scalar `2·(5·c0·runDyadicMult) ≤ (c⋆ξ/24)·10`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_25_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (hcW : 10 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((5 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (10 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 10) (b1 := 5)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_25_2.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_25_2.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (25, 12)`: period `10`, cycle `23 → 21 → 17 → 9 → 11 → 19 → 13 → 1 → 7 → 3`, bands `1, 1, 1, 2, 2, 1, 1, 5, 2, 4` — band-1 count `≤ 5`. -/
private theorem runCycle_25_12 :
    slopeOrbit 25 12 (1 + 10) = slopeOrbit 25 12 1
      ∧ ((Finset.Icc 1 10).filter
          (fun j => canonGap 25 (slopeOrbit 25 12 j) = 1)).card ≤ 5 := by
  have e0 : slopeOrbit 25 12 0 = 12 := rfl
  have e1 : slopeOrbit 25 12 1 = 23 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 25 12 2 = 21 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 25 12 3 = 17 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 25 12 4 = 9 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 25 12 5 = 11 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 25 12 6 = 19 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 25 12 7 = 13 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 25 12 8 = 1 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 25 12 9 = 7 :=
    slopeOrbit_step_eval 8 4 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 25 12 10 = 3 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 25 12 11 = 23 :=
    slopeOrbit_step_eval 10 3 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 25 12 11 = slopeOrbit 25 12 1
    rw [e11, e1]
  · have hsub : (Finset.Icc 1 10).filter
        (fun j => canonGap 25 (slopeOrbit 25 12 j) = 1) ⊆ ({1, 2, 3, 6, 7} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · exfalso
        rw [e4] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · exfalso
        rw [e8] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e9] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e10] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (25, 12)`: the per-pair threshold — period `10`, band-1
count `5`; the half-density scalar `2·(5·c0·runDyadicMult) ≤ (c⋆ξ/24)·10`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_25_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 12)
    (hcW : 10 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((5 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (10 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 10) (b1 := 5)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_25_12.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_25_12.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (27, 1)`: period `9`, cycle `5 → 13 → 25 → 23 → 19 → 11 → 17 → 7 → 1`, bands `3, 2, 1, 1, 1, 2, 1, 2, 5` — band-1 count `≤ 4`. -/
private theorem runCycle_27_1 :
    slopeOrbit 27 1 (1 + 9) = slopeOrbit 27 1 1
      ∧ ((Finset.Icc 1 9).filter
          (fun j => canonGap 27 (slopeOrbit 27 1 j) = 1)).card ≤ 4 := by
  have e0 : slopeOrbit 27 1 0 = 1 := rfl
  have e1 : slopeOrbit 27 1 1 = 5 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 27 1 2 = 13 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 27 1 3 = 25 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 27 1 4 = 23 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 27 1 5 = 19 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 27 1 6 = 11 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 27 1 7 = 17 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 27 1 8 = 7 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 27 1 9 = 1 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 27 1 10 = 5 :=
    slopeOrbit_step_eval 9 4 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 27 1 10 = slopeOrbit 27 1 1
    rw [e10, e1]
  · have hsub : (Finset.Icc 1 9).filter
        (fun j => canonGap 27 (slopeOrbit 27 1 j) = 1) ⊆ ({3, 4, 5, 7} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exfalso
        rw [e1] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e2] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · decide
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e8] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e9] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (27, 1)`: the per-pair threshold — period `9`, band-1
count `4`; the half-density scalar `2·(4·c0·runDyadicMult) ≤ (c⋆ξ/24)·9`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_27_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hcW : 9 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((4 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (9 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 9) (b1 := 4)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_27_1.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_27_1.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (27, 4)`: period `9`, cycle `5 → 13 → 25 → 23 → 19 → 11 → 17 → 7 → 1`, bands `3, 2, 1, 1, 1, 2, 1, 2, 5` — band-1 count `≤ 4`. -/
private theorem runCycle_27_4 :
    slopeOrbit 27 4 (1 + 9) = slopeOrbit 27 4 1
      ∧ ((Finset.Icc 1 9).filter
          (fun j => canonGap 27 (slopeOrbit 27 4 j) = 1)).card ≤ 4 := by
  have e0 : slopeOrbit 27 4 0 = 4 := rfl
  have e1 : slopeOrbit 27 4 1 = 5 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 27 4 2 = 13 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 27 4 3 = 25 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 27 4 4 = 23 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 27 4 5 = 19 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 27 4 6 = 11 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 27 4 7 = 17 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 27 4 8 = 7 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 27 4 9 = 1 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 27 4 10 = 5 :=
    slopeOrbit_step_eval 9 4 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 27 4 10 = slopeOrbit 27 4 1
    rw [e10, e1]
  · have hsub : (Finset.Icc 1 9).filter
        (fun j => canonGap 27 (slopeOrbit 27 4 j) = 1) ⊆ ({3, 4, 5, 7} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exfalso
        rw [e1] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e2] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · decide
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e8] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e9] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (27, 4)`: the per-pair threshold — period `9`, band-1
count `4`; the half-density scalar `2·(4·c0·runDyadicMult) ≤ (c⋆ξ/24)·9`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_27_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 4)
    (hcW : 9 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((4 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (9 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 9) (b1 := 4)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_27_4.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_27_4.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (27, 13)`: period `9`, cycle `25 → 23 → 19 → 11 → 17 → 7 → 1 → 5 → 13`, bands `1, 1, 1, 2, 1, 2, 5, 3, 2` — band-1 count `≤ 4`. -/
private theorem runCycle_27_13 :
    slopeOrbit 27 13 (1 + 9) = slopeOrbit 27 13 1
      ∧ ((Finset.Icc 1 9).filter
          (fun j => canonGap 27 (slopeOrbit 27 13 j) = 1)).card ≤ 4 := by
  have e0 : slopeOrbit 27 13 0 = 13 := rfl
  have e1 : slopeOrbit 27 13 1 = 25 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 27 13 2 = 23 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 27 13 3 = 19 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 27 13 4 = 11 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 27 13 5 = 17 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 27 13 6 = 7 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 27 13 7 = 1 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 27 13 8 = 5 :=
    slopeOrbit_step_eval 7 4 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 27 13 9 = 13 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 27 13 10 = 25 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 27 13 10 = slopeOrbit 27 13 1
    rw [e10, e1]
  · have hsub : (Finset.Icc 1 9).filter
        (fun j => canonGap 27 (slopeOrbit 27 13 j) = 1) ⊆ ({1, 2, 3, 5} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · exfalso
        rw [e4] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e7] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e8] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e9] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (27, 13)`: the per-pair threshold — period `9`, band-1
count `4`; the half-density scalar `2·(4·c0·runDyadicMult) ≤ (c⋆ξ/24)·9`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_27_13 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 13)
    (hcW : 9 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((4 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (9 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 9) (b1 := 4)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_27_13.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_27_13.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (29, 14)`: period `14`, cycle `27 → 25 → 21 → 13 → 23 → 17 → 5 → 11 → 15 → 1 → 3 → 19 → 9 → 7`, bands `1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 4, 1, 2, 3` — band-1 count `≤ 7`. -/
private theorem runCycle_29_14 :
    slopeOrbit 29 14 (1 + 14) = slopeOrbit 29 14 1
      ∧ ((Finset.Icc 1 14).filter
          (fun j => canonGap 29 (slopeOrbit 29 14 j) = 1)).card ≤ 7 := by
  have e0 : slopeOrbit 29 14 0 = 14 := rfl
  have e1 : slopeOrbit 29 14 1 = 27 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 29 14 2 = 25 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 29 14 3 = 21 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 29 14 4 = 13 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 29 14 5 = 23 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 29 14 6 = 17 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 29 14 7 = 5 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 29 14 8 = 11 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 29 14 9 = 15 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 29 14 10 = 1 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 29 14 11 = 3 :=
    slopeOrbit_step_eval 10 4 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 29 14 12 = 19 :=
    slopeOrbit_step_eval 11 3 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 29 14 13 = 9 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 29 14 14 = 7 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 29 14 15 = 27 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 29 14 15 = slopeOrbit 29 14 1
    rw [e15, e1]
  · have hsub : (Finset.Icc 1 14).filter
        (fun j => canonGap 29 (slopeOrbit 29 14 j) = 1) ⊆ ({1, 2, 3, 5, 6, 9, 12} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · exfalso
        rw [e4] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · exfalso
        rw [e7] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e8] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e10] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e11] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e13] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e14] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (29, 14)`: the per-pair threshold — period `14`, band-1
count `7`; the half-density scalar `2·(7·c0·runDyadicMult) ≤ (c⋆ξ/24)·14`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_29_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 29) (hK : (class1SlopeDatum ctx).K₀ = 14)
    (hcW : 14 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((7 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (14 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 14) (b1 := 7)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_29_14.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_29_14.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (31, 15)`: period `4`, cycle `29 → 27 → 23 → 15`, bands `1, 1, 1, 2` — band-1 count `≤ 3`. -/
private theorem runCycle_31_15 :
    slopeOrbit 31 15 (1 + 4) = slopeOrbit 31 15 1
      ∧ ((Finset.Icc 1 4).filter
          (fun j => canonGap 31 (slopeOrbit 31 15 j) = 1)).card ≤ 3 := by
  have e0 : slopeOrbit 31 15 0 = 15 := rfl
  have e1 : slopeOrbit 31 15 1 = 29 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 31 15 2 = 27 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 31 15 3 = 23 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 31 15 4 = 15 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 31 15 5 = 29 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 31 15 5 = slopeOrbit 31 15 1
    rw [e5, e1]
  · have hsub : (Finset.Icc 1 4).filter
        (fun j => canonGap 31 (slopeOrbit 31 15 j) = 1) ⊆ ({1, 2, 3} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · exfalso
        rw [e4] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (31, 15)`: the per-pair threshold — period `4`, band-1
count `3`; the half-density scalar `2·(3·c0·runDyadicMult) ≤ (c⋆ξ/24)·4`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_31_15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 31) (hK : (class1SlopeDatum ctx).K₀ = 15)
    (hcW : 4 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((3 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (4 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 4) (b1 := 3)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_31_15.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_31_15.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (33, 1)`: period `5`, cycle `31 → 29 → 25 → 17 → 1`, bands `1, 1, 1, 1, 6` — band-1 count `≤ 4`. -/
private theorem runCycle_33_1 :
    slopeOrbit 33 1 (1 + 5) = slopeOrbit 33 1 1
      ∧ ((Finset.Icc 1 5).filter
          (fun j => canonGap 33 (slopeOrbit 33 1 j) = 1)).card ≤ 4 := by
  have e0 : slopeOrbit 33 1 0 = 1 := rfl
  have e1 : slopeOrbit 33 1 1 = 31 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 33 1 2 = 29 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 33 1 3 = 25 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 33 1 4 = 17 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 33 1 5 = 1 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 33 1 6 = 31 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 33 1 6 = slopeOrbit 33 1 1
    rw [e6, e1]
  · have hsub : (Finset.Icc 1 5).filter
        (fun j => canonGap 33 (slopeOrbit 33 1 j) = 1) ⊆ ({1, 2, 3, 4} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (33, 1)`: the per-pair threshold — period `5`, band-1
count `4`; the half-density scalar `2·(4·c0·runDyadicMult) ≤ (c⋆ξ/24)·5`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_33_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hcW : 5 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((4 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (5 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 5) (b1 := 4)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_33_1.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_33_1.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (33, 5)`: period `5`, cycle `7 → 23 → 13 → 19 → 5`, bands `3, 1, 2, 1, 3` — band-1 count `≤ 2`. -/
private theorem runCycle_33_5 :
    slopeOrbit 33 5 (1 + 5) = slopeOrbit 33 5 1
      ∧ ((Finset.Icc 1 5).filter
          (fun j => canonGap 33 (slopeOrbit 33 5 j) = 1)).card ≤ 2 := by
  have e0 : slopeOrbit 33 5 0 = 5 := rfl
  have e1 : slopeOrbit 33 5 1 = 7 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 33 5 2 = 23 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 33 5 3 = 13 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 33 5 4 = 19 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 33 5 5 = 5 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 33 5 6 = 7 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 33 5 6 = slopeOrbit 33 5 1
    rw [e6, e1]
  · have hsub : (Finset.Icc 1 5).filter
        (fun j => canonGap 33 (slopeOrbit 33 5 j) = 1) ⊆ ({2, 4} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exfalso
        rw [e1] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e3] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (33, 5)`: the per-pair threshold — period `5`, band-1
count `2`; the half-density scalar `2·(2·c0·runDyadicMult) ≤ (c⋆ξ/24)·5`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_33_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 5)
    (hcW : 5 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((2 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (5 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 5) (b1 := 2)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_33_5.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_33_5.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (33, 16)`: period `5`, cycle `31 → 29 → 25 → 17 → 1`, bands `1, 1, 1, 1, 6` — band-1 count `≤ 4`. -/
private theorem runCycle_33_16 :
    slopeOrbit 33 16 (1 + 5) = slopeOrbit 33 16 1
      ∧ ((Finset.Icc 1 5).filter
          (fun j => canonGap 33 (slopeOrbit 33 16 j) = 1)).card ≤ 4 := by
  have e0 : slopeOrbit 33 16 0 = 16 := rfl
  have e1 : slopeOrbit 33 16 1 = 31 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 33 16 2 = 29 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 33 16 3 = 25 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 33 16 4 = 17 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 33 16 5 = 1 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 33 16 6 = 31 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 33 16 6 = slopeOrbit 33 16 1
    rw [e6, e1]
  · have hsub : (Finset.Icc 1 5).filter
        (fun j => canonGap 33 (slopeOrbit 33 16 j) = 1) ⊆ ({1, 2, 3, 4} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (33, 16)`: the per-pair threshold — period `5`, band-1
count `4`; the half-density scalar `2·(4·c0·runDyadicMult) ≤ (c⋆ξ/24)·5`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_33_16 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 16)
    (hcW : 5 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((4 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (5 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 5) (b1 := 4)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_33_16.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_33_16.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (35, 2)`: period `5`, cycle `29 → 23 → 11 → 9 → 1`, bands `1, 1, 2, 2, 6` — band-1 count `≤ 2`. -/
private theorem runCycle_35_2 :
    slopeOrbit 35 2 (1 + 5) = slopeOrbit 35 2 1
      ∧ ((Finset.Icc 1 5).filter
          (fun j => canonGap 35 (slopeOrbit 35 2 j) = 1)).card ≤ 2 := by
  have e0 : slopeOrbit 35 2 0 = 2 := rfl
  have e1 : slopeOrbit 35 2 1 = 29 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 35 2 2 = 23 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 35 2 3 = 11 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 35 2 4 = 9 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 35 2 5 = 1 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 35 2 6 = 29 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 35 2 6 = slopeOrbit 35 2 1
    rw [e6, e1]
  · have hsub : (Finset.Icc 1 5).filter
        (fun j => canonGap 35 (slopeOrbit 35 2 j) = 1) ⊆ ({1, 2} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · exfalso
        rw [e3] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e4] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (35, 2)`: the per-pair threshold — period `5`, band-1
count `2`; the half-density scalar `2·(2·c0·runDyadicMult) ≤ (c⋆ξ/24)·5`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_35_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (hcW : 5 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((2 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (5 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 5) (b1 := 2)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_35_2.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_35_2.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (35, 3)`: period `7`, cycle `13 → 17 → 33 → 31 → 27 → 19 → 3`, bands `2, 2, 1, 1, 1, 1, 4` — band-1 count `≤ 4`. -/
private theorem runCycle_35_3 :
    slopeOrbit 35 3 (1 + 7) = slopeOrbit 35 3 1
      ∧ ((Finset.Icc 1 7).filter
          (fun j => canonGap 35 (slopeOrbit 35 3 j) = 1)).card ≤ 4 := by
  have e0 : slopeOrbit 35 3 0 = 3 := rfl
  have e1 : slopeOrbit 35 3 1 = 13 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 35 3 2 = 17 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 35 3 3 = 33 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 35 3 4 = 31 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 35 3 5 = 27 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 35 3 6 = 19 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 35 3 7 = 3 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 35 3 8 = 13 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 35 3 8 = slopeOrbit 35 3 1
    rw [e8, e1]
  · have hsub : (Finset.Icc 1 7).filter
        (fun j => canonGap 35 (slopeOrbit 35 3 j) = 1) ⊆ ({3, 4, 5, 6} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exfalso
        rw [e1] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e2] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e7] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (35, 3)`: the per-pair threshold — period `7`, band-1
count `4`; the half-density scalar `2·(4·c0·runDyadicMult) ≤ (c⋆ξ/24)·7`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_35_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 3)
    (hcW : 7 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((4 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (7 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 7) (b1 := 4)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_35_3.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_35_3.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (35, 17)`: period `7`, cycle `33 → 31 → 27 → 19 → 3 → 13 → 17`, bands `1, 1, 1, 1, 4, 2, 2` — band-1 count `≤ 4`. -/
private theorem runCycle_35_17 :
    slopeOrbit 35 17 (1 + 7) = slopeOrbit 35 17 1
      ∧ ((Finset.Icc 1 7).filter
          (fun j => canonGap 35 (slopeOrbit 35 17 j) = 1)).card ≤ 4 := by
  have e0 : slopeOrbit 35 17 0 = 17 := rfl
  have e1 : slopeOrbit 35 17 1 = 33 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 35 17 2 = 31 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 35 17 3 = 27 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 35 17 4 = 19 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 35 17 5 = 3 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 35 17 6 = 13 :=
    slopeOrbit_step_eval 5 3 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 35 17 7 = 17 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 35 17 8 = 33 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 35 17 8 = slopeOrbit 35 17 1
    rw [e8, e1]
  · have hsub : (Finset.Icc 1 7).filter
        (fun j => canonGap 35 (slopeOrbit 35 17 j) = 1) ⊆ ({1, 2, 3, 4} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e7] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (35, 17)`: the per-pair threshold — period `7`, band-1
count `4`; the half-density scalar `2·(4·c0·runDyadicMult) ≤ (c⋆ξ/24)·7`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_35_17 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 17)
    (hcW : 7 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((4 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (7 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 7) (b1 := 4)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_35_17.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_35_17.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (37, 18)`: period `18`, cycle `35 → 33 → 29 → 21 → 5 → 3 → 11 → 7 → 19 → 1 → 27 → 17 → 31 → 25 → 13 → 15 → 23 → 9`, bands `1, 1, 1, 1, 3, 4, 2, 3, 1, 6, 1, 2, 1, 1, 2, 2, 1, 3` — band-1 count `≤ 9`. -/
private theorem runCycle_37_18 :
    slopeOrbit 37 18 (1 + 18) = slopeOrbit 37 18 1
      ∧ ((Finset.Icc 1 18).filter
          (fun j => canonGap 37 (slopeOrbit 37 18 j) = 1)).card ≤ 9 := by
  have e0 : slopeOrbit 37 18 0 = 18 := rfl
  have e1 : slopeOrbit 37 18 1 = 35 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 37 18 2 = 33 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 37 18 3 = 29 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 37 18 4 = 21 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 37 18 5 = 5 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 37 18 6 = 3 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 37 18 7 = 11 :=
    slopeOrbit_step_eval 6 3 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 37 18 8 = 7 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 37 18 9 = 19 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 37 18 10 = 1 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 37 18 11 = 27 :=
    slopeOrbit_step_eval 10 5 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 37 18 12 = 17 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 37 18 13 = 31 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 37 18 14 = 25 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 37 18 15 = 13 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 37 18 16 = 15 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 37 18 17 = 23 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 37 18 18 = 9 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 37 18 19 = 35 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 37 18 19 = slopeOrbit 37 18 1
    rw [e19, e1]
  · have hsub : (Finset.Icc 1 18).filter
        (fun j => canonGap 37 (slopeOrbit 37 18 j) = 1) ⊆ ({1, 2, 3, 4, 9, 11, 13, 14, 17} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e7] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e8] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e10] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e12] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · exfalso
        rw [e15] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e16] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e18] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (37, 18)`: the per-pair threshold — period `18`, band-1
count `9`; the half-density scalar `2·(9·c0·runDyadicMult) ≤ (c⋆ξ/24)·18`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_37_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 37) (hK : (class1SlopeDatum ctx).K₀ = 18)
    (hcW : 18 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((9 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (18 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 18) (b1 := 9)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_37_18.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_37_18.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (39, 1)`: period `4`, cycle `25 → 11 → 5 → 1`, bands `1, 2, 3, 6` — band-1 count `≤ 1`. -/
private theorem runCycle_39_1 :
    slopeOrbit 39 1 (1 + 4) = slopeOrbit 39 1 1
      ∧ ((Finset.Icc 1 4).filter
          (fun j => canonGap 39 (slopeOrbit 39 1 j) = 1)).card ≤ 1 := by
  have e0 : slopeOrbit 39 1 0 = 1 := rfl
  have e1 : slopeOrbit 39 1 1 = 25 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 39 1 2 = 11 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 39 1 3 = 5 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 39 1 4 = 1 :=
    slopeOrbit_step_eval 3 2 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 39 1 5 = 25 :=
    slopeOrbit_step_eval 4 5 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 39 1 5 = slopeOrbit 39 1 1
    rw [e5, e1]
  · have hsub : (Finset.Icc 1 4).filter
        (fun j => canonGap 39 (slopeOrbit 39 1 j) = 1) ⊆ ({1} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · exfalso
        rw [e2] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e3] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e4] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (39, 1)`: the per-pair threshold — period `4`, band-1
count `1`; the half-density scalar `2·(1·c0·runDyadicMult) ≤ (c⋆ξ/24)·4`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_39_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hcW : 4 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((1 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (4 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 4) (b1 := 1)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_39_1.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_39_1.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (39, 6)`: period `6`, cycle `9 → 33 → 27 → 15 → 21 → 3`, bands `3, 1, 1, 2, 1, 4` — band-1 count `≤ 3`. -/
private theorem runCycle_39_6 :
    slopeOrbit 39 6 (1 + 6) = slopeOrbit 39 6 1
      ∧ ((Finset.Icc 1 6).filter
          (fun j => canonGap 39 (slopeOrbit 39 6 j) = 1)).card ≤ 3 := by
  have e0 : slopeOrbit 39 6 0 = 6 := rfl
  have e1 : slopeOrbit 39 6 1 = 9 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 39 6 2 = 33 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 39 6 3 = 27 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 39 6 4 = 15 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 39 6 5 = 21 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 39 6 6 = 3 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 39 6 7 = 9 :=
    slopeOrbit_step_eval 6 3 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 39 6 7 = slopeOrbit 39 6 1
    rw [e7, e1]
  · have hsub : (Finset.Icc 1 6).filter
        (fun j => canonGap 39 (slopeOrbit 39 6 j) = 1) ⊆ ({2, 3, 5} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exfalso
        rw [e1] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · exfalso
        rw [e4] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (39, 6)`: the per-pair threshold — period `6`, band-1
count `3`; the half-density scalar `2·(3·c0·runDyadicMult) ≤ (c⋆ξ/24)·6`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_39_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 6)
    (hcW : 6 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((3 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (6 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 6) (b1 := 3)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_39_6.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_39_6.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (39, 19)`: period `8`, cycle `37 → 35 → 31 → 23 → 7 → 17 → 29 → 19`, bands `1, 1, 1, 1, 3, 2, 1, 2` — band-1 count `≤ 5`. -/
private theorem runCycle_39_19 :
    slopeOrbit 39 19 (1 + 8) = slopeOrbit 39 19 1
      ∧ ((Finset.Icc 1 8).filter
          (fun j => canonGap 39 (slopeOrbit 39 19 j) = 1)).card ≤ 5 := by
  have e0 : slopeOrbit 39 19 0 = 19 := rfl
  have e1 : slopeOrbit 39 19 1 = 37 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 39 19 2 = 35 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 39 19 3 = 31 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 39 19 4 = 23 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 39 19 5 = 7 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 39 19 6 = 17 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 39 19 7 = 29 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 39 19 8 = 19 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 39 19 9 = 37 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 39 19 9 = slopeOrbit 39 19 1
    rw [e9, e1]
  · have hsub : (Finset.Icc 1 8).filter
        (fun j => canonGap 39 (slopeOrbit 39 19 j) = 1) ⊆ ({1, 2, 3, 4, 7} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e8] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (39, 19)`: the per-pair threshold — period `8`, band-1
count `5`; the half-density scalar `2·(5·c0·runDyadicMult) ≤ (c⋆ξ/24)·8`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_39_19 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 19)
    (hcW : 8 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((5 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (8 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 8) (b1 := 5)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_39_19.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_39_19.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (41, 20)`: period `10`, cycle `39 → 37 → 33 → 25 → 9 → 31 → 21 → 1 → 23 → 5`, bands `1, 1, 1, 1, 3, 1, 1, 6, 1, 4` — band-1 count `≤ 7`. -/
private theorem runCycle_41_20 :
    slopeOrbit 41 20 (1 + 10) = slopeOrbit 41 20 1
      ∧ ((Finset.Icc 1 10).filter
          (fun j => canonGap 41 (slopeOrbit 41 20 j) = 1)).card ≤ 7 := by
  have e0 : slopeOrbit 41 20 0 = 20 := rfl
  have e1 : slopeOrbit 41 20 1 = 39 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 41 20 2 = 37 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 41 20 3 = 33 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 41 20 4 = 25 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 41 20 5 = 9 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 41 20 6 = 31 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 41 20 7 = 21 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 41 20 8 = 1 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 41 20 9 = 23 :=
    slopeOrbit_step_eval 8 5 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 41 20 10 = 5 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 41 20 11 = 39 :=
    slopeOrbit_step_eval 10 3 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 41 20 11 = slopeOrbit 41 20 1
    rw [e11, e1]
  · have hsub : (Finset.Icc 1 10).filter
        (fun j => canonGap 41 (slopeOrbit 41 20 j) = 1) ⊆ ({1, 2, 3, 4, 6, 7, 9} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · exfalso
        rw [e8] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e10] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (41, 20)`: the per-pair threshold — period `10`, band-1
count `7`; the half-density scalar `2·(7·c0·runDyadicMult) ≤ (c⋆ξ/24)·10`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_41_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 41) (hK : (class1SlopeDatum ctx).K₀ = 20)
    (hcW : 10 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((7 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (10 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 10) (b1 := 7)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_41_20.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_41_20.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (43, 21)`: period `7`, cycle `41 → 39 → 35 → 27 → 11 → 1 → 21`, bands `1, 1, 1, 1, 2, 6, 2` — band-1 count `≤ 4`. -/
private theorem runCycle_43_21 :
    slopeOrbit 43 21 (1 + 7) = slopeOrbit 43 21 1
      ∧ ((Finset.Icc 1 7).filter
          (fun j => canonGap 43 (slopeOrbit 43 21 j) = 1)).card ≤ 4 := by
  have e0 : slopeOrbit 43 21 0 = 21 := rfl
  have e1 : slopeOrbit 43 21 1 = 41 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 43 21 2 = 39 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 43 21 3 = 35 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 43 21 4 = 27 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 43 21 5 = 11 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 43 21 6 = 1 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 43 21 7 = 21 :=
    slopeOrbit_step_eval 6 5 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 43 21 8 = 41 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 43 21 8 = slopeOrbit 43 21 1
    rw [e8, e1]
  · have hsub : (Finset.Icc 1 7).filter
        (fun j => canonGap 43 (slopeOrbit 43 21 j) = 1) ⊆ ({1, 2, 3, 4} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e7] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (43, 21)`: the per-pair threshold — period `7`, band-1
count `4`; the half-density scalar `2·(4·c0·runDyadicMult) ≤ (c⋆ξ/24)·7`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_43_21 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 43) (hK : (class1SlopeDatum ctx).K₀ = 21)
    (hcW : 7 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((4 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (7 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 7) (b1 := 4)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_43_21.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_43_21.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (45, 1)`: period `5`, cycle `19 → 31 → 17 → 23 → 1`, bands `2, 1, 2, 1, 6` — band-1 count `≤ 2`. -/
private theorem runCycle_45_1 :
    slopeOrbit 45 1 (1 + 5) = slopeOrbit 45 1 1
      ∧ ((Finset.Icc 1 5).filter
          (fun j => canonGap 45 (slopeOrbit 45 1 j) = 1)).card ≤ 2 := by
  have e0 : slopeOrbit 45 1 0 = 1 := rfl
  have e1 : slopeOrbit 45 1 1 = 19 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 45 1 2 = 31 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 45 1 3 = 17 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 45 1 4 = 23 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 45 1 5 = 1 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 45 1 6 = 19 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 45 1 6 = slopeOrbit 45 1 1
    rw [e6, e1]
  · have hsub : (Finset.Icc 1 5).filter
        (fun j => canonGap 45 (slopeOrbit 45 1 j) = 1) ⊆ ({2, 4} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exfalso
        rw [e1] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e3] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (45, 1)`: the per-pair threshold — period `5`, band-1
count `2`; the half-density scalar `2·(2·c0·runDyadicMult) ≤ (c⋆ξ/24)·5`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_45_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hcW : 5 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((2 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (5 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 5) (b1 := 2)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_45_1.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_45_1.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (45, 2)`: period `5`, cycle `19 → 31 → 17 → 23 → 1`, bands `2, 1, 2, 1, 6` — band-1 count `≤ 2`. -/
private theorem runCycle_45_2 :
    slopeOrbit 45 2 (1 + 5) = slopeOrbit 45 2 1
      ∧ ((Finset.Icc 1 5).filter
          (fun j => canonGap 45 (slopeOrbit 45 2 j) = 1)).card ≤ 2 := by
  have e0 : slopeOrbit 45 2 0 = 2 := rfl
  have e1 : slopeOrbit 45 2 1 = 19 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 45 2 2 = 31 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 45 2 3 = 17 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 45 2 4 = 23 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 45 2 5 = 1 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 45 2 6 = 19 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 45 2 6 = slopeOrbit 45 2 1
    rw [e6, e1]
  · have hsub : (Finset.Icc 1 5).filter
        (fun j => canonGap 45 (slopeOrbit 45 2 j) = 1) ⊆ ({2, 4} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exfalso
        rw [e1] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e3] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (45, 2)`: the per-pair threshold — period `5`, band-1
count `2`; the half-density scalar `2·(2·c0·runDyadicMult) ≤ (c⋆ξ/24)·5`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_45_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (hcW : 5 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((2 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (5 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 5) (b1 := 2)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_45_2.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_45_2.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (45, 4)`: period `5`, cycle `19 → 31 → 17 → 23 → 1`, bands `2, 1, 2, 1, 6` — band-1 count `≤ 2`. -/
private theorem runCycle_45_4 :
    slopeOrbit 45 4 (1 + 5) = slopeOrbit 45 4 1
      ∧ ((Finset.Icc 1 5).filter
          (fun j => canonGap 45 (slopeOrbit 45 4 j) = 1)).card ≤ 2 := by
  have e0 : slopeOrbit 45 4 0 = 4 := rfl
  have e1 : slopeOrbit 45 4 1 = 19 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 45 4 2 = 31 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 45 4 3 = 17 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 45 4 4 = 23 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 45 4 5 = 1 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 45 4 6 = 19 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 45 4 6 = slopeOrbit 45 4 1
    rw [e6, e1]
  · have hsub : (Finset.Icc 1 5).filter
        (fun j => canonGap 45 (slopeOrbit 45 4 j) = 1) ⊆ ({2, 4} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exfalso
        rw [e1] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e3] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (45, 4)`: the per-pair threshold — period `5`, band-1
count `2`; the half-density scalar `2·(2·c0·runDyadicMult) ≤ (c⋆ξ/24)·5`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_45_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 4)
    (hcW : 5 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((2 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (5 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 5) (b1 := 2)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_45_4.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_45_4.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (45, 7)`: period `7`, cycle `11 → 43 → 41 → 37 → 29 → 13 → 7`, bands `3, 1, 1, 1, 1, 2, 3` — band-1 count `≤ 4`. -/
private theorem runCycle_45_7 :
    slopeOrbit 45 7 (1 + 7) = slopeOrbit 45 7 1
      ∧ ((Finset.Icc 1 7).filter
          (fun j => canonGap 45 (slopeOrbit 45 7 j) = 1)).card ≤ 4 := by
  have e0 : slopeOrbit 45 7 0 = 7 := rfl
  have e1 : slopeOrbit 45 7 1 = 11 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 45 7 2 = 43 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 45 7 3 = 41 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 45 7 4 = 37 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 45 7 5 = 29 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 45 7 6 = 13 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 45 7 7 = 7 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 45 7 8 = 11 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 45 7 8 = slopeOrbit 45 7 1
    rw [e8, e1]
  · have hsub : (Finset.Icc 1 7).filter
        (fun j => canonGap 45 (slopeOrbit 45 7 j) = 1) ⊆ ({2, 3, 4, 5} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exfalso
        rw [e1] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e7] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (45, 7)`: the per-pair threshold — period `7`, band-1
count `4`; the half-density scalar `2·(4·c0·runDyadicMult) ≤ (c⋆ξ/24)·7`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_45_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 7)
    (hcW : 7 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((4 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (7 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 7) (b1 := 4)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_45_7.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_45_7.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (45, 22)`: period `7`, cycle `43 → 41 → 37 → 29 → 13 → 7 → 11`, bands `1, 1, 1, 1, 2, 3, 3` — band-1 count `≤ 4`. -/
private theorem runCycle_45_22 :
    slopeOrbit 45 22 (1 + 7) = slopeOrbit 45 22 1
      ∧ ((Finset.Icc 1 7).filter
          (fun j => canonGap 45 (slopeOrbit 45 22 j) = 1)).card ≤ 4 := by
  have e0 : slopeOrbit 45 22 0 = 22 := rfl
  have e1 : slopeOrbit 45 22 1 = 43 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 45 22 2 = 41 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 45 22 3 = 37 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 45 22 4 = 29 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 45 22 5 = 13 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 45 22 6 = 7 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 45 22 7 = 11 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 45 22 8 = 43 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 45 22 8 = slopeOrbit 45 22 1
    rw [e8, e1]
  · have hsub : (Finset.Icc 1 7).filter
        (fun j => canonGap 45 (slopeOrbit 45 22 j) = 1) ⊆ ({1, 2, 3, 4} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e7] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (45, 22)`: the per-pair threshold — period `7`, band-1
count `4`; the half-density scalar `2·(4·c0·runDyadicMult) ≤ (c⋆ξ/24)·7`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_45_22 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 22)
    (hcW : 7 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((4 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (7 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 7) (b1 := 4)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_45_22.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_45_22.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (47, 23)`: period `14`, cycle `45 → 43 → 39 → 31 → 15 → 13 → 5 → 33 → 19 → 29 → 11 → 41 → 35 → 23`, bands `1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 2` — band-1 count `≤ 8`. -/
private theorem runCycle_47_23 :
    slopeOrbit 47 23 (1 + 14) = slopeOrbit 47 23 1
      ∧ ((Finset.Icc 1 14).filter
          (fun j => canonGap 47 (slopeOrbit 47 23 j) = 1)).card ≤ 8 := by
  have e0 : slopeOrbit 47 23 0 = 23 := rfl
  have e1 : slopeOrbit 47 23 1 = 45 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 47 23 2 = 43 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 47 23 3 = 39 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 47 23 4 = 31 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 47 23 5 = 15 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 47 23 6 = 13 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 47 23 7 = 5 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 47 23 8 = 33 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 47 23 9 = 19 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 47 23 10 = 29 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 47 23 11 = 11 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 47 23 12 = 41 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 47 23 13 = 35 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 47 23 14 = 23 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 47 23 15 = 45 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 47 23 15 = slopeOrbit 47 23 1
    rw [e15, e1]
  · have hsub : (Finset.Icc 1 14).filter
        (fun j => canonGap 47 (slopeOrbit 47 23 j) = 1) ⊆ ({1, 2, 3, 4, 8, 10, 12, 13} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e7] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e9] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e11] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · exfalso
        rw [e14] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (47, 23)`: the per-pair threshold — period `14`, band-1
count `8`; the half-density scalar `2·(8·c0·runDyadicMult) ≤ (c⋆ξ/24)·14`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_47_23 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 47) (hK : (class1SlopeDatum ctx).K₀ = 23)
    (hcW : 14 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((8 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (14 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 14) (b1 := 8)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_47_23.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_47_23.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (49, 3)`: period `11`, cycle `47 → 45 → 41 → 33 → 17 → 19 → 27 → 5 → 31 → 13 → 3`, bands `1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5` — band-1 count `≤ 6`. -/
private theorem runCycle_49_3 :
    slopeOrbit 49 3 (1 + 11) = slopeOrbit 49 3 1
      ∧ ((Finset.Icc 1 11).filter
          (fun j => canonGap 49 (slopeOrbit 49 3 j) = 1)).card ≤ 6 := by
  have e0 : slopeOrbit 49 3 0 = 3 := rfl
  have e1 : slopeOrbit 49 3 1 = 47 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 49 3 2 = 45 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 49 3 3 = 41 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 49 3 4 = 33 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 49 3 5 = 17 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 49 3 6 = 19 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 49 3 7 = 27 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 49 3 8 = 5 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 49 3 9 = 31 :=
    slopeOrbit_step_eval 8 3 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 49 3 10 = 13 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 49 3 11 = 3 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 49 3 12 = 47 :=
    slopeOrbit_step_eval 11 4 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 49 3 12 = slopeOrbit 49 3 1
    rw [e12, e1]
  · have hsub : (Finset.Icc 1 11).filter
        (fun j => canonGap 49 (slopeOrbit 49 3 j) = 1) ⊆ ({1, 2, 3, 4, 7, 9} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e8] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e10] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e11] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (49, 3)`: the per-pair threshold — period `11`, band-1
count `6`; the half-density scalar `2·(6·c0·runDyadicMult) ≤ (c⋆ξ/24)·11`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_49_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 49) (hK : (class1SlopeDatum ctx).K₀ = 3)
    (hcW : 11 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((6 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (11 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 11) (b1 := 6)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_49_3.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_49_3.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (49, 24)`: period `11`, cycle `47 → 45 → 41 → 33 → 17 → 19 → 27 → 5 → 31 → 13 → 3`, bands `1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5` — band-1 count `≤ 6`. -/
private theorem runCycle_49_24 :
    slopeOrbit 49 24 (1 + 11) = slopeOrbit 49 24 1
      ∧ ((Finset.Icc 1 11).filter
          (fun j => canonGap 49 (slopeOrbit 49 24 j) = 1)).card ≤ 6 := by
  have e0 : slopeOrbit 49 24 0 = 24 := rfl
  have e1 : slopeOrbit 49 24 1 = 47 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 49 24 2 = 45 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 49 24 3 = 41 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 49 24 4 = 33 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 49 24 5 = 17 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 49 24 6 = 19 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 49 24 7 = 27 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 49 24 8 = 5 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 49 24 9 = 31 :=
    slopeOrbit_step_eval 8 3 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 49 24 10 = 13 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 49 24 11 = 3 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 49 24 12 = 47 :=
    slopeOrbit_step_eval 11 4 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 49 24 12 = slopeOrbit 49 24 1
    rw [e12, e1]
  · have hsub : (Finset.Icc 1 11).filter
        (fun j => canonGap 49 (slopeOrbit 49 24 j) = 1) ⊆ ({1, 2, 3, 4, 7, 9} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e8] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e10] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e11] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (49, 24)`: the per-pair threshold — period `11`, band-1
count `6`; the half-density scalar `2·(6·c0·runDyadicMult) ≤ (c⋆ξ/24)·11`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_49_24 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 49) (hK : (class1SlopeDatum ctx).K₀ = 24)
    (hcW : 11 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((6 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (11 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 11) (b1 := 6)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_49_24.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_49_24.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (51, 1)`: period `2`, cycle `13 → 1`, bands `2, 6` — band-`{1,4}`-free. -/
private theorem runCycle_51_1 :
    slopeOrbit 51 1 (1 + 2) = slopeOrbit 51 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 →
          canonGap 51 (slopeOrbit 51 1 j) ≠ 1
            ∧ canonGap 51 (slopeOrbit 51 1 j) ≠ 4 := by
  have e0 : slopeOrbit 51 1 0 = 1 := rfl
  have e1 : slopeOrbit 51 1 1 = 13 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 51 1 2 = 1 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 51 1 3 = 13 :=
    slopeOrbit_step_eval 2 5 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 51 1 3 = slopeOrbit 51 1 1
    rw [e3, e1]
  · intro j hj1 hjc
    interval_cases j
    · rw [e1]
      exact ⟨canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num),
        canonGap_ne_four_of_band (Or.inl (by norm_num))⟩
    · rw [e2]
      exact ⟨canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num),
        canonGap_ne_four_of_band (Or.inr (by norm_num))⟩

/-- `(q, K₀) = (51, 1)` closes the capstone inequality OUTRIGHT (band-`{1,4}`-free cycle). -/
theorem runNumericIneq_of_datum_51_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 51) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    RunNumericIneq ctx := by
  refine runNumericIneq_of_cycle_band_free ctx (c := 2) (by norm_num) ?_ ?_
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_51_1.1
  · rw [hq, hK]
    exact runCycle_51_1.2

/-- `(q, K₀) = (51, 1)` settles `Class5CycleNumericCloses` unconditionally (count `0`). -/
theorem class5CycleNumericCloses_of_datum_51_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 51) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    Class5CycleNumericCloses ctx := by
  refine class5CycleNumericCloses_of_cycle_band_free ctx (c := 2) (by norm_num) ?_ ?_
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_51_1.1
  · rw [hq, hK]
    exact runCycle_51_1.2

/-- `(q, K₀) = (51, 8)`: period `2`, cycle `13 → 1`, bands `2, 6` — band-`{1,4}`-free. -/
private theorem runCycle_51_8 :
    slopeOrbit 51 8 (1 + 2) = slopeOrbit 51 8 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 →
          canonGap 51 (slopeOrbit 51 8 j) ≠ 1
            ∧ canonGap 51 (slopeOrbit 51 8 j) ≠ 4 := by
  have e0 : slopeOrbit 51 8 0 = 8 := rfl
  have e1 : slopeOrbit 51 8 1 = 13 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 51 8 2 = 1 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 51 8 3 = 13 :=
    slopeOrbit_step_eval 2 5 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 51 8 3 = slopeOrbit 51 8 1
    rw [e3, e1]
  · intro j hj1 hjc
    interval_cases j
    · rw [e1]
      exact ⟨canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num),
        canonGap_ne_four_of_band (Or.inl (by norm_num))⟩
    · rw [e2]
      exact ⟨canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num),
        canonGap_ne_four_of_band (Or.inr (by norm_num))⟩

/-- `(q, K₀) = (51, 8)` closes the capstone inequality OUTRIGHT (band-`{1,4}`-free cycle). -/
theorem runNumericIneq_of_datum_51_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 51) (hK : (class1SlopeDatum ctx).K₀ = 8) :
    RunNumericIneq ctx := by
  refine runNumericIneq_of_cycle_band_free ctx (c := 2) (by norm_num) ?_ ?_
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_51_8.1
  · rw [hq, hK]
    exact runCycle_51_8.2

/-- `(q, K₀) = (51, 8)` settles `Class5CycleNumericCloses` unconditionally (count `0`). -/
theorem class5CycleNumericCloses_of_datum_51_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 51) (hK : (class1SlopeDatum ctx).K₀ = 8) :
    Class5CycleNumericCloses ctx := by
  refine class5CycleNumericCloses_of_cycle_band_free ctx (c := 2) (by norm_num) ?_ ?_
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_51_8.1
  · rw [hq, hK]
    exact runCycle_51_8.2

/-- `(q, K₀) = (51, 25)`: period `6`, cycle `49 → 47 → 43 → 35 → 19 → 25`, bands `1, 1, 1, 1, 2, 2` — band-1 count `≤ 4`. -/
private theorem runCycle_51_25 :
    slopeOrbit 51 25 (1 + 6) = slopeOrbit 51 25 1
      ∧ ((Finset.Icc 1 6).filter
          (fun j => canonGap 51 (slopeOrbit 51 25 j) = 1)).card ≤ 4 := by
  have e0 : slopeOrbit 51 25 0 = 25 := rfl
  have e1 : slopeOrbit 51 25 1 = 49 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 51 25 2 = 47 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 51 25 3 = 43 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 51 25 4 = 35 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 51 25 5 = 19 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 51 25 6 = 25 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 51 25 7 = 49 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 51 25 7 = slopeOrbit 51 25 1
    rw [e7, e1]
  · have hsub : (Finset.Icc 1 6).filter
        (fun j => canonGap 51 (slopeOrbit 51 25 j) = 1) ⊆ ({1, 2, 3, 4} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (51, 25)`: the per-pair threshold — period `6`, band-1
count `4`; the half-density scalar `2·(4·c0·runDyadicMult) ≤ (c⋆ξ/24)·6`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_51_25 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 51) (hK : (class1SlopeDatum ctx).K₀ = 25)
    (hcW : 6 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((4 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (6 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 6) (b1 := 4)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_51_25.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_51_25.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (53, 26)`: period `26`, cycle `51 → 49 → 45 → 37 → 21 → 31 → 9 → 19 → 23 → 39 → 25 → 47 → 41 → 29 → 5 → 27 → 1 → 11 → 35 → 17 → 15 → 7 → 3 → 43 → 33 → 13`, bands `1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4, 1, 6, 3, 1, 2, 2, 3, 5, 1, 1, 3` — band-1 count `≤ 13`. -/
private theorem runCycle_53_26 :
    slopeOrbit 53 26 (1 + 26) = slopeOrbit 53 26 1
      ∧ ((Finset.Icc 1 26).filter
          (fun j => canonGap 53 (slopeOrbit 53 26 j) = 1)).card ≤ 13 := by
  have e0 : slopeOrbit 53 26 0 = 26 := rfl
  have e1 : slopeOrbit 53 26 1 = 51 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 53 26 2 = 49 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 53 26 3 = 45 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 53 26 4 = 37 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 53 26 5 = 21 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 53 26 6 = 31 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 53 26 7 = 9 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 53 26 8 = 19 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 53 26 9 = 23 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 53 26 10 = 39 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 53 26 11 = 25 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 53 26 12 = 47 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 53 26 13 = 41 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 53 26 14 = 29 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 53 26 15 = 5 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 53 26 16 = 27 :=
    slopeOrbit_step_eval 15 3 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 53 26 17 = 1 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 53 26 18 = 11 :=
    slopeOrbit_step_eval 17 5 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 53 26 19 = 35 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 53 26 20 = 17 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 53 26 21 = 15 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 53 26 22 = 7 :=
    slopeOrbit_step_eval 21 1 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 53 26 23 = 3 :=
    slopeOrbit_step_eval 22 2 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 53 26 24 = 43 :=
    slopeOrbit_step_eval 23 4 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 53 26 25 = 33 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 53 26 26 = 13 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 53 26 27 = 51 :=
    slopeOrbit_step_eval 26 2 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 53 26 27 = slopeOrbit 53 26 1
    rw [e27, e1]
  · have hsub : (Finset.Icc 1 26).filter
        (fun j => canonGap 53 (slopeOrbit 53 26 j) = 1) ⊆ ({1, 2, 3, 4, 6, 10, 12, 13, 14, 16, 19, 24, 25} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e7] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e8] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e9] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e11] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · decide
      · exfalso
        rw [e15] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e17] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e18] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e20] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e21] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e22] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e23] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · exfalso
        rw [e26] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (53, 26)`: the per-pair threshold — period `26`, band-1
count `13`; the half-density scalar `2·(13·c0·runDyadicMult) ≤ (c⋆ξ/24)·26`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_53_26 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 53) (hK : (class1SlopeDatum ctx).K₀ = 26)
    (hcW : 26 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((13 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (26 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 26) (b1 := 13)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_53_26.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_53_26.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (55, 2)`: period `8`, cycle `9 → 17 → 13 → 49 → 43 → 31 → 7 → 1`, bands `3, 2, 3, 1, 1, 1, 3, 6` — band-1 count `≤ 3`. -/
private theorem runCycle_55_2 :
    slopeOrbit 55 2 (1 + 8) = slopeOrbit 55 2 1
      ∧ ((Finset.Icc 1 8).filter
          (fun j => canonGap 55 (slopeOrbit 55 2 j) = 1)).card ≤ 3 := by
  have e0 : slopeOrbit 55 2 0 = 2 := rfl
  have e1 : slopeOrbit 55 2 1 = 9 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 55 2 2 = 17 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 55 2 3 = 13 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 55 2 4 = 49 :=
    slopeOrbit_step_eval 3 2 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 55 2 5 = 43 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 55 2 6 = 31 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 55 2 7 = 7 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 55 2 8 = 1 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 55 2 9 = 9 :=
    slopeOrbit_step_eval 8 5 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 55 2 9 = slopeOrbit 55 2 1
    rw [e9, e1]
  · have hsub : (Finset.Icc 1 8).filter
        (fun j => canonGap 55 (slopeOrbit 55 2 j) = 1) ⊆ ({4, 5, 6} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exfalso
        rw [e1] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e2] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e3] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · decide
      · exfalso
        rw [e7] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e8] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (55, 2)`: the per-pair threshold — period `8`, band-1
count `3`; the half-density scalar `2·(3·c0·runDyadicMult) ≤ (c⋆ξ/24)·8`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_55_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 55) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (hcW : 8 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((3 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (8 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 8) (b1 := 3)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_55_2.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_55_2.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (55, 5)`: period `5`, cycle `25 → 45 → 35 → 15 → 5`, bands `2, 1, 1, 2, 4` — band-1 count `≤ 2`. -/
private theorem runCycle_55_5 :
    slopeOrbit 55 5 (1 + 5) = slopeOrbit 55 5 1
      ∧ ((Finset.Icc 1 5).filter
          (fun j => canonGap 55 (slopeOrbit 55 5 j) = 1)).card ≤ 2 := by
  have e0 : slopeOrbit 55 5 0 = 5 := rfl
  have e1 : slopeOrbit 55 5 1 = 25 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 55 5 2 = 45 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 55 5 3 = 35 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 55 5 4 = 15 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 55 5 5 = 5 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 55 5 6 = 25 :=
    slopeOrbit_step_eval 5 3 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 55 5 6 = slopeOrbit 55 5 1
    rw [e6, e1]
  · have hsub : (Finset.Icc 1 5).filter
        (fun j => canonGap 55 (slopeOrbit 55 5 j) = 1) ⊆ ({2, 3} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exfalso
        rw [e1] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · exfalso
        rw [e4] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (55, 5)`: the per-pair threshold — period `5`, band-1
count `2`; the half-density scalar `2·(2·c0·runDyadicMult) ≤ (c⋆ξ/24)·5`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_55_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 55) (hK : (class1SlopeDatum ctx).K₀ = 5)
    (hcW : 5 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((2 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (5 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 5) (b1 := 2)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_55_5.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_55_5.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (55, 27)`: period `12`, cycle `53 → 51 → 47 → 39 → 23 → 37 → 19 → 21 → 29 → 3 → 41 → 27`, bands `1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2` — band-1 count `≤ 7`. -/
private theorem runCycle_55_27 :
    slopeOrbit 55 27 (1 + 12) = slopeOrbit 55 27 1
      ∧ ((Finset.Icc 1 12).filter
          (fun j => canonGap 55 (slopeOrbit 55 27 j) = 1)).card ≤ 7 := by
  have e0 : slopeOrbit 55 27 0 = 27 := rfl
  have e1 : slopeOrbit 55 27 1 = 53 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 55 27 2 = 51 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 55 27 3 = 47 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 55 27 4 = 39 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 55 27 5 = 23 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 55 27 6 = 37 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 55 27 7 = 19 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 55 27 8 = 21 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 55 27 9 = 29 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 55 27 10 = 3 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 55 27 11 = 41 :=
    slopeOrbit_step_eval 10 4 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 55 27 12 = 27 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 55 27 13 = 53 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 55 27 13 = slopeOrbit 55 27 1
    rw [e13, e1]
  · have hsub : (Finset.Icc 1 12).filter
        (fun j => canonGap 55 (slopeOrbit 55 27 j) = 1) ⊆ ({1, 2, 3, 4, 6, 9, 11} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e7] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e8] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e10] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e12] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (55, 27)`: the per-pair threshold — period `12`, band-1
count `7`; the half-density scalar `2·(7·c0·runDyadicMult) ≤ (c⋆ξ/24)·12`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_55_27 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 55) (hK : (class1SlopeDatum ctx).K₀ = 27)
    (hcW : 12 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((7 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (12 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 12) (b1 := 7)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_55_27.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_55_27.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (57, 1)`: period `9`, cycle `7 → 55 → 53 → 49 → 41 → 25 → 43 → 29 → 1`, bands `4, 1, 1, 1, 1, 2, 1, 1, 6` — band-1 count `≤ 6`. -/
private theorem runCycle_57_1 :
    slopeOrbit 57 1 (1 + 9) = slopeOrbit 57 1 1
      ∧ ((Finset.Icc 1 9).filter
          (fun j => canonGap 57 (slopeOrbit 57 1 j) = 1)).card ≤ 6 := by
  have e0 : slopeOrbit 57 1 0 = 1 := rfl
  have e1 : slopeOrbit 57 1 1 = 7 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 57 1 2 = 55 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 57 1 3 = 53 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 57 1 4 = 49 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 57 1 5 = 41 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 57 1 6 = 25 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 57 1 7 = 43 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 57 1 8 = 29 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 57 1 9 = 1 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 57 1 10 = 7 :=
    slopeOrbit_step_eval 9 5 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 57 1 10 = slopeOrbit 57 1 1
    rw [e10, e1]
  · have hsub : (Finset.Icc 1 9).filter
        (fun j => canonGap 57 (slopeOrbit 57 1 j) = 1) ⊆ ({2, 3, 4, 5, 7, 8} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exfalso
        rw [e1] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e6] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · exfalso
        rw [e9] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (57, 1)`: the per-pair threshold — period `9`, band-1
count `6`; the half-density scalar `2·(6·c0·runDyadicMult) ≤ (c⋆ξ/24)·9`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_57_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hcW : 9 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((6 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (9 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 9) (b1 := 6)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_57_1.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_57_1.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (57, 9)`: period `9`, cycle `15 → 3 → 39 → 21 → 27 → 51 → 45 → 33 → 9`, bands `2, 5, 1, 2, 2, 1, 1, 1, 3` — band-1 count `≤ 4`. -/
private theorem runCycle_57_9 :
    slopeOrbit 57 9 (1 + 9) = slopeOrbit 57 9 1
      ∧ ((Finset.Icc 1 9).filter
          (fun j => canonGap 57 (slopeOrbit 57 9 j) = 1)).card ≤ 4 := by
  have e0 : slopeOrbit 57 9 0 = 9 := rfl
  have e1 : slopeOrbit 57 9 1 = 15 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 57 9 2 = 3 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 57 9 3 = 39 :=
    slopeOrbit_step_eval 2 4 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 57 9 4 = 21 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 57 9 5 = 27 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 57 9 6 = 51 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 57 9 7 = 45 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 57 9 8 = 33 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 57 9 9 = 9 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 57 9 10 = 15 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 57 9 10 = slopeOrbit 57 9 1
    rw [e10, e1]
  · have hsub : (Finset.Icc 1 9).filter
        (fun j => canonGap 57 (slopeOrbit 57 9 j) = 1) ⊆ ({3, 6, 7, 8} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exfalso
        rw [e1] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e2] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e4] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · decide
      · exfalso
        rw [e9] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (57, 9)`: the per-pair threshold — period `9`, band-1
count `4`; the half-density scalar `2·(4·c0·runDyadicMult) ≤ (c⋆ξ/24)·9`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_57_9 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 9)
    (hcW : 9 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((4 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (9 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 9) (b1 := 4)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_57_9.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_57_9.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (57, 28)`: period `9`, cycle `55 → 53 → 49 → 41 → 25 → 43 → 29 → 1 → 7`, bands `1, 1, 1, 1, 2, 1, 1, 6, 4` — band-1 count `≤ 6`. -/
private theorem runCycle_57_28 :
    slopeOrbit 57 28 (1 + 9) = slopeOrbit 57 28 1
      ∧ ((Finset.Icc 1 9).filter
          (fun j => canonGap 57 (slopeOrbit 57 28 j) = 1)).card ≤ 6 := by
  have e0 : slopeOrbit 57 28 0 = 28 := rfl
  have e1 : slopeOrbit 57 28 1 = 55 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 57 28 2 = 53 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 57 28 3 = 49 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 57 28 4 = 41 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 57 28 5 = 25 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 57 28 6 = 43 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 57 28 7 = 29 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 57 28 8 = 1 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 57 28 9 = 7 :=
    slopeOrbit_step_eval 8 5 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 57 28 10 = 55 :=
    slopeOrbit_step_eval 9 3 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 57 28 10 = slopeOrbit 57 28 1
    rw [e10, e1]
  · have hsub : (Finset.Icc 1 9).filter
        (fun j => canonGap 57 (slopeOrbit 57 28 j) = 1) ⊆ ({1, 2, 3, 4, 6, 7} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · exfalso
        rw [e8] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e9] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (57, 28)`: the per-pair threshold — period `9`, band-1
count `6`; the half-density scalar `2·(6·c0·runDyadicMult) ≤ (c⋆ξ/24)·9`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_57_28 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 28)
    (hcW : 9 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((6 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (9 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 9) (b1 := 6)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_57_28.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_57_28.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (59, 29)`: period `29`, cycle `57 → 55 → 51 → 43 → 27 → 49 → 39 → 19 → 17 → 9 → 13 → 45 → 31 → 3 → 37 → 15 → 1 → 5 → 21 → 25 → 41 → 23 → 33 → 7 → 53 → 47 → 35 → 11 → 29`, bands `1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 5, 1, 2, 6, 4, 2, 2, 1, 2, 1, 4, 1, 1, 1, 3, 2` — band-1 count `≤ 14`. -/
private theorem runCycle_59_29 :
    slopeOrbit 59 29 (1 + 29) = slopeOrbit 59 29 1
      ∧ ((Finset.Icc 1 29).filter
          (fun j => canonGap 59 (slopeOrbit 59 29 j) = 1)).card ≤ 14 := by
  have e0 : slopeOrbit 59 29 0 = 29 := rfl
  have e1 : slopeOrbit 59 29 1 = 57 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 59 29 2 = 55 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 59 29 3 = 51 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 59 29 4 = 43 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 59 29 5 = 27 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 59 29 6 = 49 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 59 29 7 = 39 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 59 29 8 = 19 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 59 29 9 = 17 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 59 29 10 = 9 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 59 29 11 = 13 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 59 29 12 = 45 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 59 29 13 = 31 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 59 29 14 = 3 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 59 29 15 = 37 :=
    slopeOrbit_step_eval 14 4 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 59 29 16 = 15 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 59 29 17 = 1 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 59 29 18 = 5 :=
    slopeOrbit_step_eval 17 5 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 59 29 19 = 21 :=
    slopeOrbit_step_eval 18 3 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 59 29 20 = 25 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 59 29 21 = 41 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 59 29 22 = 23 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 59 29 23 = 33 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 59 29 24 = 7 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 59 29 25 = 53 :=
    slopeOrbit_step_eval 24 3 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 59 29 26 = 47 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 59 29 27 = 35 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 59 29 28 = 11 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 59 29 29 = 29 :=
    slopeOrbit_step_eval 28 2 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 59 29 30 = 57 :=
    slopeOrbit_step_eval 29 1 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 59 29 30 = slopeOrbit 59 29 1
    rw [e30, e1]
  · have hsub : (Finset.Icc 1 29).filter
        (fun j => canonGap 59 (slopeOrbit 59 29 j) = 1) ⊆ ({1, 2, 3, 4, 6, 7, 12, 13, 15, 21, 23, 25, 26, 27} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · exfalso
        rw [e8] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e9] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e10] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e11] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · exfalso
        rw [e14] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e16] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e17] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e18] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e19] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e20] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e22] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e24] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · decide
      · exfalso
        rw [e28] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e29] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (59, 29)`: the per-pair threshold — period `29`, band-1
count `14`; the half-density scalar `2·(14·c0·runDyadicMult) ≤ (c⋆ξ/24)·29`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_59_29 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 59) (hK : (class1SlopeDatum ctx).K₀ = 29)
    (hcW : 29 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((14 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (29 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 29) (b1 := 14)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_59_29.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_59_29.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (61, 30)`: period `30`, cycle `59 → 57 → 53 → 45 → 29 → 55 → 49 → 37 → 13 → 43 → 25 → 39 → 17 → 7 → 51 → 41 → 21 → 23 → 31 → 1 → 3 → 35 → 9 → 11 → 27 → 47 → 33 → 5 → 19 → 15`, bands `1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 6, 5, 1, 3, 3, 2, 1, 1, 4, 2, 3` — band-1 count `≤ 15`. -/
private theorem runCycle_61_30 :
    slopeOrbit 61 30 (1 + 30) = slopeOrbit 61 30 1
      ∧ ((Finset.Icc 1 30).filter
          (fun j => canonGap 61 (slopeOrbit 61 30 j) = 1)).card ≤ 15 := by
  have e0 : slopeOrbit 61 30 0 = 30 := rfl
  have e1 : slopeOrbit 61 30 1 = 59 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 61 30 2 = 57 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 61 30 3 = 53 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 61 30 4 = 45 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 61 30 5 = 29 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 61 30 6 = 55 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 61 30 7 = 49 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 61 30 8 = 37 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 61 30 9 = 13 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 61 30 10 = 43 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 61 30 11 = 25 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 61 30 12 = 39 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 61 30 13 = 17 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 61 30 14 = 7 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 61 30 15 = 51 :=
    slopeOrbit_step_eval 14 3 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 61 30 16 = 41 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 61 30 17 = 21 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 61 30 18 = 23 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 61 30 19 = 31 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 61 30 20 = 1 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 61 30 21 = 3 :=
    slopeOrbit_step_eval 20 5 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 61 30 22 = 35 :=
    slopeOrbit_step_eval 21 4 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 61 30 23 = 9 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 61 30 24 = 11 :=
    slopeOrbit_step_eval 23 2 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 61 30 25 = 27 :=
    slopeOrbit_step_eval 24 2 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 61 30 26 = 47 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 61 30 27 = 33 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 61 30 28 = 5 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 61 30 29 = 19 :=
    slopeOrbit_step_eval 28 3 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 61 30 30 = 15 :=
    slopeOrbit_step_eval 29 1 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 61 30 31 = 59 :=
    slopeOrbit_step_eval 30 2 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 61 30 31 = slopeOrbit 61 30 1
    rw [e31, e1]
  · have hsub : (Finset.Icc 1 30).filter
        (fun j => canonGap 61 (slopeOrbit 61 30 j) = 1) ⊆ ({1, 2, 3, 4, 6, 7, 8, 10, 12, 15, 16, 19, 22, 26, 27} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · decide
      · exfalso
        rw [e9] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e11] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e13] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e14] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · exfalso
        rw [e17] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e18] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e20] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e21] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · exfalso
        rw [e23] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e24] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e25] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · decide
      · decide
      · exfalso
        rw [e28] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e29] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e30] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (61, 30)`: the per-pair threshold — period `30`, band-1
count `15`; the half-density scalar `2·(15·c0·runDyadicMult) ≤ (c⋆ξ/24)·30`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_61_30 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 61) (hK : (class1SlopeDatum ctx).K₀ = 30)
    (hcW : 30 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((15 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (30 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 30) (b1 := 15)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_61_30.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_61_30.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (63, 1)`: period `1`, cycle `1`, bands `6` — band-`{1,4}`-free. -/
private theorem runCycle_63_1 :
    slopeOrbit 63 1 (1 + 1) = slopeOrbit 63 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 →
          canonGap 63 (slopeOrbit 63 1 j) ≠ 1
            ∧ canonGap 63 (slopeOrbit 63 1 j) ≠ 4 := by
  have e0 : slopeOrbit 63 1 0 = 1 := rfl
  have e1 : slopeOrbit 63 1 1 = 1 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 1 2 = 1 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 63 1 2 = slopeOrbit 63 1 1
    rw [e2, e1]
  · intro j hj1 hjc
    interval_cases j
    · rw [e1]
      exact ⟨canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num),
        canonGap_ne_four_of_band (Or.inr (by norm_num))⟩

/-- `(q, K₀) = (63, 1)` closes the capstone inequality OUTRIGHT (band-`{1,4}`-free cycle). -/
theorem runNumericIneq_of_datum_63_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    RunNumericIneq ctx := by
  refine runNumericIneq_of_cycle_band_free ctx (c := 1) (by norm_num) ?_ ?_
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_63_1.1
  · rw [hq, hK]
    exact runCycle_63_1.2

/-- `(q, K₀) = (63, 1)` settles `Class5CycleNumericCloses` unconditionally (count `0`). -/
theorem class5CycleNumericCloses_of_datum_63_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    Class5CycleNumericCloses ctx := by
  refine class5CycleNumericCloses_of_cycle_band_free ctx (c := 1) (by norm_num) ?_ ?_
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_63_1.1
  · rw [hq, hK]
    exact runCycle_63_1.2

/-- `(q, K₀) = (63, 3)`: period `2`, cycle `33 → 3`, bands `1, 5` — band-1 count `≤ 1`. -/
private theorem runCycle_63_3 :
    slopeOrbit 63 3 (1 + 2) = slopeOrbit 63 3 1
      ∧ ((Finset.Icc 1 2).filter
          (fun j => canonGap 63 (slopeOrbit 63 3 j) = 1)).card ≤ 1 := by
  have e0 : slopeOrbit 63 3 0 = 3 := rfl
  have e1 : slopeOrbit 63 3 1 = 33 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 3 2 = 3 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 63 3 3 = 33 :=
    slopeOrbit_step_eval 2 4 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 63 3 3 = slopeOrbit 63 3 1
    rw [e3, e1]
  · have hsub : (Finset.Icc 1 2).filter
        (fun j => canonGap 63 (slopeOrbit 63 3 j) = 1) ⊆ ({1} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · exfalso
        rw [e2] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (63, 3)`: the per-pair threshold — period `2`, band-1
count `1`; the half-density scalar `2·(1·c0·runDyadicMult) ≤ (c⋆ξ/24)·2`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_63_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 3)
    (hcW : 2 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((1 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (2 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 2) (b1 := 1)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_63_3.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_63_3.2
  · exact_mod_cast hb1

/-- `(q, K₀) = (63, 4)`: period `1`, cycle `1`, bands `6` — band-`{1,4}`-free. -/
private theorem runCycle_63_4 :
    slopeOrbit 63 4 (1 + 1) = slopeOrbit 63 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 →
          canonGap 63 (slopeOrbit 63 4 j) ≠ 1
            ∧ canonGap 63 (slopeOrbit 63 4 j) ≠ 4 := by
  have e0 : slopeOrbit 63 4 0 = 4 := rfl
  have e1 : slopeOrbit 63 4 1 = 1 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 4 2 = 1 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 63 4 2 = slopeOrbit 63 4 1
    rw [e2, e1]
  · intro j hj1 hjc
    interval_cases j
    · rw [e1]
      exact ⟨canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num),
        canonGap_ne_four_of_band (Or.inr (by norm_num))⟩

/-- `(q, K₀) = (63, 4)` closes the capstone inequality OUTRIGHT (band-`{1,4}`-free cycle). -/
theorem runNumericIneq_of_datum_63_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    RunNumericIneq ctx := by
  refine runNumericIneq_of_cycle_band_free ctx (c := 1) (by norm_num) ?_ ?_
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_63_4.1
  · rw [hq, hK]
    exact runCycle_63_4.2

/-- `(q, K₀) = (63, 4)` settles `Class5CycleNumericCloses` unconditionally (count `0`). -/
theorem class5CycleNumericCloses_of_datum_63_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    Class5CycleNumericCloses ctx := by
  refine class5CycleNumericCloses_of_cycle_band_free ctx (c := 1) (by norm_num) ?_ ?_
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_63_4.1
  · rw [hq, hK]
    exact runCycle_63_4.2

/-- `(q, K₀) = (63, 10)`: period `2`, cycle `17 → 5`, bands `2, 4` — band-1 count `≤ 0`. -/
private theorem runCycle_63_10 :
    slopeOrbit 63 10 (1 + 2) = slopeOrbit 63 10 1
      ∧ ((Finset.Icc 1 2).filter
          (fun j => canonGap 63 (slopeOrbit 63 10 j) = 1)).card ≤ 0 := by
  have e0 : slopeOrbit 63 10 0 = 10 := rfl
  have e1 : slopeOrbit 63 10 1 = 17 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 10 2 = 5 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 63 10 3 = 17 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 63 10 3 = slopeOrbit 63 10 1
    rw [e3, e1]
  · have hsub : (Finset.Icc 1 2).filter
        (fun j => canonGap 63 (slopeOrbit 63 10 j) = 1) ⊆ (∅ : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · exfalso
        rw [e1] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
      · exfalso
        rw [e2] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (63, 10)`: band-4-only cycle (`b1 = 0`) — the band-1 scalar
holds for FREE; only the heavy-span scalar remains. -/
theorem class5BandHeavy_of_datum_63_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10)
    (hcW : 2 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 2) (b1 := 0)
    (by norm_num) ?_ hcW ?_ (run_b1_zero_scalar _ _) hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_63_10.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_63_10.2

/-- `(q, K₀) = (63, 31)`: period `5`, cycle `61 → 59 → 55 → 47 → 31`, bands `1, 1, 1, 1, 2` — band-1 count `≤ 4`. -/
private theorem runCycle_63_31 :
    slopeOrbit 63 31 (1 + 5) = slopeOrbit 63 31 1
      ∧ ((Finset.Icc 1 5).filter
          (fun j => canonGap 63 (slopeOrbit 63 31 j) = 1)).card ≤ 4 := by
  have e0 : slopeOrbit 63 31 0 = 31 := rfl
  have e1 : slopeOrbit 63 31 1 = 61 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 31 2 = 59 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 63 31 3 = 55 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 63 31 4 = 47 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 63 31 5 = 31 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 63 31 6 = 61 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 63 31 6 = slopeOrbit 63 31 1
    rw [e6, e1]
  · have hsub : (Finset.Icc 1 5).filter
        (fun j => canonGap 63 (slopeOrbit 63 31 j) = 1) ⊆ ({1, 2, 3, 4} : Finset ℕ) := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hjc⟩, hband⟩ := hj
      interval_cases j
      · decide
      · decide
      · decide
      · decide
      · exfalso
        rw [e5] at hband
        exact canonGap_ne_one_of_two_mul_le (by norm_num) (by norm_num) hband
    exact le_trans (Finset.card_le_card hsub) (by decide)

/-- `(q, K₀) = (63, 31)`: the per-pair threshold — period `5`, band-1
count `4`; the half-density scalar `2·(4·c0·runDyadicMult) ≤ (c⋆ξ/24)·5`
plus the heavy-span scalar close the context. -/
theorem class5BandHeavy_of_datum_63_31 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 31)
    (hcW : 5 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hb1 : 2 * ((4 : ℝ) * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (5 : ℝ))
    (hheavy : RunHeavyNumeric ctx) :
    Class5BandHeavyNumericCloses ctx := by
  refine class5BandHeavyCloses_of_period_count ctx (c := 5) (b1 := 4)
    (by norm_num) ?_ hcW ?_ ?_ hheavy
  · rw [hq, hK]
    exact slopeOrbit_period_of_return runCycle_63_31.1
  · rw [class5Band1CycleBand_congr ctx hq hK]
    exact runCycle_63_31.2
  · exact_mod_cast hb1

/-! ## Part 8.  The datum verdict on odd `q < 64` -/

/-- The fifty-four divisor-pin pairs on odd `q < 64` whose cycles carry band-1
or band-4 residues (the six band-`{1,4}`-free pairs are excluded — they close
outright). -/
def runBandCarryingPairs : List (ℕ × ℕ) :=
  [(5, 2), (7, 3), (9, 1), (9, 4), (11, 5), (13, 6), (15, 1), (15, 2), (15, 7), (17, 8), (19, 9), (21, 1), (21, 10), (23, 11), (25, 2), (25, 12), (27, 1), (27, 4), (27, 13), (29, 14), (31, 15), (33, 1), (33, 5), (33, 16), (35, 2), (35, 3), (35, 17), (37, 18), (39, 1), (39, 6), (39, 19), (41, 20), (43, 21), (45, 1), (45, 2), (45, 4), (45, 7), (45, 22), (47, 23), (49, 3), (49, 24), (51, 25), (53, 26), (55, 2), (55, 5), (55, 27), (57, 1), (57, 9), (57, 28), (59, 29), (61, 30), (63, 3), (63, 10), (63, 31)]

/-- The six band-`{1,4}`-free pairs settle `Class5CycleNumericCloses`
unconditionally. -/
theorem class5CycleNumericCloses_of_free_datum (ctx : ActualFailureContext)
    (h : ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1)
      ∨ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3)
      ∨ ((class1SlopeDatum ctx).q = 51 ∧ (class1SlopeDatum ctx).K₀ = 1)
      ∨ ((class1SlopeDatum ctx).q = 51 ∧ (class1SlopeDatum ctx).K₀ = 8)
      ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 1)
      ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 4)) :
    Class5CycleNumericCloses ctx := by
  rcases h with h | h | h | h | h | h
  · exact class5CycleNumericCloses_of_datum_3_1 ctx h.1 h.2
  · exact class5CycleNumericCloses_of_datum_21_3 ctx h.1 h.2
  · exact class5CycleNumericCloses_of_datum_51_1 ctx h.1 h.2
  · exact class5CycleNumericCloses_of_datum_51_8 ctx h.1 h.2
  · exact class5CycleNumericCloses_of_datum_63_1 ctx h.1 h.2
  · exact class5CycleNumericCloses_of_datum_63_4 ctx h.1 h.2

/-- **The complete datum verdict on odd `q < 64`**: every actual context with
`q < 64` either settles `Class5CycleNumericCloses` outright (band-`{1,4}`-free
cycle) or its datum is one of the fifty-four explicitly enumerated band-carrying
pairs (each with a certified per-pair threshold `class5BandHeavy_of_datum_*`). -/
theorem runDatum_lt64_verdict (ctx : ActualFailureContext)
    (h64 : (class1SlopeDatum ctx).q < 64) :
    Class5CycleNumericCloses ctx
      ∨ ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
          ∈ runBandCarryingPairs := by
  have h3 := runDatum_q_ge_three ctx
  have hK1 := (class1SlopeDatum ctx).hK₀_pos
  have h2K := class1SlopeDatum_two_K₀_lt ctx
  have hdvd := class0_datum_dvd ctx
  obtain ⟨t, ht⟩ := (class1SlopeDatum ctx).hq_odd
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 16 with h16 | h16
  · rcases datum_low_window_pairs (class1SlopeDatum ctx).hq_odd hK1 h2K hdvd
      h3 h16 with
      h | h | h | h | h | h | h | h | h | h
    · exact Or.inl (class5CycleNumericCloses_of_datum_3_1 ctx h.1 h.2)
    · exact Or.inr (by rw [h.1, h.2]; decide)
    · exact Or.inr (by rw [h.1, h.2]; decide)
    · exact Or.inr (by rw [h.1, h.2]; decide)
    · exact Or.inr (by rw [h.1, h.2]; decide)
    · exact Or.inr (by rw [h.1, h.2]; decide)
    · exact Or.inr (by rw [h.1, h.2]; decide)
    · exact Or.inr (by rw [h.1, h.2]; decide)
    · exact Or.inr (by rw [h.1, h.2]; decide)
    · exact Or.inr (by rw [h.1, h.2]; decide)
  · rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 32 with h32 | h32
    · have h17 : 17 ≤ (class1SlopeDatum ctx).q := by omega
      rcases datum_mid_window_pairs (class1SlopeDatum ctx).hq_odd hK1 h2K hdvd
        h17 h32 with
        h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inr (by rw [h.1, h.2]; decide)
      · exact Or.inr (by rw [h.1, h.2]; decide)
      · exact Or.inr (by rw [h.1, h.2]; decide)
      · exact Or.inl (class5CycleNumericCloses_of_datum_21_3 ctx h.1 h.2)
      · exact Or.inr (by rw [h.1, h.2]; decide)
      · exact Or.inr (by rw [h.1, h.2]; decide)
      · exact Or.inr (by rw [h.1, h.2]; decide)
      · exact Or.inr (by rw [h.1, h.2]; decide)
      · exact Or.inr (by rw [h.1, h.2]; decide)
      · exact Or.inr (by rw [h.1, h.2]; decide)
      · exact Or.inr (by rw [h.1, h.2]; decide)
      · exact Or.inr (by rw [h.1, h.2]; decide)
      · exact Or.inr (by rw [h.1, h.2]; decide)
    · rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 48 with h48 | h48
      · rcases datum_upper_window_pairs (class1SlopeDatum ctx).hq_odd hK1 h2K hdvd
          h32 h48 with
          h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
      · rcases datum_top_window_pairs (class1SlopeDatum ctx).hq_odd hK1 h2K hdvd
          h48 h64 with
          h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inl (class5CycleNumericCloses_of_datum_51_1 ctx h.1 h.2)
        · exact Or.inl (class5CycleNumericCloses_of_datum_51_8 ctx h.1 h.2)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inl (class5CycleNumericCloses_of_datum_63_1 ctx h.1 h.2)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inl (class5CycleNumericCloses_of_datum_63_4 ctx h.1 h.2)
        · exact Or.inr (by rw [h.1, h.2]; decide)
        · exact Or.inr (by rw [h.1, h.2]; decide)

/-! ## Part 9.  Honest status -/

/-- Machine-readable status of the Run / class-5 cycle-numeric closure. -/
def runCycleNumericClosureStatus : List String :=
  [ "SUBJECT: the run residual RunNumericSettlementHyp (RunNumericSettlement.lean) - " ++
      "per r >= 1 ctx, a period c with c0 * (#class5CycleBand * ceil(W/c)) * " ++
      "runDyadicMult <= (cStar*xi/12) * #supportShell. This module builds the strictly " ++
      "smaller successor by splitting the class-5 fibre along mem_class5Fibre_iff: " ++
      "band 1 (q < 2K on the orbit) vs heavy band 4 (gap floor 130L+64 <= 64*gW).",
    "ENGINE (band-1 count, NEW): class5Band1CycleBand (band-1-ONLY residues of one " ++
      "period) and class5Band1Fibre_card_le_cycleDensity - the band-1 part of fibre5 " ++
      "injects into (band-1 residues) x (window blocks), #fibre5^{band1} <= " ++
      "#class5Band1CycleBand * ceil(W/c). Strictly sharper than the proved band-{1,4} " ++
      "count whenever the cycle carries band-4 residues.",
    "ENGINE (heavy mass, NEW): class5HeavyFibre (class-5 starts with the heavy floor " ++
      "130L+64 <= 64*gW) and class5HeavyFibre_card_mul_le_span - UNCONDITIONAL: " ++
      "#heavy * (130L+64) <= (r+1) * 64 * (a(i+W+r) - a(i)) = runHeavySpanBudget, by " ++
      "the sliding-window telescoping engine slidingWindow_card_mul_le_span " ++
      "(ReturnClass4CycleClosure). Total split: class5Fibre_card_le_band1_add_heavy " ++
      "(#fibre5 <= b1-density + #heavy; existential form at some c <= q).",
    "ROUNDING (exact, NEW): class5HalfDensityRounding - 2*(b1*c0*M) <= T*c with " ++
      "c <= W gives c0*(b1*ceil(W/c))*M <= T*W (the real form of " ++
      "towerHalfDensity_rounding; ceil loses at most one period, absorbed by the " ++
      "factor-2 slack); class5HeavySpanRounding - #heavy*H <= S and c0*M*S <= T*W*H " ++
      "give c0*#heavy*M <= T*W. Engine runNumericIneq_of_band1_heavy_counted splits " ++
      "the Section 26 budget cStar*xi/12 = cStar*xi/24 + cStar*xi/24.",
    "DATUM ENUMERATION (odd q < 64, NEW windows): the divisor pin (2K0+1) | q " ++
      "(class0_datum_dvd from class1SlopeDatum_H_dvd) with 1 <= K0, 2K0 < q admits " ++
      "EXACTLY 60 pairs: datum_low_window_pairs (3 <= q < 16, ten pairs) and " ++
      "datum_top_window_pairs (48 <= q < 64, nineteen pairs) NEW; mid/upper windows " ++
      "reused from ChernoffClass0DatumClosure. Verdict runDatum_lt64_verdict: every " ++
      "q < 64 ctx closes outright or its datum is one of the 54 runBandCarryingPairs.",
    "CLOSED OUTRIGHT (6 band-{1,4}-free pairs, unconditional): (3,1), (21,3), " ++
      "(51,1), (51,8), (63,1), (63,4) - runNumericIneq_of_datum_* via " ++
      "runNumericIneq_of_cycle_band_free, plus Class5CycleNumericCloses versions " ++
      "(count 0) feeding the settlement hypothesis; (21,3) re-derives the proved " ++
      "q21_K3 family through the table route.",
    "PER-PAIR THRESHOLDS (51 band-1 pairs + 3 band-4-only pairs, certified counts): " ++
      "class5BandHeavy_of_datum_* - per pair, the certified period c and band-1 " ++
      "count b1 reduce the context to the two scalars (half-density band-1 numeric " ++
      "2*(b1*c0*runDyadicMult) <= (cStar*xi/24)*c with c <= W, plus the heavy-span " ++
      "numeric RunHeavyNumeric). Band-4-only pairs (15,1), (15,2), (63,10) have " ++
      "b1 = 0: the band-1 scalar holds for FREE (run_b1_zero_scalar) - on the (15,1) " ++
      "family the OLD full count was vacuous (b = c), the successor is strictly " ++
      "weaker there. Per-pair (c, b1) data are recorded in the runCycle_* " ++
      "docstrings (largest periods: (53,26) c=26 b1=13, (59,29) c=29 b1=14, " ++
      "(61,30) c=30 b1=15).",
    "SUCCESSOR (strictly smaller, NEW): Class5BandHeavyNumericCloses ctx := EXISTS " ++
      "c, period AND c <= W AND the two cStar*xi/24 scalars; " ++
      "RunCycleNumericSettlementHyp := forall ctx, 1 <= r -> " ++
      "Class5BandHeavyNumericCloses OR Class5CycleNumericCloses. Weakening witness " ++
      "runCycleNumericSettlementHyp_of_settlement : RunNumericSettlementHyp -> " ++
      "successor. Bridges (mirroring runNumericField_settled / " ++
      "runSplitBoundary_settled): runCycleNumericField_settled gives the runNumeric " ++
      "field of Erdos260CycleResidual VERBATIM; runCycleSplitBoundary_settled gives " ++
      "forall ctx, RunClass5SplitBoundary ctx through runSplitOfNumeric. r = 0 needs " ++
      "NO hypothesis (runNumericIneq_of_r_eq_zero).",
    "HONEST RESIDUAL: on r >= 1 shells the successor still demands per-ctx scalars " ++
      "- the band-1 half-density numeric (vacuous when b1 = 0) and the heavy-span " ++
      "numeric c0*M*spanBudget <= (cStar*xi/24)*W*(130L+64). Neither is derivable " ++
      "from the formalized content: the failure hypothesis bounds W from ABOVE only, " ++
      "and the span budget (r+1)*64*(a(i+W+r) - a(i)) is not bounded against W " ++
      "(the top escape gaps are unconstrained). The successor strictly enlarges the " ++
      "closable surface (band-4 cycle mass now paid by the PROVED sliding-window " ++
      "bound instead of the unprovable full cycle count).",
    "NO sorry / admit / new axiom / native_decide; per-pair tables are pure numeral " ++
      "arithmetic (slopeOrbit_step_eval, no Nat.log evaluation); audit block at file " ++
      "end." ]

theorem runCycleNumericClosureStatus_nonempty : runCycleNumericClosureStatus ≠ [] := by
  simp [runCycleNumericClosureStatus]

/-! ## Part 10.  Axiom audit -/

#print axioms canonGap_ne_one_of_two_mul_le
#print axioms class5Band1CycleBand
#print axioms mem_class5Band1CycleBand
#print axioms class5Band1CycleBand_congr
#print axioms class5HeavyFibre
#print axioms mem_class5HeavyFibre
#print axioms runHeavyFloor
#print axioms runHeavyFloor_pos
#print axioms runHeavySpanBudget
#print axioms RunHeavyNumeric
#print axioms class5Band1Fibre_card_le_cycleDensity
#print axioms class5HeavyFibre_card_mul_le_span
#print axioms class5Fibre_card_le_band1_add_heavy
#print axioms class5Fibre_card_le_band1_add_heavy_exists
#print axioms class5HalfDensityRounding
#print axioms class5HeavySpanRounding
#print axioms runNumericIneq_of_band1_heavy_counted
#print axioms class5CycleNumericCloses_of_cycle_band_free
#print axioms run_b1_zero_scalar
#print axioms Class5BandHeavyNumericCloses
#print axioms runNumericIneq_of_bandHeavyCloses
#print axioms class5BandHeavyCloses_of_period_count
#print axioms RunCycleNumericSettlementHyp
#print axioms runCycleNumericSettlementHyp_of_settlement
#print axioms runCycleNumericField_settled
#print axioms runCycleSplitBoundary_settled
#print axioms runDatum_q_ge_three
#print axioms datum_low_window_pairs
#print axioms datum_top_window_pairs
#print axioms runBandCarryingPairs
#print axioms class5CycleNumericCloses_of_free_datum
#print axioms runDatum_lt64_verdict
#print axioms runCycleNumericClosureStatus_nonempty
#print axioms runNumericIneq_of_datum_3_1
#print axioms class5CycleNumericCloses_of_datum_3_1
#print axioms class5BandHeavy_of_datum_5_2
#print axioms class5BandHeavy_of_datum_7_3
#print axioms class5BandHeavy_of_datum_9_1
#print axioms class5BandHeavy_of_datum_9_4
#print axioms class5BandHeavy_of_datum_11_5
#print axioms class5BandHeavy_of_datum_13_6
#print axioms class5BandHeavy_of_datum_15_1
#print axioms class5BandHeavy_of_datum_15_2
#print axioms class5BandHeavy_of_datum_15_7
#print axioms class5BandHeavy_of_datum_17_8
#print axioms class5BandHeavy_of_datum_19_9
#print axioms class5BandHeavy_of_datum_21_1
#print axioms runNumericIneq_of_datum_21_3
#print axioms class5CycleNumericCloses_of_datum_21_3
#print axioms class5BandHeavy_of_datum_21_10
#print axioms class5BandHeavy_of_datum_23_11
#print axioms class5BandHeavy_of_datum_25_2
#print axioms class5BandHeavy_of_datum_25_12
#print axioms class5BandHeavy_of_datum_27_1
#print axioms class5BandHeavy_of_datum_27_4
#print axioms class5BandHeavy_of_datum_27_13
#print axioms class5BandHeavy_of_datum_29_14
#print axioms class5BandHeavy_of_datum_31_15
#print axioms class5BandHeavy_of_datum_33_1
#print axioms class5BandHeavy_of_datum_33_5
#print axioms class5BandHeavy_of_datum_33_16
#print axioms class5BandHeavy_of_datum_35_2
#print axioms class5BandHeavy_of_datum_35_3
#print axioms class5BandHeavy_of_datum_35_17
#print axioms class5BandHeavy_of_datum_37_18
#print axioms class5BandHeavy_of_datum_39_1
#print axioms class5BandHeavy_of_datum_39_6
#print axioms class5BandHeavy_of_datum_39_19
#print axioms class5BandHeavy_of_datum_41_20
#print axioms class5BandHeavy_of_datum_43_21
#print axioms class5BandHeavy_of_datum_45_1
#print axioms class5BandHeavy_of_datum_45_2
#print axioms class5BandHeavy_of_datum_45_4
#print axioms class5BandHeavy_of_datum_45_7
#print axioms class5BandHeavy_of_datum_45_22
#print axioms class5BandHeavy_of_datum_47_23
#print axioms class5BandHeavy_of_datum_49_3
#print axioms class5BandHeavy_of_datum_49_24
#print axioms runNumericIneq_of_datum_51_1
#print axioms class5CycleNumericCloses_of_datum_51_1
#print axioms runNumericIneq_of_datum_51_8
#print axioms class5CycleNumericCloses_of_datum_51_8
#print axioms class5BandHeavy_of_datum_51_25
#print axioms class5BandHeavy_of_datum_53_26
#print axioms class5BandHeavy_of_datum_55_2
#print axioms class5BandHeavy_of_datum_55_5
#print axioms class5BandHeavy_of_datum_55_27
#print axioms class5BandHeavy_of_datum_57_1
#print axioms class5BandHeavy_of_datum_57_9
#print axioms class5BandHeavy_of_datum_57_28
#print axioms class5BandHeavy_of_datum_59_29
#print axioms class5BandHeavy_of_datum_61_30
#print axioms runNumericIneq_of_datum_63_1
#print axioms class5CycleNumericCloses_of_datum_63_1
#print axioms class5BandHeavy_of_datum_63_3
#print axioms runNumericIneq_of_datum_63_4
#print axioms class5CycleNumericCloses_of_datum_63_4
#print axioms class5BandHeavy_of_datum_63_10
#print axioms class5BandHeavy_of_datum_63_31

end

end Erdos260
