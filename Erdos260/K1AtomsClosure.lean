import Erdos260.Erdos260KeystoneCapstone
import Erdos260.OrbitPinVoiding

/-!
# The K.1 atoms closure (`K1AtomsClosure`)

This module (NEW; it edits no existing file) works the K.1/densepack remainder of the
wave-20 keystone (`Erdos260KeystoneCapstone`): the two named atoms `K1ClusterFloor` /
`K1StartSpacing` at `r >= 1`, the density field `densePackEndpointDensity` at `b3 > 0`,
and the structural slot `DscTopBandExitFree`.

## 1.  The cluster floor (`K1ClusterFloor`)

* Per-start anatomy: `K1ClusterFloorAt` (the per-window slack at ONE genuine start),
  decomposition `k1acClusterFloor_iff_at`, and the sharp top-subwindow reformulation
  `k1acClusterFloorAt_iff_topSubwindow_empty` - the floor at a start IS the emptiness
  of the top `W - 1` slots of its endpoint window.
* PROVED stratum: every start whose window top sticks out above the shell ceiling
  (`2X + W <= k + r + spread + 1`) satisfies the floor outright
  (`k1acClusterFloorAt_of_topAbove`); at `r = 1` this is the explicit top band
  `2X + B <= k + L + 2` (`k1acClusterFloorAt_of_r_one_high`).
* SHARP REDUCTION: `K1ClusterFloor <-> K1InteriorClusterFloor`
  (`k1acClusterFloor_iff_interior`) - the named minimal sub-atom is the floor at
  INTERIOR endpoints only (window top at or below `2X + W - spread - 1`); the
  boundary stratum is free.  A violation pins an explicit shell hit in the top
  subwindow (`k1acClusterFloorAt_or_witness`) - no in-tree placement atom excludes it.

## 2.  The spacing atom at `r >= 2` (`K1StartSpacing`)

* The cycle-spacing route is DEAD at `r >= 2`: the width is `>= L + 3B + 2`
  (`k1acWidth_lower_of_r_ge_two`; exact at `r = 2`: `k1acWidth_eq_of_r_two`), and
  `L >= 15421` on every `r >= 1` stratum, so EVERY period `c <= 15430` (in particular
  the whole `c <= 199` table) is outrun (`k1acTablePeriod_lt_width_of_r_ge_two`,
  `k1acDepth_lt_width_of_r_ge_two`).  Only the `r = 1` regime `2B + 1 <= c` survives
  (in-tree, `k1CoverBody_of_r_one_singleResidue`).
* The RARITY route (the surviving mechanism): `K1StartSpacing <-> K1SpanRarity`
  (at most one genuine start per width-`W` span; `k1acStartSpacing_iff_spanRarity`).
* The level-set count cap TRANSCRIBED to the densepack fibre:
  `Y * |gdps| <= (r+1) * emExitMass` at recurrent band `<= 4`
  (`k1acGenuineCount_cap` - the densepack analogue of `nsgLevelSet_count_cap_ofBand`),
  and its LOCALIZED per-span form `Y * |span gdps| <= (r+1) * localExitMass`
  (`k1acSpanCount_cap`, with `localExitMass` the exit mass of the `W + r` gap-index
  span).  Consequence: per-span exit-lightness (`K1LocalExitLight`) supplies the
  spacing atom outright (`k1acStartSpacing_of_localExitLight`); a global count
  collapse `|gdps| <= 1` also suffices (`k1acStartSpacing_of_card_le_one`).

## 3.  The density field at `b3 > 0` (`densePackEndpointDensity`)

* SHARP STRUCTURE: density `<->` anchor-with-surplus at some radius
  (`k1acDensity_iff_anchorSurplus` via the window-shift counting lemma
  `k1acWindowCard_shift`: moving a window by `<= d` loses `<= 2d` hits).  The named
  landing core is `K1AnchorSurplus ctx d`: every genuine endpoint sits within `d` of
  a marker with surplus `2d` - the manuscript "descent lands IN a dense cluster".
* The syndetic supply at the band-3 pin, QUANTIFIED: at `OrbitBandPinned ctx 3` the
  value is exactly dyadic, the word hits every `(N, N + L + 2]` window
  (`k1acBand3_next_hit`), so every in-shell window position carries `>= 1` shell hit
  (`k1acBand3_window_one_hit`) - while the demand is `>= L/8` real
  (`k1acDensity_demand_real_floor`), strictly `>= 2` (`k1acDensity_demand_ge_two`):
  the syndetic floor UNDERSHOOTS the demand by the factor `~ L/8`; the gap is the
  honest hard core, named `K1AnchorSurplus`.

## 4.  The top-band slot (`DscTopBandExitFree`)

* THE PRICE IS PAID AT THE PINS: the slot's only in-tree quantitative consequence -
  the sharpened support floor `X <= 2*(W - (r+1))*(L+B+1)`
  (`mdc_topBandExitFree_support_floor`) - holds UNCONDITIONALLY at every band-2/3/4
  orbit-pinned context (`k1acTopBandPricePaid_of_pin2/3/4`), from the opv syndetic
  support floors `X/(L+2) <= W` (resp. `X/(L+4)`) and the dyadic largeness
  `2(L+2)(L+4) <= 2^L` (`k1ac_two_poly_le_two_pow`).  So the slot cannot be refuted
  through its price at any pinned context; the cost is free there.
* THE VOID, EXTENDED: the only in-tree supplier (index persistence at a fixed-family
  hit) EMPTIES the genuine densepack start set (`k1acGenuine_empty_of_indexPersistence`),
  hence voids ALL THREE K.1 demands at once (`k1acK1Demands_of_indexPersistence`):
  density, cluster floor and spacing hold vacuously where the supplier fires.  The
  slot itself stays a genuine structural residual (no in-tree mechanism proves or
  refutes it off the voided stratum).

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option maxRecDepth 8192
set_option linter.unusedVariables false

/-! ## Part 1.  The cluster floor: per-start anatomy and the provable strata -/

/-- **The per-start cluster floor**: the endpoint window's hits at the single genuine
start `k` keep top slack `W`. -/
def K1ClusterFloorAt (ctx : ActualFailureContext) (k : ℕ) : Prop :=
  ∀ n ∈ proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r),
    n + k1CoverWidth ctx
      ≤ k + ctx.n24CarryData.r + proofV4DensePackSpread ctx.shell + 1

/-- The atom decomposes into its per-start slices (definitional). -/
theorem k1acClusterFloor_iff_at (ctx : ActualFailureContext) :
    K1ClusterFloor ctx ↔ ∀ k ∈ genuineDensePackStarts ctx, K1ClusterFloorAt ctx k :=
  Iff.rfl

/-- The top subwindow of the endpoint window at `k`: the hits violating the slack. -/
def k1acTopSubwindow (ctx : ActualFailureContext) (k : ℕ) : Finset ℕ :=
  (proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)).filter
    (fun n => k + ctx.n24CarryData.r + proofV4DensePackSpread ctx.shell + 1
      < n + k1CoverWidth ctx)

/-- **The sharp reformulation**: the per-start floor IS the emptiness of the top
subwindow (the top `W - 1` slots of the endpoint window carry no shell hit). -/
theorem k1acClusterFloorAt_iff_topSubwindow_empty (ctx : ActualFailureContext)
    (k : ℕ) :
    K1ClusterFloorAt ctx k ↔ k1acTopSubwindow ctx k = ∅ := by
  unfold k1acTopSubwindow
  rw [Finset.filter_eq_empty_iff]
  constructor
  · intro h n hn
    have := h n hn
    omega
  · intro h n hn
    have := h hn
    omega

/-- **The boundary stratum is FREE**: if the window top sticks out above the shell
ceiling `2X` by at least the width (`2X + W ≤ k + r + spread + 1`), every shell hit
(`n ≤ 2X`) automatically keeps the slack. -/
theorem k1acClusterFloorAt_of_topAbove (ctx : ActualFailureContext) {k : ℕ}
    (h : 2 * ctx.shell.X + k1CoverWidth ctx
      ≤ k + ctx.n24CarryData.r + proofV4DensePackSpread ctx.shell + 1) :
    K1ClusterFloorAt ctx k := by
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  obtain ⟨hX1, hX2, hd1⟩ := (mem_supportShell _ _ n).mp hn'.1
  omega

/-- The `r = 1` boundary stratum, explicit: at `r = 1` the width is exactly `2B + 1`,
so the floor is free at every start with `2X + B ≤ k + L + 2` (the top `L - B`-band
of endpoints; nonempty under density since `B + 25 ≤ L`). -/
theorem k1acClusterFloorAt_of_r_one_high (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 1) {k : ℕ}
    (h : 2 * ctx.shell.X + carryB ctx.shell.Q ≤ k + shellLadderDepth ctx + 2) :
    K1ClusterFloorAt ctx k := by
  apply k1acClusterFloorAt_of_topAbove
  have hW := k1CoverWidth_eq_of_r_eq_one ctx hr
  have hspread : proofV4DensePackSpread ctx.shell
      = shellLadderDepth ctx + carryB ctx.shell.Q + 1 := rfl
  omega

/-- **THE NAMED MINIMAL SUB-ATOM (interior cluster floor)**: the per-window floor
demanded only at INTERIOR endpoints (window top strictly below `2X + W`).  This is
the irreducible placement core; the boundary stratum closes for free. -/
def K1InteriorClusterFloor (ctx : ActualFailureContext) : Prop :=
  ∀ k ∈ genuineDensePackStarts ctx,
    k + ctx.n24CarryData.r + proofV4DensePackSpread ctx.shell + 1
        < 2 * ctx.shell.X + k1CoverWidth ctx →
      K1ClusterFloorAt ctx k

/-- **The sharp reduction**: the full cluster-floor atom is EQUIVALENT to its
interior stratum - the boundary stratum is discharged by `k1acClusterFloorAt_of_topAbove`. -/
theorem k1acClusterFloor_iff_interior (ctx : ActualFailureContext) :
    K1ClusterFloor ctx ↔ K1InteriorClusterFloor ctx := by
  constructor
  · intro h k hk _
    exact fun n hn => h k hk n hn
  · intro h k hk
    rcases Nat.lt_or_ge
      (k + ctx.n24CarryData.r + proofV4DensePackSpread ctx.shell + 1)
      (2 * ctx.shell.X + k1CoverWidth ctx) with hlo | hhi
    · exact h k hk hlo
    · exact k1acClusterFloorAt_of_topAbove ctx hhi

/-- **The refutation interface**: at every start the floor either holds or pins an
EXPLICIT shell hit inside the top subwindow - the position constraint that no
in-tree placement atom excludes. -/
theorem k1acClusterFloorAt_or_witness (ctx : ActualFailureContext) (k : ℕ) :
    K1ClusterFloorAt ctx k ∨ ∃ n : ℕ,
      ctx.shell.X < n ∧ n ≤ 2 * ctx.shell.X ∧ ctx.shell.d n = 1 ∧
      k + ctx.n24CarryData.r ≤ n ∧
      n ≤ k + ctx.n24CarryData.r + proofV4DensePackSpread ctx.shell ∧
      k + ctx.n24CarryData.r + proofV4DensePackSpread ctx.shell + 1
        < n + k1CoverWidth ctx := by
  by_cases h : K1ClusterFloorAt ctx k
  · exact Or.inl h
  · right
    unfold K1ClusterFloorAt at h
    simp only [not_forall, not_le] at h
    obtain ⟨n, hn, hlt⟩ := h
    have hn' := Finset.mem_filter.mp hn
    obtain ⟨hX1, hX2, hd1⟩ := (mem_supportShell _ _ n).mp hn'.1
    obtain ⟨hmn, hns⟩ := hn'.2
    exact ⟨n, hX1, hX2, hd1, hmn, hns, hlt⟩

/-- The whole atom from per-start boundary membership (the all-high supplier). -/
theorem k1acClusterFloor_of_topAbove (ctx : ActualFailureContext)
    (h : ∀ k ∈ genuineDensePackStarts ctx,
      2 * ctx.shell.X + k1CoverWidth ctx
        ≤ k + ctx.n24CarryData.r + proofV4DensePackSpread ctx.shell + 1) :
    K1ClusterFloor ctx :=
  fun k hk => k1acClusterFloorAt_of_topAbove ctx (h k hk)

/-- **The exact keystone `densePackClusterFloor` field from the interior sub-atom**
(the boundary stratum is closed here; guards verbatim). -/
theorem k1acDensePackClusterFloorField_of_interior
    (h : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1InteriorClusterFloor ctx) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1ClusterFloor ctx :=
  fun ctx h1 h2 h3 h4 h5 h6 =>
    (k1acClusterFloor_iff_interior ctx).mpr (h ctx h1 h2 h3 h4 h5 h6)

/-! ## Part 2.  The spacing atom at `r ≥ 2`: the cycle route dies, the rarity route -/

/-- **The exact `r = 2` width**: `W = L + 3B + 2` - the width has caught the depth. -/
theorem k1acWidth_eq_of_r_two (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 2) :
    k1CoverWidth ctx = shellLadderDepth ctx + 3 * carryB ctx.shell.Q + 2 := by
  have hG0 : densePackDyadicG0 ctx
      = shellLadderDepth ctx + carryB ctx.shell.Q + 1 := rfl
  unfold k1CoverWidth
  rw [hr, hG0]
  omega

/-- At `r ≥ 2` the width is at least `L + 3B + 2`. -/
theorem k1acWidth_lower_of_r_ge_two (ctx : ActualFailureContext)
    (hr : 2 ≤ ctx.n24CarryData.r) :
    shellLadderDepth ctx + 3 * carryB ctx.shell.Q + 2 ≤ k1CoverWidth ctx := by
  have hG0 : densePackDyadicG0 ctx
      = shellLadderDepth ctx + carryB ctx.shell.Q + 1 := rfl
  have h3 : 3 * densePackDyadicG0 ctx
      ≤ (ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx :=
    Nat.mul_le_mul (by omega) (le_refl _)
  unfold k1CoverWidth
  rw [hG0] at h3 ⊢
  omega

/-- **The depth is outrun**: at `r ≥ 2` the width strictly exceeds `L` - no period
`c ≤ L` can ever clear `W ≤ c`. -/
theorem k1acDepth_lt_width_of_r_ge_two (ctx : ActualFailureContext)
    (hr : 2 ≤ ctx.n24CarryData.r) :
    shellLadderDepth ctx < k1CoverWidth ctx := by
  have h := k1acWidth_lower_of_r_ge_two ctx hr
  have hB := k1_carryB_ge_three ctx
  omega

/-- **The cycle-spacing route is DEAD at `r ≥ 2`** (the (c, r) tabulation): every
period `c ≤ 15430` - in particular the whole certified table `c ≤ 199` - is strictly
below the width (`r ≥ 2` forces `L ≥ 15421`, so `W ≥ L + 3B + 2 ≥ 15432`).  The
single-residue discharge regime `W ≤ c` is empty off `r = 1`. -/
theorem k1acTablePeriod_lt_width_of_r_ge_two (ctx : ActualFailureContext)
    (hr : 2 ≤ ctx.n24CarryData.r) {c : ℕ} (hc : c ≤ 15430) :
    c < k1CoverWidth ctx := by
  have h := k1acWidth_lower_of_r_ge_two ctx hr
  have hB := k1_carryB_ge_three ctx
  have hL : 15421 ≤ shellLadderDepth ctx := by
    by_contra hL
    have h0 := n24_r_eq_zero_of_L_le ctx (by omega)
    omega
  omega

/-- The genuine densepack starts sit inside the carry start window. -/
theorem k1acGenuine_subset_starts (ctx : ActualFailureContext) :
    genuineDensePackStarts ctx ⊆ ctx.n24CarryData.starts := by
  intro k hk
  have h := (mem_genuineDensePackStarts ctx k).mp hk
  exact (mem_highExcessStarts.mp h.1).1

/-- Every genuine densepack start carries the high-excess floor `Y`. -/
theorem k1acGenuine_Y_le (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ genuineDensePackStarts ctx) :
    ctx.n24CarryData.Y
      ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          ctx.n24CarryData.T :=
  (mem_highExcessStarts.mp ((mem_genuineDensePackStarts ctx k).mp hk).1).2

/-- **The densepack heavy-count cap** (the level-set count cap transcribed onto the
genuine densepack fibre, generic overlap `r + 1`): at recurrent band `≤ 4`,
`Y · |gdps| ≤ (r+1) · emExitMass` - heavy starts are RARE, in count.  This is the
densepack analogue of `nsgLevelSet_count_cap_ofBand`. -/
theorem k1acGenuineCount_cap (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) :
    ctx.n24CarryData.Y * ((genuineDensePackStarts ctx).card : ℝ)
      ≤ (((ctx.n24CarryData.r + 1) * emExitMass ctx : ℕ) : ℝ) := by
  have h1 : ∑ _k ∈ genuineDensePackStarts ctx, ctx.n24CarryData.Y
      = ctx.n24CarryData.Y * ((genuineDensePackStarts ctx).card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have h2 : ∑ _k ∈ genuineDensePackStarts ctx, ctx.n24CarryData.Y
      ≤ ∑ k ∈ genuineDensePackStarts ctx,
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ctx.n24CarryData.T :=
    Finset.sum_le_sum (fun k hk => k1acGenuine_Y_le ctx hk)
  have h3 : ∑ k ∈ genuineDensePackStarts ctx,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          ctx.n24CarryData.T
      ≤ ((∑ k ∈ genuineDensePackStarts ctx, emDevWindow ctx k : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum (fun k _ => em_windowExcess_le_devWindow ctx hband k)
  have h4 : ∑ k ∈ genuineDensePackStarts ctx, emDevWindow ctx k
      ≤ (ctx.n24CarryData.r + 1) * emExitMass ctx :=
    le_trans (Finset.sum_le_sum_of_subset (k1acGenuine_subset_starts ctx))
      (em_devWindow_sum_le ctx)
  rw [← h1]
  refine le_trans h2 (le_trans h3 ?_)
  exact_mod_cast h4

/-- The genuine starts inside a width-`W` span. -/
def k1acSpanStarts (ctx : ActualFailureContext) (m : ℕ) : Finset ℕ :=
  (genuineDensePackStarts ctx).filter
    (fun k => m ≤ k ∧ k < m + k1CoverWidth ctx)

/-- **THE NAMED RARITY ATOM**: at most ONE genuine start per width-`W` span. -/
def K1SpanRarity (ctx : ActualFailureContext) : Prop :=
  ∀ m : ℕ, (k1acSpanStarts ctx m).card ≤ 1

/-- **The spacing atom IS the rarity atom**: `W`-spacing of distinct genuine starts
is equivalent to one-per-span counting. -/
theorem k1acStartSpacing_iff_spanRarity (ctx : ActualFailureContext) :
    K1StartSpacing ctx ↔ K1SpanRarity ctx := by
  constructor
  · intro hsp m
    rw [Finset.card_le_one]
    intro a ha b hb
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    obtain ⟨ha1, ha2⟩ := ha'.2
    obtain ⟨hb1, hb2⟩ := hb'.2
    by_contra hab
    rcases Nat.lt_or_ge a b with h | h
    · have := hsp a ha'.1 b hb'.1 h
      omega
    · have hba : b < a := by omega
      have := hsp b hb'.1 a ha'.1 hba
      omega
  · intro hra k hk k' hk' hlt
    by_contra hclose
    have hmem : k ∈ k1acSpanStarts ctx k :=
      Finset.mem_filter.mpr ⟨hk, le_refl k, by omega⟩
    have hmem' : k' ∈ k1acSpanStarts ctx k :=
      Finset.mem_filter.mpr ⟨hk', by omega, by omega⟩
    have hcard := hra k
    rw [Finset.card_le_one] at hcard
    have := hcard k hmem k' hmem'
    omega

/-- A global count collapse supplies the spacing atom outright. -/
theorem k1acStartSpacing_of_card_le_one (ctx : ActualFailureContext)
    (h : (genuineDensePackStarts ctx).card ≤ 1) : K1StartSpacing ctx := by
  intro k hk k' hk' hlt
  rw [Finset.card_le_one] at h
  have := h k hk k' hk'
  omega

/-- **The localized exit mass** of a width-`W` span: the deviation mass carried by
the gap indices `[m, m + W + r)` reachable from the span's descent windows. -/
def k1acLocalExitMass (ctx : ActualFailureContext) (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ico m (m + k1CoverWidth ctx + ctx.n24CarryData.r),
    emExitWeight ctx j

/-- **The PER-SPAN heavy-count cap** (the localized level-set bound the global cap
does not give): at recurrent band `≤ 4`, every width-`W` span obeys
`Y · |span gdps| ≤ (r+1) · localExitMass` - the span's heavy population is paid by
the span's OWN exit mass. -/
theorem k1acSpanCount_cap (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) (m : ℕ) :
    ctx.n24CarryData.Y * ((k1acSpanStarts ctx m).card : ℝ)
      ≤ (((ctx.n24CarryData.r + 1) * k1acLocalExitMass ctx m : ℕ) : ℝ) := by
  have h1 : ∑ _k ∈ k1acSpanStarts ctx m, ctx.n24CarryData.Y
      = ctx.n24CarryData.Y * ((k1acSpanStarts ctx m).card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have h2 : ∑ _k ∈ k1acSpanStarts ctx m, ctx.n24CarryData.Y
      ≤ ∑ k ∈ k1acSpanStarts ctx m,
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ctx.n24CarryData.T :=
    Finset.sum_le_sum (fun k hk =>
      k1acGenuine_Y_le ctx (Finset.mem_filter.mp hk).1)
  have h3 : ∑ k ∈ k1acSpanStarts ctx m,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          ctx.n24CarryData.T
      ≤ ((∑ k ∈ k1acSpanStarts ctx m, emDevWindow ctx k : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum (fun k _ => em_windowExcess_le_devWindow ctx hband k)
  have hloc : ∑ k ∈ k1acSpanStarts ctx m, emDevWindow ctx k
      ≤ (ctx.n24CarryData.r + 1) * k1acLocalExitMass ctx m := by
    unfold emDevWindow
    rw [Finset.sum_comm]
    calc ∑ i ∈ Finset.range (ctx.n24CarryData.r + 1),
          ∑ k ∈ k1acSpanStarts ctx m, emExitWeight ctx (k + i)
        ≤ ∑ _i ∈ Finset.range (ctx.n24CarryData.r + 1),
            k1acLocalExitMass ctx m := by
          refine Finset.sum_le_sum ?_
          intro i hi
          rw [Finset.mem_range] at hi
          have hinj : ∀ a ∈ k1acSpanStarts ctx m, ∀ b ∈ k1acSpanStarts ctx m,
              a + i = b + i → a = b := by
            intro a _ b _ hab
            omega
          have hsubset : (k1acSpanStarts ctx m).image (fun k => k + i)
              ⊆ Finset.Ico m (m + k1CoverWidth ctx + ctx.n24CarryData.r) := by
            intro j hj
            rw [Finset.mem_image] at hj
            obtain ⟨k, hk, rfl⟩ := hj
            have hk' := Finset.mem_filter.mp hk
            obtain ⟨hk1, hk2⟩ := hk'.2
            rw [Finset.mem_Ico]
            omega
          calc ∑ k ∈ k1acSpanStarts ctx m, emExitWeight ctx (k + i)
              = ∑ j ∈ (k1acSpanStarts ctx m).image (fun k => k + i),
                  emExitWeight ctx j := (Finset.sum_image hinj).symm
            _ ≤ ∑ j ∈ Finset.Ico m (m + k1CoverWidth ctx + ctx.n24CarryData.r),
                  emExitWeight ctx j := Finset.sum_le_sum_of_subset hsubset
            _ = k1acLocalExitMass ctx m := rfl
      _ = (ctx.n24CarryData.r + 1) * k1acLocalExitMass ctx m := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_range]
  rw [← h1]
  refine le_trans h2 (le_trans h3 ?_)
  exact_mod_cast hloc

/-- **THE NAMED LOCALIZED SUB-ATOM**: every width-`W` span is exit-light -
`(r+1) · localExitMass < 2Y`.  Satisfiable (exit-free spans give `0 < 2Y`); the
honest open content is the spans that DO carry exits. -/
def K1LocalExitLight (ctx : ActualFailureContext) : Prop :=
  ∀ m : ℕ, (((ctx.n24CarryData.r + 1) * k1acLocalExitMass ctx m : ℕ) : ℝ)
    < 2 * ctx.n24CarryData.Y

/-- Per-span exit-lightness forces one-per-span rarity. -/
theorem k1acSpanRarity_of_localExitLight (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) (h : K1LocalExitLight ctx) :
    K1SpanRarity ctx := by
  intro m
  by_contra hc
  have h2 : 2 ≤ (k1acSpanStarts ctx m).card := by omega
  have hcap := k1acSpanCount_cap ctx hband m
  have hY := n24CarryData_Y_pos ctx
  have hlt := h m
  have h2R : (2 : ℝ) ≤ ((k1acSpanStarts ctx m).card : ℝ) := by exact_mod_cast h2
  nlinarith

/-- **The spacing atom from per-span exit-lightness** (the best conditional at
`r ≥ 2`, where the cycle route is dead): band `≤ 4` + `K1LocalExitLight` supply
`K1StartSpacing` outright. -/
theorem k1acStartSpacing_of_localExitLight (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) (h : K1LocalExitLight ctx) :
    K1StartSpacing ctx :=
  (k1acStartSpacing_iff_spanRarity ctx).mpr
    (k1acSpanRarity_of_localExitLight ctx hband h)

/-- **The exact keystone `densePackStartSpacing` field from the rarity atom**
(guards verbatim). -/
theorem k1acDensePackStartSpacingField_of_spanRarity
    (h : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1SpanRarity ctx) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1StartSpacing ctx :=
  fun ctx h1 h2 h3 h4 h5 h6 =>
    (k1acStartSpacing_iff_spanRarity ctx).mpr (h ctx h1 h2 h3 h4 h5 h6)

/-! ## Part 3.  The density field at `b3 > 0`: anchor surplus and the syndetic supply -/

/-- **The window-shift counting lemma**: moving the support window by at most `d`
positions loses at most `2d` hits (a hit escapes only through the `≤ d` slots cut at
each end). -/
theorem k1acWindowCard_shift (shell : FailingDyadicShell) {m m' d : ℕ}
    (h1 : m' ≤ m + d) (h2 : m ≤ m' + d) :
    (proofV4DensePackSupportWindow shell m).card
      ≤ (proofV4DensePackSupportWindow shell m').card + 2 * d := by
  have hsub : proofV4DensePackSupportWindow shell m
      ⊆ proofV4DensePackSupportWindow shell m'
        ∪ (Finset.Ico m m'
          ∪ Finset.Ioc (m' + proofV4DensePackSpread shell)
              (m + proofV4DensePackSpread shell)) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    obtain ⟨hmn, hns⟩ := hn'.2
    rw [Finset.mem_union, Finset.mem_union]
    by_cases hin : m' ≤ n ∧ n ≤ m' + proofV4DensePackSpread shell
    · exact Or.inl (Finset.mem_filter.mpr ⟨hn'.1, hin⟩)
    · right
      rcases Nat.lt_or_ge n m' with hlow | hhigh
      · exact Or.inl (Finset.mem_Ico.mpr ⟨hmn, hlow⟩)
      · have hgt : m' + proofV4DensePackSpread shell < n := by
          rcases Nat.lt_or_ge (m' + proofV4DensePackSpread shell) n with hg | hle
          · exact hg
          · exact absurd ⟨hhigh, hle⟩ hin
        exact Or.inr (Finset.mem_Ioc.mpr ⟨hgt, by omega⟩)
  have hc1 := Finset.card_le_card hsub
  have hc2 := Finset.card_union_le
    (proofV4DensePackSupportWindow shell m')
    (Finset.Ico m m'
      ∪ Finset.Ioc (m' + proofV4DensePackSpread shell)
          (m + proofV4DensePackSpread shell))
  have hc3 := Finset.card_union_le (Finset.Ico m m')
    (Finset.Ioc (m' + proofV4DensePackSpread shell)
      (m + proofV4DensePackSpread shell))
  rw [Nat.card_Ico, Nat.card_Ioc] at hc3
  omega

/-- **THE NAMED LANDING CORE (anchor with surplus)**: every genuine endpoint sits
within distance `d` of an anchor position whose window carries `2d` SURPLUS hits
over the demand - the manuscript "the descent lands IN a dense cluster", made
exact at radius `d`. -/
def K1AnchorSurplus (ctx : ActualFailureContext) (d : ℕ) : Prop :=
  ∀ k ∈ genuineDensePackStarts ctx, ∃ m₀ : ℕ,
    m₀ ≤ k + ctx.n24CarryData.r + d ∧
    k + ctx.n24CarryData.r ≤ m₀ + d ∧
    proofV4DensePackMinHits ctx.shell + 2 * d
      ≤ (proofV4DensePackSupportWindow ctx.shell m₀).card

/-- **Density from anchor surplus**: the surplus pays exactly for the shift loss. -/
theorem k1acDensity_of_anchorSurplus (ctx : ActualFailureContext) {d : ℕ}
    (h : K1AnchorSurplus ctx d) : densePackEndpointDensity ctx := by
  intro k hk
  obtain ⟨m₀, h1, h2, h3⟩ := h k hk
  have hshift := k1acWindowCard_shift ctx.shell
    (m := m₀) (m' := k + ctx.n24CarryData.r) (d := d) h2 h1
  omega

/-- **The sharp characterization**: the density field IS anchor-with-surplus at some
radius (`d = 0` recovers density verbatim; positive `d` is the genuine landing
content - an enriched marker near each endpoint). -/
theorem k1acDensity_iff_anchorSurplus (ctx : ActualFailureContext) :
    densePackEndpointDensity ctx ↔ ∃ d : ℕ, K1AnchorSurplus ctx d := by
  constructor
  · intro h
    refine ⟨0, fun k hk => ⟨k + ctx.n24CarryData.r, by omega, by omega, ?_⟩⟩
    simpa using h k hk
  · rintro ⟨d, h⟩
    exact k1acDensity_of_anchorSurplus ctx h

/-- **The exact keystone `densePackDensityOffTable` field from anchor surplus**
(guards verbatim; per-context radius). -/
theorem k1acDensePackDensityOffTableField_of_anchorSurplus
    (h : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → ∃ d : ℕ, K1AnchorSurplus ctx d) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → densePackEndpointDensity ctx := by
  intro ctx h1 h2 h3 h4
  obtain ⟨d, hd⟩ := h ctx h1 h2 h3 h4
  exact k1acDensity_of_anchorSurplus ctx hd

/-- **The band-3 next-hit window** (the densepack sibling of
`orbitBandPinned2_next_hit`): at every band-3-pinned context the value is exactly
dyadic, so the word hits inside `(N, N + h]` for every `N ≥ t` as soon as
`N + h + 2 < 2^h`. -/
theorem k1acBand3_next_hit (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) :
    ∃ t : ℕ, ctx.shell.Q = 3 * 2 ^ t ∧
      ∀ N h : ℕ, t ≤ N → ((N + h + 2 : ℕ) : ℤ) < 2 ^ h →
        ∃ j, N < j ∧ j ≤ N + h ∧ ctx.shell.d j = 1 := by
  obtain ⟨t, hQ, hval⟩ := orbitBandPinned3_value ctx hpin
  exact ⟨t, hQ, fun N h htN hwin =>
    dyadicValue_next_one ctx.hd hval ctx.hnonterm htN hwin⟩

/-- **The syndetic one-hit floor at the band-3 pin**: every window position in the
in-shell range `[X, 2X - L - 2]` carries at least ONE shell hit - the quantified
syndetic supply of the K.1 landing region. -/
theorem k1acBand3_window_one_hit (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) {m : ℕ}
    (hlo : ctx.shell.X ≤ m)
    (hhi : m + shellLadderDepth ctx + 2 ≤ 2 * ctx.shell.X) :
    1 ≤ (proofV4DensePackSupportWindow ctx.shell m).card := by
  obtain ⟨t, hQ, hnext⟩ := k1acBand3_next_hit ctx hpin
  have hX : ctx.shell.X = 2 ^ shellLadderDepth ctx := scc_X_pow ctx
  have hB : 3 ≤ carryB ctx.shell.Q := k1_carryB_ge_three ctx
  have htm : t ≤ m := by
    have hQQ : ctx.shell.Q = ctx.Q := ctx.shell_Q
    have hXX : ctx.shell.X = ctx.X := ctx.shell_X
    have h2t : 2 ^ t ≤ ctx.shell.Q := by
      rw [hQ]
      have := Nat.two_pow_pos t
      omega
    have hQX : ctx.Q < ctx.X := carryWord_Q_lt_X ctx
    have hlt : t < 2 ^ t := Nat.lt_two_pow_self
    omega
  have hwin : ((m + (shellLadderDepth ctx + 2) + 2 : ℕ) : ℤ)
      < 2 ^ (shellLadderDepth ctx + 2) := by
    have hpow : (2 : ℕ) ^ (shellLadderDepth ctx + 2) = 4 * ctx.shell.X := by
      rw [hX, pow_add]
      ring
    have hX28 : 268435456 ≤ ctx.shell.X := scc_X_ge ctx
    have hnat : m + (shellLadderDepth ctx + 2) + 2
        < 2 ^ (shellLadderDepth ctx + 2) := by
      rw [hpow]
      omega
    exact_mod_cast hnat
  obtain ⟨j, hj1, hj2, hj3⟩ := hnext m (shellLadderDepth ctx + 2) htm hwin
  have hspread : proofV4DensePackSpread ctx.shell
      = shellLadderDepth ctx + carryB ctx.shell.Q + 1 := rfl
  have hmem : j ∈ proofV4DensePackSupportWindow ctx.shell m := by
    refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
    · exact (mem_supportShell _ _ j).mpr ⟨by omega, by omega, hj3⟩
    · omega
    · omega
  exact Finset.card_pos.mpr ⟨j, hmem⟩

/-- The demand side, in real form: the actual-point filter asks `≥ L/8` hits. -/
theorem k1acDensity_demand_real_floor (ctx : ActualFailureContext) :
    ((shellLadderDepth ctx : ℕ) : ℝ) / 8
      ≤ (proofV4DensePackMinHits ctx.shell : ℝ) :=
  proofV4DensePackMinHits_ge_L_div_eight_of_carryLarge ctx.shell_carryLarge

/-- **The honest shortfall**: the demand is at least `2` on every failing shell
(`L ≥ 28` gives `L/8 ≥ 3.5`), so the syndetic one-hit floor NEVER meets it - the
gap (factor `~ L/8`) is the open landing core `K1AnchorSurplus`. -/
theorem k1acDensity_demand_ge_two (ctx : ActualFailureContext) :
    2 ≤ proofV4DensePackMinHits ctx.shell := by
  have hreal := k1acDensity_demand_real_floor ctx
  have hL : 28 ≤ shellLadderDepth ctx := shellLadderDepth_ge ctx
  have hLR : (28 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by exact_mod_cast hL
  have h2 : (2 : ℝ) ≤ (proofV4DensePackMinHits ctx.shell : ℝ) := by linarith
  exact_mod_cast h2

/-! ## Part 4.  The top-band slot: the price is paid at the pins; the void extends -/

/-- Dyadic largeness: `2(n+2)(n+4) ≤ 2^n` for `n ≥ 28`. -/
theorem k1ac_two_poly_le_two_pow {n : ℕ} (hn : 28 ≤ n) :
    2 * ((n + 2) * (n + 4)) ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hstep : 2 * ((n + 1 + 2) * (n + 1 + 4))
          ≤ 2 * (2 * ((n + 2) * (n + 4))) := by nlinarith
      calc 2 * ((n + 1 + 2) * (n + 1 + 4))
          ≤ 2 * (2 * ((n + 2) * (n + 4))) := hstep
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul (le_refl 2) ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- **The generic price discharge**: any support floor `X/(L+4) ≤ W` (with the
standing largeness `L ≥ 28`, `B ≥ 3`, `r ≤ L`, `X = 2^L`) already pays the sharpened
top-band support floor `X ≤ 2(W - (r+1))(L+B+1)`. -/
theorem k1ac_price_of_div_floor {X L B r W : ℕ} (hL : 28 ≤ L) (hB : 3 ≤ B)
    (hrL : r ≤ L) (hX : X = 2 ^ L) (hfloor : X / (L + 4) ≤ W) :
    X ≤ 2 * ((W - (r + 1)) * (L + B + 1)) := by
  have hXpoly : 2 * ((L + 2) * (L + 4)) ≤ X := by
    rw [hX]
    exact k1ac_two_poly_le_two_pow hL
  have hdm : (L + 4) * (X / (L + 4)) + X % (L + 4) = X := Nat.div_add_mod X (L + 4)
  have hmod : X % (L + 4) < L + 4 := Nat.mod_lt X (by omega)
  have hWB : (X / (L + 4) - (r + 1)) * (L + 4)
      ≤ (W - (r + 1)) * (L + B + 1) :=
    Nat.mul_le_mul (Nat.sub_le_sub_right hfloor _) (by omega)
  have hsm : (X / (L + 4) - (r + 1)) * (L + 4)
      = (L + 4) * (X / (L + 4)) - (L + 4) * (r + 1) := by
    rw [Nat.sub_mul, Nat.mul_comm (L + 4) (X / (L + 4)), Nat.mul_comm (L + 4) (r + 1)]
  have hRA : (L + 4) * (r + 1) ≤ (L + 4) * (L + 1) :=
    Nat.mul_le_mul (le_refl _) (by omega)
  have hCA : 2 * ((L + 2) * (L + 4)) = 2 * ((L + 4) * (L + 1)) + 2 * (L + 4) := by
    ring
  generalize hP : (L + 4) * (X / (L + 4)) = P at hdm hsm
  generalize hA : (L + 4) * (L + 1) = A at hRA hCA
  generalize hR : (L + 4) * (r + 1) = R at hsm hRA
  generalize hs : X % (L + 4) = s at hdm hmod
  generalize hC : 2 * ((L + 2) * (L + 4)) = C at hXpoly hCA
  refine le_trans ?_ (Nat.mul_le_mul (le_refl 2) hWB)
  rw [hsm]
  omega

/-- **The price is paid at the band-2 pin**: the sharpened top-band support floor
holds UNCONDITIONALLY (no `DscTopBandExitFree` needed) at every band-2-pinned
context, from the opv syndetic floor `X/(L+2) ≤ W`. -/
theorem k1acTopBandPricePaid_of_pin2 (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2) :
    ctx.shell.X ≤ 2 * ((emW ctx - (ctx.n24CarryData.r + 1))
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := by
  have hfloor : ctx.shell.X / (shellLadderDepth ctx + 2) ≤ emW ctx :=
    orbitBandPinned2_support_floor ctx hpin
  have h24 : ctx.shell.X / (shellLadderDepth ctx + 4)
      ≤ ctx.shell.X / (shellLadderDepth ctx + 2) := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < shellLadderDepth ctx + 2)]
    calc ctx.shell.X / (shellLadderDepth ctx + 4) * (shellLadderDepth ctx + 2)
        ≤ ctx.shell.X / (shellLadderDepth ctx + 4) * (shellLadderDepth ctx + 4) :=
          Nat.mul_le_mul (le_refl _) (by omega)
      _ ≤ ctx.shell.X := Nat.div_mul_le_self _ _
  exact k1ac_price_of_div_floor (shellLadderDepth_ge ctx) (k1_carryB_ge_three ctx)
    (fde_r_le_L ctx) (scc_X_pow ctx) (le_trans h24 hfloor)

/-- **The price is paid at the band-3 pin** (the densepack-relevant pin:
`Band3PinnedWide ↔ OrbitBandPinned 3`). -/
theorem k1acTopBandPricePaid_of_pin3 (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) :
    ctx.shell.X ≤ 2 * ((emW ctx - (ctx.n24CarryData.r + 1))
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := by
  have hfloor : ctx.shell.X / (shellLadderDepth ctx + 2) ≤ emW ctx :=
    orbitBandPinned3_support_floor ctx hpin
  have h24 : ctx.shell.X / (shellLadderDepth ctx + 4)
      ≤ ctx.shell.X / (shellLadderDepth ctx + 2) := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < shellLadderDepth ctx + 2)]
    calc ctx.shell.X / (shellLadderDepth ctx + 4) * (shellLadderDepth ctx + 2)
        ≤ ctx.shell.X / (shellLadderDepth ctx + 4) * (shellLadderDepth ctx + 4) :=
          Nat.mul_le_mul (le_refl _) (by omega)
      _ ≤ ctx.shell.X := Nat.div_mul_le_self _ _
  exact k1ac_price_of_div_floor (shellLadderDepth_ge ctx) (k1_carryB_ge_three ctx)
    (fde_r_le_L ctx) (scc_X_pow ctx) (le_trans h24 hfloor)

/-- **The price is paid at the band-4 pin** (floor `X/(L+4) ≤ W`, used as-is). -/
theorem k1acTopBandPricePaid_of_pin4 (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4) :
    ctx.shell.X ≤ 2 * ((emW ctx - (ctx.n24CarryData.r + 1))
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := by
  have hfloor : ctx.shell.X / (shellLadderDepth ctx + 4) ≤ emW ctx :=
    orbitBandPinned4_support_floor ctx hpin
  exact k1ac_price_of_div_floor (shellLadderDepth_ge ctx) (k1_carryB_ge_three ctx)
    (fde_r_le_L ctx) (scc_X_pow ctx) hfloor

/-- **The void, extended to the WHOLE K.1 demand set**: index persistence at a
fixed-family hit empties the genuine densepack start set itself. -/
theorem k1acGenuine_empty_of_indexPersistence (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hp : FixedFamilyIndexPersistence ctx) :
    genuineDensePackStarts ctx = ∅ := by
  have h := highExcessStarts_empty_of_indexPersistence ctx hhit hp
  unfold genuineDensePackStarts
  rw [h, Finset.filter_empty]

/-- The cluster floor closes on the vacuous stratum. -/
theorem k1acClusterFloor_of_emptyStarts (ctx : ActualFailureContext)
    (h : genuineDensePackStarts ctx = ∅) : K1ClusterFloor ctx := by
  intro k hk
  rw [h] at hk
  simp at hk

/-- The spacing atom closes on the vacuous stratum. -/
theorem k1acStartSpacing_of_emptyStarts (ctx : ActualFailureContext)
    (h : genuineDensePackStarts ctx = ∅) : K1StartSpacing ctx := by
  intro k hk
  rw [h] at hk
  simp at hk

/-- **All three K.1 demands are voided where the onset supplier fires**: at a
fixed-family hit with index persistence, density, cluster floor and spacing all hold
vacuously - the only in-tree route to `DscTopBandExitFree` voids the densepack
demand exactly as it voids the class-0 fibre (`mdcIndexPersistence_voids_class0`). -/
theorem k1acK1Demands_of_indexPersistence (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hp : FixedFamilyIndexPersistence ctx) :
    densePackEndpointDensity ctx ∧ K1ClusterFloor ctx ∧ K1StartSpacing ctx := by
  have h := k1acGenuine_empty_of_indexPersistence ctx hhit hp
  exact ⟨densePackEndpointDensity_of_emptyStarts ctx h,
    k1acClusterFloor_of_emptyStarts ctx h,
    k1acStartSpacing_of_emptyStarts ctx h⟩

/-! ## Part 5.  Honest status inventory -/

/-- The precise per-item status of the K.1 atoms pass. -/
def k1AtomsClosureStatus : List String :=
  [ "CLUSTER FLOOR (goal 1, SHARP REDUCTION proved): K1ClusterFloor <-> " ++
      "K1InteriorClusterFloor (k1acClusterFloor_iff_interior) - the atom is " ++
      "EXACTLY its interior stratum; the boundary stratum (window top at or " ++
      "above 2X + W) is closed free (k1acClusterFloorAt_of_topAbove; at r = 1 " ++
      "the explicit top band 2X + B <= k + L + 2, " ++
      "k1acClusterFloorAt_of_r_one_high).  Per-start anatomy: the floor at a " ++
      "start IS the emptiness of the top W-1 slots of its endpoint window " ++
      "(k1acClusterFloorAt_iff_topSubwindow_empty); a violation pins an " ++
      "explicit shell hit there (k1acClusterFloorAt_or_witness).  HONEST: no " ++
      "in-tree atom constrains hit PLACEMENT inside a window (the shell " ++
      "sparsity hfailure caps the global COUNT only; genuineness is a SPAN " ++
      "property of the hit sequence, not a placement property of the word), " ++
      "so the interior stratum is the named irreducible remainder.",
    "SPACING AT r >= 2 (goal 2, the cycle route is DEAD - proved): the width " ++
      "is >= L + 3B + 2 at r >= 2 (exact L + 3B + 2 at r = 2, " ++
      "k1acWidth_eq_of_r_two), and r >= 1 forces L >= 15421, so EVERY period " ++
      "c <= 15430 - the whole dscPairTable range c <= 199 included - is " ++
      "strictly outrun (k1acTablePeriod_lt_width_of_r_ge_two, " ++
      "k1acDepth_lt_width_of_r_ge_two).  The single-residue discharge regime " ++
      "W <= c is EMPTY off r = 1: the wave-20 b3 = 1 route survives only at " ++
      "r = 1 with 2B + 1 <= c.",
    "SPACING AT r >= 2 (goal 2, the rarity route - the surviving mechanism): " ++
      "K1StartSpacing <-> K1SpanRarity (one genuine start per width-W span; " ++
      "k1acStartSpacing_iff_spanRarity, exact, both directions).  The " ++
      "level-set count cap TRANSCRIBED to the densepack fibre: " ++
      "Y * |gdps| <= (r+1) * emExitMass at band <= 4 (k1acGenuineCount_cap), " ++
      "and the LOCALIZED per-span form Y * |span| <= (r+1) * localExitMass " ++
      "(k1acSpanCount_cap; localExitMass = exit mass of the span's own W + r " ++
      "gap indices).  Best conditional: K1LocalExitLight (every W-span has " ++
      "(r+1) * localExitMass < 2Y) supplies the spacing atom outright " ++
      "(k1acStartSpacing_of_localExitLight); |gdps| <= 1 also suffices " ++
      "(k1acStartSpacing_of_card_le_one).  HONEST: two close heavy starts " ++
      "share their exits and produce NO contradiction in-tree (their excess " ++
      "difference is paid by <= d boundary gaps); K1LocalExitLight fails on " ++
      "spans carrying one large exit (a single gap of size >= 2Y/(r+1) " ++
      "swamps it) - the atom's content is exactly exit-size control inside " ++
      "genuine-start spans, the same currency as MdcClass0ExitMassControl.",
    "DENSITY AT b3 > 0 (goal 3, SHARP STRUCTURE proved): density <-> anchor " ++
      "surplus at some radius (k1acDensity_iff_anchorSurplus), via the " ++
      "window-shift counting lemma (move by <= d, lose <= 2d hits; " ++
      "k1acWindowCard_shift).  K1AnchorSurplus d (every genuine endpoint " ++
      "within d of a marker with 2d surplus hits) is the named landing core " ++
      "- the manuscript K.1 anchoring 'the descent lands IN a dense " ++
      "cluster', made exact; supplier wired to the verbatim v19 field " ++
      "(k1acDensePackDensityOffTableField_of_anchorSurplus).",
    "DENSITY AT b3 > 0 (goal 3, the syndetic supply QUANTIFIED - and its " ++
      "honest shortfall): at the band-3 pin the value is exactly dyadic and " ++
      "the word hits every (N, N + L + 2] window (k1acBand3_next_hit), so " ++
      "every in-shell window position carries >= 1 shell hit " ++
      "(k1acBand3_window_one_hit).  The demand is >= L/8 real " ++
      "(k1acDensity_demand_real_floor), >= 2 strictly " ++
      "(k1acDensity_demand_ge_two): the syndetic floor UNDERSHOOTS by the " ++
      "factor ~ L/8.  HONEST: single-residue (b3 = 1) pinning constrains " ++
      "START residues mod c, not endpoint hit counts - no in-tree lemma " ++
      "links residue pinning to window density; the density at b3 > 0 " ++
      "remains the landing's hard core, named K1AnchorSurplus.",
    "TOP-BAND SLOT (goal 4, THE PRICE IS PAID AT THE PINS - proved): the " ++
      "slot's only in-tree quantitative consequence, the sharpened support " ++
      "floor X <= 2(W - (r+1))(L+B+1) (mdc_topBandExitFree_support_floor), " ++
      "holds UNCONDITIONALLY at every band-2/3/4 orbit-pinned context " ++
      "(k1acTopBandPricePaid_of_pin2/3/4) from the opv syndetic floors " ++
      "X/(L+2) (resp. L+4) <= W and 2(L+2)(L+4) <= 2^L " ++
      "(k1ac_two_poly_le_two_pow).  VERDICT: the slot CANNOT be refuted " ++
      "through its price at any pinned (deep fixed-family) context - the " ++
      "cost is free there; but the price being paid does NOT prove the slot " ++
      "- DscTopBandExitFree itself stays open off the voided stratum.  " ++
      "HONEST: the opv floors exist only AT the pins; no pin-free syndetic " ++
      "floor is in-tree, so 'deep context' here means 'band-pinned " ++
      "context'.",
    "TOP-BAND SLOT (goal 4, the void EXTENDED - proved): the only in-tree " ++
      "supplier (index persistence at a fixed-family hit) empties the " ++
      "genuine densepack start set itself " ++
      "(k1acGenuine_empty_of_indexPersistence), so it voids ALL THREE K.1 " ++
      "demands at once - density, cluster floor, spacing " ++
      "(k1acK1Demands_of_indexPersistence) - exactly as it voids the " ++
      "class-0 fibre.  NOTE (in-tree, SCCPersistence): persistence onsets " ++
      "at or below the start window contradict the pressure floor, so the " ++
      "voided stratum is itself thin; the slot is a genuine structural " ++
      "residual either way.",
    "FIELD WIRING (all additive, guards verbatim): " ++
      "k1acDensePackClusterFloorField_of_interior (cluster field from the " ++
      "interior sub-atom), k1acDensePackStartSpacingField_of_spanRarity " ++
      "(spacing field from the rarity atom), " ++
      "k1acDensePackDensityOffTableField_of_anchorSurplus (density field " ++
      "from the landing core).  NAMED REMAINDER after this pass: " ++
      "K1InteriorClusterFloor, K1SpanRarity (or K1LocalExitLight at band " ++
      "<= 4), K1AnchorSurplus, and DscTopBandExitFree itself.",
    "HYGIENE: additive only - ONE new module, no existing file edited, root " ++
      "import untouched; no sorry / admit / new axiom / native_decide; " ++
      "every key declaration passes #print axioms within [propext, " ++
      "Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem k1AtomsClosureStatus_nonempty : k1AtomsClosureStatus ≠ [] := by
  simp [k1AtomsClosureStatus]

/-! ## Part 6.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]` or
fewer. -/

#print axioms k1acClusterFloor_iff_at
#print axioms k1acClusterFloorAt_iff_topSubwindow_empty
#print axioms k1acClusterFloorAt_of_topAbove
#print axioms k1acClusterFloorAt_of_r_one_high
#print axioms k1acClusterFloor_iff_interior
#print axioms k1acClusterFloorAt_or_witness
#print axioms k1acClusterFloor_of_topAbove
#print axioms k1acDensePackClusterFloorField_of_interior
#print axioms k1acWidth_eq_of_r_two
#print axioms k1acWidth_lower_of_r_ge_two
#print axioms k1acDepth_lt_width_of_r_ge_two
#print axioms k1acTablePeriod_lt_width_of_r_ge_two
#print axioms k1acGenuine_subset_starts
#print axioms k1acGenuine_Y_le
#print axioms k1acGenuineCount_cap
#print axioms k1acStartSpacing_iff_spanRarity
#print axioms k1acStartSpacing_of_card_le_one
#print axioms k1acSpanCount_cap
#print axioms k1acSpanRarity_of_localExitLight
#print axioms k1acStartSpacing_of_localExitLight
#print axioms k1acDensePackStartSpacingField_of_spanRarity
#print axioms k1acWindowCard_shift
#print axioms k1acDensity_of_anchorSurplus
#print axioms k1acDensity_iff_anchorSurplus
#print axioms k1acDensePackDensityOffTableField_of_anchorSurplus
#print axioms k1acBand3_next_hit
#print axioms k1acBand3_window_one_hit
#print axioms k1acDensity_demand_real_floor
#print axioms k1acDensity_demand_ge_two
#print axioms k1ac_two_poly_le_two_pow
#print axioms k1ac_price_of_div_floor
#print axioms k1acTopBandPricePaid_of_pin2
#print axioms k1acTopBandPricePaid_of_pin3
#print axioms k1acTopBandPricePaid_of_pin4
#print axioms k1acGenuine_empty_of_indexPersistence
#print axioms k1acClusterFloor_of_emptyStarts
#print axioms k1acStartSpacing_of_emptyStarts
#print axioms k1acK1Demands_of_indexPersistence
#print axioms k1AtomsClosureStatus_nonempty

end

end Erdos260
