import Erdos260.ReturnClass4Closure
import Erdos260.ReturnCarryEndpointCore
import Erdos260.CNLClass1Closure

/-!
# Return / Class 4 — cycle density, sliding-window rigidity, and the digit reductions
(`ReturnClass4CycleClosure`, wave 3)

This module (NEW; it edits no existing file) pushes the two wave-2 Return residual fields —
`Class4FibreSmall` and the three-field `ReturnClass4DigitResidual` — strictly further.  Everything
is proved from the routing/orbit arithmetic of the canonical objects; no fabricated witnesses, no
new axioms.

## 1.  `Class4FibreSmall` (the ungated count) — two new unconditional engines

* **Sliding-window rigidity (the telescoping engine).**  Class-4 starts all satisfy the gap-window
  floor `129L + 64 ≤ 64·(a(k+r+1) − a(k))` (`class4Fibre_hitPosition_floor`).  Floor-windows at
  starts `≥ r+1` apart are disjoint, so the floors *telescope* against the total hit-position
  span:
  - `slidingWindow_card_mul_le_span` (generic): `|S|·F ≤ (r+1)·(a(hi+r) − a(lo))` for any set of
    starts in `[lo, hi)` whose windows all clear `F`;
  - `class4Fibre_card_mul_floor_le_span`: `|fibre₄|·(129L+64) ≤ (r+1)·64·(a(i+K+r) − a(i))` —
    the honest ungated population bound (the span includes the unconstrained top escape gaps);
  - `class4Fibre_interior_card_mul_floor_le_X`: the INTERIOR sub-fibre (descent window inside the
    shell window) has `|fibre₄^int|·(129L+64) ≤ (r+1)·64·X` — in-window hit positions live in
    `(X, 2X]`, so the interior span is `< X`.  This FORMALIZES the wave-2 claim that the model
    only bounds the interior population by `≈ (r+1)·64X/(129L)`;
  - `class4Fibre_card_mul_floor_le_global`: `|fibre₄|·(129L+64) ≤ (r+1)·(129L+64) + (r+1)·64·X`
    (interior + top band) — the sharpest fully unconditional global count of this pass;
  - **two new per-shell closure gates** for the exact capstone field `|fibre₄| ≤ r+1`:
    the two-window span gate `64·(a(i+K+r) − a(i)) < 2·(129L+64)`
    (`class4Fibre_card_le_succ_r_of_span_gate`: two disjoint floor-windows cannot fit) and the
    in-window span gate `64·(a(i+K−1) − a(i)) < 129L+64`
    (`class4Fibre_topBand_of_inWindow_span` / `class4Fibre_card_le_succ_r_of_inWindow_span`:
    interior windows cannot even reach the floor, so the fibre sits in the top `r+1` band).
    Both are INCOMPARABLE with the wave-2 K.1 gate `64(r+1)(L+B+1) < 129L+64` (they constrain
    realized positions, not the worst-case gap ceiling).

* **Band-2 cycle density (the orbit engine).**  Class 4 reads `canonGap q K_k = 2` at `k`
  (`mem_class4Fibre_iff`), and the orbit `k ↦ K_k` is purely periodic from index 1 with period
  `c ≤ q` (`slopeOrbit_exists_period`, imported).  Hence class-4-eligible indices sit on the
  band-2 residues of the cycle:
  - `periodic_filter_card_le` (generic): a `c`-periodic reading hits a fixed value at most
    `t·b` times on any window covered by `t` blocks, `b` = per-cycle count;
  - `class4Fibre_card_le_cycle_count`: `|fibre₄| ≤ t·b₂(c)` whenever `K ≤ t·c`, with
    `b₂(c) = #{j ∈ [1,c] : canonGap q K_j = 2}` — the per-(q,K₀) FINITE cycle inequality;
  - `class4Fibre_empty_of_cycle_band_free`: a band-2-free period closes the fibre outright
    (the class-4 mirror of `class1Fibre_empty_of_cycle_band_free`);
  - `band2_run_forces_three_mul_or_pow_le`: **band-2 run rigidity** — `s` consecutive band-2
    orbit indices force `3K_j = q` (the fixed point) or `2·4^{s−1} ≤ q`: deviations from the
    fixed point `q/3` QUADRUPLE under the band-2 step `K ↦ 4K − q`, so off the `3 ∣ q` family
    every band-2 run has length `≤ log₄(q/2) + 1` — `b₂` is structurally small off the fixed
    point (`band2_run_pow_le_of_three_not_dvd`).  At the fixed point `q = 3K` (the proved wave-2
    obstruction) the cycle bound is vacuous (`b₂ = c`) and ONLY the sliding-window engine bites.

* **The combined bridge** `class4FibreSmall_of_gates`: `Class4FibreSmall` holds as soon as every
  ctx satisfies ONE of: the K.1 gate, the two-window span gate, the in-window span gate, or a
  cycle-count bound `t·b₂ ≤ r+1`.  (Per-ctx closers are also exported individually.)

## 2.  `class4Interior` — the top-band finite check

`class4Interior` is exactly top-band emptiness (`class4Interior_iff_topBand_empty`, wave 2), and
the top band has `≤ r+1` positions.  New closers:

* `class4Interior_of_topBand_band_free`: if the orbit avoids band 2 at the `≤ r+1` top-band
  indices, the interior field HOLDS — no gate, pure orbit reading;
* `class4Interior_of_cycle_topBand_check`: with a period `c`, the reading at a top-band index
  `k` equals the cycle reading at the explicit residue `(k−1) % c + 1 ∈ [1,c]` — the interior
  field reduces to `≤ r+1` FINITE cycle evaluations per ctx;
* `class4Interior_of_cycle_band_free`: a band-2-free cycle gives interior via emptiness.
  The `q = 3K` fixed-point family is the honest hard case: there EVERY residue is band 2
  (`canonGap_orbit_three_mul`, wave 2), so the top-band check cannot fire and interior remains
  genuine window content.

## 3.  The digit fields — the genuine attempt and its honest outcome

The M.2.1 self-referential congruence at the pinned positions (`returnSelfRefKey_gapDiv`) yields
SPACING (`2^{v₂} ∣ z − x`), and the window pins confine same-slice pairs to `z − x < K`.  The
attempt outcome:

* **A genuine partial closure of `hzero`** (`returnDigit_hzero_of_carryVal2_large`): whenever the
  fibre's carry valuations satisfy `K ≤ 2^{carryVal2 k}`, same-key pairs are IMPOSSIBLE
  (`returnSelfRef_pair_false_of_carryVal2_large`: the spacing divisor exceeds the window width),
  so the (Z) zero-run field holds VACUOUSLY — the digit residual collapses to
  `hcleanStep + interior` (`ReturnClass4DigitResidual.ofCarryVal2Large`).  This is spacing
  arithmetic, not fabricated emptiness: the slices genuinely cannot hold two starts.
* **The maxima reduction** (`returnDigit_cleanStep_of_hzero_max`,
  `ReturnClass4DigitResidual.ofSelfRefMaxCleanStep`): given `hzero`, the clean step
  `d(k+1) = 0` is FORCED at every non-maximal slice member (the zero-run to the next member
  covers `k+1`), so `hcleanStep` shrinks to the `≤ #slices` per-slice MAXIMA.
* **The consecutive-pair reduction** (`returnDigit_hzero_of_consecutive`, chaining the imported
  `zeroRun_allPairs_of_consecutive`): `hzero` shrinks to consecutive same-slice pairs; and under
  per-slice adjacency the whole of `hzero` follows from `hcleanStep` alone
  (`returnDigit_hzero_of_adjacent_consecutive`).
* **The honest obstruction (unchanged, now sharper).**  The remaining digit content is exactly:
  the clean step at the `≤ #slices` slice maxima, plus the zero-runs at non-adjacent consecutive
  pairs with `carryVal2 < log₂ K`.  These read `ctx.d` at positions the class-4 pins never
  constrain (the pins fix hit gaps at indices `≥ k` and the orbit at `k`; the proved forcing
  direction `anchoredSeed_forces_clean_step` shows every inhabitant carries this content).  The
  M.2.1 congruence technique cannot produce digit VALUES — it is a statement about key equality,
  i.e. about spacing.  No unconditional closure of the digit fields is claimed.

No `sorry`, `admit`, `axiom`, or `native_decide`.  `ofEmptyFibre` is consumed only through the
proved cycle-emptiness theorem.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## Part 1.  The sliding-window rigidity engine

Floor-satisfying windows at starts `≥ r+1` apart are disjoint blocks of `r+1` consecutive gaps,
so their floors add up inside the total position span.  The engine is generic over any monotone
position function; class 4 instantiates it at the 64-scaled actual hit positions. -/

/-- **The fuel-indexed telescoping bound.**  If every start in `S ⊆ [lo, hi)` has its
`(r+1)`-gap window sum at least `F` (in position form: `F ≤ a(k+r+1) − a(k)`), then
`|S|·F ≤ (r+1)·(a(hi+r) − a(lo))`: peel the minimum `m`, charge its `≤ r+1` companions in
`[m, m+r]` to the window `[a(m), a(m+r+1)]`, and recurse above `m+r+1`. -/
theorem slidingWindow_card_mul_le_span_fuel (a : ℕ → ℕ) (ha : Monotone a) (F r : ℕ) :
    ∀ fuel lo hi : ℕ, ∀ S : Finset ℕ, hi ≤ lo + fuel →
      (∀ k ∈ S, lo ≤ k ∧ k < hi) →
      (∀ k ∈ S, F ≤ a (k + r + 1) - a k) →
      S.card * F ≤ (r + 1) * (a (hi + r) - a lo) := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi S hfuel hsub hfloor
      have hS : S = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro k hk
        have := hsub k hk
        omega
      rw [hS]
      simp
  | succ fuel ih =>
      intro lo hi S hfuel hsub hfloor
      rcases S.eq_empty_or_nonempty with rfl | hne
      · simp
      · have hmS : S.min' hne ∈ S := S.min'_mem hne
        have hmwin := hsub (S.min' hne) hmS
        have hmfloor := hfloor (S.min' hne) hmS
        -- the near block `[m, m+r]` and the far tail `≥ m+r+1`
        have hsplit : S ⊆ S.filter (fun k => k ≤ S.min' hne + r)
            ∪ S.filter (fun k => ¬ k ≤ S.min' hne + r) := by
          intro x hx
          rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
          by_cases hxr : x ≤ S.min' hne + r
          · exact Or.inl ⟨hx, hxr⟩
          · exact Or.inr ⟨hx, hxr⟩
        have hcards : S.card ≤ (S.filter (fun k => k ≤ S.min' hne + r)).card
            + (S.filter (fun k => ¬ k ≤ S.min' hne + r)).card :=
          le_trans (Finset.card_le_card hsplit) (Finset.card_union_le _ _)
        have hnear : (S.filter (fun k => k ≤ S.min' hne + r)).card ≤ r + 1 := by
          have hsub' : S.filter (fun k => k ≤ S.min' hne + r)
              ⊆ Finset.Icc (S.min' hne) (S.min' hne + r) := by
            intro x hx
            rw [Finset.mem_filter] at hx
            rw [Finset.mem_Icc]
            exact ⟨S.min'_le x hx.1, hx.2⟩
          calc (S.filter (fun k => k ≤ S.min' hne + r)).card
              ≤ (Finset.Icc (S.min' hne) (S.min' hne + r)).card := Finset.card_le_card hsub'
            _ ≤ r + 1 := by rw [Nat.card_Icc]; omega
        have htail : (S.filter (fun k => ¬ k ≤ S.min' hne + r)).card * F
            ≤ (r + 1) * (a (hi + r) - a (S.min' hne + r + 1)) := by
          apply ih (S.min' hne + r + 1) hi _ (by omega)
          · intro k hk
            rw [Finset.mem_filter] at hk
            exact ⟨by have := hk.2; omega, (hsub k hk.1).2⟩
          · intro k hk
            rw [Finset.mem_filter] at hk
            exact hfloor k hk.1
        have hu1 : a lo ≤ a (S.min' hne) := ha hmwin.1
        have hu2 : a (S.min' hne) ≤ a (S.min' hne + r + 1) := ha (by omega)
        have hu3 : a (S.min' hne + r + 1) ≤ a (hi + r) := ha (by omega)
        calc S.card * F
            ≤ ((S.filter (fun k => k ≤ S.min' hne + r)).card
                + (S.filter (fun k => ¬ k ≤ S.min' hne + r)).card) * F :=
              Nat.mul_le_mul_right F hcards
          _ = (S.filter (fun k => k ≤ S.min' hne + r)).card * F
                + (S.filter (fun k => ¬ k ≤ S.min' hne + r)).card * F := add_mul _ _ _
          _ ≤ (r + 1) * F + (r + 1) * (a (hi + r) - a (S.min' hne + r + 1)) :=
              add_le_add (Nat.mul_le_mul_right F hnear) htail
          _ = (r + 1) * (F + (a (hi + r) - a (S.min' hne + r + 1))) := (mul_add _ _ _).symm
          _ ≤ (r + 1) * (a (hi + r) - a lo) := Nat.mul_le_mul_left _ (by omega)

/-- **The sliding-window density bound** (generic): floor-satisfying starts in `[lo, hi)` obey
`|S|·F ≤ (r+1)·(a(hi+r) − a(lo))`. -/
theorem slidingWindow_card_mul_le_span (a : ℕ → ℕ) (ha : Monotone a) {F r lo hi : ℕ}
    {S : Finset ℕ} (hsub : ∀ k ∈ S, lo ≤ k ∧ k < hi)
    (hfloor : ∀ k ∈ S, F ≤ a (k + r + 1) - a k) :
    S.card * F ≤ (r + 1) * (a (hi + r) - a lo) :=
  slidingWindow_card_mul_le_span_fuel a ha F r hi lo hi S (by omega) hsub hfloor

/-- **The two-window span criterion** (generic): if the total span cannot host TWO disjoint
floor-windows (`a(hi+r) − a(lo) < 2F`), the floor-satisfying starts fit in one block:
`|S| ≤ r + 1`. -/
theorem slidingWindow_card_le_succ_of_span (a : ℕ → ℕ) (ha : Monotone a) {F r lo hi : ℕ}
    {S : Finset ℕ} (hsub : ∀ k ∈ S, lo ≤ k ∧ k < hi)
    (hfloor : ∀ k ∈ S, F ≤ a (k + r + 1) - a k)
    (hspan : a (hi + r) - a lo < 2 * F) :
    S.card ≤ r + 1 := by
  by_contra hcon
  push Not at hcon
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hmS : S.min' hne ∈ S := S.min'_mem hne
  have hnotsub : ¬ S ⊆ Finset.Icc (S.min' hne) (S.min' hne + r) := by
    intro hsub'
    have := Finset.card_le_card hsub'
    rw [Nat.card_Icc] at this
    omega
  obtain ⟨z, hzS, hz⟩ := Finset.not_subset.mp hnotsub
  rw [Finset.mem_Icc] at hz
  push Not at hz
  have hzr : S.min' hne + r < z := hz (S.min'_le z hzS)
  have hf1 := hfloor (S.min' hne) hmS
  have hf2 := hfloor z hzS
  have hw1 := hsub (S.min' hne) hmS
  have hw2 := hsub z hzS
  have hu1 : a lo ≤ a (S.min' hne) := ha hw1.1
  have hu2 : a (S.min' hne) ≤ a (S.min' hne + r + 1) := ha (by omega)
  have hu3 : a (S.min' hne + r + 1) ≤ a z := ha (by omega)
  have hu4 : a z ≤ a (z + r + 1) := ha (by omega)
  have hu5 : a (z + r + 1) ≤ a (hi + r) := ha (by omega)
  omega

/-! ## Part 2.  The class-4 pins in telescoped hit-position form -/

/-- Every class-4 start lies in the dyadic shell index window (the `olcFibre` form). -/
theorem olcFibre_mem_window (ctx : ActualFailureContext) {k : ℕ} (hk : k ∈ olcFibre ctx) :
    ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X ≤ k
      ∧ k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card := by
  rw [olcFibre_def] at hk
  exact class4Fibre_mem_window ctx hk

/-- **The class-4 gap floor in telescoped hit-position form**: every class-4 start realizes
`129L + 64 ≤ 64·(a(k+r+1) − a(k))` — the inequality the sliding-window engine consumes. -/
theorem class4Fibre_hitPosition_floor (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ olcFibre ctx) :
    129 * shellLadderDepth ctx + 64
      ≤ 64 * (ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) - ctx.n24CarryData.a k) := by
  rw [olcFibre_def] at hk
  have h := ((mem_class4Fibre_iff ctx k).mp hk).2.1
  rwa [ctx.n24CarryData.carry.hits.gapWindow_hitGap_eq] at h

/-- The class-4 band-2 pin in the `olcFibre` form. -/
theorem olcFibre_canonGap_two (ctx : ActualFailureContext) {k : ℕ} (hk : k ∈ olcFibre ctx) :
    canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
  rw [olcFibre_def] at hk
  exact class4Fibre_canonGap_eq ctx hk

/-! ## Part 3.  The sliding-window population bounds for the class-4 fibre -/

/-- **The honest ungated class-4 population bound (full window)**:
`|fibre₄|·(129L+64) ≤ (r+1)·64·(a(i+K+r) − a(i))`.  The right side includes the unconstrained
top escape gaps `a(i+K), …, a(i+K+r)` — this is exactly why the bound does not close the count
outright on deep shells. -/
theorem class4Fibre_card_mul_floor_le_span (ctx : ActualFailureContext) :
    (olcFibre ctx).card * (129 * shellLadderDepth ctx + 64)
      ≤ (ctx.n24CarryData.r + 1)
        * (64 * (ctx.n24CarryData.a
              (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
                + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
            - ctx.n24CarryData.a
              (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X))) := by
  have hmono : Monotone ctx.n24CarryData.a := ctx.n24CarryData.carry.hits.strict.monotone
  have hmono64 : Monotone (fun j => 64 * ctx.n24CarryData.a j) :=
    fun x y hxy => Nat.mul_le_mul_left 64 (hmono hxy)
  have hsub : ∀ k ∈ olcFibre ctx,
      ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X ≤ k
        ∧ k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card :=
    fun k hk => olcFibre_mem_window ctx hk
  have hfloor : ∀ k ∈ olcFibre ctx,
      129 * shellLadderDepth ctx + 64
        ≤ 64 * ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1)
          - 64 * ctx.n24CarryData.a k := by
    intro k hk
    have hfl := class4Fibre_hitPosition_floor ctx hk
    have hm : ctx.n24CarryData.a k ≤ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) :=
      hmono (by omega)
    omega
  have hmaster : (olcFibre ctx).card * (129 * shellLadderDepth ctx + 64)
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
    omega
  rw [hfac] at hmaster
  exact hmaster

/-- **The two-window span gate** (NEW per-shell closure of the capstone count): if the total
window span cannot host two disjoint floor-windows, `64·(a(i+K+r) − a(i)) < 2·(129L+64)`, then
`|fibre₄| ≤ r + 1` — with no K.1 gate and no orbit hypothesis. -/
theorem class4Fibre_card_le_succ_r_of_span_gate (ctx : ActualFailureContext)
    (hspan : 64 * (ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
        - ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X))
      < 2 * (129 * shellLadderDepth ctx + 64)) :
    (olcFibre ctx).card ≤ ctx.n24CarryData.r + 1 := by
  have hmono : Monotone ctx.n24CarryData.a := ctx.n24CarryData.carry.hits.strict.monotone
  have hmono64 : Monotone (fun j => 64 * ctx.n24CarryData.a j) :=
    fun x y hxy => Nat.mul_le_mul_left 64 (hmono hxy)
  have hsub : ∀ k ∈ olcFibre ctx,
      ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X ≤ k
        ∧ k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card :=
    fun k hk => olcFibre_mem_window ctx hk
  have hfloor : ∀ k ∈ olcFibre ctx,
      129 * shellLadderDepth ctx + 64
        ≤ 64 * ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1)
          - 64 * ctx.n24CarryData.a k := by
    intro k hk
    have hfl := class4Fibre_hitPosition_floor ctx hk
    have hm : ctx.n24CarryData.a k ≤ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) :=
      hmono (by omega)
    omega
  have hspan64 : 64 * ctx.n24CarryData.a
        (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
      - 64 * ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
      < 2 * (129 * shellLadderDepth ctx + 64) := by
    omega
  exact slidingWindow_card_le_succ_of_span (fun j => 64 * ctx.n24CarryData.a j) hmono64
    hsub hfloor hspan64

/-- **The interior population bound**: starts whose descent window stays inside the shell window
satisfy `|fibre₄^int|·(129L+64) ≤ (r+1)·64·(a(i+K−1) − a(i))` — the interior windows telescope
inside the in-window position range. -/
theorem class4Fibre_interior_card_mul_floor_le (ctx : ActualFailureContext) :
    ((olcFibre ctx).filter (fun k =>
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card)).card
        * (129 * shellLadderDepth ctx + 64)
      ≤ (ctx.n24CarryData.r + 1)
        * (64 * (ctx.n24CarryData.a
              (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
                + (supportShell ctx.shell.d ctx.shell.X).card - 1)
            - ctx.n24CarryData.a
              (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X))) := by
  have hmono : Monotone ctx.n24CarryData.a := ctx.n24CarryData.carry.hits.strict.monotone
  have hmono64 : Monotone (fun j => 64 * ctx.n24CarryData.a j) :=
    fun x y hxy => Nat.mul_le_mul_left 64 (hmono hxy)
  have hKr : ctx.n24CarryData.r + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
    cnlMulti_r_add_one_le_width ctx
  have hsub : ∀ k ∈ (olcFibre ctx).filter (fun k =>
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card),
      ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X ≤ k
        ∧ k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    have hwin := olcFibre_mem_window ctx hk.1
    have hint := hk.2
    exact ⟨hwin.1, by omega⟩
  have hfloor : ∀ k ∈ (olcFibre ctx).filter (fun k =>
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card),
      129 * shellLadderDepth ctx + 64
        ≤ 64 * ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1)
          - 64 * ctx.n24CarryData.a k := by
    intro k hk
    rw [Finset.mem_filter] at hk
    have hfl := class4Fibre_hitPosition_floor ctx hk.1
    have hm : ctx.n24CarryData.a k ≤ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) :=
      hmono (by omega)
    omega
  have hmaster : ((olcFibre ctx).filter (fun k =>
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card)).card
          * (129 * shellLadderDepth ctx + 64)
      ≤ (ctx.n24CarryData.r + 1)
        * (64 * ctx.n24CarryData.a
              (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
                + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1)
                + ctx.n24CarryData.r)
          - 64 * ctx.n24CarryData.a
              (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)) :=
    slidingWindow_card_mul_le_span (fun j => 64 * ctx.n24CarryData.a j) hmono64 hsub hfloor
  have hidx : ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
      + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1)
      + ctx.n24CarryData.r
      = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card - 1 := by
    omega
  rw [hidx] at hmaster
  have hfac : 64 * ctx.n24CarryData.a
        (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card - 1)
      - 64 * ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
      = 64 * (ctx.n24CarryData.a
            (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card - 1)
          - ctx.n24CarryData.a
            (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)) := by
    omega
  rw [hfac] at hmaster
  exact hmaster

/-- **The interior population is `X`-bounded** (the wave-2 audit claim, now a THEOREM):
`|fibre₄^int|·(129L+64) ≤ (r+1)·64·X` — in-window hit positions live in `(X, 2X]`, so the
interior span is below `X`.  This is the honest model-level ceiling: the interior count can
genuinely reach `≈ (r+1)·64·X/(129L)`, exponentially beyond `r+1` on deep shells. -/
theorem class4Fibre_interior_card_mul_floor_le_X (ctx : ActualFailureContext) :
    ((olcFibre ctx).filter (fun k =>
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card)).card
        * (129 * shellLadderDepth ctx + 64)
      ≤ (ctx.n24CarryData.r + 1) * (64 * ctx.shell.X) := by
  have h := class4Fibre_interior_card_mul_floor_le ctx
  have hKr : ctx.n24CarryData.r + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
    cnlMulti_r_add_one_le_width ctx
  have h2X : ctx.n24CarryData.a
      (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card - 1) ≤ 2 * ctx.shell.X :=
    ctx.n24CarryData.carry.hits.a_le_two_mul_of_lt_add_card ctx.shell.X (by omega)
  have hXa : ctx.shell.X < ctx.n24CarryData.a
      (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X) :=
    ctx.n24CarryData.carry.hits.firstIndexAbove_spec ctx.shell.X
  have hdiff : ctx.n24CarryData.a
        (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card - 1)
      - ctx.n24CarryData.a (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
      ≤ ctx.shell.X := by omega
  calc ((olcFibre ctx).filter (fun k =>
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card)).card
        * (129 * shellLadderDepth ctx + 64)
      ≤ (ctx.n24CarryData.r + 1)
        * (64 * (ctx.n24CarryData.a
              (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
                + (supportShell ctx.shell.d ctx.shell.X).card - 1)
            - ctx.n24CarryData.a
              (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X))) := h
    _ ≤ (ctx.n24CarryData.r + 1) * (64 * ctx.shell.X) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 64 hdiff)

/-- **The global unconditional class-4 population bound**:
`|fibre₄|·(129L+64) ≤ (r+1)·(129L+64) + (r+1)·64·X` — interior (sliding-window telescoping
against the in-window span `< X`) plus the top `r+1` boundary band. -/
theorem class4Fibre_card_mul_floor_le_global (ctx : ActualFailureContext) :
    (olcFibre ctx).card * (129 * shellLadderDepth ctx + 64)
      ≤ (ctx.n24CarryData.r + 1) * (129 * shellLadderDepth ctx + 64)
        + (ctx.n24CarryData.r + 1) * (64 * ctx.shell.X) := by
  have hint := class4Fibre_interior_card_mul_floor_le_X ctx
  have hKr : ctx.n24CarryData.r + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
    cnlMulti_r_add_one_le_width ctx
  have hsplit : olcFibre ctx ⊆
      (olcFibre ctx).filter (fun k =>
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card)
      ∪ (olcFibre ctx).filter (fun k =>
        ¬ (k + ctx.n24CarryData.r + 1
            < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
                + (supportShell ctx.shell.d ctx.shell.X).card)) := by
    intro x hx
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hc : x + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card
    · exact Or.inl ⟨hx, hc⟩
    · exact Or.inr ⟨hx, hc⟩
  have htop : ((olcFibre ctx).filter (fun k =>
      ¬ (k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card))).card
      ≤ ctx.n24CarryData.r + 1 := by
    have hsub2 : (olcFibre ctx).filter (fun k =>
        ¬ (k + ctx.n24CarryData.r + 1
            < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
                + (supportShell ctx.shell.d ctx.shell.X).card))
        ⊆ Finset.Ico
            (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1))
            (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have hwin := olcFibre_mem_window ctx hx.1
      have hge := hx.2
      rw [Finset.mem_Ico]
      omega
    calc ((olcFibre ctx).filter (fun k =>
        ¬ (k + ctx.n24CarryData.r + 1
            < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
                + (supportShell ctx.shell.d ctx.shell.X).card))).card
        ≤ (Finset.Ico
            (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1))
            (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card)).card :=
          Finset.card_le_card hsub2
      _ ≤ ctx.n24CarryData.r + 1 := by rw [Nat.card_Ico]; omega
  have hcards : (olcFibre ctx).card
      ≤ ((olcFibre ctx).filter (fun k =>
          k + ctx.n24CarryData.r + 1
            < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
                + (supportShell ctx.shell.d ctx.shell.X).card)).card
        + ((olcFibre ctx).filter (fun k =>
          ¬ (k + ctx.n24CarryData.r + 1
              < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
                  + (supportShell ctx.shell.d ctx.shell.X).card))).card :=
    le_trans (Finset.card_le_card hsplit) (Finset.card_union_le _ _)
  have htopF : ((olcFibre ctx).filter (fun k =>
      ¬ (k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card))).card
        * (129 * shellLadderDepth ctx + 64)
      ≤ (ctx.n24CarryData.r + 1) * (129 * shellLadderDepth ctx + 64) :=
    Nat.mul_le_mul_right _ htop
  have hcardsF := Nat.mul_le_mul_right (129 * shellLadderDepth ctx + 64) hcards
  rw [add_mul] at hcardsF
  omega

/-- **The in-window span gate forces top-band confinement** (NEW): if the in-window hit span
cannot reach the floor, `64·(a(i+K−1) − a(i)) < 129L + 64`, every class-4 start overruns the
shell window. -/
theorem class4Fibre_topBand_of_inWindow_span (ctx : ActualFailureContext)
    (hspan : 64 * (ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - 1)
        - ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X))
      < 129 * shellLadderDepth ctx + 64)
    {k : ℕ} (hk : k ∈ olcFibre ctx) :
    ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
      + (supportShell ctx.shell.d ctx.shell.X).card ≤ k + ctx.n24CarryData.r + 1 := by
  by_contra hint
  have hwin := olcFibre_mem_window ctx hk
  have hfl := class4Fibre_hitPosition_floor ctx hk
  have hmono : Monotone ctx.n24CarryData.a := ctx.n24CarryData.carry.hits.strict.monotone
  have hm1 : ctx.n24CarryData.a (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
      ≤ ctx.n24CarryData.a k := hmono hwin.1
  have hm2 : ctx.n24CarryData.a k ≤ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) :=
    hmono (by omega)
  have hm3 : ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1)
      ≤ ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - 1) :=
    hmono (by omega)
  omega

/-- **The in-window span gate count** (NEW per-shell closure of the capstone count): under
`64·(a(i+K−1) − a(i)) < 129L + 64` the class-4 fibre sits inside the top `r+1` band, so
`|fibre₄| ≤ r + 1`. -/
theorem class4Fibre_card_le_succ_r_of_inWindow_span (ctx : ActualFailureContext)
    (hspan : 64 * (ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - 1)
        - ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X))
      < 129 * shellLadderDepth ctx + 64) :
    (olcFibre ctx).card ≤ ctx.n24CarryData.r + 1 := by
  have hsub : olcFibre ctx
      ⊆ Finset.Ico
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1))
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) := by
    intro k hk
    have hover := class4Fibre_topBand_of_inWindow_span ctx hspan hk
    have hwin := olcFibre_mem_window ctx hk
    rw [Finset.mem_Ico]
    omega
  calc (olcFibre ctx).card
      ≤ (Finset.Ico
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1))
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card)).card :=
        Finset.card_le_card hsub
    _ ≤ ctx.n24CarryData.r + 1 := by rw [Nat.card_Ico]; omega

/-! ## Part 4.  The band-2 cycle-density engine

The orbit reading is periodic from index `1` (period `c ≤ q`, imported machinery), so class-4
eligibility is confined to the band-2 residues of the cycle: per block of `c` consecutive
indices at most `b₂ = #{j ∈ [1,c] : canonGap q K_j = 2}` candidates. -/

/-- Period propagation: a `c`-periodic reading (from index 1) is `t·c`-periodic. -/
theorem periodic_add_mul {f : ℕ → ℕ} {c : ℕ}
    (hper : ∀ m, 1 ≤ m → f (m + c) = f m) :
    ∀ (t m : ℕ), 1 ≤ m → f (m + t * c) = f m := by
  intro t
  induction t with
  | zero => intro m hm; simp
  | succ t ih =>
      intro m hm
      have h1 : m + (t + 1) * c = m + t * c + c := by ring
      rw [h1, hper (m + t * c) (le_trans hm (Nat.le_add_right m (t * c))), ih m hm]

/-- Residue normalization: a `c`-periodic reading at `k ≥ 1` equals its reading at the canonical
cycle residue `(k − 1) % c + 1 ∈ [1, c]`. -/
theorem periodic_eq_residue {f : ℕ → ℕ} {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → f (m + c) = f m) {k : ℕ} (hk : 1 ≤ k) :
    f k = f ((k - 1) % c + 1) := by
  have hsplit : (k - 1) % c + (k - 1) / c * c = k - 1 := Nat.mod_add_div' (k - 1) c
  have hidx : ((k - 1) % c + 1) + (k - 1) / c * c = k := by
    set A := (k - 1) % c with hA
    set B := (k - 1) / c * c with hB
    omega
  calc f k = f (((k - 1) % c + 1) + (k - 1) / c * c) := by rw [hidx]
    _ = f ((k - 1) % c + 1) :=
        periodic_add_mul hper ((k - 1) / c) ((k - 1) % c + 1)
          (Nat.succ_le_succ (Nat.zero_le _))

/-- **Single-block cycle count**: on any block of `≤ c` consecutive indices starting at `lo ≥ 1`,
the number of indices reading value `v` is at most the per-cycle count over `[1, c]` — the
residue map is injective on the block and preserves the reading. -/
theorem periodic_filter_block_card_le {f : ℕ → ℕ} {c v : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → f (m + c) = f m) {lo n : ℕ} (hlo : 1 ≤ lo) (hn : n ≤ c) :
    ((Finset.Ico lo (lo + n)).filter (fun k => f k = v)).card
      ≤ ((Finset.Icc 1 c).filter (fun j => f j = v)).card := by
  apply Finset.card_le_card_of_injOn (fun k => (k - 1) % c + 1)
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc] at hk ⊢
    obtain ⟨⟨hk1, hk2⟩, hkv⟩ := hk
    have hk1' : 1 ≤ k := by omega
    have hmod : (k - 1) % c < c := Nat.mod_lt _ (by omega)
    refine ⟨⟨Nat.succ_le_succ (Nat.zero_le _), hmod⟩, ?_⟩
    rw [← periodic_eq_residue hc hper hk1']
    exact hkv
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hx hy
    have hxy' : (x - 1) % c + 1 = (y - 1) % c + 1 := hxy
    have hmodeq : (x - 1) % c = (y - 1) % c := Nat.add_right_cancel hxy'
    by_contra hne
    rcases Nat.lt_or_ge x y with hlt | hge
    · have hdvd : c ∣ (y - 1) - (x - 1) :=
        (Nat.modEq_iff_dvd' (by omega : x - 1 ≤ y - 1)).mp hmodeq
      have hpos : 0 < (y - 1) - (x - 1) := by omega
      have hle := Nat.le_of_dvd hpos hdvd
      omega
    · have hlt : y < x := by omega
      have hdvd : c ∣ (x - 1) - (y - 1) :=
        (Nat.modEq_iff_dvd' (by omega : y - 1 ≤ x - 1)).mp hmodeq.symm
      have hpos : 0 < (x - 1) - (y - 1) := by omega
      have hle := Nat.le_of_dvd hpos hdvd
      omega

/-- **Multi-block cycle count**: on any window of `n ≤ t·c` consecutive indices starting at
`lo ≥ 1`, the number of indices reading `v` is at most `t` times the per-cycle count. -/
theorem periodic_filter_card_le {f : ℕ → ℕ} {c v : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → f (m + c) = f m) :
    ∀ (t lo n : ℕ), 1 ≤ lo → n ≤ t * c →
      ((Finset.Ico lo (lo + n)).filter (fun k => f k = v)).card
        ≤ t * ((Finset.Icc 1 c).filter (fun j => f j = v)).card := by
  intro t
  induction t with
  | zero =>
      intro lo n hlo hn
      rw [Nat.zero_mul] at hn
      have hn0 : n = 0 := by omega
      subst hn0
      simp
  | succ t ih =>
      intro lo n hlo hn
      by_cases hnc : n ≤ c
      · calc ((Finset.Ico lo (lo + n)).filter (fun k => f k = v)).card
            ≤ ((Finset.Icc 1 c).filter (fun j => f j = v)).card :=
              periodic_filter_block_card_le hc hper hlo hnc
          _ = 1 * ((Finset.Icc 1 c).filter (fun j => f j = v)).card := (one_mul _).symm
          _ ≤ (t + 1) * ((Finset.Icc 1 c).filter (fun j => f j = v)).card :=
              Nat.mul_le_mul_right _ (by omega)
      · push Not at hnc
        have hio : Finset.Ico lo (lo + n)
            = Finset.Ico lo (lo + c) ∪ Finset.Ico (lo + c) (lo + n) :=
          (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
        have hrest : lo + n = lo + c + (n - c) := by omega
        rw [Nat.succ_mul] at hn
        have htail := ih (lo + c) (n - c) (by omega) (Nat.sub_le_iff_le_add.mpr hn)
        rw [← hrest] at htail
        calc ((Finset.Ico lo (lo + n)).filter (fun k => f k = v)).card
            = ((Finset.Ico lo (lo + c)).filter (fun k => f k = v)
                ∪ (Finset.Ico (lo + c) (lo + n)).filter (fun k => f k = v)).card := by
              rw [hio, Finset.filter_union]
          _ ≤ ((Finset.Ico lo (lo + c)).filter (fun k => f k = v)).card
                + ((Finset.Ico (lo + c) (lo + n)).filter (fun k => f k = v)).card :=
              Finset.card_union_le _ _
          _ ≤ ((Finset.Icc 1 c).filter (fun j => f j = v)).card
                + t * ((Finset.Icc 1 c).filter (fun j => f j = v)).card :=
              add_le_add (periodic_filter_block_card_le hc hper hlo le_rfl) htail
          _ = (t + 1) * ((Finset.Icc 1 c).filter (fun j => f j = v)).card := by ring

/-- **The class-4 cycle-density count** (the per-`(q, K₀)` FINITE cycle inequality): if the
orbit has period `c` from index 1 and the shell window is covered by `t` cycle blocks
(`K ≤ t·c`), then `|fibre₄| ≤ t·b₂` with `b₂` the per-cycle band-2 count. -/
theorem class4Fibre_card_le_cycle_count (ctx : ActualFailureContext) {c t : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hcover : (supportShell ctx.shell.d ctx.shell.X).card ≤ t * c) :
    (olcFibre ctx).card
      ≤ t * ((Finset.Icc 1 c).filter (fun j =>
          canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2)).card := by
  have hper' : ∀ m, 1 ≤ m →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c))
        = canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) :=
    fun m hm => by rw [hper m hm]
  have hsub : olcFibre ctx
      ⊆ (Finset.Ico (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card)).filter
          (fun k => canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Ico]
    have hwin := olcFibre_mem_window ctx hk
    exact ⟨hwin, olcFibre_canonGap_two ctx hk⟩
  calc (olcFibre ctx).card
      ≤ ((Finset.Ico (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card)).filter
          (fun k => canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2)).card :=
        Finset.card_le_card hsub
    _ ≤ t * ((Finset.Icc 1 c).filter (fun j =>
          canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2)).card :=
        periodic_filter_card_le hc hper' t
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
          ((supportShell ctx.shell.d ctx.shell.X).card)
          (n24_firstIndexAbove_pos ctx) hcover

/-- **The band-2-free cycle closure** (the class-4 mirror of
`class1Fibre_empty_of_cycle_band_free`): if one period of the orbit avoids band 2, the class-4
routed fibre is empty — the orbit side of the Return atom is a finite per-ctx check. -/
theorem class4Fibre_empty_of_cycle_band_free (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c → canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 2) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have hstart : k ∈ ctx.n24CarryData.starts := ((mem_class4Fibre_iff ctx k).mp hk).1
  have hk1 : 1 ≤ k := n24_starts_pos ctx hstart
  have hper' : ∀ m, 1 ≤ m →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c))
        = canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) :=
    fun m hm => by rw [hper m hm]
  have hres : canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k)
      = canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ ((k - 1) % c + 1)) :=
    periodic_eq_residue (f := fun m => canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)) hc hper' hk1
  have hband2 := ((mem_class4Fibre_iff ctx k).mp hk).2.2
  rw [hres] at hband2
  exact hband ((k - 1) % c + 1) (Nat.succ_le_succ (Nat.zero_le _))
    (Nat.mod_lt _ (by omega)) hband2

/-- A band-2-free cycle also yields the per-ctx capstone count (`|∅| = 0 ≤ r + 1`). -/
theorem class4Fibre_card_le_succ_r_of_cycle_band_free (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c → canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 2) :
    (olcFibre ctx).card ≤ ctx.n24CarryData.r + 1 := by
  rw [olcFibre_def, class4Fibre_empty_of_cycle_band_free ctx hc hper hband]
  simp

/-! ## Part 5.  Band-2 run rigidity: deviations from the fixed point quadruple

Under the band-2 step `K ↦ 4K − q` the deviation `3K − q` is multiplied by exactly `4`, so a
band-2 run either sits AT the fixed point `q = 3K` forever (the proved wave-2 obstruction
family) or escapes the band in `O(log₄ q)` steps.  This is the class-4 analogue of the class-2
band-4 run rigidity, and the structural reason `b₂` is small off the `3 ∣ q` family. -/

/-- **Band-2 run rigidity**: `s ≥ 1` consecutive band-2 orbit indices starting at `j` force
either the band-2 fixed point `3·K_j = q` or the length bound `2·4^{s−1} ≤ q`. -/
theorem band2_run_forces_three_mul_or_pow_le {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀)
    (hKq : K₀ < q) (j s : ℕ) (hs : 1 ≤ s)
    (hrun : ∀ t, t < s → canonGap q (slopeOrbit q K₀ (j + t)) = 2) :
    3 * slopeOrbit q K₀ j = q ∨ 2 * 4 ^ (s - 1) ≤ q := by
  have hband : ∀ t, t < s →
      2 * slopeOrbit q K₀ (j + t) ≤ q ∧ q < 4 * slopeOrbit q K₀ (j + t) :=
    fun t ht => (canonGap_eq_two_iff (slopeOrbit_mem hq hK1 hKq (j + t)).1).mp (hrun t ht)
  have hstep : ∀ t, t < s →
      slopeOrbit q K₀ (j + (t + 1)) = 4 * slopeOrbit q K₀ (j + t) - q := by
    intro t ht
    have h0 : slopeOrbit q K₀ (j + (t + 1))
        = boundedSlopeStep q (slopeOrbit q K₀ (j + t)) := rfl
    rw [h0]
    unfold boundedSlopeStep
    rw [hrun t ht]
    norm_num
  rcases Nat.lt_trichotomy (3 * slopeOrbit q K₀ j) q with hlt | heq | hgt
  · -- below the fixed point: `e = q − 3K_j ≥ 1` quadruples
    right
    have hclaim : ∀ t, t < s →
        3 * slopeOrbit q K₀ (j + t) + 4 ^ t * (q - 3 * slopeOrbit q K₀ j) = q := by
      intro t
      induction t with
      | zero =>
          intro _
          rw [pow_zero, one_mul, Nat.add_zero]
          omega
      | succ t ih =>
          intro ht
          have iht := ih (by omega)
          have hst := hstep t (by omega)
          have hbt := hband t (by omega)
          have hp : 4 ^ (t + 1) * (q - 3 * slopeOrbit q K₀ j)
              = 4 * (4 ^ t * (q - 3 * slopeOrbit q K₀ j)) := by ring
          rw [hst]
          omega
    have hcl := hclaim (s - 1) (by omega)
    have hb := hband (s - 1) (by omega)
    have hpe : 4 ^ (s - 1) ≤ 4 ^ (s - 1) * (q - 3 * slopeOrbit q K₀ j) := by
      calc 4 ^ (s - 1) = 4 ^ (s - 1) * 1 := (mul_one _).symm
        _ ≤ 4 ^ (s - 1) * (q - 3 * slopeOrbit q K₀ j) :=
            Nat.mul_le_mul_left _ (by omega)
    omega
  · exact Or.inl heq
  · -- above the fixed point: `e = 3K_j − q ≥ 1` quadruples
    right
    have hclaim : ∀ t, t < s →
        3 * slopeOrbit q K₀ (j + t) = q + 4 ^ t * (3 * slopeOrbit q K₀ j - q) := by
      intro t
      induction t with
      | zero =>
          intro _
          rw [pow_zero, one_mul, Nat.add_zero]
          omega
      | succ t ih =>
          intro ht
          have iht := ih (by omega)
          have hst := hstep t (by omega)
          have hbt := hband t (by omega)
          have hp : 4 ^ (t + 1) * (3 * slopeOrbit q K₀ j - q)
              = 4 * (4 ^ t * (3 * slopeOrbit q K₀ j - q)) := by ring
          rw [hst]
          omega
    have hcl := hclaim (s - 1) (by omega)
    have hb := hband (s - 1) (by omega)
    have hpe : 4 ^ (s - 1) ≤ 4 ^ (s - 1) * (3 * slopeOrbit q K₀ j - q) := by
      calc 4 ^ (s - 1) = 4 ^ (s - 1) * 1 := (mul_one _).symm
        _ ≤ 4 ^ (s - 1) * (3 * slopeOrbit q K₀ j - q) :=
            Nat.mul_le_mul_left _ (by omega)
    omega

/-- **Off the `3 ∣ q` family every band-2 run is short**: `2·4^{s−1} ≤ q`, i.e.
`s ≤ log₄(q/2) + 1`. -/
theorem band2_run_pow_le_of_three_not_dvd {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀)
    (hKq : K₀ < q) (h3 : ¬ 3 ∣ q) (j s : ℕ) (hs : 1 ≤ s)
    (hrun : ∀ t, t < s → canonGap q (slopeOrbit q K₀ (j + t)) = 2) :
    2 * 4 ^ (s - 1) ≤ q := by
  rcases band2_run_forces_three_mul_or_pow_le hq hK1 hKq j s hs hrun with h | h
  · exact absurd ⟨slopeOrbit q K₀ j, h.symm⟩ h3
  · exact h

/-! ## Part 6.  The combined `Class4FibreSmall` bridge -/

/-- **The wave-3 `Class4FibreSmall` bridge**: the capstone count field holds as soon as every
context satisfies ONE of the four proved per-shell closers — the wave-2 K.1 gap-ceiling gate,
the NEW two-window span gate, the NEW in-window span gate, or a band-2 cycle-count bound
`t·b₂ ≤ r + 1`. -/
theorem class4FibreSmall_of_gates
    (h : ∀ ctx : ActualFailureContext,
      64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64
      ∨ 64 * (ctx.n24CarryData.a
            (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          - ctx.n24CarryData.a
            (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X))
        < 2 * (129 * shellLadderDepth ctx + 64)
      ∨ 64 * (ctx.n24CarryData.a
            (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card - 1)
          - ctx.n24CarryData.a
            (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X))
        < 129 * shellLadderDepth ctx + 64
      ∨ ∃ c t : ℕ, 1 ≤ c
          ∧ (∀ m, 1 ≤ m →
              slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
                = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
          ∧ (supportShell ctx.shell.d ctx.shell.X).card ≤ t * c
          ∧ t * ((Finset.Icc 1 c).filter (fun j =>
              canonGap (class1SlopeDatum ctx).q
                (slopeOrbit (class1SlopeDatum ctx).q
                  (class1SlopeDatum ctx).K₀ j) = 2)).card
              ≤ ctx.n24CarryData.r + 1) :
    Class4FibreSmall := by
  intro ctx
  rcases h ctx with h1 | h2 | h3 | ⟨c, t, hc, hper, hcover, hle⟩
  · rw [olcFibre_def]
    exact class4Fibre_card_le_of_gapCeiling ctx h1
  · exact class4Fibre_card_le_succ_r_of_span_gate ctx h2
  · exact class4Fibre_card_le_succ_r_of_inWindow_span ctx h3
  · exact le_trans (class4Fibre_card_le_cycle_count ctx hc hper hcover) hle

/-! ## Part 7.  The `class4Interior` top-band finite check

The interior field is exactly top-band emptiness (`class4Interior_iff_topBand_empty`, wave 2);
the top band has `≤ r+1` positions, each demanding band 2 of the periodic orbit — a finite
per-ctx cycle check. -/

/-- **The top-band orbit check closes the interior field** (no gate): if the orbit avoids
band 2 at every top-band position `k ∈ [i+K−(r+1), i+K)`, the K.1 interior condition holds. -/
theorem class4Interior_of_topBand_band_free (ctx : ActualFailureContext)
    (hband : ∀ k,
      ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1) ≤ k →
      k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) ≠ 2) :
    ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card := by
  intro k hk
  by_contra hge
  have hwin := class4Fibre_mem_window ctx hk
  exact hband k (by omega) hwin.2 (class4Fibre_canonGap_eq ctx hk)

/-- **The per-ctx FINITE cycle check for the interior field**: with a period `c`, the top-band
readings reduce to the `≤ r+1` explicit cycle residues `(k−1) % c + 1 ∈ [1, c]` — if all of
them avoid band 2, `class4Interior` holds. -/
theorem class4Interior_of_cycle_topBand_check (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ k,
      ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1) ≤ k →
      k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ ((k - 1) % c + 1))
        ≠ 2) :
    ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card := by
  apply class4Interior_of_topBand_band_free ctx
  intro k hk1 hk2
  have hi1 : 1 ≤ ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X :=
    n24_firstIndexAbove_pos ctx
  have hKr : ctx.n24CarryData.r + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
    cnlMulti_r_add_one_le_width ctx
  have hk0 : 1 ≤ k := by omega
  have hper' : ∀ m, 1 ≤ m →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c))
        = canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) :=
    fun m hm => by rw [hper m hm]
  have hres : canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k)
      = canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ ((k - 1) % c + 1)) :=
    periodic_eq_residue (f := fun m => canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)) hc hper' hk0
  rw [hres]
  exact hband k hk1 hk2

/-- A band-2-free cycle closes the interior field outright (through fibre emptiness). -/
theorem class4Interior_of_cycle_band_free (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c → canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 2) :
    ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card := by
  intro k hk
  rw [class4Fibre_empty_of_cycle_band_free ctx hc hper hband] at hk
  exact absurd hk (Finset.notMem_empty k)

/-! ## Part 8.  The digit fields: the genuine M.2.1 attempt and the proved reductions

The self-referential congruence at the pinned positions yields SPACING (`2^{v₂} ∣ z − x`,
`returnSelfRefKey_gapDiv`), and the window pins confine same-slice pairs to `z − x < K`.
Below: the valuation-vacuity closure of `hzero`, the maxima reduction of `hcleanStep`, the
consecutive-pair reduction of `hzero`, and the adjacency bridge `hcleanStep ⇒ hzero`. -/

/-- Same-key class-4 pairs are confined to the shell window: `z − x < K`. -/
theorem olcFibre_pair_dist_lt_width (ctx : ActualFailureContext) {x z : ℕ}
    (hx : x ∈ olcFibre ctx) (hz : z ∈ olcFibre ctx) :
    z - x < (supportShell ctx.shell.d ctx.shell.X).card := by
  have hxw := olcFibre_mem_window ctx hx
  have hzw := olcFibre_mem_window ctx hz
  omega

/-- **The spacing/width clash**: a same-key class-4 pair `x < z` is IMPOSSIBLE whenever the
M.2.1 spacing divisor `2^{carryVal2 x}` reaches the window width `K` — the congruence
`2^{v₂} ∣ z − x` (`returnSelfRefKey_gapDiv`) cannot fit inside `z − x < K`. -/
theorem returnSelfRef_pair_false_of_carryVal2_large (ctx : ActualFailureContext) {x z : ℕ}
    (hx : x ∈ olcFibre ctx) (hz : z ∈ olcFibre ctx)
    (hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z) (hlt : x < z)
    (hval : (supportShell ctx.shell.d ctx.shell.X).card ≤ 2 ^ carryVal2 ctx x) :
    False := by
  have hdvd := returnSelfRefKey_gapDiv ctx hkey hlt
  have hdist := olcFibre_pair_dist_lt_width ctx hx hz
  have hpos : 0 < z - x := by omega
  have hle := Nat.le_of_dvd hpos hdvd
  omega

/-- **`hzero` is a THEOREM under large carry valuations**: if every fibre member has
`K ≤ 2^{carryVal2 k}`, the self-referential slices are singletons (no same-key pair exists),
so the (Z) all-pairs zero-run field holds vacuously — by spacing arithmetic, not fabricated
emptiness. -/
theorem returnDigit_hzero_of_carryVal2_large (ctx : ActualFailureContext)
    (hval : ∀ k ∈ olcFibre ctx,
      (supportShell ctx.shell.d ctx.shell.X).card ≤ 2 ^ carryVal2 ctx k) :
    ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
      ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y,
        ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
          x < z → ∀ j, x < j → j ≤ z → ctx.d j = 0 := by
  intro y hy x hx z hz hxz
  rw [olcSlice_def, Finset.mem_filter] at hx hz
  exact absurd hxz (fun hlt =>
    returnSelfRef_pair_false_of_carryVal2_large ctx hx.1 hz.1
      (hx.2.trans hz.2.symm) hlt (hval x hx.1))

/-- **The consecutive-pair reduction of `hzero`** (chaining the imported
`zeroRun_allPairs_of_consecutive`): the (Z) field needs only the zero-runs between CONSECUTIVE
same-slice starts. -/
theorem returnDigit_hzero_of_consecutive (ctx : ActualFailureContext) (key : ℕ → ℕ)
    (hcons : ∀ y ∈ (olcFibre ctx).image key,
      ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
        (∀ w ∈ olcSlice ctx key y, x < w → z ≤ w) →
        ∀ j, x < j → j ≤ z → ctx.d j = 0) :
    ∀ y ∈ (olcFibre ctx).image key,
      ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
        ∀ j, x < j → j ≤ z → ctx.d j = 0 :=
  fun y hy => zeroRun_allPairs_of_consecutive (hcons y hy)

/-- **The maxima reduction of `hcleanStep`**: given the (Z) zero-runs, the clean step
`d(k+1) = 0` is FORCED at every non-maximal slice member (the zero-run to the next member
covers position `k+1`), so the genuine clean-step content shrinks to the per-slice MAXIMA. -/
theorem returnDigit_cleanStep_of_hzero_max (ctx : ActualFailureContext) (key : ℕ → ℕ)
    (hzero : ∀ y ∈ (olcFibre ctx).image key,
      ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
        ∀ j, x < j → j ≤ z → ctx.d j = 0)
    (hmax : ∀ k ∈ olcFibre ctx,
      (∀ z ∈ olcFibre ctx, key z = key k → z ≤ k) → ctx.d (k + 1) = 0) :
    ∀ k ∈ olcFibre ctx, ctx.d (k + 1) = 0 := by
  intro k hk
  by_cases hex : ∃ z ∈ olcFibre ctx, key z = key k ∧ k < z
  · obtain ⟨z, hzF, hkey, hkz⟩ := hex
    have hy : key k ∈ (olcFibre ctx).image key := Finset.mem_image_of_mem key hk
    have hks : k ∈ olcSlice ctx key (key k) := by
      rw [olcSlice_def, Finset.mem_filter]
      exact ⟨hk, rfl⟩
    have hzs : z ∈ olcSlice ctx key (key k) := by
      rw [olcSlice_def, Finset.mem_filter]
      exact ⟨hzF, hkey⟩
    exact hzero (key k) hy k hks z hzs hkz (k + 1) (Nat.lt_succ_self k) (by omega)
  · push Not at hex
    exact hmax k hk hex

/-- **The adjacency bridge `hcleanStep ⇒ hzero`** (the honest partial converse from the gapDiv
structure): if every consecutive same-slice pair is ADJACENT (`z = x + 1` — by the spacing
congruence this is the `carryVal2 = 0` regime), the whole (Z) field follows from the clean
step alone. -/
theorem returnDigit_hzero_of_adjacent_consecutive (ctx : ActualFailureContext) (key : ℕ → ℕ)
    (hadj : ∀ y ∈ (olcFibre ctx).image key,
      ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
        (∀ w ∈ olcSlice ctx key y, x < w → z ≤ w) → z = x + 1)
    (hclean : ∀ k ∈ olcFibre ctx, ctx.d (k + 1) = 0) :
    ∀ y ∈ (olcFibre ctx).image key,
      ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
        ∀ j, x < j → j ≤ z → ctx.d j = 0 := by
  apply returnDigit_hzero_of_consecutive ctx key
  intro y hy x hx z hz hxz hcons j hj1 hj2
  have hz1 : z = x + 1 := hadj y hy x hx z hz hxz hcons
  have hjx : j = x + 1 := by omega
  have hxF : x ∈ olcFibre ctx := by
    rw [olcSlice_def, Finset.mem_filter] at hx
    exact hx.1
  rw [hjx]
  exact hclean x hxF

/-- **Digit residual from the maxima reduction**: `hzero` at the self-referential key plus the
clean step at slice MAXIMA only (strictly fewer positions than the full `hcleanStep`) plus the
interior field. -/
def ReturnClass4DigitResidual.ofSelfRefMaxCleanStep (ctx : ActualFailureContext)
    (hzero : ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
      ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y,
        ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
          x < z → ∀ j, x < j → j ≤ z → ctx.d j = 0)
    (hmax : ∀ k ∈ olcFibre ctx,
      (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
      ctx.d (k + 1) = 0)
    (hint : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) :
    ReturnClass4DigitResidual ctx where
  hzero := hzero
  hcleanStep := returnDigit_cleanStep_of_hzero_max ctx (returnSelfRefKey ctx) hzero hmax
  class4Interior := hint

/-- **Digit residual under large carry valuations**: with `K ≤ 2^{carryVal2}` on the fibre the
(Z) field is vacuous (singleton slices), so only the clean step and the interior remain. -/
def ReturnClass4DigitResidual.ofCarryVal2Large (ctx : ActualFailureContext)
    (hval : ∀ k ∈ olcFibre ctx,
      (supportShell ctx.shell.d ctx.shell.X).card ≤ 2 ^ carryVal2 ctx k)
    (hclean : ∀ k ∈ olcFibre ctx, ctx.d (k + 1) = 0)
    (hint : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) :
    ReturnClass4DigitResidual ctx where
  hzero := returnDigit_hzero_of_carryVal2_large ctx hval
  hcleanStep := hclean
  class4Interior := hint

/-- **The whole digit residual from a band-2-free cycle** — consumed through the PROVED
emptiness theorem `class4Fibre_empty_of_cycle_band_free` (per-ctx finite check; never a
fabricated witness). -/
def returnDigitOfCycleBandFree (ctx : ActualFailureContext) {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c → canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 2) :
    ReturnClass4DigitResidual ctx :=
  ReturnClass4DigitResidual.ofEmptyFibre ctx (by
    rw [olcFibre_def]
    exact class4Fibre_empty_of_cycle_band_free ctx hc hper hband)

/-! ## Part 9.  Honest machine-readable status -/

/-- The precise status of the Return/Class-4 atom after the wave-3 cycle-closure pass. -/
def returnClass4CycleClosureStatus : List String :=
  [ "CLOSED UNCONDITIONALLY (sliding-window rigidity engine, NEW) — " ++
      "slidingWindow_card_mul_le_span: |S|·F ≤ (r+1)·(a(hi+r) − a(lo)) for floor-satisfying " ++
      "starts (disjoint-window telescoping, fuel induction on the minimum); " ++
      "slidingWindow_card_le_succ_of_span: span < 2F forces |S| ≤ r+1 (two disjoint windows " ++
      "cannot fit).  Generic over monotone position functions.",
    "CLOSED UNCONDITIONALLY (class-4 population bounds, NEW) — class4Fibre_hitPosition_floor: " ++
      "129L+64 ≤ 64·(a(k+r+1) − a(k)) at every class-4 start; " ++
      "class4Fibre_card_mul_floor_le_span: |fibre₄|·(129L+64) ≤ (r+1)·64·(a(i+K+r) − a(i)); " ++
      "class4Fibre_interior_card_mul_floor_le(_X): the interior sub-fibre obeys " ++
      "|fibre₄^int|·(129L+64) ≤ (r+1)·64·X (in-window positions live in (X, 2X]) — the wave-2 " ++
      "audit claim ((r+1)·64X/(129L) interior ceiling) is now a THEOREM; " ++
      "class4Fibre_card_mul_floor_le_global: |fibre₄|·(129L+64) ≤ (r+1)·(129L+64) + (r+1)·64·X.",
    "NEW PER-SHELL CLOSURES of the capstone count |olcFibre| ≤ r+1 — " ++
      "class4Fibre_card_le_succ_r_of_span_gate: under 64·(a(i+K+r) − a(i)) < 2·(129L+64); " ++
      "class4Fibre_topBand_of_inWindow_span / class4Fibre_card_le_succ_r_of_inWindow_span: " ++
      "under 64·(a(i+K−1) − a(i)) < 129L+64 (interior windows cannot reach the floor).  Both " ++
      "are position-realized gates, INCOMPARABLE with the wave-2 worst-case K.1 gate " ++
      "64(r+1)(L+B+1) < 129L+64.",
    "CLOSED UNCONDITIONALLY (band-2 cycle density, NEW) — periodic_add_mul / " ++
      "periodic_eq_residue / periodic_filter_block_card_le / periodic_filter_card_le: a " ++
      "c-periodic orbit reading hits a value ≤ t·(per-cycle count) on any t·c-covered window; " ++
      "class4Fibre_card_le_cycle_count: |fibre₄| ≤ t·b₂(c) whenever K ≤ t·c — the per-(q,K₀) " ++
      "FINITE cycle inequality for the Return count; class4Fibre_empty_of_cycle_band_free / " ++
      "class4Fibre_card_le_succ_r_of_cycle_band_free: a band-2-free period closes the fibre " ++
      "outright (mirror of the class-1 cycle closer).",
    "CLOSED UNCONDITIONALLY (band-2 run rigidity, NEW) — " ++
      "band2_run_forces_three_mul_or_pow_le: s consecutive band-2 orbit indices force " ++
      "3·K_j = q (the fixed point) or 2·4^{s−1} ≤ q — deviations from q/3 QUADRUPLE under " ++
      "K ↦ 4K − q; band2_run_pow_le_of_three_not_dvd: off 3 ∣ q every band-2 run has " ++
      "s ≤ log₄(q/2) + 1, so b₂ is structurally small there.  At q = 3K (the proved wave-2 " ++
      "fixed-point obstruction) the cycle bound is vacuous (b₂ = c) and only the " ++
      "sliding-window engine bites: the gap floor IS realizable at many starts " ++
      "simultaneously in the model — the density theorem (r+1)·64X/(129L+64) is the honest " ++
      "quantitative answer, exponentially beyond r+1 on deep shells.",
    "BRIDGED (the count field) — class4FibreSmall_of_gates: Class4FibreSmall holds as soon as " ++
      "every ctx satisfies ONE of {K.1 gate, two-window span gate, in-window span gate, " ++
      "cycle-count bound t·b₂ ≤ r+1}.  NOT claimed unconditionally: on deep shells with " ++
      "q = 3K-type cycles and wide realized spans all four gates can fail simultaneously — " ++
      "the count stays genuine M.2/Prop. 23.1 analytic content.",
    "CLOSED (the interior top-band finite check, NEW) — class4Interior_of_topBand_band_free: " ++
      "the K.1 interior field holds whenever the orbit avoids band 2 at the ≤ r+1 top-band " ++
      "positions (no gate); class4Interior_of_cycle_topBand_check: with a period c the check " ++
      "reduces to ≤ r+1 explicit cycle residues (k−1) % c + 1 ∈ [1,c] — a FINITE per-ctx " ++
      "check; class4Interior_of_cycle_band_free: band-2-free cycles close interior through " ++
      "emptiness.  Honest limit: at the q = 3K fixed point every residue is band 2 " ++
      "(canonGap_orbit_three_mul, wave 2), so the top-band check cannot fire there.",
    "CLOSED (digit field hzero, valuation regime, NEW) — " ++
      "returnSelfRef_pair_false_of_carryVal2_large: a same-key class-4 pair x < z is " ++
      "IMPOSSIBLE when K ≤ 2^{carryVal2 x} (the M.2.1 spacing 2^{v₂} ∣ z − x cannot fit in " ++
      "z − x < K — olcFibre_pair_dist_lt_width); returnDigit_hzero_of_carryVal2_large: hzero " ++
      "holds VACUOUSLY there (singleton slices, spacing arithmetic, not fabricated " ++
      "emptiness); ReturnClass4DigitResidual.ofCarryVal2Large: the digit residual collapses " ++
      "to hcleanStep + interior in that regime.",
    "REDUCED (digit fields, NEW) — returnDigit_cleanStep_of_hzero_max + " ++
      "ReturnClass4DigitResidual.ofSelfRefMaxCleanStep: given hzero, the clean step is FORCED " ++
      "at every non-maximal slice member (the zero-run to the next member covers k+1), so " ++
      "hcleanStep shrinks to the ≤ #slices per-slice MAXIMA; " ++
      "returnDigit_hzero_of_consecutive (chaining the imported " ++
      "zeroRun_allPairs_of_consecutive): hzero shrinks to consecutive same-slice pairs; " ++
      "returnDigit_hzero_of_adjacent_consecutive: under per-slice adjacency (the " ++
      "carryVal2 = 0 regime of the gapDiv congruence) hzero follows from hcleanStep alone; " ++
      "returnDigitOfCycleBandFree: the whole digit residual from a band-2-free cycle " ++
      "(through the PROVED emptiness theorem).",
    "AUDIT (the genuine digit attempt, honest outcome) — the M.2.1 self-referential " ++
      "congruence technique (returnSelfRefKey_gapDiv) produces key-equality consequences, " ++
      "i.e. SPACING, never digit VALUES; the ReturnInputUnconditional shellLevels chain " ++
      "builds abstract DirtyCrossing data anchored at coordinate 0, not constraints on " ++
      "ctx.d at the fibre positions k+1; the class-4 pins (gap floor at indices ≥ k, band-2 " ++
      "orbit at k) never touch the digit position k+1, and the proved forcing direction " ++
      "anchoredSeed_forces_clean_step shows every inhabitant genuinely carries that digit " ++
      "content.  HONEST RESIDUAL after this pass (per ctx, beyond the proved gates): the " ++
      "clean step at the ≤ #slices slice maxima + the zero-runs at non-adjacent consecutive " ++
      "same-slice pairs in the carryVal2 < log₂ K regime + the top-band band-2 exclusions " ++
      "where the cycle check fails (q = 3K family).  No unconditional closure of " ++
      "Class4FibreSmall or ReturnClass4DigitResidual is claimed." ]

theorem returnClass4CycleClosureStatus_nonempty : returnClass4CycleClosureStatus ≠ [] := by
  simp [returnClass4CycleClosureStatus]

/-! ## Part 10.  Axiom-cleanliness audit -/

#print axioms slidingWindow_card_mul_le_span_fuel
#print axioms slidingWindow_card_mul_le_span
#print axioms slidingWindow_card_le_succ_of_span
#print axioms olcFibre_mem_window
#print axioms class4Fibre_hitPosition_floor
#print axioms olcFibre_canonGap_two
#print axioms class4Fibre_card_mul_floor_le_span
#print axioms class4Fibre_card_le_succ_r_of_span_gate
#print axioms class4Fibre_interior_card_mul_floor_le
#print axioms class4Fibre_interior_card_mul_floor_le_X
#print axioms class4Fibre_card_mul_floor_le_global
#print axioms class4Fibre_topBand_of_inWindow_span
#print axioms class4Fibre_card_le_succ_r_of_inWindow_span
#print axioms periodic_add_mul
#print axioms periodic_eq_residue
#print axioms periodic_filter_block_card_le
#print axioms periodic_filter_card_le
#print axioms class4Fibre_card_le_cycle_count
#print axioms class4Fibre_empty_of_cycle_band_free
#print axioms class4Fibre_card_le_succ_r_of_cycle_band_free
#print axioms band2_run_forces_three_mul_or_pow_le
#print axioms band2_run_pow_le_of_three_not_dvd
#print axioms class4FibreSmall_of_gates
#print axioms class4Interior_of_topBand_band_free
#print axioms class4Interior_of_cycle_topBand_check
#print axioms class4Interior_of_cycle_band_free
#print axioms olcFibre_pair_dist_lt_width
#print axioms returnSelfRef_pair_false_of_carryVal2_large
#print axioms returnDigit_hzero_of_carryVal2_large
#print axioms returnDigit_hzero_of_consecutive
#print axioms returnDigit_cleanStep_of_hzero_max
#print axioms returnDigit_hzero_of_adjacent_consecutive
#print axioms ReturnClass4DigitResidual.ofSelfRefMaxCleanStep
#print axioms ReturnClass4DigitResidual.ofCarryVal2Large
#print axioms returnDigitOfCycleBandFree
#print axioms returnClass4CycleClosureStatus_nonempty

end

end Erdos260
