import Erdos260.Erdos260ValuationCapstone

/-!
# The Q-odd reset closure - the digit-side core after wave 10

This module (NEW; it edits no existing file) attacks the remaining Q-odd digit core
with the wave-10 reset law `carryVal2_eq_zero_iff_of_Q_odd` (`CarryValuationFloor`):
at a Q-odd context the carry valuation is `0` exactly at odd raw positions that are
hits (`carryVal2 N = 0 iff N odd and d N = 1`, for `N >= 1`).

## 1.  The off-by-one verdict (goal 1) - the demand INCLUDES the right endpoint

The verbatim `ReturnZeroBody` (`ReturnSpanGateClosure`) demands `d j = 0` for all
`x < j <= z` on same-slice pairs `x < z` - the interval is `(x, z]`, so `j = z` IS
demanded (`returnZeroBody_demands_right_endpoint`).  At `carryVal2 = 0` the
self-referential key collapses: `returnSelfRefKey k = Nat.pair 0 (k % 2^0) =
Nat.pair 0 0` (`returnSelfRefKey_eq_pairZero_iff_val0`), so ALL val-0 fibre members
are pairwise same-slice.  But the reset law says a val-0 member z (at Q odd) has
`d z = 1` - the demand `d z = 0` is REFUTED OUTRIGHT
(`returnZeroBody_refuted_of_val0_pair`).  Hence `ReturnZeroBody` forces AT MOST ONE
val-0 member in the whole fibre (`returnZeroBody_val0_unique_of_Q_odd`,
`returnZeroBody_val0_card_le_one_of_Q_odd`).

## 2.  The val-0 member structure and counts (goal 2)

A val-0 fibre member at Q odd is an odd raw position that is a hit
(`olcFibre_val0_odd_hit_of_Q_odd`), hence a support element `<= 2X`
(`olcFibre_val0_mem_supportIn_of_Q_odd`) inside the index window `[F, F+W)`
(`olcFibre_val0_subset_window_hits_of_Q_odd`); the val-0 count is bounded by the
window hit count (`olcFibre_val0_card_le_window_hits_of_Q_odd`) and by
`supportCount d (2X)` (`olcFibre_val0_card_le_supportCount_of_Q_odd`).  Combined
with step 1: under `ReturnZeroBody` the fibre is the val-positive part plus at most
one element (`returnZeroBody_fibre_card_le_of_Q_odd`).

## 3.  The exact Q-odd decomposition of `returnZero` (the sharp restatement)

`ReturnZeroBody <-> (at most one val-0 member) AND (the zero-run demand on
val-POSITIVE slice pairs)` at Q-odd contexts (`returnZeroBody_iff_qOddSplit`); the
same split is in fact an UNCONDITIONAL restatement (`returnZeroBody_iff_qOddSplit_uncond`:
at Q even the first clause is vacuous by `carryVal2_pos_of_Q_even`).  Trajectory
form: `belowBandTrajectory_iff_qOddSplit`.  Slices are parity-pure at Q odd
(`sameKey_parity_eq_of_Q_odd`): val-0 members are all odd (reset law); val-positive
same-key members agree mod `2^v`, `v >= 1`, hence mod 2.

## 4.  `returnMaxClean` at Q odd (goal 3) - the parity split

Via the parity dictionary `carryOf_emod_two`, at Q odd and `k+1` ODD the demanded
clean step `d(k+1) = 0` is EQUIVALENT to the carry being even at `k+1`
(`digit_succ_zero_iff_carry_even_of_Q_odd`) - a pure carry-parity fact.  At `k+1`
EVEN the digit is invisible mod 2 (the dictionary forces `carryOf (k+1) % 2 = 0`
REGARDLESS of the digit and of Q-parity: `carryOf_emod_two_eq_zero_at_even_succ`),
and the demand stays the unchanged doubling form.  Exact split:
`returnMaxCleanBody_iff_qOddSplit` / `maxCleanCarryTrajectory_iff_qOddSplit`
(`QOddMaxCleanSplit`).  HONEST: even maxima are NOT excluded by the slice structure;
they sit in val-positive parity-pure slices and keep the doubling demand.

## 5.  Capstone bridges (goal 4, additive only)

Successor field shapes per parity regime (`ReturnZeroQOddSplitField`,
`ReturnZeroQEvenFloorField`, `ReturnMaxCleanQOddSplitField`,
`ReturnMaxCleanQEvenField`), the rebuilds
(`returnZeroTrajectoryFloor_of_qOddSplit`, `returnMaxCleanTrajectory_of_qOddSplit`),
the combinator `valuationResidual_withQOddSplit` on the wave-10 surface
`Erdos260ValuationResidual`, and the endpoint `erdos260_of_qOddSplit`.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The off-by-one verdict and the val-0 slice collapse -/

/-- **The demand interval is `(x, z]` - the right endpoint IS demanded**: under
`ReturnZeroBody`, every same-slice pair `x < z` demands `d z = 0` (instantiate
`j := z` in `x < j -> j <= z -> d j = 0`).  This is the formal off-by-one verdict. -/
theorem returnZeroBody_demands_right_endpoint (ctx : ActualFailureContext) {y x z : ℕ}
    (hy : y ∈ (olcFibre ctx).image (returnSelfRefKey ctx))
    (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y)
    (hz : z ∈ olcSlice ctx (returnSelfRefKey ctx) y)
    (hxz : x < z) (H : ReturnZeroBody ctx) : ctx.d z = 0 :=
  H y hy x hx z hz hxz z hxz le_rfl

/-- **The val-0 key collapse**: the self-referential key equals `Nat.pair 0 0` exactly
at carry-valuation-0 positions (`k % 2^0 = k % 1 = 0`), so ALL val-0 positions share
ONE slice. -/
theorem returnSelfRefKey_eq_pairZero_iff_val0 (ctx : ActualFailureContext) (k : ℕ) :
    returnSelfRefKey ctx k = Nat.pair 0 0 ↔ carryVal2 ctx k = 0 := by
  constructor
  · intro h
    have hpair : Nat.pair (carryVal2 ctx k) (k % 2 ^ carryVal2 ctx k)
        = Nat.pair 0 0 := h
    exact (Nat.pair_eq_pair.mp hpair).1
  · intro h0
    show Nat.pair (carryVal2 ctx k) (k % 2 ^ carryVal2 ctx k) = Nat.pair 0 0
    rw [h0, pow_zero, Nat.mod_one]

/-- Equal keys force equal carry valuations (first component of `Nat.pair`). -/
theorem carryVal2_eq_of_returnSelfRefKey_eq (ctx : ActualFailureContext) {x z : ℕ}
    (h : returnSelfRefKey ctx x = returnSelfRefKey ctx z) :
    carryVal2 ctx x = carryVal2 ctx z := by
  have hpair : Nat.pair (carryVal2 ctx x) (x % 2 ^ carryVal2 ctx x)
      = Nat.pair (carryVal2 ctx z) (z % 2 ^ carryVal2 ctx z) := h
  exact (Nat.pair_eq_pair.mp hpair).1

/-- Every fibre member is `>= 1` (indeed `>= L >= 28`); the form consumed by the
reset law. -/
theorem olcFibre_mem_one_le (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ olcFibre ctx) : 1 ≤ k :=
  olcFibre_mem_ge_of_le_depth ctx
    (le_trans (by norm_num) (shellLadderDepth_ge ctx)) hk

/-- **The outright refutation (the contradiction check, settled)**: at a Q-odd context,
TWO distinct val-0 fibre members refute `ReturnZeroBody`.  They are same-slice (key
collapse), the demand includes the right endpoint `z`, and the reset law says
`d z = 1`. -/
theorem returnZeroBody_refuted_of_val0_pair (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {x z : ℕ} (hx : x ∈ olcFibre ctx) (hz : z ∈ olcFibre ctx)
    (hxz : x < z) (h0x : carryVal2 ctx x = 0) (h0z : carryVal2 ctx z = 0) :
    ¬ ReturnZeroBody ctx := by
  intro H
  have hkx : returnSelfRefKey ctx x = Nat.pair 0 0 :=
    (returnSelfRefKey_eq_pairZero_iff_val0 ctx x).mpr h0x
  have hkz : returnSelfRefKey ctx z = Nat.pair 0 0 :=
    (returnSelfRefKey_eq_pairZero_iff_val0 ctx z).mpr h0z
  have hy : returnSelfRefKey ctx x ∈ (olcFibre ctx).image (returnSelfRefKey ctx) :=
    Finset.mem_image_of_mem _ hx
  have hxs : x ∈ olcSlice ctx (returnSelfRefKey ctx) (returnSelfRefKey ctx x) := by
    rw [olcSlice_def]
    exact Finset.mem_filter.mpr ⟨hx, rfl⟩
  have hzs : z ∈ olcSlice ctx (returnSelfRefKey ctx) (returnSelfRefKey ctx x) := by
    rw [olcSlice_def]
    exact Finset.mem_filter.mpr ⟨hz, by rw [hkz, hkx]⟩
  have hdz : ctx.d z = 0 :=
    returnZeroBody_demands_right_endpoint ctx hy hxs hzs hxz H
  have hz1 : 1 ≤ z := olcFibre_mem_one_le ctx hz
  have hreset := (carryVal2_eq_zero_iff_of_Q_odd ctx hQodd hz1).mp h0z
  omega

/-- **`returnZero` forces at most one val-0 member (Q odd)**: under `ReturnZeroBody`,
any two val-0 fibre members coincide. -/
theorem returnZeroBody_val0_unique_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (H : ReturnZeroBody ctx) :
    ∀ x ∈ olcFibre ctx, ∀ z ∈ olcFibre ctx,
      carryVal2 ctx x = 0 → carryVal2 ctx z = 0 → x = z := by
  intro x hx z hz h0x h0z
  rcases Nat.lt_trichotomy x z with hlt | heq | hgt
  · exact absurd H (returnZeroBody_refuted_of_val0_pair ctx hQodd hx hz hlt h0x h0z)
  · exact heq
  · exact (absurd H
      (returnZeroBody_refuted_of_val0_pair ctx hQodd hz hx hgt h0z h0x))

/-- The count form: under `ReturnZeroBody` at Q odd, the val-0 part of the fibre has
at most one element. -/
theorem returnZeroBody_val0_card_le_one_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (H : ReturnZeroBody ctx) :
    ((olcFibre ctx).filter (fun k => carryVal2 ctx k = 0)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  exact returnZeroBody_val0_unique_of_Q_odd ctx hQodd H a ha.1 b hb.1 ha.2 hb.2

/-- The contrapositive closure trigger: two or more val-0 members refute the field
body outright. -/
theorem returnZeroBody_refuted_of_two_val0_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1)
    (h2 : 1 < ((olcFibre ctx).filter (fun k => carryVal2 ctx k = 0)).card) :
    ¬ ReturnZeroBody ctx := by
  intro H
  have := returnZeroBody_val0_card_le_one_of_Q_odd ctx hQodd H
  omega

/-! ## Part 2.  The val-0 member structure and counts (Q odd) -/

/-- **A val-0 fibre member is an odd raw hit position** - the reset law evaluated at
the member's raw position (`k >= L >= 28 >= 1`). -/
theorem olcFibre_val0_odd_hit_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {k : ℕ} (hk : k ∈ olcFibre ctx)
    (h0 : carryVal2 ctx k = 0) : k % 2 = 1 ∧ ctx.d k = 1 :=
  (carryVal2_eq_zero_iff_of_Q_odd ctx hQodd (olcFibre_mem_one_le ctx hk)).mp h0

/-- A val-0 fibre member is a support element below `2X` (`1 <= k <= 2X`, `d k = 1`). -/
theorem olcFibre_val0_mem_supportIn_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {k : ℕ} (hk : k ∈ olcFibre ctx)
    (h0 : carryVal2 ctx k = 0) :
    k ∈ supportIn ctx.d (2 * ctx.shell.X) := by
  rw [mem_supportIn]
  exact ⟨olcFibre_mem_one_le ctx hk, returnFibre_le_two_mul ctx hk,
    (olcFibre_val0_odd_hit_of_Q_odd ctx hQodd hk h0).2⟩

/-- **The val-0 members inject into the odd hits of the index window `[F, F+W)`** -
sparse support makes them rare. -/
theorem olcFibre_val0_subset_window_hits_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) :
    (olcFibre ctx).filter (fun k => carryVal2 ctx k = 0) ⊆
      (Finset.Ico (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card)).filter
        (fun n => n % 2 = 1 ∧ ctx.d n = 1) := by
  intro k hk
  rw [Finset.mem_filter] at hk
  obtain ⟨hkf, hk0⟩ := hk
  have hwin := olcFibre_mem_window ctx hkf
  rw [Finset.mem_filter, Finset.mem_Ico]
  exact ⟨⟨hwin.1, hwin.2⟩, olcFibre_val0_odd_hit_of_Q_odd ctx hQodd hkf hk0⟩

/-- The window-hit count bound: `#val-0 members <= #{odd hits in [F, F+W)}`. -/
theorem olcFibre_val0_card_le_window_hits_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) :
    ((olcFibre ctx).filter (fun k => carryVal2 ctx k = 0)).card ≤
      ((Finset.Ico (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card)).filter
        (fun n => n % 2 = 1 ∧ ctx.d n = 1)).card :=
  Finset.card_le_card (olcFibre_val0_subset_window_hits_of_Q_odd ctx hQodd)

/-- The global support-count bound: `#val-0 members <= supportCount d (2X)`. -/
theorem olcFibre_val0_card_le_supportCount_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) :
    ((olcFibre ctx).filter (fun k => carryVal2 ctx k = 0)).card ≤
      supportCount ctx.d (2 * ctx.shell.X) := by
  have hsub : (olcFibre ctx).filter (fun k => carryVal2 ctx k = 0) ⊆
      supportIn ctx.d (2 * ctx.shell.X) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    exact olcFibre_val0_mem_supportIn_of_Q_odd ctx hQodd hk.1 hk.2
  simpa [supportCount] using Finset.card_le_card hsub

/-- **The fibre count split under `returnZero` (Q odd)**: the fibre is its val-positive
part plus at most one element. -/
theorem returnZeroBody_fibre_card_le_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (H : ReturnZeroBody ctx) :
    (olcFibre ctx).card ≤
      ((olcFibre ctx).filter (fun k => 1 ≤ carryVal2 ctx k)).card + 1 := by
  have hsub : olcFibre ctx ⊆
      (olcFibre ctx).filter (fun k => carryVal2 ctx k = 0) ∪
        (olcFibre ctx).filter (fun k => 1 ≤ carryVal2 ctx k) := by
    intro k hk
    rcases Nat.eq_zero_or_pos (carryVal2 ctx k) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, h⟩)
  have h1 := returnZeroBody_val0_card_le_one_of_Q_odd ctx hQodd H
  have h2 := Finset.card_le_card hsub
  have h3 := Finset.card_union_le
    ((olcFibre ctx).filter (fun k => carryVal2 ctx k = 0))
    ((olcFibre ctx).filter (fun k => 1 ≤ carryVal2 ctx k))
  omega

/-! ## Part 3.  The exact Q-odd decomposition of `returnZero` -/

/-- The first split clause: at most one val-0 fibre member. -/
def QOddVal0AtMostOne (ctx : ActualFailureContext) : Prop :=
  ∀ x ∈ olcFibre ctx, ∀ z ∈ olcFibre ctx,
    carryVal2 ctx x = 0 → carryVal2 ctx z = 0 → x = z

/-- The second split clause: the verbatim zero-run demand restricted to slice pairs
whose carry valuation is POSITIVE (where the slice spacing `2^v | z - x` has content). -/
def QOddValPosZeroRun (ctx : ActualFailureContext) : Prop :=
  ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
    ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y,
      ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
        x < z → 1 ≤ carryVal2 ctx x → ∀ j, x < j → j ≤ z → ctx.d j = 0

/-- **The Q-odd split form of the `returnZero` demand**: at most one val-0 member,
plus the zero-run demand on val-positive slice pairs. -/
def QOddReturnZeroSplit (ctx : ActualFailureContext) : Prop :=
  QOddVal0AtMostOne ctx ∧ QOddValPosZeroRun ctx

/-- **The exact Q-odd decomposition**: `ReturnZeroBody` IS the split form.  Forward:
the at-most-one clause is the reset-law refutation; the val-positive clause is a
weakening.  Backward: a same-slice pair with val-0 left endpoint forces an equal pair
(at-most-one), contradiction with `x < z`; otherwise the val-positive clause fires. -/
theorem returnZeroBody_iff_qOddSplit (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) :
    ReturnZeroBody ctx ↔ QOddReturnZeroSplit ctx := by
  constructor
  · intro H
    refine ⟨returnZeroBody_val0_unique_of_Q_odd ctx hQodd H, ?_⟩
    intro y hy x hx z hz hxz _ j hjx hjz
    exact H y hy x hx z hz hxz j hjx hjz
  · rintro ⟨h1, h2⟩
    intro y hy x hx z hz hxz j hjx hjz
    rcases Nat.eq_zero_or_pos (carryVal2 ctx x) with h0 | hpos
    · have hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z :=
        (key_eq_of_mem_olcSlice hx).trans (key_eq_of_mem_olcSlice hz).symm
      have h0z : carryVal2 ctx z = 0 := by
        have := carryVal2_eq_of_returnSelfRefKey_eq ctx hkey
        omega
      have := h1 x (mem_olcFibre_of_mem_olcSlice hx)
        z (mem_olcFibre_of_mem_olcSlice hz) h0 h0z
      omega
    · exact h2 y hy x hx z hz hxz hpos j hjx hjz

/-- **The split form is an UNCONDITIONAL restatement**: at Q even the at-most-one
clause is vacuous (`carryVal2_pos_of_Q_even`: no val-0 member exists), so the split
is the verbatim demand there too. -/
theorem returnZeroBody_iff_qOddSplit_uncond (ctx : ActualFailureContext) :
    ReturnZeroBody ctx ↔ QOddReturnZeroSplit ctx := by
  rcases Nat.mod_two_eq_zero_or_one ctx.Q with hq | hq
  · have hQ2 : 2 ∣ ctx.Q := Nat.dvd_of_mod_eq_zero hq
    constructor
    · intro H
      constructor
      · intro x hx z hz h0x h0z
        have := carryVal2_pos_of_Q_even ctx hQ2 (olcFibre_mem_one_le ctx hx)
        omega
      · intro y hy x hx z hz hxz _ j hjx hjz
        exact H y hy x hx z hz hxz j hjx hjz
    · rintro ⟨h1, h2⟩
      intro y hy x hx z hz hxz j hjx hjz
      have hpos : 1 ≤ carryVal2 ctx x :=
        carryVal2_pos_of_Q_even ctx hQ2
          (olcFibre_mem_one_le ctx (mem_olcFibre_of_mem_olcSlice hx))
      exact h2 y hy x hx z hz hxz hpos j hjx hjz
  · exact returnZeroBody_iff_qOddSplit ctx hq

/-- The trajectory-side form: the wave-9/10 capstone field shape
`ReturnZeroBelowBandTrajectory` IS the Q-odd split (through the wave-10
unconditional equivalence `returnZeroBody_iff_belowBandTrajectory_uncond`). -/
theorem belowBandTrajectory_iff_qOddSplit (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) :
    ReturnZeroBelowBandTrajectory ctx ↔ QOddReturnZeroSplit ctx :=
  (returnZeroBody_iff_belowBandTrajectory_uncond ctx).symm.trans
    (returnZeroBody_iff_qOddSplit ctx hQodd)

/-- **Slices are parity-pure at Q odd**: same-key fibre members share parity - val-0
members are all odd (reset law); val-positive same-key members agree mod `2^v` with
`v >= 1`, hence mod 2. -/
theorem sameKey_parity_eq_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {x z : ℕ} (hx : x ∈ olcFibre ctx)
    (hz : z ∈ olcFibre ctx)
    (hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z) :
    x % 2 = z % 2 := by
  have hval := carryVal2_eq_of_returnSelfRefKey_eq ctx hkey
  have hpair : Nat.pair (carryVal2 ctx x) (x % 2 ^ carryVal2 ctx x)
      = Nat.pair (carryVal2 ctx z) (z % 2 ^ carryVal2 ctx z) := hkey
  have hres := (Nat.pair_eq_pair.mp hpair).2
  rcases Nat.eq_zero_or_pos (carryVal2 ctx x) with h0 | hpos
  · have h0z : carryVal2 ctx z = 0 := by omega
    have hxo := (olcFibre_val0_odd_hit_of_Q_odd ctx hQodd hx h0).1
    have hzo := (olcFibre_val0_odd_hit_of_Q_odd ctx hQodd hz h0z).1
    omega
  · rw [← hval] at hres
    have h2 : (2 : ℕ) ∣ 2 ^ carryVal2 ctx x := dvd_pow_self 2 (by omega)
    exact Nat.ModEq.of_dvd h2 hres

/-! ## Part 4.  `returnMaxClean` at Q odd - the parity split -/

/-- **The clean step at ODD `k+1` is a pure carry-parity fact (Q odd)**: via the
parity dictionary `carryOf_emod_two`, `d(k+1) = 0 <-> carryOf (k+1)` is even - the
demanded digit equals the reduced carry parity at odd positions. -/
theorem digit_succ_zero_iff_carry_even_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {k : ℕ} (hkeven : k % 2 = 0) :
    ctx.d (k + 1) = 0 ↔ carryOf ctx (k + 1) % 2 = 0 := by
  have hdict := carryOf_emod_two ctx k
  have hk1 : (k + 1) % 2 = 1 := by omega
  have hQk : (ctx.Q * (k + 1)) % 2 = 1 := by
    rw [Nat.mul_mod, hQodd, hk1]
  constructor
  · intro h0
    rw [hdict, h0]
    simp
  · intro hc
    rcases ctx.hd (k + 1) with h | h
    · exact h
    · exfalso
      rw [hdict, h, mul_one] at hc
      omega

/-- **At EVEN `k+1` the digit is invisible mod 2** (any `Q`): the parity dictionary
forces `carryOf (k+1)` even regardless of `d(k+1)` - the parity route gives no
information at even positions; the demand stays the unchanged doubling form. -/
theorem carryOf_emod_two_eq_zero_at_even_succ (ctx : ActualFailureContext) {k : ℕ}
    (hkodd : k % 2 = 1) : carryOf ctx (k + 1) % 2 = 0 := by
  have hdict := carryOf_emod_two ctx k
  have hk1 : (k + 1) % 2 = 0 := by omega
  have hm : (ctx.Q * (k + 1) * ctx.d (k + 1)) % 2 = 0 := by
    rw [Nat.mul_mod, Nat.mul_mod ctx.Q (k + 1), hk1]
    simp
  rw [hdict]
  omega

/-- **The Q-odd split form of the `returnMaxClean` demand**: at per-slice maxima `k`,
odd `k+1` (`k` even) demands the carry EVEN at `k+1` (pure parity); even `k+1`
(`k` odd) demands the unchanged carry doubling. -/
def QOddMaxCleanSplit (ctx : ActualFailureContext) : Prop :=
  ∀ k ∈ olcFibre ctx,
    (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
    ((k % 2 = 0 → carryOf ctx (k + 1) % 2 = 0) ∧
      (k % 2 = 1 → carryOf ctx (k + 1) = 2 * carryOf ctx k))

/-- **The exact Q-odd decomposition of `returnMaxClean`**: the verbatim digit demand
is the parity/doubling split. -/
theorem returnMaxCleanBody_iff_qOddSplit (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) :
    ReturnMaxCleanBody ctx ↔ QOddMaxCleanSplit ctx := by
  constructor
  · intro H k hk hmax
    have hd0 := H k hk hmax
    constructor
    · intro hke
      exact (digit_succ_zero_iff_carry_even_of_Q_odd ctx hQodd hke).mp hd0
    · intro _
      exact (digit_zero_iff_carry_doubles ctx k).mp hd0
  · intro H k hk hmax
    obtain ⟨h0, h1⟩ := H k hk hmax
    rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
    · exact (digit_succ_zero_iff_carry_even_of_Q_odd ctx hQodd hk2).mpr (h0 hk2)
    · exact (digit_zero_iff_carry_doubles ctx k).mpr (h1 hk2)

/-- The trajectory-side form: the wave-9/10 capstone field shape
`ReturnMaxCleanCarryTrajectory` IS the Q-odd split (through the wave-9 unconditional
equivalence `returnMaxCleanBody_iff_carryTrajectory`). -/
theorem maxCleanCarryTrajectory_iff_qOddSplit (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) :
    ReturnMaxCleanCarryTrajectory ctx ↔ QOddMaxCleanSplit ctx :=
  (returnMaxCleanBody_iff_carryTrajectory ctx).symm.trans
    (returnMaxCleanBody_iff_qOddSplit ctx hQodd)

/-! ## Part 5.  Capstone bridges - the per-parity successor fields -/

/-- **The Q-odd `returnZero` successor field**: under the verbatim capstone guards,
provide the SPLIT form at Q-odd contexts only.  (The dyadic-floor guard
`2^{v2(Q)} < W` is dropped: at Q odd it reads `1 < W` and is implied by the third
guard anyway.) -/
def ReturnZeroQOddSplitField : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    ctx.Q % 2 = 1 →
    QOddReturnZeroSplit ctx

/-- **The Q-even `returnZero` successor field**: the verbatim wave-10 dyadic-floor
trajectory field restricted to even denominators (where the floor `2^{v2(Q)} >= 2`
has content; the `W <= 2^{v2(Q)}` regime is already closed by
`returnZero_guard_refuted_of_width_le`). -/
def ReturnZeroQEvenFloorField : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    2 ^ ctxDyadicPart ctx < (supportShell ctx.shell.d ctx.shell.X).card →
    ctx.Q % 2 = 0 →
    ReturnZeroBelowBandTrajectory ctx

/-- **The Q-odd `returnMaxClean` successor field**: the parity/doubling split at
Q-odd contexts. -/
def ReturnMaxCleanQOddSplitField : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnIndexWindowClean ctx →
    ctx.Q % 2 = 1 →
    QOddMaxCleanSplit ctx

/-- **The Q-even `returnMaxClean` successor field**: the verbatim wave-9 trajectory
field restricted to even denominators. -/
def ReturnMaxCleanQEvenField : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnIndexWindowClean ctx →
    ctx.Q % 2 = 0 →
    ReturnMaxCleanCarryTrajectory ctx

/-- **The `returnZero` rebuild**: the two per-parity fields rebuild the verbatim
wave-10 `returnZeroTrajectoryFloor` field shape - parity case split, then the Q-odd
split equivalence or the Q-even field directly. -/
theorem returnZeroTrajectoryFloor_of_qOddSplit (h1 : ReturnZeroQOddSplitField)
    (h0 : ReturnZeroQEvenFloorField) :
    ∀ ctx : ActualFailureContext,
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      (∃ k ∈ olcFibre ctx,
        2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
      ¬ ReturnIndexWindowClean ctx →
      2 ^ ctxDyadicPart ctx < (supportShell ctx.shell.d ctx.shell.X).card →
      ReturnZeroBelowBandTrajectory ctx := by
  intro ctx hA hB hC hD hE
  rcases Nat.mod_two_eq_zero_or_one ctx.Q with hq | hq
  · exact h0 ctx hA hB hC hD hE hq
  · exact (belowBandTrajectory_iff_qOddSplit ctx hq).mpr (h1 ctx hA hB hC hD hq)

/-- **The `returnMaxClean` rebuild**: the two per-parity fields rebuild the verbatim
wave-9/10 `returnMaxCleanTrajectory` field shape. -/
theorem returnMaxCleanTrajectory_of_qOddSplit (h1 : ReturnMaxCleanQOddSplitField)
    (h0 : ReturnMaxCleanQEvenField) :
    ∀ ctx : ActualFailureContext,
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnIndexWindowClean ctx →
      ReturnMaxCleanCarryTrajectory ctx := by
  intro ctx hA hD
  rcases Nat.mod_two_eq_zero_or_one ctx.Q with hq | hq
  · exact h0 ctx hA hD hq
  · exact (maxCleanCarryTrajectory_iff_qOddSplit ctx hq).mpr (h1 ctx hA hD hq)

/-- **The combinator**: replace the two digit-side fields of any wave-10 valuation
surface by the four per-parity successor fields - the result is again a full
`Erdos260ValuationResidual`. -/
def valuationResidual_withQOddSplit (base : Erdos260ValuationResidual)
    (hz1 : ReturnZeroQOddSplitField) (hz0 : ReturnZeroQEvenFloorField)
    (hm1 : ReturnMaxCleanQOddSplitField) (hm0 : ReturnMaxCleanQEvenField) :
    Erdos260ValuationResidual :=
  { base with
    returnZeroTrajectoryFloor := returnZeroTrajectoryFloor_of_qOddSplit hz1 hz0
    returnMaxCleanTrajectory := returnMaxCleanTrajectory_of_qOddSplit hm1 hm0 }

/-- **Endpoint**: `Erdos260Statement` from a wave-10 surface whose two digit-side
fields are supplied in per-parity split form. -/
theorem erdos260_of_qOddSplit (base : Erdos260ValuationResidual)
    (hz1 : ReturnZeroQOddSplitField) (hz0 : ReturnZeroQEvenFloorField)
    (hm1 : ReturnMaxCleanQOddSplitField) (hm0 : ReturnMaxCleanQEvenField) :
    Erdos260Statement :=
  erdos260_of_valuationResidual
    (valuationResidual_withQOddSplit base hz1 hz0 hm1 hm0)

/-! ## Part 6.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the Q-odd reset-closure module. -/
def qOddResetClosureStatus : List String :=
  [ "OFF-BY-ONE VERDICT (goal 1, settled): the ReturnZeroBody demand interval is " ++
      "(x, z] INCLUDING the right endpoint z (x < j -> j <= z -> d j = 0; " ++
      "returnZeroBody_demands_right_endpoint).  At carryVal2 = 0 the slice key " ++
      "collapses to Nat.pair 0 0 (returnSelfRefKey_eq_pairZero_iff_val0: k % 2^0 = " ++
      "0), so ALL val-0 fibre members are pairwise same-slice.  At Q odd the reset " ++
      "law (carryVal2_eq_zero_iff_of_Q_odd) says a val-0 member z has d z = 1, " ++
      "contradicting the demanded d z = 0: TWO distinct val-0 members refute " ++
      "ReturnZeroBody OUTRIGHT (returnZeroBody_refuted_of_val0_pair).  Hence " ++
      "returnZero forces AT MOST ONE val-0 member in the WHOLE fibre - not just per " ++
      "slice, since the val-0 slice is unique (returnZeroBody_val0_unique_of_Q_odd, " ++
      "card form returnZeroBody_val0_card_le_one_of_Q_odd, trigger " ++
      "returnZeroBody_refuted_of_two_val0_of_Q_odd).",
    "VAL-0 MEMBER STRUCTURE (goal 2): at Q odd a val-0 fibre member k is an odd raw " ++
      "position that is a hit, d k = 1 (olcFibre_val0_odd_hit_of_Q_odd: carryVal2 " ++
      "measures the carry at the member's RAW position; members sit at k >= L >= 28 " ++
      ">= 1 so the reset law applies, olcFibre_mem_one_le).  Sparse-support counts: " ++
      "val-0 members lie in supportIn d (2X) (olcFibre_val0_mem_supportIn_of_Q_odd, " ++
      "via returnFibre_le_two_mul) and inject into the odd hits of the index window " ++
      "[F, F+W) (olcFibre_val0_subset_window_hits_of_Q_odd); counts " ++
      "olcFibre_val0_card_le_window_hits_of_Q_odd and " ++
      "olcFibre_val0_card_le_supportCount_of_Q_odd.  Under ReturnZeroBody the fibre " ++
      "is its val-positive part plus at most one element " ++
      "(returnZeroBody_fibre_card_le_of_Q_odd).",
    "THE Q-ODD DECOMPOSITION (the sharp restatement, goal 1+2): ReturnZeroBody <-> " ++
      "QOddReturnZeroSplit = QOddVal0AtMostOne AND QOddValPosZeroRun " ++
      "(returnZeroBody_iff_qOddSplit) - the reset law converts the val-0 part of " ++
      "the demand into a pure COUNT statement (at most one val-0 member) and leaves " ++
      "the zero-run demand only on val-POSITIVE slice pairs (where the spacing " ++
      "2^carryVal2 | z - x has content).  The split is an UNCONDITIONAL restatement " ++
      "(returnZeroBody_iff_qOddSplit_uncond: at Q even the count clause is vacuous " ++
      "by carryVal2_pos_of_Q_even).  Trajectory form belowBandTrajectory_iff_" ++
      "qOddSplit (via the wave-10 returnZeroBody_iff_belowBandTrajectory_uncond).  " ++
      "Slice geometry: slices are parity-pure at Q odd (sameKey_parity_eq_of_Q_odd).",
    "HONEST: returnZero at Q odd is NOT closed outright.  What would close it: " ++
      "either (refutation route) TWO val-0 fibre members - i.e. two odd raw hit " ++
      "positions inside the member window - or (vacuous route) emptiness of " ++
      "val-positive same-slice pairs plus val-0 count <= 1.  Neither count fact is " ++
      "provable from the in-tree window floors: carryFloor_supportCount_ge_of_le_" ++
      "depth gives >= L hits below X but controls neither their parity nor their " ++
      "membership in the class-4 fibre.  The residual demand after this module is " ++
      "the SPLIT form (strictly sharper surface than the verbatim field: the val-0 " ++
      "interval demands are replaced by one counting clause).",
    "RETURNMAXCLEAN AT Q ODD (goal 3): at a per-slice maximum k the demand d(k+1) = " ++
      "0 splits by the parity of k+1.  k+1 ODD (k even): the demand is EQUIVALENT " ++
      "to the carry being EVEN at k+1 (digit_succ_zero_iff_carry_even_of_Q_odd, via " ++
      "the parity dictionary carryOf_emod_two with Q(k+1) odd) - a pure carry-parity " ++
      "fact, no digit content.  k+1 EVEN (k odd): the digit is INVISIBLE mod 2 - " ++
      "the dictionary forces carryOf (k+1) % 2 = 0 regardless of the digit AND of Q " ++
      "(carryOf_emod_two_eq_zero_at_even_succ), so the parity route gives nothing " ++
      "and the demand stays the unchanged doubling form (digit_zero_iff_carry_" ++
      "doubles).  Exact split: ReturnMaxCleanBody <-> QOddMaxCleanSplit " ++
      "(returnMaxCleanBody_iff_qOddSplit); trajectory form maxCleanCarryTrajectory_" ++
      "iff_qOddSplit.  HONEST: even maxima are NOT excluded by the slice structure " ++
      "- they sit in val-positive parity-pure slices (sameKey_parity_eq_of_Q_odd); " ++
      "no in-tree fact rules them out.",
    "THE TOTAL REMAINING DIGIT SURFACE (goal 4, honest): returnZero - (a) W <= " ++
      "2^{v2(Q)} shells CLOSED (wave 10, returnZero_guard_refuted_of_width_le; for " ++
      "Q odd this is only W <= 1); (b) Q even, W > 2^{v2(Q)}: OPEN in trajectory " ++
      "form (ReturnZeroQEvenFloorField); (c) Q odd: OPEN in SPLIT form " ++
      "(ReturnZeroQOddSplitField = at-most-one val-0 member + val-positive " ++
      "zero-runs; this module's sharpening - the dyadic-floor guard is dropped as " ++
      "contentless at Q odd).  returnMaxClean - (a) Q even: OPEN in doubling form " ++
      "(ReturnMaxCleanQEvenField, unchanged); (b) Q odd: OPEN in parity/doubling " ++
      "split form (ReturnMaxCleanQOddSplitField; at odd k+1 reduced to a carry-" ++
      "parity fact).  No regime of returnMaxClean was previously closed; none is " ++
      "closed here.",
    "CAPSTONE BRIDGES (goal 4): the four per-parity successor fields rebuild the " ++
      "verbatim wave-10 capstone fields - returnZeroTrajectoryFloor_of_qOddSplit " ++
      "and returnMaxCleanTrajectory_of_qOddSplit; combinator " ++
      "valuationResidual_withQOddSplit (base : Erdos260ValuationResidual) (four " ++
      "split fields) : Erdos260ValuationResidual; endpoint erdos260_of_qOddSplit : " ++
      "Erdos260Statement.  Strictly-weaker-to-provide accounting: the Q-odd " ++
      "returnZero obligation shrank from all-pairs zero-runs to the split form; " ++
      "the Q-odd returnMaxClean obligation shrank at odd k+1 from a digit equation " ++
      "to a carry parity; the Q-even fields are verbatim restrictions.",
    "HYGIENE: additive only; no upstream module touched; no sorry / admit / new " ++
      "axiom / native_decide; all #print axioms in [propext, Classical.choice, " ++
      "Quot.sound]." ]

theorem qOddResetClosureStatus_nonempty : qOddResetClosureStatus ≠ [] := by
  simp [qOddResetClosureStatus]

/-! ## Part 7.  Axiom-cleanliness audit -/

#print axioms returnZeroBody_demands_right_endpoint
#print axioms returnSelfRefKey_eq_pairZero_iff_val0
#print axioms carryVal2_eq_of_returnSelfRefKey_eq
#print axioms olcFibre_mem_one_le
#print axioms returnZeroBody_refuted_of_val0_pair
#print axioms returnZeroBody_val0_unique_of_Q_odd
#print axioms returnZeroBody_val0_card_le_one_of_Q_odd
#print axioms returnZeroBody_refuted_of_two_val0_of_Q_odd
#print axioms olcFibre_val0_odd_hit_of_Q_odd
#print axioms olcFibre_val0_mem_supportIn_of_Q_odd
#print axioms olcFibre_val0_subset_window_hits_of_Q_odd
#print axioms olcFibre_val0_card_le_window_hits_of_Q_odd
#print axioms olcFibre_val0_card_le_supportCount_of_Q_odd
#print axioms returnZeroBody_fibre_card_le_of_Q_odd
#print axioms returnZeroBody_iff_qOddSplit
#print axioms returnZeroBody_iff_qOddSplit_uncond
#print axioms belowBandTrajectory_iff_qOddSplit
#print axioms sameKey_parity_eq_of_Q_odd
#print axioms digit_succ_zero_iff_carry_even_of_Q_odd
#print axioms carryOf_emod_two_eq_zero_at_even_succ
#print axioms returnMaxCleanBody_iff_qOddSplit
#print axioms maxCleanCarryTrajectory_iff_qOddSplit
#print axioms returnZeroTrajectoryFloor_of_qOddSplit
#print axioms returnMaxCleanTrajectory_of_qOddSplit
#print axioms valuationResidual_withQOddSplit
#print axioms erdos260_of_qOddSplit
#print axioms qOddResetClosureStatus_nonempty

end

end Erdos260
