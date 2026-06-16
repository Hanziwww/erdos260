import Erdos260.Erdos260DatumCapstone

/-!
# Return / class 4 — quantified span gates, the band-2-free datum enumeration, and the
spaced-cycle digit criteria (`ReturnSpanGateClosure`, wave 5)

This module (NEW; it edits no existing file) attacks the four Return-lane fields still
carried by `Erdos260DatumResidual` (`returnGates` / `returnZero` / `returnMaxClean` /
`returnInterior`) and aggregates everything into a STRICTLY SMALLER successor residual
`ReturnSpanGateResidual`, bridged additively into the wave-4 capstone
(`erdos260_of_returnSpanGateResidual`).

## 1.  The span gates QUANTIFIED (numeric criteria, proved)

The wave-3 span gates constrain REALIZED hit positions.  Combining them with the proved
dyadic gap ceiling `hitGap ≤ L + B + 1` (`n24_hitGap_le_reach`, valid on every index
`j < i + K + r`) through a generic telescoped span bound (`hitGap_span_le`,
`a (i+n) − a i ≤ n·(L+B+1)`) yields purely NUMERIC per-shell criteria:

* **two-window**: `64·((W + r)·(L+B+1)) < 2·(129L + 64)` forces the wave-3 two-window span
  gate `64·(a(i+K+r) − a(i)) < 2·(129L+64)` (`returnSpanGate_twoWindow_of_numeric`), hence
  `returnGates` (`returnGatesBody_of_reach_numeric`) and `|fibre₄| ≤ r + 1`
  (`olcFibre_card_le_succ_r_of_reach_numeric`) — here `W = |supportShell| = K`;
* **in-window**: `64·((W − 1)·(L+B+1)) < 129L + 64` forces the in-window span gate
  `64·(a(i+K−1) − a(i)) < 129L+64` (`returnSpanGate_inWindow_of_numeric`, gates form
  `returnGatesBody_of_inWindow_numeric`, count form
  `olcFibre_card_le_succ_r_of_inWindow_numeric`);
* exact arithmetic relating them: K.1 gate + in-window numeric ⟹ two-window numeric
  (`returnSpan_twoWindow_numeric_of_gate_and_inWindow` — `(W+r) = (W−1) + (r+1)` splits the
  span additively across the two thresholds).

## 2.  The off-fixed cycle-count gate and the band-2-free datum enumeration

Off the unique band-2 fixed pair `(3, 1)`, `b₂ < c` on every period
(`datum_band2CycleCount_lt_of_offFixed`, imported).  The ceiling witness `t = ⌈W/c⌉`
(`ceil_cover`) turns the gate-4 entry into the explicit criterion
`⌈W/c⌉·b₂ ≤ r + 1` (`returnGatesBody_of_cycle_ceil`, off-fixed packaging
`returnGatesBody_offFixed_ceil`).  This is generally FALSE for large `W`, so the datum is
enumerated instead: the divisor pin `(2K₀+1) ∣ q` (`class0_datum_dvd`) confines odd `q < 64`
to EXACTLY 60 pairs — the two new windows `returnSG_datum_low_window_pairs` (`q < 17`, ten pairs) and
`datum_high_window_pairs` (`48 ≤ q < 64`, nineteen pairs) complete the existing mid/upper
enumerations.  Orbit tables (`canonGap_eq_of_bounds` arithmetic, no `Nat.log` evaluation)
classify all 60 pairs by per-cycle band-2 count `b₂`:

* **`b₂ = 0` (FIFTEEN pairs)**: `(5,2) (9,1) (9,4) (15,1) (15,2) (17,8) (21,1) (21,3)
  (21,10) (33,1) (33,16) (41,20) (63,1) (63,3) (63,4)` — a band-2-free period empties the
  class-4 fibre (`class4Fibre_empty_of_cycle_band_free`), so ALL FOUR return fields close
  outright (`returnCtxAllFour_of_cycle_band_free`, per-pair
  `returnCtxAllFour_of_datum_*`, aggregated over `ReturnB2FreeDatum` by
  `returnCtxAllFour_of_b2FreeDatum`).
* **`b₂ = 1` (seventeen pairs)**: `(3,1)c1{1} (7,3)c2{2} (13,6)c6{3} (15,7)c3{3}
  (31,15)c4{4} (33,5)c5{3} (39,1)c4{2} (39,6)c6{4} (45,7)c7{6} (45,22)c7{5} (51,1)c2{1}
  (51,8)c2{1} (55,2)c8{2} (57,1)c9{6} (57,28)c9{5} (63,10)c2{1} (63,31)c5{5}` (period `c`,
  band-2 residue set in braces).
* **`b₂ ≥ 2` (twenty-eight pairs)**: residue sets recorded in the status list below.

## 3.  The spaced-cycle digit criteria (`b₂ = 1`)

With a UNIQUE band-2 residue `j₀` per period, every two class-4 fibre members are congruent
mod `c` (`olcFibre_pair_mod_eq_of_band2_unique`) — the fibre is `c`-spaced.  Since any fibre
pair sits inside one window (`z − x < W`), `W ≤ c` forces the fibre to a SINGLETON
(`olcFibre_card_le_one_of_band2_unique`):

* `returnGates` closes (gate 4, `t = 1`: `returnGatesBody_of_band2_unique`);
* `returnZero` closes outright — no same-slice pair exists
  (`returnZeroBody_of_fibre_card_le_one`, `returnZeroBody_of_band2_unique`);
* `returnMaxClean` SHRINKS to one bare digit fact per member
  (`returnMaxCleanBody_iff_of_fibre_card_le_one` — the slice-max hypothesis is automatic);
* the full M.2.1 spacing pin for same-slice pairs `x < z`:
  `lcm(2^{carryVal2 x}, c) ∣ z − x`, `z − x < W`, AND `2^{carryVal2 x} < W`
  (`returnSelfRef_slice_pair_spacing` — combines `returnSelfRefKey_gapDiv`, the `c`-spacing
  and `returnSelfRef_sliceModulus_lt_width_of_pair`), with the lcm singleton criterion
  `returnZeroBody_of_band2_unique_lcm` (`W ≤ lcm(2^{v₂}, c)` kills all pairs).

Six pairs are closed per-pair on their spaced regimes (`W ≤ c`):
`(7,3) (31,15) (51,1) (51,8) (63,10) (63,31)` (`returnGatesZeroCard_of_datum_*`,
aggregated over `ReturnB2OneSpacedDatum`).  The fixed pair `(3, 1)` is NOT touched: there
`b₂ = c = 1`, every residue is band 2, and the spacing is vacuous — the honest wave-3/4
obstruction stays where it was.

## 4.  The successor residual (additive, strictly smaller)

`ReturnSpanGateResidual` rebuilds `Erdos260DatumResidual` VERBATIM (`toDatum`) while
demanding:

* `returnGates` only on ctx that are (i) NOT a band-2-free pair, (ii) NOT a spaced `b₂ = 1`
  pair, and (iii) FAIL the two-window numeric criterion;
* `returnZero` (small-carry regime) only on ctx that are neither (i) nor (ii);
* `returnMaxClean` / `returnInterior` only on ctx that are not (i).

Everything else is carried verbatim.  Final endpoint:
`erdos260_of_returnSpanGateResidual : ReturnSpanGateResidual → Erdos260Statement`.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## Part 0.  The four Return field bodies (verbatim wave-4 shapes) -/

/-- The `returnGates` field body of `Erdos260DatumResidual`, verbatim: K.1 gap-ceiling gate
OR two-window span gate OR in-window span gate OR band-2 cycle-count bound. -/
abbrev ReturnGatesBody (ctx : ActualFailureContext) : Prop :=
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
          ≤ ctx.n24CarryData.r + 1

/-- The `returnZero` field CONCLUSION, verbatim (the part after the small-carry regime
hypothesis): all-pairs zero-run between same-slice starts of the self-referential key. -/
abbrev ReturnZeroBody (ctx : ActualFailureContext) : Prop :=
  ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
    ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y,
      ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
        x < z → ∀ j, x < j → j ≤ z → ctx.d j = 0

/-- The `returnMaxClean` field body, verbatim: `d(k+1) = 0` at per-slice maxima. -/
abbrev ReturnMaxCleanBody (ctx : ActualFailureContext) : Prop :=
  ∀ k ∈ olcFibre ctx,
    (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
    ctx.d (k + 1) = 0

/-- The `returnInterior` field body, verbatim: descent windows stay strictly inside the
shell window. -/
abbrev ReturnInteriorBody (ctx : ActualFailureContext) : Prop :=
  ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
    k + ctx.n24CarryData.r + 1
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card

/-- All four Return field bodies at one ctx. -/
abbrev ReturnCtxAllFour (ctx : ActualFailureContext) : Prop :=
  ReturnGatesBody ctx ∧ ReturnZeroBody ctx ∧ ReturnMaxCleanBody ctx ∧ ReturnInteriorBody ctx

/-! ## Part 1.  The telescoped span ceiling and the QUANTIFIED span gates

The two wave-3 span gates constrain realized positions `a(i+K+r) − a(i)` and
`a(i+K−1) − a(i)`.  Telescoping the proved per-gap ceiling `hitGap ≤ L + B + 1`
(`n24_hitGap_le_reach`, valid on EVERY `j < i + K + r`) across the span yields numeric
per-shell criteria with no position data at all. -/

/-- **The generic telescoped span bound**: if every gap in `[i, i+n)` is `≤ G`, the total
position span obeys `a(i+n) − a(i) ≤ n·G`. -/
theorem hitGap_span_le (a : ℕ → ℕ) (ha : Monotone a) (G : ℕ) :
    ∀ n i : ℕ, (∀ m, m < n → hitGap a (i + m) ≤ G) → a (i + n) - a i ≤ n * G := by
  intro n
  induction n with
  | zero => intro i _; simp
  | succ n ih =>
      intro i h
      have hstep : a (i + n + 1) - a (i + n) ≤ G := by
        have h0 := h n (Nat.lt_succ_self n)
        unfold hitGap at h0
        exact h0
      have hih : a (i + n) - a i ≤ n * G := ih i (fun m hm => h m (Nat.lt_succ_of_lt hm))
      have h1 : a i ≤ a (i + n) := ha (Nat.le_add_right i n)
      have h2 : a (i + n) ≤ a (i + n + 1) := ha (Nat.le_succ (i + n))
      have hadd : i + (n + 1) = i + n + 1 := by omega
      rw [hadd, Nat.succ_mul]
      omega

/-- **The full-reach span ceiling**: `a(i + (W + r)) − a(i) ≤ (W + r)·(L + B + 1)` — every
gap of the total two-window span is within the proved dyadic reach ceiling. -/
theorem n24_span_le_reach (ctx : ActualFailureContext) :
    ctx.n24CarryData.a
        (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + ((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r))
      - ctx.n24CarryData.a (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
    ≤ ((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
  apply hitGap_span_le _ ctx.n24CarryData.carry.hits.strict.monotone
  intro m hm
  exact n24_hitGap_le_reach ctx (by omega)

/-- **The in-window span ceiling**: `a(i + (W − 1)) − a(i) ≤ (W − 1)·(L + B + 1)`. -/
theorem n24_span_le_window (ctx : ActualFailureContext) :
    ctx.n24CarryData.a
        (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + ((supportShell ctx.shell.d ctx.shell.X).card - 1))
      - ctx.n24CarryData.a (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
    ≤ ((supportShell ctx.shell.d ctx.shell.X).card - 1)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
  apply hitGap_span_le _ ctx.n24CarryData.carry.hits.strict.monotone
  intro m hm
  exact n24_hitGap_le_reach ctx (by omega)

/-- **The two-window span gate is NUMERIC** on shells with
`64·((W + r)·(L+B+1)) < 2·(129L + 64)`: the realized two-window span inequality of
`class4Fibre_card_le_succ_r_of_span_gate` holds with no position data. -/
theorem returnSpanGate_twoWindow_of_numeric (ctx : ActualFailureContext)
    (hnum : 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
      < 2 * (129 * shellLadderDepth ctx + 64)) :
    64 * (ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
        - ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X))
      < 2 * (129 * shellLadderDepth ctx + 64) := by
  have hspan := n24_span_le_reach ctx
  have hidx : ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
      + ((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
      = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r := by omega
  rw [hidx] at hspan
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 64 hspan) hnum

/-- **The in-window span gate is NUMERIC** on shells with
`64·((W − 1)·(L+B+1)) < 129L + 64`. -/
theorem returnSpanGate_inWindow_of_numeric (ctx : ActualFailureContext)
    (hnum : 64 * (((supportShell ctx.shell.d ctx.shell.X).card - 1)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
      < 129 * shellLadderDepth ctx + 64) :
    64 * (ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - 1)
        - ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X))
      < 129 * shellLadderDepth ctx + 64 := by
  have hW1 : 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
    le_trans (Nat.le_add_left 1 ctx.n24CarryData.r) (cnlMulti_r_add_one_le_width ctx)
  have hspan := n24_span_le_window ctx
  have hidx : ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
      + ((supportShell ctx.shell.d ctx.shell.X).card - 1)
      = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card - 1 := by omega
  rw [hidx] at hspan
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 64 hspan) hnum

/-- The two-window numeric criterion makes `returnGates` a THEOREM (second disjunct). -/
theorem returnGatesBody_of_reach_numeric (ctx : ActualFailureContext)
    (hnum : 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
      < 2 * (129 * shellLadderDepth ctx + 64)) :
    ReturnGatesBody ctx :=
  Or.inr (Or.inl (returnSpanGate_twoWindow_of_numeric ctx hnum))

/-- The in-window numeric criterion makes `returnGates` a THEOREM (third disjunct). -/
theorem returnGatesBody_of_inWindow_numeric (ctx : ActualFailureContext)
    (hnum : 64 * (((supportShell ctx.shell.d ctx.shell.X).card - 1)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
      < 129 * shellLadderDepth ctx + 64) :
    ReturnGatesBody ctx :=
  Or.inr (Or.inr (Or.inl (returnSpanGate_inWindow_of_numeric ctx hnum)))

/-- The K.1 gap-ceiling numeric criterion is the first gate verbatim. -/
theorem returnGatesBody_of_gapCeiling_numeric (ctx : ActualFailureContext)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
      < 129 * shellLadderDepth ctx + 64) :
    ReturnGatesBody ctx :=
  Or.inl hnum

/-- Count corollary: the two-window numeric criterion bounds the class-4 fibre,
`|fibre₄| ≤ r + 1`. -/
theorem olcFibre_card_le_succ_r_of_reach_numeric (ctx : ActualFailureContext)
    (hnum : 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
      < 2 * (129 * shellLadderDepth ctx + 64)) :
    (olcFibre ctx).card ≤ ctx.n24CarryData.r + 1 :=
  class4Fibre_card_le_succ_r_of_span_gate ctx (returnSpanGate_twoWindow_of_numeric ctx hnum)

/-- Count corollary: the in-window numeric criterion bounds the class-4 fibre. -/
theorem olcFibre_card_le_succ_r_of_inWindow_numeric (ctx : ActualFailureContext)
    (hnum : 64 * (((supportShell ctx.shell.d ctx.shell.X).card - 1)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
      < 129 * shellLadderDepth ctx + 64) :
    (olcFibre ctx).card ≤ ctx.n24CarryData.r + 1 :=
  class4Fibre_card_le_succ_r_of_inWindow_span ctx
    (returnSpanGate_inWindow_of_numeric ctx hnum)

/-- **The exact arithmetic between the criteria**: the K.1 gate plus the in-window numeric
criterion IMPLY the two-window numeric criterion — `(W + r) = (W − 1) + (r + 1)` splits the
span additively across the two `129L + 64` thresholds. -/
theorem returnSpan_twoWindow_numeric_of_gate_and_inWindow (ctx : ActualFailureContext)
    (h1 : 64 * ((ctx.n24CarryData.r + 1)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
      < 129 * shellLadderDepth ctx + 64)
    (h3 : 64 * (((supportShell ctx.shell.d ctx.shell.X).card - 1)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
      < 129 * shellLadderDepth ctx + 64) :
    64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
      < 2 * (129 * shellLadderDepth ctx + 64) := by
  have hW1 : 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
    le_trans (Nat.le_add_left 1 ctx.n24CarryData.r) (cnlMulti_r_add_one_le_width ctx)
  have hsplit : ((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
      * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
      = ((supportShell ctx.shell.d ctx.shell.X).card - 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
        + (ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
    have he : (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r
        = ((supportShell ctx.shell.d ctx.shell.X).card - 1) + (ctx.n24CarryData.r + 1) := by
      omega
    rw [he, Nat.add_mul]
  rw [hsplit]
  omega

/-! ## Part 2.  The off-fixed cycle-count gate: the explicit `⌈W/c⌉·b₂ ≤ r + 1` criterion -/

/-- The ceiling witness covers the window: `W ≤ ⌈W/c⌉·c` with `⌈W/c⌉ = (W + c − 1)/c`. -/
theorem ceil_cover {W c : ℕ} (hc : 1 ≤ c) : W ≤ (W + c - 1) / c * c := by
  have hdm : (W + c - 1) / c * c + (W + c - 1) % c = W + c - 1 :=
    Nat.div_add_mod' (W + c - 1) c
  have hmod : (W + c - 1) % c < c := Nat.mod_lt _ (by omega)
  omega

/-- **The explicit cycle-count criterion for the gate-4 entry**: any period `c ≥ 1` with
`⌈W/c⌉·b₂(q, K₀, c) ≤ r + 1` discharges `returnGates` (fourth disjunct, witness
`t = ⌈W/c⌉`). -/
theorem returnGatesBody_of_cycle_ceil (ctx : ActualFailureContext) {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hceil : ((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c
        * band2CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c
      ≤ ctx.n24CarryData.r + 1) :
    ReturnGatesBody ctx := by
  refine Or.inr (Or.inr (Or.inr
    ⟨c, ((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c, hc, hper,
      ceil_cover hc, ?_⟩))
  have hcount : band2CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c
      = ((Finset.Icc 1 c).filter (fun j =>
          canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q
              (class1SlopeDatum ctx).K₀ j) = 2)).card := rfl
  rw [← hcount]
  exact hceil

/-- **The off-fixed packaging**: off `(3, 1)` the ceiling criterion closes the gates AND the
cycle count is strictly deficient, `b₂ < c` (the strict factor the criterion can exploit). -/
theorem returnGatesBody_offFixed_ceil (ctx : ActualFailureContext)
    (hoff : ¬((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1))
    {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hceil : ((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c
        * band2CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c
      ≤ ctx.n24CarryData.r + 1) :
    ReturnGatesBody ctx
      ∧ band2CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c < c :=
  ⟨returnGatesBody_of_cycle_ceil ctx hc hper hceil,
    datum_band2CycleCount_lt_of_offFixed ctx hoff hc hper⟩

/-! ## Part 3.  The datum enumerations: `q < 17` and `48 ≤ q < 64`

Pure `(q, K)` arithmetic from the divisor pin, completing the existing mid/upper windows to
ALL odd moduli `q < 64` (60 pairs total: 10 + 13 + 18 + 19). -/

/-- **The low-window datum enumeration**: on `q < 17` the divisor pin admits exactly ten
pairs. -/
theorem returnSG_datum_low_window_pairs {q K : ℕ} (hq_odd : Odd q) (hK1 : 1 ≤ K)
    (h2K : 2 * K < q) (hdvd : 2 * K + 1 ∣ q) (h17 : q < 17) :
    (q = 3 ∧ K = 1) ∨ (q = 5 ∧ K = 2) ∨ (q = 7 ∧ K = 3) ∨ (q = 9 ∧ K = 1)
    ∨ (q = 9 ∧ K = 4) ∨ (q = 11 ∧ K = 5) ∨ (q = 13 ∧ K = 6) ∨ (q = 15 ∧ K = 1)
    ∨ (q = 15 ∧ K = 2) ∨ (q = 15 ∧ K = 7) := by
  obtain ⟨s, hs⟩ := hdvd
  obtain ⟨t, ht⟩ := hq_odd
  have hK7 : K ≤ 7 := by omega
  have hq7 : q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 9 ∨ q = 11 ∨ q = 13 ∨ q = 15 := by omega
  rcases hq7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases K <;> ((try ring_nf at hs); first | (norm_num; done) | (exfalso; omega))

/-- **The high-window datum enumeration**: on `48 ≤ q < 64` the divisor pin admits exactly
nineteen pairs. -/
theorem datum_high_window_pairs {q K : ℕ} (hq_odd : Odd q) (hK1 : 1 ≤ K)
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

/-- Ctx form of the low-window enumeration (the pin is `class0_datum_dvd`). -/
theorem returnDatum_low_window_resolved (ctx : ActualFailureContext)
    (h17 : (class1SlopeDatum ctx).q < 17) :
    ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1)
    ∨ ((class1SlopeDatum ctx).q = 5 ∧ (class1SlopeDatum ctx).K₀ = 2)
    ∨ ((class1SlopeDatum ctx).q = 7 ∧ (class1SlopeDatum ctx).K₀ = 3)
    ∨ ((class1SlopeDatum ctx).q = 9 ∧ (class1SlopeDatum ctx).K₀ = 1)
    ∨ ((class1SlopeDatum ctx).q = 9 ∧ (class1SlopeDatum ctx).K₀ = 4)
    ∨ ((class1SlopeDatum ctx).q = 11 ∧ (class1SlopeDatum ctx).K₀ = 5)
    ∨ ((class1SlopeDatum ctx).q = 13 ∧ (class1SlopeDatum ctx).K₀ = 6)
    ∨ ((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 1)
    ∨ ((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 2)
    ∨ ((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 7) :=
  returnSG_datum_low_window_pairs (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum_two_K₀_lt ctx) (class0_datum_dvd ctx) h17

/-- Ctx form of the high-window enumeration. -/
theorem returnDatum_high_window_resolved (ctx : ActualFailureContext)
    (h48 : 48 ≤ (class1SlopeDatum ctx).q) (h64 : (class1SlopeDatum ctx).q < 64) :
    ((class1SlopeDatum ctx).q = 49 ∧ (class1SlopeDatum ctx).K₀ = 3)
    ∨ ((class1SlopeDatum ctx).q = 49 ∧ (class1SlopeDatum ctx).K₀ = 24)
    ∨ ((class1SlopeDatum ctx).q = 51 ∧ (class1SlopeDatum ctx).K₀ = 1)
    ∨ ((class1SlopeDatum ctx).q = 51 ∧ (class1SlopeDatum ctx).K₀ = 8)
    ∨ ((class1SlopeDatum ctx).q = 51 ∧ (class1SlopeDatum ctx).K₀ = 25)
    ∨ ((class1SlopeDatum ctx).q = 53 ∧ (class1SlopeDatum ctx).K₀ = 26)
    ∨ ((class1SlopeDatum ctx).q = 55 ∧ (class1SlopeDatum ctx).K₀ = 2)
    ∨ ((class1SlopeDatum ctx).q = 55 ∧ (class1SlopeDatum ctx).K₀ = 5)
    ∨ ((class1SlopeDatum ctx).q = 55 ∧ (class1SlopeDatum ctx).K₀ = 27)
    ∨ ((class1SlopeDatum ctx).q = 57 ∧ (class1SlopeDatum ctx).K₀ = 1)
    ∨ ((class1SlopeDatum ctx).q = 57 ∧ (class1SlopeDatum ctx).K₀ = 9)
    ∨ ((class1SlopeDatum ctx).q = 57 ∧ (class1SlopeDatum ctx).K₀ = 28)
    ∨ ((class1SlopeDatum ctx).q = 59 ∧ (class1SlopeDatum ctx).K₀ = 29)
    ∨ ((class1SlopeDatum ctx).q = 61 ∧ (class1SlopeDatum ctx).K₀ = 30)
    ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 1)
    ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 3)
    ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 4)
    ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 10)
    ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 31) :=
  datum_high_window_pairs (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum_two_K₀_lt ctx) (class0_datum_dvd ctx) h48 h64

/-! ## Part 4.  The band-2-free full closure: a band-2-free period closes ALL FOUR fields -/

/-- One explicit orbit step through the band bounds (no `Nat.log` evaluation). -/
private theorem orbit_step {q K₀ j K g K' : ℕ} (hq : Odd q)
    (h : slopeOrbit q K₀ j = K) (hK1 : 1 ≤ K) (hKq : K < q)
    (hlow : q < 2 ^ g * K) (hhigh : 2 ^ g * K < 2 * q) (hval : 2 ^ g * K - q = K') :
    slopeOrbit q K₀ (j + 1) = K' := by
  have hstep : slopeOrbit q K₀ (j + 1) = boundedSlopeStep q (slopeOrbit q K₀ j) := rfl
  rw [hstep, h, boundedSlopeStep_eq_of_bounds hq hK1 hKq hlow hhigh, hval]

/-- A non-band-2 reading through the band bounds. -/
private theorem canonGap_ne_two_of_bounds {q K g : ℕ} (hq : Odd q) (hK1 : 1 ≤ K)
    (hKq : K < q) (hlow : q < 2 ^ g * K) (hhigh : 2 ^ g * K < 2 * q) (hg : g ≠ 2) :
    canonGap q K ≠ 2 := by
  rw [canonGap_eq_of_bounds hq hK1 hKq hlow hhigh]
  exact hg

/-- **A band-2-free period closes ALL FOUR Return fields at once**: the class-4 fibre is
empty (`class4Fibre_empty_of_cycle_band_free`), so the count gate holds with `t·b₂ = 0`,
the digit fields hold vacuously, and interior holds through emptiness. -/
theorem returnCtxAllFour_of_cycle_band_free (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c → canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 2) :
    ReturnCtxAllFour ctx := by
  have hempty : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4 = ∅ :=
    class4Fibre_empty_of_cycle_band_free ctx hc hper hband
  have holc : olcFibre ctx = ∅ := by
    rw [olcFibre_def]
    exact hempty
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Or.inr (Or.inr (Or.inr
      ⟨c, (supportShell ctx.shell.d ctx.shell.X).card, hc, hper, ?_, ?_⟩))
    · exact Nat.le_mul_of_pos_right _ hc
    · have hfe : (Finset.Icc 1 c).filter (fun j =>
          canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q
              (class1SlopeDatum ctx).K₀ j) = 2) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro j hj
        rw [Finset.mem_Icc] at hj
        exact hband j hj.1 hj.2
      rw [hfe, Finset.card_empty, Nat.mul_zero]
      exact Nat.zero_le _
  · intro y hy
    rw [holc, Finset.image_empty] at hy
    exact absurd hy (Finset.notMem_empty y)
  · intro k hk
    rw [holc] at hk
    exact absurd hk (Finset.notMem_empty k)
  · exact class4Interior_of_cycle_band_free ctx hc hper hband

/-! ### The fifteen band-2-free pairs (orbit certificates + per-pair closures) -/

/-- `(5, 2)`: cycle `[3, 1]` (period 2, bands `1, 3`) — band-2-free. -/
theorem returnCtxAllFour_of_datum_5_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 5) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    ReturnCtxAllFour ctx := by
  have hodd : Odd (5 : ℕ) := ⟨2, by norm_num⟩
  have h0 : slopeOrbit 5 2 0 = 2 := rfl
  have h1 : slopeOrbit 5 2 1 = 3 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 5 2 2 = 1 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h3 : slopeOrbit 5 2 3 = 3 :=
    orbit_step hodd h2 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num)
      (by norm_num)
  refine returnCtxAllFour_of_cycle_band_free ctx (c := 2) (by norm_num) ?_ ?_
  · rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 5 2 3 = slopeOrbit 5 2 1
    rw [h3, h1]
  · rw [hq, hK]
    intro j hj1 hj2
    interval_cases j
    · rw [h1]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h2]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 3)
        (by norm_num) (by norm_num) (by norm_num)

/-- `(9, 1)`: cycle `[7, 5, 1]` (period 3, bands `1, 1, 4`) — band-2-free. -/
theorem returnCtxAllFour_of_datum_9_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ReturnCtxAllFour ctx := by
  have hodd : Odd (9 : ℕ) := ⟨4, by norm_num⟩
  have h0 : slopeOrbit 9 1 0 = 1 := rfl
  have h1 : slopeOrbit 9 1 1 = 7 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 9 1 2 = 5 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h3 : slopeOrbit 9 1 3 = 1 :=
    orbit_step hodd h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h4 : slopeOrbit 9 1 4 = 7 :=
    orbit_step hodd h3 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num)
      (by norm_num)
  refine returnCtxAllFour_of_cycle_band_free ctx (c := 3) (by norm_num) ?_ ?_
  · rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 9 1 4 = slopeOrbit 9 1 1
    rw [h4, h1]
  · rw [hq, hK]
    intro j hj1 hj2
    interval_cases j
    · rw [h1]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h2]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h3]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 4)
        (by norm_num) (by norm_num) (by norm_num)

/-- `(9, 4)`: enters the band-2-free cycle `[7, 5, 1]` after one step. -/
theorem returnCtxAllFour_of_datum_9_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    ReturnCtxAllFour ctx := by
  have hodd : Odd (9 : ℕ) := ⟨4, by norm_num⟩
  have h0 : slopeOrbit 9 4 0 = 4 := rfl
  have h1 : slopeOrbit 9 4 1 = 7 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 9 4 2 = 5 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h3 : slopeOrbit 9 4 3 = 1 :=
    orbit_step hodd h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h4 : slopeOrbit 9 4 4 = 7 :=
    orbit_step hodd h3 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num)
      (by norm_num)
  refine returnCtxAllFour_of_cycle_band_free ctx (c := 3) (by norm_num) ?_ ?_
  · rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 9 4 4 = slopeOrbit 9 4 1
    rw [h4, h1]
  · rw [hq, hK]
    intro j hj1 hj2
    interval_cases j
    · rw [h1]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h2]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h3]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 4)
        (by norm_num) (by norm_num) (by norm_num)

/-- `(15, 1)`: fixed cycle `[1]` (band `4`) — band-2-free. -/
theorem returnCtxAllFour_of_datum_15_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ReturnCtxAllFour ctx := by
  have hodd : Odd (15 : ℕ) := ⟨7, by norm_num⟩
  have h0 : slopeOrbit 15 1 0 = 1 := rfl
  have h1 : slopeOrbit 15 1 1 = 1 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 15 1 2 = 1 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num)
      (by norm_num)
  refine returnCtxAllFour_of_cycle_band_free ctx (c := 1) (by norm_num) ?_ ?_
  · rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 15 1 2 = slopeOrbit 15 1 1
    rw [h2, h1]
  · rw [hq, hK]
    intro j hj1 hj2
    interval_cases j
    rw [h1]
    exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 4)
      (by norm_num) (by norm_num) (by norm_num)

/-- `(15, 2)`: enters the fixed cycle `[1]` after one step — band-2-free. -/
theorem returnCtxAllFour_of_datum_15_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    ReturnCtxAllFour ctx := by
  have hodd : Odd (15 : ℕ) := ⟨7, by norm_num⟩
  have h0 : slopeOrbit 15 2 0 = 2 := rfl
  have h1 : slopeOrbit 15 2 1 = 1 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 15 2 2 = 1 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num)
      (by norm_num)
  refine returnCtxAllFour_of_cycle_band_free ctx (c := 1) (by norm_num) ?_ ?_
  · rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 15 2 2 = slopeOrbit 15 2 1
    rw [h2, h1]
  · rw [hq, hK]
    intro j hj1 hj2
    interval_cases j
    rw [h1]
    exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 4)
      (by norm_num) (by norm_num) (by norm_num)

/-- `(17, 8)`: cycle `[15, 13, 9, 1]` (period 4, bands `1, 1, 1, 5`) — band-2-free. -/
theorem returnCtxAllFour_of_datum_17_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 17) (hK : (class1SlopeDatum ctx).K₀ = 8) :
    ReturnCtxAllFour ctx := by
  have hodd : Odd (17 : ℕ) := ⟨8, by norm_num⟩
  have h0 : slopeOrbit 17 8 0 = 8 := rfl
  have h1 : slopeOrbit 17 8 1 = 15 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 17 8 2 = 13 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h3 : slopeOrbit 17 8 3 = 9 :=
    orbit_step hodd h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h4 : slopeOrbit 17 8 4 = 1 :=
    orbit_step hodd h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h5 : slopeOrbit 17 8 5 = 15 :=
    orbit_step hodd h4 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num)
      (by norm_num)
  refine returnCtxAllFour_of_cycle_band_free ctx (c := 4) (by norm_num) ?_ ?_
  · rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 17 8 5 = slopeOrbit 17 8 1
    rw [h5, h1]
  · rw [hq, hK]
    intro j hj1 hj2
    interval_cases j
    · rw [h1]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h2]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h3]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h4]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 5)
        (by norm_num) (by norm_num) (by norm_num)

/-- `(21, 1)`: cycle `[11, 1]` (period 2, bands `1, 5`) — band-2-free. -/
theorem returnCtxAllFour_of_datum_21_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ReturnCtxAllFour ctx := by
  have hodd : Odd (21 : ℕ) := ⟨10, by norm_num⟩
  have h0 : slopeOrbit 21 1 0 = 1 := rfl
  have h1 : slopeOrbit 21 1 1 = 11 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 21 1 2 = 1 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h3 : slopeOrbit 21 1 3 = 11 :=
    orbit_step hodd h2 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num)
      (by norm_num)
  refine returnCtxAllFour_of_cycle_band_free ctx (c := 2) (by norm_num) ?_ ?_
  · rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 21 1 3 = slopeOrbit 21 1 1
    rw [h3, h1]
  · rw [hq, hK]
    intro j hj1 hj2
    interval_cases j
    · rw [h1]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h2]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 5)
        (by norm_num) (by norm_num) (by norm_num)

/-- `(21, 3)`: fixed cycle `[3]` (band `3`) — band-2-free. -/
theorem returnCtxAllFour_of_datum_21_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    ReturnCtxAllFour ctx := by
  have hodd : Odd (21 : ℕ) := ⟨10, by norm_num⟩
  have h0 : slopeOrbit 21 3 0 = 3 := rfl
  have h1 : slopeOrbit 21 3 1 = 3 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 21 3 2 = 3 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num)
      (by norm_num)
  refine returnCtxAllFour_of_cycle_band_free ctx (c := 1) (by norm_num) ?_ ?_
  · rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 21 3 2 = slopeOrbit 21 3 1
    rw [h2, h1]
  · rw [hq, hK]
    intro j hj1 hj2
    interval_cases j
    rw [h1]
    exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 3)
      (by norm_num) (by norm_num) (by norm_num)

/-- `(21, 10)`: cycle `[19, 17, 13, 5]` (period 4, bands `1, 1, 1, 3`) — band-2-free. -/
theorem returnCtxAllFour_of_datum_21_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    ReturnCtxAllFour ctx := by
  have hodd : Odd (21 : ℕ) := ⟨10, by norm_num⟩
  have h0 : slopeOrbit 21 10 0 = 10 := rfl
  have h1 : slopeOrbit 21 10 1 = 19 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 21 10 2 = 17 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h3 : slopeOrbit 21 10 3 = 13 :=
    orbit_step hodd h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h4 : slopeOrbit 21 10 4 = 5 :=
    orbit_step hodd h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h5 : slopeOrbit 21 10 5 = 19 :=
    orbit_step hodd h4 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num)
      (by norm_num)
  refine returnCtxAllFour_of_cycle_band_free ctx (c := 4) (by norm_num) ?_ ?_
  · rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 21 10 5 = slopeOrbit 21 10 1
    rw [h5, h1]
  · rw [hq, hK]
    intro j hj1 hj2
    interval_cases j
    · rw [h1]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h2]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h3]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h4]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 3)
        (by norm_num) (by norm_num) (by norm_num)

/-- `(33, 1)`: cycle `[31, 29, 25, 17, 1]` (period 5, bands `1, 1, 1, 1, 6`) —
band-2-free. -/
theorem returnCtxAllFour_of_datum_33_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ReturnCtxAllFour ctx := by
  have hodd : Odd (33 : ℕ) := ⟨16, by norm_num⟩
  have h0 : slopeOrbit 33 1 0 = 1 := rfl
  have h1 : slopeOrbit 33 1 1 = 31 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 33 1 2 = 29 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h3 : slopeOrbit 33 1 3 = 25 :=
    orbit_step hodd h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h4 : slopeOrbit 33 1 4 = 17 :=
    orbit_step hodd h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h5 : slopeOrbit 33 1 5 = 1 :=
    orbit_step hodd h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h6 : slopeOrbit 33 1 6 = 31 :=
    orbit_step hodd h5 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num)
      (by norm_num)
  refine returnCtxAllFour_of_cycle_band_free ctx (c := 5) (by norm_num) ?_ ?_
  · rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 33 1 6 = slopeOrbit 33 1 1
    rw [h6, h1]
  · rw [hq, hK]
    intro j hj1 hj2
    interval_cases j
    · rw [h1]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h2]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h3]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h4]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h5]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 6)
        (by norm_num) (by norm_num) (by norm_num)

/-- `(33, 16)`: enters the band-2-free cycle `[31, 29, 25, 17, 1]` after one step. -/
theorem returnCtxAllFour_of_datum_33_16 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 16) :
    ReturnCtxAllFour ctx := by
  have hodd : Odd (33 : ℕ) := ⟨16, by norm_num⟩
  have h0 : slopeOrbit 33 16 0 = 16 := rfl
  have h1 : slopeOrbit 33 16 1 = 31 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 33 16 2 = 29 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h3 : slopeOrbit 33 16 3 = 25 :=
    orbit_step hodd h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h4 : slopeOrbit 33 16 4 = 17 :=
    orbit_step hodd h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h5 : slopeOrbit 33 16 5 = 1 :=
    orbit_step hodd h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h6 : slopeOrbit 33 16 6 = 31 :=
    orbit_step hodd h5 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num)
      (by norm_num)
  refine returnCtxAllFour_of_cycle_band_free ctx (c := 5) (by norm_num) ?_ ?_
  · rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 33 16 6 = slopeOrbit 33 16 1
    rw [h6, h1]
  · rw [hq, hK]
    intro j hj1 hj2
    interval_cases j
    · rw [h1]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h2]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h3]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h4]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h5]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 6)
        (by norm_num) (by norm_num) (by norm_num)

/-- `(41, 20)`: cycle `[39, 37, 33, 25, 9, 31, 21, 1, 23, 5]` (period 10, bands
`1, 1, 1, 1, 3, 1, 1, 6, 1, 4`) — band-2-free. -/
theorem returnCtxAllFour_of_datum_41_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 41) (hK : (class1SlopeDatum ctx).K₀ = 20) :
    ReturnCtxAllFour ctx := by
  have hodd : Odd (41 : ℕ) := ⟨20, by norm_num⟩
  have h0 : slopeOrbit 41 20 0 = 20 := rfl
  have h1 : slopeOrbit 41 20 1 = 39 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 41 20 2 = 37 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h3 : slopeOrbit 41 20 3 = 33 :=
    orbit_step hodd h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h4 : slopeOrbit 41 20 4 = 25 :=
    orbit_step hodd h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h5 : slopeOrbit 41 20 5 = 9 :=
    orbit_step hodd h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h6 : slopeOrbit 41 20 6 = 31 :=
    orbit_step hodd h5 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num)
      (by norm_num)
  have h7 : slopeOrbit 41 20 7 = 21 :=
    orbit_step hodd h6 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h8 : slopeOrbit 41 20 8 = 1 :=
    orbit_step hodd h7 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h9 : slopeOrbit 41 20 9 = 23 :=
    orbit_step hodd h8 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num)
      (by norm_num)
  have h10 : slopeOrbit 41 20 10 = 5 :=
    orbit_step hodd h9 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h11 : slopeOrbit 41 20 11 = 39 :=
    orbit_step hodd h10 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num)
      (by norm_num)
  refine returnCtxAllFour_of_cycle_band_free ctx (c := 10) (by norm_num) ?_ ?_
  · rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 41 20 11 = slopeOrbit 41 20 1
    rw [h11, h1]
  · rw [hq, hK]
    intro j hj1 hj2
    interval_cases j
    · rw [h1]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h2]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h3]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h4]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h5]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 3)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h6]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h7]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h8]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 6)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h9]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h10]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 4)
        (by norm_num) (by norm_num) (by norm_num)

/-- `(63, 1)`: fixed cycle `[1]` (band `6`) — band-2-free. -/
theorem returnCtxAllFour_of_datum_63_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ReturnCtxAllFour ctx := by
  have hodd : Odd (63 : ℕ) := ⟨31, by norm_num⟩
  have h0 : slopeOrbit 63 1 0 = 1 := rfl
  have h1 : slopeOrbit 63 1 1 = 1 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 63 1 2 = 1 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num)
      (by norm_num)
  refine returnCtxAllFour_of_cycle_band_free ctx (c := 1) (by norm_num) ?_ ?_
  · rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 63 1 2 = slopeOrbit 63 1 1
    rw [h2, h1]
  · rw [hq, hK]
    intro j hj1 hj2
    interval_cases j
    rw [h1]
    exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 6)
      (by norm_num) (by norm_num) (by norm_num)

/-- `(63, 3)`: cycle `[33, 3]` (period 2, bands `1, 5`) — band-2-free. -/
theorem returnCtxAllFour_of_datum_63_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    ReturnCtxAllFour ctx := by
  have hodd : Odd (63 : ℕ) := ⟨31, by norm_num⟩
  have h0 : slopeOrbit 63 3 0 = 3 := rfl
  have h1 : slopeOrbit 63 3 1 = 33 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 63 3 2 = 3 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h3 : slopeOrbit 63 3 3 = 33 :=
    orbit_step hodd h2 (by norm_num) (by norm_num) (g := 5) (by norm_num) (by norm_num)
      (by norm_num)
  refine returnCtxAllFour_of_cycle_band_free ctx (c := 2) (by norm_num) ?_ ?_
  · rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 63 3 3 = slopeOrbit 63 3 1
    rw [h3, h1]
  · rw [hq, hK]
    intro j hj1 hj2
    interval_cases j
    · rw [h1]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 1)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [h2]
      exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 5)
        (by norm_num) (by norm_num) (by norm_num)

/-- `(63, 4)`: enters the fixed cycle `[1]` after one step — band-2-free. -/
theorem returnCtxAllFour_of_datum_63_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    ReturnCtxAllFour ctx := by
  have hodd : Odd (63 : ℕ) := ⟨31, by norm_num⟩
  have h0 : slopeOrbit 63 4 0 = 4 := rfl
  have h1 : slopeOrbit 63 4 1 = 1 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 63 4 2 = 1 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num)
      (by norm_num)
  refine returnCtxAllFour_of_cycle_band_free ctx (c := 1) (by norm_num) ?_ ?_
  · rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 63 4 2 = slopeOrbit 63 4 1
    rw [h2, h1]
  · rw [hq, hK]
    intro j hj1 hj2
    interval_cases j
    rw [h1]
    exact canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num) (g := 6)
      (by norm_num) (by norm_num) (by norm_num)

/-! ### The aggregated band-2-free datum predicate -/

/-- **The fifteen band-2-free data**: the pin pairs of odd `q < 64` whose slope cycle never
reads band 2 — on these ALL FOUR Return fields are theorems. -/
def ReturnB2FreeDatum (ctx : ActualFailureContext) : Prop :=
  ((class1SlopeDatum ctx).q = 5 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 9 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 9 ∧ (class1SlopeDatum ctx).K₀ = 4)
  ∨ ((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 17 ∧ (class1SlopeDatum ctx).K₀ = 8)
  ∨ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3)
  ∨ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 10)
  ∨ ((class1SlopeDatum ctx).q = 33 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 33 ∧ (class1SlopeDatum ctx).K₀ = 16)
  ∨ ((class1SlopeDatum ctx).q = 41 ∧ (class1SlopeDatum ctx).K₀ = 20)
  ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 3)
  ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 4)

/-- **Every band-2-free datum closes all four Return fields.** -/
theorem returnCtxAllFour_of_b2FreeDatum (ctx : ActualFailureContext)
    (h : ReturnB2FreeDatum ctx) : ReturnCtxAllFour ctx := by
  rcases h with ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩
    | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩
    | ⟨hq, hK⟩ | ⟨hq, hK⟩
  · exact returnCtxAllFour_of_datum_5_2 ctx hq hK
  · exact returnCtxAllFour_of_datum_9_1 ctx hq hK
  · exact returnCtxAllFour_of_datum_9_4 ctx hq hK
  · exact returnCtxAllFour_of_datum_15_1 ctx hq hK
  · exact returnCtxAllFour_of_datum_15_2 ctx hq hK
  · exact returnCtxAllFour_of_datum_17_8 ctx hq hK
  · exact returnCtxAllFour_of_datum_21_1 ctx hq hK
  · exact returnCtxAllFour_of_datum_21_3 ctx hq hK
  · exact returnCtxAllFour_of_datum_21_10 ctx hq hK
  · exact returnCtxAllFour_of_datum_33_1 ctx hq hK
  · exact returnCtxAllFour_of_datum_33_16 ctx hq hK
  · exact returnCtxAllFour_of_datum_41_20 ctx hq hK
  · exact returnCtxAllFour_of_datum_63_1 ctx hq hK
  · exact returnCtxAllFour_of_datum_63_3 ctx hq hK
  · exact returnCtxAllFour_of_datum_63_4 ctx hq hK

/-! ## Part 5.  The `b₂ = 1` spaced-cycle criteria: `c`-spacing, singleton fibres, and the
small-carry digit regime -/

/-- Fibre members are positive (they sit in the window above `firstIndexAbove ≥ 1`). -/
theorem olcFibre_mem_pos (ctx : ActualFailureContext) {k : ℕ} (hk : k ∈ olcFibre ctx) :
    1 ≤ k := by
  have hw := olcFibre_mem_window ctx hk
  have hi := n24_firstIndexAbove_pos ctx
  omega

/-- The cycle representative of every fibre member reads band 2. -/
theorem olcFibre_cycleRep_band2 (ctx : ActualFailureContext) {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    {k : ℕ} (hk : k ∈ olcFibre ctx) :
    canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (cycleRep c k)) = 2 := by
  have hk1 : 1 ≤ k := olcFibre_mem_pos ctx hk
  have hband : canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
    rw [olcFibre_def] at hk
    exact class4Fibre_canonGap_eq ctx hk
  rw [← slopeOrbit_cycleRep hc hper hk1]
  exact hband

/-- **The `c`-spacing congruence**: with a UNIQUE band-2 cycle residue `j₀`, any two class-4
fibre members are congruent mod `c`. -/
theorem olcFibre_pair_mod_eq_of_band2_unique (ctx : ActualFailureContext) {c j₀ : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (huniq : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = j₀)
    {x z : ℕ} (hx : x ∈ olcFibre ctx) (hz : z ∈ olcFibre ctx) :
    x % c = z % c := by
  have hcx : cycleRep c x = j₀ :=
    huniq _ (cycleRep_pos hc x) (cycleRep_le hc x) (olcFibre_cycleRep_band2 ctx hc hper hx)
  have hcz : cycleRep c z = j₀ :=
    huniq _ (cycleRep_pos hc z) (cycleRep_le hc z) (olcFibre_cycleRep_band2 ctx hc hper hz)
  unfold cycleRep at hcx hcz
  by_cases h0x : x % c = 0 <;> by_cases h0z : z % c = 0
  · rw [h0x, h0z]
  · rw [if_pos h0x] at hcx
    rw [if_neg h0z] at hcz
    have hzc : z % c < c := Nat.mod_lt _ (by omega)
    omega
  · rw [if_neg h0x] at hcx
    rw [if_pos h0z] at hcz
    have hxc : x % c < c := Nat.mod_lt _ (by omega)
    omega
  · rw [if_neg h0x] at hcx
    rw [if_neg h0z] at hcz
    omega

/-- **The singleton criterion**: a unique band-2 residue with spacing `c ≥ W` confines the
WHOLE class-4 fibre to at most ONE member — two members would be `c ∣ z − x` apart inside a
window of width `W ≤ c`. -/
theorem olcFibre_card_le_one_of_band2_unique (ctx : ActualFailureContext) {c j₀ : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (huniq : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = j₀)
    (hWc : (supportShell ctx.shell.d ctx.shell.X).card ≤ c) :
    (olcFibre ctx).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx z hz
  rcases Nat.lt_trichotomy x z with hlt | heq | hgt
  · exfalso
    have hmod := olcFibre_pair_mod_eq_of_band2_unique ctx hc hper huniq hx hz
    have hdvd : c ∣ z - x := (Nat.modEq_iff_dvd' (le_of_lt hlt)).mp hmod
    have hle : c ≤ z - x := Nat.le_of_dvd (by omega) hdvd
    have hwid := olcFibre_pair_dist_lt_width ctx hx hz
    omega
  · exact heq
  · exfalso
    have hmod := olcFibre_pair_mod_eq_of_band2_unique ctx hc hper huniq hz hx
    have hdvd : c ∣ x - z := (Nat.modEq_iff_dvd' (le_of_lt hgt)).mp hmod
    have hle : c ≤ x - z := Nat.le_of_dvd (by omega) hdvd
    have hwid := olcFibre_pair_dist_lt_width ctx hz hx
    omega

/-- A fibre with at most one member has NO same-slice pair: `returnZero` holds outright (in
particular on the small-carry regime). -/
theorem returnZeroBody_of_fibre_card_le_one (ctx : ActualFailureContext)
    (h : (olcFibre ctx).card ≤ 1) : ReturnZeroBody ctx := by
  intro y hy x hx z hz hxz j hj1 hj2
  exfalso
  rw [olcSlice_def, Finset.mem_filter] at hx hz
  have heq := Finset.card_le_one.mp h x hx.1 z hz.1
  omega

/-- **Gates from the spaced cycle**: a unique band-2 residue with `W ≤ c` discharges the
gate-4 entry with `t = 1` (`1·b₂ = 1 ≤ r + 1`). -/
theorem returnGatesBody_of_band2_unique (ctx : ActualFailureContext) {c j₀ : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (huniq : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = j₀)
    (hWc : (supportShell ctx.shell.d ctx.shell.X).card ≤ c) :
    ReturnGatesBody ctx := by
  refine Or.inr (Or.inr (Or.inr ⟨c, 1, hc, hper, ?_, ?_⟩))
  · rw [Nat.one_mul]
    exact hWc
  · have hsub : (Finset.Icc 1 c).filter (fun j =>
        canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀ j) = 2) ⊆ {j₀} := by
      intro j hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj
      rw [Finset.mem_singleton]
      exact huniq j hj.1.1 hj.1.2 hj.2
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    rw [Nat.one_mul]
    omega

/-- `returnZero` from the spaced cycle (singleton fibre ⟹ no pairs). -/
theorem returnZeroBody_of_band2_unique (ctx : ActualFailureContext) {c j₀ : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (huniq : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = j₀)
    (hWc : (supportShell ctx.shell.d ctx.shell.X).card ≤ c) :
    ReturnZeroBody ctx :=
  returnZeroBody_of_fibre_card_le_one ctx
    (olcFibre_card_le_one_of_band2_unique ctx hc hper huniq hWc)

/-- The bundled spaced-cycle closure: gates + zero + the singleton count. -/
theorem returnGZC_of_band2_unique (ctx : ActualFailureContext) {c j₀ : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (huniq : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = j₀)
    (hWc : (supportShell ctx.shell.d ctx.shell.X).card ≤ c) :
    ReturnGatesBody ctx ∧ ReturnZeroBody ctx ∧ (olcFibre ctx).card ≤ 1 := by
  have hcard := olcFibre_card_le_one_of_band2_unique ctx hc hper huniq hWc
  exact ⟨returnGatesBody_of_band2_unique ctx hc hper huniq hWc,
    returnZeroBody_of_fibre_card_le_one ctx hcard, hcard⟩

/-- **The full M.2.1 spacing pin for same-slice pairs** (the small-carry digit regime
quantified): a same-key class-4 pair `x < z` carries the COMBINED spacing
`lcm(2^{carryVal2 x}, c) ∣ z − x` inside `z − x < W`, and forces the small-carry pin
`2^{carryVal2 x} < W`. -/
theorem returnSelfRef_slice_pair_spacing (ctx : ActualFailureContext) {c j₀ : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (huniq : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = j₀)
    {x z : ℕ} (hx : x ∈ olcFibre ctx) (hz : z ∈ olcFibre ctx)
    (hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z) (hlt : x < z) :
    Nat.lcm (2 ^ carryVal2 ctx x) c ∣ (z - x)
      ∧ z - x < (supportShell ctx.shell.d ctx.shell.X).card
      ∧ 2 ^ carryVal2 ctx x < (supportShell ctx.shell.d ctx.shell.X).card := by
  have h2 := returnSelfRefKey_gapDiv ctx hkey hlt
  have hmod := olcFibre_pair_mod_eq_of_band2_unique ctx hc hper huniq hx hz
  have hcd : c ∣ z - x := (Nat.modEq_iff_dvd' (le_of_lt hlt)).mp hmod
  exact ⟨Nat.lcm_dvd h2 hcd, olcFibre_pair_dist_lt_width ctx hx hz,
    returnSelfRef_sliceModulus_lt_width_of_pair ctx hx hz hkey hlt⟩

/-- **The lcm singleton criterion** (strictly stronger than `W ≤ c`): if every fibre member
has `W ≤ lcm(2^{carryVal2 k}, c)`, the combined spacing kills all same-slice pairs and
`returnZero` holds. -/
theorem returnZeroBody_of_band2_unique_lcm (ctx : ActualFailureContext) {c j₀ : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (huniq : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = j₀)
    (hbig : ∀ k ∈ olcFibre ctx,
      (supportShell ctx.shell.d ctx.shell.X).card ≤ Nat.lcm (2 ^ carryVal2 ctx k) c) :
    ReturnZeroBody ctx := by
  intro y hy x hx z hz hxz j hj1 hj2
  exfalso
  rw [olcSlice_def, Finset.mem_filter] at hx hz
  have hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z := by
    rw [hx.2, hz.2]
  obtain ⟨hdvd, hwid, _⟩ :=
    returnSelfRef_slice_pair_spacing ctx hc hper huniq hx.1 hz.1 hkey hxz
  have hle : Nat.lcm (2 ^ carryVal2 ctx x) c ≤ z - x := Nat.le_of_dvd (by omega) hdvd
  have hb := hbig x hx.1
  omega

/-- **The `returnMaxClean` SHRINKAGE**: on a singleton fibre the slice-max hypothesis is
automatic, so the field is equivalent to ONE bare digit fact per member,
`∀ k ∈ fibre₄, d(k+1) = 0`. -/
theorem returnMaxCleanBody_iff_of_fibre_card_le_one (ctx : ActualFailureContext)
    (h : (olcFibre ctx).card ≤ 1) :
    ReturnMaxCleanBody ctx ↔ ∀ k ∈ olcFibre ctx, ctx.d (k + 1) = 0 := by
  constructor
  · intro hmc k hk
    apply hmc k hk
    intro z hz _
    have heq := Finset.card_le_one.mp h z hz k hk
    omega
  · intro hmc k hk _
    exact hmc k hk

/-! ### The six spaced `b₂ = 1` pairs -/

/-- `(7, 3)`: cycle `[5, 3]` (period 2, bands `1, 2`) — unique band-2 residue `j₀ = 2`; on
`W ≤ 2` shells the fibre is a `2`-spaced singleton. -/
theorem returnGatesZeroCard_of_datum_7_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 7) (hK : (class1SlopeDatum ctx).K₀ = 3)
    (hW : (supportShell ctx.shell.d ctx.shell.X).card ≤ 2) :
    ReturnGatesBody ctx ∧ ReturnZeroBody ctx ∧ (olcFibre ctx).card ≤ 1 := by
  have hodd : Odd (7 : ℕ) := ⟨3, by norm_num⟩
  have h0 : slopeOrbit 7 3 0 = 3 := rfl
  have h1 : slopeOrbit 7 3 1 = 5 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 7 3 2 = 3 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h3 : slopeOrbit 7 3 3 = 5 :=
    orbit_step hodd h2 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 2)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 7 3 3 = slopeOrbit 7 3 1
    rw [h3, h1]
  have huniq : ∀ j, 1 ≤ j → j ≤ 2 →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = 2 := by
    rw [hq, hK]
    intro j hj1 hj2 hband
    interval_cases j
    · rw [h1] at hband
      exact absurd hband (canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num)
        (g := 1) (by norm_num) (by norm_num) (by norm_num))
    · rfl
  exact returnGZC_of_band2_unique ctx (by norm_num) hper huniq hW

/-- `(31, 15)`: cycle `[29, 27, 23, 15]` (period 4, bands `1, 1, 1, 2`) — unique band-2
residue `j₀ = 4`. -/
theorem returnGatesZeroCard_of_datum_31_15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 31) (hK : (class1SlopeDatum ctx).K₀ = 15)
    (hW : (supportShell ctx.shell.d ctx.shell.X).card ≤ 4) :
    ReturnGatesBody ctx ∧ ReturnZeroBody ctx ∧ (olcFibre ctx).card ≤ 1 := by
  have hodd : Odd (31 : ℕ) := ⟨15, by norm_num⟩
  have h0 : slopeOrbit 31 15 0 = 15 := rfl
  have h1 : slopeOrbit 31 15 1 = 29 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 31 15 2 = 27 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h3 : slopeOrbit 31 15 3 = 23 :=
    orbit_step hodd h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h4 : slopeOrbit 31 15 4 = 15 :=
    orbit_step hodd h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h5 : slopeOrbit 31 15 5 = 29 :=
    orbit_step hodd h4 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 4)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 31 15 5 = slopeOrbit 31 15 1
    rw [h5, h1]
  have huniq : ∀ j, 1 ≤ j → j ≤ 4 →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = 4 := by
    rw [hq, hK]
    intro j hj1 hj2 hband
    interval_cases j
    · rw [h1] at hband
      exact absurd hband (canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num)
        (g := 1) (by norm_num) (by norm_num) (by norm_num))
    · rw [h2] at hband
      exact absurd hband (canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num)
        (g := 1) (by norm_num) (by norm_num) (by norm_num))
    · rw [h3] at hband
      exact absurd hband (canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num)
        (g := 1) (by norm_num) (by norm_num) (by norm_num))
    · rfl
  exact returnGZC_of_band2_unique ctx (by norm_num) hper huniq hW

/-- `(51, 1)`: cycle `[13, 1]` (period 2, bands `2, 6`) — unique band-2 residue `j₀ = 1`. -/
theorem returnGatesZeroCard_of_datum_51_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 51) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hW : (supportShell ctx.shell.d ctx.shell.X).card ≤ 2) :
    ReturnGatesBody ctx ∧ ReturnZeroBody ctx ∧ (olcFibre ctx).card ≤ 1 := by
  have hodd : Odd (51 : ℕ) := ⟨25, by norm_num⟩
  have h0 : slopeOrbit 51 1 0 = 1 := rfl
  have h1 : slopeOrbit 51 1 1 = 13 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 51 1 2 = 1 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have h3 : slopeOrbit 51 1 3 = 13 :=
    orbit_step hodd h2 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num)
      (by norm_num)
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 2)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 51 1 3 = slopeOrbit 51 1 1
    rw [h3, h1]
  have huniq : ∀ j, 1 ≤ j → j ≤ 2 →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = 1 := by
    rw [hq, hK]
    intro j hj1 hj2 hband
    interval_cases j
    · rfl
    · rw [h2] at hband
      exact absurd hband (canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num)
        (g := 6) (by norm_num) (by norm_num) (by norm_num))
  exact returnGZC_of_band2_unique ctx (by norm_num) hper huniq hW

/-- `(51, 8)`: enters the cycle `[13, 1]` after one step — unique band-2 residue
`j₀ = 1`. -/
theorem returnGatesZeroCard_of_datum_51_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 51) (hK : (class1SlopeDatum ctx).K₀ = 8)
    (hW : (supportShell ctx.shell.d ctx.shell.X).card ≤ 2) :
    ReturnGatesBody ctx ∧ ReturnZeroBody ctx ∧ (olcFibre ctx).card ≤ 1 := by
  have hodd : Odd (51 : ℕ) := ⟨25, by norm_num⟩
  have h0 : slopeOrbit 51 8 0 = 8 := rfl
  have h1 : slopeOrbit 51 8 1 = 13 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 51 8 2 = 1 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have h3 : slopeOrbit 51 8 3 = 13 :=
    orbit_step hodd h2 (by norm_num) (by norm_num) (g := 6) (by norm_num) (by norm_num)
      (by norm_num)
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 2)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 51 8 3 = slopeOrbit 51 8 1
    rw [h3, h1]
  have huniq : ∀ j, 1 ≤ j → j ≤ 2 →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = 1 := by
    rw [hq, hK]
    intro j hj1 hj2 hband
    interval_cases j
    · rfl
    · rw [h2] at hband
      exact absurd hband (canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num)
        (g := 6) (by norm_num) (by norm_num) (by norm_num))
  exact returnGZC_of_band2_unique ctx (by norm_num) hper huniq hW

/-- `(63, 10)`: cycle `[17, 5]` (period 2, bands `2, 4`) — unique band-2 residue
`j₀ = 1`. -/
theorem returnGatesZeroCard_of_datum_63_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10)
    (hW : (supportShell ctx.shell.d ctx.shell.X).card ≤ 2) :
    ReturnGatesBody ctx ∧ ReturnZeroBody ctx ∧ (olcFibre ctx).card ≤ 1 := by
  have hodd : Odd (63 : ℕ) := ⟨31, by norm_num⟩
  have h0 : slopeOrbit 63 10 0 = 10 := rfl
  have h1 : slopeOrbit 63 10 1 = 17 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 3) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 63 10 2 = 5 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have h3 : slopeOrbit 63 10 3 = 17 :=
    orbit_step hodd h2 (by norm_num) (by norm_num) (g := 4) (by norm_num) (by norm_num)
      (by norm_num)
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 2)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 63 10 3 = slopeOrbit 63 10 1
    rw [h3, h1]
  have huniq : ∀ j, 1 ≤ j → j ≤ 2 →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = 1 := by
    rw [hq, hK]
    intro j hj1 hj2 hband
    interval_cases j
    · rfl
    · rw [h2] at hband
      exact absurd hband (canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num)
        (g := 4) (by norm_num) (by norm_num) (by norm_num))
  exact returnGZC_of_band2_unique ctx (by norm_num) hper huniq hW

/-- `(63, 31)`: cycle `[61, 59, 55, 47, 31]` (period 5, bands `1, 1, 1, 1, 2`) — unique
band-2 residue `j₀ = 5`. -/
theorem returnGatesZeroCard_of_datum_63_31 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 31)
    (hW : (supportShell ctx.shell.d ctx.shell.X).card ≤ 5) :
    ReturnGatesBody ctx ∧ ReturnZeroBody ctx ∧ (olcFibre ctx).card ≤ 1 := by
  have hodd : Odd (63 : ℕ) := ⟨31, by norm_num⟩
  have h0 : slopeOrbit 63 31 0 = 31 := rfl
  have h1 : slopeOrbit 63 31 1 = 61 :=
    orbit_step hodd h0 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : slopeOrbit 63 31 2 = 59 :=
    orbit_step hodd h1 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h3 : slopeOrbit 63 31 3 = 55 :=
    orbit_step hodd h2 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h4 : slopeOrbit 63 31 4 = 47 :=
    orbit_step hodd h3 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h5 : slopeOrbit 63 31 5 = 31 :=
    orbit_step hodd h4 (by norm_num) (by norm_num) (g := 1) (by norm_num) (by norm_num)
      (by norm_num)
  have h6 : slopeOrbit 63 31 6 = 61 :=
    orbit_step hodd h5 (by norm_num) (by norm_num) (g := 2) (by norm_num) (by norm_num)
      (by norm_num)
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 5)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    apply slopeOrbit_period_of_return
    show slopeOrbit 63 31 6 = slopeOrbit 63 31 1
    rw [h6, h1]
  have huniq : ∀ j, 1 ≤ j → j ≤ 5 →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = 5 := by
    rw [hq, hK]
    intro j hj1 hj2 hband
    interval_cases j
    · rw [h1] at hband
      exact absurd hband (canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num)
        (g := 1) (by norm_num) (by norm_num) (by norm_num))
    · rw [h2] at hband
      exact absurd hband (canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num)
        (g := 1) (by norm_num) (by norm_num) (by norm_num))
    · rw [h3] at hband
      exact absurd hband (canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num)
        (g := 1) (by norm_num) (by norm_num) (by norm_num))
    · rw [h4] at hband
      exact absurd hband (canonGap_ne_two_of_bounds hodd (by norm_num) (by norm_num)
        (g := 1) (by norm_num) (by norm_num) (by norm_num))
    · rfl
  exact returnGZC_of_band2_unique ctx (by norm_num) hper huniq hW

/-- **The six spaced `b₂ = 1` data**: the cheap unique-band-2 pairs on their `W ≤ c`
regimes (spacing exceeds window width — slices are singletons). -/
def ReturnB2OneSpacedDatum (ctx : ActualFailureContext) : Prop :=
  ((class1SlopeDatum ctx).q = 7 ∧ (class1SlopeDatum ctx).K₀ = 3
    ∧ (supportShell ctx.shell.d ctx.shell.X).card ≤ 2)
  ∨ ((class1SlopeDatum ctx).q = 31 ∧ (class1SlopeDatum ctx).K₀ = 15
    ∧ (supportShell ctx.shell.d ctx.shell.X).card ≤ 4)
  ∨ ((class1SlopeDatum ctx).q = 51 ∧ (class1SlopeDatum ctx).K₀ = 1
    ∧ (supportShell ctx.shell.d ctx.shell.X).card ≤ 2)
  ∨ ((class1SlopeDatum ctx).q = 51 ∧ (class1SlopeDatum ctx).K₀ = 8
    ∧ (supportShell ctx.shell.d ctx.shell.X).card ≤ 2)
  ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 10
    ∧ (supportShell ctx.shell.d ctx.shell.X).card ≤ 2)
  ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 31
    ∧ (supportShell ctx.shell.d ctx.shell.X).card ≤ 5)

/-- Every spaced `b₂ = 1` datum closes gates + zero (+ singleton count). -/
theorem returnGatesZeroCard_of_b2OneSpacedDatum (ctx : ActualFailureContext)
    (h : ReturnB2OneSpacedDatum ctx) :
    ReturnGatesBody ctx ∧ ReturnZeroBody ctx ∧ (olcFibre ctx).card ≤ 1 := by
  rcases h with ⟨hq, hK, hW⟩ | ⟨hq, hK, hW⟩ | ⟨hq, hK, hW⟩ | ⟨hq, hK, hW⟩
    | ⟨hq, hK, hW⟩ | ⟨hq, hK, hW⟩
  · exact returnGatesZeroCard_of_datum_7_3 ctx hq hK hW
  · exact returnGatesZeroCard_of_datum_31_15 ctx hq hK hW
  · exact returnGatesZeroCard_of_datum_51_1 ctx hq hK hW
  · exact returnGatesZeroCard_of_datum_51_8 ctx hq hK hW
  · exact returnGatesZeroCard_of_datum_63_10 ctx hq hK hW
  · exact returnGatesZeroCard_of_datum_63_31 ctx hq hK hW

/-! ## Part 6.  The successor residual and the additive bridge -/

/-- **The wave-5 Return successor residual** — `Erdos260DatumResidual` with the Return lane
STRICTLY SMALLER:

* `returnGates` demanded only off the fifteen band-2-free pairs, off the six spaced
  `b₂ = 1` regimes, AND only where the two-window numeric criterion FAILS
  (`2·(129L+64) ≤ 64·((W+r)·(L+B+1))`);
* `returnZero` (small-carry regime) demanded only off the band-2-free pairs and the spaced
  `b₂ = 1` regimes;
* `returnMaxClean` / `returnInterior` demanded only off the band-2-free pairs.

All other fields are carried verbatim from the wave-4 capstone. -/
structure ReturnSpanGateResidual where
  /-- Tower / class 2 (escape surface only) — verbatim wave-4 field. -/
  towerFixed : TowerFixedPointResidual
  /-- Run / class 5 (`r ≥ 1` only) — verbatim wave-4 field. -/
  runNumeric : RunNumericSettlementHyp
  /-- Return / class 4 count gates — demanded only off the closed data and regimes. -/
  returnGatesRes : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBody ctx
  /-- Return / class 4 digit Z (small-carry regime) — demanded only off the closed data. -/
  returnZeroRes : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ReturnZeroBody ctx
  /-- Return / class 4 clean step at slice maxima — demanded only off the band-2-free
  pairs. -/
  returnMaxCleanRes : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnMaxCleanBody ctx
  /-- Return / class 4 K.1 interior — demanded only off the band-2-free pairs. -/
  returnInteriorRes : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- Chernoff / class 0 (survivor shells) — verbatim wave-4 field. -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    Class0WindowCycleCheck ctx
  /-- Chernoff / class 0 (large moduli) — verbatim wave-4 field. -/
  class0Big : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
    Class0WindowCycleCheck ctx
  /-- CNL / class 1 — verbatim wave-4 field. -/
  class1Datum : Class1DatumResidual
  /-- DensePack / class 3 — verbatim wave-4 field. -/
  densePackDatum : DensePackDatumSplitResidual

namespace ReturnSpanGateResidual

/-- **The additive bridge into the wave-4 datum capstone**: every Return field is rebuilt by
per-ctx case split — band-2-free pairs through `returnCtxAllFour_of_b2FreeDatum`, spaced
`b₂ = 1` regimes through `returnGatesZeroCard_of_b2OneSpacedDatum`, the two-window numeric
regime through `returnGatesBody_of_reach_numeric`, the rest from the residual fields.
Nothing is re-proved. -/
def toDatum (R : ReturnSpanGateResidual) : Erdos260DatumResidual where
  towerFixed := R.towerFixed
  runNumeric := R.runNumeric
  returnGates := fun ctx => by
    by_cases hfree : ReturnB2FreeDatum ctx
    · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).1
    · by_cases hone : ReturnB2OneSpacedDatum ctx
      · exact (returnGatesZeroCard_of_b2OneSpacedDatum ctx hone).1
      · by_cases hnum : 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
            < 2 * (129 * shellLadderDepth ctx + 64)
        · exact returnGatesBody_of_reach_numeric ctx hnum
        · exact R.returnGatesRes ctx hfree hone (not_lt.mp hnum)
  returnZero := fun ctx hex => by
    by_cases hfree : ReturnB2FreeDatum ctx
    · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).2.1
    · by_cases hone : ReturnB2OneSpacedDatum ctx
      · exact (returnGatesZeroCard_of_b2OneSpacedDatum ctx hone).2.1
      · exact R.returnZeroRes ctx hfree hone hex
  returnMaxClean := fun ctx => by
    by_cases hfree : ReturnB2FreeDatum ctx
    · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).2.2.1
    · exact R.returnMaxCleanRes ctx hfree
  returnInterior := fun ctx => by
    by_cases hfree : ReturnB2FreeDatum ctx
    · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).2.2.2
    · exact R.returnInteriorRes ctx hfree
  class0Survivor := R.class0Survivor
  class0Big := R.class0Big
  class1Datum := R.class1Datum
  densePackDatum := R.densePackDatum

end ReturnSpanGateResidual

/-- **The wave-5 endpoint**: the Erdős 260 statement from the span-gate successor residual,
through the wave-4 datum capstone. -/
theorem erdos260_of_returnSpanGateResidual (R : ReturnSpanGateResidual) :
    Erdos260Statement :=
  erdos260_of_datumResidual R.toDatum

/-! ## Part 7.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the wave-5 Return span-gate closure. -/
def returnSpanGateClosureStatus : List String :=
  [ "SCOPE: the four Return-lane fields of Erdos260DatumResidual (returnGates 4-way " ++
      "disjunction, returnZero on the small-carry regime, returnMaxClean, " ++
      "returnInterior); everything here is additive - no existing file is edited.",
    "GATES QUANTIFIED (span gates -> numeric criteria, NEW): hitGap_span_le telescopes " ++
      "the PROVED reach ceiling hitGap <= L+B+1 (n24_hitGap_le_reach) into " ++
      "a(i+n) - a(i) <= n*(L+B+1) (n24_span_le_reach / n24_span_le_window); hence " ++
      "64*((W+r)*(L+B+1)) < 2*(129L+64) forces the two-window span gate " ++
      "(returnSpanGate_twoWindow_of_numeric, gates form returnGatesBody_of_reach_numeric, " ++
      "count form olcFibre_card_le_succ_r_of_reach_numeric) and " ++
      "64*((W-1)*(L+B+1)) < 129L+64 forces the in-window span gate " ++
      "(returnSpanGate_inWindow_of_numeric / returnGatesBody_of_inWindow_numeric / " ++
      "olcFibre_card_le_succ_r_of_inWindow_numeric), W = |supportShell|. Exact " ++
      "arithmetic: K.1 gate + in-window numeric => two-window numeric " ++
      "(returnSpan_twoWindow_numeric_of_gate_and_inWindow, via (W+r) = (W-1)+(r+1)).",
    "OFF-FIXED CYCLE-COUNT GATE (NEW): ceil_cover (W <= ceil(W/c)*c) turns the gate-4 " ++
      "entry into the explicit criterion ceil(W/c)*b2 <= r+1 " ++
      "(returnGatesBody_of_cycle_ceil); off (3,1) it is packaged with the proved strict " ++
      "deficiency b2 < c (returnGatesBody_offFixed_ceil, via " ++
      "datum_band2CycleCount_lt_of_offFixed). HONEST: for large W the criterion needs " ++
      "W <= c*(r+1)/b2 and is generally FALSE - hence the per-pair enumeration below.",
    "DATUM ENUMERATION COMPLETED to all odd q < 64 (NEW): returnSG_datum_low_window_pairs (q < 17: " ++
      "ten pairs (3,1) (5,2) (7,3) (9,1) (9,4) (11,5) (13,6) (15,1) (15,2) (15,7)) and " ++
      "datum_high_window_pairs (48 <= q < 64: nineteen pairs (49,3) (49,24) (51,1) (51,8) " ++
      "(51,25) (53,26) (55,2) (55,5) (55,27) (57,1) (57,9) (57,28) (59,29) (61,30) (63,1) " ++
      "(63,3) (63,4) (63,10) (63,31)) complete the existing mid/upper windows - 60 pin " ++
      "pairs total (ctx forms returnDatum_low/high_window_resolved).",
    "B2-FREE PAIRS CLOSED OUTRIGHT (the wave-5 lever, NEW): FIFTEEN pairs have " ++
      "band-2-free cycles - (5,2)c2 (9,1)c3 (9,4)c3 (15,1)c1 (15,2)c1 (17,8)c4 (21,1)c2 " ++
      "(21,3)c1 (21,10)c4 (33,1)c5 (33,16)c5 (41,20)c10 (63,1)c1 (63,3)c2 (63,4)c1; " ++
      "a band-2-free period EMPTIES the class-4 fibre, so ALL FOUR Return fields are " ++
      "theorems there (returnCtxAllFour_of_cycle_band_free, per-pair " ++
      "returnCtxAllFour_of_datum_*, aggregated by returnCtxAllFour_of_b2FreeDatum over " ++
      "ReturnB2FreeDatum). Gates close via the count gate with t = W, b2 = 0; zero/" ++
      "maxClean vacuously; interior via class4Interior_of_cycle_band_free.",
    "B2 = 1 RESIDUE SETS (seventeen pairs, recorded; period c, band-2 residues in " ++
      "braces): (3,1)c1{1} (7,3)c2{2} (13,6)c6{3} (15,7)c3{3} (31,15)c4{4} (33,5)c5{3} " ++
      "(39,1)c4{2} (39,6)c6{4} (45,7)c7{6} (45,22)c7{5} (51,1)c2{1} (51,8)c2{1} " ++
      "(55,2)c8{2} (57,1)c9{6} (57,28)c9{5} (63,10)c2{1} (63,31)c5{5}.",
    "B2 >= 2 RESIDUE SETS (twenty-eight pairs, recorded): (11,5)c5{3,5} (19,9)c9{5,8,9} " ++
      "(23,11)c7{4,7} (25,2)c10{1,6,7} (25,12)c10{4,5,9} (27,1)c9{2,6,8} (27,4)c9{2,6,8} " ++
      "(27,13)c9{4,6,9} (29,14)c14{4,8,13} (35,2)c5{3,4} (35,3)c7{1,2} (35,17)c7{6,7} " ++
      "(37,18)c18{7,12,15,16} (39,19)c8{6,8} (43,21)c7{5,7} (45,1)c5{1,3} (45,2)c5{1,3} " ++
      "(45,4)c5{1,3} (47,23)c14{5,6,9,14} (49,3)c11{5,6,10} (49,24)c11{5,6,10} " ++
      "(51,25)c6{5,6} (53,26)c26{5,8,9,11,20,21} (55,5)c5{1,4} (55,27)c12{5,7,8,12} " ++
      "(57,9)c9{1,4,5} (59,29)c29{5,8,9,16,19,20,22,29} (61,30)c30{5,11,13,17,18,25,29}.",
    "SPACED b2 = 1 DIGIT CRITERIA (the small-carry regime, NEW): a unique band-2 cycle " ++
      "residue makes the class-4 fibre c-spaced (olcFibre_pair_mod_eq_of_band2_unique); " ++
      "with W <= c the fibre is a SINGLETON (olcFibre_card_le_one_of_band2_unique), so " ++
      "returnGates closes (gate 4, t = 1: returnGatesBody_of_band2_unique), returnZero " ++
      "closes outright (returnZeroBody_of_fibre_card_le_one / _of_band2_unique), and " ++
      "returnMaxClean SHRINKS to one bare digit fact per member " ++
      "(returnMaxCleanBody_iff_of_fibre_card_le_one). Full M.2.1 spacing pin for " ++
      "same-slice pairs: lcm(2^carryVal2, c) | z-x AND z-x < W AND 2^carryVal2 < W " ++
      "(returnSelfRef_slice_pair_spacing); lcm singleton criterion " ++
      "returnZeroBody_of_band2_unique_lcm. Six pairs closed per-pair on W <= c regimes: " ++
      "(7,3) (31,15) (51,1) (51,8) (63,10) (63,31) (ReturnB2OneSpacedDatum, " ++
      "returnGatesZeroCard_of_b2OneSpacedDatum).",
    "NOT CLOSED (honest): the fixed pair (3,1) - b2 = c = 1, every residue band 2, the " ++
      "spacing and cycle-count gates are vacuous there (the known wave-3/4 hard point, " ++
      "left to the Q-parity lane); b2 >= 1 pairs OFF their W <= c regimes; q >= 64 " ++
      "moduli (no enumeration); the in-window/two-window numeric criteria on shells " ++
      "where they fail. These are exactly the guards of ReturnSpanGateResidual.",
    "SUCCESSOR RESIDUAL (additive bridge, NEW): ReturnSpanGateResidual demands " ++
      "returnGates only off the 15 b2-free pairs, off the 6 spaced regimes AND where the " ++
      "two-window numeric criterion fails; returnZero only off the closed data/regimes " ++
      "(small-carry hypothesis kept); returnMaxClean/returnInterior only off the b2-free " ++
      "pairs; all six non-Return fields verbatim. Bridge: toDatum (per-ctx case split, " ++
      "nothing re-proved), endpoint erdos260_of_returnSpanGateResidual : " ++
      "ReturnSpanGateResidual -> Erdos260Statement." ]

theorem returnSpanGateClosureStatus_nonempty : returnSpanGateClosureStatus ≠ [] := by
  simp [returnSpanGateClosureStatus]

/-! ## Part 8.  Axiom-cleanliness audit -/

#print axioms hitGap_span_le
#print axioms n24_span_le_reach
#print axioms n24_span_le_window
#print axioms returnSpanGate_twoWindow_of_numeric
#print axioms returnSpanGate_inWindow_of_numeric
#print axioms returnGatesBody_of_reach_numeric
#print axioms returnGatesBody_of_inWindow_numeric
#print axioms returnGatesBody_of_gapCeiling_numeric
#print axioms olcFibre_card_le_succ_r_of_reach_numeric
#print axioms olcFibre_card_le_succ_r_of_inWindow_numeric
#print axioms returnSpan_twoWindow_numeric_of_gate_and_inWindow
#print axioms ceil_cover
#print axioms returnGatesBody_of_cycle_ceil
#print axioms returnGatesBody_offFixed_ceil
#print axioms returnSG_datum_low_window_pairs
#print axioms datum_high_window_pairs
#print axioms returnDatum_low_window_resolved
#print axioms returnDatum_high_window_resolved
#print axioms returnCtxAllFour_of_cycle_band_free
#print axioms returnCtxAllFour_of_datum_5_2
#print axioms returnCtxAllFour_of_datum_9_1
#print axioms returnCtxAllFour_of_datum_9_4
#print axioms returnCtxAllFour_of_datum_15_1
#print axioms returnCtxAllFour_of_datum_15_2
#print axioms returnCtxAllFour_of_datum_17_8
#print axioms returnCtxAllFour_of_datum_21_1
#print axioms returnCtxAllFour_of_datum_21_3
#print axioms returnCtxAllFour_of_datum_21_10
#print axioms returnCtxAllFour_of_datum_33_1
#print axioms returnCtxAllFour_of_datum_33_16
#print axioms returnCtxAllFour_of_datum_41_20
#print axioms returnCtxAllFour_of_datum_63_1
#print axioms returnCtxAllFour_of_datum_63_3
#print axioms returnCtxAllFour_of_datum_63_4
#print axioms returnCtxAllFour_of_b2FreeDatum
#print axioms olcFibre_mem_pos
#print axioms olcFibre_cycleRep_band2
#print axioms olcFibre_pair_mod_eq_of_band2_unique
#print axioms olcFibre_card_le_one_of_band2_unique
#print axioms returnZeroBody_of_fibre_card_le_one
#print axioms returnGatesBody_of_band2_unique
#print axioms returnZeroBody_of_band2_unique
#print axioms returnGZC_of_band2_unique
#print axioms returnSelfRef_slice_pair_spacing
#print axioms returnZeroBody_of_band2_unique_lcm
#print axioms returnMaxCleanBody_iff_of_fibre_card_le_one
#print axioms returnGatesZeroCard_of_datum_7_3
#print axioms returnGatesZeroCard_of_datum_31_15
#print axioms returnGatesZeroCard_of_datum_51_1
#print axioms returnGatesZeroCard_of_datum_51_8
#print axioms returnGatesZeroCard_of_datum_63_10
#print axioms returnGatesZeroCard_of_datum_63_31
#print axioms returnGatesZeroCard_of_b2OneSpacedDatum
#print axioms ReturnSpanGateResidual.toDatum
#print axioms erdos260_of_returnSpanGateResidual
#print axioms returnSpanGateClosureStatus_nonempty

end

end Erdos260
