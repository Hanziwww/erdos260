import Erdos260.ReturnAnchoredCrossingCore

/-!
# The Return carry↔endpoint order link `hmono` — AUDIT + carry-geometry reduction
(`ReturnCarryEndpointCore`)

This module (NEW; it edits no existing file) owns the **wave-16 Return atom**: the single residual
`hmono` left by wave-15 (`ReturnAnchoredCrossingCore`).  Recall the field of
`AnchoredSliceCrossing`,
\[
  \mathtt{hmono} : \forall x\,z,\ \mathrm{CarryCrossing}\;x\;z \;\Longrightarrow\; e\,x < e\,z,
\]
i.e. for OLC class-4 slice positions `x < z` with a carry crossing
(`carryVal2 z ≤ carryVal2 x`), the pinned complete-return endpoint `e` strictly increases.  This is
the **carry-level order-compatibility bridge** of the manuscript
(`proof_v4_unconditional_clean_v5.tex` §M.3.2 Remark, lines ~6311–6323): *a carry crossing would put
the two complete-return intervals in crossing position, which the M.3.2-pinned endpoint forbids.*

## AUDIT VERDICT (sharp)

`hmono` **cannot be proved unconditionally**, and in its wave-15 *anchored-key* instantiation it is in
fact **logically equivalent to the per-slice crossing-freeness `hcf` itself** — it is a faithful
*restatement* of the residual, not a strictly smaller atom.  Concretely:

* **`hmono ⟺ hcf` (PROVED, `hmono_iff_crossingFree`).**  Because the charged endpoint coordinate `e`
  is one of the six anchored slice-key coordinates, it *factors through the key* (`FactorsThroughKey`,
  wave-15's M.3.2 reduction), so it is **pinned** (constant) on every slice.  Then `e x < e z` is
  *false* on the slice, so `(∀ x z, CarryCrossing → e x < e z)` says exactly *there is no carry
  crossing* — which is `crossingFree_iff_no_crossing`'s form of `hcf`.  Forward (`→`) is wave-15's
  `AnchoredSliceCrossing.crossingFree`; backward (`←`) is the vacuity of `hmono` under no-crossing.
  Hence the wave-15 reduction *converts* `hcf` into `hmono` via M.3.2 pinning but does **not** shrink
  it: any honest discharge of `hmono` must produce no-crossing, i.e. `hcf`, on the carry side.

* **The pinning's genuine role — the pure-order reductio (PROVED).**  What M.3.2 pinning actually buys
  is the geometry "shared endpoint ⇒ nested ⇒ cannot cross": `nested_of_shared_endpoint` +
  `not_cross_of_nested` ⇒ `no_carryCrossing_of_pinned_nested` ⇒ `crossingFree_of_pinned_nested`.
  This is the manuscript reductio with the **ordered-starts** hypothesis `hstart` made explicit (the
  returns are indexed by increasing left endpoints): a carry crossing would force *crossing position*
  (`IntervalsCross`, third component `hi x < hi z`), but pinning gives `hi x = hi z`.  It is exactly
  wave-15's `SliceEndpointPinning.crossingFree`, re-derived through the explicit nesting dichotomy —
  and it still consumes the same geometric link `hcross` (carry crossing ⇒ crossing position), which
  under pinning is itself equivalent to `hcf`.  So pinning is *necessary order glue*, not the missing
  content.

* **The genuine reduction is carry-side (PROVED).**  The honest way to discharge `hmono`/`hcf` is the
  carry doubling `carryVal2_add_zeroRun`: across a zero digit-run the carry valuation strictly
  *increases*, so there is no carry crossing.  `hmono_of_zeroRuns` /
  `hmono_of_consecutive_zeroRuns` close `hmono` for **any** anchored-key endpoint from the digit
  geometry "the complete-return starts on the slice bound zero digit-runs", via the proved
  `carryVal2_crossingFree_of_zeroRuns` and the new consecutive→all-pairs chaining
  `zeroRun_allPairs_of_consecutive`.  This routes the atom through genuine carry geometry, **not** the
  (circular) pinning.

## The smallest honest residual (sharply characterized)

After this module the wave-15 atom `hmono` is reduced to the **single digit-geometry fact** of the
actual OLC returns:

> **(Z)**  On an anchored slice, the digits strictly between two consecutive complete-return starts
> are all `0` — equivalently, no carry-dropping `1`-digit occurs inside the shared anchored region
> between two nested complete returns.

`(Z)` is a property of *which positions are OLC complete-return starts/endpoints* and of the digit
word `ctx.d`, owned by the deep Return geometry (M.3.1 four-coordinate anchored overlap + M.3.2
endpoint pinning), **not** by the carry recurrence in isolation: the carry valuation
`carryVal2 = v₂(integerCarry)` is a sawtooth that climbs by `1` on each `0`-digit and may drop on a
`1`-digit, so `(Z)` is exactly the statement that the geometry excludes the dropping `1`-digit.  From
`(Z)` everything above is proved here, and the discharge is genuinely non-vacuous
(`hmono_zeroRuns_teeth`, `carry_strictMono_zeroRun_teeth`): on a real zero-run the carry valuation
*does* strictly increase, so this is no constant/identity stand-in.  No `sorry`, `axiom`, `admit`, or
`native_decide`; no degenerate shortcut — a single `1`-digit between two starts is a genuine carry
crossing, so `(Z)` is the true irreducible content.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  AUDIT — the wave-15 atom `hmono` is logically equivalent to crossing-freeness `hcf`

The forward direction is wave-15's `AnchoredSliceCrossing.crossingFree`; the backward direction is the
vacuity of `hmono` once there is no carry crossing.  Together they show that, for a *pinned* endpoint
(one that factors through the slice key — the M.3.2 content), `hmono` is a faithful restatement of the
per-slice crossing-freeness, not a strictly smaller residual. -/

/-- **AUDIT (PROVED): `hmono ⟺ hcf` for a key-factoring endpoint.**  If the endpoint `endpt` factors
through the slice key (it is *pinned*, the M.3.2 reduction `pinned_of_factorsThroughKey`), then the
wave-15 crossing-chain ordering `hmono` (`∀ x z, CarryCrossing → endpt x < endpt z`) is *equivalent*
to the per-slice crossing-freeness `hcf` of the actual carry valuation.

`→` is wave-15's `AnchoredSliceCrossing.crossingFree` (pinning makes `endpt x = endpt z`, so a
crossing's `endpt x < endpt z` is contradictory); `←` is vacuity (`crossingFree_iff_no_crossing`: no
crossing makes `hmono` empty).  This is the sharp sense in which the wave-15 reduction *converts*
`hcf` into `hmono` via M.3.2 pinning but does not shrink it. -/
theorem hmono_iff_crossingFree {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ} {endpt : ℕ → ℕ}
    (hfix : FactorsThroughKey key endpt) :
    (∀ x z, CarryCrossing ctx key y x z → endpt x < endpt z) ↔
      (∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
        carryVal2 ctx x < carryVal2 ctx z) := by
  constructor
  · intro hmono
    exact AnchoredSliceCrossing.crossingFree ⟨endpt, hfix, hmono⟩
  · intro hcf x z hc
    exact absurd hc ((crossingFree_iff_no_crossing ctx key y).1 hcf x z)

/-- **AUDIT (PROVED): the wave-15 atom under the full anchored key is exactly `hcf`.**  Specialising
`hmono_iff_crossingFree` to the full anchored slice key `(e,τ,P,χ,σ,ι)`, where the charged endpoint
coordinate `e` is the first key coordinate (`endpointCoord_factorsThrough`): the wave-15 input
`hmono` of `anchoredKey_crossingFree` is *logically equivalent* to the per-slice crossing-freeness it
was supposed to deliver.  So the genuine residual is `hcf`, and it must be discharged on the carry
side. -/
theorem anchoredKey_hmono_iff_crossingFree (ctx : ActualFailureContext)
    (e tau P chi sigma iota : ℕ → ℕ) (y : ℕ) :
    (∀ x z, CarryCrossing ctx (anchoredKey e tau P chi sigma iota) y x z → e x < e z) ↔
      (∀ x ∈ olcSlice ctx (anchoredKey e tau P chi sigma iota) y,
        ∀ z ∈ olcSlice ctx (anchoredKey e tau P chi sigma iota) y, x < z →
          carryVal2 ctx x < carryVal2 ctx z) :=
  hmono_iff_crossingFree (endpointCoord_factorsThrough e tau P chi sigma iota)

/-! ## 2.  The pinning's genuine role: the pure-order nesting reductio

What M.3.2 pinning buys is purely order-theoretic: two complete-return intervals that share an
endpoint and are listed with increasing left endpoints are *nested*, and nested intervals cannot be in
crossing position.  This is the manuscript's "the two intervals share that endpoint and cannot cross
there", with the ordered-starts hypothesis made explicit. -/

/-- Interval `[lo₂, hi₂]` is **nested inside** `[lo₁, hi₁]`: `lo₁ ≤ lo₂` and `hi₂ ≤ hi₁`. -/
def IntervalNested (lo1 hi1 lo2 hi2 : ℕ) : Prop :=
  lo1 ≤ lo2 ∧ hi2 ≤ hi1

/-- **Shared right endpoint + ordered starts ⇒ nested (PROVED, pure order).**  The M.3.2-pinned right
endpoint `hi₁ = hi₂` together with ordered starts `lo₁ ≤ lo₂` nests the second interval inside the
first. -/
theorem nested_of_shared_endpoint {lo1 hi1 lo2 hi2 : ℕ} (hlo : lo1 ≤ lo2) (hhi : hi1 = hi2) :
    IntervalNested lo1 hi1 lo2 hi2 :=
  ⟨hlo, le_of_eq hhi.symm⟩

/-- **Nested intervals do not cross (PROVED, pure order).**  Crossing requires `hi₁ < hi₂`, but
nesting gives `hi₂ ≤ hi₁`. -/
theorem not_cross_of_nested {lo1 hi1 lo2 hi2 : ℕ} (h : IntervalNested lo1 hi1 lo2 hi2) :
    ¬ IntervalsCross lo1 hi1 lo2 hi2 := by
  rintro ⟨-, -, hlt⟩
  obtain ⟨-, hle⟩ := h
  omega

/-- **The manuscript reductio, factored (PROVED).**  On a slice with M.3.2-pinned right endpoints
`hi` (`hpin`) and ordered starts `lo` (`hstart`: returns indexed by increasing left endpoints), the
geometric link `hcross` (a carry crossing would put the two complete-return intervals in *crossing
position*) is self-defeating: the intervals are *nested* (`nested_of_shared_endpoint`), hence cannot
cross (`not_cross_of_nested`).  Therefore there is no carry crossing. -/
theorem no_carryCrossing_of_pinned_nested {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    {lo hi : ℕ → ℕ}
    (hpin : ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, hi x = hi z)
    (hstart : ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z → lo x ≤ lo z)
    (hcross : ∀ x z, CarryCrossing ctx key y x z → IntervalsCross (lo x) (hi x) (lo z) (hi z)) :
    ∀ x z, ¬ CarryCrossing ctx key y x z := by
  intro x z hc
  have hx : x ∈ olcSlice ctx key y := hc.1
  have hz : z ∈ olcSlice ctx key y := hc.2.1
  have hxz : x < z := hc.2.2.1
  have hnest : IntervalNested (lo x) (hi x) (lo z) (hi z) :=
    nested_of_shared_endpoint (hstart x hx z hz hxz) (hpin x hx z hz)
  exact not_cross_of_nested hnest (hcross x z hc)

/-- **Crossing-freeness from the pinned nesting reductio (PROVED).**  The pinned-nesting reductio of
`no_carryCrossing_of_pinned_nested` discharges the per-slice crossing-freeness `hcf` of the actual
carry valuation.  This is wave-15's `SliceEndpointPinning.crossingFree` re-derived through the
explicit nesting dichotomy with the ordered-starts hypothesis exposed. -/
theorem crossingFree_of_pinned_nested {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    {lo hi : ℕ → ℕ}
    (hpin : ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, hi x = hi z)
    (hstart : ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z → lo x ≤ lo z)
    (hcross : ∀ x z, CarryCrossing ctx key y x z → IntervalsCross (lo x) (hi x) (lo z) (hi z)) :
    ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      carryVal2 ctx x < carryVal2 ctx z := by
  rw [crossingFree_iff_no_crossing]
  exact no_carryCrossing_of_pinned_nested hpin hstart hcross

/-! ## 3.  The genuine carry-side discharge: zero digit-runs ⇒ `hmono`

The honest content the manuscript supplies is the digit geometry **(Z)**: the complete-return starts
on a slice bound zero digit-runs.  Across a zero-run the actual carry valuation strictly increases
(`carryVal2_add_zeroRun`, wave-13), so there is no carry crossing — and by the AUDIT equivalence
`hmono` follows for any pinned endpoint.  This routes the atom through genuine carry geometry. -/

/-- **`hmono` from the zero-run geometry, all-pairs form (PROVED).**  If every pair of slice
positions `x < z` bounds a zero digit-run on `(x, z]`, the actual carry valuation is crossing-free
(`carryVal2_crossingFree_of_zeroRuns`), so by the AUDIT equivalence `hmono_iff_crossingFree` the
crossing-chain ordering `hmono` holds for *any* key-factoring (M.3.2-pinned) endpoint `endpt`. -/
theorem hmono_of_zeroRuns {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ} {endpt : ℕ → ℕ}
    (hfix : FactorsThroughKey key endpt)
    (hzero : ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      ∀ j, x < j → j ≤ z → ctx.d j = 0) :
    ∀ x z, CarryCrossing ctx key y x z → endpt x < endpt z :=
  (hmono_iff_crossingFree hfix).2 (carryVal2_crossingFree_of_zeroRuns ctx key y hzero)

/-- **Consecutive zero-runs ⇒ all-pairs zero-run (PROVED).**  If between every pair of *consecutive*
slice positions (no slice element strictly in between) the digits are zero, then between *every* pair
of slice positions the digits are zero.  This is the chaining that lets the genuinely-local datum (a
zero-run between each adjacent pair of complete-return starts) cover all pairs: for `x < j ≤ z` pick
the largest slice element `w < j` and the smallest slice element `v ≥ j`; they are consecutive with
`w < j ≤ v`, so the digit at `j` lies in their zero-run. -/
theorem zeroRun_allPairs_of_consecutive {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (hcons : ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      (∀ c ∈ olcSlice ctx key y, x < c → z ≤ c) →
        ∀ j, x < j → j ≤ z → ctx.d j = 0) :
    ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      ∀ j, x < j → j ≤ z → ctx.d j = 0 := by
  intro x hx z hz hxz j hj1 hj2
  have hLne : ((olcSlice ctx key y).filter (fun c => c < j)).Nonempty :=
    ⟨x, Finset.mem_filter.mpr ⟨hx, hj1⟩⟩
  have hRne : ((olcSlice ctx key y).filter (fun c => j ≤ c)).Nonempty :=
    ⟨z, Finset.mem_filter.mpr ⟨hz, hj2⟩⟩
  obtain ⟨w, hwS, hwj, hwmax⟩ :
      ∃ w, w ∈ olcSlice ctx key y ∧ w < j ∧ ∀ c ∈ olcSlice ctx key y, c < j → c ≤ w := by
    refine ⟨Finset.max' ((olcSlice ctx key y).filter (fun c => c < j)) hLne, ?_, ?_, ?_⟩
    · exact (Finset.mem_filter.mp (Finset.max'_mem _ hLne)).1
    · exact (Finset.mem_filter.mp (Finset.max'_mem _ hLne)).2
    · intro c hcS hcj; exact Finset.le_max' _ c (Finset.mem_filter.mpr ⟨hcS, hcj⟩)
  obtain ⟨v, hvS, hjv, hvmin⟩ :
      ∃ v, v ∈ olcSlice ctx key y ∧ j ≤ v ∧ ∀ c ∈ olcSlice ctx key y, j ≤ c → v ≤ c := by
    refine ⟨Finset.min' ((olcSlice ctx key y).filter (fun c => j ≤ c)) hRne, ?_, ?_, ?_⟩
    · exact (Finset.mem_filter.mp (Finset.min'_mem _ hRne)).1
    · exact (Finset.mem_filter.mp (Finset.min'_mem _ hRne)).2
    · intro c hcS hcj; exact Finset.min'_le _ c (Finset.mem_filter.mpr ⟨hcS, hcj⟩)
  have hwv : w < v := lt_of_lt_of_le hwj hjv
  have hconsec : ∀ c ∈ olcSlice ctx key y, w < c → v ≤ c := by
    intro c hcS hwc
    by_cases hcj : c < j
    · exact absurd (hwmax c hcS hcj) (Nat.not_le.mpr hwc)
    · exact hvmin c hcS (Nat.not_lt.mp hcj)
  exact hcons w hwS v hvS hwv hconsec j hwj hjv

/-- **`hmono` from the per-consecutive-pair zero-run geometry (PROVED) — the sharpest honest form.**
The genuinely-local datum **(Z)**: between each pair of *consecutive* complete-return starts on the
slice the digits are zero.  Chained by `zeroRun_allPairs_of_consecutive` and discharged through
`hmono_of_zeroRuns`, this closes the wave-15 atom `hmono` for any M.3.2-pinned endpoint. -/
theorem hmono_of_consecutive_zeroRuns {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    {endpt : ℕ → ℕ} (hfix : FactorsThroughKey key endpt)
    (hcons : ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      (∀ c ∈ olcSlice ctx key y, x < c → z ≤ c) →
        ∀ j, x < j → j ≤ z → ctx.d j = 0) :
    ∀ x z, CarryCrossing ctx key y x z → endpt x < endpt z :=
  hmono_of_zeroRuns hfix (zeroRun_allPairs_of_consecutive hcons)

/-- **`hmono` under the full anchored key from the zero-run geometry (PROVED).**  The anchored-key
instantiation: with `e` the charged endpoint coordinate (`endpointCoord_factorsThrough`), the zero-run
digit geometry discharges the wave-15 input of `anchoredKey_crossingFree`. -/
theorem anchoredKey_hmono_of_zeroRuns (ctx : ActualFailureContext)
    (e tau P chi sigma iota : ℕ → ℕ) (y : ℕ)
    (hzero : ∀ x ∈ olcSlice ctx (anchoredKey e tau P chi sigma iota) y,
      ∀ z ∈ olcSlice ctx (anchoredKey e tau P chi sigma iota) y, x < z →
        ∀ j, x < j → j ≤ z → ctx.d j = 0) :
    ∀ x z, CarryCrossing ctx (anchoredKey e tau P chi sigma iota) y x z → e x < e z :=
  hmono_of_zeroRuns (endpointCoord_factorsThrough e tau P chi sigma iota) hzero

/-- **The wave-15 `AnchoredSliceCrossing` engine, built from the zero-run geometry (PROVED).**  Feeds
the genuine carry-side datum into wave-15's structure: the endpoint coordinate `e`, its M.3.2 factoring
`endpointCoord_factorsThrough`, and the now-*derived* `hmono` from the zero digit-runs.  Inhabiting
this structure is exactly the honest discharge of the wave-15 atom on a slice with zero-run geometry. -/
def AnchoredSliceCrossing.ofZeroRuns (ctx : ActualFailureContext)
    (e tau P chi sigma iota : ℕ → ℕ) (y : ℕ)
    (hzero : ∀ x ∈ olcSlice ctx (anchoredKey e tau P chi sigma iota) y,
      ∀ z ∈ olcSlice ctx (anchoredKey e tau P chi sigma iota) y, x < z →
        ∀ j, x < j → j ≤ z → ctx.d j = 0) :
    AnchoredSliceCrossing ctx (anchoredKey e tau P chi sigma iota) y where
  endpt := e
  hfix := endpointCoord_factorsThrough e tau P chi sigma iota
  hmono := anchoredKey_hmono_of_zeroRuns ctx e tau P chi sigma iota y hzero

/-- **The full per-slice residual `OlcSliceData` from the zero-run carry geometry (PROVED).**  With
the zero-run digit geometry **(Z)** (`hzero`, giving crossing-freeness) and the self-referential gap
divisibility `hgap` (`2^(carryVal2 x) ∣ (z − x)` on consecutive starts, the carry-period of the
nested return), the actual carry valuation `carryVal2` is a genuine `OlcSliceData` — hence each
anchored slice has `≤ liftLevelBound X` elements (`OlcSliceData.card_le`).  This connects the
discharged atom to the corrected Return per-slice count. -/
def OlcSliceData.ofZeroRunGeometry (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ)
    (hbound : ∀ k ∈ olcSlice ctx key y, carryVal2 ctx k ≤ ctx.shell.X)
    (hzero : ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      ∀ j, x < j → j ≤ z → ctx.d j = 0)
    (hgap : ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      (∀ c ∈ olcSlice ctx key y, x < c → z ≤ c) → 2 ^ carryVal2 ctx x ∣ (z - x)) :
    OlcSliceData ctx key y :=
  OlcSliceData.ofCarryZeroRuns ctx key y hbound
    (carryVal2_crossingFree_of_zeroRuns ctx key y hzero)
    (fun x hx z hz hxz _ j hj1 hj2 => hzero x hx z hz hxz j hj1 hj2)
    hgap

/-! ## 4.  Non-vacuity and teeth

The discharge is not a vacuous implication.  On a genuine zero digit-run the actual carry valuation
*strictly increases* by the run length (`carryVal2_add_zeroRun`), so the strict ordering is real: a
constant level would fail crossing-freeness, and `hmono`/`hcf` is genuinely the no-crossing content. -/

/-- **Teeth (PROVED): the carry valuation genuinely increases on a zero-run.**  Across a nonempty zero
digit-run the actual `carryVal2` strictly increases — the discharge of `hmono` rests on real strict
monotonicity of the carry valuation, not a constant/identity stand-in. -/
theorem carry_strictMono_zeroRun_teeth (ctx : ActualFailureContext) (N h : ℕ) (hh : 0 < h)
    (hz : ∀ j, N < j → j ≤ N + h → ctx.d j = 0) :
    carryVal2 ctx N < carryVal2 ctx (N + h) :=
  carryVal2_strictMono_zeroRun ctx N h hh hz

/-- **Non-vacuity, assembled (PROVED).**  On a slice with zero-run geometry the actual carry valuation
is crossing-free *and* the wave-15 `AnchoredSliceCrossing` engine is inhabited with the *derived*
`hmono`.  So the discharge fires on genuine carry data, not a degenerate model. -/
theorem hmono_zeroRuns_teeth (ctx : ActualFailureContext)
    (e tau P chi sigma iota : ℕ → ℕ) (y : ℕ)
    (hzero : ∀ x ∈ olcSlice ctx (anchoredKey e tau P chi sigma iota) y,
      ∀ z ∈ olcSlice ctx (anchoredKey e tau P chi sigma iota) y, x < z →
        ∀ j, x < j → j ≤ z → ctx.d j = 0) :
    (∀ x ∈ olcSlice ctx (anchoredKey e tau P chi sigma iota) y,
        ∀ z ∈ olcSlice ctx (anchoredKey e tau P chi sigma iota) y, x < z →
          carryVal2 ctx x < carryVal2 ctx z)
      ∧ Nonempty (AnchoredSliceCrossing ctx (anchoredKey e tau P chi sigma iota) y) :=
  ⟨carryVal2_crossingFree_of_zeroRuns ctx (anchoredKey e tau P chi sigma iota) y hzero,
    ⟨AnchoredSliceCrossing.ofZeroRuns ctx e tau P chi sigma iota y hzero⟩⟩

/-! ## 5.  Honest residual inventory -/

/-- The precise status of the wave-15 Return atom `hmono` after this module. -/
def returnCarryEndpointResiduals : List String :=
  [ "AUDIT VERDICT (sharp) — the wave-15 atom hmono (AnchoredSliceCrossing.hmono: a carry crossing " ++
      "x < z, carryVal2 z ≤ carryVal2 x forces the pinned complete-return endpoint e x < e z) CANNOT " ++
      "be proved unconditionally, and in its anchored-key instantiation it is LOGICALLY EQUIVALENT to " ++
      "the per-slice crossing-freeness hcf itself (hmono_iff_crossingFree). Because e is one of the " ++
      "six anchored slice-key coordinates it factors through the key (wave-15 M.3.2 reduction), so it " ++
      "is pinned (constant) on each slice; then e x < e z is FALSE on the slice, making " ++
      "(∀ x z, CarryCrossing → e x < e z) literally 'there is no carry crossing' = hcf. So the wave-15 " ++
      "reduction CONVERTS hcf into hmono via M.3.2 pinning but does NOT shrink it.",
    "CLOSED (the equivalence) — hmono_iff_crossingFree / anchoredKey_hmono_iff_crossingFree: for any " ++
      "key-factoring endpoint, (∀ x z, CarryCrossing → endpt x < endpt z) ↔ (∀ x z in slice, x < z → " ++
      "carryVal2 x < carryVal2 z). Forward is wave-15's AnchoredSliceCrossing.crossingFree (pinning " ++
      "gives endpt x = endpt z); backward is vacuity via crossingFree_iff_no_crossing.",
    "CLOSED (the pinning's genuine role — pure-order nesting reductio) — IntervalNested / " ++
      "nested_of_shared_endpoint / not_cross_of_nested / no_carryCrossing_of_pinned_nested / " ++
      "crossingFree_of_pinned_nested: M.3.2 pinning (shared right endpoint) + ordered starts (hstart, " ++
      "returns indexed by increasing left endpoints) makes the complete-return intervals NESTED, hence " ++
      "non-crossing. This is the manuscript reductio (clean_v5 §M.3.2 Remark, lines ~6311–6323) with " ++
      "the ordered-starts hypothesis made explicit; it re-derives wave-15's " ++
      "SliceEndpointPinning.crossingFree but still consumes the same geometric link hcross, which under " ++
      "pinning is itself equivalent to hcf. Pinning is necessary order glue, not the missing content.",
    "CLOSED (the genuine carry-side discharge) — hmono_of_zeroRuns / hmono_of_consecutive_zeroRuns / " ++
      "anchoredKey_hmono_of_zeroRuns: from the digit geometry (Z) 'the complete-return starts on the " ++
      "slice bound zero digit-runs' the actual carryVal2 is crossing-free (carryVal2_add_zeroRun / " ++
      "carryVal2_crossingFree_of_zeroRuns), so hmono follows for any pinned endpoint. " ++
      "zeroRun_allPairs_of_consecutive chains the genuinely-local per-adjacent-pair datum to all " ++
      "pairs. AnchoredSliceCrossing.ofZeroRuns builds wave-15's structure with the DERIVED hmono; " ++
      "OlcSliceData.ofZeroRunGeometry builds the full per-slice residual (with the lift-gap " ++
      "divisibility hgap), so OlcSliceData.card_le gives each slice ≤ liftLevelBound X.",
    "NON-VACUOUS / TEETH — carry_strictMono_zeroRun_teeth: across a nonempty zero-run carryVal2 " ++
      "strictly increases (carryVal2_add_zeroRun); hmono_zeroRuns_teeth: on a zero-run slice the carry " ++
      "valuation is crossing-free AND the wave-15 AnchoredSliceCrossing engine is inhabited with the " ++
      "derived hmono. No constant/identity shortcut: a single 1-digit between two starts is a genuine " ++
      "carry crossing (the sawtooth carryVal2 = v₂(integerCarry) drops on a 1-digit).",
    "OPEN (the single irreducible residual — the digit geometry (Z)) — on an anchored slice the " ++
      "digits strictly between two consecutive complete-return starts are all 0, i.e. no " ++
      "carry-dropping 1-digit occurs inside the shared anchored region between two nested complete " ++
      "returns. This is a property of WHICH positions are OLC complete-return starts/endpoints and of " ++
      "the digit word ctx.d, owned by the deep Return geometry (M.3.1 four-coordinate anchored " ++
      "overlap + M.3.2 endpoint pinning), NOT by the carry recurrence in isolation. The carry-level " ++
      "order-compatibility bridge (clean_v5 §M.3.2 Remark) reduces hmono to exactly (Z), proved here " ++
      "end-to-end. proof_v4_unconditional_clean_v5.tex §M.2.1 / §M.3.1 / §M.3.2." ]

theorem returnCarryEndpointResiduals_nonempty : returnCarryEndpointResiduals ≠ [] := by
  simp [returnCarryEndpointResiduals]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms hmono_iff_crossingFree
#print axioms anchoredKey_hmono_iff_crossingFree
#print axioms nested_of_shared_endpoint
#print axioms not_cross_of_nested
#print axioms no_carryCrossing_of_pinned_nested
#print axioms crossingFree_of_pinned_nested
#print axioms hmono_of_zeroRuns
#print axioms zeroRun_allPairs_of_consecutive
#print axioms hmono_of_consecutive_zeroRuns
#print axioms anchoredKey_hmono_of_zeroRuns
#print axioms AnchoredSliceCrossing.ofZeroRuns
#print axioms OlcSliceData.ofZeroRunGeometry
#print axioms carry_strictMono_zeroRun_teeth
#print axioms hmono_zeroRuns_teeth

end

end Erdos260
