import Erdos260.ReturnCarryNestingCore
import Erdos260.ReturnLiftChainProof

/-!
# The M.2.1 per-slice OLC endpoint multiplicity from the actual carry valuation
(`ReturnM21SliceCore`)

This module (NEW; it edits no existing file) owns the **genuine analytic input** behind the per-slice
M.2.1 ordinary-local-long (OLC) endpoint-nesting count: for a fixed slice `(e, τ, P)` the nested OLC
return endpoints have lift heights `δ` reducing to a common 2-adic centre,
\[
  δ_{i+1} ≡ δ_i \pmod{2^{δ_i}} \quad\Longrightarrow\quad δ_{i+1} ≥ δ_i + 2^{δ_i},
\]
so at most `O(log* L)` of them — **unless they cross**, which Fine–Wilf (K.2.3 / K.2.5) excludes.

Wave-11 isolated the per-slice residual `OlcSliceData` (`ReturnCarryNestingCore`) — a per-slice level
map with the shell-scale bound `hbound`, **crossing-freeness** `hcf`, and the consecutive
self-referential lift separation `hcons` — and proved each slice has `≤ liftLevelBound X` elements
(`OlcSliceData.card_le`, via wave-10's `card_le_liftLevelBound_of_crossingFree`), hence the corrected
global shape `|routedFibre 4| ≤ #sliceKeys · liftLevelBound X` (`routedFibre4_card_le_of_slices`).

But wave-11 left `OlcSliceData` with **no constructor** beyond the empty slice, and nothing connected
its abstract `level` to the **actual carry valuation** `carryVal2 = v₂(integerCarry)`.  Separately,
`ReturnLiftChainProof` proved the manuscript "hence" step `lift_congruence_imp_separation`
(`2^a ∣ (b-a) ⇒ a + 2^a ≤ b`) but fed it into the *injection* path (`ReturnInjectionCore`,
all-pairs `hchain` + `hinj`), **not** the per-slice crossing-free path, and also used an abstract
`level`.

This module closes that gap.

## What is genuinely PROVED here (new content)

* `card_le_liftLevelBound_of_crossingFree_congruence` / `…_modCongruence` — **the per-slice count
  from the literal manuscript congruence primitive**: crossing-freeness `hcf` plus the consecutive
  self-referential lift *congruence* `2^(level x) ∣ (level z − level x)` (resp.
  `level z % 2^(level x) = level x % 2^(level x)`) on the actual fibre.  The separated `hcons` of
  `card_le_liftLevelBound_of_crossingFree` is *derived* via `lift_congruence_imp_separation`.  This
  feeds wave-10's count, so `|F| ≤ liftLevelBound L`.
* `OlcSliceData.ofLiftCongruence` / `…ofLiftModCongruence` — **the missing `OlcSliceData`
  constructors**: build the per-slice residual from crossing-freeness + the consecutive lift
  congruence (the genuine manuscript hypothesis), deriving `hcons`.
* `carryVal2_dvd_sub_of_zeroRun` — **the carry-side realisation of the congruence primitive**: across
  a zero digit-run whose length is a multiple of `2^δ` (the self-referential recurrence period), the
  actual carry valuation `δ = carryVal2` satisfies `2^(carryVal2 N) ∣ (carryVal2 (N+h) − carryVal2 N)`
  (built on `carryVal2_add_zeroRun`).  So `carryVal2` is the genuine level map, not an abstract one.
* `carryVal2_le_log` — the level map is logarithmic in the carry magnitude:
  `carryVal2 N ≤ log₂((integerCarry)⁺)` (a `2^v ∣ R` argument), the level-map analogue of the
  `carry_zeroRun_length_le` `O(log X)` bound that `liftLevelBound` compresses to `O(log* X)`.
* `OlcSliceData.ofCarryVal2` / `OlcSliceData.ofCarryZeroRuns` — **the per-slice residual with
  `level = carryVal2 ctx`**: from crossing-freeness (Fine–Wilf) + the congruence on the carry
  valuations (resp. from per-consecutive-pair zero-runs of `2^δ`-multiple length).  The intended
  carry-side level map, never faked.
* `carryVal2_olcSlice_ingredients_on_zeroRun` — on a genuine zero-run of `2^δ`-multiple length the
  actual `carryVal2` provides **both** the crossing-free strict increase (`carryVal2_strictMono_zeroRun`)
  and the lift congruence — the two non-empty-slice `OlcSliceData` ingredients, non-degenerate.
* `routedFibre4_card_le_of_carryVal2_congruence` — **the corrected global bound from the carry-side
  per-slice family**: `|routedFibre 4| ≤ #sliceKeys · liftLevelBound X` with the level map pinned to
  the actual carry valuation `carryVal2`.
* `crossingFree_congruence_count_nonvacuous` — **non-vacuity**: the per-slice crossing-free +
  congruence count fires on the genuine non-empty tower chain `shellLevels L`
  (via `shellLevels_isLiftCongruenceChain`), recovering `|shellLevels L| ≤ liftLevelBound L`.

## The smallest honest residual (sharply characterized)

After this module the per-slice M.2.1 count is reduced, for the ACTUAL carry valuation, to the two
**geometric** facts of the actual OLC return endpoints in each slice — not derivable from the carry
recurrence alone, owned by the deep Return/Fine–Wilf geometry:

1. **Crossing-freeness** `hcf`: along each slice, position-increasing endpoints have strictly
   increasing `carryVal2` — the Fine–Wilf K.2.3/K.2.5 crossing exclusion
   (`fineWilf_distinct_primitive_excluded`): a crossing would expose two distinct primitive
   semiperiodic arm descriptions on a long overlap, forbidden.
2. **The self-referential congruence** `hcong`: consecutive slice endpoints `x < z` obey
   `2^(carryVal2 x) ∣ (carryVal2 z − carryVal2 x)` — equivalently (via `carryVal2_add_zeroRun`) the
   inter-endpoint gap `z − x` is a positive multiple of `2^(carryVal2 x)`, the carry-period structure
   of the nested returns.

Both are properties of *which positions are OLC return endpoints* (the classifier↔endpoint geometric
link), not of the carry recurrence in isolation.  No `sorry`, `axiom`, `admit`, or `native_decide`;
no degenerate shortcut — a constant level fails `hcf`, the identity fails `hcong`.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The per-slice count from the literal lift-congruence primitive (generic, PROVED)

Wave-10's `card_le_liftLevelBound_of_crossingFree` consumes the *separated* consecutive bound
`hcons : level x + 2^(level x) ≤ level z`.  Here we feed it the genuine manuscript primitive — the
self-referential lift *congruence* on consecutive pairs — and *derive* the separation through the
proved `lift_congruence_imp_separation` (`ReturnLiftChainProof`). -/

/-- **The per-slice M.2.1 count from the lift congruence (PROVED).**

For a finite `F ⊆ ℕ` with a level map `level` that is (a) bounded by `L`, (b) **crossing-free**
(`x < y → level x < level y`, the Fine–Wilf crossing exclusion), and (c) obeys the **consecutive
self-referential lift congruence** `2^(level x) ∣ (level y − level x)` on position-successor pairs
(the manuscript `δ_{i+1} ≡ δ_i (mod 2^{δ_i})`), the count is `≤ liftLevelBound L = O(log* L)`.  The
separated `hcons` is derived by `lift_congruence_imp_separation`. -/
theorem card_le_liftLevelBound_of_crossingFree_congruence {F : Finset ℕ} {L : ℕ} {level : ℕ → ℕ}
    (hbound : ∀ k ∈ F, level k ≤ L)
    (hcf : ∀ x ∈ F, ∀ y ∈ F, x < y → level x < level y)
    (hcong : ∀ x ∈ F, ∀ y ∈ F, x < y →
      (∀ c ∈ F, x < c → y ≤ c) → 2 ^ level x ∣ (level y - level x)) :
    F.card ≤ liftLevelBound L :=
  card_le_liftLevelBound_of_crossingFree hbound hcf
    (fun x hx y hy hxy hsucc =>
      lift_congruence_imp_separation (hcf x hx y hy hxy) (hcong x hx y hy hxy hsucc))

/-- **The per-slice M.2.1 count from the lift congruence, literal `[MOD]` form (PROVED).**

As above with the congruence phrased as `level y % 2^(level x) = level x % 2^(level x)` — i.e.
`δ_{i+1} ≡ δ_i (mod 2^{δ_i})` with the smaller height `δ_i = level x`. -/
theorem card_le_liftLevelBound_of_crossingFree_modCongruence {F : Finset ℕ} {L : ℕ} {level : ℕ → ℕ}
    (hbound : ∀ k ∈ F, level k ≤ L)
    (hcf : ∀ x ∈ F, ∀ y ∈ F, x < y → level x < level y)
    (hcong : ∀ x ∈ F, ∀ y ∈ F, x < y →
      (∀ c ∈ F, x < c → y ≤ c) → level y % 2 ^ level x = level x % 2 ^ level x) :
    F.card ≤ liftLevelBound L :=
  card_le_liftLevelBound_of_crossingFree hbound hcf
    (fun x hx y hy hxy hsucc =>
      lift_modCongruence_imp_separation (hcf x hx y hy hxy) (hcong x hx y hy hxy hsucc))

/-! ## 2.  The missing `OlcSliceData` constructors from the lift-congruence primitive

The per-slice residual `OlcSliceData` (`ReturnCarryNestingCore`) had only `ofEmpty`.  These are the
genuine non-empty-slice constructors: from crossing-freeness + the consecutive lift *congruence* (the
manuscript hypothesis), deriving the separated `hcons`. -/

/-- **`OlcSliceData` from the lift-congruence primitive.**  Builds the per-`(e,τ,P)`-slice residual
from the level map, the shell-scale bound `hbound`, crossing-freeness `hcf` (Fine–Wilf K.2.3/K.2.5),
and the **consecutive self-referential lift congruence** `2^(level x) ∣ (level z − level x)` (`hcong`,
the manuscript `δ_{i+1} ≡ δ_i (mod 2^{δ_i})`).  The separated `hcons` is *derived* through
`lift_congruence_imp_separation`. -/
def OlcSliceData.ofLiftCongruence (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ)
    (level : ℕ → ℕ)
    (hbound : ∀ k ∈ (olcFibre ctx).filter (fun k => key k = y), level k ≤ ctx.shell.X)
    (hcf : ∀ x ∈ (olcFibre ctx).filter (fun k => key k = y),
      ∀ z ∈ (olcFibre ctx).filter (fun k => key k = y), x < z → level x < level z)
    (hcong : ∀ x ∈ (olcFibre ctx).filter (fun k => key k = y),
      ∀ z ∈ (olcFibre ctx).filter (fun k => key k = y), x < z →
        (∀ c ∈ (olcFibre ctx).filter (fun k => key k = y), x < c → z ≤ c) →
          2 ^ level x ∣ (level z - level x)) :
    OlcSliceData ctx key y where
  level := level
  hbound := hbound
  hcf := hcf
  hcons := fun x hx z hz hxz hsucc =>
    lift_congruence_imp_separation (hcf x hx z hz hxz) (hcong x hx z hz hxz hsucc)

/-- **`OlcSliceData` from the lift congruence, literal `[MOD]` form.**  As `ofLiftCongruence` with the
congruence phrased `level z % 2^(level x) = level x % 2^(level x)`. -/
def OlcSliceData.ofLiftModCongruence (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ)
    (level : ℕ → ℕ)
    (hbound : ∀ k ∈ (olcFibre ctx).filter (fun k => key k = y), level k ≤ ctx.shell.X)
    (hcf : ∀ x ∈ (olcFibre ctx).filter (fun k => key k = y),
      ∀ z ∈ (olcFibre ctx).filter (fun k => key k = y), x < z → level x < level z)
    (hcong : ∀ x ∈ (olcFibre ctx).filter (fun k => key k = y),
      ∀ z ∈ (olcFibre ctx).filter (fun k => key k = y), x < z →
        (∀ c ∈ (olcFibre ctx).filter (fun k => key k = y), x < c → z ≤ c) →
          level z % 2 ^ level x = level x % 2 ^ level x) :
    OlcSliceData ctx key y where
  level := level
  hbound := hbound
  hcf := hcf
  hcons := fun x hx z hz hxz hsucc =>
    lift_modCongruence_imp_separation (hcf x hx z hz hxz) (hcong x hx z hz hxz hsucc)

/-! ## 3.  The actual carry valuation `carryVal2` realises the congruence primitive

The level map intended by the manuscript is the 2-adic valuation of the integer carry,
`carryVal2 = v₂(integerCarry)` (`ReturnCarryNestingCore`).  Here it is shown to genuinely realise the
lift-congruence primitive, and the `OlcSliceData` constructors are specialised to it. -/

/-- **The carry valuation realises the lift congruence across a zero-run (PROVED).**

Across a zero digit-run of length `h` after `N`, `carryVal2 (N+h) = carryVal2 N + h`
(`carryVal2_add_zeroRun`).  If the run length `h` is a multiple of `2^(carryVal2 N)` (the
self-referential recurrence period of the nested return), then
`2^(carryVal2 N) ∣ (carryVal2 (N+h) − carryVal2 N)` — the carry-side realisation of
`δ_{i+1} ≡ δ_i (mod 2^{δ_i})`. -/
theorem carryVal2_dvd_sub_of_zeroRun (ctx : ActualFailureContext) (N h : ℕ)
    (hz : ∀ j, N < j → j ≤ N + h → ctx.d j = 0)
    (hdvd : 2 ^ carryVal2 ctx N ∣ h) :
    2 ^ carryVal2 ctx N ∣ (carryVal2 ctx (N + h) - carryVal2 ctx N) := by
  rw [carryVal2_add_zeroRun ctx N h hz]
  have he : carryVal2 ctx N + h - carryVal2 ctx N = h := by omega
  rw [he]; exact hdvd

/-- **The carry valuation is logarithmic in the carry magnitude (PROVED).**

`carryVal2 N = v₂(R_N) ≤ log₂(R_N)` because `2^(v₂ R_N) ∣ R_N` with `R_N > 0` (`carryOf_pos`).  This
is the level-map analogue of the `carry_zeroRun_length_le` `O(log X)` bound: the M.2.1 nesting levels
of the actual carries are `O(log X)`, which `liftLevelBound` compresses to `O(log* X)`. -/
theorem carryVal2_le_log (ctx : ActualFailureContext) (N : ℕ) :
    carryVal2 ctx N ≤ Nat.log 2 (carryOf ctx N).toNat := by
  have hpos : 0 < (carryOf ctx N).toNat := by have h := carryOf_pos ctx N; omega
  simp only [carryVal2]
  have hdvd : 2 ^ ((carryOf ctx N).toNat.factorization 2) ∣ (carryOf ctx N).toNat :=
    Nat.ordProj_dvd _ _
  exact Nat.le_log_of_pow_le Nat.one_lt_two (Nat.le_of_dvd hpos hdvd)

/-- **`OlcSliceData` with the actual carry valuation as level map.**  The per-`(e,τ,P)`-slice residual
with `level = carryVal2 ctx`: from the shell-scale bound, crossing-freeness `hcf` (Fine–Wilf), and the
consecutive lift congruence `2^(carryVal2 x) ∣ (carryVal2 z − carryVal2 x)` on the actual carry
valuations.  This is the intended carry-side level map — non-degenerate, not an abstract stand-in. -/
def OlcSliceData.ofCarryVal2 (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ)
    (hbound : ∀ k ∈ (olcFibre ctx).filter (fun k => key k = y), carryVal2 ctx k ≤ ctx.shell.X)
    (hcf : ∀ x ∈ (olcFibre ctx).filter (fun k => key k = y),
      ∀ z ∈ (olcFibre ctx).filter (fun k => key k = y), x < z → carryVal2 ctx x < carryVal2 ctx z)
    (hcong : ∀ x ∈ (olcFibre ctx).filter (fun k => key k = y),
      ∀ z ∈ (olcFibre ctx).filter (fun k => key k = y), x < z →
        (∀ c ∈ (olcFibre ctx).filter (fun k => key k = y), x < c → z ≤ c) →
          2 ^ carryVal2 ctx x ∣ (carryVal2 ctx z - carryVal2 ctx x)) :
    OlcSliceData ctx key y :=
  OlcSliceData.ofLiftCongruence ctx key y (carryVal2 ctx) hbound hcf hcong

/-- **`OlcSliceData` with `carryVal2`, from the carry-side zero-run geometry.**  The per-slice
residual reduced to the most primitive carry-side data: crossing-freeness `hcf` (Fine–Wilf) together
with, for each consecutive endpoint pair `x < z`, a zero digit-run on `(x, z]` (`hzero`) whose gap
`z − x` is a positive multiple of `2^(carryVal2 x)` (`hgap`, the self-referential recurrence period).
The congruence on the carry valuations is then produced by `carryVal2_dvd_sub_of_zeroRun`. -/
def OlcSliceData.ofCarryZeroRuns (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ)
    (hbound : ∀ k ∈ (olcFibre ctx).filter (fun k => key k = y), carryVal2 ctx k ≤ ctx.shell.X)
    (hcf : ∀ x ∈ (olcFibre ctx).filter (fun k => key k = y),
      ∀ z ∈ (olcFibre ctx).filter (fun k => key k = y), x < z → carryVal2 ctx x < carryVal2 ctx z)
    (hzero : ∀ x ∈ (olcFibre ctx).filter (fun k => key k = y),
      ∀ z ∈ (olcFibre ctx).filter (fun k => key k = y), x < z →
        (∀ c ∈ (olcFibre ctx).filter (fun k => key k = y), x < c → z ≤ c) →
          ∀ j, x < j → j ≤ z → ctx.d j = 0)
    (hgap : ∀ x ∈ (olcFibre ctx).filter (fun k => key k = y),
      ∀ z ∈ (olcFibre ctx).filter (fun k => key k = y), x < z →
        (∀ c ∈ (olcFibre ctx).filter (fun k => key k = y), x < c → z ≤ c) →
          2 ^ carryVal2 ctx x ∣ (z - x)) :
    OlcSliceData ctx key y :=
  OlcSliceData.ofCarryVal2 ctx key y hbound hcf (by
    intro x hx z hz hxz hsucc
    have hzx : x + (z - x) = z := by omega
    have hrun : ∀ j, x < j → j ≤ x + (z - x) → ctx.d j = 0 := by
      intro j hj1 hj2; rw [hzx] at hj2; exact hzero x hx z hz hxz hsucc j hj1 hj2
    have hk := carryVal2_dvd_sub_of_zeroRun ctx x (z - x) hrun (hgap x hx z hz hxz hsucc)
    rwa [hzx] at hk)

/-- **Non-degeneracy of the carry-side per-slice ingredients (PROVED).**  On a genuine zero digit-run
of length `h > 0` that is a multiple of `2^(carryVal2 N)`, the actual carry valuation `carryVal2`
supplies *both* `OlcSliceData` ingredients on the `(N, N+h)` step: the crossing-free strict increase
(`carryVal2_strictMono_zeroRun`) and the lift congruence (`carryVal2_dvd_sub_of_zeroRun`).  So the
level map is genuinely the (non-constant) carry valuation, not a faked constant/identity. -/
theorem carryVal2_olcSlice_ingredients_on_zeroRun (ctx : ActualFailureContext) (N h : ℕ) (hh : 0 < h)
    (hz : ∀ j, N < j → j ≤ N + h → ctx.d j = 0)
    (hdvd : 2 ^ carryVal2 ctx N ∣ h) :
    carryVal2 ctx N < carryVal2 ctx (N + h) ∧
      2 ^ carryVal2 ctx N ∣ (carryVal2 ctx (N + h) - carryVal2 ctx N) :=
  ⟨carryVal2_strictMono_zeroRun ctx N h hh hz, carryVal2_dvd_sub_of_zeroRun ctx N h hz hdvd⟩

/-! ## 4.  The corrected global OLC bound from a carry-side per-slice family

The faithful `M_L·X` shape (wave-11's `routedFibre4_card_le_of_slices`) with the per-slice level map
pinned to the actual carry valuation `carryVal2`. -/

/-- **The corrected global OLC count from the carry-side per-slice family (PROVED).**

Given, for every slice key `y`, the shell-scale bound, the Fine–Wilf crossing-freeness, and the
consecutive lift congruence on the actual carry valuations `carryVal2`, the global OLC fibre count is
`|routedFibre 4| ≤ #sliceKeys · liftLevelBound X` — the manuscript `M_L·X` envelope
(`#sliceKeys = O(X·(log L)^2)`, `liftLevelBound X = O(log* X)`), with the genuine carry-side level
map throughout. -/
theorem routedFibre4_card_le_of_carryVal2_congruence (ctx : ActualFailureContext) (key : ℕ → ℕ)
    (hbound : ∀ y ∈ (olcFibre ctx).image key,
      ∀ k ∈ (olcFibre ctx).filter (fun k => key k = y), carryVal2 ctx k ≤ ctx.shell.X)
    (hcf : ∀ y ∈ (olcFibre ctx).image key,
      ∀ x ∈ (olcFibre ctx).filter (fun k => key k = y),
        ∀ z ∈ (olcFibre ctx).filter (fun k => key k = y), x < z → carryVal2 ctx x < carryVal2 ctx z)
    (hcong : ∀ y ∈ (olcFibre ctx).image key,
      ∀ x ∈ (olcFibre ctx).filter (fun k => key k = y),
        ∀ z ∈ (olcFibre ctx).filter (fun k => key k = y), x < z →
          (∀ c ∈ (olcFibre ctx).filter (fun k => key k = y), x < c → z ≤ c) →
            2 ^ carryVal2 ctx x ∣ (carryVal2 ctx z - carryVal2 ctx x)) :
    (olcFibre ctx).card ≤ ((olcFibre ctx).image key).card * liftLevelBound ctx.shell.X :=
  routedFibre4_card_le_of_slices ctx key
    (fun y hy => OlcSliceData.ofCarryVal2 ctx key y (hbound y hy) (hcf y hy) (hcong y hy))

/-! ## 5.  Non-vacuity — the per-slice congruence mechanism fires on a genuine chain

The crossing-free + lift-congruence count is not a vacuous implication: it fires on the concrete
non-empty self-referential tower chain `shellLevels L`, whose tower-level coordinate is crossing-free
(`level = id`) and obeys the lift congruence (`shellLevels_isLiftCongruenceChain`), recovering the
inverse-tower count.  This is the J.4 chain, never an empty/constant/degenerate stand-in. -/

/-- **Non-vacuity of the per-slice congruence count (PROVED).**  On the genuine tower chain
`shellLevels L` the identity level map is crossing-free and obeys the lift congruence, so the new
crossing-free + congruence count fires and recovers `|shellLevels L| ≤ liftLevelBound L`. -/
theorem crossingFree_congruence_count_nonvacuous (L : ℕ) :
    (shellLevels L).card ≤ liftLevelBound L :=
  card_le_liftLevelBound_of_crossingFree_congruence
    (L := L) (level := fun n => n)
    (fun k hk => shellLevels_subset_le k hk)
    (fun x hx y hy hxy => hxy)
    (fun x hx y hy hxy _hsucc => shellLevels_isLiftCongruenceChain x hx y hy hxy)

/-- **The genuine tower chain is non-empty** — the per-slice congruence count is realised on a
non-empty fibre model. -/
theorem crossingFree_congruence_count_nonvacuous_nonempty (L : ℕ) : (shellLevels L).Nonempty :=
  shellLevels_nonempty L

/-! ## 6.  Honest residual inventory -/

/-- The precise status of the per-slice M.2.1 OLC endpoint multiplicity after this module. -/
def returnM21SliceResiduals : List String :=
  [ "CLOSED (per-slice count from the congruence primitive) — " ++
      "card_le_liftLevelBound_of_crossingFree_congruence / _modCongruence: crossing-freeness hcf plus " ++
      "the consecutive self-referential lift congruence 2^(level x) ∣ (level z − level x) (resp. " ++
      "level z % 2^(level x) = level x % 2^(level x)) gives |F| ≤ liftLevelBound L. The separated " ++
      "hcons of wave-10's card_le_liftLevelBound_of_crossingFree is DERIVED via " ++
      "lift_congruence_imp_separation (ReturnLiftChainProof).",
    "CLOSED (the missing OlcSliceData constructors) — OlcSliceData.ofLiftCongruence / " ++
      "ofLiftModCongruence: build the per-(e,τ,P)-slice residual (ReturnCarryNestingCore, which had " ++
      "only ofEmpty) from the level map + hbound + hcf + the consecutive lift congruence, deriving " ++
      "hcons. OlcSliceData.card_le then gives each slice ≤ liftLevelBound X.",
    "CLOSED (carry-side level map realises the congruence) — carryVal2_dvd_sub_of_zeroRun: across a " ++
      "zero digit-run of 2^δ-multiple length, the actual carry valuation δ = carryVal2 satisfies " ++
      "2^(carryVal2 N) ∣ (carryVal2 (N+h) − carryVal2 N), via carryVal2_add_zeroRun. carryVal2_le_log: " ++
      "carryVal2 N ≤ log₂(R_N⁺) (the level map is O(log) in the carry magnitude). " ++
      "carryVal2_olcSlice_ingredients_on_zeroRun: carryVal2 supplies BOTH per-slice ingredients " ++
      "(strict increase + congruence) on a genuine zero-run — non-degenerate, non-constant.",
    "CLOSED (per-slice residual with the actual carry valuation) — OlcSliceData.ofCarryVal2 / " ++
      "ofCarryZeroRuns: the OlcSliceData with level = carryVal2 ctx, from crossing-freeness (Fine–Wilf) " ++
      "+ the congruence on the carry valuations (resp. per-consecutive-pair zero-runs of 2^δ-multiple " ++
      "length). routedFibre4_card_le_of_carryVal2_congruence: the corrected global bound " ++
      "|routedFibre 4| ≤ #sliceKeys · liftLevelBound X with the genuine carry-side level map.",
    "NON-VACUOUS — crossingFree_congruence_count_nonvacuous: the per-slice crossing-free + congruence " ++
      "count fires on the genuine non-empty tower chain shellLevels L (via " ++
      "shellLevels_isLiftCongruenceChain), recovering |shellLevels L| ≤ liftLevelBound L. No " ++
      "empty/constant/identity shortcut on the actual fibre.",
    -- WAVE-14 (additive note): the crossing exclusion in this OPEN entry is the M.2.1 endpoint
    -- *pinning* `ReturnCrossingFreeCore.SliceEndpointPinning` (a pinned return endpoint forbids a
    -- strict carry crossing — pure order); Fine–Wilf (fineWilf_distinct_primitive_excluded) is the
    -- *dirty-family* route, and a strict per-slice `hcf` needs the full anchored slice key (e,τ,P,χ,σ,ι).
    "OPEN (the smallest residual — the classifier↔OLC-endpoint geometric link of the ACTUAL carries) — " ++
      "for each slice (e,τ,P): (1) crossing-freeness hcf of carryVal2 (the Fine–Wilf K.2.3/K.2.5 " ++
      "crossing exclusion: a crossing exposes two distinct primitive semiperiodic arm descriptions on " ++
      "a long overlap, forbidden by fineWilf_distinct_primitive_excluded); (2) the consecutive " ++
      "self-referential congruence hcong = 2^(carryVal2 x) ∣ (carryVal2 z − carryVal2 x), equivalently " ++
      "(via carryVal2_add_zeroRun) the inter-endpoint gap z − x is a positive multiple of 2^(carryVal2 " ++
      "x) (the carry-period structure of the nested returns). Both are properties of WHICH positions " ++
      "are OLC return endpoints, owned by the deep Return geometry, not the carry recurrence alone. " ++
      "proof_v4 §M.2 / M.2.1 / J.4 / K.2.4–K.2.5." ]

theorem returnM21SliceResiduals_nonempty : returnM21SliceResiduals ≠ [] := by
  simp [returnM21SliceResiduals]

/-! ## 7.  Axiom-cleanliness audit -/

#print axioms card_le_liftLevelBound_of_crossingFree_congruence
#print axioms card_le_liftLevelBound_of_crossingFree_modCongruence
#print axioms OlcSliceData.ofLiftCongruence
#print axioms OlcSliceData.ofLiftModCongruence
#print axioms carryVal2_dvd_sub_of_zeroRun
#print axioms carryVal2_le_log
#print axioms OlcSliceData.ofCarryVal2
#print axioms OlcSliceData.ofCarryZeroRuns
#print axioms carryVal2_olcSlice_ingredients_on_zeroRun
#print axioms routedFibre4_card_le_of_carryVal2_congruence
#print axioms crossingFree_congruence_count_nonvacuous

end

end Erdos260
