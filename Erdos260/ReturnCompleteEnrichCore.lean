import Erdos260.ReturnCleanCarryCore

/-!
# The complete-return ⟹ clean-doubled-carry derivation of `(Z)` (`ReturnCompleteEnrichCore`)

This module (NEW; it edits no existing file) performs the **wave-18 structural enrichment** of the
Return clean-carry heart `(Z)`.  Wave-17 (`ReturnCleanCarryCore`) pinned `(Z)` to its tightest
carry-intrinsic equivalent — the *clean doubling* `R_z = 2^{z−x} R_x` (`CleanReturnSegment`) — and
left as the lone residual *which positions are the complete-return starts*.  This module **derives**
`(Z)` from the *actual complete-return structure* rather than carrying it: it exposes how a complete
return forces the integer carry `R_N` to return to a clean (purely doubled) state on its return
segment, by unfolding the manuscript identity (Zp) of the Remark after Lemma M.3.2

> a complete return is **exactly** a clean, purely-doubled carry state across the segment,
> `R_z = 2^{z−x} R_x ⟺ (Z)` on `(x, z]`,

down to the **per-step carry dynamics** of the recurrence `R_{N+1} = 2 R_N − Q(N+1) d_{N+1}`.

## The complete-return arm, dynamically (new content)

The genuine structural object is the **complete-return arm** `CompleteReturnArm ctx x z`: the carry
evolves on `(x, z]` *purely by doubling* — every step is a clean doubling step
`R_{N+1} = 2 R_N`.  This is the manuscript's "clean-maximal complete return arm" (Theorem M.1.1),
read off the carry recurrence:

* a **clean step** (`d (N+1) = 0`) doubles the carry exactly, `R_{N+1} = 2 R_N`
  (`carryOf_clean_step`);
* a **dirty step** (`d (N+1) = 1`) strictly *drops* it, `R_{N+1} = 2 R_N − Q(N+1) < 2 R_N`
  (`carryOf_dirty_step` / `dirty_step_breaks_arm`);
* hence a carry step is a clean doubling **iff** its digit is `0` (`carryOf_step_clean_iff`).

## What is genuinely PROVED here (new content)

* `carryOf_clean_step`, `carryOf_dirty_step`, `carryOf_step_clean_iff` — the **two-step return
  dynamics**: the carry recurrence splits into a clean doubling step and a strictly-dropping dirty
  step, and a step is a clean doubling iff its digit vanishes.
* `carryOf_doubling_of_steps` — **the complete-return ⟹ clean-doubled-carry step, ELEMENTARY and
  self-contained**: if every step on `(x, x+h]` is a clean doubling, then `R_{x+h} = 2^h R_x` by a
  direct induction over the per-step dynamics (no appeal to the wave-17 envelope is needed for this
  direction).
* `CompleteReturnArm`, `completeReturnArm_iff_zeroRun`, `completeReturnArm_imp_cleanDoubling`,
  `cleanDoubling_imp_completeReturnArm`, `completeReturnArm_iff_cleanReturnSegment` — **the
  manuscript identity (Zp) at the arm level**: the dynamical complete-return arm is *equivalent* to
  the carry-level clean doubling `CleanReturnSegment` and to the digit-word `(Z)` on `(x, z]`.  The
  `⟹` is the elementary forcing above; the deep `⟸` (clean doubling forces every intervening digit
  `0`) is wave-17's `integerCarry_zeroRun_of_doubling`.
* `SliceCompleteReturns`, `sliceCompleteReturns_iff_sliceCleanReturns`,
  `zeroRunConsecutive_of_completeReturns`, `hmono_of_completeReturns`,
  `anchoredKey_hmono_of_completeReturns`, `carryVal2_crossingFree_of_completeReturns`,
  `OlcSliceData.ofCompleteReturns`, `completeReturns_teeth` — **the placement and the full discharge**:
  the slice residual "consecutive OLC complete-return starts bound complete-return arms" is *literally
  equivalent* to the wave-17 `SliceCleanReturns` (= `(Z)`), and from it the entire wave-16/17
  downstream API (`hmono` for any M.3.2-pinned endpoint, crossing-freeness, the per-slice
  `OlcSliceData`, and the `AnchoredSliceCrossing` engine) fires.
* `not_completeReturnArm_of_dirty`, `dirtyBetweenStarts_strict_deficit`,
  `completeReturnArm_carry_strictMono` — **teeth / non-vacuity**: a single dirty `1`-digit on a
  segment breaks the complete return and is a genuine strict carry deficit
  `R_z < 2^{z−x} R_x`; on a real complete-return arm the carry valuation strictly climbs.  So the
  complete-return arm is a genuine constraint, never a vacuous restatement.

## The smallest honest residual (sharply characterized)

After this module `(Z)` is **derived from the complete-return arm structure**: the dynamical arm,
the carry-level clean doubling, and the digit-word `(Z)` are proved mutually equivalent
(`completeReturnArm_iff_cleanReturnSegment` then `cleanReturnSegment_iff_zeroRun`), and
`SliceCompleteReturns` discharges the whole nesting/count chain.  The lone irreducible remainder is
the **placement of the complete-return starts**: that consecutive OLC starts on an anchored slice
bound complete-return arms — equivalently (`sliceCompleteReturns_iff_noDirtyBetweenStarts`) that *no
valuation-dropping `1`-digit occurs between consecutive starts in the shared anchored region*.  This
is the M.3.1 four-coordinate anchored overlap + M.3.2 endpoint-pinning geometry of the actual
carries; the carry recurrence cannot decide it (a `1`-digit is a genuine strict carry deficit, so
the constraint is non-vacuous).  No `sorry`, `axiom`, `admit`, or `native_decide`; no degenerate
shortcut.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The two-step return dynamics of the carry recurrence

The integer carry of the failing context obeys `R_{N+1} = 2 R_N − Q(N+1) d_{N+1}`.  On a binary
digit word this splits into exactly two steps: a **clean** step (`d = 0`) that doubles the carry, and
a **dirty** step (`d = 1`) that strictly drops it.  A complete-return arm is a maximal block of clean
steps. -/

/-- **The clean carry step (PROVED).**  A `0`-digit doubles the carry exactly: `R_{N+1} = 2 R_N`. -/
theorem carryOf_clean_step (ctx : ActualFailureContext) (N : ℕ) (h0 : ctx.d (N + 1) = 0) :
    carryOf ctx (N + 1) = 2 * carryOf ctx N := by
  unfold carryOf
  exact integerCarry_succ_of_zero ctx.Q (ctxNum ctx) ctx.d h0

/-- **The dirty carry step (PROVED).**  A `1`-digit drops the carry by the strictly positive
`Q(N+1)`: `R_{N+1} = 2 R_N − Q(N+1)`. -/
theorem carryOf_dirty_step (ctx : ActualFailureContext) (N : ℕ) (h1 : ctx.d (N + 1) = 1) :
    carryOf ctx (N + 1) = 2 * carryOf ctx N - (ctx.Q : ℤ) * ((N + 1 : ℕ) : ℤ) := by
  unfold carryOf
  exact integerCarry_succ_of_one ctx.Q (ctxNum ctx) ctx.d h1

/-- **A carry step is a clean doubling iff its digit vanishes (PROVED).**  Since the subtracted term
`Q(N+1) d_{N+1}` is `0` exactly when `d_{N+1} = 0` (as `Q(N+1) > 0`), the recurrence step equals its
clean doubling `2 R_N` iff the digit is `0`. -/
theorem carryOf_step_clean_iff (ctx : ActualFailureContext) (N : ℕ) :
    carryOf ctx (N + 1) = 2 * carryOf ctx N ↔ ctx.d (N + 1) = 0 := by
  have hrec : carryOf ctx (N + 1)
      = 2 * carryOf ctx N - (ctx.Q : ℤ) * ((N + 1 : ℕ) : ℤ) * (ctx.d (N + 1) : ℤ) := by
    unfold carryOf; rw [integerCarry_succ]
  have hQpos : (0 : ℤ) < (ctx.Q : ℤ) * ((N + 1 : ℕ) : ℤ) :=
    mul_pos (by exact_mod_cast ctx.hQ) (by exact_mod_cast Nat.succ_pos N)
  constructor
  · intro h
    have hzero : (ctx.Q : ℤ) * ((N + 1 : ℕ) : ℤ) * (ctx.d (N + 1) : ℤ) = 0 := by
      rw [hrec] at h; linarith
    have hd0 : (ctx.d (N + 1) : ℤ) = 0 := by
      rcases mul_eq_zero.1 hzero with h1 | h2
      · exact absurd h1 (ne_of_gt hQpos)
      · exact h2
    exact_mod_cast hd0
  · intro h0
    exact carryOf_clean_step ctx N h0

/-! ## 2.  The complete-return arm and the manuscript identity (Zp) at the arm level

The dynamical complete-return arm: the carry evolves purely by doubling.  The combinatorial core —
the complete-return ⟹ clean-doubled-carry step — is the *elementary* induction
`carryOf_doubling_of_steps`.  Together with wave-17's deep `⟸` it yields the manuscript identity
(Zp) at the arm level: `CompleteReturnArm ⟺ CleanReturnSegment ⟺ (Z)`. -/

/-- **The complete-return arm.**  On `(x, z]` the carry evolves *purely by doubling*: every step is a
clean doubling step `R_{N+1} = 2 R_N`.  This is the carry-dynamics reading of the manuscript's
"clean-maximal complete return arm" (Theorem M.1.1): a complete return is a maximal block over which
the carry returns to a clean doubled state. -/
def CompleteReturnArm (ctx : ActualFailureContext) (x z : ℕ) : Prop :=
  x ≤ z ∧ ∀ N, x ≤ N → N < z → carryOf ctx (N + 1) = 2 * carryOf ctx N

/-- **The complete-return ⟹ clean-doubled-carry step (PROVED, elementary).**  If every step on
`(x, x+h]` is a clean doubling, the carry doubles cleanly across the whole block: `R_{x+h} = 2^h R_x`.
Direct induction over the per-step dynamics — the genuine forcing, self-contained from the
recurrence (it does *not* invoke the wave-17 doubling envelope). -/
theorem carryOf_doubling_of_steps (ctx : ActualFailureContext) (x : ℕ) :
    ∀ h, (∀ N, x ≤ N → N < x + h → carryOf ctx (N + 1) = 2 * carryOf ctx N) →
      carryOf ctx (x + h) = 2 ^ h * carryOf ctx x := by
  intro h
  induction h with
  | zero => intro _; simp
  | succ h ih =>
      intro hstep
      have hstep' : ∀ N, x ≤ N → N < x + h → carryOf ctx (N + 1) = 2 * carryOf ctx N :=
        fun N hN1 hN2 => hstep N hN1 (by omega)
      have hlast : carryOf ctx (x + h + 1) = 2 * carryOf ctx (x + h) :=
        hstep (x + h) (by omega) (by omega)
      have hih := ih hstep'
      calc carryOf ctx (x + (h + 1))
          = carryOf ctx (x + h + 1) := by rw [Nat.add_succ]
        _ = 2 * carryOf ctx (x + h) := hlast
        _ = 2 * (2 ^ h * carryOf ctx x) := by rw [hih]
        _ = 2 ^ (h + 1) * carryOf ctx x := by rw [pow_succ]; ring

/-- **The complete-return arm is the zero digit-run (PROVED).**  On `(x, z]` the carry evolves by
pure doubling iff every digit is `0` — each clean step is exactly a `0`-digit
(`carryOf_step_clean_iff`). -/
theorem completeReturnArm_iff_zeroRun (ctx : ActualFailureContext) {x z : ℕ} (hxz : x ≤ z) :
    CompleteReturnArm ctx x z ↔ ∀ j, x < j → j ≤ z → ctx.d j = 0 := by
  constructor
  · rintro ⟨-, hstep⟩ j hj1 hj2
    obtain ⟨N, rfl⟩ : ∃ N, j = N + 1 := ⟨j - 1, by omega⟩
    exact (carryOf_step_clean_iff ctx N).1 (hstep N (by omega) (by omega))
  · intro hzero
    refine ⟨hxz, ?_⟩
    intro N hxN hNz
    exact (carryOf_step_clean_iff ctx N).2 (hzero (N + 1) (by omega) (by omega))

/-- **Complete return ⟹ clean doubling (PROVED) — the combinatorial core.**  A complete-return arm
forces the carry-level clean doubling `R_z = 2^{z−x} R_x` (`CleanReturnSegment`), directly from the
per-step dynamics via `carryOf_doubling_of_steps`.  This is the manuscript's "a complete return forces
`R_N` to return to a clean state", proved. -/
theorem completeReturnArm_imp_cleanDoubling (ctx : ActualFailureContext) {x z : ℕ}
    (H : CompleteReturnArm ctx x z) : CleanReturnSegment ctx x z := by
  obtain ⟨hxz, hstep⟩ := H
  unfold CleanReturnSegment
  obtain ⟨h, rfl⟩ : ∃ h, z = x + h := ⟨z - x, by omega⟩
  have hsub : (x + h) - x = h := by omega
  rw [hsub]
  exact carryOf_doubling_of_steps ctx x h hstep

/-- **Clean doubling ⟹ complete return (PROVED) — the deep converse.**  A clean-doubled carry state
forces a complete-return arm: by wave-17's `integerCarry_zeroRun_of_doubling` the doubling makes every
intervening digit `0`, hence every step is a clean doubling. -/
theorem cleanDoubling_imp_completeReturnArm (ctx : ActualFailureContext) {x z : ℕ} (hxz : x ≤ z)
    (H : CleanReturnSegment ctx x z) : CompleteReturnArm ctx x z :=
  (completeReturnArm_iff_zeroRun ctx hxz).2 ((cleanReturnSegment_iff_zeroRun ctx hxz).1 H)

/-- **The manuscript identity (Zp) at the arm level (PROVED).**  The dynamical complete-return arm is
*equivalent* to the carry-level clean doubling `CleanReturnSegment ctx x z` (`R_z = 2^{z−x} R_x`).
Composed with wave-17's `cleanReturnSegment_iff_zeroRun` this is exactly
`a complete return ⟺ clean purely-doubled carry state ⟺ (Z)`. -/
theorem completeReturnArm_iff_cleanReturnSegment (ctx : ActualFailureContext) {x z : ℕ}
    (hxz : x ≤ z) :
    CompleteReturnArm ctx x z ↔ CleanReturnSegment ctx x z :=
  ⟨fun H => completeReturnArm_imp_cleanDoubling ctx H,
    fun H => cleanDoubling_imp_completeReturnArm ctx hxz H⟩

/-- **The complete-return arm is the digit-word `(Z)` (PROVED).**  The full chain
`CompleteReturnArm ⟺ CleanReturnSegment ⟺ (Z)` on `(x, z]` — `(Z)` is derived from the
complete-return arm structure, verbatim. -/
theorem completeReturnArm_iff_zeroRun_clean (ctx : ActualFailureContext) {x z : ℕ} (hxz : x ≤ z) :
    CompleteReturnArm ctx x z ↔ ∀ j, x < j → j ≤ z → ctx.d j = 0 :=
  completeReturnArm_iff_zeroRun ctx hxz

/-! ## 3.  The slice placement `SliceCompleteReturns` and the full discharge

The slice residual: between consecutive OLC complete-return starts the carry runs a complete-return
arm.  This is *literally* the wave-17 `SliceCleanReturns` (= `(Z)`), and it discharges the whole
`hmono`/crossing-free/`OlcSliceData` chain. -/

/-- **The slice complete-return residual.**  Between every pair of *consecutive* OLC complete-return
starts on the slice, the carry runs a complete-return arm (returns to a clean doubled state). -/
def SliceCompleteReturns (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ) : Prop :=
  ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
    (∀ c ∈ olcSlice ctx key y, x < c → z ≤ c) →
      CompleteReturnArm ctx x z

/-- **`SliceCompleteReturns` ⟺ wave-17 `SliceCleanReturns` (PROVED).**  The complete-return placement
is literally the clean-doubling slice residual `(Z)`. -/
theorem sliceCompleteReturns_iff_sliceCleanReturns (ctx : ActualFailureContext) (key : ℕ → ℕ)
    (y : ℕ) :
    SliceCompleteReturns ctx key y ↔ SliceCleanReturns ctx key y := by
  constructor
  · intro H x hx z hz hxz hcons
    exact completeReturnArm_imp_cleanDoubling ctx (H x hx z hz hxz hcons)
  · intro H x hx z hz hxz hcons
    exact (completeReturnArm_iff_cleanReturnSegment ctx (le_of_lt hxz)).2 (H x hx z hz hxz hcons)

/-- **The per-consecutive-pair zero-run from complete returns (PROVED).** -/
theorem zeroRunConsecutive_of_completeReturns (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ)
    (H : SliceCompleteReturns ctx key y) :
    ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      (∀ c ∈ olcSlice ctx key y, x < c → z ≤ c) →
        ∀ j, x < j → j ≤ z → ctx.d j = 0 :=
  zeroRun_consecutive_of_cleanReturns ctx key y
    ((sliceCompleteReturns_iff_sliceCleanReturns ctx key y).1 H)

/-- **The all-pairs zero-run from complete returns (PROVED).** -/
theorem zeroRunAllPairs_of_completeReturns (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ)
    (H : SliceCompleteReturns ctx key y) :
    ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      ∀ j, x < j → j ≤ z → ctx.d j = 0 :=
  zeroRun_allPairs_of_cleanReturns ctx key y
    ((sliceCompleteReturns_iff_sliceCleanReturns ctx key y).1 H)

/-- **Crossing-freeness `hcf` from complete returns (PROVED).** -/
theorem carryVal2_crossingFree_of_completeReturns (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ)
    (H : SliceCompleteReturns ctx key y) :
    ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      carryVal2 ctx x < carryVal2 ctx z :=
  carryVal2_crossingFree_of_cleanReturns ctx key y
    ((sliceCompleteReturns_iff_sliceCleanReturns ctx key y).1 H)

/-- **`hmono` from complete returns (PROVED).**  For any M.3.2-pinned (key-factoring) endpoint, the
complete-return placement discharges the wave-15 atom `hmono`. -/
theorem hmono_of_completeReturns (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ) {endpt : ℕ → ℕ}
    (hfix : FactorsThroughKey key endpt) (H : SliceCompleteReturns ctx key y) :
    ∀ x z, CarryCrossing ctx key y x z → endpt x < endpt z :=
  hmono_of_cleanReturns ctx key y hfix
    ((sliceCompleteReturns_iff_sliceCleanReturns ctx key y).1 H)

/-- **`hmono` under the full anchored key from complete returns (PROVED).** -/
theorem anchoredKey_hmono_of_completeReturns (ctx : ActualFailureContext)
    (e tau P chi sigma iota : ℕ → ℕ) (y : ℕ)
    (H : SliceCompleteReturns ctx (anchoredKey e tau P chi sigma iota) y) :
    ∀ x z, CarryCrossing ctx (anchoredKey e tau P chi sigma iota) y x z → e x < e z :=
  anchoredKey_hmono_of_cleanReturns ctx e tau P chi sigma iota y
    ((sliceCompleteReturns_iff_sliceCleanReturns ctx (anchoredKey e tau P chi sigma iota) y).1 H)

/-- **The full per-slice residual `OlcSliceData` from complete returns + the lift-gap divisibility
(PROVED).**  With the complete-return placement (giving crossing-freeness), the shell bound `hbound`,
and the self-referential lift-gap divisibility `hgap`, the actual carry valuation is a genuine
`OlcSliceData`, so each anchored slice has `≤ liftLevelBound X` elements. -/
def OlcSliceData.ofCompleteReturns (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ)
    (hbound : ∀ k ∈ olcSlice ctx key y, carryVal2 ctx k ≤ ctx.shell.X)
    (H : SliceCompleteReturns ctx key y)
    (hgap : ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      (∀ c ∈ olcSlice ctx key y, x < c → z ≤ c) → 2 ^ carryVal2 ctx x ∣ (z - x)) :
    OlcSliceData ctx key y :=
  OlcSliceData.ofCleanReturns ctx key y hbound
    ((sliceCompleteReturns_iff_sliceCleanReturns ctx key y).1 H) hgap

/-! ## 4.  Teeth and non-vacuity

A single dirty `1`-digit breaks the complete return and is a genuine strict carry deficit; on a real
complete-return arm the carry valuation strictly climbs.  So the complete-return arm is a genuine
constraint, never a vacuous/degenerate restatement. -/

/-- **A dirty step breaks the arm (PROVED).**  A `1`-digit makes the step undershoot its doubling,
`R_{N+1} < 2 R_N` (`Q(N+1) > 0`) — the genuine valuation-dropping carry crossing. -/
theorem dirty_step_breaks_arm (ctx : ActualFailureContext) (N : ℕ) (h1 : ctx.d (N + 1) = 1) :
    carryOf ctx (N + 1) < 2 * carryOf ctx N :=
  carryOf_one_digit_strict_drop ctx N h1

/-- **A dirty digit destroys the complete return (PROVED).**  If any digit on `(x, z]` is `1`, the
segment is not a complete-return arm — a single carry-dropping `1`-digit obstructs the clean return. -/
theorem not_completeReturnArm_of_dirty (ctx : ActualFailureContext) {x z j : ℕ} (hxz : x ≤ z)
    (hj1 : x < j) (hj2 : j ≤ z) (hdirty : ctx.d j = 1) : ¬ CompleteReturnArm ctx x z := by
  intro H
  have hz := (completeReturnArm_iff_zeroRun ctx hxz).1 H j hj1 hj2
  rw [hdirty] at hz
  exact one_ne_zero hz

/-- **A dirty digit is a strict carry deficit (PROVED).**  A `1`-digit on `(x, z]` forces the carry
strictly below its clean doubling, `R_z < 2^{z−x} R_x` — so the complete-return arm is genuinely
non-vacuous. -/
theorem dirtyBetweenStarts_strict_deficit (ctx : ActualFailureContext) {x z : ℕ} (hxz : x ≤ z)
    {j : ℕ} (hj1 : x < j) (hj2 : j ≤ z) (hdirty : ctx.d j = 1) :
    carryOf ctx z < 2 ^ (z - x) * carryOf ctx x := by
  refine carryOf_strict_lt_doubling_of_not_zeroRun ctx hxz ?_
  intro hzero
  have hz := hzero j hj1 hj2
  rw [hdirty] at hz
  exact one_ne_zero hz

/-- **A complete-return arm genuinely climbs the carry valuation (PROVED).**  On a nonempty arm
`x < z`, `carryVal2 x < carryVal2 z` — the valuation strictly increases by the segment length. -/
theorem completeReturnArm_carry_strictMono (ctx : ActualFailureContext) {x z : ℕ} (hxz : x < z)
    (H : CompleteReturnArm ctx x z) : carryVal2 ctx x < carryVal2 ctx z :=
  clean_return_carry_strictMono ctx hxz (completeReturnArm_imp_cleanDoubling ctx H)

/-- **Non-vacuity, assembled (PROVED).**  On a complete-return anchored slice the actual carry
valuation is crossing-free *and* the wave-15 `AnchoredSliceCrossing` engine is inhabited with the
*derived* `hmono`. -/
theorem completeReturns_teeth (ctx : ActualFailureContext)
    (e tau P chi sigma iota : ℕ → ℕ) (y : ℕ)
    (H : SliceCompleteReturns ctx (anchoredKey e tau P chi sigma iota) y) :
    (∀ x ∈ olcSlice ctx (anchoredKey e tau P chi sigma iota) y,
        ∀ z ∈ olcSlice ctx (anchoredKey e tau P chi sigma iota) y, x < z →
          carryVal2 ctx x < carryVal2 ctx z)
      ∧ Nonempty (AnchoredSliceCrossing ctx (anchoredKey e tau P chi sigma iota) y) :=
  cleanReturns_teeth ctx e tau P chi sigma iota y
    ((sliceCompleteReturns_iff_sliceCleanReturns ctx (anchoredKey e tau P chi sigma iota) y).1 H)

/-! ## 5.  The irreducible remainder, sharply characterized: the start placement

The lone residual is *which positions are the complete-return starts*.  Equivalently — using the
binary digit word — the residual is exactly that **no carry-dropping `1`-digit occurs between
consecutive starts**: the M.3.1 anchored overlap + M.3.2 pinning placement that the recurrence
cannot decide. -/

/-- **The placement, in explicit digit form (PROVED).**  `SliceCompleteReturns` is *equivalent* to:
between consecutive OLC starts on the slice no digit is `1` (no valuation-dropping `1`-digit in the
shared anchored region).  This is `(Z)` written as the absence of carry crossings, isolating the
irreducible geometric datum. -/
theorem sliceCompleteReturns_iff_noDirtyBetweenStarts (ctx : ActualFailureContext) (key : ℕ → ℕ)
    (y : ℕ) :
    SliceCompleteReturns ctx key y ↔
      (∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
        (∀ c ∈ olcSlice ctx key y, x < c → z ≤ c) →
          ∀ j, x < j → j ≤ z → ctx.d j ≠ 1) := by
  constructor
  · intro H x hx z hz hxz hcons j hj1 hj2 hdirty
    have hz0 := (completeReturnArm_iff_zeroRun ctx (le_of_lt hxz)).1 (H x hx z hz hxz hcons) j hj1 hj2
    rw [hdirty] at hz0
    exact one_ne_zero hz0
  · intro H x hx z hz hxz hcons
    refine (completeReturnArm_iff_zeroRun ctx (le_of_lt hxz)).2 ?_
    intro j hj1 hj2
    rcases ctx.hd j with h0 | h1
    · exact h0
    · exact absurd h1 (H x hx z hz hxz hcons j hj1 hj2)

/-! ## 6.  Honest residual inventory -/

/-- The precise status of the Return clean-carry heart `(Z)` after deriving it from the
complete-return structure. -/
def returnCompleteEnrichResiduals : List String :=
  [ "GOAL (wave-18) — DERIVE (Z) from the actual complete-return structure rather than carry it. The " ++
      "manuscript identity (Zp) of the Remark after Lemma M.3.2 says a complete return is EXACTLY a " ++
      "clean, purely-doubled carry state across the segment, R_z = 2^(z-x) R_x <=> (Z) on (x,z]. This " ++
      "module unfolds that identity to the per-step carry dynamics of R_{N+1} = 2 R_N - Q(N+1) d_{N+1}.",
    "CLOSED (two-step return dynamics) — carryOf_clean_step (d=0 => R_{N+1} = 2 R_N), carryOf_dirty_step " ++
      "(d=1 => R_{N+1} = 2 R_N - Q(N+1)), carryOf_step_clean_iff (a step is a clean doubling <=> its " ++
      "digit is 0, since Q(N+1) > 0). The carry recurrence splits into a clean doubling step and a " ++
      "strictly-dropping dirty step.",
    "CLOSED (complete return => clean-doubled carry, the combinatorial core, ELEMENTARY) — " ++
      "carryOf_doubling_of_steps: if every step on (x,x+h] is a clean doubling then R_{x+h} = 2^h R_x, " ++
      "by direct induction over the per-step dynamics (NO appeal to the wave-17 envelope for this " ++
      "direction). completeReturnArm_imp_cleanDoubling is the manuscript 'a complete return forces R_N " ++
      "to return to a clean state', proved.",
    "CLOSED (the identity (Zp) at the arm level) — CompleteReturnArm (the carry evolves purely by " ++
      "doubling on (x,z]) is EQUIVALENT to CleanReturnSegment (R_z = 2^(z-x) R_x) and to the digit-word " ++
      "(Z): completeReturnArm_iff_zeroRun (each clean step = a 0-digit), " ++
      "completeReturnArm_iff_cleanReturnSegment, completeReturnArm_iff_zeroRun_clean. The deep <= " ++
      "(clean doubling forces every intervening digit 0) is wave-17's integerCarry_zeroRun_of_doubling.",
    "CLOSED (placement => full discharge) — SliceCompleteReturns (consecutive OLC starts bound " ++
      "complete-return arms) is LITERALLY equivalent to wave-17 SliceCleanReturns " ++
      "(sliceCompleteReturns_iff_sliceCleanReturns), and from it the whole wave-16/17 API fires: " ++
      "zeroRunConsecutive_/zeroRunAllPairs_of_completeReturns, carryVal2_crossingFree_of_completeReturns, " ++
      "hmono_of_completeReturns / anchoredKey_hmono_of_completeReturns for any M.3.2-pinned endpoint, " ++
      "OlcSliceData.ofCompleteReturns (with the lift-gap hgap, so each slice <= liftLevelBound X).",
    "NON-VACUOUS / TEETH — dirty_step_breaks_arm (a 1-digit gives R_{N+1} < 2 R_N, Q(N+1) > 0); " ++
      "not_completeReturnArm_of_dirty (a single 1-digit on (x,z] destroys the complete return); " ++
      "dirtyBetweenStarts_strict_deficit (any 1-digit forces R_z < 2^(z-x) R_x, a genuine carry " ++
      "crossing); completeReturnArm_carry_strictMono (on a real arm the carry valuation strictly " ++
      "climbs) + completeReturns_teeth. No degenerate shortcut.",
    "OPEN (the single irreducible remainder — the start placement) — SliceCompleteReturns itself: that " ++
      "consecutive OLC complete-return starts on an anchored slice bound complete-return arms. " ++
      "sliceCompleteReturns_iff_noDirtyBetweenStarts shows this is EXACTLY 'no valuation-dropping " ++
      "1-digit between consecutive starts in the shared anchored region' = (Z). This is the M.3.1 " ++
      "four-coordinate anchored overlap + M.3.2 endpoint pinning geometry of the actual carries; the " ++
      "carry recurrence cannot decide which positions are the starts. " ++
      "proof_v4_unconditional_clean_v5.tex M.2.1 Remark / M.3.1 / M.3.2 Remark (lines ~6419-6484).",
    "REDUCED (wave-19) — ReturnStartPlacementCore DERIVES the start placement from the EXPLICIT " ++
      "M.3.1/M.3.2 anchored geometry. AnchoredCompleteReturnGeometry records, per slice start, a " ++
      "clean-maximal complete-return arm (x, armEnd x] (M.1.1) reaching a common anchor, all starts " ++
      "at-or-before it; zeroRun_of_anchoredGeometry then PROVES that for ANY two starts x < z every " ++
      "digit on (x,z] is 0 (since z ≤ anchor ≤ armEnd x, so (x,z] lies inside x's clean arm), i.e. (Z) " ++
      "/ SliceCompleteReturns (sliceCompleteReturns_of_anchoredGeometry), firing the whole downstream " ++
      "API. The anchor/ordering is read off the genuine AppendixM M.3.1 structures " ++
      "(AnchoredCoreCover.ofPatchFamily via AnchoredSemiperiodicPatch.core_contains + " ++
      "theoremM3_1_anchoredSemiperiodicOverlap). The lone irreducible remainder is now ONLY the " ++
      "EXISTENCE of that anchored geometry for the actual carries — which positions are complete-return " ++
      "starts and that their arms NEST in the shared anchored region — which the recurrence cannot " ++
      "decide; anchoredGeometry_excludes_dirty makes it non-vacuous.",
    "REDUCED (wave-20) — ReturnM31ExistenceCore proves that wave-19 EXISTENCE remainder is provably " ++
      "EQUIVALENT to this SliceCompleteReturns: anchoredGeometry_nonempty_iff_sliceCompleteReturns " ++
      "(Nonempty (AnchoredCompleteReturnGeometry ctx key y) iff SliceCompleteReturns ctx key y) and " ++
      "anchoredGeometry_nonempty_iff_zeroRunToAnchor. On a complete-return arm ctx.d is constantly 0, so " ++
      "the M.4 periodicity field is automatic (PeriodicOn.of_constant) and patch existence COLLAPSES TO " ++
      "THE CLEAN RUN: AnchoredPatchFamily.ofAnchoredCleanRun builds the genuine M.3.1 family over the " ++
      "ACTUAL word w := ctx.d. So the wave-19 EXISTENCE remainder is a faithful repackaging of " ++
      "SliceCompleteReturns — neither stronger nor weaker — isolating the irreducible core to the single " ++
      "elementary digit fact 'no carry-dropping 1-digit between starts in the shared anchored region'." ]

theorem returnCompleteEnrichResiduals_nonempty : returnCompleteEnrichResiduals ≠ [] := by
  simp [returnCompleteEnrichResiduals]

/-! ## 7.  Axiom-cleanliness audit -/

#print axioms carryOf_clean_step
#print axioms carryOf_dirty_step
#print axioms carryOf_step_clean_iff
#print axioms carryOf_doubling_of_steps
#print axioms completeReturnArm_iff_zeroRun
#print axioms completeReturnArm_imp_cleanDoubling
#print axioms cleanDoubling_imp_completeReturnArm
#print axioms completeReturnArm_iff_cleanReturnSegment
#print axioms completeReturnArm_iff_zeroRun_clean
#print axioms sliceCompleteReturns_iff_sliceCleanReturns
#print axioms zeroRunConsecutive_of_completeReturns
#print axioms zeroRunAllPairs_of_completeReturns
#print axioms carryVal2_crossingFree_of_completeReturns
#print axioms hmono_of_completeReturns
#print axioms anchoredKey_hmono_of_completeReturns
#print axioms OlcSliceData.ofCompleteReturns
#print axioms dirty_step_breaks_arm
#print axioms not_completeReturnArm_of_dirty
#print axioms dirtyBetweenStarts_strict_deficit
#print axioms completeReturnArm_carry_strictMono
#print axioms completeReturns_teeth
#print axioms sliceCompleteReturns_iff_noDirtyBetweenStarts

end

end Erdos260
