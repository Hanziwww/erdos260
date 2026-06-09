import Erdos260.ReturnM31ExistenceCore
import Erdos260.FailingShellPeriodicityCore

/-!
# The value-level core of the complete-return placement `(Z)` (`SliceCompleteReturnsCore`)

This module (NEW; it edits no existing file) attacks the genuine **value-level core** of the Return
clean-carry placement `SliceCompleteReturns` (`ReturnCompleteEnrichCore`): between two consecutive
complete-return starts on an anchored slice the digit word `ctx.d` has no `1`-digit, so the carry
doubles cleanly, `R_z = 2^{z−x} R_x`.  Wave-18 derived `(Z)` from the complete-return arm structure
and sharpened the residual to `sliceCompleteReturns_iff_noDirtyBetweenStarts`; waves 19/20 packaged
the start placement through the M.3.1/M.3.2 anchored geometry
(`anchoredGeometry_nonempty_iff_sliceCompleteReturns`); wave-21 pinned the §24 carry periodicity but
showed the digit is **value-decided** (`digit_zero_iff_carry_doubles`): the carry *residue* mod `Q`
is eventually periodic while the *value* (which decides the digits) is unbounded.

## The genuinely new content: the exact dirty-weight deficit decomposition

The recurrence `R_{N+1} = 2 R_N − Q(N+1) d_{N+1}` unfolds over a block `(x, x+h]` into an **exact**
identity isolating the digit contribution as a single nonnegative integer weight:

* `dirtyCarryWeight ctx x h` — the recursively defined **dirty carry weight**
  `W_{h+1} = 2 W_h + (x+h+1) d_{x+h+1}` (`W_0 = 0`), the position-weighted digit sum on `(x, x+h]`.
* `carryOf_add_eq_doubling_sub_dirtyWeight` — **the decomposition (PROVED)**:
  `R_{x+h} = 2^h R_x − Q · W`.  The carry is the clean doubling minus exactly `Q` times the dirty
  weight, by a direct induction over the per-step recurrence.
* `carryDeficit ctx x z := 2^{z−x} R_x − R_z`, `carryDeficit_eq_Q_mul_dirtyWeight` — the doubling
  deficit is **exactly** `Q · W` (`x ≤ z`); `carryDeficit_nonneg`, `Q_dvd_carryDeficit`.

## The sharp dichotomy (residue automatic, value is the residual)

* `carryOf_add_modEq_doubling` — **the §24 residue identity, automatic and digit-insensitive**:
  `R_{x+h} ≡ 2^h R_x [ZMOD Q]` for *every* block, clean or dirty (the deficit is a multiple of `Q`).
  Re-derived from §24's `carryOf_modEq_two_pow_mul` in `carryOf_add_modEq_doubling_of_s24`.  So the
  carry residue mod `Q` cannot see a dirty digit at all.
* `carryDeficit_zero_iff_clean` — **the value identity is the placement**: `carryDeficit = 0` iff the
  segment is a `CleanReturnSegment` (iff every intervening digit is `0`).  Hence the residual is
  *exactly* the lift of the §24-automatic mod-`Q` identity `Q ∣ carryDeficit` (always true) to the
  exact integer identity `carryDeficit = 0` (the placement the recurrence cannot decide).

## The slice residual and the explicit value-level placement datum

* `cleanReturnSegment_iff_dirtyWeight_zero`, `dirtyCarryWeight_eq_zero_iff` — `W = 0` is equivalent to
  the carry-level clean doubling and to the digit-word `(Z)` on `(x, x+h]`.
* `sliceCompleteReturns_iff_consecutiveDirtyWeightZero` — **the sharp slice characterization**:
  `SliceCompleteReturns` is *equivalent* to the consecutive-start dirty weights vanishing, the value
  form of `(Z)`.
* `CleanReturnPlacement` — the explicit, documented value-level placement hypothesis (no `sorry`):
  between consecutive starts the dirty weight vanishes.  `sliceCompleteReturns_of_cleanReturnPlacement`
  and `anchoredGeometry_nonempty_of_cleanReturnPlacement` fire the whole `(Z)` downstream and the
  M.3.1/M.3.2 anchored geometry from it.

## Teeth / non-vacuity (quantitative)

* `one_le_dirtyCarryWeight_of_dirty` — a single `1`-digit on `(x, x+h]` forces `1 ≤ W`.
* `carryDeficit_ge_Q_of_dirty`, `carryOf_le_doubling_sub_Q_of_dirty` — hence the deficit is at least
  `Q`: `R_z ≤ 2^{z−x} R_x − Q`.  This is a sharpening of wave-18's strict deficit
  `R_z < 2^{z−x} R_x` to the *quantitative* drop by a full period `Q`, witnessing that a dirty digit
  is a genuine, `Q`-sized carry crossing.

## Audit verdict (the irreducible remainder, sharply characterized)

`SliceCompleteReturns` is **not** provable from the carry recurrence `R_{N+1}=2R_N−Q(N+1)d_{N+1}` and
the §24 periodicity alone: the decomposition shows the residue mod `Q` is *insensitive* to the dirty
weight (`carryOf_add_modEq_doubling` holds for every block), so the §24 residue periodicity carries no
information about whether `W = 0`.  The single irreducible remainder is exactly the **value-level
vanishing of `W` between consecutive starts** — equivalently that the §24-automatic congruence
`R_z ≡ 2^{z−x} R_x [ZMOD Q]` lifts to the exact integer equality — which is *which* positions are the
complete-return starts (the M.3.1 + M.3.2 anchored geometry of the actual carries,
`proof_v4_unconditional_clean_v5.tex` §M.3, lines ~6503–6689).  It is carried here as the explicit
`CleanReturnPlacement` field, never a `sorry`.  No `sorry`, `axiom`, `admit`, or `native_decide`; no
degenerate shortcut.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The dirty carry weight and the exact deficit decomposition

The recurrence `R_{N+1} = 2 R_N − Q(N+1) d_{N+1}` accumulates, across a block `(x, x+h]`, the
position-weighted digit sum `W_h := Σ_{i=1}^{h} 2^{h−i} (x+i) d_{x+i}`, recorded recursively as the
**dirty carry weight**.  The carry is then the clean doubling minus exactly `Q · W_h`. -/

/-- **The dirty carry weight** on `(x, x+h]`: the position-weighted digit sum
`W_{h+1} = 2 W_h + (x+h+1) d_{x+h+1}` (`W_0 = 0`).  A nonnegative integer, the genuine value-level
record of the dirty digits that the carry recurrence subtracts (each scaled by `Q`). -/
def dirtyCarryWeight (ctx : ActualFailureContext) (x : ℕ) : ℕ → ℤ
  | 0 => 0
  | h + 1 => 2 * dirtyCarryWeight ctx x h + ((x + h + 1 : ℕ) : ℤ) * (ctx.d (x + h + 1) : ℤ)

@[simp] theorem dirtyCarryWeight_zero (ctx : ActualFailureContext) (x : ℕ) :
    dirtyCarryWeight ctx x 0 = 0 := rfl

@[simp] theorem dirtyCarryWeight_succ (ctx : ActualFailureContext) (x h : ℕ) :
    dirtyCarryWeight ctx x (h + 1)
      = 2 * dirtyCarryWeight ctx x h + ((x + h + 1 : ℕ) : ℤ) * (ctx.d (x + h + 1) : ℤ) := rfl

/-- **The dirty carry weight is nonnegative (PROVED).**  Each accumulated term is a product of a
nonnegative position and a binary digit. -/
theorem dirtyCarryWeight_nonneg (ctx : ActualFailureContext) (x h : ℕ) :
    0 ≤ dirtyCarryWeight ctx x h := by
  induction h with
  | zero => simp
  | succ h ih =>
      rw [dirtyCarryWeight_succ]
      have hterm : (0 : ℤ) ≤ ((x + h + 1 : ℕ) : ℤ) * (ctx.d (x + h + 1) : ℤ) :=
        mul_nonneg (by positivity) (by positivity)
      linarith

/-- **The exact dirty-weight deficit decomposition (PROVED — the genuine value-level identity).**
Unfolding the recurrence `R_{N+1} = 2 R_N − Q(N+1) d_{N+1}` over `(x, x+h]` gives
`R_{x+h} = 2^h R_x − Q · W`: the carry is the clean doubling `2^h R_x` minus exactly `Q` times the
dirty carry weight.  Direct induction over the per-step dynamics. -/
theorem carryOf_add_eq_doubling_sub_dirtyWeight (ctx : ActualFailureContext) (x h : ℕ) :
    carryOf ctx (x + h) = 2 ^ h * carryOf ctx x - (ctx.Q : ℤ) * dirtyCarryWeight ctx x h := by
  induction h with
  | zero => simp
  | succ h ih =>
      have hstep : carryOf ctx (x + h + 1)
          = 2 * carryOf ctx (x + h)
              - (ctx.Q : ℤ) * ((x + h + 1 : ℕ) : ℤ) * (ctx.d (x + h + 1) : ℤ) := by
        unfold carryOf
        rw [integerCarry_succ]
      calc carryOf ctx (x + (h + 1))
          = carryOf ctx (x + h + 1) := by rw [Nat.add_succ]
        _ = 2 * carryOf ctx (x + h)
              - (ctx.Q : ℤ) * ((x + h + 1 : ℕ) : ℤ) * (ctx.d (x + h + 1) : ℤ) := hstep
        _ = 2 * (2 ^ h * carryOf ctx x - (ctx.Q : ℤ) * dirtyCarryWeight ctx x h)
              - (ctx.Q : ℤ) * ((x + h + 1 : ℕ) : ℤ) * (ctx.d (x + h + 1) : ℤ) := by rw [ih]
        _ = 2 ^ (h + 1) * carryOf ctx x - (ctx.Q : ℤ) * dirtyCarryWeight ctx x (h + 1) := by
              rw [dirtyCarryWeight_succ]; ring

/-! ## 2.  The clean-doubling / zero-run characterizations of `W = 0`

The carry doubles cleanly `R_{x+h} = 2^h R_x` exactly when the dirty weight vanishes (since `Q > 0`),
which — through the wave-17 envelope `carryOf_doubling_iff_zeroRun` — is exactly the digit-word `(Z)`
on `(x, x+h]`. -/

/-- **Clean doubling ⟺ `W = 0` (PROVED).**  `R_{x+h} = 2^h R_x` iff the dirty carry weight vanishes;
the deficit `Q · W` is `0` iff `W = 0` because `Q > 0`. -/
theorem cleanDoubling_iff_dirtyWeight_zero (ctx : ActualFailureContext) (x h : ℕ) :
    carryOf ctx (x + h) = 2 ^ h * carryOf ctx x ↔ dirtyCarryWeight ctx x h = 0 := by
  rw [carryOf_add_eq_doubling_sub_dirtyWeight]
  have hQ : (ctx.Q : ℤ) ≠ 0 := by exact_mod_cast ctx.hQ.ne'
  constructor
  · intro hh
    have hz : (ctx.Q : ℤ) * dirtyCarryWeight ctx x h = 0 := by linarith
    rcases mul_eq_zero.1 hz with h1 | h2
    · exact absurd h1 hQ
    · exact h2
  · intro hw
    rw [hw]; ring

/-- **`W = 0` ⟺ the digit-word `(Z)` on `(x, x+h]` (PROVED).**  Composing the clean-doubling
characterization with the wave-17 doubling envelope `carryOf_doubling_iff_zeroRun`. -/
theorem dirtyCarryWeight_eq_zero_iff (ctx : ActualFailureContext) (x h : ℕ) :
    dirtyCarryWeight ctx x h = 0 ↔ ∀ j, x < j → j ≤ x + h → ctx.d j = 0 := by
  rw [← cleanDoubling_iff_dirtyWeight_zero]
  exact carryOf_doubling_iff_zeroRun ctx x h

/-- **`CleanReturnSegment` ⟺ `W = 0` (PROVED).**  The carry-level complete return
`R_z = 2^{z−x} R_x` is exactly the vanishing of the dirty weight `dirtyCarryWeight ctx x (z−x)`. -/
theorem cleanReturnSegment_iff_dirtyWeight_zero (ctx : ActualFailureContext) {x z : ℕ}
    (hxz : x ≤ z) :
    CleanReturnSegment ctx x z ↔ dirtyCarryWeight ctx x (z - x) = 0 := by
  unfold CleanReturnSegment
  have hzx : x + (z - x) = z := by omega
  have key := cleanDoubling_iff_dirtyWeight_zero ctx x (z - x)
  rw [hzx] at key
  exact key

/-! ## 3.  The §24 residue identity is automatic and digit-insensitive

The doubling deficit is a multiple of `Q`, so the carry residue mod `Q` doubles cleanly across
*every* block, clean or dirty.  This is the local §24 statement, and it carries no information about
whether the segment is clean — exactly why the residue periodicity (wave-21) cannot decide the
placement. -/

/-- **The §24 residue identity, automatic (PROVED).**  `R_{x+h} ≡ 2^h R_x [ZMOD Q]` for *every*
block — the deficit `Q · W` vanishes mod `Q` regardless of the digits.  The carry residue is
insensitive to dirty digits. -/
theorem carryOf_add_modEq_doubling (ctx : ActualFailureContext) (x h : ℕ) :
    carryOf ctx (x + h) ≡ 2 ^ h * carryOf ctx x [ZMOD (ctx.Q : ℤ)] := by
  refine Int.modEq_iff_dvd.mpr ?_
  rw [carryOf_add_eq_doubling_sub_dirtyWeight]
  exact ⟨dirtyCarryWeight ctx x h, by ring⟩

/-- **The same residue identity, re-derived from the §24 root (PROVED).**  From wave-21's
`carryOf_modEq_two_pow_mul` (`R_N ≡ 2^N · P [ZMOD Q]`): `R_{x+h} ≡ 2^{x+h} P = 2^h (2^x P) ≡ 2^h R_x`.
This cross-validates the decomposition against the §24 geometric-orbit form. -/
theorem carryOf_add_modEq_doubling_of_s24 (ctx : ActualFailureContext) (x h : ℕ) :
    carryOf ctx (x + h) ≡ 2 ^ h * carryOf ctx x [ZMOD (ctx.Q : ℤ)] := by
  have hx := (carryOf_modEq_two_pow_mul ctx x).mul_left ((2 : ℤ) ^ h)
  have hxh := carryOf_modEq_two_pow_mul ctx (x + h)
  have heq : (2 : ℤ) ^ (x + h) * ctxNum ctx = 2 ^ h * (2 ^ x * ctxNum ctx) := by
    rw [pow_add]; ring
  rw [heq] at hxh
  exact hxh.trans hx.symm

/-! ## 4.  The carry deficit: the sharp residue/value dichotomy

The doubling deficit `carryDeficit = 2^{z−x} R_x − R_z` is exactly `Q · W`: a nonnegative multiple
of `Q`.  The mod-`Q` vanishing `Q ∣ carryDeficit` is automatic (§24, residue level); the exact
vanishing `carryDeficit = 0` is the placement `(Z)` (value level). -/

/-- **The carry doubling deficit** `2^{z−x} R_x − R_z`. -/
def carryDeficit (ctx : ActualFailureContext) (x z : ℕ) : ℤ :=
  2 ^ (z - x) * carryOf ctx x - carryOf ctx z

/-- **The deficit is exactly `Q · W` (PROVED).**  For `x ≤ z` the doubling deficit equals `Q` times
the dirty carry weight `dirtyCarryWeight ctx x (z−x)`. -/
theorem carryDeficit_eq_Q_mul_dirtyWeight (ctx : ActualFailureContext) {x z : ℕ} (hxz : x ≤ z) :
    carryDeficit ctx x z = (ctx.Q : ℤ) * dirtyCarryWeight ctx x (z - x) := by
  unfold carryDeficit
  have hzx : x + (z - x) = z := by omega
  have hdec := carryOf_add_eq_doubling_sub_dirtyWeight ctx x (z - x)
  rw [hzx] at hdec
  rw [hdec]; ring

/-- **The deficit is a multiple of `Q` (PROVED) — the §24 residue identity, deficit form.** -/
theorem Q_dvd_carryDeficit (ctx : ActualFailureContext) {x z : ℕ} (hxz : x ≤ z) :
    (ctx.Q : ℤ) ∣ carryDeficit ctx x z :=
  ⟨dirtyCarryWeight ctx x (z - x), carryDeficit_eq_Q_mul_dirtyWeight ctx hxz⟩

/-- **The deficit is nonnegative (PROVED).**  The carry never exceeds its clean doubling. -/
theorem carryDeficit_nonneg (ctx : ActualFailureContext) {x z : ℕ} (hxz : x ≤ z) :
    0 ≤ carryDeficit ctx x z := by
  rw [carryDeficit_eq_Q_mul_dirtyWeight ctx hxz]
  exact mul_nonneg (by positivity) (dirtyCarryWeight_nonneg ctx x (z - x))

/-- **The value-level placement is exactly `carryDeficit = 0` (PROVED — the sharp dichotomy).**  The
doubling deficit vanishes iff the segment is a `CleanReturnSegment` (iff every intervening digit is
`0`).  Combined with `Q_dvd_carryDeficit` (the mod-`Q` vanishing is automatic), this isolates the
residual to the lift from the §24-automatic congruence to the exact integer equality. -/
theorem carryDeficit_zero_iff_clean (ctx : ActualFailureContext) {x z : ℕ} (hxz : x ≤ z) :
    carryDeficit ctx x z = 0 ↔ CleanReturnSegment ctx x z := by
  rw [carryDeficit_eq_Q_mul_dirtyWeight ctx hxz, cleanReturnSegment_iff_dirtyWeight_zero ctx hxz]
  have hQ : (ctx.Q : ℤ) ≠ 0 := by exact_mod_cast ctx.hQ.ne'
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h1 | h2
    · exact absurd h1 hQ
    · exact h2
  · intro h; rw [h]; ring

/-! ## 5.  Teeth and non-vacuity (quantitative)

A single `1`-digit forces the dirty weight to be at least `1`, hence the deficit to be at least a full
period `Q`: the carry drops by at least `Q` below its clean doubling.  This sharpens wave-18's strict
`R_z < 2^{z−x} R_x` to a quantitative `Q`-sized drop. -/

/-- **A `1`-digit forces `1 ≤ W` (PROVED).**  If any digit on `(x, x+h]` is `1`, the dirty carry
weight is at least `1` (it is nonnegative and, by `dirtyCarryWeight_eq_zero_iff`, nonzero). -/
theorem one_le_dirtyCarryWeight_of_dirty (ctx : ActualFailureContext) {x h j : ℕ}
    (hj1 : x < j) (hj2 : j ≤ x + h) (hdirty : ctx.d j = 1) :
    1 ≤ dirtyCarryWeight ctx x h := by
  have hpos := dirtyCarryWeight_nonneg ctx x h
  have hne : dirtyCarryWeight ctx x h ≠ 0 := by
    intro h0
    have := (dirtyCarryWeight_eq_zero_iff ctx x h).1 h0 j hj1 hj2
    rw [hdirty] at this
    exact one_ne_zero this
  omega

/-- **A `1`-digit forces a deficit of at least `Q` (PROVED).**  Any `1`-digit on `(x, z]` makes the
doubling deficit at least a full period: `Q ≤ carryDeficit ctx x z`. -/
theorem carryDeficit_ge_Q_of_dirty (ctx : ActualFailureContext) {x z j : ℕ} (hxz : x ≤ z)
    (hj1 : x < j) (hj2 : j ≤ z) (hdirty : ctx.d j = 1) :
    (ctx.Q : ℤ) ≤ carryDeficit ctx x z := by
  rw [carryDeficit_eq_Q_mul_dirtyWeight ctx hxz]
  have hw : 1 ≤ dirtyCarryWeight ctx x (z - x) :=
    one_le_dirtyCarryWeight_of_dirty ctx hj1 (by omega) hdirty
  have hQ0 : (0 : ℤ) ≤ (ctx.Q : ℤ) := by positivity
  calc (ctx.Q : ℤ) = (ctx.Q : ℤ) * 1 := by ring
    _ ≤ (ctx.Q : ℤ) * dirtyCarryWeight ctx x (z - x) := mul_le_mul_of_nonneg_left hw hQ0

/-- **The quantitative strict carry drop (PROVED).**  A `1`-digit on `(x, z]` forces the carry a full
period below its clean doubling: `R_z ≤ 2^{z−x} R_x − Q`.  This is wave-18's
`dirtyBetweenStarts_strict_deficit` sharpened to a `Q`-sized drop. -/
theorem carryOf_le_doubling_sub_Q_of_dirty (ctx : ActualFailureContext) {x z j : ℕ} (hxz : x ≤ z)
    (hj1 : x < j) (hj2 : j ≤ z) (hdirty : ctx.d j = 1) :
    carryOf ctx z ≤ 2 ^ (z - x) * carryOf ctx x - (ctx.Q : ℤ) := by
  have h := carryDeficit_ge_Q_of_dirty ctx hxz hj1 hj2 hdirty
  unfold carryDeficit at h
  linarith

/-! ## 6.  The slice residual and the explicit value-level placement datum

`SliceCompleteReturns` is *equivalent* to the consecutive-start dirty weights vanishing — the value
form of `(Z)`.  The explicit, documented placement hypothesis `CleanReturnPlacement` (no `sorry`)
fires the whole `(Z)` downstream and the M.3.1/M.3.2 anchored geometry. -/

/-- **The slice residual ⟺ consecutive dirty weights vanish (PROVED — the sharp characterization).**
`SliceCompleteReturns` is *equivalent* to: between consecutive OLC starts the dirty carry weight
`dirtyCarryWeight ctx x (z−x)` is `0`.  This is the value form of the wave-18 residual `(Z)`. -/
theorem sliceCompleteReturns_iff_consecutiveDirtyWeightZero (ctx : ActualFailureContext)
    (key : ℕ → ℕ) (y : ℕ) :
    SliceCompleteReturns ctx key y ↔
      ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
        (∀ c ∈ olcSlice ctx key y, x < c → z ≤ c) →
          dirtyCarryWeight ctx x (z - x) = 0 := by
  rw [sliceCompleteReturns_iff_sliceCleanReturns]
  constructor
  · intro H x hx z hz hxz hcons
    exact (cleanReturnSegment_iff_dirtyWeight_zero ctx (le_of_lt hxz)).1 (H x hx z hz hxz hcons)
  · intro H x hx z hz hxz hcons
    exact (cleanReturnSegment_iff_dirtyWeight_zero ctx (le_of_lt hxz)).2 (H x hx z hz hxz hcons)

/-- **The explicit value-level complete-return placement datum.**

The single irreducible remainder, isolated to its sharpest value form (no `sorry`): between every
pair of *consecutive* OLC complete-return starts on the slice, the dirty carry weight vanishes —
equivalently (`carryDeficit_zero_iff_clean`) the §24-automatic congruence `R_z ≡ 2^{z−x} R_x [ZMOD Q]`
lifts to the exact integer equality `R_z = 2^{z−x} R_x`.  This is *which* positions are the
complete-return starts (the M.3.1 + M.3.2 anchored geometry of the actual carries), which the carry
recurrence cannot decide. -/
structure CleanReturnPlacement (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ) : Prop where
  /-- **(Z), value form.**  Between consecutive starts the dirty carry weight is `0`. -/
  dirtyWeight_zero : ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
    (∀ c ∈ olcSlice ctx key y, x < c → z ≤ c) →
      dirtyCarryWeight ctx x (z - x) = 0

/-- **The placement datum forces `SliceCompleteReturns` (PROVED).** -/
theorem sliceCompleteReturns_of_cleanReturnPlacement (ctx : ActualFailureContext) (key : ℕ → ℕ)
    (y : ℕ) (H : CleanReturnPlacement ctx key y) : SliceCompleteReturns ctx key y :=
  (sliceCompleteReturns_iff_consecutiveDirtyWeightZero ctx key y).2 H.dirtyWeight_zero

/-- **The placement datum forces the M.3.1/M.3.2 anchored geometry (PROVED).**  Through wave-20's
`anchoredGeometry_nonempty_iff_sliceCompleteReturns`, the value-level placement yields the full
anchored complete-return geometry for the actual carries. -/
theorem anchoredGeometry_nonempty_of_cleanReturnPlacement (ctx : ActualFailureContext)
    (key : ℕ → ℕ) (y : ℕ) (H : CleanReturnPlacement ctx key y) :
    Nonempty (AnchoredCompleteReturnGeometry ctx key y) :=
  (anchoredGeometry_nonempty_iff_sliceCompleteReturns ctx key y).2
    (sliceCompleteReturns_of_cleanReturnPlacement ctx key y H)

/-- **Conversely, `SliceCompleteReturns` gives the placement datum (PROVED).**  So the explicit
value-level datum is a faithful repackaging of the wave-18 residual, neither stronger nor weaker. -/
theorem cleanReturnPlacement_of_sliceCompleteReturns (ctx : ActualFailureContext) (key : ℕ → ℕ)
    (y : ℕ) (H : SliceCompleteReturns ctx key y) : CleanReturnPlacement ctx key y :=
  ⟨(sliceCompleteReturns_iff_consecutiveDirtyWeightZero ctx key y).1 H⟩

/-! ## 7.  Honest residual inventory -/

/-- The precise status of the complete-return placement `(Z)` after isolating its value-level core. -/
def sliceCompleteReturnsResiduals : List String :=
  [ "GOAL (wave-22) — attack the value-level core of SliceCompleteReturns: between two consecutive " ++
      "complete-return starts the digit word ctx.d has no 1-digit, so the carry doubles cleanly " ++
      "R_z = 2^(z-x) R_x. Mechanism: the complete-return arm forces a clean doubled carry; combined " ++
      "with §24 periodicity (digit value-decided, digit_zero_iff_carry_doubles) and the M.3.1 " ++
      "anchored overlap the inter-start region is clean. proof_v4_unconditional_clean_v5.tex §M.3 " ++
      "(lines ~6503-6689).",
    "CLOSED (the exact dirty-weight deficit decomposition, the genuine value-level identity) — " ++
      "dirtyCarryWeight (W_{h+1} = 2 W_h + (x+h+1) d_{x+h+1}, W_0 = 0) records the position-weighted " ++
      "digit sum on (x,x+h]; carryOf_add_eq_doubling_sub_dirtyWeight: R_{x+h} = 2^h R_x - Q W, the " ++
      "carry is the clean doubling minus exactly Q times the dirty weight (direct induction over the " ++
      "recurrence R_{N+1} = 2 R_N - Q(N+1) d_{N+1}). dirtyCarryWeight_nonneg.",
    "CLOSED (the residue/value dichotomy, the sharp isolation) — carryOf_add_modEq_doubling: " ++
      "R_{x+h} ≡ 2^h R_x [ZMOD Q] for EVERY block, clean or dirty (deficit is a multiple of Q), so " ++
      "the §24 residue cannot see a dirty digit; re-derived from §24 carryOf_modEq_two_pow_mul in " ++
      "carryOf_add_modEq_doubling_of_s24. carryDeficit = 2^(z-x) R_x - R_z = Q W " ++
      "(carryDeficit_eq_Q_mul_dirtyWeight), nonneg, Q | carryDeficit (automatic), and " ++
      "carryDeficit_zero_iff_clean: carryDeficit = 0 <=> CleanReturnSegment. So the residual is the " ++
      "lift of the §24-automatic mod-Q identity to the exact integer equality.",
    "CLOSED (clean-doubling / zero-run / slice characterizations) — cleanDoubling_iff_dirtyWeight_zero " ++
      "(R_{x+h} = 2^h R_x <=> W = 0), dirtyCarryWeight_eq_zero_iff (W = 0 <=> (Z) on (x,x+h], via the " ++
      "wave-17 envelope carryOf_doubling_iff_zeroRun), cleanReturnSegment_iff_dirtyWeight_zero, and " ++
      "sliceCompleteReturns_iff_consecutiveDirtyWeightZero: SliceCompleteReturns <=> the " ++
      "consecutive-start dirty weights vanish (the value form of (Z)).",
    "NON-VACUOUS / TEETH (quantitative) — one_le_dirtyCarryWeight_of_dirty (a 1-digit on (x,x+h] " ++
      "forces 1 <= W); carryDeficit_ge_Q_of_dirty (Q <= carryDeficit); carryOf_le_doubling_sub_Q_of_" ++
      "dirty (R_z <= 2^(z-x) R_x - Q). This sharpens wave-18's strict deficit R_z < 2^(z-x) R_x to a " ++
      "quantitative Q-sized drop: a dirty digit is a genuine, full-period carry crossing.",
    "OPEN (the single irreducible remainder, pinned to the value-level vanishing of W) — " ++
      "CleanReturnPlacement: between consecutive starts the dirty carry weight is 0 (equivalently the " ++
      "§24-automatic congruence R_z ≡ 2^(z-x) R_x [ZMOD Q] lifts to the exact integer equality). " ++
      "sliceCompleteReturns_of_cleanReturnPlacement and anchoredGeometry_nonempty_of_cleanReturnPlacement " ++
      "fire the whole (Z) downstream and the M.3.1/M.3.2 geometry; " ++
      "cleanReturnPlacement_of_sliceCompleteReturns shows it is a faithful repackaging. This is WHICH " ++
      "positions are the complete-return starts (the M.3.1 + M.3.2 anchored geometry of the actual " ++
      "carries), which the recurrence R_{N+1} = 2 R_N - Q(N+1) d_{N+1} CANNOT decide: the decomposition " ++
      "shows the residue mod Q is insensitive to W, so §24 periodicity carries no information about it. " ++
      "proof_v4_unconditional_clean_v5.tex Lemma M.3.1 / M.3.2 + Remarks (lines ~6503-6689)." ]

theorem sliceCompleteReturnsResiduals_nonempty : sliceCompleteReturnsResiduals ≠ [] := by
  simp [sliceCompleteReturnsResiduals]

/-! ## 8.  Axiom-cleanliness audit -/

#print axioms dirtyCarryWeight_nonneg
#print axioms carryOf_add_eq_doubling_sub_dirtyWeight
#print axioms cleanDoubling_iff_dirtyWeight_zero
#print axioms dirtyCarryWeight_eq_zero_iff
#print axioms cleanReturnSegment_iff_dirtyWeight_zero
#print axioms carryOf_add_modEq_doubling
#print axioms carryOf_add_modEq_doubling_of_s24
#print axioms carryDeficit_eq_Q_mul_dirtyWeight
#print axioms Q_dvd_carryDeficit
#print axioms carryDeficit_nonneg
#print axioms carryDeficit_zero_iff_clean
#print axioms one_le_dirtyCarryWeight_of_dirty
#print axioms carryDeficit_ge_Q_of_dirty
#print axioms carryOf_le_doubling_sub_Q_of_dirty
#print axioms sliceCompleteReturns_iff_consecutiveDirtyWeightZero
#print axioms sliceCompleteReturns_of_cleanReturnPlacement
#print axioms anchoredGeometry_nonempty_of_cleanReturnPlacement
#print axioms cleanReturnPlacement_of_sliceCompleteReturns

end

end Erdos260
