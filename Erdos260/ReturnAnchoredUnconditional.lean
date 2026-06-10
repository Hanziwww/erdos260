import Erdos260.ReturnPerSliceClosure
import Erdos260.P9V3Closure
import Erdos260.CNLMultiChargeUnconditional

/-!
# Return / Class 4 — the anchored per-slice atom, maximally closed (`ReturnAnchoredUnconditional`)

This module (NEW; it edits no existing file) attacks the remaining Return/Class-4 gap recorded by
`ReturnPerSliceClosure`: the per-ctx anchored family `ReturnClass4AnchoredSeed ctx` (equivalently the
sharper `ReturnClass4AnchoredCore ctx`) whose fields are
`key / family / hbound / hgapDiv / class4Interior (hContain) / hnumeric`.

## What is CLOSED UNCONDITIONALLY here (new proved content)

* **`hbound` — the M.2.1 carry-side shell bound, PROVED for the actual fibre**
  (`returnFibre_carryVal2_le_shell`): for every class-4 start `k ∈ olcFibre ctx`,
  `carryVal2 ctx k ≤ ctx.shell.X`.  Proof chain, all read off `ctx`:
  the start set is the dyadic shell index window (`n24Starts_eq_window`), so `k ≤ a k ≤ 2X`
  (`StrictMono.le_apply`, `HitSequence.a_le_two_mul_of_lt_add_card`); the actual integer carry obeys
  the linear envelope `R_k ≤ Q(k+2)` (`integerCarry_bounds_of_rational_value`); hence
  `2^{v₂(R_k)} ≤ R_k ≤ Q(2X+2) ≤ 4QX ≤ 2^{B+L}` (`carryB_spec` via
  `aboveCarryThreshold_provides_windowScale`), so `carryVal2 k ≤ B + L ≤ 2L ≤ 2^L = X`.
  This removes `hbound` from the residual surface for **every** slice key.

* **`family` — the anchored M.3.1 family is now CONSTRUCTED, not assumed**
  (`returnCleanRunOfZeroData` + the existing audited bridge
  `AnchoredLongReturnFamily.ofAnchoredCleanRun`): from the digit-level **(Z) zero-run data** on a
  slice (all-zero digits between slice starts, plus one clean step past the top start), the
  anchored clean run with anchor `= max(slice) + 1` and the full
  `AnchoredLongReturnFamily ctx key y` are produced.  The load-bearing digit content sits in the
  M.1.1 complete-return arms (`R_{N+1} = 2R_N` along the run, manuscript line ~6680); nothing is
  empty, all-zero-factory, or vacuous — the (Z) facts are genuine constraints on `ctx.d`.

## The OBSTRUCTION theorems (why goal "construct the seed from nothing" is impossible)

* `anchoredLongReturnFamily_forces_clean_step` /
  `anchoredSeed_forces_clean_step` / `anchoredCore_forces_clean_step`:
  **any** `ReturnClass4AnchoredSeed ctx` (for any key) forces the digit-level fact
  `∀ k ∈ olcFibre ctx, ctx.d (k+1) = 0`.  Class-4 fibre membership is a hit-gap/orbit condition
  (`genuineChargeRoute`, `towerClsOfShell`, `returnCls`) that does not by itself determine the
  digit `ctx.d (k+1)`, so no bookkeeping-only term of type
  `∀ ctx, ReturnClass4AnchoredSeed ctx` can exist: every such term carries genuine M.1.1/(Z)
  digit content.  (The seed's interface is *sound*: it really transports manuscript geometry.)
* `anchoredSeed_forces_interior`: the seed also forces the class-4 active-window interior
  condition `k + r + 1 < firstIndexAbove X + |supportShell|`, which is false for the top `r+1`
  window starts in general (`windowContainment_top_start_fails`), hence also not bookkeeping.

## The SHARP two-sided reduction (the new frontier, faithful — no loss, no overclaim)

`ReturnAnchoredZResidual ctx` carries exactly the genuinely-undischarged data:

* `hzero` — the **(Z)** all-pairs zero-run on each slice (proof_v4 §M.1.1/M.3, the documented
  "RETURN (Z)" frontier of the V3 wave-16 inventory);
* `hcleanStep` — one clean step past each class-4 start (`ctx.d (k+1) = 0`, M.1.1 trace);
* `hgapDiv` — the self-referential dyadic spacing `2^{carryVal2 x} ∣ (z − x)` of consecutive
  slice starts (the G.7/J.4 lift congruence, manuscript line ~6536);
* `class4Interior` — the active-window interior (the K.1 endpoint boundary term);
* `hnumeric` — the matched `M_L·X` smallness `(#keys)·liftLevelBound X·returnDyadicMult ≤ c⋆ξX/6`.

`ReturnAnchoredZResidual.toAnchoredCore` **constructs** the full anchored core from it (family
built, `hbound` proved); `ReturnAnchoredZResidual.ofAnchoredCore` / `.ofAnchoredSeed` recover the
residual from any core/seed.  `nonempty_anchoredCore_iff_zResidual` and
`nonempty_anchoredSeed_iff_zResidual` prove the reduction is an **equivalence**: the Z-residual is
*exactly* the remaining Return atom — strictly smaller than the previous frontier
(`family` and `hbound` are gone), and provably not smaller than possible.

`ReturnDiagonalZResidual` is the singleton-key (`key = id`) specialisation: `hzero`/`hgapDiv`
become theorems (no pairs share a slice), leaving only
`hcleanStep / class4Interior / hnumeric` — at the price of the *strongest* numeric
(`#keys = |olcFibre|`); it is recorded as a sufficient route, not as the manuscript-faithful one.

## The class-4 fibre is PINNED (new unconditional content of this pass)

* **The band-2 pin** (`class4Fibre_canonGap_eq`, `mem_class4Fibre_iff`,
  `class4Fibre_eq_pinnedFilter`): on the genuine first-obstruction route the class-4 fibre IS the
  window filter `{k ∈ starts : 129L + 64 ≤ 64·gapWindow(k) ∧ canonGap q K_k = 2}` — the exact
  analogue of the class-1 `mem_class1Fibre_iff`.  The exceptional `cnlTail ∧ returnCls = 2`
  route branch forces `k = 0` (`class4_exceptional_k_eq_zero`), and `0` is never a carry-window
  start (`zero_notMem_n24Starts`, from `firstIndexAbove X ≥ 1`): only the L.3.1 `returnPkg` band
  survives on the actual fibre.  Orbit corollaries: `2K_k ≤ q < 4K_k` (`class4Fibre_orbit_band`),
  successor pin `K_{k+1} = 4K_k − q` (`class4Fibre_orbit_step`), `q ≥ 3` on any shell with a
  class-4 start (`modulus_ge_three_of_class4Fibre_nonempty`, `class4Fibre_empty_of_modulus_lt_three`).

* **The K.1 gate dichotomy** (`class4Fibre_window_overrun`, `class4Interior_iff_fibre_empty`,
  `zResidual_iff_class4Fibre_empty`): under the numeric gate `64(r+1)(L+B+1) < 129L + 64` (the
  same gate as class 1; automatic on every `r = 0` shell, i.e. all `L ≤ 15420`), every class-4
  start overruns the shell-window top, so the K.1 interior field holds **iff the fibre is
  empty** — hence `Nonempty (ReturnAnchoredZResidual ctx) ↔ olcFibre ctx = ∅` on gated shells
  (also in seed/core form), and on `r = 0` shells the whole Return atom is the single membership
  fact `top ∉ olcFibre ctx` (`zResidual_iff_top_notMem_of_r_eq_zero`).

* **`hgapDiv` CLOSED on the self-referential key** (`returnSelfRefKey`,
  `returnSelfRefKey_gapDiv`, `ReturnSelfRefZResidual`): with the manuscript M.2.1 key
  `k ↦ (carryVal2 k, k mod 2^{carryVal2 k})` (level × residue, the self-referential congruence,
  proof_v4 ~6536), same-slice starts are congruent mod `2^{carryVal2 x}`, so
  `2^{carryVal2 x} ∣ (z − x)` is a THEOREM.  `ReturnSelfRefZResidual` carries only
  `hzero / hcleanStep / class4Interior / hnumeric` and bridges into the full Z-residual.

* **`hnumeric` CLOSED on `r = 0` shells** (`returnDyadicMult_eq_zero_of_r_eq_zero`,
  `return_hnumeric_of_r_eq_zero`): `r = 0` gives `(r+1)·g₀ − T = (L+B+1) − (2L+1) ≤ −25 < 0`
  from the largeness gate `B + 25 ≤ L`, so the matched multiplier vanishes and the `M_L·X`
  smallness holds for EVERY key.

* **The named empty-fibre residual** (`Class4FibreEmpty`, `returnZResidualsOfClass4FibreEmpty`,
  `erdos260_p9V3_ofClass4FibreEmpty`): the per-ctx Prop `olcFibre ctx = ∅`, carried as an
  EXPLICIT hypothesis (mirror of the CNL `Class1FibreEmpty`), supplies the full Z-residual family
  and the P9/V3 endpoint.  Under the gate it is per-ctx EQUIVALENT to the Z-residual
  (`class4FibreEmpty_iff_zResiduals_of_gate`) — the empty-fibre route is then not a shortcut but
  the sharp truth.  No unconditional closure of `Class4FibreEmpty` is claimed.

## Wiring (the V3/P9 Return field is supplied by the Z-residual)

`returnAnchoredSeedOfZ` / `returnChargeOfZResiduals` / `returnPerSliceCoreResidualOfZ` /
`returnPerSliceClosureResidualOfZ` / `returnFloorOfZ` feed the existing
`ReturnPerSliceClosure` bridges, and `P9V3RunResidual.ofReturnZ` + `erdos260_p9V3_ofReturnZ`
instantiate the Return field of `P9V3RunResidual` from a Z-residual family, reaching
`Erdos260Statement` together with the other five class atoms.

No `sorry`, `axiom`, `admit`, or `native_decide`.  No all-zero factory data, no empty or vacuous
return witness: the constructed families run on the genuine carries (`CompleteReturnArm` =
clean doubling of the actual integer carry), `ReturnAnchoredZResidual.ofEmptyFibre` is consumed
by endpoints ONLY through the explicitly named hypothesis `Class4FibreEmpty` (and is, under the
proved gate, the `mpr` of an equivalence — not a vacuity shortcut), and the forbidden
`genuineReturnShellInputTrivial` route is not touched.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  `hbound` CLOSED — the M.2.1 carry-side shell bound on the actual class-4 fibre

The class-4 fibre lives in the dyadic shell index window, every window index is at most its own
hit value `a k ≤ 2X`, and the actual integer carry obeys the linear envelope `R_k ≤ Q(k+2)`; the
2-adic valuation is therefore at most `B + L ≤ X`.  All parameters are read off `ctx`. -/

/-- **Every class-4 start is at most `2X`.**  Window membership (`n24Starts_eq_window`) gives
`k < firstIndexAbove X + |supportShell|`, the hit value there is `≤ 2X`
(`HitSequence.a_le_two_mul_of_lt_add_card`), and the strictly monotone hit enumeration satisfies
`k ≤ a k` (`StrictMono.le_apply`). -/
theorem returnFibre_le_two_mul (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ olcFibre ctx) : k ≤ 2 * ctx.shell.X := by
  have hwin := mem_window_of_mem_fibre ctx (genuineChargeRoute ctx) 4 hk
  have hak : ctx.n24CarryData.a k ≤ 2 * ctx.shell.X :=
    ctx.n24CarryData.carry.hits.a_le_two_mul_of_lt_add_card ctx.shell.X hwin.2
  have hka : k ≤ ctx.n24CarryData.a k := ctx.n24CarryData.carry.hits.strict.le_apply
  omega

/-- **The M.2.1 carry-side shell bound, PROVED unconditionally on the class-4 fibre.**
For every `k ∈ olcFibre ctx`, `carryVal2 ctx k ≤ ctx.shell.X`.  This discharges the `hbound`
field of `ReturnClass4AnchoredCore`/`ReturnClass4AnchoredSeed` for **every** slice key:
`2^{v₂(R_k)} ≤ R_k ≤ Q(k+2) ≤ Q(2X+2) ≤ 4QX ≤ 2^B·2^L`, so `carryVal2 k ≤ B + L ≤ 2L ≤ 2^L = X`
(`integerCarry_bounds_of_rational_value`, `carryB_spec`, `aboveCarryThreshold`). -/
theorem returnFibre_carryVal2_le_shell (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ olcFibre ctx) : carryVal2 ctx k ≤ ctx.shell.X := by
  -- the dyadic exponent and the carry-threshold window scale
  set L := Classical.choose ctx.shell.hXdyadic with hLdef
  have hXL : ctx.shell.X = 2 ^ L := Classical.choose_spec ctx.shell.hXdyadic
  have hthr : ctx.shell.aboveCarryThreshold :=
    aboveCarryThreshold_of_manuscriptLargeThreshold_le ctx.shell ctx.shell_large
  obtain ⟨hQ4, hB25⟩ := aboveCarryThreshold_provides_windowScale hXL hthr
  set B := carryB ctx.shell.Q with hBdef
  have hQ4' : ctx.Q * 4 ≤ 2 ^ B := hQ4
  -- the fibre start is window-bounded
  have hk2X : k ≤ 2 * ctx.shell.X := returnFibre_le_two_mul ctx hk
  have hXpos : 1 ≤ ctx.shell.X := returnShellX_pos ctx
  -- the actual integer carry obeys the linear envelope `R_k ≤ Q(k+2)`
  have hbounds := integerCarry_bounds_of_rational_value
    (Q := ctx.Q) (P := ctxNum ctx) (d := ctx.d) k ctx.hQ ctx.hd (ctxEta ctx)
  have hRleZ : carryOf ctx k ≤ ((ctx.Q * (k + 2) : ℕ) : ℤ) := by
    have h2 : carryOf ctx k ≤ (ctx.Q : ℤ) * ((k + 2 : ℕ) : ℤ) := hbounds.2
    calc carryOf ctx k ≤ (ctx.Q : ℤ) * ((k + 2 : ℕ) : ℤ) := h2
      _ = ((ctx.Q * (k + 2) : ℕ) : ℤ) := by push_cast; ring
  have hRle : (carryOf ctx k).toNat ≤ ctx.Q * (k + 2) := Int.toNat_le.mpr hRleZ
  -- chain the envelope to the dyadic scale `2^(B+L)`
  have hchain : (carryOf ctx k).toNat ≤ 2 ^ (B + L) := by
    have h1 : ctx.Q * (k + 2) ≤ ctx.Q * (4 * ctx.shell.X) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : ctx.Q * (4 * ctx.shell.X) = (ctx.Q * 4) * ctx.shell.X := by ring
    have h3 : (ctx.Q * 4) * ctx.shell.X ≤ 2 ^ B * ctx.shell.X :=
      Nat.mul_le_mul_right _ hQ4'
    have h4 : 2 ^ B * ctx.shell.X = 2 ^ (B + L) := by rw [hXL, ← pow_add]
    calc (carryOf ctx k).toNat ≤ ctx.Q * (k + 2) := hRle
      _ ≤ ctx.Q * (4 * ctx.shell.X) := h1
      _ = (ctx.Q * 4) * ctx.shell.X := h2
      _ ≤ 2 ^ B * ctx.shell.X := h3
      _ = 2 ^ (B + L) := h4
  -- the 2-adic valuation is logarithmic
  have hv : carryVal2 ctx k ≤ B + L := by
    have hlog := carryVal2_le_log ctx k
    have hmono := Nat.log_mono_right (b := 2) hchain
    rw [Nat.log_pow Nat.one_lt_two] at hmono
    omega
  -- and `B + L ≤ 2L − 25 + 25 ≤ 2L ≤ 2^L = X`
  have h2L : 2 * L ≤ 2 ^ L := by
    have hp : L - 1 < 2 ^ (L - 1) := Nat.lt_two_pow_self
    have hstep : 2 ^ (L - 1) * 2 = 2 ^ L := by
      rw [← pow_succ]
      congr 1
      omega
    omega
  have hfin : B + L ≤ ctx.shell.X := by
    rw [hXL]
    omega
  omega

/-! ## 2.  The OBSTRUCTION theorems — the anchored interface forces digit-level content

Any anchored long-return family on a slice forces a clean carry step (`d (x+1) = 0`) at each of
its starts: the M.1.1 arm reaches past the start into the anchored core, and a complete-return
step is *exactly* a clean doubling of the actual integer carry.  Hence the anchored seed/core can
never be produced by bookkeeping alone — every term carries genuine (Z)/M.1.1 digit content. -/

/-- **The anchored family forces a clean step at every slice start.**
`anchoredLongReturnFamily_arm_reaches_core` gives `CompleteReturnArm ctx x (anchor + margin)`
with `x < anchor + margin` (`start_lt_core`), and `completeReturnArm_iff_zeroRun` reads off
`ctx.d (x+1) = 0`. -/
theorem anchoredLongReturnFamily_forces_clean_step {ctx : ActualFailureContext} {key : ℕ → ℕ}
    {y : ℕ} (R : AnchoredLongReturnFamily ctx key y) {x : ℕ}
    (hx : x ∈ olcSlice ctx key y) : ctx.d (x + 1) = 0 := by
  have harm : CompleteReturnArm ctx x (R.anchor + R.margin) :=
    anchoredLongReturnFamily_arm_reaches_core R hx
  have hlt : x < R.anchor + R.margin := R.start_lt_core x hx
  exact (completeReturnArm_iff_zeroRun ctx (Nat.le_of_lt hlt)).1 harm (x + 1)
    (Nat.lt_succ_self x) hlt

/-- **OBSTRUCTION (seed level).**  Any `ReturnClass4AnchoredSeed ctx` — for any slice key —
forces the digit fact `ctx.d (k+1) = 0` at every class-4 start.  Class-4 membership is a hit-gap
/ orbit condition that does not constrain `ctx.d (k+1)`, so the seed is not constructible from
the abstract interface alone: the (Z)/M.1.1 digit residual is genuinely necessary. -/
theorem anchoredSeed_forces_clean_step {ctx : ActualFailureContext}
    (S : ReturnClass4AnchoredSeed ctx) :
    ∀ k ∈ olcFibre ctx, ctx.d (k + 1) = 0 := fun k hk =>
  anchoredLongReturnFamily_forces_clean_step
    (S.family (S.key k) (Finset.mem_image_of_mem S.key hk))
    (Finset.mem_filter.mpr ⟨hk, rfl⟩)

/-- **OBSTRUCTION (core level).**  The sharper anchored core forces the same digit fact. -/
theorem anchoredCore_forces_clean_step {ctx : ActualFailureContext}
    (C : ReturnClass4AnchoredCore ctx) :
    ∀ k ∈ olcFibre ctx, ctx.d (k + 1) = 0 := fun k hk =>
  anchoredLongReturnFamily_forces_clean_step
    (C.family (C.key k) (Finset.mem_image_of_mem C.key hk))
    (Finset.mem_filter.mpr ⟨hk, rfl⟩)

/-- **OBSTRUCTION (window half).**  Any anchored seed forces the class-4 active-window interior
condition — which fails for the top `r+1` window starts in general
(`windowContainment_top_start_fails`), so it too is genuinely non-bookkeeping. -/
theorem anchoredSeed_forces_interior {ctx : ActualFailureContext}
    (S : ReturnClass4AnchoredSeed ctx) :
    ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card := by
  intro k hk
  have h1 := S.hContain k hk
  have h2 := S.hReach
  omega

/-! ## 3.  The (Z) zero-run data constructs the anchored family

From the digit-level (Z) facts on a slice — all-zero digits between slice starts and one clean
step past the top start — the anchored clean run with anchor `max(slice) + 1` is built, and the
existing audited bridge `AnchoredLongReturnFamily.ofAnchoredCleanRun` yields the family.  This is
exactly the inverse of the §2 forcing direction. -/

/-- A slice at a key in the fibre image is nonempty. -/
theorem olcSlice_nonempty_of_mem_image (ctx : ActualFailureContext) (key : ℕ → ℕ) {y : ℕ}
    (hy : y ∈ (olcFibre ctx).image key) : (olcSlice ctx key y).Nonempty := by
  obtain ⟨k, hk, hky⟩ := Finset.mem_image.mp hy
  exact ⟨k, Finset.mem_filter.mpr ⟨hk, hky⟩⟩

/-- The top start of a nonempty slice lies in the class-4 fibre. -/
theorem olcSlice_max'_mem_fibre (ctx : ActualFailureContext) (key : ℕ → ℕ) {y : ℕ}
    (hne : (olcSlice ctx key y).Nonempty) :
    (olcSlice ctx key y).max' hne ∈ olcFibre ctx :=
  (Finset.mem_filter.mp (Finset.max'_mem _ hne)).1

/-- **The anchored clean run from (Z) zero-run data.**  Anchor `= max(slice) + 1`, core length
`1`: the M.1.1 cleanliness on `(x, anchor + 1)` is the pairwise zero-run up to the top start
plus the clean step past it.  The genuine digit content of the construction lives here. -/
def returnCleanRunOfZeroData (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ)
    (hne : (olcSlice ctx key y).Nonempty)
    (hzero : ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      ∀ j, x < j → j ≤ z → ctx.d j = 0)
    (hstep : ctx.d ((olcSlice ctx key y).max' hne + 1) = 0) :
    AnchoredCleanRun ctx key y where
  anchor := (olcSlice ctx key y).max' hne + 1
  coreLen := 1
  coreLen_pos := Nat.one_pos
  start_lt := fun x hx => by
    have hxM : x ≤ (olcSlice ctx key y).max' hne := Finset.le_max' _ x hx
    omega
  clean := fun x hx j hj1 hj2 => by
    have hxM : x ≤ (olcSlice ctx key y).max' hne := Finset.le_max' _ x hx
    rcases Nat.lt_or_ge j ((olcSlice ctx key y).max' hne + 1) with hjM | hjM
    · exact hzero x hx ((olcSlice ctx key y).max' hne) (Finset.max'_mem _ hne)
        (by omega) j hj1 (by omega)
    · have hje : j = (olcSlice ctx key y).max' hne + 1 := by omega
      rw [hje]
      exact hstep

/-! ## 4.  The sharp residual `ReturnAnchoredZResidual` and the two-sided reduction -/

/-- **The sharp Return/Class-4 residual after this module** — exactly the genuinely-undischarged
data of the anchored per-slice atom, in digit-level manuscript vocabulary:

* `hzero` — the (Z) all-pairs zero-run on each slice (M.1.1/M.3: between class-4 complete-return
  starts of one slice the digits are all `0`);
* `hcleanStep` — one clean step past each class-4 start (`ctx.d (k+1) = 0`, the M.1.1 trace);
* `hgapDiv` — the self-referential dyadic spacing of consecutive slice starts
  (`2^{carryVal2 x} ∣ z − x`, the G.7/J.4 lift congruence, manuscript ~6536);
* `class4Interior` — the class-4 active-window interior (the K.1 endpoint boundary term);
* `hnumeric` — the matched `M_L·X` smallness with the K.1.2/L.20 multiplier.

`family` and `hbound` are **gone**: the family is constructed (§3) and the bound proved (§1). -/
structure ReturnAnchoredZResidual (ctx : ActualFailureContext) where
  /-- The per-`(e,τ,P)`-slice key. -/
  key : ℕ → ℕ
  /-- **(Z).**  All-pairs zero-run between slice starts. -/
  hzero : ∀ y ∈ (olcFibre ctx).image key,
    ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      ∀ j, x < j → j ≤ z → ctx.d j = 0
  /-- **(Z′ / M.1.1 trace).**  One clean step past each class-4 start. -/
  hcleanStep : ∀ k ∈ olcFibre ctx, ctx.d (k + 1) = 0
  /-- **G.7/J.4.**  Consecutive self-referential lift-gap divisibility. -/
  hgapDiv : ∀ y ∈ (olcFibre ctx).image key,
    ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      (∀ c ∈ olcSlice ctx key y, x < c → z ≤ c) → 2 ^ carryVal2 ctx x ∣ (z - x)
  /-- **K.1 boundary.**  Class-4 descent windows stay strictly inside the shell window. -/
  class4Interior : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
    k + ctx.n24CarryData.r + 1
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card
  /-- **The `M_L·X` smallness** with the matched multiplier `max 0 ((r+1)(L+B+1) − T)`. -/
  hnumeric : (((olcFibre ctx).image key).card : ℝ) * (liftLevelBound ctx.shell.X : ℝ)
      * returnDyadicMult ctx
    ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6

namespace ReturnAnchoredZResidual

variable {ctx : ActualFailureContext}

/-- **The anchored core from the Z-residual (the constructive direction).**  The family is built
from the (Z) data (§3); `hbound` is the §1 proved shell bound; the remaining fields transport. -/
def toAnchoredCore (R : ReturnAnchoredZResidual ctx) : ReturnClass4AnchoredCore ctx where
  key := R.key
  family := fun y hy =>
    AnchoredLongReturnFamily.ofAnchoredCleanRun
      (returnCleanRunOfZeroData ctx R.key y (olcSlice_nonempty_of_mem_image ctx R.key hy)
        (R.hzero y hy)
        (R.hcleanStep _ (olcSlice_max'_mem_fibre ctx R.key
          (olcSlice_nonempty_of_mem_image ctx R.key hy))))
  hbound := fun y hy k hk =>
    returnFibre_carryVal2_le_shell ctx (Finset.mem_filter.mp hk).1
  hgapDiv := R.hgapDiv
  class4Interior := R.class4Interior
  hnumeric := R.hnumeric

/-- The anchored seed from the Z-residual. -/
def toAnchoredSeed (R : ReturnAnchoredZResidual ctx) : ReturnClass4AnchoredSeed ctx :=
  R.toAnchoredCore.toAnchoredSeed

/-- The full V3 Return/Class-4 charge from the Z-residual. -/
def toCharge (R : ReturnAnchoredZResidual ctx) : Class4ReturnPerSliceCharge ctx :=
  R.toAnchoredCore.toCharge

/-- The Return capacity floor from the Z-residual. -/
theorem returnFloor (R : ReturnAnchoredZResidual ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  R.toAnchoredCore.returnFloor

/-- The corrected M.2.1 per-slice count from the Z-residual. -/
theorem perSliceCount (R : ReturnAnchoredZResidual ctx) :
    (olcFibre ctx).card
      ≤ ((olcFibre ctx).image R.key).card * liftLevelBound ctx.shell.X :=
  R.toAnchoredCore.perSliceCount

/-- **The Z-residual from any anchored core (the forcing direction).**  `hzero` is the derived
all-pairs zero-run, `hcleanStep` the §2 forcing, the rest are fields.  Nothing is lost. -/
def ofAnchoredCore (C : ReturnClass4AnchoredCore ctx) : ReturnAnchoredZResidual ctx where
  key := C.key
  hzero := fun y hy => C.zeroRunAllPairs hy
  hcleanStep := anchoredCore_forces_clean_step C
  hgapDiv := C.hgapDiv
  class4Interior := C.class4Interior
  hnumeric := C.hnumeric

/-- **The Z-residual from any anchored seed.**  The interior condition is forced from
`hReach`/`hContain` (§2); the zero-runs from the M.3.1 family via the complete-return placement. -/
def ofAnchoredSeed (S : ReturnClass4AnchoredSeed ctx) : ReturnAnchoredZResidual ctx where
  key := S.key
  hzero := fun y hy =>
    zeroRunAllPairs_of_completeReturns ctx S.key y
      (sliceCompleteReturns_of_anchoredLongReturnFamily (S.family y hy))
  hcleanStep := anchoredSeed_forces_clean_step S
  hgapDiv := S.hgapDiv
  class4Interior := anchoredSeed_forces_interior S
  hnumeric := S.hnumeric

end ReturnAnchoredZResidual

/-- **The faithful equivalence (core form).**  The Z-residual is *exactly* the remaining
Return/Class-4 anchored-core atom: neither stronger nor weaker. -/
theorem nonempty_anchoredCore_iff_zResidual (ctx : ActualFailureContext) :
    Nonempty (ReturnClass4AnchoredCore ctx) ↔ Nonempty (ReturnAnchoredZResidual ctx) :=
  ⟨fun h => h.elim fun C => ⟨ReturnAnchoredZResidual.ofAnchoredCore C⟩,
   fun h => h.elim fun R => ⟨R.toAnchoredCore⟩⟩

/-- **The faithful equivalence (seed form).**  Likewise for the original anchored seed. -/
theorem nonempty_anchoredSeed_iff_zResidual (ctx : ActualFailureContext) :
    Nonempty (ReturnClass4AnchoredSeed ctx) ↔ Nonempty (ReturnAnchoredZResidual ctx) :=
  ⟨fun h => h.elim fun S => ⟨ReturnAnchoredZResidual.ofAnchoredSeed S⟩,
   fun h => h.elim fun R => ⟨R.toAnchoredSeed⟩⟩

/-- **The empty-fibre witness (the `mpr` of the gate equivalence — NOT an unconditional
closure).**  When the class-4 fibre is empty the Z-residual is trivially inhabited.  This is not
merely a consistency check: under the K.1 numeric gate `64(r+1)(L+B+1) < 129L + 64` (automatic on
every `r = 0` shell) the converse is PROVED below (`zResidual_iff_class4Fibre_empty`), so
fibre-emptiness is then *exactly* the remaining Return atom.  Endpoints consume this construction
only through the explicitly named hypothesis `Class4FibreEmpty`; no claim is made that the fibre
is empty, and non-empty fibres still demand the genuine digit-level (Z) facts. -/
def ReturnAnchoredZResidual.ofEmptyFibre (ctx : ActualFailureContext)
    (hempty : olcFibre ctx = ∅) : ReturnAnchoredZResidual ctx where
  key := id
  hzero := fun y hy => absurd hy (by
    rw [hempty, Finset.image_empty]
    exact Finset.notMem_empty y)
  hcleanStep := fun k hk => absurd hk (by
    rw [hempty]
    exact Finset.notMem_empty k)
  hgapDiv := fun y hy => absurd hy (by
    rw [hempty, Finset.image_empty]
    exact Finset.notMem_empty y)
  class4Interior := fun k hk =>
    absurd (show k ∈ olcFibre ctx from hk) (by
      rw [hempty]
      exact Finset.notMem_empty k)
  hnumeric := by
    rw [hempty]
    simp only [Finset.image_empty, Finset.card_empty, Nat.cast_zero, zero_mul]
    rw [show erdos260Constants.cStar = (31 / 16 : ℝ) from rfl,
        show erdos260Constants.ξ = (1 / 16 : ℝ) from rfl]
    positivity

/-! ## 5.  The class-4 fibre characterization on the genuine route

The genuine first-obstruction route reaches class `4` either through the L.3.1 `returnPkg` exit
(`genuineChargeRoute_eq_four_iff`, proved upstream) or through the `cnlTail` catch-all with a
nonlocal-long window excess (`returnCls = 2`).  The second branch forces `k = 0` — for `k ≠ 0`
the run classifier already claims every start with `2Y ≤ windowExcess` — and `0` is never a
carry-window start, because a genuinely failing shell has digit support at or below `X`
(`shell_supportCount_pos`), so the window begins at `firstIndexAbove X ≥ 1`.  Hence on the
actual fibre only the E.13 **band-2** branch survives: `canonGap q K_k = 2`, i.e.
`2K_k ≤ q < 4K_k`.  Together with the high-excess floor in exact `ℕ` form this gives the sharp
membership characterization `mem_class4Fibre_iff` — the class-4 analogue of the class-1
`mem_class1Fibre_iff`. -/

/-- The L.3.1 band classifier hits `returnPkg` exactly on band index `2`. -/
theorem towerExitClassOfGap_eq_returnPkg_iff (g : ℕ) :
    towerExitClassOfGap g = TowerExitClass.returnPkg ↔ g = 2 := by
  constructor
  · intro h
    rcases g with _ | _ | _ | _ | _ | n
    · cases h
    · cases h
    · rfl
    · cases h
    · cases h
    · cases h
  · intro h
    subst h
    rfl

/-- **The E.13 band-2 window**: `canonGap q K = 2` iff `2K ≤ q < 4K` (for `K ≥ 1`). -/
theorem canonGap_eq_two_iff {q K : ℕ} (hK : 1 ≤ K) :
    canonGap q K = 2 ↔ 2 * K ≤ q ∧ q < 4 * K := by
  unfold canonGap
  constructor
  · intro h
    have hlog : Nat.log 2 (q / K) = 1 := by omega
    have hne : q / K ≠ 0 := by
      intro h0
      rw [h0, Nat.log_zero_right] at hlog
      exact absurd hlog (by norm_num)
    have h2 : 2 ≤ q / K := by
      have hpow := Nat.pow_log_le_self 2 hne
      rw [hlog] at hpow
      norm_num at hpow
      exact hpow
    have h4 : q / K < 4 := by
      have hpow := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (q / K)
      rw [hlog] at hpow
      norm_num at hpow
      exact hpow
    exact ⟨(Nat.le_div_iff_mul_le hK).mp h2, (Nat.div_lt_iff_lt_mul hK).mp h4⟩
  · rintro ⟨h2, h4⟩
    have h2' : 2 ≤ q / K := (Nat.le_div_iff_mul_le hK).mpr h2
    have h4' : q / K < 4 := (Nat.div_lt_iff_lt_mul hK).mpr h4
    have hlog : Nat.log 2 (q / K) = 1 :=
      Nat.log_eq_of_pow_le_of_lt_pow (by norm_num; omega) (by norm_num; omega)
    omega

/-- **The exceptional `cnlTail` branch of the class-4 route forces `k = 0`**: for `k ≠ 0`, a
nonlocal-long excess (`returnCls = 2`, so `2Y ≤ windowExcess`) already routes `k` to the run
class (`runClsOfShell k = 1`), which the route tests first. -/
theorem class4_exceptional_k_eq_zero (ctx : ActualFailureContext) {k : ℕ}
    (hrun : runClsOfShell ctx k ≠ 1) (hret : returnCls ctx k = 2) : k = 0 := by
  by_contra hk0
  apply hrun
  have h2Y : 2 * ctx.n24CarryData.Y
      ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T := by
    unfold returnCls at hret
    split_ifs at hret with h1 h2
    · exact absurd hret (by decide)
    · exact absurd hret (by decide)
    · exact le_of_lt (not_le.mp h2)
  unfold runClsOfShell
  rw [if_neg hk0, if_pos h2Y]

/-- **The carry window starts strictly above index `0`**: a genuinely failing shell has digit
support at or below `X` (`shell_supportCount_pos`), so `firstIndexAbove X ≥ 1`. -/
theorem n24_firstIndexAbove_pos (ctx : ActualFailureContext) :
    1 ≤ ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X :=
  ctx.n24CarryData.carry.hits.firstIndexAbove_pos_of_supportCount_pos
    ctx.shell_supportCount_pos

/-- `0` is never a carry-window start. -/
theorem zero_notMem_n24Starts (ctx : ActualFailureContext) :
    0 ∉ ctx.n24CarryData.starts := by
  rw [cnlMulti_starts_eq_window, Finset.mem_Ico]
  have h := n24_firstIndexAbove_pos ctx
  omega

/-- **The class-4 band pin**: every class-4 routed start of the genuine route has its slope-orbit
canonical-gap band index EXACTLY `2` (the L.3.1 `returnPkg` window).  The exceptional `cnlTail`
route branch would force `0 ∈ starts`, which is impossible. -/
theorem class4Fibre_canonGap_eq (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4) :
    canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
  have hstart : k ∈ ctx.n24CarryData.starts :=
    (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1
  have hroute : genuineChargeRoute ctx k = 4 := (Finset.mem_filter.mp hk).2
  rcases (genuineChargeRoute_eq_four_iff ctx k).mp hroute with h | ⟨ht, hrun, hret⟩
  · rw [towerClsOfShell_eq_band] at h
    exact (towerExitClassOfGap_eq_returnPkg_iff _).mp h
  · exfalso
    have hk0 : k = 0 := class4_exceptional_k_eq_zero ctx hrun hret
    rw [hk0] at hstart
    exact zero_notMem_n24Starts ctx hstart

/-- The high-excess floor `Y ≤ windowExcess` in exact `ℕ` form: with the pinned `T = 2L + 1` and
`Y = L/64` it reads `129·L + 64 ≤ 64·gapWindow`. -/
theorem Y_le_windowExcess_iff_gapWindow (ctx : ActualFailureContext) (k : ℕ) :
    ctx.n24CarryData.Y
        ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ↔ 129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r := by
  rw [cnlMulti_n24_T_eq, n24CarryData_Y_eq_div]
  have hL : (28 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
    exact_mod_cast shellLadderDepth_ge ctx
  unfold windowExcess positivePart
  constructor
  · intro h
    by_cases hle : ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ)
        - (2 * ((shellLadderDepth ctx : ℕ) : ℝ) + 1) ≤ 0
    · rw [max_eq_right hle] at h
      linarith
    · rw [max_eq_left (not_le.mp hle).le] at h
      have hreal : (129 : ℝ) * ((shellLadderDepth ctx : ℕ) : ℝ) + 64
          ≤ 64 * ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ) := by
        linarith
      exact_mod_cast hreal
  · intro h
    have hreal : (129 : ℝ) * ((shellLadderDepth ctx : ℕ) : ℝ) + 64
        ≤ 64 * ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [max_eq_left (by linarith)]
    linarith

/-- **The sharp class-4 membership characterization** (the class-4 analogue of
`mem_class1Fibre_iff`): `k ∈ fibre₄` iff `k` is a carry-window start with the high-excess
gap-window floor `129L + 64 ≤ 64·gapWindow` and the E.13 band-2 pin `canonGap q K_k = 2`. -/
theorem mem_class4Fibre_iff (ctx : ActualFailureContext) (k : ℕ) :
    k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4
      ↔ k ∈ ctx.n24CarryData.starts
        ∧ 129 * shellLadderDepth ctx + 64
            ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2 := by
  constructor
  · intro hk
    have hhigh := mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1
    exact ⟨hhigh.1, (Y_le_windowExcess_iff_gapWindow ctx k).mp hhigh.2,
      class4Fibre_canonGap_eq ctx hk⟩
  · rintro ⟨hstart, hgw, hband⟩
    refine Finset.mem_filter.mpr
      ⟨mem_highExcessStarts.mpr
        ⟨hstart, (Y_le_windowExcess_iff_gapWindow ctx k).mpr hgw⟩, ?_⟩
    refine (genuineChargeRoute_eq_four_iff ctx k).mpr (Or.inl ?_)
    rw [towerClsOfShell_eq_band]
    exact (towerExitClassOfGap_eq_returnPkg_iff _).mpr hband

/-- **The class-4 fibre IS the doubly-pinned window filter** (irreducible arithmetic form). -/
theorem class4Fibre_eq_pinnedFilter (ctx : ActualFailureContext) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4
      = ctx.n24CarryData.starts.filter (fun k =>
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ∧ canonGap (class1SlopeDatum ctx).q
                (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 2) := by
  ext k
  rw [Finset.mem_filter, mem_class4Fibre_iff]

/-- **The class-4 orbit-band pin**: the slope-orbit numerator at every class-4 start sits in the
dyadic band `2·K_k ≤ q < 4·K_k`, i.e. `q/4 < K_k ≤ q/2`. -/
theorem class4Fibre_orbit_band (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4) :
    2 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
        ≤ (class1SlopeDatum ctx).q
      ∧ (class1SlopeDatum ctx).q
        < 4 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k := by
  have hband := class4Fibre_canonGap_eq ctx hk
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k
  exact (canonGap_eq_two_iff horb.1).mp hband

/-- **The class-4 orbit-step pin**: at every class-4 start the E.12/E.13 successor numerator is
EXACTLY `4·K_k − q` (the band-2 carry-doubling step). -/
theorem class4Fibre_orbit_step (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4) :
    slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (k + 1)
      = 4 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
        - (class1SlopeDatum ctx).q := by
  have hband := class4Fibre_canonGap_eq ctx hk
  have hstep : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (k + 1)
      = boundedSlopeStep (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) := rfl
  rw [hstep]
  unfold boundedSlopeStep
  rw [hband]
  norm_num

/-- **A nonempty class-4 fibre forces an odd modulus `q ≥ 3`**: the band `2K ≤ q` needs `q ≥ 2`,
and `q` is odd. -/
theorem modulus_ge_three_of_class4Fibre_nonempty (ctx : ActualFailureContext)
    (h : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).Nonempty) :
    3 ≤ (class1SlopeDatum ctx).q := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨h2, h4⟩ := class4Fibre_orbit_band ctx hk
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k
  obtain ⟨m, hm⟩ := (class1SlopeDatum ctx).hq_odd
  have h1 := horb.1
  omega

/-- **Small-modulus closure**: the class-4 routed fibre of the genuine route is PROVABLY EMPTY on
every shell whose closed AP-subfibre modulus is `< 3` — the band-2 window `2K ≤ q < 4K` is
unsatisfiable at `q = 1`. -/
theorem class4Fibre_empty_of_modulus_lt_three (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q < 3) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have h3 := modulus_ge_three_of_class4Fibre_nonempty ctx ⟨k, hk⟩
  omega

/-! ## 6.  The K.1 gate dichotomy: under the gap ceiling, `class4Interior ↔ fibre = ∅`

The carry start set is the dyadic shell index window and the PROVED dyadic gap ceiling
`hitGap ≤ L + B + 1` holds strictly inside it (`n24_hitGap_le_window`).  The class-4 floor
demands `64·gapWindow ≥ 129L + 64 > 64(r+1)(L+B+1)` under the numeric gate, so every class-4
start must push its descent window past the ceiling's reach: it lives in the top `r + 1`
boundary band — exactly the band the K.1 interior field `class4Interior` excludes.  Hence under
the gate the interior field is *equivalent* to fibre-emptiness, and with
`nonempty_anchoredSeed_iff_zResidual` the whole Return atom collapses to `olcFibre ctx = ∅` on
gated shells.  On `r = 0` shells (all `L ≤ 15420`) the gate is automatic. -/

/-- Every class-4 routed start lies in the dyadic shell index window `i ≤ k < i + K`. -/
theorem class4Fibre_mem_window (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4) :
    ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X ≤ k
      ∧ k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card := by
  have hstart : k ∈ ctx.n24CarryData.starts :=
    (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1
  rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hstart
  exact hstart

/-- **The window-overrun pin.**  Under the numeric gate `64·(r+1)·(L+B+1) < 129·L + 64`, every
class-4 start's descent window must overrun the shell window:
`firstIndexAbove X + |supportShell d X| ≤ k + r + 1`. -/
theorem class4Fibre_window_overrun (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card
      ≤ k + ctx.n24CarryData.r + 1 := by
  by_contra hint
  have hint' : k + ctx.n24CarryData.r + 1
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card := Nat.lt_of_not_le hint
  have hgap : ∀ m ∈ Finset.range (ctx.n24CarryData.r + 1),
      hitGap ctx.n24CarryData.a (k + m)
        ≤ shellLadderDepth ctx + carryB ctx.shell.Q + 1 := by
    intro m hm
    rw [Finset.mem_range] at hm
    exact n24_hitGap_le_window ctx (by omega)
  have hsum : gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ≤ (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
    unfold gapWindow
    calc ∑ m ∈ Finset.range (ctx.n24CarryData.r + 1), hitGap ctx.n24CarryData.a (k + m)
        ≤ ∑ _m ∈ Finset.range (ctx.n24CarryData.r + 1),
            (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := Finset.sum_le_sum hgap
      _ = (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hY : ctx.n24CarryData.Y
      ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T :=
    Y_le_windowExcess_of_mem_routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4 hk
  have hpin := (Y_le_windowExcess_iff_gapWindow ctx k).mp hY
  have h64 : 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ≤ 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) :=
    Nat.mul_le_mul_left 64 hsum
  omega

/-- **The boundary-band cardinality bound**: under the numeric gate the class-4 fibre has at most
`r + 1` elements (it sits inside the top `r + 1` positions of the shell window). -/
theorem class4Fibre_card_le_of_gapCeiling (ctx : ActualFailureContext)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).card
      ≤ ctx.n24CarryData.r + 1 := by
  have hsub : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4
      ⊆ Finset.Ico
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1))
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) := by
    intro k hk
    have hover := class4Fibre_window_overrun ctx hk hnum
    have hwin := class4Fibre_mem_window ctx hk
    rw [Finset.mem_Ico]
    omega
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).card
      ≤ _ := Finset.card_le_card hsub
    _ ≤ ctx.n24CarryData.r + 1 := by
        rw [Nat.card_Ico]
        omega

/-- The numeric gate holds automatically on every `r = 0` shell, from the largeness gate
`B + 25 ≤ L`. -/
theorem class4_gate_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    64 * ((ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
      < 129 * shellLadderDepth ctx + 64 := by
  have hB : carryB ctx.shell.Q + 25 ≤ shellLadderDepth ctx := ctx.shell_carryLarge
  rw [hr]
  omega

/-- **`r = 0` shells: the class-4 fibre is pinned to the SINGLE topmost window start.** -/
theorem class4Fibre_top_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4) :
    k + 1 = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card := by
  have hover := class4Fibre_window_overrun ctx hk (class4_gate_of_r_eq_zero ctx hr)
  have hwin := class4Fibre_mem_window ctx hk
  omega

/-- **`r = 0` shells: at most ONE class-4 routed start** (`r = ⌊κL⌋ = 0` covers all
`L ≤ 15420`). -/
theorem class4Fibre_card_le_one_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro x hx y hy
  have hxe := class4Fibre_top_of_r_eq_zero ctx hr hx
  have hye := class4Fibre_top_of_r_eq_zero ctx hr hy
  omega

/-- **The K.1 dichotomy.**  Under the numeric gate, the class-4 active-window interior field is
EQUIVALENT to the emptiness of the class-4 fibre: a fibre member would have to sit in the top
`r + 1` boundary band (overrun) and strictly below it (interior) at once. -/
theorem class4Interior_iff_fibre_empty (ctx : ActualFailureContext)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    (∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card)
      ↔ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4 = ∅ := by
  constructor
  · intro hint
    rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    have h1 := hint k hk
    have h2 := class4Fibre_window_overrun ctx hk hnum
    omega
  · intro hempty k hk
    rw [hempty] at hk
    exact absurd hk (Finset.notMem_empty k)

/-- **The gate collapse (Z-residual form).**  Under the numeric gate, the Z-residual is
inhabited IFF the class-4 fibre is empty: `ofEmptyFibre` is the `mpr`, and the K.1 interior
field is the `mp`.  On gated shells the WHOLE Return atom is the single Prop
`olcFibre ctx = ∅`. -/
theorem zResidual_iff_class4Fibre_empty (ctx : ActualFailureContext)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    Nonempty (ReturnAnchoredZResidual ctx) ↔ olcFibre ctx = ∅ := by
  constructor
  · rintro ⟨R⟩
    exact (class4Interior_iff_fibre_empty ctx hnum).mp R.class4Interior
  · intro hempty
    exact ⟨ReturnAnchoredZResidual.ofEmptyFibre ctx hempty⟩

/-- The gate collapse, anchored-seed form. -/
theorem anchoredSeed_iff_class4Fibre_empty (ctx : ActualFailureContext)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    Nonempty (ReturnClass4AnchoredSeed ctx) ↔ olcFibre ctx = ∅ :=
  (nonempty_anchoredSeed_iff_zResidual ctx).trans (zResidual_iff_class4Fibre_empty ctx hnum)

/-- The gate collapse, anchored-core form. -/
theorem anchoredCore_iff_class4Fibre_empty (ctx : ActualFailureContext)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    Nonempty (ReturnClass4AnchoredCore ctx) ↔ olcFibre ctx = ∅ :=
  (nonempty_anchoredCore_iff_zResidual ctx).trans (zResidual_iff_class4Fibre_empty ctx hnum)

/-- The gate collapse on `r = 0` shells (the gate is automatic there). -/
theorem zResidual_iff_class4Fibre_empty_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    Nonempty (ReturnAnchoredZResidual ctx) ↔ olcFibre ctx = ∅ :=
  zResidual_iff_class4Fibre_empty ctx (class4_gate_of_r_eq_zero ctx hr)

/-- The gate collapse on every shell with `L ≤ 15420` (the explicit `r = ⌊κL⌋ = 0` range). -/
theorem zResidual_iff_class4Fibre_empty_of_L_le (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 15420) :
    Nonempty (ReturnAnchoredZResidual ctx) ↔ olcFibre ctx = ∅ :=
  zResidual_iff_class4Fibre_empty_of_r_eq_zero ctx (n24_r_eq_zero_of_L_le ctx hL)

/-- **`r = 0` shells: the whole Return atom is ONE membership fact** — the Z-residual is
inhabited iff the single topmost window start is not class-4 routed. -/
theorem zResidual_iff_top_notMem_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    Nonempty (ReturnAnchoredZResidual ctx)
      ↔ ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - 1
          ∉ olcFibre ctx := by
  rw [zResidual_iff_class4Fibre_empty_of_r_eq_zero ctx hr]
  constructor
  · intro hempty
    rw [hempty]
    exact Finset.notMem_empty _
  · intro htop
    rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    have htopk := class4Fibre_top_of_r_eq_zero ctx hr hk
    have hke : k = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card - 1 := by omega
    rw [hke] at hk
    exact htop hk

/-! ## 7.  `hgapDiv` CLOSED on the self-referential M.2.1 key

The manuscript's per-`(e,τ,P)` slice key buckets each class-4 start by its self-referential
congruence data: the carry level `e = carryVal2 k` and the residue `τ = k mod 2^e` (proof_v4
~6536).  On that key the G.7/J.4 lift-gap divisibility is a THEOREM — two same-slice starts are
congruent mod `2^{carryVal2 x}` by construction — so the Z-residual loses the `hgapDiv` field
on this route.  `ReturnSelfRefZResidual` records the strictly smaller surface. -/

/-- **The self-referential M.2.1 slice key**: carry level × dyadic residue,
`k ↦ ⟨carryVal2 k, k mod 2^{carryVal2 k}⟩` (packed by the ℕ pairing). -/
def returnSelfRefKey (ctx : ActualFailureContext) : ℕ → ℕ := fun k =>
  Nat.pair (carryVal2 ctx k) (k % 2 ^ carryVal2 ctx k)

/-- **The self-referential congruence is automatic on the key's slices**: same key ⟹ same carry
level and same residue ⟹ `2^{carryVal2 x} ∣ (z − x)`. -/
theorem returnSelfRefKey_gapDiv (ctx : ActualFailureContext) {x z : ℕ}
    (hxz : returnSelfRefKey ctx x = returnSelfRefKey ctx z) (hlt : x < z) :
    2 ^ carryVal2 ctx x ∣ (z - x) := by
  have hpair : Nat.pair (carryVal2 ctx x) (x % 2 ^ carryVal2 ctx x)
      = Nat.pair (carryVal2 ctx z) (z % 2 ^ carryVal2 ctx z) := hxz
  obtain ⟨hv, hm⟩ := Nat.pair_eq_pair.mp hpair
  rw [← hv] at hm
  exact (Nat.modEq_iff_dvd' (le_of_lt hlt)).mp hm

/-- **The self-referential-key Return residual** — the Z-residual at the canonical M.2.1 key,
with `hgapDiv` REMOVED (it is a theorem there): `hzero / hcleanStep / class4Interior / hnumeric`
only. -/
structure ReturnSelfRefZResidual (ctx : ActualFailureContext) where
  /-- **(Z).**  All-pairs zero-run between same-slice starts of the self-referential key. -/
  hzero : ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
    ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y, ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
      x < z → ∀ j, x < j → j ≤ z → ctx.d j = 0
  /-- **(Z′ / M.1.1 trace).**  One clean step past each class-4 start. -/
  hcleanStep : ∀ k ∈ olcFibre ctx, ctx.d (k + 1) = 0
  /-- **K.1 boundary.**  Class-4 descent windows stay strictly inside the shell window. -/
  class4Interior : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
    k + ctx.n24CarryData.r + 1
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card
  /-- **The `M_L·X` smallness** at the self-referential key count. -/
  hnumeric : (((olcFibre ctx).image (returnSelfRefKey ctx)).card : ℝ)
      * (liftLevelBound ctx.shell.X : ℝ) * returnDyadicMult ctx
    ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6

namespace ReturnSelfRefZResidual

variable {ctx : ActualFailureContext}

/-- The full Z-residual from the self-referential-key residual: `hgapDiv` is the proved
congruence `returnSelfRefKey_gapDiv`. -/
def toZResidual (R : ReturnSelfRefZResidual ctx) : ReturnAnchoredZResidual ctx where
  key := returnSelfRefKey ctx
  hzero := R.hzero
  hcleanStep := R.hcleanStep
  hgapDiv := fun y hy x hx z hz hxz hsucc =>
    returnSelfRefKey_gapDiv ctx
      ((Finset.mem_filter.mp hx).2.trans ((Finset.mem_filter.mp hz).2).symm) hxz
  class4Interior := R.class4Interior
  hnumeric := R.hnumeric

/-- The anchored core from the self-referential-key residual. -/
def toAnchoredCore (R : ReturnSelfRefZResidual ctx) : ReturnClass4AnchoredCore ctx :=
  R.toZResidual.toAnchoredCore

/-- The full V3 Return/Class-4 charge from the self-referential-key residual. -/
def toCharge (R : ReturnSelfRefZResidual ctx) : Class4ReturnPerSliceCharge ctx :=
  R.toZResidual.toCharge

/-- The Return capacity floor from the self-referential-key residual. -/
theorem returnFloor (R : ReturnSelfRefZResidual ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  R.toZResidual.returnFloor

end ReturnSelfRefZResidual

/-- The Z-residual family from a self-referential-key residual family (feeds every wiring
endpoint of §10). -/
def returnZResidualsOfSelfRef
    (R : ∀ ctx : ActualFailureContext, ReturnSelfRefZResidual ctx) :
    ∀ ctx : ActualFailureContext, ReturnAnchoredZResidual ctx :=
  fun ctx => (R ctx).toZResidual

/-- **Key-count monotonicity**: the keyed `M_L·X` smallness (for ANY key, in particular the
self-referential one) follows from the diagonal numeric — `#keys ≤ |olcFibre|`. -/
theorem return_hnumeric_key_of_diagonal (ctx : ActualFailureContext) (key : ℕ → ℕ)
    (h : ((olcFibre ctx).card : ℝ) * (liftLevelBound ctx.shell.X : ℝ) * returnDyadicMult ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    (((olcFibre ctx).image key).card : ℝ) * (liftLevelBound ctx.shell.X : ℝ)
        * returnDyadicMult ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  refine le_trans ?_ h
  have hcard : (((olcFibre ctx).image key).card : ℝ) ≤ ((olcFibre ctx).card : ℝ) := by
    exact_mod_cast Finset.card_image_le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg _))
    (returnDyadicMult_nonneg ctx)

/-! ## 8.  `hnumeric` CLOSED on `r = 0` shells: the matched multiplier vanishes

With `r = 0` the matched K.1.2/L.20 multiplier is `max 0 ((L+B+1) − (2L+1)) = max 0 (B − L) = 0`
by the largeness gate `B + 25 ≤ L`, so the `M_L·X` smallness holds for EVERY key on every
`r = ⌊κL⌋ = 0` shell — the entire `L ≤ 15420` range. -/

/-- The shared dyadic gap ceiling, in ladder-depth form (definitional). -/
theorem returnDyadicG0_eq (ctx : ActualFailureContext) :
    returnDyadicG0 ctx = shellLadderDepth ctx + carryB ctx.shell.Q + 1 := rfl

/-- **The matched window-excess multiplier vanishes on `r = 0` shells**:
`(0+1)·(L+B+1) − (2L+1) = B − L ≤ −25 < 0`. -/
theorem returnDyadicMult_eq_zero_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) : returnDyadicMult ctx = 0 := by
  have hB : carryB ctx.shell.Q + 25 ≤ shellLadderDepth ctx := ctx.shell_carryLarge
  have hBL : ((carryB ctx.shell.Q : ℕ) : ℝ) + 25 ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
    exact_mod_cast hB
  have hG0 : ((returnDyadicG0 ctx : ℕ) : ℝ)
      = ((shellLadderDepth ctx : ℕ) : ℝ) + ((carryB ctx.shell.Q : ℕ) : ℝ) + 1 := by
    exact_mod_cast congrArg (Nat.cast (R := ℝ)) (returnDyadicG0_eq ctx)
  unfold returnDyadicMult
  rw [hr, cnlMulti_n24_T_eq, hG0]
  rw [max_eq_left (by push_cast; linarith)]

/-- **The `M_L·X` smallness holds for EVERY key on `r = 0` shells** — the `hnumeric` field of the
Z-residual is closed there unconditionally. -/
theorem return_hnumeric_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) (key : ℕ → ℕ) :
    (((olcFibre ctx).image key).card : ℝ) * (liftLevelBound ctx.shell.X : ℝ)
        * returnDyadicMult ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  rw [returnDyadicMult_eq_zero_of_r_eq_zero ctx hr, mul_zero]
  rw [show erdos260Constants.cStar = (31 / 16 : ℝ) from rfl,
      show erdos260Constants.ξ = (1 / 16 : ℝ) from rfl]
  positivity

/-! ## 9.  The diagonal (singleton-key) specialisation

With `key = id` every slice is a singleton, so `hzero` and `hgapDiv` hold outright and the
residual shrinks to three fields.  The price is the strongest possible numeric
(`#keys = |olcFibre ctx|`): this route is *sufficient*, and is recorded honestly as such —
the manuscript-faithful route keeps the `(e,τ,P)` key with the smaller `#keys`. -/

/-- **The diagonal Return residual** — `hcleanStep` + `class4Interior` + the diagonal numeric. -/
structure ReturnDiagonalZResidual (ctx : ActualFailureContext) where
  /-- One clean step past each class-4 start. -/
  hcleanStep : ∀ k ∈ olcFibre ctx, ctx.d (k + 1) = 0
  /-- Class-4 descent windows stay strictly inside the shell window. -/
  class4Interior : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
    k + ctx.n24CarryData.r + 1
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card
  /-- The diagonal `M_L·X` smallness (`#keys = |olcFibre|`, the strongest form). -/
  hnumeric : ((olcFibre ctx).card : ℝ) * (liftLevelBound ctx.shell.X : ℝ)
      * returnDyadicMult ctx
    ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6

namespace ReturnDiagonalZResidual

variable {ctx : ActualFailureContext}

/-- The diagonal residual is a Z-residual: singleton slices have no pairs, so the pairwise
(Z) and gap-divisibility obligations hold outright. -/
def toZResidual (R : ReturnDiagonalZResidual ctx) : ReturnAnchoredZResidual ctx where
  key := id
  hzero := fun y hy x hx z hz hxz => by
    have hx' := (Finset.mem_filter.mp hx).2
    have hz' := (Finset.mem_filter.mp hz).2
    simp only [id_eq] at hx' hz'
    exact absurd hxz (by omega)
  hcleanStep := R.hcleanStep
  hgapDiv := fun y hy x hx z hz hxz hsucc => by
    have hx' := (Finset.mem_filter.mp hx).2
    have hz' := (Finset.mem_filter.mp hz).2
    simp only [id_eq] at hx' hz'
    exact absurd hxz (by omega)
  class4Interior := R.class4Interior
  hnumeric := by simpa [Finset.image_id] using R.hnumeric

/-- The anchored core from the diagonal residual. -/
def toAnchoredCore (R : ReturnDiagonalZResidual ctx) : ReturnClass4AnchoredCore ctx :=
  R.toZResidual.toAnchoredCore

/-- The full V3 Return/Class-4 charge from the diagonal residual. -/
def toCharge (R : ReturnDiagonalZResidual ctx) : Class4ReturnPerSliceCharge ctx :=
  R.toZResidual.toCharge

/-- The Return capacity floor from the diagonal residual. -/
theorem returnFloor (R : ReturnDiagonalZResidual ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  R.toZResidual.returnFloor

end ReturnDiagonalZResidual

/-! ## 10.  Wiring — the V3/P9 Return field from a Z-residual family -/

/-- **The goal-1-shaped seed family, conditional on exactly the Z-residual.**  This is the
sharpest available form of `returnAnchoredSeedUnconditional`: by §2 the unconditional version is
impossible (it would force digit facts no interface supplies), and by §4 this conditional form
loses nothing. -/
def returnAnchoredSeedOfZ
    (R : ∀ ctx : ActualFailureContext, ReturnAnchoredZResidual ctx) :
    ∀ ctx : ActualFailureContext, ReturnClass4AnchoredSeed ctx :=
  fun ctx => (R ctx).toAnchoredSeed

/-- The V3 `returnCharge` field from a Z-residual family. -/
def returnChargeOfZResiduals
    (R : ∀ ctx : ActualFailureContext, ReturnAnchoredZResidual ctx) :
    ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx :=
  fun ctx => (R ctx).toCharge

/-- The sharper core-residual surface of `ReturnPerSliceClosure`, from a Z-residual family. -/
def returnPerSliceCoreResidualOfZ
    (R : ∀ ctx : ActualFailureContext, ReturnAnchoredZResidual ctx) :
    ReturnPerSliceCoreResidual :=
  ⟨fun ctx => (R ctx).toAnchoredCore⟩

/-- The seed-residual surface of `ReturnPerSliceClosure`, from a Z-residual family. -/
def returnPerSliceClosureResidualOfZ
    (R : ∀ ctx : ActualFailureContext, ReturnAnchoredZResidual ctx) :
    ReturnPerSliceClosureResidual :=
  ⟨returnAnchoredSeedOfZ R⟩

/-- The Return capacity floor for a Z-residual family. -/
theorem returnFloorOfZ
    (R : ∀ ctx : ActualFailureContext, ReturnAnchoredZResidual ctx) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  fun ctx => (R ctx).returnFloor

/-- **The P9/V3 endpoint with the Return field supplied by the Z-residual.**  The Return slot of
`P9V3RunResidual` is `returnChargeOfZResiduals returnZ`; the other five class atoms are taken in
their existing residual forms. -/
def P9V3RunResidual.ofReturnZ
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnZ : ∀ ctx : ActualFailureContext, ReturnAnchoredZResidual ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual)
        (returnChargeOfZResiduals returnZ)))
    (cnl : Class1CNLInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual)
        (returnChargeOfZResiduals returnZ)))
    (densePackCount : ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card
        ≤ (densePackMarkers
            (v3Budget towerCount (p9V3RunChainOfResidual runResidual)
              (returnChargeOfZResiduals returnZ)) ctx).card)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k,
      k ∈ genuineDensePackStarts ctx →
        k + ctx.n24CarryData.r
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    P9V3RunResidual where
  towerCount := towerCount
  runResidual := runResidual
  returnCharge := returnChargeOfZResiduals returnZ
  chernoff := chernoff
  cnl := cnl
  densePackCount := densePackCount
  windowReach := windowReach
  hReach := hReach
  hContain := hContain
  hScale := hScale

/-- **Endpoint.**  `Erdos260Statement` from the Z-residual Return atom plus the other five class
atoms, through the ctx-pinned P9/V3 capstone.  The Return field of `P9V3RunResidual` is now
supplied by `returnChargeOfZResiduals`. -/
theorem erdos260_p9V3_ofReturnZ
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnZ : ∀ ctx : ActualFailureContext, ReturnAnchoredZResidual ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual)
        (returnChargeOfZResiduals returnZ)))
    (cnl : Class1CNLInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual)
        (returnChargeOfZResiduals returnZ)))
    (densePackCount : ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card
        ≤ (densePackMarkers
            (v3Budget towerCount (p9V3RunChainOfResidual runResidual)
              (returnChargeOfZResiduals returnZ)) ctx).card)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k,
      k ∈ genuineDensePackStarts ctx →
        k + ctx.n24CarryData.r
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Erdos260Statement :=
  (P9V3RunResidual.ofReturnZ towerCount runResidual returnZ chernoff cnl densePackCount
    windowReach hReach hContain hScale).toStatement

/-! ### The named empty-fibre residual `Class4FibreEmpty`

The per-ctx Prop `olcFibre ctx = ∅`, carried as an EXPLICIT hypothesis (the exact mirror of the
clean-CNL `Class1FibreEmpty`).  Under the K.1 numeric gate it is per-ctx EQUIVALENT to the
Z-residual (§6), so on gated shells — in particular every `r = 0` shell, i.e. all `L ≤ 15420` —
this named residual is not merely sufficient but *exactly* the remaining Return atom.  No
unconditional closure of `Class4FibreEmpty` is claimed: the top-band window gaps are not bounded
by the shell ceiling, so a top start CAN carry high excess in the model. -/

/-- **The named class-4 empty-fibre residual**: the genuine route charges no start to the
Return/Class-4 leaf, at any failure context. -/
def Class4FibreEmpty : Prop :=
  ∀ ctx : ActualFailureContext, olcFibre ctx = ∅

/-- The Z-residual family from the named empty-fibre residual (`ofEmptyFibre`, pointwise). -/
def returnZResidualsOfClass4FibreEmpty (h : Class4FibreEmpty) :
    ∀ ctx : ActualFailureContext, ReturnAnchoredZResidual ctx :=
  fun ctx => ReturnAnchoredZResidual.ofEmptyFibre ctx (h ctx)

/-- **On uniformly gated shell families the named residual is EXACTLY the Z-residual family**:
`Class4FibreEmpty ↔ ∀ ctx, Nonempty (ReturnAnchoredZResidual ctx)`. -/
theorem class4FibreEmpty_iff_zResiduals_of_gate
    (hg : ∀ ctx : ActualFailureContext,
      64 * ((ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    Class4FibreEmpty
      ↔ ∀ ctx : ActualFailureContext, Nonempty (ReturnAnchoredZResidual ctx) :=
  forall_congr' fun ctx => (zResidual_iff_class4Fibre_empty ctx (hg ctx)).symm

/-- The Return capacity floor from the named empty-fibre residual. -/
theorem returnFloor_ofClass4FibreEmpty (h : Class4FibreEmpty) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  returnFloorOfZ (returnZResidualsOfClass4FibreEmpty h)

/-- **Endpoint.**  `Erdos260Statement` from the named empty-fibre residual `Class4FibreEmpty`
plus the other five class atoms — the Return hypothesis is the explicitly carried Prop, never a
silent vacuity. -/
theorem erdos260_p9V3_ofClass4FibreEmpty
    (hfibre : Class4FibreEmpty)
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual)
        (returnChargeOfZResiduals (returnZResidualsOfClass4FibreEmpty hfibre))))
    (cnl : Class1CNLInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual)
        (returnChargeOfZResiduals (returnZResidualsOfClass4FibreEmpty hfibre))))
    (densePackCount : ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card
        ≤ (densePackMarkers
            (v3Budget towerCount (p9V3RunChainOfResidual runResidual)
              (returnChargeOfZResiduals (returnZResidualsOfClass4FibreEmpty hfibre)))
            ctx).card)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k,
      k ∈ genuineDensePackStarts ctx →
        k + ctx.n24CarryData.r
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Erdos260Statement :=
  erdos260_p9V3_ofReturnZ towerCount runResidual
    (returnZResidualsOfClass4FibreEmpty hfibre) chernoff cnl densePackCount
    windowReach hReach hContain hScale

/-! ## 11.  Honest machine-readable status -/

/-- The precise status of the Return/Class-4 anchored atom after this module. -/
def returnAnchoredUnconditionalStatus : List String :=
  [ "CLOSED UNCONDITIONALLY (hbound) — returnFibre_carryVal2_le_shell: for every class-4 start " ++
      "k ∈ olcFibre ctx, carryVal2 ctx k ≤ ctx.shell.X. Proof: starts = Ico i (i+K) " ++
      "(n24Starts_eq_window) ⇒ k ≤ a k ≤ 2X (StrictMono.le_apply, a_le_two_mul_of_lt_add_card); " ++
      "R_k ≤ Q(k+2) (integerCarry_bounds_of_rational_value); 2^{v₂ R_k} ≤ 4QX ≤ 2^{B+L} " ++
      "(carryB_spec, aboveCarryThreshold_provides_windowScale); B + L ≤ 2L ≤ 2^L = X. The hbound " ++
      "field of ReturnClass4AnchoredCore/Seed is no longer a residual for ANY slice key.",
    "CLOSED UNCONDITIONALLY (family construction) — returnCleanRunOfZeroData + " ++
      "AnchoredLongReturnFamily.ofAnchoredCleanRun: the per-slice M.3.1 anchored family is " ++
      "CONSTRUCTED from digit-level (Z) zero-run data (pairwise zero-runs + one clean step past " ++
      "the top start), anchor = max(slice)+1. The digit content lives in the M.1.1 " ++
      "complete-return arms (clean doubling of the actual integer carry); nothing is empty, " ++
      "all-zero-factory, or vacuous.",
    "OBSTRUCTION (PROVED) — anchoredLongReturnFamily_forces_clean_step / " ++
      "anchoredSeed_forces_clean_step / anchoredCore_forces_clean_step: ANY anchored seed/core, " ++
      "for ANY key, forces ctx.d (k+1) = 0 at every class-4 start; and " ++
      "anchoredSeed_forces_interior: it forces the class-4 window-interior condition, which fails " ++
      "for the top r+1 window starts in general (windowContainment_top_start_fails). Class-4 " ++
      "membership (genuineChargeRoute: towerClsOfShell orbit-gap class / returnCls window-excess " ++
      "band) does not determine ctx.d (k+1), so a from-nothing returnAnchoredSeedUnconditional is " ++
      "impossible: goal 1 is genuinely blocked at the digit level, not at bookkeeping.",
    "REDUCED, FAITHFULLY (the new frontier) — ReturnAnchoredZResidual ctx: key + hzero ((Z) " ++
      "pairwise slice zero-runs) + hcleanStep (d(k+1) = 0 on the fibre) + hgapDiv (G.7/J.4 dyadic " ++
      "spacing 2^{carryVal2 x} ∣ z−x) + class4Interior (K.1 boundary) + hnumeric (M_L·X " ++
      "smallness). toAnchoredCore CONSTRUCTS the full anchored core from it; ofAnchoredCore / " ++
      "ofAnchoredSeed recover it from any core/seed; nonempty_anchoredCore_iff_zResidual and " ++
      "nonempty_anchoredSeed_iff_zResidual prove the reduction is an EQUIVALENCE — strictly " ++
      "smaller than the previous frontier (family + hbound eliminated), provably not smaller " ++
      "than possible.",
    "RESIDUAL (precise Lean types, all forced by the target, none artificial) — (i) hzero : " ++
      "∀ y ∈ (olcFibre ctx).image key, ∀ x z ∈ olcSlice, x < z → zero-run on (x,z]; (ii) " ++
      "hcleanStep : ∀ k ∈ olcFibre ctx, ctx.d (k+1) = 0; (iii) hgapDiv : consecutive " ++
      "2^{carryVal2 x} ∣ (z−x); (iv) class4Interior : k + r + 1 < firstIndexAbove X + " ++
      "|supportShell|; (v) hnumeric : (#keys)·liftLevelBound X·returnDyadicMult ctx ≤ c⋆ξX/6. " ++
      "(i)+(ii) = the documented V3 wave-16 'RETURN (Z)' frontier; (iii) = the M.2.1 " ++
      "self-referential congruence (proof_v4 ~6536); (iv) = the shared K.1 endpoint boundary " ++
      "(same shape as Chernoff/CNL/DensePack); (v) = the genuine analytic M_L·X input.  " ++
      "AFTER THIS PASS: (iii) is CLOSED on the canonical self-referential key " ++
      "(returnSelfRefKey, ReturnSelfRefZResidual); (v) is CLOSED on every r = 0 shell (all " ++
      "L ≤ 15420); and on every gated shell (64(r+1)(L+B+1) < 129L+64, automatic at r = 0) " ++
      "the WHOLE residual (i)–(v) is equivalent to the single Prop olcFibre ctx = ∅.",
    "CLOSED UNCONDITIONALLY (the class-4 band pin, NEW) — the genuine route reaches class 4 " ++
      "only through towerClsOfShell = returnPkg = band index 2 (genuineChargeRoute_eq_four_iff " ++
      "upstream; the exceptional cnlTail ∧ returnCls = 2 branch forces k = 0 " ++
      "(class4_exceptional_k_eq_zero) and 0 is never a carry-window start " ++
      "(zero_notMem_n24Starts, from firstIndexAbove X ≥ 1 via shell_supportCount_pos)). Hence " ++
      "every class-4 start has canonGap q K_k = 2 (class4Fibre_canonGap_eq), equivalently " ++
      "2K_k ≤ q < 4K_k (canonGap_eq_two_iff, class4Fibre_orbit_band), successor numerator " ++
      "4K_k − q (class4Fibre_orbit_step), and the fibre IS the doubly-pinned window filter " ++
      "{k ∈ starts : 129L+64 ≤ 64·gapWindow(k) ∧ canonGap = 2} (mem_class4Fibre_iff, " ++
      "class4Fibre_eq_pinnedFilter, Y_le_windowExcess_iff_gapWindow) — the exact class-4 " ++
      "analogue of mem_class1Fibre_iff. Small-modulus closure: q ≥ 3 on any shell with a " ++
      "class-4 start (modulus_ge_three_of_class4Fibre_nonempty, " ++
      "class4Fibre_empty_of_modulus_lt_three).",
    "REDUCED (the K.1 gate dichotomy, NEW) — under the numeric gate 64(r+1)(L+B+1) < 129L+64 " ++
      "(the SAME gate as class 1; automatic on r = 0, i.e. all L ≤ 15420 via " ++
      "n24_r_eq_zero_of_L_le): every class-4 start overruns the shell-window top " ++
      "(class4Fibre_window_overrun), |fibre₄| ≤ r + 1 (class4Fibre_card_le_of_gapCeiling), on " ++
      "r = 0 the fibre is pinned inside the SINGLE topmost start (class4Fibre_top_of_r_eq_zero, " ++
      "class4Fibre_card_le_one_of_r_eq_zero), and the K.1 interior field holds IFF the fibre " ++
      "is empty (class4Interior_iff_fibre_empty). Hence Nonempty (ReturnAnchoredZResidual ctx) " ++
      "↔ olcFibre ctx = ∅ on gated shells (zResidual_iff_class4Fibre_empty, also seed/core " ++
      "forms anchoredSeed/Core_iff_class4Fibre_empty); on r = 0 shells the whole Return atom " ++
      "is the ONE membership fact top ∉ olcFibre ctx (zResidual_iff_top_notMem_of_r_eq_zero).",
    "CLOSED UNCONDITIONALLY (hgapDiv on the self-referential key, NEW) — returnSelfRefKey " ++
      "ctx k = Nat.pair (carryVal2 k) (k mod 2^{carryVal2 k}) is the manuscript (e,τ) " ++
      "self-referential congruence key (proof_v4 ~6536); same-slice starts are congruent mod " ++
      "2^{carryVal2 x}, so 2^{carryVal2 x} ∣ (z−x) is a THEOREM (returnSelfRefKey_gapDiv). " ++
      "ReturnSelfRefZResidual = {hzero, hcleanStep, class4Interior, hnumeric} (4 fields, one " ++
      "fewer) bridges to the full Z-residual (toZResidual / toAnchoredCore / toCharge / " ++
      "returnFloor / returnZResidualsOfSelfRef); its numeric follows from the diagonal numeric " ++
      "(return_hnumeric_key_of_diagonal, #keys ≤ |olcFibre|).",
    "CLOSED UNCONDITIONALLY (hnumeric at r = 0, NEW) — returnDyadicMult ctx = max 0 " ++
      "((r+1)(L+B+1) − (2L+1)) vanishes at r = 0 since B + 25 ≤ L " ++
      "(returnDyadicMult_eq_zero_of_r_eq_zero), so the M_L·X smallness holds for EVERY key " ++
      "on every r = ⌊κL⌋ = 0 shell, i.e. the entire L ≤ 15420 range " ++
      "(return_hnumeric_of_r_eq_zero).",
    "NAMED RESIDUAL (the empty-fibre route, NEW — hypothesis, NOT a theorem) — " ++
      "Class4FibreEmpty := ∀ ctx, olcFibre ctx = ∅ (the exact mirror of the CNL " ++
      "Class1FibreEmpty). returnZResidualsOfClass4FibreEmpty supplies the full Z-residual " ++
      "family from it; returnFloor_ofClass4FibreEmpty and erdos260_p9V3_ofClass4FibreEmpty " ++
      "consume it ONLY as an explicitly carried hypothesis. Under a uniform gate it is exactly " ++
      "the Z-residual family (class4FibreEmpty_iff_zResiduals_of_gate). NOT closed: the " ++
      "top-band window gaps are not bounded by the shell ceiling, so a top start CAN carry " ++
      "high excess in the model — no vacuous-closure claim is made.",
    "DIAGONAL SPECIALISATION (sufficient, NOT manuscript-sharp) — ReturnDiagonalZResidual: with " ++
      "key = id all slices are singletons, hzero/hgapDiv hold outright, leaving hcleanStep + " ++
      "class4Interior + the DIAGONAL numeric |olcFibre|·liftLevelBound X·mult ≤ c⋆ξX/6 (the " ++
      "strongest numeric form, #keys = |fibre|). Recorded honestly as a sufficient route; the " ++
      "manuscript-faithful route keeps the (e,τ,P) key with smaller #keys.",
    "PROMOTED (was CONSISTENCY ONLY) — ReturnAnchoredZResidual.ofEmptyFibre: an empty class-4 " ++
      "fibre satisfies the residual trivially. After this pass it is the mpr of the PROVED gate " ++
      "equivalence zResidual_iff_class4Fibre_empty (so on gated shells it is the sharp truth, " ++
      "not a shortcut), and endpoints consume it ONLY through the explicitly named hypothesis " ++
      "Class4FibreEmpty. No claim is made that the fibre is empty: non-empty fibres still " ++
      "demand the genuine (Z) digit facts.",
    "WIRED — returnAnchoredSeedOfZ / returnChargeOfZResiduals / returnPerSliceCoreResidualOfZ / " ++
      "returnPerSliceClosureResidualOfZ / returnFloorOfZ feed the existing ReturnPerSliceClosure " ++
      "bridges; P9V3RunResidual.ofReturnZ + erdos260_p9V3_ofReturnZ supply the Return field of " ++
      "P9V3RunResidual from a Z-residual family and reach Erdos260Statement with the other five " ++
      "class atoms.",
    "NO TRIVIAL CLOSURE — the bridge runs through ReturnClass4AnchoredCore/Seed on the genuine " ++
      "M.3.1 anchored geometry; the constructed arms are clean doublings of the ACTUAL integer " ++
      "carry (CompleteReturnArm, manuscript ~6680); the forbidden all-zero " ++
      "genuineReturnShellInputTrivial route is not used in any form." ]

theorem returnAnchoredUnconditionalStatus_nonempty :
    returnAnchoredUnconditionalStatus ≠ [] := by
  simp [returnAnchoredUnconditionalStatus]

/-! ## 12.  Axiom-cleanliness audit -/

#print axioms returnFibre_le_two_mul
#print axioms returnFibre_carryVal2_le_shell
#print axioms anchoredLongReturnFamily_forces_clean_step
#print axioms anchoredSeed_forces_clean_step
#print axioms anchoredCore_forces_clean_step
#print axioms anchoredSeed_forces_interior
#print axioms olcSlice_nonempty_of_mem_image
#print axioms olcSlice_max'_mem_fibre
#print axioms returnCleanRunOfZeroData
#print axioms ReturnAnchoredZResidual.toAnchoredCore
#print axioms ReturnAnchoredZResidual.toAnchoredSeed
#print axioms ReturnAnchoredZResidual.toCharge
#print axioms ReturnAnchoredZResidual.returnFloor
#print axioms ReturnAnchoredZResidual.perSliceCount
#print axioms ReturnAnchoredZResidual.ofAnchoredCore
#print axioms ReturnAnchoredZResidual.ofAnchoredSeed
#print axioms nonempty_anchoredCore_iff_zResidual
#print axioms nonempty_anchoredSeed_iff_zResidual
#print axioms ReturnAnchoredZResidual.ofEmptyFibre
#print axioms ReturnDiagonalZResidual.toZResidual
#print axioms ReturnDiagonalZResidual.toAnchoredCore
#print axioms ReturnDiagonalZResidual.toCharge
#print axioms ReturnDiagonalZResidual.returnFloor
#print axioms returnAnchoredSeedOfZ
#print axioms returnChargeOfZResiduals
#print axioms returnPerSliceCoreResidualOfZ
#print axioms returnPerSliceClosureResidualOfZ
#print axioms returnFloorOfZ
#print axioms P9V3RunResidual.ofReturnZ
#print axioms erdos260_p9V3_ofReturnZ
#print axioms towerExitClassOfGap_eq_returnPkg_iff
#print axioms canonGap_eq_two_iff
#print axioms class4_exceptional_k_eq_zero
#print axioms n24_firstIndexAbove_pos
#print axioms zero_notMem_n24Starts
#print axioms class4Fibre_canonGap_eq
#print axioms Y_le_windowExcess_iff_gapWindow
#print axioms mem_class4Fibre_iff
#print axioms class4Fibre_eq_pinnedFilter
#print axioms class4Fibre_orbit_band
#print axioms class4Fibre_orbit_step
#print axioms modulus_ge_three_of_class4Fibre_nonempty
#print axioms class4Fibre_empty_of_modulus_lt_three
#print axioms class4Fibre_mem_window
#print axioms class4Fibre_window_overrun
#print axioms class4Fibre_card_le_of_gapCeiling
#print axioms class4_gate_of_r_eq_zero
#print axioms class4Fibre_top_of_r_eq_zero
#print axioms class4Fibre_card_le_one_of_r_eq_zero
#print axioms class4Interior_iff_fibre_empty
#print axioms zResidual_iff_class4Fibre_empty
#print axioms anchoredSeed_iff_class4Fibre_empty
#print axioms anchoredCore_iff_class4Fibre_empty
#print axioms zResidual_iff_class4Fibre_empty_of_r_eq_zero
#print axioms zResidual_iff_class4Fibre_empty_of_L_le
#print axioms zResidual_iff_top_notMem_of_r_eq_zero
#print axioms returnSelfRefKey
#print axioms returnSelfRefKey_gapDiv
#print axioms ReturnSelfRefZResidual.toZResidual
#print axioms ReturnSelfRefZResidual.toAnchoredCore
#print axioms ReturnSelfRefZResidual.toCharge
#print axioms ReturnSelfRefZResidual.returnFloor
#print axioms returnZResidualsOfSelfRef
#print axioms return_hnumeric_key_of_diagonal
#print axioms returnDyadicG0_eq
#print axioms returnDyadicMult_eq_zero_of_r_eq_zero
#print axioms return_hnumeric_of_r_eq_zero
#print axioms Class4FibreEmpty
#print axioms returnZResidualsOfClass4FibreEmpty
#print axioms class4FibreEmpty_iff_zResiduals_of_gate
#print axioms returnFloor_ofClass4FibreEmpty
#print axioms erdos260_p9V3_ofClass4FibreEmpty

end

end Erdos260
