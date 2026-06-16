import Erdos260.Erdos260SplitCapstone

/-!
# The valuation-vs-run-length cap on the Q-odd zero-run clause

This module (NEW; it edits no existing file) shrinks the wave-11 Q-odd val-positive
zero-run clause `QOddValPosZeroRun` (`QOddResetClosure`) via the valuation-vs-length
cap, and then closes it OUTRIGHT level by level.

## 1.  The exact cap (goal 1)

Same-slice val-positive pairs `x < z` of the self-referential key share carry
valuation `v = carryVal2 x >= 1` and spacing `2^v | z - x` (`returnSelfRefKey_gapDiv`),
so `z - x >= 2^v`; the zero-run demand on `(x, z]` is envelope-capped
(`zeroRun_pow_le_envelope`: `2^(z-x) <= Q*(z+2)`), and members are `<= 2X`
(`returnFibre_le_two_mul`).  Chaining: `2^(2^v) <= Q*(2X+2)`, i.e.
`v <= vCap ctx := log2(log2(Q*(2X+2)))` - a DOUBLE-log cap
(`sameKey_zeroRun_val_le_vCap`).  Above the cap, demanded slices are singletons:
the clause is VACUOUS there (`qOddValPosZeroRun_singletons_above_vCap`,
`returnZeroBody_valPos_vacuous_of_val_gt`).  The clause decomposes by valuation
level with only the levels `1 <= v <= vCap` carrying content
(`qOddValPosZeroRun_iff_capped_levels`); the decomposition is UNCONDITIONAL (no
parity input).

## 2.  The band mechanism at low levels (goal 2)

Fibre members are deep (`>= 28 >= 3`), so EVERY demanded run forces the carry
strictly below band on the interior `[x, z-2]` (`sameKey_zeroRun_interior_belowBand`
via `zeroRun_belowBand_interior`; a band position inside would escape within
`<= 3` steps, `band_zeroRun_le_three` / `band_zeroRun_le_one_of_deep` - already at
run length `2`, i.e. ALL of `v >= 1`, not only `2^v > 3`).  The below-band cap
(`belowBand_pow_lt`) gives the strict variant `2^(z-x-1) < Q*(z-1)`
(`sameKey_zeroRun_belowBand_pow_lt`), hence `2^(2^v - 1) < Q*(z-1)`
(`sameKey_valPos_pair_band_cap`) - the same double-log through the band mechanism.
CONSOLIDATION: the envelope route is the sharper single statement
(`Q*(z+2) <= 2*Q*(z-1)` for `z >= 4`), so the consolidated cap is
`2^(2^v) <= Q*(z+2)` and `vCap` is defined through it.

## 3.  THE FULL PER-LEVEL COLLAPSE (goals 2+3, beyond the cap)

The cap is NOT the end: at Q odd the reset law closes EVERY level, not just the
levels above `vCap`.  The descent engine: along the demanded zero run the carry
valuation grows by exactly the step count (`carryVal2_add_zeroRun`), so reading
the run BACKWARDS from `z` (valuation `v`), the valuation at `z - v` is `0`; the
reset law (`carryVal2_eq_zero_iff_of_Q_odd`) then demands `z - v` odd AND
`d (z - v) = 1` - but `z - v` lies INSIDE the demanded interval
(`v < 2^v <= z - x`), where the run demands `d (z - v) = 0`.  Outright
contradiction at EVERY valuation level, `v = 0` included
(`sameKey_zeroRun_refuted_of_Q_odd` - the wave-11 val-0 refutation is the `v = 0`
instance).  Consequences: each level closes to a pure counting statement
(`qOddValPosZeroRunAt_iff_singleton`), the whole val-positive clause IS
"val-positive slices are singletons" (`qOddValPosZeroRun_iff_valPosSingletons`),
and `ReturnZeroBody` at Q odd IS injectivity of the self-referential key on the
fibre (`returnZeroBody_iff_keyInjOn_of_Q_odd`) - ZERO digit content remains.

## 4.  The v = 1 level - who the members are (goal 3)

The positional dictionary: at Q odd and `N >= 2`, `carryVal2 N = 1` iff `N` is
EVEN and the digit pair `(d (N-1), d N)` matches one of three patterns -
`(1, 0)` (non-hit preceded by an odd-position hit), `(1, 1)` with `N % 4 = 0`, or
`(0, 1)` with `N % 4 = 2` (`carryVal2_eq_one_iff_of_Q_odd`, via the mod-4 carry
dictionary `carryVal2_eq_one_iff_emod_four` and the predecessor parity
`carryOf_pred_emod_two_of_Q_odd`).  All val-1 members are even, so they ALL share
the single key `Nat.pair 1 0` (`returnSelfRefKey_eq_pairOneZero_of_val1`): under
the demand there is AT MOST ONE val-1 member in the whole fibre
(`qOddValPosZeroRun_val1_card_le_one`) - exactly parallel to the wave-11 val-0
count.  The two-step digit clash that kills v = 1 pairs is recorded explicitly
(`valOne_pair_zeroRun_digit_clash`): the run demands `d z = d (z-1) = 0`, but
`carryVal2 z = 1` with `d z = 0` forces `d (z-1) = 1`.  General level count:
at most `2^v` val-v members under the demand (`qOddValPosZeroRun_level_card_le_pow`).

## 5.  Capstone bridges (goal 4, additive only)

The successor surface is the counting field `ReturnKeyInjectiveField` (key
injectivity on the fibre under the verbatim wave-8 guards at Q odd); it rebuilds
the wave-11 split field (`returnZeroQOddSplitField_of_keyInjective`), plugs into
the wave-11 split capstone (`splitResidual_withKeyInjective`,
`erdos260_split_of_keyInjective`) and the wave-10 valuation surface
(`valuationResidual_withKeyInjective`, `erdos260_of_keyInjective`).  The exchange
is an EQUIVALENCE, not just a weakening (`qOddReturnZeroSplit_iff_keyInjOn`,
`returnKeyInjectiveField_of_qOddSplitField`).

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 0.  Small helpers -/

/-- `v < 2^v` - the spacing always strictly exceeds the valuation. -/
theorem valSliceCap_self_lt_two_pow : ∀ v : ℕ, v < 2 ^ v := by
  intro v
  induction v with
  | zero => norm_num
  | succ n ih =>
      have h1 : 0 < 2 ^ n := pow_pos (by norm_num) n
      calc n + 1 < 2 ^ n + 1 := by omega
        _ ≤ 2 ^ n + 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- Every fibre member is `>= 2` (indeed `>= L >= 28`). -/
theorem olcFibre_mem_two_le (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ olcFibre ctx) : 2 ≤ k :=
  olcFibre_mem_ge_of_le_depth ctx
    (le_trans (by norm_num) (shellLadderDepth_ge ctx)) hk

/-- Every fibre member is `>= 3` - the deepness consumed by the band-interior
escape. -/
theorem olcFibre_mem_three_le (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ olcFibre ctx) : 3 ≤ k :=
  olcFibre_mem_ge_of_le_depth ctx
    (le_trans (by norm_num) (shellLadderDepth_ge ctx)) hk

/-- A fibre member lies in its own key slice. -/
theorem mem_own_slice (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ olcFibre ctx) :
    k ∈ olcSlice ctx (returnSelfRefKey ctx) (returnSelfRefKey ctx k) := by
  rw [olcSlice_def]
  exact Finset.mem_filter.mpr ⟨hk, rfl⟩

/-- A fibre member with the same key lies in the first member's slice. -/
theorem mem_slice_of_key_eq (ctx : ActualFailureContext) {x z : ℕ}
    (hz : z ∈ olcFibre ctx)
    (hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z) :
    z ∈ olcSlice ctx (returnSelfRefKey ctx) (returnSelfRefKey ctx x) := by
  rw [olcSlice_def]
  exact Finset.mem_filter.mpr ⟨hz, hkey.symm⟩

/-! ## Part 1.  The reset-law descent engine (the master refutation)

A same-key pair `x < z` (ANY common valuation `v`, including `v = 0`) refutes the
zero-run demand on `(x, z]` outright at Q odd: the valuation descends to `0` at
`z - v`, which sits INSIDE the demanded interval (`v < 2^v <= z - x`), and the
reset law demands the hit `d (z - v) = 1` that the run forbids. -/

/-- **The valuation-descent refutation (Q odd)**: a same-key pair `x < z` with a
zero run on `(x, z]` is contradictory - at EVERY valuation level.  Reading the run
backwards from `z`, `carryVal2 (z - v) = carryVal2 z - v = 0`
(`carryVal2_add_zeroRun`), so the reset law forces `d (z - v) = 1`; but
`v < 2^v <= z - x` places `z - v` strictly inside `(x, z]`, where the run demands
`d (z - v) = 0`. -/
theorem sameKey_zeroRun_refuted_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {x z : ℕ} (hx1 : 1 ≤ x)
    (hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z) (hxz : x < z)
    (hrun : ∀ j, x < j → j ≤ z → ctx.d j = 0) : False := by
  have hvz : carryVal2 ctx z = carryVal2 ctx x :=
    (carryVal2_eq_of_returnSelfRefKey_eq ctx hkey).symm
  have hdvd : 2 ^ carryVal2 ctx x ∣ (z - x) := returnSelfRefKey_gapDiv ctx hkey hxz
  have hgap : 2 ^ carryVal2 ctx x ≤ z - x := Nat.le_of_dvd (by omega) hdvd
  have hvlt : carryVal2 ctx x < 2 ^ carryVal2 ctx x :=
    valSliceCap_self_lt_two_pow (carryVal2 ctx x)
  have hvzx : carryVal2 ctx x < z - x := lt_of_lt_of_le hvlt hgap
  have hz0 : ∀ j, z - carryVal2 ctx x < j → j ≤ (z - carryVal2 ctx x) + carryVal2 ctx x →
      ctx.d j = 0 := by
    intro j hj1 hj2
    exact hrun j (by omega) (by omega)
  have hadd := carryVal2_add_zeroRun ctx (z - carryVal2 ctx x) (carryVal2 ctx x) hz0
  have hidx : z - carryVal2 ctx x + carryVal2 ctx x = z := by omega
  rw [hidx] at hadd
  have h0 : carryVal2 ctx (z - carryVal2 ctx x) = 0 := by omega
  obtain ⟨hodd, hhit⟩ := (carryVal2_eq_zero_iff_of_Q_odd ctx hQodd
    (show 1 ≤ z - carryVal2 ctx x by omega)).mp h0
  have hdzv : ctx.d (z - carryVal2 ctx x) = 0 := hrun _ (by omega) (by omega)
  omega

/-! ## Part 2.  The exact valuation cap `vCap` (the envelope route) -/

/-- **The valuation cap**: `vCap ctx = log2(log2(Q*(2X+2)))` - the exact double-log
constant above which demanded same-slice val-positive pairs cannot exist (members
are `<= 2X`, the envelope caps `2^(z-x) <= Q*(z+2)`, the spacing forces
`z - x >= 2^v`). -/
def vCap (ctx : ActualFailureContext) : ℕ :=
  Nat.log 2 (Nat.log 2 (ctx.Q * (2 * ctx.shell.X + 2)))

/-- Slices above a valuation threshold are singletons: every same-key fibre pair
whose common valuation exceeds `V` is degenerate. -/
def ValPosSingletonsAbove (ctx : ActualFailureContext) (V : ℕ) : Prop :=
  ∀ x ∈ olcFibre ctx, ∀ z ∈ olcFibre ctx,
    returnSelfRefKey ctx x = returnSelfRefKey ctx z → V < carryVal2 ctx x → x = z

/-- **The double-exponential collision** on any demanded same-key interval:
`2^(2^(carryVal2 x)) <= Q*(z+2)` (spacing + envelope; no parity, no fibre input
beyond the run). -/
theorem sameKey_zeroRun_doubleExp (ctx : ActualFailureContext) {x z : ℕ}
    (hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z) (hxz : x < z)
    (hrun : ∀ j, x < j → j ≤ z → ctx.d j = 0) :
    2 ^ 2 ^ carryVal2 ctx x ≤ ctx.Q * (z + 2) := by
  have h1 : 2 ^ carryVal2 ctx x ≤ z - x :=
    Nat.le_of_dvd (by omega) (returnSelfRefKey_gapDiv ctx hkey hxz)
  have h2 := zeroRun_pow_le_envelope ctx (le_of_lt hxz) hrun
  calc 2 ^ 2 ^ carryVal2 ctx x ≤ 2 ^ (z - x) :=
        Nat.pow_le_pow_right (by norm_num) h1
    _ ≤ ctx.Q * (z + 2) := h2

/-- **THE EXACT CAP**: a demanded same-key pair with fibre right endpoint has
`carryVal2 x <= vCap ctx = log2(log2(Q*(2X+2)))`. -/
theorem sameKey_zeroRun_val_le_vCap (ctx : ActualFailureContext) {x z : ℕ}
    (hz : z ∈ olcFibre ctx)
    (hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z) (hxz : x < z)
    (hrun : ∀ j, x < j → j ≤ z → ctx.d j = 0) :
    carryVal2 ctx x ≤ vCap ctx := by
  have hde := sameKey_zeroRun_doubleExp ctx hkey hxz hrun
  have hz2X : z ≤ 2 * ctx.shell.X := returnFibre_le_two_mul ctx hz
  have hmono : ctx.Q * (z + 2) ≤ ctx.Q * (2 * ctx.shell.X + 2) :=
    Nat.mul_le_mul (le_refl ctx.Q) (by omega)
  have hpow : 2 ^ 2 ^ carryVal2 ctx x ≤ ctx.Q * (2 * ctx.shell.X + 2) :=
    le_trans hde hmono
  have hlog1 : 2 ^ carryVal2 ctx x ≤ Nat.log 2 (ctx.Q * (2 * ctx.shell.X + 2)) :=
    Nat.le_log_of_pow_le (by norm_num) hpow
  exact Nat.le_log_of_pow_le (by norm_num) hlog1

/-- **Vacuity above the cap**: under the val-positive zero-run demand, slices at
valuation `> vCap` are singletons (UNCONDITIONAL - the envelope route needs no
parity). -/
theorem qOddValPosZeroRun_singletons_above_vCap (ctx : ActualFailureContext)
    (H : QOddValPosZeroRun ctx) : ValPosSingletonsAbove ctx (vCap ctx) := by
  intro x hx z hz hkey hgt
  have hveq : carryVal2 ctx x = carryVal2 ctx z :=
    carryVal2_eq_of_returnSelfRefKey_eq ctx hkey
  rcases Nat.lt_trichotomy x z with hlt | heq | hgt'
  · exfalso
    have hrun := H _ (Finset.mem_image_of_mem _ hx) x (mem_own_slice ctx hx)
      z (mem_slice_of_key_eq ctx hz hkey) hlt (by omega)
    have := sameKey_zeroRun_val_le_vCap ctx hz hkey hlt hrun
    omega
  · exact heq
  · exfalso
    have hrun := H _ (Finset.mem_image_of_mem _ hz) z (mem_own_slice ctx hz)
      x (mem_slice_of_key_eq ctx hx hkey.symm) hgt' (by omega)
    have := sameKey_zeroRun_val_le_vCap ctx hx hkey.symm hgt' hrun
    omega

/-- The weakening: `ReturnZeroBody` yields the val-positive zero-run clause
(through the unconditional wave-11 split). -/
theorem returnZeroBody_valPosZeroRun (ctx : ActualFailureContext)
    (H : ReturnZeroBody ctx) : QOddValPosZeroRun ctx :=
  ((returnZeroBody_iff_qOddSplit_uncond ctx).mp H).2

/-- **The vacuity in `ReturnZeroBody` form** (the requested shape): under the
verbatim demand, any same-key fibre pair at valuation `> vCap` is degenerate -
the zero-run clause is VACUOUS above the cap. -/
theorem returnZeroBody_valPos_vacuous_of_val_gt (ctx : ActualFailureContext)
    (H : ReturnZeroBody ctx) {x z : ℕ}
    (hx : x ∈ olcFibre ctx) (hz : z ∈ olcFibre ctx)
    (hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z)
    (hgt : vCap ctx < carryVal2 ctx x) : x = z :=
  qOddValPosZeroRun_singletons_above_vCap ctx
    (returnZeroBody_valPosZeroRun ctx H) x hx z hz hkey hgt

/-! ## Part 3.  The leveled decomposition -/

/-- The level-`v` zero-run clause: the verbatim demand restricted to same-slice
pairs whose left endpoint has carry valuation exactly `v`. -/
def QOddValPosZeroRunAt (ctx : ActualFailureContext) (v : ℕ) : Prop :=
  ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
    ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y,
      ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
        x < z → carryVal2 ctx x = v → ∀ j, x < j → j ≤ z → ctx.d j = 0

/-- The clause is the conjunction of all its positive levels. -/
theorem qOddValPosZeroRun_iff_forall_levels (ctx : ActualFailureContext) :
    QOddValPosZeroRun ctx ↔ ∀ v, 1 ≤ v → QOddValPosZeroRunAt ctx v := by
  constructor
  · intro H v hv y hy x hx z hz hxz hval j hjx hjz
    exact H y hy x hx z hz hxz (by omega) j hjx hjz
  · intro H y hy x hx z hz hxz hpos j hjx hjz
    exact H (carryVal2 ctx x) hpos y hy x hx z hz hxz rfl j hjx hjz

/-- **THE LEVELED DECOMPOSITION (UNCONDITIONAL)**: the val-positive zero-run clause
is EXACTLY the levels `1 <= v <= vCap` plus singleton slices above the cap - the
levels above `vCap` carry no zero-run content. -/
theorem qOddValPosZeroRun_iff_capped_levels (ctx : ActualFailureContext) :
    QOddValPosZeroRun ctx ↔
      ((∀ v, 1 ≤ v → v ≤ vCap ctx → QOddValPosZeroRunAt ctx v) ∧
        ValPosSingletonsAbove ctx (vCap ctx)) := by
  constructor
  · intro H
    refine ⟨fun v hv1 _ => ?_, qOddValPosZeroRun_singletons_above_vCap ctx H⟩
    intro y hy x hx z hz hxz hval j hjx hjz
    exact H y hy x hx z hz hxz (by omega) j hjx hjz
  · rintro ⟨hlev, hsing⟩
    intro y hy x hx z hz hxz hpos j hjx hjz
    rcases Nat.lt_or_ge (vCap ctx) (carryVal2 ctx x) with hgt | hle
    · have hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z :=
        (key_eq_of_mem_olcSlice hx).trans (key_eq_of_mem_olcSlice hz).symm
      have := hsing x (mem_olcFibre_of_mem_olcSlice hx)
        z (mem_olcFibre_of_mem_olcSlice hz) hkey hgt
      omega
    · exact hlev (carryVal2 ctx x) hpos hle y hy x hx z hz hxz rfl j hjx hjz

/-! ## Part 4.  The band mechanism at the low levels -/

/-- **Demanded runs are fully below band on the interior** `[x, z-2]`: fibre
members are deep (`>= 3`), so ANY band position inside a demanded run would
escape within one step (`band_zeroRun_le_one_of_deep` inside
`zeroRun_belowBand_interior`) - already at run length `2`, i.e. for ALL levels
`v >= 1`, not only `2^v > 3`. -/
theorem sameKey_zeroRun_interior_belowBand (ctx : ActualFailureContext) {x z : ℕ}
    (hx : x ∈ olcFibre ctx)
    (hrun : ∀ j, x < j → j ≤ z → ctx.d j = 0) :
    ∀ N, x ≤ N → N + 1 < z → StrictlyBelowBand ctx N :=
  zeroRun_belowBand_interior ctx (olcFibre_mem_three_le ctx hx) hrun

/-- **The below-band length cap on demanded runs** (the band route): a demanded
run of length `>= 2` from a fibre member forces `2^(z-x-1) < Q*(z-1)` - the
doubling below-band carry must stay under the lower band edge. -/
theorem sameKey_zeroRun_belowBand_pow_lt (ctx : ActualFailureContext) {x z : ℕ}
    (hx : x ∈ olcFibre ctx) (hgap2 : 2 ≤ z - x)
    (hrun : ∀ j, x < j → j ≤ z → ctx.d j = 0) :
    2 ^ (z - x - 1) < ctx.Q * (z - 1) := by
  have hbb := sameKey_zeroRun_interior_belowBand ctx hx hrun
  have hbb' : ∀ N, x ≤ N → N < z - 1 → StrictlyBelowBand ctx N := by
    intro N h1 h2
    exact hbb N h1 (by omega)
  have h := belowBand_pow_lt ctx (show x < z - 1 by omega) hbb'
  have hidx : z - 1 - x = z - x - 1 := by omega
  rwa [hidx] at h

/-- **The band-route double-log cap**: a demanded same-key val-positive pair obeys
`2^(2^v - 1) < Q*(z-1)` - the same double-log smallness through the band-escape
mechanism.  CONSOLIDATION: the envelope route (`sameKey_zeroRun_doubleExp`,
`2^(2^v) <= Q*(z+2)`) is the sharper single statement for `z >= 4` (all fibre
endpoints), so `vCap` is defined through the envelope. -/
theorem sameKey_valPos_pair_band_cap (ctx : ActualFailureContext) {x z : ℕ}
    (hx : x ∈ olcFibre ctx)
    (hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z) (hxz : x < z)
    (hpos : 1 ≤ carryVal2 ctx x)
    (hrun : ∀ j, x < j → j ≤ z → ctx.d j = 0) :
    2 ^ (2 ^ carryVal2 ctx x - 1) < ctx.Q * (z - 1) := by
  have hgap : 2 ^ carryVal2 ctx x ≤ z - x :=
    Nat.le_of_dvd (by omega) (returnSelfRefKey_gapDiv ctx hkey hxz)
  have h2 : 2 ≤ 2 ^ carryVal2 ctx x := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ carryVal2 ctx x := Nat.pow_le_pow_right (by norm_num) hpos
  have hlt := sameKey_zeroRun_belowBand_pow_lt ctx hx (by omega) hrun
  calc 2 ^ (2 ^ carryVal2 ctx x - 1) ≤ 2 ^ (z - x - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
    _ < ctx.Q * (z - 1) := hlt

/-! ## Part 5.  The per-level closures and the full collapse (Q odd) -/

/-- Level-`v` slices are singletons: same-key fibre pairs at valuation exactly `v`
are degenerate. -/
def ValPosLevelSingleton (ctx : ActualFailureContext) (v : ℕ) : Prop :=
  ∀ x ∈ olcFibre ctx, ∀ z ∈ olcFibre ctx,
    returnSelfRefKey ctx x = returnSelfRefKey ctx z → carryVal2 ctx x = v → x = z

/-- **THE PER-LEVEL CLOSURE (Q odd)**: at EVERY positive level `v`, the level-`v`
zero-run clause IS the counting statement "level-`v` slices are singletons" - the
reset-law descent refutes every genuine pair, so the demand has no digit content
at any level. -/
theorem qOddValPosZeroRunAt_iff_singleton (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {v : ℕ} (hv : 1 ≤ v) :
    QOddValPosZeroRunAt ctx v ↔ ValPosLevelSingleton ctx v := by
  constructor
  · intro H x hx z hz hkey hval
    have hveq : carryVal2 ctx x = carryVal2 ctx z :=
      carryVal2_eq_of_returnSelfRefKey_eq ctx hkey
    rcases Nat.lt_trichotomy x z with hlt | heq | hgt
    · exfalso
      have hrun := H _ (Finset.mem_image_of_mem _ hx) x (mem_own_slice ctx hx)
        z (mem_slice_of_key_eq ctx hz hkey) hlt hval
      exact sameKey_zeroRun_refuted_of_Q_odd ctx hQodd
        (olcFibre_mem_one_le ctx hx) hkey hlt hrun
    · exact heq
    · exfalso
      have hrun := H _ (Finset.mem_image_of_mem _ hz) z (mem_own_slice ctx hz)
        x (mem_slice_of_key_eq ctx hx hkey.symm) hgt (by omega)
      exact sameKey_zeroRun_refuted_of_Q_odd ctx hQodd
        (olcFibre_mem_one_le ctx hz) hkey.symm hgt hrun
  · intro H y hy x hx z hz hxz hval j hjx hjz
    have hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z :=
      (key_eq_of_mem_olcSlice hx).trans (key_eq_of_mem_olcSlice hz).symm
    have := H x (mem_olcFibre_of_mem_olcSlice hx)
      z (mem_olcFibre_of_mem_olcSlice hz) hkey hval
    omega

/-- **THE FULL COLLAPSE (Q odd)**: the entire val-positive zero-run clause IS
"val-positive slices are singletons" (`ValPosSingletonsAbove ctx 0`) - no level
survives as a digit demand. -/
theorem qOddValPosZeroRun_iff_valPosSingletons (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) :
    QOddValPosZeroRun ctx ↔ ValPosSingletonsAbove ctx 0 := by
  constructor
  · intro H x hx z hz hkey hpos
    have hveq : carryVal2 ctx x = carryVal2 ctx z :=
      carryVal2_eq_of_returnSelfRefKey_eq ctx hkey
    rcases Nat.lt_trichotomy x z with hlt | heq | hgt
    · exfalso
      have hrun := H _ (Finset.mem_image_of_mem _ hx) x (mem_own_slice ctx hx)
        z (mem_slice_of_key_eq ctx hz hkey) hlt (by omega)
      exact sameKey_zeroRun_refuted_of_Q_odd ctx hQodd
        (olcFibre_mem_one_le ctx hx) hkey hlt hrun
    · exact heq
    · exfalso
      have hrun := H _ (Finset.mem_image_of_mem _ hz) z (mem_own_slice ctx hz)
        x (mem_slice_of_key_eq ctx hx hkey.symm) hgt (by omega)
      exact sameKey_zeroRun_refuted_of_Q_odd ctx hQodd
        (olcFibre_mem_one_le ctx hz) hkey.symm hgt hrun
  · intro H y hy x hx z hz hxz hpos j hjx hjz
    have hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z :=
      (key_eq_of_mem_olcSlice hx).trans (key_eq_of_mem_olcSlice hz).symm
    have := H x (mem_olcFibre_of_mem_olcSlice hx)
      z (mem_olcFibre_of_mem_olcSlice hz) hkey (by omega)
    omega

/-- Injectivity of the self-referential key on the class-4 fibre - the pure
counting statement that the whole Q-odd `returnZero` demand reduces to. -/
def ReturnKeyInjOn (ctx : ActualFailureContext) : Prop :=
  ∀ x ∈ olcFibre ctx, ∀ z ∈ olcFibre ctx,
    returnSelfRefKey ctx x = returnSelfRefKey ctx z → x = z

/-- **THE MASTER EQUIVALENCE (Q odd)**: `ReturnZeroBody` IS injectivity of the
self-referential key on the fibre.  Forward: the reset-law descent refutes every
same-key pair (all valuations, `v = 0` included).  Backward: injectivity makes
every slice a singleton, so the demand is vacuous.  ZERO digit content remains in
the Q-odd `returnZero` lane. -/
theorem returnZeroBody_iff_keyInjOn_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) :
    ReturnZeroBody ctx ↔ ReturnKeyInjOn ctx := by
  constructor
  · intro H x hx z hz hkey
    rcases Nat.lt_trichotomy x z with hlt | heq | hgt
    · exfalso
      have hrun := H _ (Finset.mem_image_of_mem _ hx) x (mem_own_slice ctx hx)
        z (mem_slice_of_key_eq ctx hz hkey) hlt
      exact sameKey_zeroRun_refuted_of_Q_odd ctx hQodd
        (olcFibre_mem_one_le ctx hx) hkey hlt hrun
    · exact heq
    · exfalso
      have hrun := H _ (Finset.mem_image_of_mem _ hz) z (mem_own_slice ctx hz)
        x (mem_slice_of_key_eq ctx hx hkey.symm) hgt
      exact sameKey_zeroRun_refuted_of_Q_odd ctx hQodd
        (olcFibre_mem_one_le ctx hz) hkey.symm hgt hrun
  · intro H y hy x hx z hz hxz j hjx hjz
    have hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z :=
      (key_eq_of_mem_olcSlice hx).trans (key_eq_of_mem_olcSlice hz).symm
    have := H x (mem_olcFibre_of_mem_olcSlice hx)
      z (mem_olcFibre_of_mem_olcSlice hz) hkey
    omega

/-- The count form of the collapse: under `ReturnZeroBody` at Q odd the key image
has FULL cardinality - the fibre injects into its key set. -/
theorem returnZeroBody_image_card_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (H : ReturnZeroBody ctx) :
    ((olcFibre ctx).image (returnSelfRefKey ctx)).card = (olcFibre ctx).card := by
  apply Finset.card_image_of_injOn
  intro x hx z hz h
  exact (returnZeroBody_iff_keyInjOn_of_Q_odd ctx hQodd).mp H
    x (Finset.mem_coe.mp hx) z (Finset.mem_coe.mp hz) h

/-! ## Part 6.  The v = 1 level - the positional dictionary -/

/-- **Val-1 members are even (Q odd)**: an odd position is either a hit (valuation
`0`) or a non-hit whose predecessor is even hence val-positive (valuation `>= 2`). -/
theorem carryVal2_eq_one_even_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {N : ℕ} (hN : 2 ≤ N)
    (h1 : carryVal2 ctx N = 1) : N % 2 = 0 := by
  by_contra hodd
  have hNodd : N % 2 = 1 := by omega
  rcases ctx.hd N with hd | hd
  · have hz0 : ∀ j, N - 1 < j → j ≤ (N - 1) + 1 → ctx.d j = 0 := by
      intro j hj1 hj2
      have hjN : j = N := by omega
      rwa [hjN]
    have hadd := carryVal2_add_zeroRun ctx (N - 1) 1 hz0
    have hidx : N - 1 + 1 = N := by omega
    rw [hidx] at hadd
    have h0 : carryVal2 ctx (N - 1) = 0 := by omega
    obtain ⟨ho, _⟩ := (carryVal2_eq_zero_iff_of_Q_odd ctx hQodd
      (show 1 ≤ N - 1 by omega)).mp h0
    omega
  · have h0 : carryVal2 ctx N = 0 :=
      (carryVal2_eq_zero_iff_of_Q_odd ctx hQodd (by omega)).mpr ⟨hNodd, hd⟩
    omega

/-- **The non-hit val-1 dictionary (Q odd)**: at a non-hit `N >= 2`,
`carryVal2 N = 1` iff `N` is even and the predecessor is a hit - the valuation
descends through the clean step to a reset position. -/
theorem carryVal2_eq_one_iff_prevHit_of_nonhit (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {N : ℕ} (hN : 2 ≤ N) (hd0 : ctx.d N = 0) :
    carryVal2 ctx N = 1 ↔ (N % 2 = 0 ∧ ctx.d (N - 1) = 1) := by
  have hz0 : ∀ j, N - 1 < j → j ≤ (N - 1) + 1 → ctx.d j = 0 := by
    intro j hj1 hj2
    have hjN : j = N := by omega
    rwa [hjN]
  have hadd := carryVal2_add_zeroRun ctx (N - 1) 1 hz0
  have hidx : N - 1 + 1 = N := by omega
  rw [hidx] at hadd
  have hiff := carryVal2_eq_zero_iff_of_Q_odd ctx hQodd (show 1 ≤ N - 1 by omega)
  constructor
  · intro h1
    have h0 : carryVal2 ctx (N - 1) = 0 := by omega
    obtain ⟨ho, hh⟩ := hiff.mp h0
    exact ⟨by omega, hh⟩
  · rintro ⟨hNe, hprev⟩
    have h0 : carryVal2 ctx (N - 1) = 0 := hiff.mpr ⟨by omega, hprev⟩
    omega

/-- **The mod-4 bridge**: `carryVal2 N = 1` iff the integer carry is `≡ 2 (mod 4)`
(any parity of `Q`; positivity from `carryOf_pos`). -/
theorem carryVal2_eq_one_iff_emod_four (ctx : ActualFailureContext) (N : ℕ) :
    carryVal2 ctx N = 1 ↔ carryOf ctx N % 4 = 2 := by
  have hpos : 0 < carryOf ctx N := carryOf_pos ctx N
  have hne : (carryOf ctx N).toNat ≠ 0 := by
    rw [ne_eq, Int.toNat_eq_zero]
    omega
  have hd2 : (2 : ℕ) ∣ (carryOf ctx N).toNat ↔ 1 ≤ carryVal2 ctx N := by
    have h := Nat.Prime.pow_dvd_iff_le_factorization (k := 1) Nat.prime_two hne
    rw [pow_one] at h
    exact h
  have hd4 : (4 : ℕ) ∣ (carryOf ctx N).toNat ↔ 2 ≤ carryVal2 ctx N := by
    have h := Nat.Prime.pow_dvd_iff_le_factorization (k := 2) Nat.prime_two hne
    norm_num at h
    exact h
  have hmod : (carryOf ctx N).toNat % 4 = 2 ↔
      ((2 : ℕ) ∣ (carryOf ctx N).toNat ∧ ¬ (4 : ℕ) ∣ (carryOf ctx N).toNat) := by
    omega
  have hzmod : carryOf ctx N % 4 = 2 ↔ (carryOf ctx N).toNat % 4 = 2 := by
    omega
  rw [hzmod, hmod, hd2, hd4]
  omega

/-- **The predecessor parity (Q odd, `N` even)**: `carryOf (N-1) ≡ d (N-1) (mod 2)`
- the parity dictionary at the odd predecessor. -/
theorem carryOf_pred_emod_two_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {N : ℕ} (hN : 2 ≤ N) (hNe : N % 2 = 0) :
    carryOf ctx (N - 1) % 2 = (ctx.d (N - 1) : ℤ) % 2 := by
  have hdict := carryOf_emod_two ctx (N - 2)
  rw [show N - 2 + 1 = N - 1 from by omega] at hdict
  have hN1odd : (N - 1) % 2 = 1 := by omega
  have hQN : (ctx.Q * (N - 1)) % 2 = 1 := by
    rw [Nat.mul_mod, hQodd, hN1odd]
  have hnat : (ctx.Q * (N - 1) * ctx.d (N - 1)) % 2 = ctx.d (N - 1) % 2 := by
    rcases ctx.hd (N - 1) with h | h <;> rw [h]
    · simp
    · rw [mul_one]
      omega
  rw [hdict]
  omega

/-- `Q` odd, `N` even: `Q*N ≡ N (mod 4)` - the odd factor is invisible mod 4 on
even arguments. -/
theorem q_mul_emod_four_of_odd_even (Q N : ℕ) (hQ : Q % 2 = 1) (hN : N % 2 = 0) :
    (Q * N) % 4 = N % 4 := by
  obtain ⟨a, ha⟩ : ∃ a, Q = 2 * a + 1 := ⟨Q / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, N = 2 * b := ⟨N / 2, by omega⟩
  subst ha hb
  have hx : (2 * a + 1) * (2 * b) = 4 * (a * b) + 2 * b := by ring
  rw [hx]
  omega

/-- **The hit val-1 dictionary (Q odd, `N` even)**: at a hit `N`, `carryVal2 N = 1`
iff (`N ≡ 0 (mod 4)` and the predecessor is a hit) or (`N ≡ 2 (mod 4)` and the
predecessor is a non-hit) - via the mod-4 carry recurrence. -/
theorem carryVal2_eq_one_iff_of_hit (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {N : ℕ} (hN : 2 ≤ N) (hNe : N % 2 = 0)
    (hd1 : ctx.d N = 1) :
    carryVal2 ctx N = 1 ↔
      ((N % 4 = 0 ∧ ctx.d (N - 1) = 1) ∨ (N % 4 = 2 ∧ ctx.d (N - 1) = 0)) := by
  rw [carryVal2_eq_one_iff_emod_four ctx N]
  have hidx : N - 1 + 1 = N := by omega
  have hrec0 : carryOf ctx (N - 1 + 1)
      = 2 * carryOf ctx (N - 1)
        - (ctx.Q : ℤ) * ((N - 1 + 1 : ℕ) : ℤ) * (ctx.d (N - 1 + 1) : ℤ) := rfl
  rw [hidx, hd1] at hrec0
  have hrec : carryOf ctx N
      = 2 * carryOf ctx (N - 1) - (ctx.Q : ℤ) * ((N : ℕ) : ℤ) := by
    rw [hrec0]
    push_cast
    ring
  have hcast : (ctx.Q : ℤ) * ((N : ℕ) : ℤ) = ((ctx.Q * N : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hcast] at hrec
  have hpar := carryOf_pred_emod_two_of_Q_odd ctx hQodd hN hNe
  have hqn := q_mul_emod_four_of_odd_even ctx.Q N hQodd hNe
  rcases ctx.hd (N - 1) with h | h <;> rw [h] at hpar ⊢ <;> push_cast at hpar <;> omega

/-- **THE COMPLETE VAL-1 POSITIONAL DICTIONARY (Q odd, `N >= 2`)**: `carryVal2 N = 1`
iff `N` is EVEN and the digit pair `(d (N-1), d N)` matches one of the three
patterns - `(1, 0)`, or `(1, 1)` with `N % 4 = 0`, or `(0, 1)` with `N % 4 = 2`.
The val-1 members are exactly the even positions one clean or one matched-hit step
after the parity-correct support pattern. -/
theorem carryVal2_eq_one_iff_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {N : ℕ} (hN : 2 ≤ N) :
    carryVal2 ctx N = 1 ↔
      (N % 2 = 0 ∧
        ((ctx.d N = 0 ∧ ctx.d (N - 1) = 1) ∨
         (ctx.d N = 1 ∧ N % 4 = 0 ∧ ctx.d (N - 1) = 1) ∨
         (ctx.d N = 1 ∧ N % 4 = 2 ∧ ctx.d (N - 1) = 0))) := by
  constructor
  · intro h1
    have hNe : N % 2 = 0 := carryVal2_eq_one_even_of_Q_odd ctx hQodd hN h1
    refine ⟨hNe, ?_⟩
    rcases ctx.hd N with hd | hd
    · obtain ⟨_, hprev⟩ :=
        (carryVal2_eq_one_iff_prevHit_of_nonhit ctx hQodd hN hd).mp h1
      exact Or.inl ⟨hd, hprev⟩
    · rcases (carryVal2_eq_one_iff_of_hit ctx hQodd hN hNe hd).mp h1 with
        ⟨h4, hp⟩ | ⟨h4, hp⟩
      · exact Or.inr (Or.inl ⟨hd, h4, hp⟩)
      · exact Or.inr (Or.inr ⟨hd, h4, hp⟩)
  · rintro ⟨hNe, hcase⟩
    rcases hcase with ⟨hd, hp⟩ | ⟨hd, h4, hp⟩ | ⟨hd, h4, hp⟩
    · exact (carryVal2_eq_one_iff_prevHit_of_nonhit ctx hQodd hN hd).mpr ⟨hNe, hp⟩
    · exact (carryVal2_eq_one_iff_of_hit ctx hQodd hN hNe hd).mpr (Or.inl ⟨h4, hp⟩)
    · exact (carryVal2_eq_one_iff_of_hit ctx hQodd hN hNe hd).mpr (Or.inr ⟨h4, hp⟩)

/-- The fibre form of the dictionary: who the val-1 fibre members ARE. -/
theorem olcFibre_val1_structure_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {k : ℕ} (hk : k ∈ olcFibre ctx)
    (h1 : carryVal2 ctx k = 1) :
    k % 2 = 0 ∧
      ((ctx.d k = 0 ∧ ctx.d (k - 1) = 1) ∨
       (ctx.d k = 1 ∧ k % 4 = 0 ∧ ctx.d (k - 1) = 1) ∨
       (ctx.d k = 1 ∧ k % 4 = 2 ∧ ctx.d (k - 1) = 0)) :=
  (carryVal2_eq_one_iff_of_Q_odd ctx hQodd (olcFibre_mem_two_le ctx hk)).mp h1

/-- Val-1 fibre members are even. -/
theorem olcFibre_val1_even_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {k : ℕ} (hk : k ∈ olcFibre ctx)
    (h1 : carryVal2 ctx k = 1) : k % 2 = 0 :=
  carryVal2_eq_one_even_of_Q_odd ctx hQodd (olcFibre_mem_two_le ctx hk) h1

/-- **The val-1 key collapse**: every val-1 fibre member has key `Nat.pair 1 0`
(level `1`, residue `0` - they are all even), so ALL val-1 members share ONE
slice, exactly like the val-0 members at `Nat.pair 0 0`. -/
theorem returnSelfRefKey_eq_pairOneZero_of_val1 (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {k : ℕ} (hk : k ∈ olcFibre ctx)
    (h1 : carryVal2 ctx k = 1) :
    returnSelfRefKey ctx k = Nat.pair 1 0 := by
  have heven := olcFibre_val1_even_of_Q_odd ctx hQodd hk h1
  show Nat.pair (carryVal2 ctx k) (k % 2 ^ carryVal2 ctx k) = Nat.pair 1 0
  rw [h1, pow_one, heven]

/-- **The v = 1 hard core, closed to a count**: under the val-positive zero-run
demand at Q odd there is AT MOST ONE val-1 member in the WHOLE fibre - parallel
to the wave-11 val-0 count. -/
theorem qOddValPosZeroRun_val1_card_le_one (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (H : QOddValPosZeroRun ctx) :
    ((olcFibre ctx).filter (fun k => carryVal2 ctx k = 1)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  have hkey : returnSelfRefKey ctx a = returnSelfRefKey ctx b := by
    rw [returnSelfRefKey_eq_pairOneZero_of_val1 ctx hQodd ha.1 ha.2,
        returnSelfRefKey_eq_pairOneZero_of_val1 ctx hQodd hb.1 hb.2]
  exact (qOddValPosZeroRun_iff_valPosSingletons ctx hQodd).mp H
    a ha.1 b hb.1 hkey (by omega)

/-- **The general per-level count**: under the demand at Q odd, level `v >= 1` has
at most `2^v` members - the residue map `k ↦ k % 2^v` is injective on the level
(singleton slices), with range inside `[0, 2^v)`. -/
theorem qOddValPosZeroRun_level_card_le_pow (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (H : QOddValPosZeroRun ctx) {v : ℕ} (hv : 1 ≤ v) :
    ((olcFibre ctx).filter (fun k => carryVal2 ctx k = v)).card ≤ 2 ^ v := by
  have hinj : ∀ a ∈ (olcFibre ctx).filter (fun k => carryVal2 ctx k = v),
      ∀ b ∈ (olcFibre ctx).filter (fun k => carryVal2 ctx k = v),
        a % 2 ^ v = b % 2 ^ v → a = b := by
    intro a ha b hb hres
    rw [Finset.mem_filter] at ha hb
    have hkey : returnSelfRefKey ctx a = returnSelfRefKey ctx b := by
      show Nat.pair (carryVal2 ctx a) (a % 2 ^ carryVal2 ctx a)
          = Nat.pair (carryVal2 ctx b) (b % 2 ^ carryVal2 ctx b)
      rw [ha.2, hb.2, hres]
    exact (qOddValPosZeroRun_iff_valPosSingletons ctx hQodd).mp H
      a ha.1 b hb.1 hkey (by omega)
  have hcard : (((olcFibre ctx).filter (fun k => carryVal2 ctx k = v)).image
      (fun k => k % 2 ^ v)).card
      = ((olcFibre ctx).filter (fun k => carryVal2 ctx k = v)).card :=
    Finset.card_image_of_injOn (fun a ha b hb h =>
      hinj a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) h)
  have hsub : (((olcFibre ctx).filter (fun k => carryVal2 ctx k = v)).image
      (fun k => k % 2 ^ v)) ⊆ Finset.range (2 ^ v) := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨k, _, rfl⟩ := ht
    exact Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))
  have hle := Finset.card_le_card hsub
  rw [Finset.card_range] at hle
  omega

/-- **The v = 1 digit clash, explicit** (the mechanism behind the level-1 closure):
a same-key val-1 pair `x < z` has spacing `2 | z - x`, so the run demands BOTH
`d z = 0` and `d (z-1) = 0`; but `carryVal2 z = 1` with `d z = 0` forces the
predecessor hit `d (z-1) = 1` - the run forbids the very hit the valuation needs. -/
theorem valOne_pair_zeroRun_digit_clash (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {x z : ℕ} (hx1 : 1 ≤ x)
    (hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z) (hxz : x < z)
    (hval : carryVal2 ctx x = 1)
    (hrun : ∀ j, x < j → j ≤ z → ctx.d j = 0) : False := by
  have hvz : carryVal2 ctx z = 1 := by
    have := carryVal2_eq_of_returnSelfRefKey_eq ctx hkey
    omega
  have hdvd : 2 ^ carryVal2 ctx x ∣ (z - x) := returnSelfRefKey_gapDiv ctx hkey hxz
  rw [hval, pow_one] at hdvd
  have hgap : 2 ≤ z - x := Nat.le_of_dvd (by omega) hdvd
  have hdz : ctx.d z = 0 := hrun z hxz le_rfl
  have hdz1 : ctx.d (z - 1) = 0 := hrun (z - 1) (by omega) (by omega)
  obtain ⟨_, hprev⟩ :=
    (carryVal2_eq_one_iff_prevHit_of_nonhit ctx hQodd (show 2 ≤ z by omega) hdz).mp hvz
  omega

/-! ## Part 7.  Capstone bridges (additive only) -/

/-- The split clauses from key injectivity (parity-free): the val-0 at-most-one
clause is the `Nat.pair 0 0` key collapse, the val-positive zero-run clause is
vacuous on singleton slices. -/
theorem qOddReturnZeroSplit_of_keyInjOn (ctx : ActualFailureContext)
    (hinj : ReturnKeyInjOn ctx) : QOddReturnZeroSplit ctx := by
  constructor
  · intro x hx z hz h0x h0z
    apply hinj x hx z hz
    rw [(returnSelfRefKey_eq_pairZero_iff_val0 ctx x).mpr h0x,
        (returnSelfRefKey_eq_pairZero_iff_val0 ctx z).mpr h0z]
  · intro y hy x hx z hz hxz hpos j hjx hjz
    have hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z :=
      (key_eq_of_mem_olcSlice hx).trans (key_eq_of_mem_olcSlice hz).symm
    have := hinj x (mem_olcFibre_of_mem_olcSlice hx)
      z (mem_olcFibre_of_mem_olcSlice hz) hkey
    omega

/-- **The split form IS key injectivity at Q odd** - the exchange loses nothing. -/
theorem qOddReturnZeroSplit_iff_keyInjOn (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) :
    QOddReturnZeroSplit ctx ↔ ReturnKeyInjOn ctx :=
  ⟨fun h => (returnZeroBody_iff_keyInjOn_of_Q_odd ctx hQodd).mp
      ((returnZeroBody_iff_qOddSplit ctx hQodd).mpr h),
   fun h => qOddReturnZeroSplit_of_keyInjOn ctx h⟩

/-- **The successor field**: key injectivity on the class-4 fibre under the
verbatim wave-8 guards, at Q-odd contexts - a PURE COUNTING field (no digit
content). -/
def ReturnKeyInjectiveField : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    ctx.Q % 2 = 1 →
    ReturnKeyInjOn ctx

/-- The counting field rebuilds the wave-11 Q-odd split field. -/
theorem returnZeroQOddSplitField_of_keyInjective (h : ReturnKeyInjectiveField) :
    ReturnZeroQOddSplitField :=
  fun ctx hA hB hC hD hQodd =>
    qOddReturnZeroSplit_of_keyInjOn ctx (h ctx hA hB hC hD hQodd)

/-- The converse: the wave-11 split field already implies the counting field -
the two successor surfaces are interchangeable. -/
theorem returnKeyInjectiveField_of_qOddSplitField (h : ReturnZeroQOddSplitField) :
    ReturnKeyInjectiveField :=
  fun ctx hA hB hC hD hQodd =>
    (returnZeroBody_iff_keyInjOn_of_Q_odd ctx hQodd).mp
      ((returnZeroBody_iff_qOddSplit ctx hQodd).mpr (h ctx hA hB hC hD hQodd))

/-- **The wave-11 split-capstone combinator**: replace the Q-odd `returnZero` field
of any split surface by the counting field. -/
def splitResidual_withKeyInjective (base : Erdos260SplitResidual)
    (h : ReturnKeyInjectiveField) : Erdos260SplitResidual :=
  { base with returnZeroQOddSplit := returnZeroQOddSplitField_of_keyInjective h }

/-- **Endpoint through the wave-11 split capstone**. -/
theorem erdos260_split_of_keyInjective (base : Erdos260SplitResidual)
    (h : ReturnKeyInjectiveField) : Erdos260Statement :=
  erdos260_of_splitResidual (splitResidual_withKeyInjective base h)

/-- **The wave-10 valuation-surface combinator**: the counting field plus the three
remaining per-parity fields rebuild a full `Erdos260ValuationResidual`. -/
def valuationResidual_withKeyInjective (base : Erdos260ValuationResidual)
    (h : ReturnKeyInjectiveField) (hz0 : ReturnZeroQEvenFloorField)
    (hm1 : ReturnMaxCleanQOddSplitField) (hm0 : ReturnMaxCleanQEvenField) :
    Erdos260ValuationResidual :=
  valuationResidual_withQOddSplit base
    (returnZeroQOddSplitField_of_keyInjective h) hz0 hm1 hm0

/-- **Endpoint through the wave-10 valuation surface**. -/
theorem erdos260_of_keyInjective (base : Erdos260ValuationResidual)
    (h : ReturnKeyInjectiveField) (hz0 : ReturnZeroQEvenFloorField)
    (hm1 : ReturnMaxCleanQOddSplitField) (hm0 : ReturnMaxCleanQEvenField) :
    Erdos260Statement :=
  erdos260_of_qOddSplit base
    (returnZeroQOddSplitField_of_keyInjective h) hz0 hm1 hm0

/-! ## Part 8.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the valuation-slice-cap module. -/
def valuationSliceCapStatus : List String :=
  [ "THE EXACT CAP (goal 1): vCap ctx := Nat.log 2 (Nat.log 2 (Q*(2X+2))) - the " ++
      "precise double-log constant.  Derivation: same-slice pairs x < z have " ++
      "spacing 2^(carryVal2 x) | z - x (returnSelfRefKey_gapDiv), the demanded " ++
      "zero run on (x, z] obeys the envelope 2^(z-x) <= Q*(z+2) " ++
      "(zeroRun_pow_le_envelope), and fibre members are <= 2X " ++
      "(returnFibre_le_two_mul); chaining gives 2^(2^v) <= Q*(2X+2) " ++
      "(sameKey_zeroRun_doubleExp) hence v <= vCap (sameKey_zeroRun_val_le_vCap).  " ++
      "Above the cap the demanded slices are singletons - the clause is VACUOUS " ++
      "there (qOddValPosZeroRun_singletons_above_vCap; ReturnZeroBody form " ++
      "returnZeroBody_valPos_vacuous_of_val_gt).  Leveled decomposition " ++
      "(UNCONDITIONAL, no parity): QOddValPosZeroRun <-> (levels 1..vCap, each " ++
      "QOddValPosZeroRunAt v) AND (singletons above vCap) " ++
      "(qOddValPosZeroRun_iff_capped_levels; plain repackaging " ++
      "qOddValPosZeroRun_iff_forall_levels).",
    "THE BAND MECHANISM (goal 2): fibre members are deep (>= 28 >= 3, " ++
      "olcFibre_mem_three_le), so EVERY demanded run - already at length 2, i.e. " ++
      "ALL levels v >= 1, not only 2^v > 3 - forces the carry strictly below band " ++
      "on the interior [x, z-2] (sameKey_zeroRun_interior_belowBand via " ++
      "zeroRun_belowBand_interior; a band position inside would escape within one " ++
      "step at depth >= 3, band_zeroRun_le_one_of_deep, and within 3 steps " ++
      "anywhere, band_zeroRun_le_three).  Below-band cap: 2^(z-x-1) < Q*(z-1) " ++
      "(sameKey_zeroRun_belowBand_pow_lt via belowBand_pow_lt), giving " ++
      "2^(2^v - 1) < Q*(z-1) (sameKey_valPos_pair_band_cap) - the same double-log " ++
      "through the band route.  CONSOLIDATED sharpest single statement: the " ++
      "envelope form 2^(2^v) <= Q*(z+2) (sharper than the band form for z >= 4, " ++
      "since Q*(z+2) <= 2*Q*(z-1) there); vCap is defined through it.",
    "THE FULL COLLAPSE (goals 2+3, STRONGER THAN THE CAP): at Q odd the reset-law " ++
      "descent closes EVERY level outright, not only the levels above vCap.  " ++
      "Engine (sameKey_zeroRun_refuted_of_Q_odd): along the demanded run the " ++
      "valuation grows stepwise (carryVal2_add_zeroRun), so backwards from z " ++
      "(valuation v) the position z - v has valuation 0; the reset law " ++
      "(carryVal2_eq_zero_iff_of_Q_odd) demands d (z-v) = 1, but z - v lies " ++
      "INSIDE (x, z] (v < 2^v <= z - x), where the run demands d (z-v) = 0.  " ++
      "Contradiction at EVERY common valuation, v = 0 included (the wave-11 val-0 " ++
      "refutation is the v = 0 instance).  Per-level closure: QOddValPosZeroRunAt " ++
      "v <-> level-v slices singleton (qOddValPosZeroRunAt_iff_singleton).  Whole " ++
      "clause: QOddValPosZeroRun <-> val-positive slices singleton " ++
      "(qOddValPosZeroRun_iff_valPosSingletons).  MASTER: ReturnZeroBody at Q odd " ++
      "<-> returnSelfRefKey INJECTIVE on the fibre " ++
      "(returnZeroBody_iff_keyInjOn_of_Q_odd); count form " ++
      "returnZeroBody_image_card_of_Q_odd (key image has full cardinality).  ZERO " ++
      "digit content remains in the Q-odd returnZero lane.",
    "THE V = 1 HARD CORE (goal 3): the positional dictionary " ++
      "(carryVal2_eq_one_iff_of_Q_odd, Q odd, N >= 2): carryVal2 N = 1 iff N EVEN " ++
      "and (d N = 0 and d (N-1) = 1) or (d N = 1 and N % 4 = 0 and d (N-1) = 1) " ++
      "or (d N = 1 and N % 4 = 2 and d (N-1) = 0).  Proof route: evenness " ++
      "(carryVal2_eq_one_even_of_Q_odd), the clean-step descent at non-hits " ++
      "(carryVal2_eq_one_iff_prevHit_of_nonhit), the mod-4 carry bridge " ++
      "(carryVal2_eq_one_iff_emod_four: val 1 <-> carryOf = 2 mod 4), the " ++
      "predecessor parity (carryOf_pred_emod_two_of_Q_odd), and Q*N = N mod 4 for " ++
      "even N (q_mul_emod_four_of_odd_even).  Fibre form " ++
      "olcFibre_val1_structure_of_Q_odd.  All val-1 members are EVEN, so they " ++
      "share the ONE key Nat.pair 1 0 (returnSelfRefKey_eq_pairOneZero_of_val1): " ++
      "under the demand there is AT MOST ONE val-1 member in the whole fibre " ++
      "(qOddValPosZeroRun_val1_card_le_one) - parallel to the wave-11 val-0 " ++
      "count.  General level count: at most 2^v members at level v " ++
      "(qOddValPosZeroRun_level_card_le_pow).  The two-step digit clash that " ++
      "kills v = 1 pairs: the run demands d z = d (z-1) = 0 (spacing 2 | z - x), " ++
      "but val z = 1 with d z = 0 forces the predecessor hit d (z-1) = 1 " ++
      "(valOne_pair_zeroRun_digit_clash) - the interval (x, z] contains no hits " ++
      "while the valuation at z needs one just inside.",
    "HONEST ACCOUNTING: nothing here closes returnZero at Q odd outright.  What " ++
      "remains is STRICTLY SMALLER than the wave-11 split surface: the val-" ++
      "positive zero-run clause (a digit demand on all same-slice pairs) is " ++
      "replaced by the pure counting statement 'returnSelfRefKey is injective on " ++
      "the class-4 fibre' (ReturnKeyInjOn) - equivalently, at most one member per " ++
      "(valuation, residue) key; at most one val-0 member, at most one val-1 " ++
      "member, at most 2^v at level v <= vCap.  No in-tree count fact proves " ++
      "injectivity: carryFloor_supportCount_ge_of_le_depth controls hit counts " ++
      "below X but not the fibre's key multiplicities.  The Q-even lanes and the " ++
      "returnMaxClean lanes are untouched (verbatim wave-11 fields).",
    "CAPSTONE BRIDGES (goal 4, additive only): successor field " ++
      "ReturnKeyInjectiveField (key injectivity under the verbatim wave-8 guards " ++
      "at Q odd; PURE COUNTING, no digit content); rebuilds the wave-11 split " ++
      "field (returnZeroQOddSplitField_of_keyInjective) and is implied back by it " ++
      "(returnKeyInjectiveField_of_qOddSplitField) - an interchange, not a " ++
      "weakening (ctx-level qOddReturnZeroSplit_iff_keyInjOn, " ++
      "qOddReturnZeroSplit_of_keyInjOn).  Combinators: " ++
      "splitResidual_withKeyInjective (wave-11 split surface) with endpoint " ++
      "erdos260_split_of_keyInjective; valuationResidual_withKeyInjective " ++
      "(wave-10 valuation surface) with endpoint erdos260_of_keyInjective.",
    "HYGIENE: additive only; no upstream module touched; no sorry / admit / new " ++
      "axiom / native_decide; all #print axioms in [propext, Classical.choice, " ++
      "Quot.sound]." ]

theorem valuationSliceCapStatus_nonempty : valuationSliceCapStatus ≠ [] := by
  simp [valuationSliceCapStatus]

/-! ## Part 9.  Axiom-cleanliness audit -/

#print axioms valSliceCap_self_lt_two_pow
#print axioms olcFibre_mem_two_le
#print axioms olcFibre_mem_three_le
#print axioms mem_own_slice
#print axioms mem_slice_of_key_eq
#print axioms sameKey_zeroRun_refuted_of_Q_odd
#print axioms vCap
#print axioms sameKey_zeroRun_doubleExp
#print axioms sameKey_zeroRun_val_le_vCap
#print axioms qOddValPosZeroRun_singletons_above_vCap
#print axioms returnZeroBody_valPosZeroRun
#print axioms returnZeroBody_valPos_vacuous_of_val_gt
#print axioms qOddValPosZeroRun_iff_forall_levels
#print axioms qOddValPosZeroRun_iff_capped_levels
#print axioms sameKey_zeroRun_interior_belowBand
#print axioms sameKey_zeroRun_belowBand_pow_lt
#print axioms sameKey_valPos_pair_band_cap
#print axioms qOddValPosZeroRunAt_iff_singleton
#print axioms qOddValPosZeroRun_iff_valPosSingletons
#print axioms returnZeroBody_iff_keyInjOn_of_Q_odd
#print axioms returnZeroBody_image_card_of_Q_odd
#print axioms carryVal2_eq_one_even_of_Q_odd
#print axioms carryVal2_eq_one_iff_prevHit_of_nonhit
#print axioms carryVal2_eq_one_iff_emod_four
#print axioms carryOf_pred_emod_two_of_Q_odd
#print axioms q_mul_emod_four_of_odd_even
#print axioms carryVal2_eq_one_iff_of_hit
#print axioms carryVal2_eq_one_iff_of_Q_odd
#print axioms olcFibre_val1_structure_of_Q_odd
#print axioms olcFibre_val1_even_of_Q_odd
#print axioms returnSelfRefKey_eq_pairOneZero_of_val1
#print axioms qOddValPosZeroRun_val1_card_le_one
#print axioms qOddValPosZeroRun_level_card_le_pow
#print axioms valOne_pair_zeroRun_digit_clash
#print axioms qOddReturnZeroSplit_of_keyInjOn
#print axioms qOddReturnZeroSplit_iff_keyInjOn
#print axioms returnZeroQOddSplitField_of_keyInjective
#print axioms returnKeyInjectiveField_of_qOddSplitField
#print axioms splitResidual_withKeyInjective
#print axioms erdos260_split_of_keyInjective
#print axioms valuationResidual_withKeyInjective
#print axioms erdos260_of_keyInjective
#print axioms valuationSliceCapStatus_nonempty

end

end Erdos260
