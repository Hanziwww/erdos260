import Erdos260.ReturnAnchoredUnconditional

/-!
# Return / Class 4 — the closure pass (`ReturnClass4Closure`)

This module (NEW; it edits no existing file) pushes the Return/Class-4 Z-residual frontier of
`ReturnAnchoredUnconditional` further.  Outcome of the three attack lines:

## 1.  `Class4FibreEmpty` outright — PROVABLY BLOCKED on the orbit side (obstruction theorems)

The class-4 fibre is the doubly-pinned window filter
`{k ∈ starts : 129L+64 ≤ 64·gapWindow(k) ∧ canonGap q K_k = 2}` (`mem_class4Fibre_iff`), and the
only unconditional consequences of the band-2 pin are the orbit band `2K_k ≤ q < 4K_k`, the
successor law `K_{k+1} = 4K_k − q` and the modulus floor `q ≥ 3`.  This pass shows the orbit side
can yield NOTHING more:

* **the band-2 fixed point** (`boundedSlopeStep_three_mul`, `slopeOrbit_three_mul`,
  `canonGap_orbit_three_mul`): for every `K ≥ 1` the modulus `q = 3K` makes `K` a fixed point of
  the E.13 step with `canonGap (3K) K = 2`, so the orbit `slopeOrbit (3K) K` sits in band 2 at
  EVERY index — band 2 persists forever; no growth or congruence contradiction exists in the
  recurrence itself (note `K_{j+1} = 4K_j − q` is odd for every `j ≥ 0`, and `q = 3K` with `K`
  odd is an admissible odd modulus);
* **the modulus floor is sharp** (`canonGap_orbit_three`): at `q = 3`, `K₀ = 1` the whole orbit
  is band-2, so `modulus_ge_three_of_class4Fibre_nonempty` cannot be raised: `q ≥ 3` is the
  exact orbit-side threshold (the class-1 analogue `q ≥ 9` is likewise sharp at band 4).

Hence `Class4FibreEmpty` is NOT decidable from the orbit pins: as for class 1, the hit-gap pin
(a property of the actual hit sequence `a`) and the band pin (a property of the recurrent slope
orbit) remain mutually unconstrained in the model, and the gap pin is here only an INEQUALITY
(`≥`), strictly weaker than the class-1 equality — so no integrality (`64 ∣ L`-style) closure
exists either.  No unconditional closure of `Class4FibreEmpty` is claimed.

## 2.  Deep-shell `hnumeric` — CLOSED from a fibre count, unconditionally in the shell

The missing deep-shell ingredient was exponential-vs-polynomial magnitude.  New here:

* **the inverse-tower bound is polynomially small** (`liftLevelBound_two_pow_le`,
  `returnLiftLevelBound_le`): `M_L = liftLevelBound (2^L) ≤ L + 1` (indeed
  `liftLevelBound (2^L) ≤ liftLevelBound L + 1`, the genuinely iterated-logarithmic form
  `liftLevelBound_two_pow_le_succ`);
* **the explicit exponential-vs-polynomial budget** (`return_pow4_le_two_pow`,
  `return_poly_budget`): `3072·(L+1)⁴ ≤ 31·2^L` for every `L ≥ 28` — and `L ≥ 28` holds on
  every actual failure shell (`shellLadderDepth_ge`);
* **the matched-multiplier ceiling** (`returnDyadicMult_le`):
  `returnDyadicMult ctx ≤ (r+1)(L+B+1)`;
* **the count⇒numeric bridge** (`return_hnumeric_of_key_card_le_succ_r`,
  `return_hnumeric_of_fibre_card_le`): if the key image (in particular: the fibre) has at most
  `r + 1` elements, then the `M_L·X` smallness `(#keys)·liftLevelBound X·returnDyadicMult ≤
  c⋆ξX/6` holds for EVERY key on EVERY shell — all `r`, all `L`, no gate.  The whole chain is
  `(#keys)·M_L·mult ≤ (r+1)(L+1)(r+1)(L+B+1) ≤ 2(L+1)⁴ ≤ 31·2^L/1536 = c⋆ξX/6` with
  `r ≤ L` (`proofV4CarryOrder_le_L`) and `B + 25 ≤ L` (`shell_carryLarge`);
* **`hnumeric` is now a THEOREM on every gated shell** (`return_hnumeric_of_gate`): under the
  K.1 gate `64(r+1)(L+B+1) < 129L+64` the proved boundary-band count
  `class4Fibre_card_le_of_gapCeiling` feeds the bridge — extending the previous `r = 0` closure
  (`return_hnumeric_of_r_eq_zero`) to ALL gated shells, for every key.

The genuinely-undischarged count is named: **`Class4FibreSmall`** `:= ∀ ctx, |olcFibre ctx| ≤
r + 1` — strictly weaker than `Class4FibreEmpty` (`class4FibreSmall_of_class4FibreEmpty`), a
THEOREM on every gated shell (`class4Fibre_card_le_of_gapCeiling`) hence on every `r = 0` shell,
i.e. all `L ≤ 15420`; open only on the gate-violating deep shells (necessarily `r ≥ 1`, i.e.
`L ≥ 15421`).  There the telescoping hit-position argument cannot recover it: the interior fibre
population is only bounded by `≈ (r+1)·X/(2L)` in the model (the window can genuinely contain
`X/L`-many high-excess starts), which is exponentially larger than the `poly(L)` the budget can
absorb — the count is genuine M.2/Prop. 23.1 analytic content, not bookkeeping.

## 3.  Digit fields — the residual shrinks to THREE fields (`ReturnClass4DigitResidual`)

With `hgapDiv` closed on the self-referential key (`returnSelfRefKey_gapDiv`) and `hnumeric`
closed from the count, the per-ctx residual is exactly the digit-and-boundary data

* `hzero` — the (Z) all-pairs zero-run on the self-referential slices (M.1.1/M.3);
* `hcleanStep` — one clean step past each class-4 start (M.1.1 trace);
* `class4Interior` — the K.1 active-window interior, now also restated UNGATED as the exact
  top-band emptiness `olcFibre ctx ∩ Ico (i+K−(r+1)) (i+K) = ∅`
  (`class4Interior_iff_topBand_empty`).

`ReturnClass4DigitResidual.toSelfRef` (with the count) rebuilds the full
`ReturnSelfRefZResidual`, hence the full Z-residual, anchored core, V3 charge and capacity floor;
`ofSelfRef` recovers it from any self-referential residual (`nonempty_selfRef_iff_digit_of_card_le`
— the reduction loses nothing given the count).  `returnZResidualsOfDigitAndCount` assembles the
global Z-residual family from `Class4FibreSmall` + a digit-residual family, and
`erdos260_p9V3_ofClass4DigitAndCount` reaches `Erdos260Statement` from exactly these named
residuals plus the other five class atoms.  The digit fields stay genuinely open: by the proved
obstructions (`anchoredSeed_forces_clean_step`) every inhabitant carries real digit content, and
class-4 membership is a hit-gap/orbit condition that does not determine `ctx.d (k+1)` — the
M.2.1 congruence pins SPACING of same-slice starts, not digit VALUES at the pinned positions.

No `sorry`, `axiom`, `admit`, or `native_decide`.  `ReturnAnchoredZResidual.ofEmptyFibre` (and
the new `ReturnClass4DigitResidual.ofEmptyFibre`) are consumed only through proved emptiness
theorems or the explicitly named hypotheses (`Class4FibreEmpty`, `Class4FibreSmall`).
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The inverse-tower bound is polynomially small: `M_L ≤ L + 1`

`liftLevelBound (2^L)` is the manuscript `M_L = O(log* L)`; for the budget arithmetic all we need
is the crude polynomial ceiling `M_L ≤ L + 1`, which follows because the tower already clears
`2^L` one step above `L` (`liftLevel (L+1) = liftLevel L + 2^{liftLevel L} ≥ L + 2^L > 2^L`). -/

/-- **The tower clears the dyadic scale one step above the exponent**: for `L ≥ 1`,
`liftLevelBound (2^L) ≤ L + 1`. -/
theorem liftLevelBound_two_pow_le {L : ℕ} (hL : 1 ≤ L) : liftLevelBound (2 ^ L) ≤ L + 1 := by
  have hlt : 2 ^ L < liftLevel (L + 1) := by
    have h1 : L ≤ liftLevel L := liftLevel_ge_self L
    have h2 : 2 ^ L ≤ 2 ^ liftLevel L := Nat.pow_le_pow_right (by norm_num) h1
    have h3 : liftLevel (L + 1) = liftLevel L + 2 ^ liftLevel L := liftLevel_succ L
    omega
  exact Nat.find_le hlt

/-- **The genuinely iterated-logarithmic form**: `liftLevelBound (2^L) ≤ liftLevelBound L + 1`
(each exponential costs ONE tower level — the manuscript's `log*` recursion). -/
theorem liftLevelBound_two_pow_le_succ (L : ℕ) :
    liftLevelBound (2 ^ L) ≤ liftLevelBound L + 1 := by
  have hspec : L < liftLevel (liftLevelBound L) := liftLevelBound_spec L
  have hlt : 2 ^ L < liftLevel (liftLevelBound L + 1) := by
    have h2 : 2 ^ (L + 1) ≤ 2 ^ liftLevel (liftLevelBound L) :=
      Nat.pow_le_pow_right (by norm_num) hspec
    have h3 : liftLevel (liftLevelBound L + 1)
        = liftLevel (liftLevelBound L) + 2 ^ liftLevel (liftLevelBound L) :=
      liftLevel_succ (liftLevelBound L)
    have h4 : 2 ^ L < 2 ^ (L + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self L)
    omega
  exact Nat.find_le hlt

/-- **The shell form**: on every actual failure context, `liftLevelBound X ≤ L + 1`. -/
theorem returnLiftLevelBound_le (ctx : ActualFailureContext) :
    liftLevelBound ctx.shell.X ≤ shellLadderDepth ctx + 1 := by
  have hXL : ctx.shell.X = 2 ^ shellLadderDepth ctx :=
    Classical.choose_spec ctx.shell.hXdyadic
  have hL : 1 ≤ shellLadderDepth ctx := le_trans (by norm_num) (shellLadderDepth_ge ctx)
  rw [hXL]
  exact liftLevelBound_two_pow_le hL

/-! ## 2.  The explicit exponential-vs-polynomial budget -/

/-- **Quartic-vs-exponential**: `(n+8)⁴ ≤ 2^n` for every `n ≥ 21` (`29⁴ = 707281 ≤ 2²¹`,
and the step ratio `((n+9)/(n+8))⁴ ≤ (30/29)⁴ < 2`). -/
theorem return_pow4_le_two_pow {n : ℕ} (hn : 21 ≤ n) : (n + 8) ^ 4 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hbase : (n + 9) * 29 ≤ (n + 8) * 30 := by omega
    have h1 : (n + 9) ^ 4 * 29 ^ 4 ≤ (n + 8) ^ 4 * 30 ^ 4 := by
      rw [← mul_pow, ← mul_pow]
      exact Nat.pow_le_pow_left hbase 4
    have h2 : (n + 8) ^ 4 * 30 ^ 4 ≤ (n + 8) ^ 4 * 2 * 29 ^ 4 := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ (by norm_num)
    have h4 : (n + 9) ^ 4 ≤ (n + 8) ^ 4 * 2 :=
      Nat.le_of_mul_le_mul_right (le_trans h1 h2) (by norm_num)
    calc (n + 1 + 8) ^ 4 = (n + 9) ^ 4 := by ring
      _ ≤ (n + 8) ^ 4 * 2 := h4
      _ ≤ 2 ^ n * 2 := Nat.mul_le_mul_right 2 ih
      _ = 2 ^ (n + 1) := (pow_succ 2 n).symm

/-- **The K.1.2/L.20 budget comparison**: `3072·(L+1)⁴ ≤ 31·2^L` for every `L ≥ 28` — the
exact numeric margin between the matched count×multiplier polynomial and the `c⋆ξX/6` budget. -/
theorem return_poly_budget {L : ℕ} (hL : 28 ≤ L) : 3072 * (L + 1) ^ 4 ≤ 31 * 2 ^ L := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 7 := ⟨L - 7, by omega⟩
  have hn : 21 ≤ n := by omega
  have h4 : (n + 8) ^ 4 ≤ 2 ^ n := return_pow4_le_two_pow hn
  calc 3072 * (n + 7 + 1) ^ 4 = 24 * ((n + 8) ^ 4 * 128) := by ring
    _ ≤ 24 * (2 ^ n * 128) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right 128 h4)
    _ = 24 * 2 ^ (n + 7) := by rw [pow_add]; norm_num
    _ ≤ 31 * 2 ^ (n + 7) := Nat.mul_le_mul_right _ (by norm_num)

/-! ## 3.  The matched-multiplier ceiling and the count⇒numeric bridge -/

/-- **The matched K.1.2/L.20 multiplier ceiling**:
`returnDyadicMult ctx ≤ (r+1)·(L+B+1)` (drop the `−T` and the `max`). -/
theorem returnDyadicMult_le (ctx : ActualFailureContext) :
    returnDyadicMult ctx
      ≤ ((ctx.n24CarryData.r : ℝ) + 1)
        * ((shellLadderDepth ctx : ℝ) + (carryB ctx.shell.Q : ℝ) + 1) := by
  have hT : ctx.n24CarryData.T = 2 * ((shellLadderDepth ctx : ℕ) : ℝ) + 1 :=
    cnlMulti_n24_T_eq ctx
  have hg0 : ((returnDyadicG0 ctx : ℕ) : ℝ)
      = ((shellLadderDepth ctx : ℕ) : ℝ) + ((carryB ctx.shell.Q : ℕ) : ℝ) + 1 := by
    rw [returnDyadicG0_eq ctx]
    push_cast
    ring
  unfold returnDyadicMult
  rw [hT, hg0]
  apply max_le
  · positivity
  · have hL0 : (0 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith

/-- **The count⇒numeric bridge (the deep-shell `hnumeric` closure).**  If the key image of the
class-4 fibre has at most `r + 1` elements, the matched `M_L·X` smallness holds — for EVERY key,
on EVERY actual failure shell (all `r`, all `L`; no gate).  Chain:
`(#keys)·M_L·mult ≤ (r+1)·(L+1)·(r+1)(L+B+1) ≤ 2(L+1)⁴ ≤ 31·2^L/1536 = c⋆ξX/6`, using
`M_L ≤ L+1` (`returnLiftLevelBound_le`), `r ≤ L` (`proofV4CarryOrder_le_L`), `B + 25 ≤ L`
(`shell_carryLarge`), and the explicit budget `return_poly_budget` at `L ≥ 28`. -/
theorem return_hnumeric_of_key_card_le_succ_r (ctx : ActualFailureContext) (key : ℕ → ℕ)
    (hcard : ((olcFibre ctx).image key).card ≤ ctx.n24CarryData.r + 1) :
    (((olcFibre ctx).image key).card : ℝ) * (liftLevelBound ctx.shell.X : ℝ)
        * returnDyadicMult ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  have hL28 : 28 ≤ shellLadderDepth ctx := shellLadderDepth_ge ctx
  have hB : carryB ctx.shell.Q + 25 ≤ shellLadderDepth ctx := ctx.shell_carryLarge
  have hrL : ctx.n24CarryData.r ≤ shellLadderDepth ctx := by
    rw [cnlMulti_n24_r_eq]
    exact proofV4CarryOrder_le_L ctx.shell
  have hML : liftLevelBound ctx.shell.X ≤ shellLadderDepth ctx + 1 :=
    returnLiftLevelBound_le ctx
  -- the ℕ master inequality `1536·(r+1)(L+1)(r+1)(L+B+1) ≤ 31·2^L`
  have hmaster : 1536 * ((ctx.n24CarryData.r + 1) * ((shellLadderDepth ctx + 1)
        * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
      ≤ 31 * 2 ^ shellLadderDepth ctx := by
    have hr1 : ctx.n24CarryData.r + 1 ≤ shellLadderDepth ctx + 1 := by omega
    have hLB : shellLadderDepth ctx + carryB ctx.shell.Q + 1
        ≤ 2 * (shellLadderDepth ctx + 1) := by omega
    have h1 : (ctx.n24CarryData.r + 1) * ((shellLadderDepth ctx + 1)
          * ((ctx.n24CarryData.r + 1)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)))
        ≤ 2 * (shellLadderDepth ctx + 1) ^ 4 := by
      calc (ctx.n24CarryData.r + 1) * ((shellLadderDepth ctx + 1)
            * ((ctx.n24CarryData.r + 1)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)))
          ≤ (shellLadderDepth ctx + 1) * ((shellLadderDepth ctx + 1)
              * ((shellLadderDepth ctx + 1) * (2 * (shellLadderDepth ctx + 1)))) :=
            Nat.mul_le_mul hr1 (Nat.mul_le_mul_left _ (Nat.mul_le_mul hr1 hLB))
        _ = 2 * (shellLadderDepth ctx + 1) ^ 4 := by ring
    calc 1536 * ((ctx.n24CarryData.r + 1) * ((shellLadderDepth ctx + 1)
          * ((ctx.n24CarryData.r + 1)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 1536 * (2 * (shellLadderDepth ctx + 1) ^ 4) := Nat.mul_le_mul_left _ h1
      _ = 3072 * (shellLadderDepth ctx + 1) ^ 4 := by ring
      _ ≤ 31 * 2 ^ shellLadderDepth ctx := return_poly_budget hL28
  -- the real-side budget identity `c⋆ξX/6 = 31·2^L/1536`
  have hX2L : (ctx.shell.X : ℝ) = 2 ^ shellLadderDepth ctx := by
    have h : ctx.shell.X = 2 ^ shellLadderDepth ctx :=
      Classical.choose_spec ctx.shell.hXdyadic
    rw [h]
    push_cast
    ring
  have hRHS : erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
      = 31 * (2 : ℝ) ^ shellLadderDepth ctx / 1536 := by
    rw [show erdos260Constants.cStar = (31 / 16 : ℝ) from rfl,
        show erdos260Constants.ξ = (1 / 16 : ℝ) from rfl, hX2L]
    ring
  -- the three real factor bounds
  have hkeys : (((olcFibre ctx).image key).card : ℝ) ≤ (ctx.n24CarryData.r : ℝ) + 1 := by
    exact_mod_cast hcard
  have hMLr : ((liftLevelBound ctx.shell.X : ℕ) : ℝ) ≤ (shellLadderDepth ctx : ℝ) + 1 := by
    exact_mod_cast hML
  have hmult := returnDyadicMult_le ctx
  have h0keys : (0 : ℝ) ≤ (((olcFibre ctx).image key).card : ℝ) := Nat.cast_nonneg _
  have h0ML : (0 : ℝ) ≤ ((liftLevelBound ctx.shell.X : ℕ) : ℝ) := Nat.cast_nonneg _
  have h0mult : 0 ≤ returnDyadicMult ctx := returnDyadicMult_nonneg ctx
  have h0r1 : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) + 1 := by positivity
  have h0L1 : (0 : ℝ) ≤ (shellLadderDepth ctx : ℝ) + 1 := by positivity
  have hprod : (((olcFibre ctx).image key).card : ℝ) * (liftLevelBound ctx.shell.X : ℝ)
        * returnDyadicMult ctx
      ≤ (((ctx.n24CarryData.r : ℝ) + 1) * ((shellLadderDepth ctx : ℝ) + 1))
        * (((ctx.n24CarryData.r : ℝ) + 1)
          * ((shellLadderDepth ctx : ℝ) + (carryB ctx.shell.Q : ℝ) + 1)) := by
    apply mul_le_mul
    · exact mul_le_mul hkeys hMLr h0ML h0r1
    · exact hmult
    · exact h0mult
    · exact mul_nonneg h0r1 h0L1
  have hgroup : (((ctx.n24CarryData.r : ℝ) + 1) * ((shellLadderDepth ctx : ℝ) + 1))
        * (((ctx.n24CarryData.r : ℝ) + 1)
          * ((shellLadderDepth ctx : ℝ) + (carryB ctx.shell.Q : ℝ) + 1))
      = ((ctx.n24CarryData.r : ℝ) + 1) * (((shellLadderDepth ctx : ℝ) + 1)
        * (((ctx.n24CarryData.r : ℝ) + 1)
          * ((shellLadderDepth ctx : ℝ) + (carryB ctx.shell.Q : ℝ) + 1))) := by ring
  rw [hgroup] at hprod
  have hcast : ((1536 * ((ctx.n24CarryData.r + 1) * ((shellLadderDepth ctx + 1)
        * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)))) : ℕ) : ℝ)
      ≤ ((31 * 2 ^ shellLadderDepth ctx : ℕ) : ℝ) := Nat.cast_le.mpr hmaster
  push_cast at hcast
  rw [hRHS]
  linarith

/-- The bridge with the count taken on the FIBRE (`#keys ≤ |olcFibre|` via `card_image_le`). -/
theorem return_hnumeric_of_fibre_card_le (ctx : ActualFailureContext) (key : ℕ → ℕ)
    (hcard : (olcFibre ctx).card ≤ ctx.n24CarryData.r + 1) :
    (((olcFibre ctx).image key).card : ℝ) * (liftLevelBound ctx.shell.X : ℝ)
        * returnDyadicMult ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  return_hnumeric_of_key_card_le_succ_r ctx key
    (le_trans Finset.card_image_le hcard)

/-- **`hnumeric` is a THEOREM on every gated shell, for every key** — the K.1 gate supplies the
boundary-band count `|olcFibre| ≤ r + 1` (`class4Fibre_card_le_of_gapCeiling`), and the bridge
does the rest.  This extends the previous `r = 0` closure (`return_hnumeric_of_r_eq_zero`) to
ALL shells satisfying `64(r+1)(L+B+1) < 129L + 64`. -/
theorem return_hnumeric_of_gate (ctx : ActualFailureContext)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) (key : ℕ → ℕ) :
    (((olcFibre ctx).image key).card : ℝ) * (liftLevelBound ctx.shell.X : ℝ)
        * returnDyadicMult ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  return_hnumeric_of_fibre_card_le ctx key (class4Fibre_card_le_of_gapCeiling ctx hnum)

/-! ## 4.  The named count residual `Class4FibreSmall` -/

/-- **The named class-4 population residual**: the genuine route charges at most `r + 1` starts
to the Return/Class-4 leaf at every failure context — the J.1.1-shape fibre population bound.
STRICTLY WEAKER than `Class4FibreEmpty`; a THEOREM on every gated shell
(`class4Fibre_card_le_of_gapCeiling`), hence on every `r = 0` shell (all `L ≤ 15420`); open only
on the gate-violating deep shells (`r ≥ 1`, `L ≥ 15421`). -/
def Class4FibreSmall : Prop :=
  ∀ ctx : ActualFailureContext, (olcFibre ctx).card ≤ ctx.n24CarryData.r + 1

/-- The empty-fibre residual implies the population residual (`0 ≤ r + 1`). -/
theorem class4FibreSmall_of_class4FibreEmpty (h : Class4FibreEmpty) : Class4FibreSmall := by
  intro ctx
  rw [h ctx]
  simp

/-- On uniformly gated shell families the population residual is a THEOREM. -/
theorem class4FibreSmall_of_uniform_gate
    (hg : ∀ ctx : ActualFailureContext,
      64 * ((ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    Class4FibreSmall :=
  fun ctx => class4Fibre_card_le_of_gapCeiling ctx (hg ctx)

/-- The per-ctx population bound holds outright on every `r = 0` shell. -/
theorem class4Fibre_card_le_succ_r_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    (olcFibre ctx).card ≤ ctx.n24CarryData.r + 1 := by
  rw [hr]
  exact class4Fibre_card_le_one_of_r_eq_zero ctx hr

/-! ## 5.  The ungated top-band form of the K.1 interior field

Without any gate, the class-4 interior condition is EXACTLY the statement that the fibre avoids
the top `r + 1` window positions (the K.1 endpoint-enlargement band): pure `Ico` arithmetic from
the windowing `i ≤ k < i + K` and `r + 1 ≤ K`. -/

/-- **The K.1 interior field is exactly top-band emptiness** (no gate):
`(∀ k ∈ fibre₄, k + r + 1 < i + K) ↔ fibre₄ ∩ Ico (i + K − (r+1)) (i + K) = ∅`. -/
theorem class4Interior_iff_topBand_empty (ctx : ActualFailureContext) :
    (∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card)
      ↔ olcFibre ctx
          ∩ Finset.Ico
              (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
                + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1))
              (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
                + (supportShell ctx.shell.d ctx.shell.X).card)
          = ∅ := by
  constructor
  · intro hint
    rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    rw [Finset.mem_inter, Finset.mem_Ico] at hk
    have h1 := hint k hk.1
    have h2 := hk.2.1
    omega
  · intro hempty k hk
    by_contra hlt
    have hwin := class4Fibre_mem_window ctx hk
    have hmem : k ∈ olcFibre ctx
        ∩ Finset.Ico
            (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1))
            (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card) := by
      rw [Finset.mem_inter, Finset.mem_Ico]
      exact ⟨hk, by omega, hwin.2⟩
    rw [hempty] at hmem
    exact absurd hmem (Finset.notMem_empty k)

/-! ## 6.  The three-field digit residual and its bridges

After this pass the per-ctx Return atom (at the canonical self-referential key, given the count)
is exactly the digit-and-boundary data below: `hgapDiv` is a theorem on the self-referential key
(`returnSelfRefKey_gapDiv`) and `hnumeric` is supplied by the count⇒numeric bridge. -/

/-- **The Return/Class-4 digit residual** — the three genuinely-undischarged fields at the
self-referential M.2.1 key: the (Z) zero-runs, the clean step, and the K.1 interior. -/
structure ReturnClass4DigitResidual (ctx : ActualFailureContext) where
  /-- **(Z).**  All-pairs zero-run between same-slice starts of the self-referential key. -/
  hzero : ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
    ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y, ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
      x < z → ∀ j, x < j → j ≤ z → ctx.d j = 0
  /-- **(Z′ / M.1.1 trace).**  One clean step past each class-4 start. -/
  hcleanStep : ∀ k ∈ olcFibre ctx, ctx.d (k + 1) = 0
  /-- **K.1 boundary.**  Class-4 descent windows stay strictly inside the shell window
  (equivalently: the fibre avoids the top `r + 1` band, `class4Interior_iff_topBand_empty`). -/
  class4Interior : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
    k + ctx.n24CarryData.r + 1
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card

namespace ReturnClass4DigitResidual

variable {ctx : ActualFailureContext}

/-- **The self-referential residual from the digit residual plus the count** — `hnumeric` is
the count⇒numeric bridge, everything else transports. -/
def toSelfRef (D : ReturnClass4DigitResidual ctx)
    (hcard : (olcFibre ctx).card ≤ ctx.n24CarryData.r + 1) :
    ReturnSelfRefZResidual ctx where
  hzero := D.hzero
  hcleanStep := D.hcleanStep
  class4Interior := D.class4Interior
  hnumeric := return_hnumeric_of_fibre_card_le ctx (returnSelfRefKey ctx) hcard

/-- The full Z-residual from the digit residual plus the count. -/
def toZResidual (D : ReturnClass4DigitResidual ctx)
    (hcard : (olcFibre ctx).card ≤ ctx.n24CarryData.r + 1) :
    ReturnAnchoredZResidual ctx :=
  (D.toSelfRef hcard).toZResidual

/-- The anchored core from the digit residual plus the count. -/
def toAnchoredCore (D : ReturnClass4DigitResidual ctx)
    (hcard : (olcFibre ctx).card ≤ ctx.n24CarryData.r + 1) :
    ReturnClass4AnchoredCore ctx :=
  (D.toSelfRef hcard).toAnchoredCore

/-- The full V3 Return/Class-4 charge from the digit residual plus the count. -/
def toCharge (D : ReturnClass4DigitResidual ctx)
    (hcard : (olcFibre ctx).card ≤ ctx.n24CarryData.r + 1) :
    Class4ReturnPerSliceCharge ctx :=
  (D.toSelfRef hcard).toCharge

/-- The Return capacity floor from the digit residual plus the count. -/
theorem returnFloor (D : ReturnClass4DigitResidual ctx)
    (hcard : (olcFibre ctx).card ≤ ctx.n24CarryData.r + 1) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (D.toSelfRef hcard).returnFloor

/-- The digit residual from any self-referential residual (forget `hnumeric`). -/
def ofSelfRef (R : ReturnSelfRefZResidual ctx) : ReturnClass4DigitResidual ctx where
  hzero := R.hzero
  hcleanStep := R.hcleanStep
  class4Interior := R.class4Interior

/-- **The empty-fibre witness (consistency direction — NOT an unconditional closure).**
Consumed by endpoints only through proved emptiness theorems or the named hypothesis
`Class4FibreEmpty`; under the K.1 gate it is the `mpr` of the proved equivalence
`digitResidual_iff_class4Fibre_empty`. -/
def ofEmptyFibre (ctx : ActualFailureContext) (hempty : olcFibre ctx = ∅) :
    ReturnClass4DigitResidual ctx where
  hzero := fun y hy => absurd hy (by
    rw [hempty, Finset.image_empty]
    exact Finset.notMem_empty y)
  hcleanStep := fun k hk => absurd hk (by
    rw [hempty]
    exact Finset.notMem_empty k)
  class4Interior := fun k hk =>
    absurd (show k ∈ olcFibre ctx from hk) (by
      rw [hempty]
      exact Finset.notMem_empty k)

end ReturnClass4DigitResidual

/-- **Given the count, the digit residual is EXACTLY the self-referential residual** — the
reduction `hnumeric ⇒ count bridge` loses nothing. -/
theorem nonempty_selfRef_iff_digit_of_card_le (ctx : ActualFailureContext)
    (hcard : (olcFibre ctx).card ≤ ctx.n24CarryData.r + 1) :
    Nonempty (ReturnSelfRefZResidual ctx) ↔ Nonempty (ReturnClass4DigitResidual ctx) :=
  ⟨fun h => h.elim fun R => ⟨ReturnClass4DigitResidual.ofSelfRef R⟩,
   fun h => h.elim fun D => ⟨D.toSelfRef hcard⟩⟩

/-- **The gate dichotomy for the digit residual**: under the K.1 numeric gate, the three-field
digit residual is inhabited IFF the class-4 fibre is empty (mirror of
`zResidual_iff_class4Fibre_empty`; the interior field alone decides). -/
theorem digitResidual_iff_class4Fibre_empty (ctx : ActualFailureContext)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    Nonempty (ReturnClass4DigitResidual ctx) ↔ olcFibre ctx = ∅ := by
  constructor
  · rintro ⟨D⟩
    exact (class4Interior_iff_fibre_empty ctx hnum).mp D.class4Interior
  · intro hempty
    exact ⟨ReturnClass4DigitResidual.ofEmptyFibre ctx hempty⟩

/-! ## 7.  Global wiring — the Z-residual family from `Class4FibreSmall` + digit residuals -/

/-- The self-referential residual family from the named count residual plus a digit-residual
family. -/
def returnSelfRefZResidualsOfDigit (hsmall : Class4FibreSmall)
    (D : ∀ ctx : ActualFailureContext, ReturnClass4DigitResidual ctx) :
    ∀ ctx : ActualFailureContext, ReturnSelfRefZResidual ctx :=
  fun ctx => (D ctx).toSelfRef (hsmall ctx)

/-- **The full Z-residual family from the named count residual plus a digit-residual family** —
feeds every wiring endpoint of `ReturnAnchoredUnconditional` §10. -/
def returnZResidualsOfDigitAndCount (hsmall : Class4FibreSmall)
    (D : ∀ ctx : ActualFailureContext, ReturnClass4DigitResidual ctx) :
    ∀ ctx : ActualFailureContext, ReturnAnchoredZResidual ctx :=
  fun ctx => ((D ctx).toSelfRef (hsmall ctx)).toZResidual

/-- The Return capacity floor from the named count residual plus a digit-residual family. -/
theorem returnFloor_ofDigitAndCount (hsmall : Class4FibreSmall)
    (D : ∀ ctx : ActualFailureContext, ReturnClass4DigitResidual ctx) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  returnFloorOfZ (returnZResidualsOfDigitAndCount hsmall D)

/-- The capstone-shaped V3 `returnCharge` family from the named residuals (the root capstone
consumes exactly this shape through `returnChargeOfZResiduals`). -/
def returnChargeOfDigitAndCount (hsmall : Class4FibreSmall)
    (D : ∀ ctx : ActualFailureContext, ReturnClass4DigitResidual ctx) :
    ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx :=
  returnChargeOfZResiduals (returnZResidualsOfDigitAndCount hsmall D)

/-- The goal-1-shaped anchored seed family from the named residuals — the sharpest available
conditional form of `returnAnchoredSeedUnconditional` after this pass. -/
def returnAnchoredSeedOfDigitAndCount (hsmall : Class4FibreSmall)
    (D : ∀ ctx : ActualFailureContext, ReturnClass4DigitResidual ctx) :
    ∀ ctx : ActualFailureContext, ReturnClass4AnchoredSeed ctx :=
  returnAnchoredSeedOfZ (returnZResidualsOfDigitAndCount hsmall D)

/-- **Endpoint.**  `Erdos260Statement` from the named residuals `Class4FibreSmall` + the
digit-residual family plus the other five class atoms — the Return field of `P9V3RunResidual`
is `returnChargeOfZResiduals (returnZResidualsOfDigitAndCount hsmall D)`. -/
theorem erdos260_p9V3_ofClass4DigitAndCount
    (hsmall : Class4FibreSmall)
    (D : ∀ ctx : ActualFailureContext, ReturnClass4DigitResidual ctx)
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual)
        (returnChargeOfZResiduals (returnZResidualsOfDigitAndCount hsmall D))))
    (cnl : Class1CNLInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual)
        (returnChargeOfZResiduals (returnZResidualsOfDigitAndCount hsmall D))))
    (densePackCount : ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card
        ≤ (densePackMarkers
            (v3Budget towerCount (p9V3RunChainOfResidual runResidual)
              (returnChargeOfZResiduals (returnZResidualsOfDigitAndCount hsmall D)))
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
    (returnZResidualsOfDigitAndCount hsmall D) chernoff cnl densePackCount
    windowReach hReach hContain hScale

/-! ## 8.  The band-2 persistence obstruction (the outcome of attack line 1)

The orbit-side analysis of `Class4FibreEmpty` terminates here: the E.13 band-2 window admits a
FIXED POINT of the slope recurrence (`q = 3K`, step `4K − q = K`), so band 2 can persist at every
orbit index, the modulus floor `q ≥ 3` is sharp (`q = 3, K₀ = 1`), and no growth or congruence
contradiction can be extracted from the recurrence alone.  Any closure of `Class4FibreEmpty`
must therefore couple the hit-gap pin to the orbit pin — content the model does not carry. -/

/-- At `q = 3K` the band index of `K` is exactly `2` (`⌊q/K⌋ = 3`, `log₂ 3 = 1`). -/
theorem canonGap_three_mul {K : ℕ} (hK : 1 ≤ K) : canonGap (3 * K) K = 2 := by
  unfold canonGap
  have h3 : 3 * K / K = 3 := Nat.div_eq_of_eq_mul_left hK rfl
  rw [h3]
  have hlog : Nat.log 2 3 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  omega

/-- **The band-2 fixed point**: at `q = 3K` the E.13 step returns `K` itself
(`2²·K − 3K = K`). -/
theorem boundedSlopeStep_three_mul {K : ℕ} (hK : 1 ≤ K) :
    boundedSlopeStep (3 * K) K = K := by
  unfold boundedSlopeStep
  rw [canonGap_three_mul hK]
  ring_nf
  omega

/-- **The orbit at the fixed point is constant**: `slopeOrbit (3K) K j = K` for every `j`. -/
theorem slopeOrbit_three_mul {K : ℕ} (hK : 1 ≤ K) (j : ℕ) :
    slopeOrbit (3 * K) K j = K := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show boundedSlopeStep (3 * K) (slopeOrbit (3 * K) K j) = K
    rw [ih]
    exact boundedSlopeStep_three_mul hK

/-- **Band 2 persists at EVERY orbit index** at the fixed-point modulus `q = 3K` — the formal
witness that the band-2 pin admits persistent orbits, so the orbit recurrence alone can never
refute class-4 fibre membership.  (For `K` odd — e.g. `K = 1`, `q = 3` — the modulus is odd, so
this is an admissible slope datum shape.) -/
theorem canonGap_orbit_three_mul {K : ℕ} (hK : 1 ≤ K) (j : ℕ) :
    canonGap (3 * K) (slopeOrbit (3 * K) K j) = 2 := by
  rw [slopeOrbit_three_mul hK j]
  exact canonGap_three_mul hK

/-- **The modulus floor `q ≥ 3` is SHARP**: at the minimal admissible odd modulus `q = 3`
(`K₀ = 1`) the whole orbit is band-2, so `modulus_ge_three_of_class4Fibre_nonempty` /
`class4Fibre_empty_of_modulus_lt_three` cannot be improved on the orbit side. -/
theorem canonGap_orbit_three (j : ℕ) : canonGap 3 (slopeOrbit 3 1 j) = 2 := by
  simpa using canonGap_orbit_three_mul (K := 1) le_rfl j

/-! ## 9.  Honest machine-readable status -/

/-- The precise status of the Return/Class-4 atom after this closure pass. -/
def returnClass4ClosureStatus : List String :=
  [ "CLOSED UNCONDITIONALLY (M_L is polynomially small, NEW) — liftLevelBound_two_pow_le: " ++
      "liftLevelBound (2^L) ≤ L + 1 for L ≥ 1 (the tower clears 2^L one step above L); " ++
      "liftLevelBound_two_pow_le_succ: liftLevelBound (2^L) ≤ liftLevelBound L + 1 (the " ++
      "genuine log* recursion); returnLiftLevelBound_le: liftLevelBound X ≤ L + 1 on every " ++
      "actual failure shell.",
    "CLOSED UNCONDITIONALLY (exponential-vs-polynomial budget, NEW) — return_pow4_le_two_pow: " ++
      "(n+8)^4 ≤ 2^n for n ≥ 21; return_poly_budget: 3072(L+1)^4 ≤ 31·2^L for L ≥ 28 (and " ++
      "L ≥ 28 on every shell via shellLadderDepth_ge); returnDyadicMult_le: returnDyadicMult " ++
      "≤ (r+1)(L+B+1).",
    "CLOSED FROM THE COUNT (deep-shell hnumeric, NEW — the count⇒numeric bridge) — " ++
      "return_hnumeric_of_key_card_le_succ_r / return_hnumeric_of_fibre_card_le: if " ++
      "#keys ≤ r+1 (in particular |olcFibre| ≤ r+1) then the M_L·X smallness " ++
      "(#keys)·liftLevelBound X·returnDyadicMult ≤ c⋆ξX/6 holds for EVERY key on EVERY " ++
      "shell — all r, all L, NO gate.  Chain: (r+1)(L+1)(r+1)(L+B+1) ≤ 2(L+1)^4 ≤ " ++
      "31·2^L/1536, using r ≤ L (proofV4CarryOrder_le_L) and B + 25 ≤ L (shell_carryLarge).",
    "CLOSED UNCONDITIONALLY (hnumeric on gated shells, NEW) — return_hnumeric_of_gate: under " ++
      "the K.1 gate 64(r+1)(L+B+1) < 129L+64 the proved boundary-band count " ++
      "class4Fibre_card_le_of_gapCeiling gives |olcFibre| ≤ r+1, so hnumeric is a THEOREM " ++
      "for every key there — extending the r = 0 closure (return_hnumeric_of_r_eq_zero) to " ++
      "ALL gated shells.",
    "NAMED RESIDUAL (the population bound, NEW — hypothesis, NOT a theorem in general) — " ++
      "Class4FibreSmall := ∀ ctx, |olcFibre ctx| ≤ r + 1.  Strictly weaker than " ++
      "Class4FibreEmpty (class4FibreSmall_of_class4FibreEmpty); a theorem on uniformly gated " ++
      "families (class4FibreSmall_of_uniform_gate) and per-ctx on every r = 0 shell " ++
      "(class4Fibre_card_le_succ_r_of_r_eq_zero); OPEN exactly on gate-violating deep shells " ++
      "(r ≥ 1, L ≥ 15421).  Obstruction: the telescoping hit-position argument only bounds " ++
      "the interior fibre by ≈ (r+1)X/(2L) in the model (the window genuinely admits X/L-many " ++
      "high-excess starts), exponentially larger than the poly(L) the budget absorbs — the " ++
      "count is genuine M.2/Prop. 23.1 analytic content.",
    "REDUCED, FAITHFULLY (the new frontier: THREE fields, NEW) — ReturnClass4DigitResidual " ++
      "ctx = {hzero (Z zero-runs at the self-referential key), hcleanStep (d(k+1) = 0 on the " ++
      "fibre), class4Interior (K.1 boundary)}: hgapDiv is a theorem at returnSelfRefKey " ++
      "(returnSelfRefKey_gapDiv) and hnumeric is the count bridge.  toSelfRef/toZResidual/" ++
      "toAnchoredCore/toCharge/returnFloor rebuild everything from it plus the count; " ++
      "ofSelfRef recovers it; nonempty_selfRef_iff_digit_of_card_le: given the count the " ++
      "reduction is an EQUIVALENCE.  Under the gate digitResidual_iff_class4Fibre_empty: " ++
      "the three fields collapse to the single Prop olcFibre ctx = ∅.",
    "RESTATED UNGATED (K.1 interior = top-band emptiness, NEW) — " ++
      "class4Interior_iff_topBand_empty: on EVERY shell the interior field is exactly " ++
      "olcFibre ctx ∩ Ico (i+K−(r+1)) (i+K) = ∅ — the fibre avoids the top r+1 window " ++
      "positions (pure Ico arithmetic; no gate).",
    "WIRED — returnSelfRefZResidualsOfDigit / returnZResidualsOfDigitAndCount: the full " ++
      "Z-residual family from Class4FibreSmall + a digit-residual family; " ++
      "returnFloor_ofDigitAndCount: the Return capacity floor; returnChargeOfDigitAndCount / " ++
      "returnAnchoredSeedOfDigitAndCount: the capstone-shaped returnCharge and seed families; " ++
      "erdos260_p9V3_ofClass4DigitAndCount: Erdos260Statement from exactly these named " ++
      "residuals plus the other five class atoms (through erdos260_p9V3_ofReturnZ).",
    "OBSTRUCTION (PROVED — attack line 1 outcome, NEW) — the band-2 orbit pin admits a FIXED " ++
      "POINT: canonGap_three_mul / boundedSlopeStep_three_mul / slopeOrbit_three_mul / " ++
      "canonGap_orbit_three_mul: at q = 3K the orbit is constant K with canonGap = 2 at " ++
      "EVERY index (band 2 persists forever; K_{j+1} = 4K_j − q yields no growth or " ++
      "congruence contradiction).  canonGap_orbit_three: q = 3, K₀ = 1 realizes it at the " ++
      "minimal admissible odd modulus, so the modulus floor q ≥ 3 " ++
      "(modulus_ge_three_of_class4Fibre_nonempty) is SHARP.  Hence Class4FibreEmpty is NOT " ++
      "decidable from the orbit pins; as for class 1, the hit-gap pin and the band pin are " ++
      "mutually unconstrained in the model, and the class-4 gap pin is only an inequality, " ++
      "so no 64 ∣ L-style integrality closure exists either.  No unconditional closure of " ++
      "Class4FibreEmpty is claimed.",
    "HONEST RESIDUAL AFTER THIS PASS (per ctx) — (a) gated shells (incl. ALL L ≤ 15420): the " ++
      "single membership fact olcFibre ctx = ∅ (zResidual_iff_class4Fibre_empty, " ++
      "digitResidual_iff_class4Fibre_empty); (b) gate-violating deep shells (r ≥ 1, " ++
      "L ≥ 15421): the count |olcFibre ctx| ≤ r+1 (Class4FibreSmall) + the digit fields " ++
      "hzero/hcleanStep (genuine M.1.1/(Z) content, forced by every inhabitant — " ++
      "anchoredSeed_forces_clean_step) + the top-band emptiness (class4Interior).  All " ++
      "bridges proved; nothing vacuous; ofEmptyFibre consumed only through the named " ++
      "hypotheses or proved equivalences." ]

theorem returnClass4ClosureStatus_nonempty : returnClass4ClosureStatus ≠ [] := by
  simp [returnClass4ClosureStatus]

/-! ## 10.  Axiom-cleanliness audit -/

#print axioms liftLevelBound_two_pow_le
#print axioms liftLevelBound_two_pow_le_succ
#print axioms returnLiftLevelBound_le
#print axioms return_pow4_le_two_pow
#print axioms return_poly_budget
#print axioms returnDyadicMult_le
#print axioms return_hnumeric_of_key_card_le_succ_r
#print axioms return_hnumeric_of_fibre_card_le
#print axioms return_hnumeric_of_gate
#print axioms Class4FibreSmall
#print axioms class4FibreSmall_of_class4FibreEmpty
#print axioms class4FibreSmall_of_uniform_gate
#print axioms class4Fibre_card_le_succ_r_of_r_eq_zero
#print axioms class4Interior_iff_topBand_empty
#print axioms ReturnClass4DigitResidual.toSelfRef
#print axioms ReturnClass4DigitResidual.toZResidual
#print axioms ReturnClass4DigitResidual.toAnchoredCore
#print axioms ReturnClass4DigitResidual.toCharge
#print axioms ReturnClass4DigitResidual.returnFloor
#print axioms ReturnClass4DigitResidual.ofSelfRef
#print axioms ReturnClass4DigitResidual.ofEmptyFibre
#print axioms nonempty_selfRef_iff_digit_of_card_le
#print axioms digitResidual_iff_class4Fibre_empty
#print axioms returnSelfRefZResidualsOfDigit
#print axioms returnZResidualsOfDigitAndCount
#print axioms returnFloor_ofDigitAndCount
#print axioms returnChargeOfDigitAndCount
#print axioms returnAnchoredSeedOfDigitAndCount
#print axioms erdos260_p9V3_ofClass4DigitAndCount
#print axioms canonGap_three_mul
#print axioms boundedSlopeStep_three_mul
#print axioms slopeOrbit_three_mul
#print axioms canonGap_orbit_three_mul
#print axioms canonGap_orbit_three

end

end Erdos260
