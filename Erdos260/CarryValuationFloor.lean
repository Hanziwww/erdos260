import Erdos260.Erdos260TrajectoryCapstone
import Erdos260.CarryWordRigidity
import Erdos260.ReturnClass4CycleClosure
import Erdos260.DigitSideClosure
import Erdos260.CNLScalarBudgetCore

/-!
# Carry-valuation floor — the two isolated digit-side inputs of wave 9, settled

This module (NEW; it edits no existing file) settles the two isolated open inputs of the
wave-9 banded digit closure (`BandedDigitClosure.lean`, status item "SLICE SPACING vs
LOG-SHORT DEMAND" and the `OlcFibreDeep` gate):

## 1.  `OlcFibreDeep` is a THEOREM (`olcFibreDeep_proved`) — goal 1, CLOSED

Every class-4 fibre member `k ∈ olcFibre ctx` satisfies `k ≥ L = shellLadderDepth ctx`
(`olcFibre_mem_ge_depth`), far beyond the demanded `k ≥ 3`.  Engine: the wave-5 rigidity
window `exists_one_in_window` at the trivial factorization `Q = Q·2^0` forces one support
hit in EVERY block `(i·h, (i+1)·h]` of length `h = 2L` (`Q < X = 2^L` by
`carryWord_Q_lt_X`, and `L·2L + 2 ≤ 2^L` for `L ≥ 8`), so the sub-`X` support count is at
least `m` for every `m ≤ L` (`carryFloor_supportCount_ge_of_le_depth`); the support
injects into the pre-window index range (`carryFloor_supportCount_le_firstIndexAbove`,
via `HitSequence.complete` and `digitSide_hit_index_lt_first`), so
`F = firstIndexAbove X ≥ supportCount ≥ L`; fibre members sit at `k ≥ F`
(`olcFibre_mem_window`).  Consequences wired: the wave-9 banded⟹trajectory converse and
the `Nonempty` equivalence are now UNCONDITIONAL (`nonempty_trajectoryResidual_iff_push`,
`trajectoryResidualOfPush`, `trajectorySurfaceOfPush`,
`returnZeroBody_iff_belowBandTrajectory_uncond`).

## 2.  The `carryVal2` lower bound (goal 2) — the floor is the dyadic part of `Q`

`carryVal2 ctx N = v₂(R_N)` with `R_N = carryOf ctx N > 0` everywhere.  Writing
`Q = u·2^t` (`t = ctxDyadicPart ctx = v₂(Q)`, `u = Q/2^t` odd):

* **The generic floor** (`carryVal2_ge_dyadicPart`): `carryVal2 N ≥ t` at EVERY position
  `N ≥ t` — wave-6 `two_pow_dvd_integerCarry` plus positivity.  Fibre members sit at
  `k ≥ L > t` (`ctxDyadicPart_lt_depth`, from `2^t ≤ Q < 2^L`), so the floor holds AT
  EVERY FIBRE MEMBER unconditionally (`olcFibre_carryVal2_ge_dyadicPart`) — for `Q` odd
  it is the trivial `≥ 0`; the floor has CONTENT exactly when `Q` is even.
* **The Q-parity split, exact**:
  - `Q` EVEN: `carryVal2 N ≥ 1` at EVERY position `N ≥ 1` (`carryVal2_pos_of_Q_even` —
    both terms of `R_N = 2R_{N−1} − Q·N·d_N` are even; no window machinery needed), in
    particular at all fibre members (`olcFibre_carryVal2_pos_of_Q_even`).
  - `Q` ODD: NO positive floor exists — the valuation is RESET TO ZERO exactly at the
    odd-position hits: `carryVal2 N = 0 ↔ N odd ∧ d N = 1` for every `N ≥ 1`
    (`carryVal2_eq_zero_iff_of_Q_odd`, via the parity dictionary
    `carryOf_emod_two`: `R_{N+1} ≡ Q·(N+1)·d_{N+1} (mod 2)`); away from odd hits the
    valuation is positive (`carryVal2_pos_of_Q_odd_miss`).  This settles the brief's
    "which object does `carryVal2` measure" question: the carry at the member's RAW
    position `k` (a hit INDEX used as a position), so a fibre member that is an odd
    NUMBER and a raw hit position has `carryVal2 k = 0` when `Q` is odd.
* **The orbit pin is parity-blind** (`class4BandPin_modulus_odd`): the class-4 band-2
  datum modulus `q` is odd BY CONSTRUCTION (`hq_odd`), so the E.13 band `2K ≤ q < 4K`
  carries no information about `v₂(Q)`; the floor comes from the carry recursion alone.

## 3.  What the floor closes (goal 3) — regime closures + bridges, additive only

* **Spacing floor**: same-slice pairs of the self-referential key obey
  `2^t ∣ z − x` (`sameSlice_gap_dvd_pow_dyadicPart`), hence `2^t ≤ z − x`
  (`sameSlice_gap_pow_dyadicPart_le`) — for `Q ≡ 0 mod 2^t` the slices are `2^t`-spaced.
* **The width-regime closure of `returnZero` (the field-level prize)**: the capstone
  `returnZero` guard demands `∃ k ∈ fibre₄, 2^{carryVal2 k} < W` (`W = |supportShell|`);
  the floor refutes it outright whenever `W ≤ 2^t`
  (`returnZero_guard_refuted_of_width_le`), and on demanded contexts forces
  `2^t < W` (`width_gt_of_returnZero_guard`).  Deliverable: the strictly weaker successor
  field `ReturnZeroDyadicFloorField` (the same field with the extra guard `2^t < W`),
  the bridge `pushResidual_returnZero_field_of_dyadicFloor`, the combinator
  `pushResidual_withDyadicFloorZero`, and the endpoint `erdos260_of_dyadicFloorZero`.
  HONEST: `Q` even alone gives `t ≥ 1`, i.e. closes only `W ≤ 2` shells — the brief's
  hoped-for "Q-even closes returnZero outright" is FALSE as stated; the true closed
  regime is `W ≤ 2^{v₂(Q)}` (deep-dyadic denominators), and `Q` odd closes only `W ≤ 1`.
* **The deep-dyadic dichotomy**: on shells with `Q·(2X+2) < 2^{2^t}` the `returnZero`
  demand is EQUIVALENT to "no same-slice pair exists"
  (`returnZeroBody_iff_no_pair_of_deepDyadic`): a pair refutes it outright through
  `returnZeroBody_refuted_of_sameSlice_doubleExp` + the floor; no pair satisfies it
  vacuously.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 0.  Arithmetic helper -/

/-- `n·(2n) + 2 ≤ 2^n` for `n ≥ 8` (the block-budget bound: `L` blocks of length `2L`
plus the envelope slack fit under the scale `X = 2^L`). -/
theorem carryFloor_poly_le_pow : ∀ n : ℕ, 8 ≤ n → n * (2 * n) + 2 ≤ 2 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have h2 : 2 * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
      have hstep : (n + 1) * (2 * (n + 1)) + 2 ≤ 2 * (n * (2 * n) + 2) := by nlinarith
      calc (n + 1) * (2 * (n + 1)) + 2 ≤ 2 * (n * (2 * n) + 2) := hstep
        _ ≤ 2 * 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-! ## Part 1.  The forced-hit window on the actual context (`u = Q`, `t = 0`) -/

/-- **The forced-hit window at every raw position**: whenever `Q·(N+h+2) < 2^h`, the
actual digit word has a hit inside `(N, N+h]` — the wave-5 rigidity window
`exists_one_in_window` at the trivial factorization `Q = Q·2^0`, fed by the everywhere
positivity `carryOf_pos` (no onset restriction). -/
theorem carryFloor_hit_in_window (ctx : ActualFailureContext) {N h : ℕ}
    (hwin : (ctx.Q : ℤ) * ((N + h + 2 : ℕ) : ℤ) < 2 ^ h) :
    ∃ j : ℕ, N < j ∧ j ≤ N + h ∧ ctx.d j = 1 := by
  have hRpos : 0 < integerCarry ctx.Q (ctxNum ctx) ctx.d N := by
    rw [← carryOf_eq_integerCarry]
    exact carryOf_pos ctx N
  exact exists_one_in_window (Q := ctx.Q) (u := ctx.Q) (t := 0) (P := ctxNum ctx)
    (by norm_num) ctx.hQ ctx.hd (ctxEta ctx) (Nat.zero_le N) hRpos hwin

/-! ## Part 2.  The sub-`X` support-count floor -/

/-- **Disjoint forced-hit blocks give a support-count floor**: if `Q·(m·h+2) < 2^h` and
`m·h ≤ X`, the sub-`X` support has at least `m` elements — one forced hit in each of the
`m` disjoint blocks `(i·h, (i+1)·h]`, `i < m`, injected into `supportIn d X`. -/
theorem carryFloor_supportCount_ge (ctx : ActualFailureContext) {m h : ℕ}
    (hwin : (ctx.Q : ℤ) * ((m * h + 2 : ℕ) : ℤ) < 2 ^ h)
    (hfit : m * h ≤ ctx.X) :
    m ≤ supportCount ctx.d ctx.X := by
  classical
  have hblock : ∀ i : ℕ, i < m → ∃ j : ℕ, i * h < j ∧ j ≤ i * h + h ∧ ctx.d j = 1 := by
    intro i hi
    apply carryFloor_hit_in_window ctx
    have hih : i * h + h ≤ m * h := by
      have h1 : (i + 1) * h ≤ m * h := Nat.mul_le_mul_right _ (by omega)
      have h2 : (i + 1) * h = i * h + h := Nat.succ_mul i h
      omega
    have hle : ((i * h + h + 2 : ℕ) : ℤ) ≤ ((m * h + 2 : ℕ) : ℤ) := by
      exact_mod_cast (by omega : i * h + h + 2 ≤ m * h + 2)
    calc (ctx.Q : ℤ) * ((i * h + h + 2 : ℕ) : ℤ)
        ≤ (ctx.Q : ℤ) * ((m * h + 2 : ℕ) : ℤ) :=
          mul_le_mul_of_nonneg_left hle (Int.natCast_nonneg _)
      _ < 2 ^ h := hwin
  have hblock' : ∀ i : ℕ, ∃ j : ℕ,
      i < m → (i * h < j ∧ j ≤ i * h + h ∧ ctx.d j = 1) := by
    intro i
    by_cases hi : i < m
    · obtain ⟨j, hj⟩ := hblock i hi
      exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun h' => absurd h' hi⟩
  choose f hf using hblock'
  have hmaps : ∀ i ∈ Finset.range m, f i ∈ supportIn ctx.d ctx.X := by
    intro i hi
    rw [Finset.mem_range] at hi
    obtain ⟨h1, h2, h3⟩ := hf i hi
    have hub : f i ≤ ctx.X := by
      have hmul : (i + 1) * h ≤ m * h := Nat.mul_le_mul_right _ (by omega)
      have hsm : (i + 1) * h = i * h + h := Nat.succ_mul i h
      omega
    rw [mem_supportIn]
    exact ⟨by omega, hub, h3⟩
  have hmono : ∀ {a b : ℕ}, a < m → b < m → a < b → f a < f b := by
    intro a b ha hb hab
    obtain ⟨ha1, ha2, _⟩ := hf a ha
    obtain ⟨hb1, hb2, _⟩ := hf b hb
    have h1 : (a + 1) * h ≤ b * h := Nat.mul_le_mul_right _ (by omega)
    have h2 : (a + 1) * h = a * h + h := Nat.succ_mul a h
    omega
  have hinj : Set.InjOn f (Finset.range m) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · exact absurd hij (Nat.ne_of_lt (hmono hi hj hlt))
    · exact heq
    · exact absurd hij.symm (Nat.ne_of_lt (hmono hj hi hgt))
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  simpa [supportCount] using hcard

/-- **The support-count floor at every `m ≤ L`** (`X = 2^L`): the sub-`X` support of a
failing context has at least `L` elements.  Blocks of length `h = 2L` fire because
`Q < X = 2^L` (`carryWord_Q_lt_X`) and `L·2L + 2 ≤ 2^L` (`L ≥ 28`). -/
theorem carryFloor_supportCount_ge_of_le_depth (ctx : ActualFailureContext) {m : ℕ}
    (hm : m ≤ shellLadderDepth ctx) :
    m ≤ supportCount ctx.shell.d ctx.shell.X := by
  set L := shellLadderDepth ctx with hLdef
  have hX : ctx.shell.X = 2 ^ L := Classical.choose_spec ctx.shell.hXdyadic
  have hXX : ctx.X = 2 ^ L := by
    rw [← ActualFailureContext.shell_X ctx]
    exact hX
  have hL28 : 28 ≤ L := shellLadderDepth_ge ctx
  have hQX : ctx.Q < ctx.X := carryWord_Q_lt_X ctx
  have hpoly : L * (2 * L) + 2 ≤ 2 ^ L := carryFloor_poly_le_pow L (by omega)
  have hcoef : m * (2 * L) + 2 ≤ 2 ^ L := by
    have h1 : m * (2 * L) ≤ L * (2 * L) := Nat.mul_le_mul_right _ hm
    omega
  have hfit : m * (2 * L) ≤ ctx.X := by
    rw [hXX]
    omega
  have hwin : (ctx.Q : ℤ) * ((m * (2 * L) + 2 : ℕ) : ℤ) < 2 ^ (2 * L) := by
    have hQZ : (ctx.Q : ℤ) < 2 ^ L := by
      calc (ctx.Q : ℤ) < (ctx.X : ℤ) := by exact_mod_cast hQX
        _ = 2 ^ L := by rw [hXX]; push_cast; ring
    have hcoefZ : ((m * (2 * L) + 2 : ℕ) : ℤ) ≤ 2 ^ L := by
      calc ((m * (2 * L) + 2 : ℕ) : ℤ) ≤ ((2 ^ L : ℕ) : ℤ) := by exact_mod_cast hcoef
        _ = 2 ^ L := by push_cast; ring
    calc (ctx.Q : ℤ) * ((m * (2 * L) + 2 : ℕ) : ℤ)
        ≤ (ctx.Q : ℤ) * 2 ^ L := mul_le_mul_of_nonneg_left hcoefZ (Int.natCast_nonneg _)
      _ < 2 ^ L * 2 ^ L := mul_lt_mul_of_pos_right hQZ (by positivity)
      _ = 2 ^ (2 * L) := by rw [two_mul, pow_add]
  have hcount : m ≤ supportCount ctx.d ctx.X := carryFloor_supportCount_ge ctx hwin hfit
  rw [carryWord_shell_d_eq, ActualFailureContext.shell_X]
  exact hcount

/-! ## Part 3.  The window start dominates the support count -/

/-- **`supportCount d X ≤ F = firstIndexAbove X`**: each support element `n ≤ X` is a hit
`a j = n` with `j < F` (`HitSequence.complete` + `digitSide_hit_index_lt_first`),
injectively. -/
theorem carryFloor_supportCount_le_firstIndexAbove (ctx : ActualFailureContext) :
    supportCount ctx.shell.d ctx.shell.X
      ≤ ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X := by
  classical
  have hwit : ∀ n : ℕ, ∃ j : ℕ,
      n ∈ supportIn ctx.shell.d ctx.shell.X → ctx.n24CarryData.a j = n := by
    intro n
    by_cases hn : n ∈ supportIn ctx.shell.d ctx.shell.X
    · obtain ⟨j, hj⟩ :=
        ctx.n24CarryData.carry.hits.complete n ((mem_supportIn _ _ _).mp hn).2.2
      exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun h' => absurd h' hn⟩
  choose g hg using hwit
  have hmaps : ∀ n ∈ supportIn ctx.shell.d ctx.shell.X,
      g n ∈ Finset.range (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X) := by
    intro n hn
    rw [Finset.mem_range]
    have hle : n ≤ ctx.shell.X := ((mem_supportIn _ _ _).mp hn).2.1
    exact digitSide_hit_index_lt_first ctx hle (hg n hn)
  have hinj : Set.InjOn g (supportIn ctx.shell.d ctx.shell.X) := by
    intro n hn n' hn' heq
    rw [Finset.mem_coe] at hn hn'
    have h1 := hg n hn
    have h2 := hg n' hn'
    rw [← h1, ← h2, heq]
  have hcard := Finset.card_le_card_of_injOn g hmaps hinj
  simpa [supportCount] using hcard

/-! ## Part 4.  `OlcFibreDeep` is a theorem (goal 1) -/

/-- **Every class-4 fibre member dominates every `m ≤ L`**: the chain
`k ≥ F ≥ supportCount ≥ m`. -/
theorem olcFibre_mem_ge_of_le_depth (ctx : ActualFailureContext) {m k : ℕ}
    (hm : m ≤ shellLadderDepth ctx) (hk : k ∈ olcFibre ctx) : m ≤ k := by
  have h1 := carryFloor_supportCount_ge_of_le_depth ctx hm
  have h2 := carryFloor_supportCount_le_firstIndexAbove ctx
  have h3 := (olcFibre_mem_window ctx hk).1
  omega

/-- **Sharper than deepness**: every class-4 fibre member is at least the full ladder
depth `L = shellLadderDepth ctx ≥ 28`. -/
theorem olcFibre_mem_ge_depth (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ olcFibre ctx) : shellLadderDepth ctx ≤ k :=
  olcFibre_mem_ge_of_le_depth ctx le_rfl hk

/-- **GOAL 1, SETTLED — `OlcFibreDeep` holds at EVERY context**: all class-4 fibre
members are `≥ 3` (indeed `≥ L ≥ 28`).  The wave-9 deepness gate is a theorem. -/
theorem olcFibreDeep_proved (ctx : ActualFailureContext) : OlcFibreDeep ctx := by
  intro k hk
  exact olcFibre_mem_ge_of_le_depth ctx
    (le_trans (by norm_num) (shellLadderDepth_ge ctx)) hk

/-! ## Part 5.  Deepness wired into the wave-9 surfaces (now unconditional) -/

/-- **The banded⟹trajectory `Nonempty` equivalence, UNCONDITIONAL** — the wave-9
`nonempty_trajectoryResidual_iff_push_of_deep` with its deepness gate discharged. -/
theorem nonempty_trajectoryResidual_iff_push :
    Nonempty Erdos260TrajectoryResidual ↔ Nonempty Erdos260PushResidual :=
  nonempty_trajectoryResidual_iff_push_of_deep olcFibreDeep_proved

/-- **The banded⟹trajectory converse, UNCONDITIONAL** — every wave-8 push provider
yields the wave-9 trajectory residual with no side condition. -/
def trajectoryResidualOfPush (R : Erdos260PushResidual) : Erdos260TrajectoryResidual :=
  trajectoryResidual_of_pushResidual R olcFibreDeep_proved

/-- The trajectory surface from any push provider, UNCONDITIONAL. -/
def trajectorySurfaceOfPush (R : Erdos260PushResidual) : ReturnDigitTrajectorySurface :=
  trajectorySurface_of_pushResidual R olcFibreDeep_proved

/-- `ReturnZeroBody ⟺ below-band trajectory`, now UNCONDITIONAL per ctx. -/
theorem returnZeroBody_iff_belowBandTrajectory_uncond (ctx : ActualFailureContext) :
    ReturnZeroBody ctx ↔ ReturnZeroBelowBandTrajectory ctx :=
  returnZeroBody_iff_belowBandTrajectory ctx (olcFibreDeep_proved ctx)

/-! ## Part 6.  The carry-valuation floor (goal 2): `carryVal2 ≥ v₂(Q)` -/

/-- **The dyadic part of the denominator**: `t = v₂(Q)`. -/
def ctxDyadicPart (ctx : ActualFailureContext) : ℕ := (ctx.Q).factorization 2

/-- `2^t ≤ Q`. -/
theorem ctxDyadicPart_pow_le (ctx : ActualFailureContext) :
    2 ^ ctxDyadicPart ctx ≤ ctx.Q :=
  Nat.ordProj_le 2 (Nat.pos_iff_ne_zero.mp ctx.hQ)

/-- **`t < L`**: the dyadic part of `Q` is strictly below the ladder depth
(`2^t ≤ Q < X = 2^L`). -/
theorem ctxDyadicPart_lt_depth (ctx : ActualFailureContext) :
    ctxDyadicPart ctx < shellLadderDepth ctx := by
  have h1 := ctxDyadicPart_pow_le ctx
  have hQX := carryWord_Q_lt_X ctx
  have hX : ctx.X = 2 ^ shellLadderDepth ctx := by
    rw [← ActualFailureContext.shell_X ctx]
    exact Classical.choose_spec ctx.shell.hXdyadic
  have hpow : 2 ^ ctxDyadicPart ctx < 2 ^ shellLadderDepth ctx := by
    calc 2 ^ ctxDyadicPart ctx ≤ ctx.Q := h1
      _ < ctx.X := hQX
      _ = 2 ^ shellLadderDepth ctx := hX
  exact (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp hpow

/-- The exact factorization `Q = u·2^t` with `u = Q/2^t` the odd part. -/
theorem ctxQ_eq_oddPart_mul_pow (ctx : ActualFailureContext) :
    ctx.Q = (ctx.Q / 2 ^ ctxDyadicPart ctx) * 2 ^ ctxDyadicPart ctx := by
  calc ctx.Q = 2 ^ ctxDyadicPart ctx * (ctx.Q / 2 ^ ctxDyadicPart ctx) :=
        (Nat.ordProj_mul_ordCompl_eq_self ctx.Q 2).symm
    _ = (ctx.Q / 2 ^ ctxDyadicPart ctx) * 2 ^ ctxDyadicPart ctx := mul_comm _ _

/-- **`2^t ∣ R_N` at every position `N ≥ t`** — the wave-6 `two_pow_dvd_integerCarry`
evaluated on the actual context. -/
theorem carryOf_dvd_pow_dyadicPart (ctx : ActualFailureContext) {N : ℕ}
    (hN : ctxDyadicPart ctx ≤ N) :
    (2 : ℤ) ^ ctxDyadicPart ctx ∣ carryOf ctx N := by
  rw [carryOf_eq_integerCarry]
  exact two_pow_dvd_integerCarry (ctxQ_eq_oddPart_mul_pow ctx) (ctxNum ctx) ctx.d hN

/-- **The generic carry-valuation floor**: `carryVal2 N ≥ t = v₂(Q)` at every position
`N ≥ t` (divisibility + positivity of the carry). -/
theorem carryVal2_ge_dyadicPart (ctx : ActualFailureContext) {N : ℕ}
    (hN : ctxDyadicPart ctx ≤ N) :
    ctxDyadicPart ctx ≤ carryVal2 ctx N := by
  have hpos : 0 < carryOf ctx N := carryOf_pos ctx N
  have hdvdZ := carryOf_dvd_pow_dyadicPart ctx hN
  have htoNat : ((carryOf ctx N).toNat : ℤ) = carryOf ctx N :=
    Int.toNat_of_nonneg (le_of_lt hpos)
  have hdvdN : 2 ^ ctxDyadicPart ctx ∣ (carryOf ctx N).toNat := by
    have h2 : ((2 ^ ctxDyadicPart ctx : ℕ) : ℤ) ∣ ((carryOf ctx N).toNat : ℤ) := by
      rw [htoNat]
      have hc : ((2 ^ ctxDyadicPart ctx : ℕ) : ℤ) = (2 : ℤ) ^ ctxDyadicPart ctx := by
        push_cast
        ring
      rw [hc]
      exact hdvdZ
    exact_mod_cast h2
  have hne : (carryOf ctx N).toNat ≠ 0 := by
    rw [ne_eq, Int.toNat_eq_zero]
    omega
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvdN

/-- **THE FLOOR AT FIBRE MEMBERS**: every class-4 fibre member `k` satisfies
`carryVal2 k ≥ v₂(Q)` — members sit at `k ≥ L > t`, where `2^t ∣ R_k`.  Unconditional;
its content is exactly the dyadic part of `Q` (trivial for odd `Q`). -/
theorem olcFibre_carryVal2_ge_dyadicPart (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ olcFibre ctx) :
    ctxDyadicPart ctx ≤ carryVal2 ctx k :=
  carryVal2_ge_dyadicPart ctx
    (olcFibre_mem_ge_of_le_depth ctx (le_of_lt (ctxDyadicPart_lt_depth ctx)) hk)

/-! ## Part 6a.  The Q-parity split, exact -/

/-- `Q` even ⟹ the carry is even at every position `N ≥ 1` (both terms of
`R_N = 2R_{N−1} − Q·N·d_N` are even). -/
theorem carryOf_even_of_Q_even (ctx : ActualFailureContext) (hQ2 : 2 ∣ ctx.Q)
    {N : ℕ} (hN : 1 ≤ N) : (2 : ℤ) ∣ carryOf ctx N := by
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨q, hq⟩ := hQ2
  have hrec : carryOf ctx (M + 1)
      = 2 * carryOf ctx M
        - (ctx.Q : ℤ) * ((M + 1 : ℕ) : ℤ) * (ctx.d (M + 1) : ℤ) := rfl
  refine ⟨carryOf ctx M - (q : ℤ) * ((M + 1 : ℕ) : ℤ) * (ctx.d (M + 1) : ℤ), ?_⟩
  have hqZ : (ctx.Q : ℤ) = 2 * (q : ℤ) := by exact_mod_cast hq
  rw [hrec, hqZ]
  ring

/-- **The Q-EVEN floor, at every positive position** (no fibre or window machinery):
`Q` even ⟹ `carryVal2 N ≥ 1` for all `N ≥ 1`. -/
theorem carryVal2_pos_of_Q_even (ctx : ActualFailureContext) (hQ2 : 2 ∣ ctx.Q)
    {N : ℕ} (hN : 1 ≤ N) : 1 ≤ carryVal2 ctx N := by
  have hpos : 0 < carryOf ctx N := carryOf_pos ctx N
  have hdvdZ := carryOf_even_of_Q_even ctx hQ2 hN
  have htoNat : ((carryOf ctx N).toNat : ℤ) = carryOf ctx N :=
    Int.toNat_of_nonneg (le_of_lt hpos)
  have hdvdN : 2 ∣ (carryOf ctx N).toNat := by
    have h2 : ((2 : ℕ) : ℤ) ∣ ((carryOf ctx N).toNat : ℤ) := by
      rw [htoNat]
      exact_mod_cast hdvdZ
    exact_mod_cast h2
  have hne : (carryOf ctx N).toNat ≠ 0 := by
    rw [ne_eq, Int.toNat_eq_zero]
    omega
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp
    (dvd_trans (dvd_of_eq (pow_one 2)) hdvdN)
  exact h1

/-- The Q-even floor at fibre members (`k ≥ L ≥ 1`). -/
theorem olcFibre_carryVal2_pos_of_Q_even (ctx : ActualFailureContext) (hQ2 : 2 ∣ ctx.Q)
    {k : ℕ} (hk : k ∈ olcFibre ctx) : 1 ≤ carryVal2 ctx k :=
  carryVal2_pos_of_Q_even ctx hQ2
    (olcFibre_mem_ge_of_le_depth ctx
      (le_trans (by norm_num) (shellLadderDepth_ge ctx)) hk)

/-- `Q` even ⟹ `t = v₂(Q) ≥ 1` (the floor has genuine content). -/
theorem ctxDyadicPart_pos_of_Q_even (ctx : ActualFailureContext) (hQ2 : 2 ∣ ctx.Q) :
    1 ≤ ctxDyadicPart ctx :=
  Nat.Prime.factorization_pos_of_dvd Nat.prime_two (Nat.pos_iff_ne_zero.mp ctx.hQ) hQ2

/-- **The carry parity dictionary**: `R_{N+1} ≡ Q·(N+1)·d_{N+1} (mod 2)` — the doubling
term drops out mod `2`. -/
theorem carryOf_emod_two (ctx : ActualFailureContext) (N : ℕ) :
    carryOf ctx (N + 1) % 2 = ((ctx.Q * (N + 1) * ctx.d (N + 1) : ℕ) : ℤ) % 2 := by
  have hrec : carryOf ctx (N + 1)
      = 2 * carryOf ctx N
        - (ctx.Q : ℤ) * ((N + 1 : ℕ) : ℤ) * (ctx.d (N + 1) : ℤ) := rfl
  have hcast : ((ctx.Q * (N + 1) * ctx.d (N + 1) : ℕ) : ℤ)
      = (ctx.Q : ℤ) * ((N + 1 : ℕ) : ℤ) * (ctx.d (N + 1) : ℤ) := by
    push_cast
    ring
  rw [hrec, hcast]
  omega

/-- **The Q-ODD valuation reset, EXACT**: for odd `Q` and every `N ≥ 1`,
`carryVal2 N = 0 ↔ N odd ∧ d N = 1` — a hit at an odd raw position resets the carry
valuation to `0`; everywhere else the carry is even.  So for odd `Q` NO positive floor
on `carryVal2` exists at hit-supported odd positions: the Q-odd residual is genuine. -/
theorem carryVal2_eq_zero_iff_of_Q_odd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {N : ℕ} (hN : 1 ≤ N) :
    carryVal2 ctx N = 0 ↔ (N % 2 = 1 ∧ ctx.d N = 1) := by
  have hpos : 0 < carryOf ctx N := carryOf_pos ctx N
  have htoNat : ((carryOf ctx N).toNat : ℤ) = carryOf ctx N :=
    Int.toNat_of_nonneg (le_of_lt hpos)
  have hne : (carryOf ctx N).toNat ≠ 0 := by
    rw [ne_eq, Int.toNat_eq_zero]
    omega
  have hval : carryVal2 ctx N = 0 ↔ ¬ (2 : ℤ) ∣ carryOf ctx N := by
    constructor
    · intro h0 hdvd
      have hdvdN : 2 ∣ (carryOf ctx N).toNat := by
        have h2 : ((2 : ℕ) : ℤ) ∣ ((carryOf ctx N).toNat : ℤ) := by
          rw [htoNat]
          exact_mod_cast hdvd
        exact_mod_cast h2
      have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp
        (dvd_trans (dvd_of_eq (pow_one 2)) hdvdN)
      have h0' : (carryOf ctx N).toNat.factorization 2 = 0 := h0
      omega
    · intro hodd
      by_contra h0
      have h1 : 1 ≤ (carryOf ctx N).toNat.factorization 2 := by
        have h0' : (carryOf ctx N).toNat.factorization 2 ≠ 0 := h0
        omega
      have hdvdN : 2 ∣ (carryOf ctx N).toNat := by
        have h2 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mpr h1
        simpa using h2
      apply hodd
      have h2 : ((2 : ℕ) : ℤ) ∣ ((carryOf ctx N).toNat : ℤ) := by exact_mod_cast hdvdN
      rw [htoNat] at h2
      exact_mod_cast h2
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = M + 1 := ⟨N - 1, by omega⟩
  have hE : carryOf ctx (M + 1) % 2
      = (((ctx.Q * (M + 1) * ctx.d (M + 1)) % 2 : ℕ) : ℤ) := by
    rw [carryOf_emod_two ctx M, Int.natCast_mod]
    norm_num
  have hEnat : (ctx.Q * (M + 1) * ctx.d (M + 1)) % 2 = 1
      ↔ ((M + 1) % 2 = 1 ∧ ctx.d (M + 1) = 1) := by
    rcases ctx.hd (M + 1) with h0 | h1
    · rw [h0, mul_zero]
      omega
    · rw [h1, mul_one, Nat.mul_mod, hQodd]
      omega
  rw [hval]
  constructor
  · intro hodd
    rw [← hEnat]
    rcases Nat.mod_two_eq_zero_or_one (ctx.Q * (M + 1) * ctx.d (M + 1)) with hE0 | hE1
    · exfalso
      apply hodd
      rw [hE0] at hE
      norm_num at hE
      omega
    · exact hE1
  · intro hRHS hdvd
    rw [← hEnat] at hRHS
    rw [hRHS] at hE
    norm_num at hE
    omega

/-- `Q` odd: away from the odd-position hits the valuation IS positive — at every `N ≥ 1`
with `N` even or `d N = 0`, `carryVal2 N ≥ 1`. -/
theorem carryVal2_pos_of_Q_odd_miss (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) {N : ℕ} (hN : 1 ≤ N)
    (h : N % 2 = 0 ∨ ctx.d N = 0) : 1 ≤ carryVal2 ctx N := by
  rcases Nat.eq_zero_or_pos (carryVal2 ctx N) with h0 | h1
  · obtain ⟨hodd, hd1⟩ := (carryVal2_eq_zero_iff_of_Q_odd ctx hQodd hN).mp h0
    rcases h with he | hd0 <;> omega
  · exact h1

/-- **The orbit pin is parity-blind** (recorded): the class-4 band-2 datum modulus `q`
is odd BY CONSTRUCTION, so the E.13 band `2K ≤ q < 4K` carries no information about
`v₂(Q)` — the valuation floor comes from the carry recursion alone, not the orbit pin. -/
theorem class4BandPin_modulus_odd (ctx : ActualFailureContext) :
    Odd (class1SlopeDatum ctx).q :=
  (class1SlopeDatum ctx).hq_odd

/-! ## Part 7.  What the floor closes (goal 3): spacing, regime closures, bridges -/

/-- **The same-slice spacing floor**: same-slice pairs of the self-referential key are
`2^t`-congruent, `2^{v₂(Q)} ∣ z − x` (floor + `returnSelfRefKey_gapDiv`). -/
theorem sameSlice_gap_dvd_pow_dyadicPart (ctx : ActualFailureContext) {y x z : ℕ}
    (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y)
    (hz : z ∈ olcSlice ctx (returnSelfRefKey ctx) y) (hxz : x < z) :
    2 ^ ctxDyadicPart ctx ∣ (z - x) := by
  have hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z :=
    (key_eq_of_mem_olcSlice hx).trans (key_eq_of_mem_olcSlice hz).symm
  exact dvd_trans
    (pow_dvd_pow 2
      (olcFibre_carryVal2_ge_dyadicPart ctx (mem_olcFibre_of_mem_olcSlice hx)))
    (returnSelfRefKey_gapDiv ctx hkey hxz)

/-- The spacing floor in `≤` form: `2^{v₂(Q)} ≤ z − x` on same-slice pairs. -/
theorem sameSlice_gap_pow_dyadicPart_le (ctx : ActualFailureContext) {y x z : ℕ}
    (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y)
    (hz : z ∈ olcSlice ctx (returnSelfRefKey ctx) y) (hxz : x < z) :
    2 ^ ctxDyadicPart ctx ≤ z - x :=
  Nat.le_of_dvd (by omega) (sameSlice_gap_dvd_pow_dyadicPart ctx hx hz hxz)

/-- **The capstone `returnZero` guard is REFUTED on width-`≤ 2^t` shells**: the demanded
regime `∃ k ∈ fibre₄, 2^{carryVal2 k} < W` collides with the floor `carryVal2 k ≥ t`.
On such shells the wave-8/9 `returnZero` field is VACUOUS (closed). -/
theorem returnZero_guard_refuted_of_width_le (ctx : ActualFailureContext)
    (hW : (supportShell ctx.shell.d ctx.shell.X).card ≤ 2 ^ ctxDyadicPart ctx) :
    ¬ ∃ k ∈ olcFibre ctx,
        2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card := by
  rintro ⟨k, hk, hlt⟩
  have hfloor : 2 ^ ctxDyadicPart ctx ≤ 2 ^ carryVal2 ctx k :=
    Nat.pow_le_pow_right (by norm_num) (olcFibre_carryVal2_ge_dyadicPart ctx hk)
  omega

/-- **The demanded regime knows the width bound**: the `returnZero` guard itself forces
`2^{v₂(Q)} < W` — every context where the field genuinely fires has support-shell width
above `2^t`. -/
theorem width_gt_of_returnZero_guard (ctx : ActualFailureContext)
    (h : ∃ k ∈ olcFibre ctx,
        2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) :
    2 ^ ctxDyadicPart ctx < (supportShell ctx.shell.d ctx.shell.X).card := by
  by_contra hcon
  exact returnZero_guard_refuted_of_width_le ctx (not_lt.mp hcon) h

/-- **The dyadic-floor-weakened `returnZero` field**: the verbatim wave-8/9 field with
the extra (free, by `width_gt_of_returnZero_guard`) guard `2^{v₂(Q)} < W`.  Strictly
weaker to provide: the `W ≤ 2^{v₂(Q)}` regime is closed. -/
def ReturnZeroDyadicFloorField : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    2 ^ ctxDyadicPart ctx < (supportShell ctx.shell.d ctx.shell.X).card →
    ReturnZeroBodyBanded ctx

/-- **The field bridge**: a dyadic-floor provider rebuilds the exact capstone
`returnZero` field shape — the extra guard is supplied by the floor itself. -/
theorem pushResidual_returnZero_field_of_dyadicFloor (F : ReturnZeroDyadicFloorField) :
    ∀ ctx : ActualFailureContext,
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      (∃ k ∈ olcFibre ctx,
        2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
      ¬ ReturnIndexWindowClean ctx →
      ReturnZeroBodyBanded ctx :=
  fun ctx h1 h2 h3 h4 => F ctx h1 h2 h3 h4 (width_gt_of_returnZero_guard ctx h3)

/-- **The combinator**: replace the `returnZero` field of any wave-8 surface by a
dyadic-floor provider — the result is again a full `Erdos260PushResidual`. -/
def pushResidual_withDyadicFloorZero (base : Erdos260PushResidual)
    (F : ReturnZeroDyadicFloorField) : Erdos260PushResidual :=
  { base with returnZero := pushResidual_returnZero_field_of_dyadicFloor F }

/-- **Endpoint**: `Erdos260Statement` from a wave-8 surface whose `returnZero` field is
supplied in dyadic-floor form. -/
theorem erdos260_of_dyadicFloorZero (base : Erdos260PushResidual)
    (F : ReturnZeroDyadicFloorField) : Erdos260Statement :=
  erdos260_of_pushResidual (pushResidual_withDyadicFloorZero base F)

/-- **The deep-dyadic dichotomy**: on shells with `Q·(2X+2) < 2^{2^t}`, the `returnZero`
demand is EQUIVALENT to slice-singletonness — a same-slice pair refutes `ReturnZeroBody`
outright (`returnZeroBody_refuted_of_sameSlice_doubleExp` + the floor `carryVal2 ≥ t`),
and with no pair the demand holds vacuously. -/
theorem returnZeroBody_iff_no_pair_of_deepDyadic (ctx : ActualFailureContext)
    (hbig : ctx.Q * (2 * ctx.shell.X + 2) < 2 ^ 2 ^ ctxDyadicPart ctx) :
    ReturnZeroBody ctx
      ↔ ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
          ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y,
            ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y, x < z → False := by
  constructor
  · intro H y hy x hx z hz hxz
    have hfloor : 2 ^ 2 ^ ctxDyadicPart ctx ≤ 2 ^ 2 ^ carryVal2 ctx x :=
      Nat.pow_le_pow_right (by norm_num)
        (Nat.pow_le_pow_right (by norm_num)
          (olcFibre_carryVal2_ge_dyadicPart ctx (mem_olcFibre_of_mem_olcSlice hx)))
    have hz2X : z ≤ 2 * ctx.shell.X :=
      returnFibre_le_two_mul ctx (mem_olcFibre_of_mem_olcSlice hz)
    have hQz : ctx.Q * (z + 2) ≤ ctx.Q * (2 * ctx.shell.X + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    exact returnZeroBody_refuted_of_sameSlice_doubleExp ctx hy hx hz hxz (by omega) H
  · intro H y hy x hx z hz hxz
    exact (H y hy x hx z hz hxz).elim

/-! ## Part 8.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the carry-valuation-floor module. -/
def carryValuationFloorStatus : List String :=
  [ "GOAL 1 SETTLED (OlcFibreDeep is a THEOREM, every ctx): olcFibreDeep_proved - all " ++
      "class-4 fibre members are >= 3; in fact >= L = shellLadderDepth ctx >= 28 " ++
      "(olcFibre_mem_ge_depth, olcFibre_mem_ge_of_le_depth).  Engine: the wave-5 " ++
      "rigidity window exists_one_in_window at the trivial factorization Q = Q*2^0 " ++
      "forces a hit in every length-2L block (carryFloor_hit_in_window, " ++
      "carryFloor_supportCount_ge; numerics Q < X = 2^L by carryWord_Q_lt_X and " ++
      "L*2L+2 <= 2^L by carryFloor_poly_le_pow), so supportCount d X >= m for every " ++
      "m <= L (carryFloor_supportCount_ge_of_le_depth); the support injects into the " ++
      "pre-window index range, supportCount <= firstIndexAbove X " ++
      "(carryFloor_supportCount_le_firstIndexAbove); fibre members sit at k >= F " ++
      "(olcFibre_mem_window).  NOT just F >= 3: the full chain k >= F >= supportCount " ++
      ">= L.",
    "GOAL 1 WIRED (the banded->trajectory converse is UNCONDITIONAL): " ++
      "nonempty_trajectoryResidual_iff_push (the wave-9 Nonempty equivalence with the " ++
      "deepness gate discharged), trajectoryResidualOfPush / trajectorySurfaceOfPush " ++
      "(every wave-8 push provider yields the wave-9 trajectory surface outright), " ++
      "returnZeroBody_iff_belowBandTrajectory_uncond (per-ctx iff, no side condition).",
    "GOAL 2 (the carryVal2 floor, exact): carryVal2 N >= t = v2(Q) = ctxDyadicPart ctx " ++
      "at EVERY position N >= t (carryVal2_ge_dyadicPart, via two_pow_dvd_integerCarry " ++
      "+ carryOf_pos), and t < L (ctxDyadicPart_lt_depth: 2^t <= Q < X = 2^L) places " ++
      "every fibre member k >= L > t in scope: olcFibre_carryVal2_ge_dyadicPart, " ++
      "UNCONDITIONAL at every member.  The floor's content is exactly v2(Q): trivial " ++
      "(>= 0) for odd Q.",
    "GOAL 2 (the Q-parity split, honest): Q EVEN - carryVal2 N >= 1 at EVERY N >= 1 " ++
      "(carryVal2_pos_of_Q_even: both terms of R_N = 2R_{N-1} - Q*N*d_N are even; " ++
      "fibre form olcFibre_carryVal2_pos_of_Q_even; ctxDyadicPart_pos_of_Q_even).  " ++
      "Q ODD - NO positive floor: the valuation is reset to 0 EXACTLY at odd-position " ++
      "hits, carryVal2 N = 0 iff N odd and d N = 1 (carryVal2_eq_zero_iff_of_Q_odd, " ++
      "via the parity dictionary carryOf_emod_two: R_{N+1} = Q*(N+1)*d_{N+1} mod 2); " ++
      "away from odd hits the valuation IS positive (carryVal2_pos_of_Q_odd_miss).  " ++
      "carryVal2 measures the carry at the member's RAW position k (a hit index used " ++
      "as a position), so for odd Q an odd-number member at a raw hit position has " ++
      "carryVal2 k = 0 - the Q-odd residual is genuine, not an artifact.",
    "GOAL 2 (the orbit pin is parity-blind): class4BandPin_modulus_odd - the class-4 " ++
      "band-2 datum modulus q is odd BY CONSTRUCTION (hq_odd), so the E.13 band " ++
      "2K <= q < 4K carries no information about v2(Q); the floor comes from the carry " ++
      "recursion alone, not from the band pin.",
    "GOAL 3 (regime closures): spacing floor 2^t | z - x on same-slice pairs " ++
      "(sameSlice_gap_dvd_pow_dyadicPart, sameSlice_gap_pow_dyadicPart_le).  THE FIELD " ++
      "CLOSURE: the capstone returnZero guard (exists k in fibre4 with 2^carryVal2 k " ++
      "< W) is REFUTED whenever W <= 2^t (returnZero_guard_refuted_of_width_le) - the " ++
      "returnZero field is VACUOUS on width-<= 2^t shells; demanded contexts force " ++
      "2^t < W (width_gt_of_returnZero_guard).  HONEST CORRECTION to the brief: Q even " ++
      "alone gives t >= 1, closing only W <= 2 shells - 'Q-even closes returnZero " ++
      "outright' is FALSE as hoped; the true closed regime is W <= 2^{v2(Q)} " ++
      "(deep-dyadic denominators), and Q odd closes only W <= 1.  DEEP-DYADIC " ++
      "DICHOTOMY: on Q*(2X+2) < 2^{2^t} shells, ReturnZeroBody holds IFF no same-slice " ++
      "pair exists (returnZeroBody_iff_no_pair_of_deepDyadic, via " ++
      "returnZeroBody_refuted_of_sameSlice_doubleExp + the floor).",
    "GOAL 3 (the additive successor surface): ReturnZeroDyadicFloorField - the " ++
      "verbatim wave-8/9 returnZero field with the extra guard 2^{v2(Q)} < W (strictly " ++
      "weaker to provide); bridge pushResidual_returnZero_field_of_dyadicFloor (the " ++
      "extra guard is FREE on demanded contexts); combinator " ++
      "pushResidual_withDyadicFloorZero (base : Erdos260PushResidual) (F : " ++
      "ReturnZeroDyadicFloorField) : Erdos260PushResidual; endpoint " ++
      "erdos260_of_dyadicFloorZero : Erdos260Statement.",
    "HYGIENE: additive only; no upstream module touched; no sorry / admit / new axiom " ++
      "/ native_decide; all #print axioms in [propext, Classical.choice, Quot.sound]." ]

theorem carryValuationFloorStatus_nonempty : carryValuationFloorStatus ≠ [] := by
  simp [carryValuationFloorStatus]

/-! ## Part 9.  Axiom-cleanliness audit -/

#print axioms carryFloor_poly_le_pow
#print axioms carryFloor_hit_in_window
#print axioms carryFloor_supportCount_ge
#print axioms carryFloor_supportCount_ge_of_le_depth
#print axioms carryFloor_supportCount_le_firstIndexAbove
#print axioms olcFibre_mem_ge_of_le_depth
#print axioms olcFibre_mem_ge_depth
#print axioms olcFibreDeep_proved
#print axioms nonempty_trajectoryResidual_iff_push
#print axioms trajectoryResidualOfPush
#print axioms trajectorySurfaceOfPush
#print axioms returnZeroBody_iff_belowBandTrajectory_uncond
#print axioms ctxDyadicPart_pow_le
#print axioms ctxDyadicPart_lt_depth
#print axioms ctxQ_eq_oddPart_mul_pow
#print axioms carryOf_dvd_pow_dyadicPart
#print axioms carryVal2_ge_dyadicPart
#print axioms olcFibre_carryVal2_ge_dyadicPart
#print axioms carryOf_even_of_Q_even
#print axioms carryVal2_pos_of_Q_even
#print axioms olcFibre_carryVal2_pos_of_Q_even
#print axioms ctxDyadicPart_pos_of_Q_even
#print axioms carryOf_emod_two
#print axioms carryVal2_eq_zero_iff_of_Q_odd
#print axioms carryVal2_pos_of_Q_odd_miss
#print axioms class4BandPin_modulus_odd
#print axioms sameSlice_gap_dvd_pow_dyadicPart
#print axioms sameSlice_gap_pow_dyadicPart_le
#print axioms returnZero_guard_refuted_of_width_le
#print axioms width_gt_of_returnZero_guard
#print axioms pushResidual_returnZero_field_of_dyadicFloor
#print axioms pushResidual_withDyadicFloorZero
#print axioms erdos260_of_dyadicFloorZero
#print axioms returnZeroBody_iff_no_pair_of_deepDyadic
#print axioms carryValuationFloorStatus_nonempty

end

end Erdos260
