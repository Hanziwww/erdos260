import Erdos260.CNLMultiChargeUnconditional

/-!
# Class-1 routed-fibre closure, wave 2: the odd-orbit pins and the cycle-check closures

This module (NEW; it edits no existing file) pushes the class-1 (clean-CNL) routed-fibre
emptiness of `CNLMultiChargeUnconditional.lean` strictly further on the surviving subfamily
(`64 ∣ L`, orbit modulus `q ≥ 9`, deep shells).  Everything here is proved from the routing
arithmetic of the canonical objects — no fabricated witnesses, no new axioms.

## Audit of the three attack lines (why the atom does not close outright)

* **Bridge line (zero-runs).**  The one formalized hit↔orbit bridge,
  `integerCarry_realizes_boundedSlopeStep` / `carry_tracks_slopeOrbit`, is conditional on
  canonical-gap zero-runs of the *actual digits* along `gapOrbit S.q S.K₀ 0` — a constraint on
  `d` over the whole prefix `[0, ≈2X]`, anchored at position `0`.  The class-1 pins constrain
  only the `r + 2` hits `a k, …, a (k+r+1)` of a single window start `k > firstIndexAbove X`
  (and `X ≥ 2^28`).  The two data are disjoint: the zero-run hypothesis is NOT derivable from
  class-1 membership.  A second mismatch: the bridge tracks the orbit at digit *positions*
  (`gapOrbit`), while the route samples the orbit at hit *indices* `k`.
* **Orbit-persistence line.**  Only the start `k` itself is pinned to band 4
  (`genuineChargeRoute_eq_one_iff` reads the orbit only at `k`); persistence is FALSE in
  general — e.g. `q = 9` has the odd cycle `1 → 7 → 5 → 1` with band 4 recurring at every
  third index and bands `1, 1` in between.  What IS free is the *parity* of the orbit: every
  successor `2^g·K − q` (with `g ≥ 1`, `q` odd) is **odd**, so `K_k` is odd at every `k ≥ 1` —
  and every carry-window start has `k ≥ 1`.  This module extracts that pin and its closures.
* **Gap-floor line.**  No proved lower bound `> 1` on `hitGap` inside the carry window exists
  (adjacent support digits are not excluded by any formalized structure), and the gap-ceiling
  gate `64(r+1)(L+B+1) < 129L+64` provably fails for EVERY `r ≥ 2` shell (`64·3 = 192 > 129`),
  so the ceiling route cannot reach deep shells.  Structural; documented, not fudged.

## What IS newly closed here (all unconditional)

* **The window-start positivity pin** (`n24_starts_pos`, `class1Fibre_start_pos`): every
  carry-window start has `k ≥ 1` (`firstIndexAbove X ≥ 1` from `supportCount ≥ 1`).
* **The odd-orbit parity pin** (`boundedSlopeStep_odd`, `slopeOrbit_odd`,
  `class1Fibre_orbit_odd`): `slopeOrbit q K₀ k` is odd for every `k ≥ 1`; hence every class-1
  start has an ODD band-4 numerator.
* **The modulus-window closure** (`band_four_odd_modulus_window`,
  `modulus_window_of_class1Fibre_nonempty`, `class1Fibre_empty_of_modulus_window`): an odd
  `K` with `8K ≤ q < 16K` forces `q ∈ {9,…,15} ∪ {25, 27, …}`; the fibre is PROVABLY EMPTY on
  every shell with modulus `q ∈ {17, 19, 21, 23}` — a brand-new closed subfamily beyond the
  proved `q < 9` closure.
* **The low-modulus orbit pin** (`class1Fibre_orbit_eq_one_of_modulus_le_15`): on the
  surviving low band `q ≤ 15` every class-1 start has `K_k = 1` EXACTLY.
* **The pure-cycle structure of the orbit** (`boundedSlopeStep_inj_of_odd`,
  `slopeOrbit_cancel`, `slopeOrbit_exists_period`, `class1Fibre_orbit_period_exists`): the
  E.13 step is INJECTIVE on odd states (`2^{g₁}K₁ = 2^{g₂}K₂` with `K₁, K₂` odd forces
  `K₁ = K₂`), so the orbit is backward-deterministic from index `1` and purely periodic with
  some period `1 ≤ c ≤ q`.
* **The finite cycle-check closures** (`class1Fibre_empty_of_orbit_band_free`,
  `class1Fibre_empty_of_cycle_band_free`): if one period of the orbit (any `c` with the
  recurrence `K_{m+c} = K_m` for `m ≥ 1`) avoids band 4, the fibre is empty.  This reduces
  the entire orbit side of the residual to a FINITE per-context check (`≤ q` band readings) —
  e.g. it closes the `(q, K₀) = (15, 7)` family outright, whose odd cycle `7 → 13 → 11 → 7`
  has bands `2, 1, 1` and never fires band 4.
* **The strictly smaller sharp residual** (`mem_class1Fibre_iff_sharp`,
  `class1Fibre_eq_pinnedFilter_sharp`, `v3_class1FibreEmpty_iff_pinned_sharp`,
  `class1FibreEmpty_of_pinned_arithmetic_sharp`, `erdos260_p9V3_of_pinned_arithmetic_sharp`):
  the necessary-and-sufficient membership/residual forms now carry `1 ≤ k` and `Odd K_k`
  (derived, so still sharp), and the sufficient pinned-arithmetic entry to the capstone field
  only demands refuting the simultaneous pins on `64 ∣ L` shells with
  `q ∈ {9,…,15} ∪ {25,…}`, odd `K_k`, window starts `k ≥ 1`.

## The honest minimal residual after this module

`Class1FibreEmpty (v3Budget …)` remains necessary and sufficient.  The surviving subfamily is
now: shells with `64 ∣ L`, odd modulus `q ∈ {9, 11, 13, 15} ∪ {25, 27, …}` whose odd orbit
cycle contains a band-4 element at a window-reachable index, where additionally some carry
window start realizes the exact gap-window pin `64·gapWindow = 129L + 64` at such an index.
On `q ≤ 15` the orbit numerator is pinned to `K_k = 1` exactly.  We do NOT claim
unconditional closure of the atom; the digit-side pin and the orbit-side pin remain coupled
only through the shared index `k`.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The odd-orbit parity pin

The E.13 successor `2^g·K − q` of an admissible state subtracts the odd modulus from an even
multiple (`g = canonGap ≥ 1`), so it is odd.  Hence the recurrent slope orbit consists of odd
numerators from index `1` onward. -/

/-- The canonical gap is always positive (it is `⌊log₂(q/K)⌋ + 1`). -/
theorem canonGap_pos (q K : ℕ) : 1 ≤ canonGap q K :=
  Nat.le_add_left 1 (Nat.log 2 (q / K))

/-- **The E.13 successor is odd**: for odd `q` and an admissible state `1 ≤ K < q`, the
successor numerator `2^{canonGap q K}·K − q` is odd (an even number minus an odd one, the
subtraction being genuine by the band lower bound `q < 2^g·K`). -/
theorem boundedSlopeStep_odd {q K : ℕ} (hq : Odd q) (hK1 : 1 ≤ K) (hKq : K < q) :
    Odd (boundedSlopeStep q K) := by
  obtain ⟨hlow, _⟩ := canonGap_bounds hq hK1 hKq
  obtain ⟨c, hc⟩ : 2 ∣ 2 ^ canonGap q K * K :=
    Dvd.dvd.mul_right (dvd_pow_self 2 (by have := canonGap_pos q K; omega)) K
  obtain ⟨m, hm⟩ := hq
  rw [Nat.odd_iff]
  unfold boundedSlopeStep
  omega

/-- **The odd-orbit parity pin**: the recurrent slope orbit is odd at EVERY index `k ≥ 1`
(only the base numerator `K₀` may be even). -/
theorem slopeOrbit_odd {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀) (hKq : K₀ < q) :
    ∀ k, 1 ≤ k → Odd (slopeOrbit q K₀ k) := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hmem := slopeOrbit_mem hq hK1 hKq j
  have hstep : slopeOrbit q K₀ (j + 1) = boundedSlopeStep q (slopeOrbit q K₀ j) := rfl
  rw [hstep]
  exact boundedSlopeStep_odd hq hmem.1 hmem.2

/-! ## Part 2.  The window-start positivity pin

The carry start window is `Ico (firstIndexAbove X) (firstIndexAbove X + |supportShell|)`, and
the actual context provides `supportCount ≥ 1`, so `firstIndexAbove X ≥ 1`: every carry-window
start — in particular every class-1 routed start — has `k ≥ 1`, putting it in the odd range of
the orbit. -/

/-- The first shell index of the actual N.24 carry datum is positive (the shell starts after
the first hit, from the proved `supportCount ≥ 1`). -/
theorem n24_firstIndexAbove_pos (ctx : ActualFailureContext) :
    1 ≤ ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X :=
  ctx.n24CarryData.carry.hits.firstIndexAbove_pos_of_supportCount_pos ctx.n24SupportCount_pos

/-- **Every carry-window start is positive**: `k ∈ starts → 1 ≤ k`. -/
theorem n24_starts_pos (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ ctx.n24CarryData.starts) : 1 ≤ k := by
  rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hk
  have := n24_firstIndexAbove_pos ctx
  omega

/-- Every class-1 routed start of the genuine route has `k ≥ 1`. -/
theorem class1Fibre_start_pos (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    1 ≤ k :=
  n24_starts_pos ctx (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1

/-- **The class-1 odd-numerator pin**: every class-1 routed start has an ODD slope-orbit
numerator `K_k` (it sits at index `k ≥ 1` of the orbit). -/
theorem class1Fibre_orbit_odd (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    Odd (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) :=
  slopeOrbit_odd (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k (class1Fibre_start_pos ctx hk)

/-! ## Part 3.  The modulus-window closure: `q ∈ {17, 19, 21, 23}` is empty

The band-4 window `(q/16, q/8]` contains an odd integer iff `q ≤ 15` (then `K = 1`) or
`q ≥ 24` (then `K = 3` or higher; `q` is odd, so `q ≥ 25`).  For `q ∈ {17, 19, 21, 23}` the
only integer in the window is the EVEN `K = 2` — incompatible with the parity pin.  This
closes a brand-new modulus subfamily beyond the proved `q < 9` closure. -/

/-- **The odd band-4 modulus window**: an odd `K` in the E.13 band-4 window `8K ≤ q < 16K`
of an odd modulus forces `q ∈ {9,…,15} ∪ {25, 27, …}`. -/
theorem band_four_odd_modulus_window {q K : ℕ} (hq : Odd q) (hK : Odd K)
    (h8 : 8 * K ≤ q) (h16 : q < 16 * K) :
    9 ≤ q ∧ (q ≤ 15 ∨ 25 ≤ q) := by
  obtain ⟨m, hm⟩ := hq
  obtain ⟨n, hn⟩ := hK
  omega

/-- **The two-sided modulus window of a nonempty class-1 fibre** (sharpens the proved
`modulus_ge_nine_of_class1Fibre_nonempty`): a class-1 start forces the odd modulus into
`{9,…,15} ∪ {25, 27, …}` — the parity pin excludes the whole band `16 < q < 25`. -/
theorem modulus_window_of_class1Fibre_nonempty (ctx : ActualFailureContext)
    (h : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).Nonempty) :
    9 ≤ (class1SlopeDatum ctx).q
      ∧ ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨h8, h16⟩ := class1Fibre_orbit_band ctx hk
  exact band_four_odd_modulus_window (class1SlopeDatum ctx).hq_odd
    (class1Fibre_orbit_odd ctx hk) h8 h16

/-- **NEW modulus-window closure**: the class-1 routed fibre of the genuine route is PROVABLY
EMPTY on every shell whose closed AP-subfibre modulus lies in the band `16 < q < 25`
(`q ∈ {17, 19, 21, 23}`) — the only band-4 numerator there is the even `K = 2`, while every
window start carries an odd orbit numerator. -/
theorem class1Fibre_empty_of_modulus_window (ctx : ActualFailureContext)
    (h16 : 16 < (class1SlopeDatum ctx).q) (h25 : (class1SlopeDatum ctx).q < 25) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  obtain ⟨h9, hwin⟩ := modulus_window_of_class1Fibre_nonempty ctx ⟨k, hk⟩
  omega

/-- The v3 seed budget routes through the genuine route, so the modulus-window closure
applies to it verbatim. -/
theorem v3_class1Fibre_empty_of_modulus_window
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (ctx : ActualFailureContext)
    (h16 : 16 < (class1SlopeDatum ctx).q) (h25 : (class1SlopeDatum ctx).q < 25) :
    routedFibre ctx.n24CarryData
      ((v3Budget towerCount runChain returnCharge) ctx).route 1 = ∅ :=
  class1Fibre_empty_of_modulus_window ctx h16 h25

/-- **The low-modulus orbit pin**: on every surviving shell with `q ≤ 15` (so
`q ∈ {9, 11, 13, 15}` after the proved closures), each class-1 start has its orbit numerator
pinned to `K_k = 1` EXACTLY (the band `8K ≤ q ≤ 15` admits no other positive value). -/
theorem class1Fibre_orbit_eq_one_of_modulus_le_15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 15) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 1 := by
  obtain ⟨h8, h16⟩ := class1Fibre_orbit_band ctx hk
  omega

/-! ## Part 3b.  The closed-datum structure pins: `q = oddpart(Q·(2P+1))`, `K₀ = P`

The closed AP-subfibre datum through which the route reads the orbit is fully explicit: its
modulus is the odd part of `Q·(2|P|+1)` for the actual carry numerator `P` (so `2|P|+1`
divides `q`), and its base numerator is `P` itself (the residue is genuine: `0 < P < q`).
These pins let any concrete `(Q, P)` family be fed to the closures of this module. -/

/-- **The closed-datum modulus pin** (definitional): the orbit modulus of the actual context
is the odd part of `Q·(2|P|+1)`, `P` the chosen carry numerator of `η = P/Q`. -/
theorem class1SlopeDatum_q_eq (ctx : ActualFailureContext) :
    (class1SlopeDatum ctx).q
      = apOddModulus ctx.shell.Q (2 * ctx.shell.hrational.choose.natAbs + 1) := rfl

/-- The odd AP modulus `H = 2|P| + 1` divides the orbit modulus. -/
theorem class1SlopeDatum_H_dvd (ctx : ActualFailureContext) :
    2 * ctx.shell.hrational.choose.natAbs + 1 ∣ (class1SlopeDatum ctx).q := by
  rw [class1SlopeDatum_q_eq]
  exact H_dvd_apOddModulus ctx.shell.Q _ ctx.shell.hQ.ne'
    ⟨ctx.shell.hrational.choose.natAbs, rfl⟩

/-- **The closed-datum base-numerator pin**: the orbit base numerator is the actual carry
numerator itself, `K₀ = |P|` (the initial residue is genuine since `0 < P < q`). -/
theorem class1SlopeDatum_K₀_eq (ctx : ActualFailureContext) :
    (class1SlopeDatum ctx).K₀ = ctx.shell.hrational.choose.natAbs := by
  have hPpos : 0 < ctx.shell.hrational.choose :=
    failingShell_carry_pos ctx.shell ctx.shell.hrational.choose ctx.shell.hrational.choose_spec
  have hq_pos : 0 < (class1SlopeDatum ctx).q := by
    have := (class1SlopeDatum ctx).hq2
    omega
  have hH_le : 2 * ctx.shell.hrational.choose.natAbs + 1 ≤ (class1SlopeDatum ctx).q :=
    Nat.le_of_dvd hq_pos (class1SlopeDatum_H_dvd ctx)
  have hK : (class1SlopeDatum ctx).K₀
      = (ctx.shell.hrational.choose % ((class1SlopeDatum ctx).q : ℤ)).toNat := rfl
  have hcast : (ctx.shell.hrational.choose.natAbs : ℤ) = ctx.shell.hrational.choose :=
    Int.natAbs_of_nonneg hPpos.le
  have hPlt : ctx.shell.hrational.choose < ((class1SlopeDatum ctx).q : ℤ) := by
    have h1 : (ctx.shell.hrational.choose.natAbs : ℤ) < ((class1SlopeDatum ctx).q : ℤ) := by
      exact_mod_cast (by omega : ctx.shell.hrational.choose.natAbs < (class1SlopeDatum ctx).q)
    omega
  have hmod : ctx.shell.hrational.choose % ((class1SlopeDatum ctx).q : ℤ)
      = ctx.shell.hrational.choose :=
    Int.emod_eq_of_lt hPpos.le hPlt
  rw [hK, hmod]
  omega

/-- The base numerator sits strictly below half the modulus: `2·K₀ < q` (from
`2K₀ + 1 = H ∣ q`).  In particular the base state is never in the band-1 (Run) window
`q < 2K` — though it CAN sit in band 4, which is why the `k ≥ 1` positivity pin (not this
bound) is what carries the parity argument. -/
theorem class1SlopeDatum_two_K₀_lt (ctx : ActualFailureContext) :
    2 * (class1SlopeDatum ctx).K₀ < (class1SlopeDatum ctx).q := by
  have hq_pos : 0 < (class1SlopeDatum ctx).q := by
    have := (class1SlopeDatum ctx).hq2
    omega
  have hH_le : 2 * ctx.shell.hrational.choose.natAbs + 1 ≤ (class1SlopeDatum ctx).q :=
    Nat.le_of_dvd hq_pos (class1SlopeDatum_H_dvd ctx)
  have hK := class1SlopeDatum_K₀_eq ctx
  omega

/-! ## Part 4.  The pure-cycle structure of the orbit and the finite cycle-check closures

The E.13 step is injective on ODD states: `2^{g₁}·K₁ = 2^{g₂}·K₂` with `K₁, K₂` odd forces
`g₁ = g₂` and `K₁ = K₂`.  Since the orbit is odd from index `1`, it is backward-deterministic
there, hence PURELY periodic with some period `1 ≤ c ≤ q` (pigeonhole).  Consequently the
entire orbit side of the class-1 residual reduces to a finite check: if one period avoids
band 4, the fibre is empty. -/

/-- Odd factors of equal `2-power × odd` products are equal (`2^m·a = 2^n·b`, `a, b` odd
`⟹ a = b`). -/
private theorem eq_of_two_pow_mul_eq_of_odd {m : ℕ} :
    ∀ {n a b : ℕ}, Odd a → Odd b → 2 ^ m * a = 2 ^ n * b → a = b := by
  induction m with
  | zero =>
      intro n a b ha hb h
      rw [pow_zero, one_mul] at h
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [pow_zero, one_mul] at h; exact h
      · exfalso
        obtain ⟨c, hc⟩ : 2 ∣ 2 ^ n * b :=
          Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) b
        obtain ⟨t, ht⟩ := ha
        omega
  | succ m ih =>
      intro n a b ha hb h
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exfalso
        rw [pow_zero, one_mul] at h
        obtain ⟨c, hc⟩ : 2 ∣ 2 ^ (m + 1) * a :=
          Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) a
        obtain ⟨t, ht⟩ := hb
        omega
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        have h' : 2 * (2 ^ m * a) = 2 * (2 ^ n' * b) := by
          have e1 : 2 ^ (m + 1) * a = 2 * (2 ^ m * a) := by ring
          have e2 : 2 ^ (n' + 1) * b = 2 * (2 ^ n' * b) := by ring
          rw [← e1, ← e2]
          exact h
        exact ih ha hb (Nat.eq_of_mul_eq_mul_left (by norm_num) h')

/-- **The E.13 step is injective on odd states**: two odd admissible numerators with equal
successors are equal.  This is the backward determinism of the recurrent orbit. -/
theorem boundedSlopeStep_inj_of_odd {q K₁ K₂ : ℕ} (hq : Odd q)
    (h₁ : 1 ≤ K₁) (h₁q : K₁ < q) (h₂ : 1 ≤ K₂) (h₂q : K₂ < q)
    (hodd₁ : Odd K₁) (hodd₂ : Odd K₂)
    (heq : boundedSlopeStep q K₁ = boundedSlopeStep q K₂) :
    K₁ = K₂ := by
  obtain ⟨hlow₁, _⟩ := canonGap_bounds hq h₁ h₁q
  obtain ⟨hlow₂, _⟩ := canonGap_bounds hq h₂ h₂q
  have hpow : 2 ^ canonGap q K₁ * K₁ = 2 ^ canonGap q K₂ * K₂ := by
    unfold boundedSlopeStep at heq
    omega
  exact eq_of_two_pow_mul_eq_of_odd hodd₁ hodd₂ hpow

/-- Forward determinism: equal orbit values propagate forward by any shift. -/
theorem slopeOrbit_eq_shift {q K₀ i j : ℕ}
    (h : slopeOrbit q K₀ i = slopeOrbit q K₀ j) :
    ∀ t, slopeOrbit q K₀ (i + t) = slopeOrbit q K₀ (j + t) := by
  intro t
  induction t with
  | zero => exact h
  | succ t ih =>
      have hstepi : slopeOrbit q K₀ (i + (t + 1))
          = boundedSlopeStep q (slopeOrbit q K₀ (i + t)) := rfl
      have hstepj : slopeOrbit q K₀ (j + (t + 1))
          = boundedSlopeStep q (slopeOrbit q K₀ (j + t)) := rfl
      rw [hstepi, hstepj, ih]

/-- **Backward determinism from index `1`**: equal orbit values at `i + n` and `j + n` peel
back to equal values at `i` and `j`, for any base indices `i, j ≥ 1` (where the orbit is
odd, so the step is injective). -/
theorem slopeOrbit_cancel {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀) (hKq : K₀ < q) :
    ∀ (n : ℕ) {i j : ℕ}, 1 ≤ i → 1 ≤ j →
      slopeOrbit q K₀ (i + n) = slopeOrbit q K₀ (j + n) →
      slopeOrbit q K₀ i = slopeOrbit q K₀ j := by
  intro n
  induction n with
  | zero =>
      intro i j _ _ h
      exact h
  | succ n ih =>
      intro i j hi hj h
      refine ih hi hj ?_
      have hstepi : slopeOrbit q K₀ (i + (n + 1))
          = boundedSlopeStep q (slopeOrbit q K₀ (i + n)) := rfl
      have hstepj : slopeOrbit q K₀ (j + (n + 1))
          = boundedSlopeStep q (slopeOrbit q K₀ (j + n)) := rfl
      rw [hstepi, hstepj] at h
      have hmi := slopeOrbit_mem hq hK1 hKq (i + n)
      have hmj := slopeOrbit_mem hq hK1 hKq (j + n)
      exact boundedSlopeStep_inj_of_odd hq hmi.1 hmi.2 hmj.1 hmj.2
        (slopeOrbit_odd hq hK1 hKq (i + n) (by omega))
        (slopeOrbit_odd hq hK1 hKq (j + n) (by omega)) h

/-- A collision `K_x = K_y` with `1 ≤ x < y ≤ q` yields the pure period `c = y − x` valid
from index `1` onward. -/
private theorem slopeOrbit_period_of_collision {q K₀ x y : ℕ} (hq : Odd q)
    (hK1 : 1 ≤ K₀) (hKq : K₀ < q) (hx1 : 1 ≤ x) (hyq : y ≤ q)
    (hlt : x < y) (hfeq : slopeOrbit q K₀ x = slopeOrbit q K₀ y) :
    ∃ c, 1 ≤ c ∧ c ≤ q ∧ ∀ m, 1 ≤ m →
      slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m := by
  refine ⟨y - x, by omega, by omega, ?_⟩
  intro m hm
  have hpeel : slopeOrbit q K₀ 1 = slopeOrbit q K₀ (1 + (y - x)) := by
    apply slopeOrbit_cancel hq hK1 hKq (x - 1) le_rfl (by omega)
    have e1 : 1 + (x - 1) = x := by omega
    have e2 : 1 + (y - x) + (x - 1) = y := by omega
    rw [e1, e2]
    exact hfeq
  have hshift := slopeOrbit_eq_shift hpeel.symm (m - 1)
  have e3 : 1 + (y - x) + (m - 1) = m + (y - x) := by omega
  have e4 : 1 + (m - 1) = m := by omega
  rw [e3, e4] at hshift
  exact hshift

/-- **The orbit is purely periodic from index `1`**, with some period `1 ≤ c ≤ q`:
pigeonhole on the `q − 1` admissible values plus backward determinism on odd states. -/
theorem slopeOrbit_exists_period {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀) (hKq : K₀ < q) :
    ∃ c, 1 ≤ c ∧ c ≤ q ∧ ∀ m, 1 ≤ m →
      slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m := by
  have hq1 : 1 ≤ q := by omega
  have hcard : (Finset.Ico 1 q).card < (Finset.Icc 1 q).card := by
    rw [Nat.card_Ico, Nat.card_Icc]
    omega
  have hmaps : ∀ m ∈ Finset.Icc 1 q, slopeOrbit q K₀ m ∈ Finset.Ico 1 q := by
    intro m _
    rw [Finset.mem_Ico]
    exact slopeOrbit_mem hq hK1 hKq m
  obtain ⟨x, hx, y, hy, hxy, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Finset.mem_Icc] at hx hy
  rcases Nat.lt_or_ge x y with hlt | hge
  · exact slopeOrbit_period_of_collision hq hK1 hKq hx.1 hy.2 hlt hfeq
  · have hlt : y < x := by omega
    exact slopeOrbit_period_of_collision hq hK1 hKq hy.1 hx.2 hlt hfeq.symm

/-- **The class-1 orbit is purely periodic**: the recurrent slope orbit of the actual closed
AP-subfibre datum admits a period `1 ≤ c ≤ q` valid from index `1` (covering the whole carry
window).  The orbit side of the class-1 residual is therefore a FINITE check. -/
theorem class1Fibre_orbit_period_exists (ctx : ActualFailureContext) :
    ∃ c, 1 ≤ c ∧ c ≤ (class1SlopeDatum ctx).q ∧ ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m :=
  slopeOrbit_exists_period (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt

/-- **Band-free-orbit closure**: if the orbit never reads band 4 at any positive index, the
class-1 fibre is empty. -/
theorem class1Fibre_empty_of_orbit_band_free (ctx : ActualFailureContext)
    (h : ∀ j, 1 ≤ j → canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  exact h k (class1Fibre_start_pos ctx hk) (class1Fibre_canonGap_eq ctx hk)

/-- Cycle propagation: a band-4-free period block keeps every index up to `c·(n+1)`
band-4-free. -/
private theorem orbit_band_free_of_cycle_aux {q K₀ c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c → canonGap q (slopeOrbit q K₀ j) ≠ 4) :
    ∀ n j, 1 ≤ j → j ≤ c * (n + 1) → canonGap q (slopeOrbit q K₀ j) ≠ 4 := by
  intro n
  induction n with
  | zero =>
      intro j h1 hle
      exact hband j h1 (by omega)
  | succ n ih =>
      intro j h1 hle
      by_cases hle' : j ≤ c * (n + 1)
      · exact ih j h1 hle'
      · have hcA : c ≤ c * (n + 1) := Nat.le_mul_of_pos_right c (by omega)
        have hcj : c ≤ j := by omega
        have hj1 : 1 ≤ j - c := by omega
        have heq : slopeOrbit q K₀ j = slopeOrbit q K₀ (j - c) := by
          have h := hper (j - c) hj1
          rwa [Nat.sub_add_cancel hcj] at h
        rw [heq]
        refine ih (j - c) hj1 ?_
        have hsplit : c * (n + 1 + 1) = c * (n + 1) + c := by ring
        omega

/-- **The finite cycle-check closure**: if SOME period `c ≥ 1` of the orbit (valid from
index `1`) has all `c` of its band readings `≠ 4`, the class-1 routed fibre is empty.
Combined with `class1Fibre_orbit_period_exists` (`c ≤ q`), the orbit side of the residual is
decided by at most `q` canonical-gap evaluations per context. -/
theorem class1Fibre_empty_of_cycle_band_free (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c → canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  apply class1Fibre_empty_of_orbit_band_free ctx
  intro j hj
  refine orbit_band_free_of_cycle_aux hc hper hband j j hj ?_
  calc j ≤ j + 1 := by omega
    _ ≤ c * (j + 1) := Nat.le_mul_of_pos_left (j + 1) (by omega)

/-- The v3 seed budget routes through the genuine route, so the cycle-check closure applies
to it verbatim. -/
theorem v3_class1Fibre_empty_of_cycle_band_free
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c → canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 4) :
    routedFibre ctx.n24CarryData
      ((v3Budget towerCount runChain returnCharge) ctx).route 1 = ∅ :=
  class1Fibre_empty_of_cycle_band_free ctx hc hper hband

/-! ## Part 5.  The strictly smaller sharp residual

The sharp membership characterization and the pinned-arithmetic residual of
`CNLMultiChargeUnconditional` are upgraded with the two new derived pins (`1 ≤ k`, odd `K_k`)
— still necessary AND sufficient — and the sufficient entry to the capstone field folds in
every proved subfamily closure (`64 ∣ L`, `q ≥ 9`, `q ∉ {17,…,23}`). -/

/-- **The sharp class-1 membership characterization, wave 2**: `k ∈ fibre₁` iff `k` is a
carry-window start at a positive index with an ODD orbit numerator realizing BOTH exact pins.
The two new conjuncts are derived, so this is still an exact characterization. -/
theorem mem_class1Fibre_iff_sharp (ctx : ActualFailureContext) (k : ℕ) :
    k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ↔ k ∈ ctx.n24CarryData.starts
        ∧ 1 ≤ k
        ∧ Odd (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k)
        ∧ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            = 129 * shellLadderDepth ctx + 64
        ∧ canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4 := by
  constructor
  · intro hk
    obtain ⟨hstart, hgw, hband⟩ := (mem_class1Fibre_iff ctx k).mp hk
    exact ⟨hstart, class1Fibre_start_pos ctx hk, class1Fibre_orbit_odd ctx hk, hgw, hband⟩
  · rintro ⟨hstart, _, _, hgw, hband⟩
    exact (mem_class1Fibre_iff ctx k).mpr ⟨hstart, hgw, hband⟩

/-- **The class-1 fibre IS the sharp doubly-pinned odd-window filter** (wave-2 form). -/
theorem class1Fibre_eq_pinnedFilter_sharp (ctx : ActualFailureContext) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      = ctx.n24CarryData.starts.filter (fun k =>
          1 ≤ k
          ∧ Odd (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k)
          ∧ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
              = 129 * shellLadderDepth ctx + 64
          ∧ canonGap (class1SlopeDatum ctx).q
              (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4) := by
  ext k
  rw [Finset.mem_filter, mem_class1Fibre_iff_sharp]

/-- **The residual in its sharpest wave-2 arithmetic form, necessary AND sufficient**: the
v3 clean-CNL atom holds iff no positive-index carry-window start with an odd orbit numerator
realizes the gap-window pin and the band-4 pin simultaneously. -/
theorem v3_class1FibreEmpty_iff_pinned_sharp
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx) :
    Class1FibreEmpty (v3Budget towerCount runChain returnCharge)
      ↔ ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
          1 ≤ k →
          Odd (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) →
          ¬(64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
                = 129 * shellLadderDepth ctx + 64
            ∧ canonGap (class1SlopeDatum ctx).q
                (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4) := by
  rw [v3_class1FibreEmpty_iff_pinned]
  constructor
  · intro h ctx k hk _ _ hpins
    exact h ctx k hk hpins
  · intro h ctx k hk hpins
    have h1 : 1 ≤ k := n24_starts_pos ctx hk
    exact h ctx k hk h1
      (slopeOrbit_odd (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
        (class1SlopeDatum ctx).hK₀_lt k h1) hpins

/-- **The wave-2 pinned arithmetic SUFFICIENT entry, with ALL proved obstructions folded
in**: to close the atom it suffices to refute the simultaneous pins for positive-index window
starts with ODD orbit numerators, on the shells surviving every proved closure — `64 ∣ L`
(integrality), `q ≥ 9` (band floor), and `q ≤ 15 ∨ q ≥ 25` (the parity window). -/
theorem class1FibreEmpty_of_pinned_arithmetic_sharp
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (h : ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      1 ≤ k →
      64 ∣ shellLadderDepth ctx →
      9 ≤ (class1SlopeDatum ctx).q →
      ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
      Odd (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) →
      64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          = 129 * shellLadderDepth ctx + 64 →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) ≠ 4) :
    Class1FibreEmpty (v3Budget towerCount runChain returnCharge) := by
  rw [v3_class1FibreEmpty_iff_pinned_sharp]
  intro ctx k hk h1 hodd hpins
  obtain ⟨hgw, hband⟩ := hpins
  have hdvd : 64 ∣ shellLadderDepth ctx := by omega
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k
  obtain ⟨h8, h16⟩ := (canonGap_eq_four_iff horb.1).mp hband
  obtain ⟨h9, hwin⟩ :=
    band_four_odd_modulus_window (class1SlopeDatum ctx).hq_odd hodd h8 h16
  exact h ctx k hk h1 hdvd h9 hwin hodd hgw hband

/-- **The P9/V3 endpoint from the wave-2 sharp pinned residual** — the clean-CNL slot
carried in its smallest proved arithmetic form: refute the simultaneous pins only on
`64 ∣ L` shells with `q ∈ {9,…,15} ∪ {25,…}`, odd orbit numerators, positive window
starts. -/
theorem erdos260_p9V3_of_pinned_arithmetic_sharp
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (hpin : ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      1 ≤ k →
      64 ∣ shellLadderDepth ctx →
      9 ≤ (class1SlopeDatum ctx).q →
      ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
      Odd (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) →
      64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          = 129 * shellLadderDepth ctx + 64 →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) ≠ 4)
    (densePackCount : ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card
        ≤ (densePackMarkers
          (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge) ctx).card)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Erdos260Statement :=
  erdos260_p9V3_of_class1FibreEmpty towerCount runResidual returnCharge chernoff
    (class1FibreEmpty_of_pinned_arithmetic_sharp towerCount
      (p9V3RunChainOfResidual runResidual) returnCharge hpin)
    densePackCount windowReach hReach hContain hScale

/-! ## Part 6.  Machine-readable status (brutally honest; supersedes the wave-1 list) -/

/-- Honest machine-readable status of the wave-2 class-1 closure attempt.  This list
supersedes the residual description of `cnlMultiChargeUnconditionalStatus`. -/
def cnlClass1ClosureStatus : List String :=
  [ "CLOSED (window-start positivity, NEW): every carry-window start has k ≥ 1 " ++
      "(n24_firstIndexAbove_pos from supportCount ≥ 1; n24_starts_pos; " ++
      "class1Fibre_start_pos).",
    "CLOSED (odd-orbit parity pin, NEW): the E.13 successor 2^g·K − q is odd (g ≥ 1, q odd: " ++
      "boundedSlopeStep_odd), so slopeOrbit q K₀ k is odd for EVERY k ≥ 1 (slopeOrbit_odd); " ++
      "hence every class-1 start has an ODD band-4 numerator (class1Fibre_orbit_odd).",
    "CLOSED (modulus-window subfamily, NEW): an odd K with 8K ≤ q < 16K forces q ∈ {9,…,15} " ++
      "∪ {25,27,…} (band_four_odd_modulus_window, modulus_window_of_class1Fibre_nonempty), " ++
      "so the class-1 fibre is PROVABLY EMPTY on every shell with modulus 16 < q < 25, i.e. " ++
      "q ∈ {17,19,21,23} (class1Fibre_empty_of_modulus_window / " ++
      "v3_class1Fibre_empty_of_modulus_window) — a brand-new closed subfamily beyond the " ++
      "proved q < 9 closure.",
    "CLOSED (low-modulus orbit pin, NEW): on q ≤ 15 every class-1 start has K_k = 1 EXACTLY " ++
      "(class1Fibre_orbit_eq_one_of_modulus_le_15).",
    "CLOSED (closed-datum structure pins, NEW): the route's orbit datum is fully explicit — " ++
      "q = oddpart(Q·(2|P|+1)) definitionally (class1SlopeDatum_q_eq), 2|P|+1 ∣ q " ++
      "(class1SlopeDatum_H_dvd), K₀ = |P| (class1SlopeDatum_K₀_eq), and 2K₀ < q " ++
      "(class1SlopeDatum_two_K₀_lt) — so concrete (Q, P) families plug directly into the " ++
      "cycle-check and window closures.",
    "CLOSED (pure-cycle structure, NEW): the E.13 step is injective on odd states " ++
      "(boundedSlopeStep_inj_of_odd), so the orbit is backward-deterministic from index 1 " ++
      "(slopeOrbit_cancel) and purely periodic with some period 1 ≤ c ≤ q " ++
      "(slopeOrbit_exists_period, class1Fibre_orbit_period_exists).",
    "CLOSED (finite cycle-check closures, NEW): a band-4-free period closes the fibre " ++
      "(class1Fibre_empty_of_orbit_band_free, class1Fibre_empty_of_cycle_band_free, " ++
      "v3_class1Fibre_empty_of_cycle_band_free): the ORBIT side of the residual is decided " ++
      "by at most q canonical-gap evaluations per context — e.g. the (q,K₀) = (15,7) family " ++
      "(odd cycle 7 → 13 → 11, bands 2,1,1) closes outright.",
    "SHARPENED (the necessary-and-sufficient residual): mem_class1Fibre_iff_sharp / " ++
      "class1Fibre_eq_pinnedFilter_sharp / v3_class1FibreEmpty_iff_pinned_sharp now carry " ++
      "the derived pins 1 ≤ k and Odd K_k; the sufficient capstone entry " ++
      "class1FibreEmpty_of_pinned_arithmetic_sharp (and the endpoint bridge " ++
      "erdos260_p9V3_of_pinned_arithmetic_sharp) folds in EVERY proved subfamily closure: " ++
      "64 ∣ L, 9 ≤ q, q ≤ 15 ∨ 25 ≤ q, Odd K_k, k ≥ 1.",
    "AUDIT (attack line 1, honest): the zero-run bridge hypothesis of " ++
      "carry_tracks_slopeOrbit constrains the digits over the whole prefix [0, ≈2X] anchored " ++
      "at position 0, while class-1 membership constrains only the r+2 hits at one window " ++
      "start above X ≥ 2^28 — the hypothesis is NOT derivable from class-1-pinned starts; a " ++
      "second mismatch is positions (gapOrbit) vs hit indices (route sampling).",
    "AUDIT (attack line 2, honest): only the start k itself is forced into band 4 " ++
      "(genuineChargeRoute_eq_one_iff reads the orbit only at k); persistence is FALSE in " ++
      "general (q = 9: odd cycle 1 → 7 → 5, band 4 only every third index).  The free " ++
      "consequences of a single banded index are exactly the parity pin, the modulus window, " ++
      "and the q ≤ 15 pin K_k = 1 — all formalized here.",
    "AUDIT (attack line 3, honest): no proved min-gap > 1 exists inside the carry window " ++
      "(adjacent support digits are not excluded by any formalized lemma), and the ceiling " ++
      "gate 64(r+1)(L+B+1) < 129L+64 fails for EVERY r ≥ 2 shell since 64·3 = 192 > 129; the " ++
      "gap-ceiling route is structurally confined to r ≤ 1.",
    "NOT CLOSED (the honest wave-2 residual): shells with 64 ∣ L, odd modulus q ∈ {9,11,13," ++
      "15} ∪ {25,27,…} whose odd orbit cycle contains a band-4 element at a window-reachable " ++
      "index, where some carry-window start k ≥ 1 with Odd K_k realizes the exact pin " ++
      "64·gapWindow = 129L + 64 at a band-4 index.  The digit-side pin and the orbit-side " ++
      "pin remain coupled only through the shared index k; no formalized bridge ties them " ++
      "for the actual ctx.  We do NOT claim unconditional closure of the atom." ]

theorem cnlClass1ClosureStatus_nonempty : cnlClass1ClosureStatus ≠ [] := by
  simp [cnlClass1ClosureStatus]

/-! ## Part 7.  Axiom-cleanliness audit -/

#print axioms canonGap_pos
#print axioms boundedSlopeStep_odd
#print axioms slopeOrbit_odd
#print axioms n24_firstIndexAbove_pos
#print axioms n24_starts_pos
#print axioms class1Fibre_start_pos
#print axioms class1Fibre_orbit_odd
#print axioms band_four_odd_modulus_window
#print axioms modulus_window_of_class1Fibre_nonempty
#print axioms class1Fibre_empty_of_modulus_window
#print axioms v3_class1Fibre_empty_of_modulus_window
#print axioms class1Fibre_orbit_eq_one_of_modulus_le_15
#print axioms class1SlopeDatum_q_eq
#print axioms class1SlopeDatum_H_dvd
#print axioms class1SlopeDatum_K₀_eq
#print axioms class1SlopeDatum_two_K₀_lt
#print axioms boundedSlopeStep_inj_of_odd
#print axioms slopeOrbit_eq_shift
#print axioms slopeOrbit_cancel
#print axioms slopeOrbit_exists_period
#print axioms class1Fibre_orbit_period_exists
#print axioms class1Fibre_empty_of_orbit_band_free
#print axioms class1Fibre_empty_of_cycle_band_free
#print axioms v3_class1Fibre_empty_of_cycle_band_free
#print axioms mem_class1Fibre_iff_sharp
#print axioms class1Fibre_eq_pinnedFilter_sharp
#print axioms v3_class1FibreEmpty_iff_pinned_sharp
#print axioms class1FibreEmpty_of_pinned_arithmetic_sharp
#print axioms erdos260_p9V3_of_pinned_arithmetic_sharp

end

end Erdos260
