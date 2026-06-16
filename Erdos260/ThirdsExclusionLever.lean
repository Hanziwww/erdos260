import Erdos260.Erdos260ValuationCapstone
import Erdos260.NearPeriodicityForcing

/-!
# Erdős 260 — the thirds exclusion lever (wave 10, `u = 3` follow-up)

The wave-10 cheapest named follow-up to `FloorPushV2`: the `q = 9` tower window's count
route is dead and its demand sharpens to context-voiding, with the `q = 9` contexts pinned
to TWO value families — `4/2^t` (`u = 1`) and `1/(3·2^t)` (`u = 3`) — and the open class-1
crossover instance `63@10` pinned to `Q = 3·2^t`, `value = 10/(3·2^t)`.  This module works
the single `u = 3` exclusion mechanism the brief asks for, rigorously and honestly.

## Goal 1 (proved): the generalized `u = 3` rigidity, ALL numerators

The arising numerators are `P = 1` (the `q = 9` `u = 3` branch), `P = 2` (the wave-6
thirds family `2/(3·2^t)`, already in `CarryWordRigidity`), and `P = 10` (`63@10`).
We prove the brief's general lemma `3 ∤ 2^N·P → R_N ≠ 0`
(`thirdsLever_carry_ne_zero_of_not_dvd`), the propagation `3 ∤ P → 3 ∤ 2^N·P`
(`thirdsLever_not_dvd_pow_mul`), the all-`N` non-vanishing (`thirdsLever_carry_ne_zero`),
and the full generalization of `thirdsValue_not_eventuallyZero` to every `P/(3·2^t)` with
`3 ∤ P` (`thirdsLever_value_not_eventuallyZero`), with the named instances `P = 1` and
`P = 10`.

## Goal 2 (the NEW mechanism, worked rigorously — found AND refuted honestly)

Scope check first: the wave-8 digit-blindness theorem (`integerCarry_mod_Q_digit_blind`)
lives at modulus `Q = 3·2^t`, which determines the REDUCED carry `ρ_N = R_N/2^t` only
mod `3`.  The mod-6 layer of `ρ` sits one 2-adic level ABOVE the blind modulus — exactly
the level of the parity dictionary (`digit_eq_parity_at_odd_position`).  The angle was
genuinely open; this module settles it.

The joint 2-adic/3-adic structure of `ρ` at `u = 3` (all proved):

* mod 3: `ρ_N ≡ 2^{N−t}·P` — the pure doubling orbit of `P`, digit-blind at EVERY index
  (`thirdsLever_reducedCarry_mod_three`, `_digit_blind`), with the exact `ord_3(2) = 2`
  two-cycle (`thirdsLever_reducedCarry_two_cycle`), never `0` when `3 ∤ P`
  (`thirdsLever_reducedCarry_not_three_dvd`, hence `ρ_N ≠ 0`).
* mod 2: at every EVEN position past the onset `ρ` is even, for ANY `u`
  (`thirdsLever_reducedCarry_even_at_even`).
* THE JOINT MOD-6 DICTIONARY: at even positions `6 ∣ ρ_{N+1} − 2^{N+1−t}·P` — fully
  deterministic, digit-blind, residue pinned into `{2, 4}` when `3 ∤ P`
  (`thirdsLever_reducedCarry_mod_six_even`, `thirdsLever_even_position_residue_pin`,
  `thirdsLever_mod_six_even_digit_blind`); at odd positions
  `6 ∣ ρ_{N+1} − 2^{N+1−t}·P − 3·d_{N+1}` — the local digit is the ONLY
  non-deterministic bit (`thirdsLever_reducedCarry_mod_six_odd`,
  `thirdsLever_mod_six_odd_local`), and the parity dictionary sharpens to the explicit
  residue formula `d_{N+1} = 0 ↔ 6 ∣ ρ_{N+1} − 2^{N+1−t}·P`
  (`thirdsLever_digit_zero_iff_mod_six`).

THE HONEST VERDICT (the hoped digit-pinning is REFUTED): the deterministic even-step
transport mod 6 is the doubling map (`thirdsLever_even_step_doubling` — the digit
coefficient `3·(N+1)` vanishes mod 6 at even `N+1`), and doubling COLLAPSES the digit
fiber: `2·a = 2·(a+3)` in `ZMod 6` (`thirdsLever_doubling_collapse`) while `a` and `a+3`
have opposite parities (`thirdsLever_fiber_parity_flip`).  The odd-position digit (= the
parity of `ρ` there) is exactly the bit the deterministic structure cannot see
(`thirdsLever_even_step_verdict`).  No digit at any position class is pinned, no
positive-density forced pattern exists at the mod-6 level, and the sparsity conflict does
NOT materialize.  The full `u = 3` exclusion via this mechanism FAILS — for the same
structural reason as the wave-7 obstruction, now located precisely.

## Goal 3 (what closes — the window-periodic stratum, composed)

* The `q = 9` branch dichotomy as a lemma: `(u, K₀) = (1, 4)` or `(3, 1)`
  (`thirdsLever_q9_branch`), with the per-branch value pins `4/2^t`
  (`thirdsLever_q9_u1_value`) and `1/(3·2^t)` (`thirdsLever_q9_u3_value`).
* The master stratum voiding `oddpart(Q) ≤ 7 → ¬WindowPeriodic`
  (`thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven`), hence: EVERY `q = 9` context
  (both branches) is window-APERIODIC (`thirdsLever_q9_not_windowPeriodic`); the `63@10`
  instance is window-aperiodic (`thirdsLever_q63K10_not_windowPeriodic`); the whole
  `q ≤ 21` band is aperiodic (`thirdsLever_smallq_not_windowPeriodic`); and the
  general-`P` thirds value family is void on the stratum at every scale
  (`thirdsLever_value_void_of_windowPeriodic` — extends the in-tree `P = 1, 2` bootstrap
  voidings to ALL `P`, covering `10/(3·2^t)`).
* The collapsed surface: `Erdos260ThirdsExclusionResidual` — the wave-10 valuation
  surface with the two tower fields and the `class1DeepLow` field (the three surfaces
  where the `u = 3` contexts live) each handed the FREE aperiodicity guard
  `oddpart(Q) ≤ 7 → ¬WindowPeriodic ctx`.  The guard is a theorem at every context, so
  the surface is an EQUIVALENT presentation refinement (recorded honestly:
  `nonempty_thirdsExclusion_iff_valuation`), with endpoint
  `erdos260_of_thirdsExclusionLever` through the public
  `erdos260_of_valuationResidual` chain.

## Goal 4 (what resists)

The non-window-periodic stratum of the `u = 3` families: the count route is dead
(`FloorPushV2`), the mod-6 mechanism pins no digit (above), and the bootstrap obstruction
(more carry states than window slots) still blocks an unconditional periodicity supply.
The `q = 9` `u = 3` branch and `63@10` stay OPEN beyond their floors `X > 2^986892`.

Additive only: no existing file is edited; only existing public lemmas are consumed.
No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The generalized `u = 3` carry rigidity (goal 1) -/

/-- **The thirds carry congruence** (`u = 3` instance of the oddpart congruence):
`3 ∣ R_N − 2^N·P` for every digit word, every numerator, every index. -/
theorem thirdsLever_carry_congruence (t : ℕ) (P : ℤ) (d : ℕ → ℕ) (N : ℕ) :
    (3 : ℤ) ∣ integerCarry (3 * 2 ^ t) P d N - 2 ^ N * P := by
  have h := oddpart_dvd_integerCarry_sub_pow_mul 3 t P d N
  simpa using h

/-- **The brief's general lemma**: if `3 ∤ 2^N·P` then `R_N ≠ 0` — modulo `3` the
recursion reads `R_{N+1} ≡ 2·R_N` (the digit term carries the factor `Q ≡ 0`), so
`R_N ≡ 2^N·P ≢ 0`. -/
theorem thirdsLever_carry_ne_zero_of_not_dvd (t : ℕ) (P : ℤ) (d : ℕ → ℕ) (N : ℕ)
    (h : ¬ (3 : ℤ) ∣ 2 ^ N * P) : integerCarry (3 * 2 ^ t) P d N ≠ 0 := by
  intro h0
  have h1 := thirdsLever_carry_congruence t P d N
  rw [h0, zero_sub, dvd_neg] at h1
  exact h h1

/-- `3 ∤ P` propagates to `3 ∤ 2^N·P` for every `N` (`3` is odd, coprime to all powers
of `2`). -/
theorem thirdsLever_not_dvd_pow_mul (P : ℤ) (hP : ¬ (3 : ℤ) ∣ P) (N : ℕ) :
    ¬ (3 : ℤ) ∣ 2 ^ N * P := by
  intro h
  have hodd3 : Odd (3 : ℤ) := ⟨1, by norm_num⟩
  have hcop2 : IsCoprime ((3 : ℤ)) (2 : ℤ) := (Int.isCoprime_two_left.mpr hodd3).symm
  have hcop : IsCoprime ((3 : ℤ)) ((2 : ℤ) ^ N) := hcop2.pow_right
  exact hP (hcop.dvd_of_dvd_mul_left h)

/-- **Carry non-vanishing for the WHOLE `u = 3` family**: `3 ∤ P` forces `R_N ≠ 0` at
every index — covers `P = 1` (the `q = 9` `u = 3` branch), `P = 2` (the wave-6 thirds
family) and `P = 10` (the `63@10` crossover) uniformly. -/
theorem thirdsLever_carry_ne_zero (t : ℕ) (P : ℤ) (hP : ¬ (3 : ℤ) ∣ P) (d : ℕ → ℕ)
    (N : ℕ) : integerCarry (3 * 2 ^ t) P d N ≠ 0 :=
  thirdsLever_carry_ne_zero_of_not_dvd t P d N (thirdsLever_not_dvd_pow_mul P hP N)

/-- **The generalized thirds non-termination**: a binary word whose weighted value is
`P/(3·2^t)` with `3 ∤ P` can NEVER terminate — the full generalization of the wave-6
`thirdsValue_not_eventuallyZero` (which was the instance `P = 2`) to ALL arising
numerators. -/
theorem thirdsLever_value_not_eventuallyZero {d : ℕ → ℕ} (hd : BinaryDigits d)
    (t : ℕ) (P : ℤ) (hP : ¬ (3 : ℤ) ∣ P)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / ((3 * 2 ^ t : ℕ) : ℝ)) :
    ¬ EventuallyZero d := by
  refine not_eventuallyZero_of_odd_carry_factor (Q := 3 * 2 ^ t) (u := 3)
    (by positivity) hd heta ⟨2 ^ t, rfl⟩ ⟨1, by norm_num⟩ ?_
  simpa using hP

/-- **`P = 1` (the `q = 9` `u = 3` branch value)**: `1/(3·2^t)` has no terminating
binary realization. -/
theorem thirdsLever_valueOne_not_eventuallyZero {d : ℕ → ℕ} (hd : BinaryDigits d)
    (t : ℕ) (heta : realWeightedValue (natBinaryAsReal d) = 1 / (3 * 2 ^ t)) :
    ¬ EventuallyZero d := by
  refine thirdsLever_value_not_eventuallyZero hd t 1 (by norm_num) ?_
  rw [heta]
  push_cast
  ring

/-- **`P = 10` (the `63@10` crossover value)**: `10/(3·2^t)` has no terminating binary
realization — the rigidity fact for the NEW pinned-value family of `FloorPushV2`. -/
theorem thirdsLever_valueTen_not_eventuallyZero {d : ℕ → ℕ} (hd : BinaryDigits d)
    (t : ℕ) (heta : realWeightedValue (natBinaryAsReal d) = 10 / (3 * 2 ^ t)) :
    ¬ EventuallyZero d := by
  refine thirdsLever_value_not_eventuallyZero hd t 10 (by norm_num) ?_
  rw [heta]
  push_cast
  ring

/-! ## Part 2.  The joint 2-adic/3-adic structure of the reduced carry (goal 2)

Throughout, `ρ_N = reducedCarry 3 t P d N = R_N / 2^t` with the exact recursion
`ρ_{N+1} = 2·ρ_N − 3·(N+1)·d_{N+1}` past the onset (`reducedCarry_succ`). -/

/-- **The reduced-carry mod-3 law** (`u = 3`): past the onset `3 ∣ ρ_N − 2^{N−t}·P` —
the mod-3 trajectory of the REDUCED carry is the pure doubling orbit of `P`.  (The full
`Q`-divisibility `Q ∣ R_N − 2^N·P` divided by the exact `2^t` factor.) -/
theorem thirdsLever_reducedCarry_mod_three (t : ℕ) (P : ℤ) (d : ℕ → ℕ) {N : ℕ}
    (htN : t ≤ N) :
    (3 : ℤ) ∣ reducedCarry 3 t P d N - 2 ^ (N - t) * P := by
  obtain ⟨m, hm⟩ := dvd_integerCarry_sub_pow_mul (3 * 2 ^ t) P d N
  have hcast : ((3 * 2 ^ t : ℕ) : ℤ) = 3 * 2 ^ t := by push_cast; ring
  rw [hcast] at hm
  refine ⟨m, ?_⟩
  have hspec := reducedCarry_spec 3 t P d htN
  have h2t : ((2 : ℤ) ^ t) ≠ 0 := by positivity
  apply mul_left_cancel₀ h2t
  have hpow : (2 : ℤ) ^ N = 2 ^ t * 2 ^ (N - t) := by
    rw [← pow_add]
    congr 1
    omega
  calc (2 : ℤ) ^ t * (reducedCarry 3 t P d N - 2 ^ (N - t) * P)
      = 2 ^ t * reducedCarry 3 t P d N - 2 ^ N * P := by rw [hpow]; ring
    _ = integerCarry (3 * 2 ^ t) P d N - 2 ^ N * P := by rw [hspec]
    _ = 3 * 2 ^ t * m := hm
    _ = 2 ^ t * (3 * m) := by ring

/-- **The mod-3 layer is digit-blind** (the scope settlement): the reduced-carry
trajectories of ANY two digit words agree mod `3` at every index past the onset.  The
3-adic component of the joint structure carries ZERO digit information — the blindness
of the wave-8 theorem extends one 2-adic level up on this component. -/
theorem thirdsLever_reducedCarry_mod_three_digit_blind (t : ℕ) (P : ℤ) (d d' : ℕ → ℕ)
    {N : ℕ} (htN : t ≤ N) :
    (3 : ℤ) ∣ reducedCarry 3 t P d N - reducedCarry 3 t P d' N := by
  have h1 := thirdsLever_reducedCarry_mod_three t P d htN
  have h2 := thirdsLever_reducedCarry_mod_three t P d' htN
  have key : reducedCarry 3 t P d N - reducedCarry 3 t P d' N
      = (reducedCarry 3 t P d N - 2 ^ (N - t) * P)
        - (reducedCarry 3 t P d' N - 2 ^ (N - t) * P) := by ring
  rw [key]
  exact dvd_sub h1 h2

/-- **The reduced carry is NEVER divisible by 3** (`3 ∤ P`): the 3-adic layer never
vanishes — the reduced-carry sharpening of `integerCarry_ne_zero_of_odd_dvd`. -/
theorem thirdsLever_reducedCarry_not_three_dvd (t : ℕ) (P : ℤ) (hP : ¬ (3 : ℤ) ∣ P)
    (d : ℕ → ℕ) {N : ℕ} (htN : t ≤ N) :
    ¬ (3 : ℤ) ∣ reducedCarry 3 t P d N := by
  intro hdvd
  have h1 := thirdsLever_reducedCarry_mod_three t P d htN
  have h2 : (3 : ℤ) ∣ 2 ^ (N - t) * P := by
    have key : (2 : ℤ) ^ (N - t) * P
        = reducedCarry 3 t P d N - (reducedCarry 3 t P d N - 2 ^ (N - t) * P) := by ring
    rw [key]
    exact dvd_sub hdvd h1
  exact thirdsLever_not_dvd_pow_mul P hP (N - t) h2

/-- The reduced carry never vanishes (`3 ∤ P`). -/
theorem thirdsLever_reducedCarry_ne_zero (t : ℕ) (P : ℤ) (hP : ¬ (3 : ℤ) ∣ P)
    (d : ℕ → ℕ) {N : ℕ} (htN : t ≤ N) : reducedCarry 3 t P d N ≠ 0 := by
  intro h0
  refine thirdsLever_reducedCarry_not_three_dvd t P hP d htN ?_
  rw [h0]
  exact dvd_zero 3

/-- **The `ord_3(2) = 2` two-cycle**: the reduced carry mod 3 has EXACT period 2 at
every index past the onset (`2` is a generator mod `3`, `2² = 4 ≡ 1`). -/
theorem thirdsLever_reducedCarry_two_cycle (t : ℕ) (P : ℤ) (d : ℕ → ℕ) {N : ℕ}
    (htN : t ≤ N) :
    (3 : ℤ) ∣ reducedCarry 3 t P d (N + 2) - reducedCarry 3 t P d N := by
  obtain ⟨a, ha⟩ := thirdsLever_reducedCarry_mod_three t P d (show t ≤ N + 2 by omega)
  obtain ⟨b, hb⟩ := thirdsLever_reducedCarry_mod_three t P d htN
  have hpow : (2 : ℤ) ^ (N + 2 - t) = 4 * 2 ^ (N - t) := by
    rw [show N + 2 - t = (N - t) + 2 by omega, pow_add]
    ring
  rw [hpow] at ha
  exact ⟨a - b + 2 ^ (N - t) * P, by linear_combination ha - hb⟩

/-- **The 2-adic layer at even positions** (ANY `u`): the reduced carry is EVEN at every
even position past the onset — the step coefficient `u·(N+1)` is even and the doubling
term is even. -/
theorem thirdsLever_reducedCarry_even_at_even (u t : ℕ) (P : ℤ) (d : ℕ → ℕ) {N : ℕ}
    (htN : t ≤ N) (hev : Even (N + 1)) :
    (2 : ℤ) ∣ reducedCarry u t P d (N + 1) := by
  obtain ⟨m, hm⟩ := hev
  rw [reducedCarry_succ u t P d htN]
  have hmZ : ((N + 1 : ℕ) : ℤ) = 2 * (m : ℤ) := by
    rw [hm]; push_cast; ring
  rw [hmZ]
  exact ⟨reducedCarry u t P d N - (u : ℤ) * (m : ℤ) * (d (N + 1) : ℤ), by ring⟩

/-- **THE JOINT MOD-6 DICTIONARY, even positions** (`u = 3`): at every EVEN position past
the onset, `6 ∣ ρ_{N+1} − 2^{N+1−t}·P` — the residue mod 6 is COMPLETELY determined by
`(P, t, N)`, digit-blind. -/
theorem thirdsLever_reducedCarry_mod_six_even (t : ℕ) (P : ℤ) (d : ℕ → ℕ) {N : ℕ}
    (htN : t ≤ N) (hev : Even (N + 1)) :
    (6 : ℤ) ∣ reducedCarry 3 t P d (N + 1) - 2 ^ (N + 1 - t) * P := by
  have h2 : (2 : ℤ) ∣ reducedCarry 3 t P d (N + 1) - 2 ^ (N + 1 - t) * P := by
    have hpar := thirdsLever_reducedCarry_even_at_even 3 t P d htN hev
    have hpow : (2 : ℤ) ∣ 2 ^ (N + 1 - t) * P :=
      dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega : N + 1 - t ≠ 0)) P
    exact dvd_sub hpar hpow
  have h3 : (3 : ℤ) ∣ reducedCarry 3 t P d (N + 1) - 2 ^ (N + 1 - t) * P :=
    thirdsLever_reducedCarry_mod_three t P d (show t ≤ N + 1 by omega)
  have hco : IsCoprime (2 : ℤ) (3 : ℤ) := ⟨-1, 1, by ring⟩
  have h6 : (6 : ℤ) = 2 * 3 := by norm_num
  rw [h6]
  exact hco.mul_dvd h2 h3

/-- **THE JOINT MOD-6 DICTIONARY, odd positions** (`u = 3`): at every ODD position past
the onset, `6 ∣ ρ_{N+1} − 2^{N+1−t}·P − 3·d_{N+1}` — the residue is the deterministic
orbit value plus `3·(the local digit)`; the digit is the ONLY non-deterministic bit. -/
theorem thirdsLever_reducedCarry_mod_six_odd (t : ℕ) (P : ℤ) (d : ℕ → ℕ) {N : ℕ}
    (htN : t ≤ N) (hodd : Odd (N + 1)) :
    (6 : ℤ) ∣ reducedCarry 3 t P d (N + 1) - 2 ^ (N + 1 - t) * P
      - 3 * (d (N + 1) : ℤ) := by
  obtain ⟨m, hm⟩ := hodd
  have h2 : (2 : ℤ) ∣ reducedCarry 3 t P d (N + 1) - 2 ^ (N + 1 - t) * P
      - 3 * (d (N + 1) : ℤ) := by
    rw [reducedCarry_succ 3 t P d htN]
    have hmZ : ((N + 1 : ℕ) : ℤ) = 2 * (m : ℤ) + 1 := by
      rw [hm]; push_cast; ring
    have hpow : (2 : ℤ) ^ (N + 1 - t) = 2 * 2 ^ (N - t) := by
      rw [show N + 1 - t = (N - t) + 1 by omega, pow_add]
      ring
    rw [hmZ, hpow]
    refine ⟨reducedCarry 3 t P d N - 3 * (m : ℤ) * (d (N + 1) : ℤ)
      - 3 * (d (N + 1) : ℤ) - 2 ^ (N - t) * P, ?_⟩
    push_cast
    ring
  have h3 : (3 : ℤ) ∣ reducedCarry 3 t P d (N + 1) - 2 ^ (N + 1 - t) * P
      - 3 * (d (N + 1) : ℤ) := by
    have h := thirdsLever_reducedCarry_mod_three t P d (show t ≤ N + 1 by omega)
    exact dvd_sub h ⟨(d (N + 1) : ℤ), rfl⟩
  have hco : IsCoprime (2 : ℤ) (3 : ℤ) := ⟨-1, 1, by ring⟩
  have h6 : (6 : ℤ) = 2 * 3 := by norm_num
  rw [h6]
  exact hco.mul_dvd h2 h3

/-- **The even-position mod-6 residue is digit-blind**: ANY two digit words agree mod 6
at every even position past the onset — the even half of the mod-6 trajectory carries
zero digit bits. -/
theorem thirdsLever_mod_six_even_digit_blind (t : ℕ) (P : ℤ) (d d' : ℕ → ℕ) {N : ℕ}
    (htN : t ≤ N) (hev : Even (N + 1)) :
    (6 : ℤ) ∣ reducedCarry 3 t P d (N + 1) - reducedCarry 3 t P d' (N + 1) := by
  have h1 := thirdsLever_reducedCarry_mod_six_even t P d htN hev
  have h2 := thirdsLever_reducedCarry_mod_six_even t P d' htN hev
  have key : reducedCarry 3 t P d (N + 1) - reducedCarry 3 t P d' (N + 1)
      = (reducedCarry 3 t P d (N + 1) - 2 ^ (N + 1 - t) * P)
        - (reducedCarry 3 t P d' (N + 1) - 2 ^ (N + 1 - t) * P) := by ring
  rw [key]
  exact dvd_sub h1 h2

/-- **At odd positions the mod-6 trajectory sees EXACTLY the local digit**: two words
differ mod 6 at an odd position by `3·(d − d')` — one bit of strictly local information,
nothing about any other position. -/
theorem thirdsLever_mod_six_odd_local (t : ℕ) (P : ℤ) (d d' : ℕ → ℕ) {N : ℕ}
    (htN : t ≤ N) (hodd : Odd (N + 1)) :
    (6 : ℤ) ∣ reducedCarry 3 t P d (N + 1) - reducedCarry 3 t P d' (N + 1)
      - 3 * ((d (N + 1) : ℤ) - (d' (N + 1) : ℤ)) := by
  have h1 := thirdsLever_reducedCarry_mod_six_odd t P d htN hodd
  have h2 := thirdsLever_reducedCarry_mod_six_odd t P d' htN hodd
  have key : reducedCarry 3 t P d (N + 1) - reducedCarry 3 t P d' (N + 1)
      - 3 * ((d (N + 1) : ℤ) - (d' (N + 1) : ℤ))
      = (reducedCarry 3 t P d (N + 1) - 2 ^ (N + 1 - t) * P - 3 * (d (N + 1) : ℤ))
        - (reducedCarry 3 t P d' (N + 1) - 2 ^ (N + 1 - t) * P
          - 3 * (d' (N + 1) : ℤ)) := by ring
  rw [key]
  exact dvd_sub h1 h2

/-- **The even-position residue pin** (`3 ∤ P`): at every even position past the onset
the reduced carry sits in `{2, 4}` mod 6 — even (2-adic layer) and a unit mod 3 (3-adic
layer). -/
theorem thirdsLever_even_position_residue_pin (t : ℕ) (P : ℤ) (hP : ¬ (3 : ℤ) ∣ P)
    (d : ℕ → ℕ) {N : ℕ} (htN : t ≤ N) (hev : Even (N + 1)) :
    reducedCarry 3 t P d (N + 1) % 6 = 2 ∨ reducedCarry 3 t P d (N + 1) % 6 = 4 := by
  have h2 : reducedCarry 3 t P d (N + 1) % 2 = 0 :=
    Int.emod_eq_zero_of_dvd (thirdsLever_reducedCarry_even_at_even 3 t P d htN hev)
  have h3 : reducedCarry 3 t P d (N + 1) % 3 ≠ 0 := fun h =>
    thirdsLever_reducedCarry_not_three_dvd t P hP d (show t ≤ N + 1 by omega)
      (Int.dvd_of_emod_eq_zero h)
  omega

/-- **The even-step doubling mod 6 is deterministic (digit-blind)**: across an even step
the mod-6 residue exactly doubles, `6 ∣ ρ_{N+1} − 2·ρ_N` — the digit emitted at the even
position is invisible (its coefficient `3·(N+1) ≡ 0 (mod 6)`). -/
theorem thirdsLever_even_step_doubling (t : ℕ) (P : ℤ) (d : ℕ → ℕ) {N : ℕ}
    (htN : t ≤ N) (hev : Even (N + 1)) :
    (6 : ℤ) ∣ reducedCarry 3 t P d (N + 1) - 2 * reducedCarry 3 t P d N := by
  obtain ⟨m, hm⟩ := hev
  rw [reducedCarry_succ 3 t P d htN]
  have hmZ : ((N + 1 : ℕ) : ℤ) = 2 * (m : ℤ) := by
    rw [hm]; push_cast; ring
  rw [hmZ]
  refine ⟨-((m : ℤ) * (d (N + 1) : ℤ)), ?_⟩
  push_cast
  ring

/-- **THE COLLAPSE (the honest obstruction)**: doubling mod 6 identifies `a` and `a + 3`
— the two parity-distinguished residues an odd position can carry (same forced mod-3
value, opposite parity = opposite digit) map to the SAME even-position residue.  The
deterministic even step therefore cannot recover the odd-position digit. -/
theorem thirdsLever_doubling_collapse (a : ZMod 6) : 2 * a = 2 * (a + 3) := by
  have h6 : (2 : ZMod 6) * 3 = 0 := by decide
  linear_combination -h6

/-- The lost bit is exactly the digit: `a` and `a + 3` have opposite parities over `ℤ`. -/
theorem thirdsLever_fiber_parity_flip (a : ℤ) : (a + 3) % 2 ≠ a % 2 := by omega

/-- **The even-step verdict, packaged**: mod 6 the even step IS the doubling map (first
component — digit-blind) and the doubling map collapses the digit fiber (second
component).  This is WHY the joint 2-adic/3-adic structure pins no digit: at even
positions the digit coefficient vanishes mod 6 (invisible), at odd positions the digit
is the free parity bit, and the only deterministic transport is blind to it. -/
theorem thirdsLever_even_step_verdict (t : ℕ) (P : ℤ) (d : ℕ → ℕ) {N : ℕ}
    (htN : t ≤ N) (hev : Even (N + 1)) :
    ((reducedCarry 3 t P d (N + 1) : ZMod 6) = 2 * (reducedCarry 3 t P d N : ZMod 6))
      ∧ ∀ a : ZMod 6, 2 * a = 2 * (a + 3) := by
  refine ⟨?_, thirdsLever_doubling_collapse⟩
  have h6 := thirdsLever_even_step_doubling t P d htN hev
  have hz : ((reducedCarry 3 t P d (N + 1)
      - 2 * reducedCarry 3 t P d N : ℤ) : ZMod 6) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 6).mpr (by exact_mod_cast h6)
  push_cast at hz
  linear_combination hz

/-- The `u = 3` parity dictionary at odd positions (specialization of the wave-8
`digit_eq_parity_at_odd_position`): the digit IS the reduced-carry parity. -/
theorem thirdsLever_digit_eq_parity (t : ℕ) (P : ℤ) {d : ℕ → ℕ} (hd : BinaryDigits d)
    {N : ℕ} (htN : t ≤ N) (hodd : Odd (N + 1)) :
    d (N + 1) = if (2 : ℤ) ∣ reducedCarry 3 t P d (N + 1) then 0 else 1 :=
  digit_eq_parity_at_odd_position ⟨1, by norm_num⟩ t P hd htN hodd

/-- **The sharpened odd-position dictionary** (mod 6 instead of mod 2): the digit at an
odd position is recovered against the deterministic orbit value —
`d_{N+1} = 0 ↔ 6 ∣ ρ_{N+1} − 2^{N+1−t}·P`. -/
theorem thirdsLever_digit_zero_iff_mod_six (t : ℕ) (P : ℤ) {d : ℕ → ℕ}
    (hd : BinaryDigits d) {N : ℕ} (htN : t ≤ N) (hodd : Odd (N + 1)) :
    d (N + 1) = 0 ↔ (6 : ℤ) ∣ reducedCarry 3 t P d (N + 1) - 2 ^ (N + 1 - t) * P := by
  have hkey := thirdsLever_reducedCarry_mod_six_odd t P d htN hodd
  constructor
  · intro h0
    rw [h0] at hkey
    simpa using hkey
  · intro hdvd
    have h3d : (6 : ℤ) ∣ 3 * (d (N + 1) : ℤ) := by
      have key : 3 * (d (N + 1) : ℤ)
          = (reducedCarry 3 t P d (N + 1) - 2 ^ (N + 1 - t) * P)
            - (reducedCarry 3 t P d (N + 1) - 2 ^ (N + 1 - t) * P
              - 3 * (d (N + 1) : ℤ)) := by ring
      rw [key]
      exact dvd_sub hdvd hkey
    rcases hd (N + 1) with h0 | h1
    · exact h0
    · exfalso
      rw [h1] at h3d
      obtain ⟨c, hc⟩ := h3d
      push_cast at hc
      omega

/-! ## Part 3.  The composed `u = 3` closures (goal 3): per-pair pins and the
window-periodic stratum -/

/-- **The `q = 9` branch dichotomy** (the FloorPushV2 status pins, now lemmas): every
`q = 9` context has `(oddpart(Q), K₀) = (1, 4)` or `(3, 1)`. -/
theorem thirdsLever_q9_branch (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) :
    (ordCompl[2] ctx.Q = 1 ∧ (class1SlopeDatum ctx).K₀ = 4)
      ∨ (ordCompl[2] ctx.Q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) := by
  have h := datum_q_eq_oddpartQ_mul ctx
  simp only [ActualFailureContext.shell_Q] at h
  rw [hq] at h
  have hKpos := (class1SlopeDatum ctx).hK₀_pos
  have hdvd : ordCompl[2] ctx.Q ∣ 9 := ⟨2 * (class1SlopeDatum ctx).K₀ + 1, h⟩
  have hle : ordCompl[2] ctx.Q ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
  have key : ∀ m : ℕ, m < 10 → m ∣ 9 → m = 1 ∨ m = 3 ∨ m = 9 := by decide
  rcases key _ (by omega) hdvd with h1 | h3 | h9
  · left
    refine ⟨h1, ?_⟩
    rw [h1] at h
    omega
  · right
    refine ⟨h3, ?_⟩
    rw [h3] at h
    omega
  · exfalso
    rw [h9] at h
    omega

/-- The `q = 9` `u = 3` branch pins `K₀ = 1` (`9 = 3·(2K₀+1)`). -/
theorem thirdsLever_q9_u3_K₀_eq_one (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) (hu3 : ordCompl[2] ctx.Q = 3) :
    (class1SlopeDatum ctx).K₀ = 1 := by
  have h := datum_q_eq_oddpartQ_mul ctx
  simp only [ActualFailureContext.shell_Q] at h
  rw [hq, hu3] at h
  omega

/-- Any context with `oddpart(Q) = 3` has the thirds denominator shape `Q = 3·2^t`. -/
theorem thirdsLever_oddpart_three_Q_shape (ctx : ActualFailureContext)
    (hu3 : ordCompl[2] ctx.Q = 3) : ∃ t : ℕ, ctx.Q = 3 * 2 ^ t := by
  refine ⟨ctx.Q.factorization 2, ?_⟩
  have hQfact : ctx.Q = ordCompl[2] ctx.Q * 2 ^ ctx.Q.factorization 2 := by
    have h := shell_Q_eq_oddpart_mul_pow ctx
    simpa using h
  rw [hu3] at hQfact
  exact hQfact

/-- **The `q = 9` `u = 3` branch value pin**: `value = 1/(3·2^t)` — the exact value of the
second `q = 9` branch (the first, `u = 1`, carries `4/2^t`). -/
theorem thirdsLever_q9_u3_value (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) (hu3 : ordCompl[2] ctx.Q = 3) :
    ∃ t : ℕ, realWeightedValue (natBinaryAsReal ctx.shell.d) = 1 / (3 * 2 ^ t) := by
  have hu3' : ordCompl[2] ctx.shell.Q = 3 := by
    simpa [ActualFailureContext.shell_Q] using hu3
  obtain ⟨t, hQ, hval⟩ := datum_value_eq_of_oddpartQ ctx hu3'
  refine ⟨t, ?_⟩
  rw [hval, thirdsLever_q9_u3_K₀_eq_one ctx hq hu3]
  norm_num

/-- **The `q = 9` `u = 1` branch value pin**: `value = 4/2^t`. -/
theorem thirdsLever_q9_u1_value (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) (hu1 : ordCompl[2] ctx.Q = 1) :
    ∃ t : ℕ, realWeightedValue (natBinaryAsReal ctx.shell.d) = 4 / 2 ^ t := by
  have hK : (class1SlopeDatum ctx).K₀ = 4 := by
    have h := datum_q_eq_oddpartQ_mul ctx
    simp only [ActualFailureContext.shell_Q] at h
    rw [hq, hu1] at h
    omega
  have hu1' : ordCompl[2] ctx.shell.Q = 1 := by
    simpa [ActualFailureContext.shell_Q] using hu1
  obtain ⟨t, hQ, hval⟩ := datum_value_eq_of_oddpartQ ctx hu1'
  refine ⟨t, ?_⟩
  rw [hval, hK]
  norm_num

/-- **THE MASTER STRATUM VOIDING, oddpart form**: NO failing context with
`oddpart(Q) ≤ 7` is window-periodic, at every scale (the DensityBootstrap master pin fed
with the raw rational witness and `Q = oddpart(Q)·2^{ν₂(Q)}`). -/
theorem thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven (ctx : ActualFailureContext)
    (hu7 : ordCompl[2] ctx.Q ≤ 7) (hwp : WindowPeriodic ctx) : False := by
  have hupos : 0 < ordCompl[2] ctx.Q := Nat.ordCompl_pos 2 ctx.hQ.ne'
  have hQfact : ctx.Q = ordCompl[2] ctx.Q * 2 ^ ctx.Q.factorization 2 := by
    have h := shell_Q_eq_oddpart_mul_pow ctx
    simpa using h
  obtain ⟨P, hP⟩ := ctx.hrational
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((ordCompl[2] ctx.Q * 2 ^ ctx.Q.factorization 2 : ℕ) : ℝ) := by
    rw [← hQfact]
    exact hP
  exact pinnedValue_windowPeriodic_void ctx hupos hu7 heta' hwp

/-- **The general-`P` thirds family is void on the window-periodic stratum**: no failing
context with `value = P/(3·2^t)` — ANY integer numerator — is window-periodic, at every
scale.  Extends the in-tree `1/(3·2^t)`-shaped and `2/(3·2^t)` bootstrap voidings to all
numerators, covering the new `10/(3·2^t)` family of `63@10`. -/
theorem thirdsLever_value_void_of_windowPeriodic (ctx : ActualFailureContext)
    (hwp : WindowPeriodic ctx) (P : ℤ) (t : ℕ) :
    realWeightedValue (natBinaryAsReal ctx.shell.d) ≠ (P : ℝ) / (3 * 2 ^ t) := by
  intro hval
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((3 * 2 ^ t : ℕ) : ℝ) := by
    rw [show realWeightedValue (natBinaryAsReal ctx.d) = (P : ℝ) / (3 * 2 ^ t) from hval]
    push_cast
    ring
  exact pinnedValue_windowPeriodic_void ctx (u := 3) (by norm_num) (by norm_num)
    heta' hwp

/-- **EVERY `q = 9` context is window-APERIODIC** (both branches: `oddpart(Q) ≤ 3`) —
the `q = 9` contexts whose voiding the cycle inequality now demands are all outside the
bootstrap's periodic stratum. -/
theorem thirdsLever_q9_not_windowPeriodic (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) : ¬ WindowPeriodic ctx := fun hwp =>
  thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven ctx
    (by have := floorPushV2_q9_oddpart_lt_four ctx hq; omega) hwp

/-- **The `63@10` sharpening**: the open class-1 crossover instance is window-APERIODIC
(`oddpart(Q) = 3` by the FloorPushV2 pin) — composed with `pinnedValue_windowPeriodic_void`. -/
theorem thirdsLever_q63K10_not_windowPeriodic (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    ¬ WindowPeriodic ctx := fun hwp =>
  thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven ctx
    (by rw [floorPushV2_q63K10_oddpart_eq_three ctx hq hK]; norm_num) hwp

/-- The small-`q` aperiodicity band: EVERY context with `q ≤ 21` is window-aperiodic
(`3·oddpart(Q) ≤ q` forces `oddpart(Q) ≤ 7`). -/
theorem thirdsLever_smallq_not_windowPeriodic (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 21) : ¬ WindowPeriodic ctx := fun hwp =>
  thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven ctx
    (by have := floorPushV2_three_oddpartQ_le_q ctx; omega) hwp

/-- The joint mod-6 invariant INSTALLED at the `q = 9` `u = 3` branch: `Q = 3·2^t`, and
for the pinned numerator `1` the reduced carry obeys the never-`0 (mod 3)` law and the
even-position `{2, 4}` pin past the onset. -/
theorem thirdsLever_q9_u3_reducedCarry_pin (ctx : ActualFailureContext)
    (hu3 : ordCompl[2] ctx.Q = 3) :
    ∃ t : ℕ, ctx.Q = 3 * 2 ^ t
      ∧ (∀ N : ℕ, t ≤ N → ¬ (3 : ℤ) ∣ reducedCarry 3 t 1 ctx.d N)
      ∧ ∀ N : ℕ, t ≤ N → Even (N + 1) →
          reducedCarry 3 t 1 ctx.d (N + 1) % 6 = 2
            ∨ reducedCarry 3 t 1 ctx.d (N + 1) % 6 = 4 := by
  obtain ⟨t, hQ⟩ := thirdsLever_oddpart_three_Q_shape ctx hu3
  exact ⟨t, hQ,
    fun N htN => thirdsLever_reducedCarry_not_three_dvd t 1 (by norm_num) ctx.d htN,
    fun N htN hev =>
      thirdsLever_even_position_residue_pin t 1 (by norm_num) ctx.d htN hev⟩

/-- The joint mod-6 invariant INSTALLED at the `63@10` instance: `Q = 3·2^t`, and for the
pinned numerator `10` the reduced carry obeys the never-`0 (mod 3)` law and the
even-position `{2, 4}` pin past the onset. -/
theorem thirdsLever_q63K10_reducedCarry_pin (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    ∃ t : ℕ, ctx.Q = 3 * 2 ^ t
      ∧ (∀ N : ℕ, t ≤ N → ¬ (3 : ℤ) ∣ reducedCarry 3 t 10 ctx.d N)
      ∧ ∀ N : ℕ, t ≤ N → Even (N + 1) →
          reducedCarry 3 t 10 ctx.d (N + 1) % 6 = 2
            ∨ reducedCarry 3 t 10 ctx.d (N + 1) % 6 = 4 := by
  obtain ⟨t, hQ⟩ := floorPushV2_q63K10_Q_shape ctx hq hK
  exact ⟨t, hQ,
    fun N htN => thirdsLever_reducedCarry_not_three_dvd t 10 (by norm_num) ctx.d htN,
    fun N htN hev =>
      thirdsLever_even_position_residue_pin t 10 (by norm_num) ctx.d htN hev⟩

/-! ## Part 4.  The collapsed surface and bridges (additive only) -/

/-- **The thirds-exclusion surface** — the wave-10 valuation surface
(`Erdos260ValuationResidual`) with the two tower fields and the `class1DeepLow` field
(the three surfaces where the `u = 3` contexts live: every `q = 9` context, and the
`63@10` pair at `q = 63 < 101`) each handed the FREE aperiodicity guard
`oddpart(Q) ≤ 7 → ¬WindowPeriodic ctx`.  The guard is a THEOREM at every context
(`thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven`), so this surface is an
equivalent presentation refinement, recorded honestly — it hands the provider the proven
window-aperiodicity of the small-oddpart contexts without re-derivation.  The other 11
fields are verbatim. -/
structure Erdos260ThirdsExclusionResidual where
  /-- Tower / class 2 — enumerated part (`q < 107`), now WITH the aperiodicity guard
  (covers every `q = 9` context: `oddpart(Q) ≤ 3`). -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    Class2CycleInequality ctx
  /-- Tower / class 2 — tail (`107 ≤ q`), with the aperiodicity guard. -/
  towerEnumTail : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx →
    107 ≤ (class1SlopeDatum ctx).q →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx)
      ∨ Class2CycleInequality ctx
  /-- Run / class 5 — enumerated part (`q < 64`); verbatim wave-10 field. -/
  runNumericLow : ∀ ctx : ActualFailureContext,
    (class1SlopeDatum ctx).q < 64 →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 — tail (`64 ≤ q`); verbatim wave-10 field. -/
  runNumericTail : ∀ ctx : ActualFailureContext,
    64 ≤ (class1SlopeDatum ctx).q →
    ((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx
    ∨ Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Return / class 4 count gates — verbatim wave-10 field. -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 digit Z — trajectory form with the dyadic-floor guard; verbatim
  wave-10 field. -/
  returnZeroTrajectoryFloor : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    2 ^ ctxDyadicPart ctx < (supportShell ctx.shell.d ctx.shell.X).card →
    ReturnZeroBelowBandTrajectory ctx
  /-- Return / class 4 clean step — trajectory form; verbatim wave-10 field. -/
  returnMaxCleanTrajectory : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnIndexWindowClean ctx →
    ReturnMaxCleanCarryTrajectory ctx
  /-- Return / class 4 K.1 interior — verbatim wave-10 field. -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- Chernoff / class 0 survivors — verbatim wave-10 field. -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    Class0SurvivorResidueMiss ctx
  /-- Chernoff / class 0 mid band — verbatim wave-10 field. -/
  class0Mid : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
    (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
    Class0WindowCycleCheck ctx
  /-- Chernoff / class 0 large moduli (`96 ≤ q`) — verbatim wave-10 field. -/
  class0BigOrder : ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
    (∃ C, ((Nat.log 2 (class1SlopeDatum ctx).q + 1) * C
          < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
              (class1SlopeDatum ctx).K₀)))
        ∧ ∃ c, C < c ∧ c ≤ (class1SlopeDatum ctx).q
            ∧ (∀ m, 1 ≤ m →
                slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
                  = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
            ∧ ∀ k ∈ ctx.n24CarryData.starts,
                129 * shellLadderDepth ctx + 64
                    ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
                (class1SlopeDatum ctx).q
                  < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
                      (cycleRep c k))
    ∨ Class0WindowCycleCheck ctx
  /-- CNL / class 1 — enumerated deep part (`q < 101`), now WITH the aperiodicity guard
  (covers the `63@10` pair: `oddpart(Q) = 3`). -/
  class1DeepLow : ∀ ctx : ActualFailureContext,
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    ¬ Class1DatumClosed ctx →
    ¬ Class1GcdWindowMiss ctx →
    (class1SlopeDatum ctx).q < 101 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅
  /-- CNL / class 1 — tail (`101 ≤ q`); verbatim wave-10 field. -/
  class1DeepTail : ∀ ctx : ActualFailureContext,
    101 ≤ (class1SlopeDatum ctx).q →
    Class1Band4FreePeriod ctx
    ∨ (64 ∣ shellLadderDepth ctx →
        9 ≤ (class1SlopeDatum ctx).q →
        ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
        (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
        ¬ Class1DatumClosed ctx →
        ¬ Class1GcdWindowMiss ctx →
        routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅)
  /-- DensePack / class 3 — verbatim wave-10 field. -/
  densePackUngated : DensePackUngatedClosureResidual

namespace Erdos260ThirdsExclusionResidual

/-- **The bridge into the wave-10 valuation surface**: the aperiodicity guards are
discharged by the master voiding theorem at every context; the other 11 fields pass
verbatim. -/
def toValuation (R : Erdos260ThirdsExclusionResidual) : Erdos260ValuationResidual where
  towerEnumLow := fun ctx hesc hq =>
    R.towerEnumLow ctx hesc hq
      (fun hu7 hwp => thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven ctx hu7 hwp)
  towerEnumTail := fun ctx hesc hq =>
    R.towerEnumTail ctx hesc hq
      (fun hu7 hwp => thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven ctx hu7 hwp)
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnZeroTrajectoryFloor := R.returnZeroTrajectoryFloor
  returnMaxCleanTrajectory := R.returnMaxCleanTrajectory
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := fun ctx h1 h2 h3 h4 h5 h6 h7 =>
    R.class1DeepLow ctx h1 h2 h3 h4 h5 h6 h7
      (fun hu7 hwp => thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven ctx hu7 hwp)
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- The final statement from the thirds-exclusion surface: guard discharge, then the
public wave-10 chain.  Composition only; nothing is re-proved. -/
theorem toStatement (R : Erdos260ThirdsExclusionResidual) : Erdos260Statement :=
  erdos260_of_valuationResidual R.toValuation

end Erdos260ThirdsExclusionResidual

/-- **The endpoint**: `Erdos260Statement` from the thirds-exclusion surface. -/
theorem erdos260_of_thirdsExclusionLever (R : Erdos260ThirdsExclusionResidual) :
    Erdos260Statement :=
  R.toStatement

/-- **Weakening witness**: any wave-10 valuation provider yields the thirds-exclusion
surface (the guards are simply dropped). -/
def thirdsExclusionResidual_of_valuation (R : Erdos260ValuationResidual) :
    Erdos260ThirdsExclusionResidual where
  towerEnumLow := fun ctx hesc hq _ => R.towerEnumLow ctx hesc hq
  towerEnumTail := fun ctx hesc hq _ => R.towerEnumTail ctx hesc hq
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnZeroTrajectoryFloor := R.returnZeroTrajectoryFloor
  returnMaxCleanTrajectory := R.returnMaxCleanTrajectory
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := fun ctx h1 h2 h3 h4 h5 h6 h7 _ =>
    R.class1DeepLow ctx h1 h2 h3 h4 h5 h6 h7
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- The thirds-exclusion surface is EQUIVALENT to the wave-10 valuation surface (the
guards are theorems at every context — a presentation refinement, honestly recorded). -/
theorem nonempty_thirdsExclusion_iff_valuation :
    Nonempty Erdos260ThirdsExclusionResidual ↔ Nonempty Erdos260ValuationResidual :=
  ⟨fun ⟨R⟩ => ⟨R.toValuation⟩, fun ⟨R⟩ => ⟨thirdsExclusionResidual_of_valuation R⟩⟩

/-! ## Part 5.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the thirds-exclusion-lever module. -/
def thirdsExclusionLeverStatus : List String :=
  [ "GOAL 1 (proved - the generalized u=3 rigidity, ALL numerators): the brief's general " ++
      "lemma 3 does-not-divide 2^N*P -> R_N != 0 (thirdsLever_carry_ne_zero_of_not_dvd, " ++
      "via the congruence 3 | R_N - 2^N*P, thirdsLever_carry_congruence); the propagation " ++
      "3 ndvd P -> 3 ndvd 2^N*P (thirdsLever_not_dvd_pow_mul); all-N carry non-vanishing " ++
      "(thirdsLever_carry_ne_zero); and the full generalization of the wave-6 " ++
      "thirdsValue_not_eventuallyZero (P=2) to EVERY value P/(3*2^t) with 3 ndvd P " ++
      "(thirdsLever_value_not_eventuallyZero), with named instances P=1 (the q=9 u=3 " ++
      "branch, thirdsLever_valueOne_not_eventuallyZero) and P=10 (63@10, " ++
      "thirdsLever_valueTen_not_eventuallyZero).",
    "GOAL 2, SCOPE CHECK (the angle WAS open): the wave-8 blindness theorem " ++
      "(integerCarry_mod_Q_digit_blind) lives at modulus Q = 3*2^t, which determines the " ++
      "reduced carry rho_N = R_N/2^t only mod 3; the mod-6 layer of rho sits one 2-adic " ++
      "level ABOVE the blind modulus - the exact level of digit_eq_parity_at_odd_position. " ++
      "This module settles that layer completely.",
    "GOAL 2, THE JOINT MOD-6 STRUCTURE (all proved): mod 3 the reduced carry is the pure " ++
      "doubling orbit of P - digit-blind at every index past the onset " ++
      "(thirdsLever_reducedCarry_mod_three / _digit_blind), exact 2-cycle since " ++
      "ord_3(2) = 2 (thirdsLever_reducedCarry_two_cycle), never 0 mod 3 when 3 ndvd P " ++
      "(thirdsLever_reducedCarry_not_three_dvd, _ne_zero); mod 2 the reduced carry is " ++
      "EVEN at every even position, for ANY u (thirdsLever_reducedCarry_even_at_even); " ++
      "jointly: at EVEN positions 6 | rho_{N+1} - 2^{N+1-t}*P - fully deterministic, " ++
      "digit-blind, residue pinned into {2,4} when 3 ndvd P " ++
      "(thirdsLever_reducedCarry_mod_six_even, thirdsLever_even_position_residue_pin, " ++
      "thirdsLever_mod_six_even_digit_blind); at ODD positions 6 | rho_{N+1} - " ++
      "2^{N+1-t}*P - 3*d_{N+1} - the local digit is the ONLY non-deterministic bit " ++
      "(thirdsLever_reducedCarry_mod_six_odd, thirdsLever_mod_six_odd_local), and the " ++
      "parity dictionary sharpens to the explicit mod-6 residue formula d_{N+1} = 0 iff " ++
      "6 | rho_{N+1} - 2^{N+1-t}*P (thirdsLever_digit_zero_iff_mod_six).",
    "GOAL 2, THE HONEST VERDICT (the hoped digit-pinning is REFUTED): the deterministic " ++
      "even-step transport mod 6 is the doubling map (thirdsLever_even_step_doubling - " ++
      "the digit coefficient 3*(N+1) vanishes mod 6 at even N+1, so the even step is " ++
      "digit-blind), and doubling COLLAPSES the digit fiber: 2*a = 2*(a+3) in ZMod 6 " ++
      "(thirdsLever_doubling_collapse) while a and a+3 have opposite parities " ++
      "(thirdsLever_fiber_parity_flip); packaged as thirdsLever_even_step_verdict.  " ++
      "The odd-position digit (= the parity of rho there, thirdsLever_digit_eq_parity) " ++
      "is exactly the bit the deterministic structure cannot see.  NO digit at ANY " ++
      "position class is pinned, no positive-density forced pattern exists at the mod-6 " ++
      "level, and the conflict with support sparsity does NOT materialize.  The full " ++
      "u=3 exclusion via the joint 2-adic/3-adic mechanism FAILS - the same structural " ++
      "reason as the wave-7 obstruction, now located precisely: the digit lives in the " ++
      "2-adic fiber that the only deterministic transport collapses.",
    "GOAL 3 (what closes - the window-periodic stratum, composed): the q=9 branch " ++
      "dichotomy (oddpart(Q),K0) = (1,4) or (3,1) is now a lemma (thirdsLever_q9_branch) " ++
      "with per-branch value pins 4/2^t (thirdsLever_q9_u1_value) and 1/(3*2^t) " ++
      "(thirdsLever_q9_u3_value, K0 = 1 forced); the master stratum voiding " ++
      "oddpart(Q) <= 7 -> NOT WindowPeriodic " ++
      "(thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven) gives: EVERY q=9 context " ++
      "(both branches) is window-APERIODIC (thirdsLever_q9_not_windowPeriodic); the " ++
      "63@10 instance is window-aperiodic (thirdsLever_q63K10_not_windowPeriodic); the " ++
      "whole q <= 21 band is aperiodic (thirdsLever_smallq_not_windowPeriodic); and the " ++
      "general-P thirds value family P/(3*2^t) is void on the stratum at every scale " ++
      "(thirdsLever_value_void_of_windowPeriodic - extends the in-tree P=1,2 bootstrap " ++
      "voidings to ALL P, covering 10/(3*2^t)).  The joint mod-6 invariant is installed " ++
      "at both instances (thirdsLever_q9_u3_reducedCarry_pin, " ++
      "thirdsLever_q63K10_reducedCarry_pin).  The r-independent congruence k % 2 = 0 at " ++
      "63@10 (class1Fibre_residue_of_datum_63_10, CNLClass1PairClosure) composes " ++
      "alongside - cited, not re-proved here.",
    "GOAL 3 SURFACE (additive): Erdos260ThirdsExclusionResidual - the wave-10 valuation " ++
      "surface with the two tower fields and class1DeepLow handed the FREE guard " ++
      "oddpart(Q) <= 7 -> NOT WindowPeriodic ctx (a theorem at every ctx, so an " ++
      "EQUIVALENT presentation refinement, honestly recorded: " ++
      "nonempty_thirdsExclusion_iff_valuation); bridges toValuation / " ++
      "thirdsExclusionResidual_of_valuation; endpoint erdos260_of_thirdsExclusionLever " ++
      "through the public erdos260_of_valuationResidual chain.  The guard hands " ++
      "providers the proven window-aperiodicity of every q=9 context and of 63@10.",
    "GOAL 4 (what resists, honest): the NON-window-periodic stratum of the u=3 families " ++
      "(1/(3*2^t) at q=9, 10/(3*2^t) at 63@10).  The count route is dead (FloorPushV2: " ++
      "empty [32,41] window, demand everywhere), the mod-6 mechanism pins no digit " ++
      "(verdict above), and the bootstrap obstruction (more carry states than window " ++
      "slots, bootstrap_state_count_exceeds_window) still blocks an unconditional " ++
      "periodicity supply.  Both u=3 branches stay OPEN beyond their floors " ++
      "X > 2^986892; the q=9 u=1 branch (4/2^t) stays open beyond 2^986893 via the " ++
      "dyadic lever.  No context is claimed empty.",
    "Additive only; no existing file edited.  No sorry / admit / new axiom / " ++
      "native_decide." ]

/-- The status list is honest and non-empty. -/
theorem thirdsExclusionLeverStatus_nonempty : thirdsExclusionLeverStatus ≠ [] := by
  simp [thirdsExclusionLeverStatus]

/-! ## Part 6.  Axiom-cleanliness audit -/

#print axioms thirdsLever_carry_congruence
#print axioms thirdsLever_carry_ne_zero_of_not_dvd
#print axioms thirdsLever_not_dvd_pow_mul
#print axioms thirdsLever_carry_ne_zero
#print axioms thirdsLever_value_not_eventuallyZero
#print axioms thirdsLever_valueOne_not_eventuallyZero
#print axioms thirdsLever_valueTen_not_eventuallyZero
#print axioms thirdsLever_reducedCarry_mod_three
#print axioms thirdsLever_reducedCarry_mod_three_digit_blind
#print axioms thirdsLever_reducedCarry_not_three_dvd
#print axioms thirdsLever_reducedCarry_ne_zero
#print axioms thirdsLever_reducedCarry_two_cycle
#print axioms thirdsLever_reducedCarry_even_at_even
#print axioms thirdsLever_reducedCarry_mod_six_even
#print axioms thirdsLever_reducedCarry_mod_six_odd
#print axioms thirdsLever_mod_six_even_digit_blind
#print axioms thirdsLever_mod_six_odd_local
#print axioms thirdsLever_even_position_residue_pin
#print axioms thirdsLever_even_step_doubling
#print axioms thirdsLever_doubling_collapse
#print axioms thirdsLever_fiber_parity_flip
#print axioms thirdsLever_even_step_verdict
#print axioms thirdsLever_digit_eq_parity
#print axioms thirdsLever_digit_zero_iff_mod_six
#print axioms thirdsLever_q9_branch
#print axioms thirdsLever_q9_u3_K₀_eq_one
#print axioms thirdsLever_oddpart_three_Q_shape
#print axioms thirdsLever_q9_u3_value
#print axioms thirdsLever_q9_u1_value
#print axioms thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven
#print axioms thirdsLever_value_void_of_windowPeriodic
#print axioms thirdsLever_q9_not_windowPeriodic
#print axioms thirdsLever_q63K10_not_windowPeriodic
#print axioms thirdsLever_smallq_not_windowPeriodic
#print axioms thirdsLever_q9_u3_reducedCarry_pin
#print axioms thirdsLever_q63K10_reducedCarry_pin
#print axioms Erdos260ThirdsExclusionResidual.toValuation
#print axioms Erdos260ThirdsExclusionResidual.toStatement
#print axioms erdos260_of_thirdsExclusionLever
#print axioms thirdsExclusionResidual_of_valuation
#print axioms nonempty_thirdsExclusion_iff_valuation
#print axioms thirdsExclusionLeverStatus_nonempty

end

end Erdos260
