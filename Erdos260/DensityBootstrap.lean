import Erdos260.CarryWordRigidity
import Erdos260.Periodic

/-!
# The density bootstrap: section 24 fixed-density periodic repetition against the actual carry

This module (NEW; it edits no existing file) formalizes the manuscript's density-bootstrap
mechanism (sections 24.1/24.2, 25.2, Appendix H.4/H.5 of `proof_v4_unconditional_clean_v5.tex`)
at the level of the ACTUAL weighted carry recursion `R_{N+1} = 2*R_N - Q*(N+1)*d_{N+1}` of a
failing shell, and determines exactly how far it closes the deep tail left open by wave 6
(`CarryWordRigidity`: every pinned-value context needs `X > 2^493443`, and beyond that floor
the single-scale rigidity density `~1/(L+4)` drops below `c0 = 17/16777216`).

## Part 1: the weighted periodic-tail identity (the 24.2 engine, derived NOT assumed)

If the digit word is `p`-periodic after an onset `x` (`d (n+p) = d n` for `n > x`) and the
weighted value is rational `P/Q`, then the carry at the onset is PINNED exactly:

  `(2^p - 1)^2 * R_x = Q * ((2^p - 1)*(x*M + J) + p*M)`      (`periodicTail_carry_identity`)

where `M`/`J` are the plain/weighted big-endian masks of one period window.  The proof is
fully discrete: the carry recursion summed over one period gives the affine map
`S_{k+1} = 2^p*S_k - Q*((x+kp)M + J)` (`integerCarry_add_bootBlock` + `bootBlock_shift`), the
deviation `T_k = D^2*S_k - Q*(D*((x+kp)M+J) + pM)` transports EXACTLY by `T_{k+1} = 2^p*T_k`,
and the two-sided carry bound `0 <= R_N <= Q(N+2)` (`integerCarry_bounds_of_rational_value`)
forces `T_0 = 0`, since `2^{pk}` beats every affine envelope
(`carryWord_exists_mul_add_lt_two_pow`).

Reducing mod `D = 2^p - 1` kills the head and the `J`-term: `D | Q*p*M`
(`periodicTail_dvd_Qp`), and since `D` is odd the ENTIRE 2-part of `Q = u*2^t` cancels:

  `(2^p - 1) | u * p * M`                                     (`periodicTail_dvd_oddpart`)

so for the pinned families (`u` in `{1,3,5,7}`) the effective 24.2 modulus is the tiny odd
part `u`, NOT `Q`.  This is the exact formal relation between `shell_value_eq_K₀_div_Q` and
the manuscript's section 24: the 24.1 plain doubling orbit does NOT run on the weighted carry
(wave 6: digits are invisible mod `u` in the weighted recursion) -- it runs on the ROTATION
MASKS of an exactly-periodic tail, which the weighted value reaches only THROUGH the identity
above.

## Part 2: the 24.1 orbit bound, ord-free (minimal period gives rotation injectivity)

For the rotation masks `M_j` of the period window the binary-division step is exact and
deterministic: `2*M_j = d(x+j+1)*D + M_{j+1}` with `M_{j+1} < D` (`bootRot_step`,
`bootStep_unique` -- the forward determinism of the periodic state, the discrete answer to
the "backward/forward determinism" question).  If `p` is the MINIMAL period (over all
onsets), the `p` rotation masks are pairwise DISTINCT (`bootRot_injOn_of_min`: a collision
propagates to a strictly smaller period), all positive multiples of `g = gcd(D, M_0)`, and
they sum to `D*k0` (`bootRot_sum`, `k0` = ones per period).  Distinct positive multiples give
the triangular bound, and `q = D/g | u*p` from Part 1, hence THE DENSITY FLOOR, scale-free
and `t`-free:

  `p + 1 <= 2*u*k0`                                           (`minimalPeriod_ones_floor`)

so one period of ANY eventually-periodic realization of a pinned value `P/(u*2^t)` carries
ones density `> 1/(2u) >= 1/14`, massively above `c0 = 17/16777216`.  (The manuscript 24.2
floor `1/(3Q)` is sharpened to `1/(2u)`; the all-ones / terminating degenerate cases are
handled by `hnonterm` directly.)

## Part 3: the window count and the per-family voidings (every scale, no 2^493443 floor)

A `p`-periodic tail with onset `x <= X` puts `>= (X/p)*k0` ones in the shell `(X, 2X]`
(`periodic_supportShell_card_lower`), so for a pinned-value context with window periodicity
(`WindowPeriodic`: onset `<= X`, period `<= X/2`) the support count is `>= ~X/(4u) >= X/28`,
contradicting `hfailure : card < (17/16777216)*X` at EVERY scale `X >= 2`
(`pinnedValue_windowPeriodic_void`).  Voidings: `shellValueDyadic_void_of_windowPeriodic`,
`towerFifthValue_void_of_windowPeriodic`, `towerThirdsValue_void_of_windowPeriodic`,
`fixedFamilyHit_void_of_windowPeriodic` plus the five per-family forms.

## Part 4: what resists, exactly, and the sharpened successors

The bootstrap does NOT close the pinned families outright, for two honest reasons:

* the bounded-state pigeonhole FAILS: the formalized carry bound is `R_N <= Q(N+2)`
  (GROWING with `N`); even after dividing by the forced `2^t` factor the state count on the
  window `(X, 2X]` is `~u*(2X+2) > X` -- more states than slots for every `u >= 1`
  (`bootstrap_state_count_exceeds_window`); and
* the weighted recursion is non-autonomous: the step coefficient `Q*(N+1)` moves with `N`,
  so a bare carry repeat does not propagate periodicity (the digit is recovered from the
  carry PAIR, `integerCarry_digit_recover`, not from the single carry value); the genuinely
  autonomous state is the real unweighted tail, which has no finite state space.

Hence eventual periodicity of the failing word is the irreducible residual input.  The
sharpened deep successors demand it ONLY at `X > 2^493443` and only with window-compatible
onset/period: `DeepDyadicWindowPeriodicity`, `DeepFifthWindowPeriodicity`,
`DeepThirdsWindowPeriodicity`, `DeepFixedFamilyWindowPeriodicity`, discharging the full
wave-5 levers (`dyadicValueLever_of_windowPeriodicity`,
`towerFifthValueLever_of_windowPeriodicity`, `towerThirdsValueLever_of_windowPeriodicity`,
`fixedFamilyHit_void_of_windowPeriodicity`) and the endpoint
`erdos260_of_dyadicWindowPeriodicity`.

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 0.  The period-window masks -/

/-- Big-endian plain mask of the period window `(x, x+p]`: the sum of `2^i * d (x + (p-i))`
over `i < p` (the first digit after the onset is the most significant bit). -/
def bootMask (d : ℕ → ℕ) (x p : ℕ) : ℕ :=
  ∑ i ∈ Finset.range p, 2 ^ i * d (x + (p - i))

/-- Big-endian weighted mask of the period window: the sum of `2^i * (p-i) * d (x + (p-i))`. -/
def bootWeight (d : ℕ → ℕ) (x p : ℕ) : ℕ :=
  ∑ i ∈ Finset.range p, 2 ^ i * (p - i) * d (x + (p - i))

/-- Number of ones in the period window `(x, x+p]`. -/
def bootOnes (d : ℕ → ℕ) (x p : ℕ) : ℕ :=
  ∑ j ∈ Finset.range p, d (x + j + 1)

/-- The `j`-th rotation mask: the big-endian mask of the shifted window `(x+j, x+j+p]`. -/
def bootRot (d : ℕ → ℕ) (x p j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range p, 2 ^ i * d (x + j + (p - i))

theorem bootRot_zero (d : ℕ → ℕ) (x p : ℕ) : bootRot d x p 0 = bootMask d x p := by
  unfold bootRot bootMask
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : x + 0 + (p - i) = x + (p - i) := by omega
  rw [h]

theorem bootMask_le {d : ℕ → ℕ} (hd : BinaryDigits d) (x p : ℕ) :
    bootMask d x p ≤ periodDen p := by
  unfold bootMask
  calc (∑ i ∈ Finset.range p, 2 ^ i * d (x + (p - i)))
      ≤ ∑ i ∈ Finset.range p, 2 ^ i := by
        refine Finset.sum_le_sum fun i _ => ?_
        rcases hd (x + (p - i)) with h | h <;> simp [h]
    _ = periodDen p := sum_range_two_pow_eq_periodDen p

theorem bootWeight_le {d : ℕ → ℕ} (hd : BinaryDigits d) (x p : ℕ) :
    bootWeight d x p ≤ p * periodDen p := by
  unfold bootWeight
  calc (∑ i ∈ Finset.range p, 2 ^ i * (p - i) * d (x + (p - i)))
      ≤ ∑ i ∈ Finset.range p, p * 2 ^ i := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : p - i ≤ p := by omega
        have h2 : d (x + (p - i)) ≤ 1 := by rcases hd (x + (p - i)) with h | h <;> omega
        calc 2 ^ i * (p - i) * d (x + (p - i))
            ≤ 2 ^ i * p * 1 := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
          _ = p * 2 ^ i := by ring
    _ = p * ∑ i ∈ Finset.range p, 2 ^ i := by rw [Finset.mul_sum]
    _ = p * periodDen p := by rw [sum_range_two_pow_eq_periodDen]

theorem bootMask_cast (d : ℕ → ℕ) (x p : ℕ) :
    ((bootMask d x p : ℕ) : ℤ)
      = ∑ i ∈ Finset.range p, (2 : ℤ) ^ i * (d (x + (p - i)) : ℤ) := by
  unfold bootMask
  push_cast
  rfl

theorem bootWeight_cast (d : ℕ → ℕ) (x p : ℕ) :
    ((bootWeight d x p : ℕ) : ℤ)
      = ∑ i ∈ Finset.range p, (2 : ℤ) ^ i * ((p - i : ℕ) : ℤ) * (d (x + (p - i)) : ℤ) := by
  unfold bootWeight
  push_cast
  rfl

/-- Periodicity transports along multiples of the period (onset form). -/
theorem boot_digit_add_mul {d : ℕ → ℕ} {x p : ℕ}
    (hper : ∀ n, x < n → d (n + p) = d n) :
    ∀ (k n : ℕ), x < n → d (n + p * k) = d n := by
  intro k
  induction k with
  | zero => intro n _; simp
  | succ k ih =>
      intro n hn
      have hidx : n + p * (k + 1) = (n + p * k) + p := by ring
      rw [hidx, hper (n + p * k) (by omega), ih n hn]

/-! ## Part 1.  The weighted periodic-tail identity -/

/-- The position-weighted digit sum of the block `(x, x+m]`, with the doubling weights. -/
def bootBlock (d : ℕ → ℕ) (x m : ℕ) : ℤ :=
  ∑ i ∈ Finset.range m, (2 : ℤ) ^ i * ((x + (m - i) : ℕ) : ℤ) * (d (x + (m - i)) : ℤ)

theorem bootBlock_succ (d : ℕ → ℕ) (x m : ℕ) :
    bootBlock d x (m + 1)
      = 2 * bootBlock d x m + ((x + m + 1 : ℕ) : ℤ) * (d (x + m + 1) : ℤ) := by
  unfold bootBlock
  rw [Finset.sum_range_succ'
    (fun i => (2 : ℤ) ^ i * ((x + (m + 1 - i) : ℕ) : ℤ) * (d (x + (m + 1 - i)) : ℤ)) m]
  have hterm : ∀ i ∈ Finset.range m,
      (2 : ℤ) ^ (i + 1) * ((x + (m + 1 - (i + 1)) : ℕ) : ℤ)
          * (d (x + (m + 1 - (i + 1))) : ℤ)
        = 2 * ((2 : ℤ) ^ i * ((x + (m - i) : ℕ) : ℤ) * (d (x + (m - i)) : ℤ)) := by
    intro i hi
    have h : m + 1 - (i + 1) = m - i := by omega
    rw [h, pow_succ]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have h0 : m + 1 - 0 = m + 1 := by omega
  rw [h0]
  push_cast
  ring

/-- The carry across an arbitrary block: `R_{x+m} = 2^m * R_x - Q * B(x,m)`. -/
theorem integerCarry_add_bootBlock (Q : ℕ) (P : ℤ) (d : ℕ → ℕ) (x : ℕ) :
    ∀ m : ℕ, integerCarry Q P d (x + m)
      = 2 ^ m * integerCarry Q P d x - (Q : ℤ) * bootBlock d x m := by
  intro m
  induction m with
  | zero => simp [bootBlock]
  | succ m ih =>
      have hidx : x + (m + 1) = (x + m) + 1 := by omega
      rw [hidx, integerCarry_succ, ih, bootBlock_succ]
      push_cast
      ring

/-- On a periodic tail the block sum at the `k`-th period start splits through the masks of
the BASE window: `B(x+kp, p) = (x+kp)*M + J`. -/
theorem bootBlock_shift {d : ℕ → ℕ} {x p : ℕ}
    (hper : ∀ n, x < n → d (n + p) = d n) (k : ℕ) :
    bootBlock d (x + k * p) p
      = ((x + k * p : ℕ) : ℤ) * (bootMask d x p : ℤ) + (bootWeight d x p : ℤ) := by
  unfold bootBlock
  have hterm : ∀ i ∈ Finset.range p,
      (2 : ℤ) ^ i * ((x + k * p + (p - i) : ℕ) : ℤ) * (d (x + k * p + (p - i)) : ℤ)
        = ((x + k * p : ℕ) : ℤ) * ((2 : ℤ) ^ i * (d (x + (p - i)) : ℤ))
          + (2 : ℤ) ^ i * ((p - i : ℕ) : ℤ) * (d (x + (p - i)) : ℤ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hc : k * p = p * k := Nat.mul_comm k p
    have harg : x + k * p + (p - i) = (x + (p - i)) + p * k := by omega
    have hdig : d (x + k * p + (p - i)) = d (x + (p - i)) := by
      rw [harg]
      exact boot_digit_add_mul hper k _ (by omega)
    rw [hdig]
    have hcast : ((x + k * p + (p - i) : ℕ) : ℤ)
        = ((x + k * p : ℕ) : ℤ) + ((p - i : ℕ) : ℤ) := by push_cast; ring
    rw [hcast]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
    bootMask_cast, bootWeight_cast]

set_option maxHeartbeats 1200000 in
/-- **THE WEIGHTED PERIODIC-TAIL IDENTITY** (the 24.2 engine, derived from the carry):
if the digit word is `p`-periodic after `x` and the weighted value is `P/Q`, then
`(2^p - 1)^2 * R_x = Q*((2^p - 1)*(x*M + J) + p*M)` with `M`/`J` the plain/weighted masks of
the base period window.  Fully discrete: the deviation transports by `T_{k+1} = 2^p * T_k`
while the carry bounds keep it affine in `k`. -/
theorem periodicTail_carry_identity {Q : ℕ} {P : ℤ} {d : ℕ → ℕ} {x p : ℕ}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hp : 0 < p) (hper : ∀ n, x < n → d (n + p) = d n) :
    (periodDen p : ℤ) ^ 2 * integerCarry Q P d x
      = (Q : ℤ) * ((periodDen p : ℤ)
            * ((x : ℤ) * (bootMask d x p : ℤ) + (bootWeight d x p : ℤ))
          + (p : ℤ) * (bootMask d x p : ℤ)) := by
  classical
  set M : ℤ := (bootMask d x p : ℤ) with hMdef
  set J : ℤ := (bootWeight d x p : ℤ) with hJdef
  set Dz : ℤ := (periodDen p : ℤ) with hDdef
  have hnat : periodDen p + 1 = 2 ^ p := by
    have h1 : 1 ≤ 2 ^ p := Nat.one_le_pow p 2 (by norm_num)
    unfold periodDen
    omega
  have h2pD : (2 : ℤ) ^ p = Dz + 1 := by
    rw [hDdef]
    exact_mod_cast hnat.symm
  have hSrec : ∀ k : ℕ,
      integerCarry Q P d (x + (k + 1) * p)
        = (Dz + 1) * integerCarry Q P d (x + k * p)
          - (Q : ℤ) * (((x + k * p : ℕ) : ℤ) * M + J) := by
    intro k
    have hidx : x + (k + 1) * p = (x + k * p) + p := by ring
    rw [hidx, integerCarry_add_bootBlock Q P d (x + k * p) p, bootBlock_shift hper k, h2pD]
  set R0 : ℤ := Dz ^ 2 * integerCarry Q P d x
      - (Q : ℤ) * (Dz * ((x : ℤ) * M + J) + (p : ℤ) * M) with hR0
  have key : ∀ k : ℕ,
      Dz ^ 2 * integerCarry Q P d (x + k * p)
          - (Q : ℤ) * (Dz * (((x + k * p : ℕ) : ℤ) * M + J) + (p : ℤ) * M)
        = (Dz + 1) ^ k * R0 := by
    intro k
    induction k with
    | zero => simp [hR0]
    | succ k ih =>
        have hidxc : ((x + (k + 1) * p : ℕ) : ℤ) = ((x + k * p : ℕ) : ℤ) + (p : ℤ) := by
          push_cast; ring
        calc Dz ^ 2 * integerCarry Q P d (x + (k + 1) * p)
              - (Q : ℤ) * (Dz * (((x + (k + 1) * p : ℕ) : ℤ) * M + J) + (p : ℤ) * M)
            = (Dz + 1) * (Dz ^ 2 * integerCarry Q P d (x + k * p)
                - (Q : ℤ) * (Dz * (((x + k * p : ℕ) : ℤ) * M + J) + (p : ℤ) * M)) := by
              rw [hSrec k, hidxc]; ring
          _ = (Dz + 1) * ((Dz + 1) ^ k * R0) := by rw [ih]
          _ = (Dz + 1) ^ (k + 1) * R0 := by rw [pow_succ]; ring
  suffices hzero : R0 = 0 by
    have h := hzero
    rw [hR0] at h
    linarith
  by_contra hne
  set a : ℕ := Q * periodDen p ^ 2 * (x + 3 * p + 2) with ha
  obtain ⟨h, hh⟩ := carryWord_exists_mul_add_lt_two_pow a 1
  have hkeyh := key h
  set B : ℤ := ((x + h * p : ℕ) : ℤ) with hBdef
  have hSb := integerCarry_bounds_of_rational_value (Q := Q) (P := P) (d := d)
    (x + h * p) hQ hd heta
  have hM0 : (0 : ℤ) ≤ M := by rw [hMdef]; exact Int.natCast_nonneg _
  have hJ0 : (0 : ℤ) ≤ J := by rw [hJdef]; exact Int.natCast_nonneg _
  have hD1 : (1 : ℤ) ≤ Dz := by
    rw [hDdef]
    exact_mod_cast periodDen_pos hp
  have hDz0 : (0 : ℤ) ≤ Dz := by linarith
  have hB0 : (0 : ℤ) ≤ B := by rw [hBdef]; exact Int.natCast_nonneg _
  have hMle : M ≤ Dz := by rw [hMdef, hDdef]; exact_mod_cast bootMask_le hd x p
  have hJle : J ≤ (p : ℤ) * Dz := by
    rw [hJdef, hDdef]
    exact_mod_cast bootWeight_le hd x p
  have hQn : (0 : ℤ) ≤ (Q : ℤ) := Int.natCast_nonneg _
  have hacast : (a : ℤ) = (Q : ℤ) * Dz ^ 2 * ((x + 3 * p + 2 : ℕ) : ℤ) := by
    rw [ha, hDdef]
    push_cast
    ring
  have hW0 : (0 : ℤ) ≤ (Q : ℤ) * (Dz * (B * M + J) + (p : ℤ) * M) := by
    have t1 : (0 : ℤ) ≤ B * M := mul_nonneg hB0 hM0
    have t2 : (0 : ℤ) ≤ B * M + J := by linarith
    have t3 : (0 : ℤ) ≤ Dz * (B * M + J) := mul_nonneg hDz0 t2
    have t4 : (0 : ℤ) ≤ (p : ℤ) * M := mul_nonneg (Int.natCast_nonneg _) hM0
    exact mul_nonneg hQn (by linarith)
  have hcoefN : x + h * p + 2 ≤ (x + 3 * p + 2) * (1 + h) := by
    have h1 : h * p ≤ h * (x + 3 * p + 2) := Nat.mul_le_mul_left h (by omega)
    have h2 : (x + 3 * p + 2) * (1 + h) = (x + 3 * p + 2) + (x + 3 * p + 2) * h := by ring
    have h3 : h * (x + 3 * p + 2) = (x + 3 * p + 2) * h := Nat.mul_comm _ _
    omega
  have hcoefZ : ((x + h * p + 2 : ℕ) : ℤ) ≤ ((x + 3 * p + 2 : ℕ) : ℤ) * (1 + (h : ℤ)) := by
    exact_mod_cast hcoefN
  have hQDz : (0 : ℤ) ≤ (Q : ℤ) * Dz ^ 2 := mul_nonneg hQn (by positivity)
  have hub : Dz ^ 2 * integerCarry Q P d (x + h * p)
      - (Q : ℤ) * (Dz * (B * M + J) + (p : ℤ) * M) ≤ (a : ℤ) * (1 + (h : ℤ)) := by
    have hs1 : Dz ^ 2 * integerCarry Q P d (x + h * p)
        ≤ Dz ^ 2 * ((Q : ℤ) * ((x + h * p + 2 : ℕ) : ℤ)) :=
      mul_le_mul_of_nonneg_left hSb.2 (by positivity)
    have hs2 : Dz ^ 2 * ((Q : ℤ) * ((x + h * p + 2 : ℕ) : ℤ))
        ≤ (a : ℤ) * (1 + (h : ℤ)) := by
      calc Dz ^ 2 * ((Q : ℤ) * ((x + h * p + 2 : ℕ) : ℤ))
          = (Q : ℤ) * Dz ^ 2 * ((x + h * p + 2 : ℕ) : ℤ) := by ring
        _ ≤ (Q : ℤ) * Dz ^ 2 * (((x + 3 * p + 2 : ℕ) : ℤ) * (1 + (h : ℤ))) :=
            mul_le_mul_of_nonneg_left hcoefZ hQDz
        _ = (a : ℤ) * (1 + (h : ℤ)) := by rw [hacast]; ring
    linarith
  have hlb : -(Dz ^ 2 * integerCarry Q P d (x + h * p)
      - (Q : ℤ) * (Dz * (B * M + J) + (p : ℤ) * M)) ≤ (a : ℤ) * (1 + (h : ℤ)) := by
    have hS0 : (0 : ℤ) ≤ integerCarry Q P d (x + h * p) := hSb.1
    have hDS : (0 : ℤ) ≤ Dz ^ 2 * integerCarry Q P d (x + h * p) :=
      mul_nonneg (by positivity) hS0
    have hBDz : B * M ≤ B * Dz := mul_le_mul_of_nonneg_left hMle hB0
    have hsum1 : B * M + J ≤ B * Dz + (p : ℤ) * Dz := add_le_add hBDz hJle
    have hm1 : Dz * (B * M + J) ≤ Dz * (B * Dz + (p : ℤ) * Dz) :=
      mul_le_mul_of_nonneg_left hsum1 hDz0
    have hpM : (p : ℤ) * M ≤ (p : ℤ) * Dz :=
      mul_le_mul_of_nonneg_left hMle (Int.natCast_nonneg _)
    have hWle : (Q : ℤ) * (Dz * (B * M + J) + (p : ℤ) * M)
        ≤ (Q : ℤ) * (Dz * (B * Dz + (p : ℤ) * Dz) + (p : ℤ) * Dz) :=
      mul_le_mul_of_nonneg_left (by linarith) hQn
    have hDzsq : (p : ℤ) * Dz ≤ (p : ℤ) * Dz ^ 2 := by
      have h1 : Dz * 1 ≤ Dz * Dz := mul_le_mul_of_nonneg_left hD1 hDz0
      have h3 : Dz ≤ Dz ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left h3 (Int.natCast_nonneg _)
    have hcoefN2 : x + h * p + 2 * p ≤ (x + 3 * p + 2) * (1 + h) := by
      have h1 : h * p ≤ h * (x + 3 * p + 2) := Nat.mul_le_mul_left h (by omega)
      have h2 : (x + 3 * p + 2) * (1 + h) = (x + 3 * p + 2) + (x + 3 * p + 2) * h := by ring
      have h3 : h * (x + 3 * p + 2) = (x + 3 * p + 2) * h := Nat.mul_comm _ _
      omega
    have hcoefZ2 : B + 2 * (p : ℤ) ≤ ((x + 3 * p + 2 : ℕ) : ℤ) * (1 + (h : ℤ)) := by
      rw [hBdef]
      exact_mod_cast hcoefN2
    have hfin : (Q : ℤ) * (Dz * (B * Dz + (p : ℤ) * Dz) + (p : ℤ) * Dz)
        ≤ (a : ℤ) * (1 + (h : ℤ)) := by
      calc (Q : ℤ) * (Dz * (B * Dz + (p : ℤ) * Dz) + (p : ℤ) * Dz)
          ≤ (Q : ℤ) * (Dz * (B * Dz + (p : ℤ) * Dz) + (p : ℤ) * Dz ^ 2) := by
            have h0 : Dz * (B * Dz + (p : ℤ) * Dz) + (p : ℤ) * Dz
                ≤ Dz * (B * Dz + (p : ℤ) * Dz) + (p : ℤ) * Dz ^ 2 := by linarith
            exact mul_le_mul_of_nonneg_left h0 hQn
        _ = (Q : ℤ) * Dz ^ 2 * (B + 2 * (p : ℤ)) := by ring
        _ ≤ (Q : ℤ) * Dz ^ 2 * (((x + 3 * p + 2 : ℕ) : ℤ) * (1 + (h : ℤ))) :=
            mul_le_mul_of_nonneg_left hcoefZ2 hQDz
        _ = (a : ℤ) * (1 + (h : ℤ)) := by rw [hacast]; ring
    linarith
  have h2p2 : (2 : ℕ) ≤ 2 ^ p := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
  have hpowN : (2 : ℕ) ^ h ≤ (2 ^ p) ^ h := Nat.pow_le_pow_left h2p2 h
  have hpow : (2 : ℤ) ^ h ≤ (Dz + 1) ^ h := by
    rw [← h2pD]
    exact_mod_cast hpowN
  have hp2 : (0 : ℤ) ≤ (Dz + 1) ^ h := pow_nonneg (by linarith) h
  have hhZ : (a : ℤ) * (1 + (h : ℤ)) < (2 : ℤ) ^ h := by exact_mod_cast hh
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h1R : (1 : ℤ) ≤ -R0 := by omega
    have h2R : (2 : ℤ) ^ h ≤ (Dz + 1) ^ h * (-R0) := by
      calc (2 : ℤ) ^ h = (2 : ℤ) ^ h * 1 := by ring
        _ ≤ (Dz + 1) ^ h * (-R0) := mul_le_mul hpow h1R (by norm_num) hp2
    have h3R : (Dz + 1) ^ h * (-R0)
        = -(Dz ^ 2 * integerCarry Q P d (x + h * p)
            - (Q : ℤ) * (Dz * (B * M + J) + (p : ℤ) * M)) := by
      rw [hkeyh]; ring
    rw [h3R] at h2R
    linarith
  · have h1R : (1 : ℤ) ≤ R0 := by omega
    have h2R : (2 : ℤ) ^ h ≤ (Dz + 1) ^ h * R0 := by
      calc (2 : ℤ) ^ h = (2 : ℤ) ^ h * 1 := by ring
        _ ≤ (Dz + 1) ^ h * R0 := mul_le_mul hpow h1R (by norm_num) hp2
    rw [← hkeyh] at h2R
    linarith

/-- **The 24.2 divisibility, derived**: a `p`-periodic tail of a rational weighted value
`P/Q` forces `(2^p - 1) | Q*p*M`. -/
theorem periodicTail_dvd_Qp {Q : ℕ} {P : ℤ} {d : ℕ → ℕ} {x p : ℕ}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hp : 0 < p) (hper : ∀ n, x < n → d (n + p) = d n) :
    periodDen p ∣ Q * p * bootMask d x p := by
  have hid := periodicTail_carry_identity hQ hd heta hp hper
  have hdvdZ : (periodDen p : ℤ) ∣ (Q : ℤ) * (p : ℤ) * (bootMask d x p : ℤ) := by
    refine ⟨(periodDen p : ℤ) * integerCarry Q P d x
      - (Q : ℤ) * ((x : ℤ) * (bootMask d x p : ℤ) + (bootWeight d x p : ℤ)), ?_⟩
    linear_combination -hid
  have hcast : ((periodDen p : ℕ) : ℤ) ∣ ((Q * p * bootMask d x p : ℕ) : ℤ) := by
    push_cast
    exact hdvdZ
  exact_mod_cast hcast

/-- **The 2-adic sharpening** (the heart of the pinned-family bootstrap): for `Q = u*2^t` the
ENTIRE 2-power cancels against the odd `2^p - 1`, leaving `(2^p - 1) | u*p*M`. -/
theorem periodicTail_dvd_oddpart {Q u t : ℕ} {P : ℤ} {d : ℕ → ℕ} {x p : ℕ}
    (hQfact : Q = u * 2 ^ t) (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hp : 0 < p) (hper : ∀ n, x < n → d (n + p) = d n) :
    periodDen p ∣ u * p * bootMask d x p := by
  have h1 := periodicTail_dvd_Qp (P := P) hQ hd heta hp hper
  rw [hQfact] at h1
  have h2 : u * 2 ^ t * p * bootMask d x p = 2 ^ t * (u * p * bootMask d x p) := by ring
  rw [h2] at h1
  have h2p : (2 : ℕ) ^ p = 2 * 2 ^ (p - 1) := by
    conv_lhs => rw [show p = (p - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have h1le : 1 ≤ 2 ^ (p - 1) := Nat.one_le_pow _ 2 (by norm_num)
  have hmod : periodDen p % 2 = 1 := by
    unfold periodDen
    omega
  have hnd : ¬ (2 ∣ periodDen p) := by omega
  have hc2 : Nat.Coprime 2 (periodDen p) := (Nat.prime_two.coprime_iff_not_dvd).mpr hnd
  have hcop : Nat.Coprime (periodDen p) (2 ^ t) := (hc2.symm).pow_right t
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop h1

/-! ## Part 2.  The rotation orbit: determinism, injectivity, and the density floor -/

/-- **The exact binary-division step on rotation masks**:
`2*M_j + d(x+j+1) = M_{j+1} + 2^p * d(x+j+1)`, i.e. `2*M_j = d(x+j+1)*(2^p-1) + M_{j+1}`. -/
theorem bootRot_step {d : ℕ → ℕ} {x p : ℕ} (hp : 0 < p)
    (hper : ∀ n, x < n → d (n + p) = d n) (j : ℕ) :
    2 * bootRot d x p j + d (x + j + 1)
      = bootRot d x p (j + 1) + 2 ^ p * d (x + j + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  have h1 : bootRot d x (m + 1) j
      = (∑ i ∈ Finset.range m, 2 ^ i * d (x + j + 1 + (m - i)))
        + 2 ^ m * d (x + j + 1) := by
    unfold bootRot
    rw [Finset.sum_range_succ (fun i => 2 ^ i * d (x + j + (m + 1 - i))) m]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      have hidx : x + j + (m + 1 - i) = x + j + 1 + (m - i) := by omega
      rw [hidx]
    · have hidx : x + j + (m + 1 - m) = x + j + 1 := by omega
      rw [hidx]
  have h2 : bootRot d x (m + 1) (j + 1)
      = 2 * (∑ i ∈ Finset.range m, 2 ^ i * d (x + j + 1 + (m - i))) + d (x + j + 1) := by
    unfold bootRot
    rw [Finset.sum_range_succ' (fun i => 2 ^ i * d (x + (j + 1) + (m + 1 - i))) m]
    have hlast : 2 ^ 0 * d (x + (j + 1) + (m + 1 - 0)) = d (x + j + 1) := by
      have hidx : x + (j + 1) + (m + 1 - 0) = (x + j + 1) + (m + 1) := by omega
      rw [hidx, hper (x + j + 1) (by omega)]
      ring
    rw [hlast]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hidx : x + (j + 1) + (m + 1 - (i + 1)) = x + j + 1 + (m - i) := by omega
    rw [hidx, pow_succ]
    ring
  rw [h1, h2, pow_succ]
  ring

/-- Rotation masks repeat with the period. -/
theorem bootRot_periodic {d : ℕ → ℕ} {x p : ℕ}
    (hper : ∀ n, x < n → d (n + p) = d n) (j : ℕ) :
    bootRot d x p (j + p) = bootRot d x p j := by
  unfold bootRot
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hidx : x + (j + p) + (p - i) = (x + j + (p - i)) + p := by omega
  rw [hidx, hper (x + j + (p - i)) (by omega)]

/-- The rotation masks over one period sum to `(2^p - 1) * k0` (`k0` = ones per period). -/
theorem bootRot_sum {d : ℕ → ℕ} {x p : ℕ} (hp : 0 < p)
    (hper : ∀ n, x < n → d (n + p) = d n) :
    ∑ j ∈ Finset.range p, bootRot d x p j = periodDen p * bootOnes d x p := by
  have hnat : periodDen p + 1 = 2 ^ p := by
    have h1 : 1 ≤ 2 ^ p := Nat.one_le_pow p 2 (by norm_num)
    unfold periodDen
    omega
  have hsumC : ∑ j ∈ Finset.range p, (2 * bootRot d x p j + d (x + j + 1))
      = ∑ j ∈ Finset.range p, (bootRot d x p (j + 1) + 2 ^ p * d (x + j + 1)) :=
    Finset.sum_congr rfl fun j _ => bootRot_step hp hper j
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    at hsumC
  have hshift : ∑ j ∈ Finset.range p, bootRot d x p (j + 1)
      = ∑ j ∈ Finset.range p, bootRot d x p j := by
    have e1 := Finset.sum_range_succ (fun j => bootRot d x p j) p
    have e2 := Finset.sum_range_succ' (fun j => bootRot d x p j) p
    have e3 : bootRot d x p (0 + p) = bootRot d x p 0 := bootRot_periodic hper 0
    simp only [Nat.zero_add] at e3
    omega
  rw [hshift] at hsumC
  have hexp : 2 ^ p * (∑ j ∈ Finset.range p, d (x + j + 1))
      = periodDen p * (∑ j ∈ Finset.range p, d (x + j + 1))
        + (∑ j ∈ Finset.range p, d (x + j + 1)) := by
    rw [← hnat]; ring
  unfold bootOnes
  omega

/-- Existence of any prescribed digit value somewhere in EVERY rotated window, transported
along the orbit from one witness in the base window. -/
theorem boot_exists_digit {d : ℕ → ℕ} {x p : ℕ} (hp : 0 < p)
    (hper : ∀ n, x < n → d (n + p) = d n) {v i₀ : ℕ}
    (h1 : 1 ≤ i₀) (h2 : i₀ ≤ p) (hv : d (x + i₀) = v) (j : ℕ) :
    ∃ s, 1 ≤ s ∧ s ≤ p ∧ d (x + j + s) = v := by
  have hdm : p * (j / p) + j % p = j := Nat.div_add_mod j p
  have hmod : j % p < p := Nat.mod_lt _ hp
  rcases Nat.lt_or_ge (j % p) i₀ with h | h
  · refine ⟨i₀ - j % p, by omega, by omega, ?_⟩
    have hidx : x + j + (i₀ - j % p) = (x + i₀) + p * (j / p) := by omega
    rw [hidx, boot_digit_add_mul hper _ _ (by omega)]
    exact hv
  · refine ⟨i₀ + p - j % p, by omega, by omega, ?_⟩
    have hmul : p * (j / p + 1) = p * (j / p) + p := by ring
    have hidx : x + j + (i₀ + p - j % p) = (x + i₀) + p * (j / p + 1) := by omega
    rw [hidx, boot_digit_add_mul hper _ _ (by omega)]
    exact hv

/-- Every rotation mask is positive once the base window has a one. -/
theorem bootRot_pos {d : ℕ → ℕ} {x p : ℕ} (hp : 0 < p)
    (hper : ∀ n, x < n → d (n + p) = d n) {i₀ : ℕ}
    (h1 : 1 ≤ i₀) (h2 : i₀ ≤ p) (hv : d (x + i₀) = 1) (j : ℕ) :
    1 ≤ bootRot d x p j := by
  obtain ⟨s, hs1, hsp, hds⟩ := boot_exists_digit hp hper h1 h2 hv j
  have hmem : p - s ∈ Finset.range p := Finset.mem_range.mpr (by omega)
  have hterm : 1 ≤ 2 ^ (p - s) * d (x + j + (p - (p - s))) := by
    have hps : p - (p - s) = s := by omega
    rw [hps, hds]
    have hpow : 1 ≤ 2 ^ (p - s) := Nat.one_le_pow _ 2 (by norm_num)
    omega
  calc 1 ≤ 2 ^ (p - s) * d (x + j + (p - (p - s))) := hterm
    _ ≤ ∑ i ∈ Finset.range p, 2 ^ i * d (x + j + (p - i)) :=
        Finset.single_le_sum (f := fun i => 2 ^ i * d (x + j + (p - i)))
          (fun i _ => Nat.zero_le _) hmem
    _ = bootRot d x p j := rfl

/-- Every rotation mask stays strictly below `2^p - 1` once the base window has a zero. -/
theorem bootRot_lt {d : ℕ → ℕ} {x p : ℕ} (hd : BinaryDigits d) (hp : 0 < p)
    (hper : ∀ n, x < n → d (n + p) = d n) {i₀ : ℕ}
    (h1 : 1 ≤ i₀) (h2 : i₀ ≤ p) (hv : d (x + i₀) = 0) (j : ℕ) :
    bootRot d x p j < periodDen p := by
  obtain ⟨s, hs1, hsp, hds⟩ := boot_exists_digit hp hper h1 h2 hv j
  have hmem : p - s ∈ Finset.range p := Finset.mem_range.mpr (by omega)
  have hzero_term : 2 ^ (p - s) * d (x + j + (p - (p - s))) = 0 := by
    have hps : p - (p - s) = s := by omega
    rw [hps, hds, Nat.mul_zero]
  have hsplit : 2 ^ (p - s) * d (x + j + (p - (p - s)))
      + ∑ i ∈ (Finset.range p).erase (p - s), 2 ^ i * d (x + j + (p - i))
      = ∑ i ∈ Finset.range p, 2 ^ i * d (x + j + (p - i)) :=
    Finset.add_sum_erase _ (fun i => 2 ^ i * d (x + j + (p - i))) hmem
  have hrotdef : bootRot d x p j
      = ∑ i ∈ Finset.range p, 2 ^ i * d (x + j + (p - i)) := rfl
  have herase : ∑ i ∈ (Finset.range p).erase (p - s), 2 ^ i * d (x + j + (p - i))
      ≤ ∑ i ∈ (Finset.range p).erase (p - s), 2 ^ i := by
    refine Finset.sum_le_sum fun i _ => ?_
    rcases hd (x + j + (p - i)) with h | h <;> simp [h]
  have hfull : 2 ^ (p - s) + ∑ i ∈ (Finset.range p).erase (p - s), 2 ^ i = periodDen p := by
    rw [Finset.add_sum_erase _ _ hmem]
    exact sum_range_two_pow_eq_periodDen p
  have hpow : 1 ≤ 2 ^ (p - s) := Nat.one_le_pow _ 2 (by norm_num)
  omega

/-- **Forward determinism of the periodic rotation state**: the Euclidean step
`2A = e*D + B` with `e` in `{0,1}` and `B < D` determines `(e, B)` from `A`. -/
theorem bootStep_unique {Dn A B₁ B₂ e₁ e₂ : ℕ}
    (he₁ : e₁ ≤ 1) (he₂ : e₂ ≤ 1) (hB₁ : B₁ < Dn) (hB₂ : B₂ < Dn)
    (h₁ : 2 * A + e₁ = B₁ + (Dn + 1) * e₁)
    (h₂ : 2 * A + e₂ = B₂ + (Dn + 1) * e₂) :
    e₁ = e₂ ∧ B₁ = B₂ := by
  rcases (show e₁ = 0 ∨ e₁ = 1 by omega) with rfl | rfl <;>
    rcases (show e₂ = 0 ∨ e₂ = 1 by omega) with rfl | rfl <;>
    exact ⟨by omega, by omega⟩

/-- **Rotation injectivity from minimality**: if `p` is the minimal eventual period (over all
onsets), the `p` rotation masks are pairwise distinct -- a collision propagates through the
deterministic Euclidean steps to an exact period `j - i < p`. -/
theorem bootRot_injOn_of_min {d : ℕ → ℕ} {x p : ℕ}
    (hd : BinaryDigits d) (hp : 0 < p)
    (hper : ∀ n, x < n → d (n + p) = d n)
    (hmin : ∀ m, 0 < m → m < p → ¬ ∃ y : ℕ, ∀ n, y < n → d (n + m) = d n)
    (hlt : ∀ j, bootRot d x p j < periodDen p) :
    Set.InjOn (bootRot d x p) ↑(Finset.range p) := by
  have hd1 : ∀ n, d n ≤ 1 := fun n => by rcases hd n with h | h <;> omega
  have hD2p : (2 : ℕ) ^ p = periodDen p + 1 := by
    have h1 : 1 ≤ 2 ^ p := Nat.one_le_pow p 2 (by norm_num)
    unfold periodDen
    omega
  have key : ∀ i j : ℕ, i < j → j < p → bootRot d x p i = bootRot d x p j → False := by
    intro i j hij hjp heq
    have hstep : ∀ s : ℕ, bootRot d x p (i + s) = bootRot d x p (j + s) →
        bootRot d x p (i + s + 1) = bootRot d x p (j + s + 1)
          ∧ d (x + (i + s) + 1) = d (x + (j + s) + 1) := by
      intro s hs
      have hci := bootRot_step hp hper (i + s)
      have hcj := bootRot_step hp hper (j + s)
      rw [hD2p] at hci hcj
      rw [hs] at hci
      have huniq := bootStep_unique (hd1 (x + (i + s) + 1)) (hd1 (x + (j + s) + 1))
        (hlt (i + s + 1)) (hlt (j + s + 1)) hci hcj
      exact ⟨huniq.2, huniq.1⟩
    have hrot : ∀ s : ℕ, bootRot d x p (i + s) = bootRot d x p (j + s) := by
      intro s
      induction s with
      | zero => simpa using heq
      | succ s ih =>
          have h := (hstep s ih).1
          have e1 : i + (s + 1) = i + s + 1 := by omega
          have e2 : j + (s + 1) = j + s + 1 := by omega
          rw [e1, e2]
          exact h
    have hdig : ∀ s : ℕ, d (x + (i + s) + 1) = d (x + (j + s) + 1) :=
      fun s => (hstep s (hrot s)).2
    refine hmin (j - i) (by omega) (by omega) ⟨x + i, ?_⟩
    intro n hn
    have h := hdig (n - x - i - 1)
    have e1 : x + (i + (n - x - i - 1)) + 1 = n := by omega
    have e2 : x + (j + (n - x - i - 1)) + 1 = n + (j - i) := by omega
    rw [e1, e2] at h
    exact h.symm
  intro i hi j hj heq
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  rcases lt_trichotomy i j with h | h | h
  · exact (key i j h hj heq).elim
  · exact h
  · exact (key j i h hi heq.symm).elim

/-- Sum of distinct positive naturals: a `k`-element set of positives sums to at least
`k(k+1)/2` (stated 2-cleared). -/
theorem bootSum_distinct_pos (s : Finset ℕ) :
    (∀ n ∈ s, 1 ≤ n) → s.card * (s.card + 1) ≤ 2 * ∑ n ∈ s, n := by
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s ha ih =>
      intro h1
      have hnotmem : a ∉ s := fun hmem => lt_irrefl a (ha a hmem)
      have ha1 : 1 ≤ a := h1 a (Finset.mem_insert_self a s)
      have hsub : s ⊆ Finset.Icc 1 (a - 1) := by
        intro n hn
        rw [Finset.mem_Icc]
        refine ⟨h1 n (Finset.mem_insert_of_mem hn), ?_⟩
        have := ha n hn
        omega
      have hcard : s.card ≤ a - 1 := by
        have h := Finset.card_le_card hsub
        rwa [Nat.card_Icc, show a - 1 + 1 - 1 = a - 1 by omega] at h
      have hih := ih (fun n hn => h1 n (Finset.mem_insert_of_mem hn))
      rw [Finset.card_insert_of_notMem hnotmem, Finset.sum_insert hnotmem]
      have hexp : (s.card + 1) * (s.card + 1 + 1)
          = s.card * (s.card + 1) + 2 * (s.card + 1) := by ring
      omega

/-- An all-zero period window forces termination of the whole word. -/
theorem eventuallyZero_of_bootOnes_zero {d : ℕ → ℕ} {x p : ℕ}
    (hd : BinaryDigits d) (hp : 0 < p)
    (hper : ∀ n, x < n → d (n + p) = d n)
    (hk : bootOnes d x p = 0) : EventuallyZero d := by
  have hz : ∀ j, j < p → d (x + j + 1) = 0 := by
    intro j hj
    have hone_le : d (x + j + 1) ≤ bootOnes d x p := by
      unfold bootOnes
      exact Finset.single_le_sum (f := fun i => d (x + i + 1))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
    omega
  refine ⟨x + 1, fun n hn => ?_⟩
  have hdm : p * ((n - x - 1) / p) + (n - x - 1) % p = n - x - 1 := Nat.div_add_mod _ p
  have hmod : (n - x - 1) % p < p := Nat.mod_lt _ hp
  have hidx : n = (x + ((n - x - 1) % p) + 1) + p * ((n - x - 1) / p) := by omega
  rw [hidx, boot_digit_add_mul hper _ _ (by omega)]
  exact hz _ hmod

/-- **THE MINIMAL-PERIOD DENSITY FLOOR** (the 24.1/24.2 headline, scale-free and `t`-free):
a non-terminating binary word with weighted value `P/(u*2^t)` that is `p`-periodic after `x`
with `p` MINIMAL (over all onsets) has at least `(p+1)/(2u)` ones per period:
`p + 1 <= 2*u*k0`. -/
theorem minimalPeriod_ones_floor {Q u t : ℕ} {P : ℤ} {d : ℕ → ℕ} {x p : ℕ}
    (hQfact : Q = u * 2 ^ t) (hupos : 0 < u)
    (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hp : 0 < p) (hper : ∀ n, x < n → d (n + p) = d n)
    (hmin : ∀ m, 0 < m → m < p → ¬ ∃ y : ℕ, ∀ n, y < n → d (n + m) = d n) :
    p + 1 ≤ 2 * u * bootOnes d x p := by
  classical
  have hQ : 0 < Q := by rw [hQfact]; positivity
  rcases Nat.eq_zero_or_pos (bootOnes d x p) with hk0 | hk0
  · exact absurd (eventuallyZero_of_bootOnes_zero hd hp hper hk0) hnonterm
  by_cases hkp : p ≤ bootOnes d x p
  · have h1 : 1 * bootOnes d x p ≤ u * bootOnes d x p :=
      Nat.mul_le_mul_right _ hupos
    have h2 : 2 * (u * bootOnes d x p) = 2 * u * bootOnes d x p := by ring
    omega
  push Not at hkp
  have hone : ∃ i₀, 1 ≤ i₀ ∧ i₀ ≤ p ∧ d (x + i₀) = 1 := by
    by_contra hno
    push Not at hno
    have hzero' : ∀ j ∈ Finset.range p, d (x + j + 1) = 0 := by
      intro j hj
      rw [Finset.mem_range] at hj
      rcases hd (x + j + 1) with h | h
      · exact h
      · exfalso
        apply absurd h
        rw [show x + j + 1 = x + (j + 1) by omega]
        exact hno (j + 1) (by omega) (by omega)
    have hzero : bootOnes d x p = 0 := by
      unfold bootOnes
      exact Finset.sum_eq_zero hzero'
    omega
  have hzero : ∃ i₀, 1 ≤ i₀ ∧ i₀ ≤ p ∧ d (x + i₀) = 0 := by
    by_contra hno
    push Not at hno
    have hone' : ∀ j ∈ Finset.range p, d (x + j + 1) = 1 := by
      intro j hj
      rw [Finset.mem_range] at hj
      rcases hd (x + j + 1) with h | h
      · exfalso
        apply absurd h
        rw [show x + j + 1 = x + (j + 1) by omega]
        exact hno (j + 1) (by omega) (by omega)
      · exact h
    have hall : bootOnes d x p = p := by
      unfold bootOnes
      rw [Finset.sum_congr rfl hone']
      simp
    omega
  obtain ⟨i₁, hi₁1, hi₁p, hi₁⟩ := hone
  obtain ⟨i₂, hi₂1, hi₂p, hi₂⟩ := hzero
  have hrot_pos : ∀ j, 1 ≤ bootRot d x p j :=
    fun j => bootRot_pos hp hper hi₁1 hi₁p hi₁ j
  have hrot_lt : ∀ j, bootRot d x p j < periodDen p :=
    fun j => bootRot_lt hd hp hper hi₂1 hi₂p hi₂ j
  have hdvd : periodDen p ∣ u * p * bootMask d x p :=
    periodicTail_dvd_oddpart hQfact hQ hd heta hp hper
  have hDpos : 0 < periodDen p := periodDen_pos hp
  set g : ℕ := Nat.gcd (periodDen p) (bootMask d x p) with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hDpos
  set q : ℕ := periodDen p / g with hqdef
  have hqg : q * g = periodDen p := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hag : bootMask d x p / g * g = bootMask d x p :=
    Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have hco : Nat.Coprime q (bootMask d x p / g) := Nat.coprime_div_gcd_div_gcd hg
  have hq_dvd : q ∣ u * p := by
    obtain ⟨c, hc⟩ := hdvd
    have hmain : (u * p * (bootMask d x p / g)) * g = (q * c) * g := by
      calc (u * p * (bootMask d x p / g)) * g
          = u * p * (bootMask d x p / g * g) := by ring
        _ = u * p * bootMask d x p := by rw [hag]
        _ = periodDen p * c := hc
        _ = (q * g) * c := by rw [hqg]
        _ = (q * c) * g := by ring
    have h7 : u * p * (bootMask d x p / g) = q * c := Nat.eq_of_mul_eq_mul_right hg hmain
    exact Nat.Coprime.dvd_of_dvd_mul_right hco ⟨c, h7⟩
  have hD2p : (2 : ℕ) ^ p = periodDen p + 1 := by
    have h1 : 1 ≤ 2 ^ p := Nat.one_le_pow p 2 (by norm_num)
    unfold periodDen
    omega
  have hgdvd : ∀ j, g ∣ bootRot d x p j := by
    intro j
    induction j with
    | zero =>
        rw [bootRot_zero]
        exact Nat.gcd_dvd_right _ _
    | succ j ih =>
        have hstep := bootRot_step hp hper j
        rw [hD2p] at hstep
        have hexpand : (periodDen p + 1) * d (x + j + 1)
            = periodDen p * d (x + j + 1) + d (x + j + 1) := by ring
        rw [hexpand] at hstep
        have h1 : g ∣ 2 * bootRot d x p j := Dvd.dvd.mul_left ih 2
        have h2 : g ∣ periodDen p * d (x + j + 1) :=
          Dvd.dvd.mul_right (Nat.gcd_dvd_left _ _) _
        have h3 : bootRot d x p (j + 1)
            = 2 * bootRot d x p j - periodDen p * d (x + j + 1) := by omega
        rw [h3]
        exact Nat.dvd_sub h1 h2
  set m : ℕ → ℕ := fun j => bootRot d x p j / g with hmdef
  have hm_mul : ∀ j, g * m j = bootRot d x p j :=
    fun j => Nat.mul_div_cancel' (hgdvd j)
  have hm_pos : ∀ j, 1 ≤ m j := by
    intro j
    have h1 := hrot_pos j
    have h2 := hm_mul j
    rcases Nat.eq_zero_or_pos (m j) with h0 | h0
    · rw [h0, Nat.mul_zero] at h2; omega
    · exact h0
  have hinj : Set.InjOn (bootRot d x p) ↑(Finset.range p) :=
    bootRot_injOn_of_min hd hp hper hmin hrot_lt
  have hm_inj : Set.InjOn m ↑(Finset.range p) := by
    intro i hi j hj heq
    apply hinj hi hj
    rw [← hm_mul i, ← hm_mul j, heq]
  set simg : Finset ℕ := (Finset.range p).image m with hsimg
  have hcard_img : simg.card = p := by
    rw [hsimg, Finset.card_image_of_injOn hm_inj, Finset.card_range]
  have hsum_img : ∑ n ∈ simg, n = ∑ j ∈ Finset.range p, m j := by
    rw [hsimg]
    exact Finset.sum_image fun a ha b hb hab =>
      hm_inj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
  have hpos_img : ∀ n ∈ simg, 1 ≤ n := by
    intro n hn
    rw [hsimg, Finset.mem_image] at hn
    obtain ⟨j, _, rfl⟩ := hn
    exact hm_pos j
  have hL := bootSum_distinct_pos simg hpos_img
  rw [hcard_img, hsum_img] at hL
  have hsum_eq : ∑ j ∈ Finset.range p, m j = q * bootOnes d x p := by
    have hgs : g * ∑ j ∈ Finset.range p, m j
        = ∑ j ∈ Finset.range p, bootRot d x p j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => hm_mul j
    have hDk := bootRot_sum hp hper
    have hqgk : periodDen p * bootOnes d x p = g * (q * bootOnes d x p) := by
      rw [← hqg]; ring
    refine Nat.eq_of_mul_eq_mul_left hg ?_
    rw [hgs, hDk, hqgk]
  rw [hsum_eq] at hL
  have hq_le : q ≤ u * p := Nat.le_of_dvd (by positivity) hq_dvd
  have h3 : q * bootOnes d x p ≤ u * p * bootOnes d x p :=
    Nat.mul_le_mul_right _ hq_le
  have h4 : 2 * (q * bootOnes d x p) ≤ 2 * (u * p * bootOnes d x p) :=
    Nat.mul_le_mul_left 2 h3
  have h5 : 2 * (u * p * bootOnes d x p) = p * (2 * u * bootOnes d x p) := by ring
  have h6 : p * (p + 1) ≤ p * (2 * u * bootOnes d x p) := by omega
  exact Nat.le_of_mul_le_mul_left h6 hp

/-! ## Part 3.  The shell window count -/

/-- The ones-count of any length-`p` window beyond the onset is the period count. -/
theorem boot_window_sum_const {d : ℕ → ℕ} {x p : ℕ}
    (hper : ∀ n, x < n → d (n + p) = d n) :
    ∀ y, x ≤ y → ∑ j ∈ Finset.range p, d (y + j + 1) = bootOnes d x p := by
  intro y hy
  induction y, hy using Nat.le_induction with
  | base => rfl
  | succ y hxy ih =>
      have e1 := Finset.sum_range_succ (fun j => d (y + j + 1)) p
      have e2 := Finset.sum_range_succ' (fun j => d (y + j + 1)) p
      have e3 : d (y + p + 1) = d (y + 1) := by
        have hidx : y + p + 1 = (y + 1) + p := by omega
        rw [hidx]
        exact hper (y + 1) (by omega)
      have e4 : ∀ j ∈ Finset.range p, d (y + (j + 1) + 1) = d ((y + 1) + j + 1) := by
        intro j _
        congr 1
        omega
      rw [Finset.sum_congr rfl e4] at e2
      have e5 : d (y + 0 + 1) = d (y + 1) := by norm_num
      rw [e3] at e1
      rw [e5] at e2
      omega

/-- **The periodic shell count**: a `p`-periodic tail with onset `x <= X` puts at least
`(X/p)*k0` ones into the dyadic shell `(X, 2X]`. -/
theorem periodic_supportShell_card_lower {d : ℕ → ℕ} {x p X : ℕ}
    (hd : BinaryDigits d) (hx : x ≤ X) (hp : 0 < p)
    (hper : ∀ n, x < n → d (n + p) = d n) :
    X / p * bootOnes d x p ≤ (supportShell d X).card := by
  classical
  set T : ℕ → Finset ℕ := fun s =>
    ((Finset.range p).filter (fun j => d (X + s * p + j + 1) = 1)).image
      (fun j => X + s * p + j + 1) with hT
  have hmemT : ∀ s n, n ∈ T s ↔
      ∃ j, j < p ∧ d (X + s * p + j + 1) = 1 ∧ n = X + s * p + j + 1 := by
    intro s n
    rw [hT]
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨j, ⟨hj, hd1⟩, rfl⟩
      exact ⟨j, hj, hd1, rfl⟩
    · rintro ⟨j, hj, hd1, rfl⟩
      exact ⟨j, ⟨hj, hd1⟩, rfl⟩
  have hcardT : ∀ s, (T s).card = bootOnes d x p := by
    intro s
    rw [hT]
    have hinj : Set.InjOn (fun j => X + s * p + j + 1)
        ↑((Finset.range p).filter (fun j => d (X + s * p + j + 1) = 1)) := by
      intro a _ b _ hab
      dsimp only at hab
      omega
    rw [Finset.card_image_of_injOn hinj, Finset.card_filter]
    have h1 : ∀ j ∈ Finset.range p,
        (if d (X + s * p + j + 1) = 1 then 1 else 0) = d (X + s * p + j + 1) := by
      intro j _
      rcases hd (X + s * p + j + 1) with h | h <;> simp [h]
    rw [Finset.sum_congr rfl h1]
    exact boot_window_sum_const hper (X + s * p) (le_trans hx (Nat.le_add_right X (s * p)))
  have hdisj : ∀ s₁ ∈ Finset.range (X / p), ∀ s₂ ∈ Finset.range (X / p),
      s₁ ≠ s₂ → Disjoint (T s₁) (T s₂) := by
    intro s₁ _ s₂ _ hne
    rw [Finset.disjoint_left]
    intro n hn₁ hn₂
    rw [hmemT] at hn₁ hn₂
    obtain ⟨j₁, hj₁, _, he₁⟩ := hn₁
    obtain ⟨j₂, hj₂, _, he₂⟩ := hn₂
    rcases Nat.lt_or_ge s₁ s₂ with h | h
    · have hmul : (s₁ + 1) * p ≤ s₂ * p := Nat.mul_le_mul_right p (by omega)
      have he : (s₁ + 1) * p = s₁ * p + p := by ring
      omega
    · have hlt : s₂ < s₁ := by omega
      have hmul : (s₂ + 1) * p ≤ s₁ * p := Nat.mul_le_mul_right p (by omega)
      have he : (s₂ + 1) * p = s₂ * p + p := by ring
      omega
  have hsub : (Finset.range (X / p)).biUnion T ⊆ supportShell d X := by
    intro n hn
    rw [Finset.mem_biUnion] at hn
    obtain ⟨s, hs, hns⟩ := hn
    rw [Finset.mem_range] at hs
    rw [hmemT] at hns
    obtain ⟨j, hj, hd1, rfl⟩ := hns
    rw [mem_supportShell]
    have h1 : (s + 1) * p ≤ X / p * p := Nat.mul_le_mul_right p (by omega)
    have h2 : X / p * p ≤ X := Nat.div_mul_le_self X p
    have he : (s + 1) * p = s * p + p := by ring
    exact ⟨by omega, by omega, hd1⟩
  calc X / p * bootOnes d x p
      = ∑ s ∈ Finset.range (X / p), (T s).card := by
        rw [Finset.sum_congr rfl (fun s _ => hcardT s), Finset.sum_const,
          Finset.card_range, smul_eq_mul]
    _ = ((Finset.range (X / p)).biUnion T).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (supportShell d X).card := Finset.card_le_card hsub

/-! ## Part 4.  The master voiding on the window-periodic stratum -/

/-- **Window periodicity of a failing context**: the digit word has an eventual period with
onset at most `X` and period at most `X/2` -- the exact stratum where the section-24 density
floor collides with the shell sparsity. -/
def WindowPeriodic (ctx : ActualFailureContext) : Prop :=
  ∃ x p : ℕ, x ≤ ctx.X ∧ 0 < p ∧ 2 * p ≤ ctx.X ∧
    ∀ n, x < n → ctx.d (n + p) = ctx.d n

/-- **THE MASTER VOIDING**: NO failing context with pinned value `P/(u*2^t)` (`u <= 7`) is
window-periodic -- at EVERY scale (no `2^493443` floor).  The minimal period `pm <= p` keeps
the onset, the floor gives `>= (pm+1)/(2u)` ones per period, the window count gives
`>= X/(4u) >= X/28` support elements in `(X, 2X]`, and `hfailure` caps them at `17X/2^24`. -/
theorem pinnedValue_windowPeriodic_void (ctx : ActualFailureContext)
    {u t : ℕ} {P : ℤ} (hupos : 0 < u) (hu7 : u ≤ 7)
    (heta : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ))
    (hwp : WindowPeriodic ctx) : False := by
  classical
  obtain ⟨x, p, hx, hp, h2p, hper⟩ := hwp
  have hex : ∃ m : ℕ, 0 < m ∧ ∃ y : ℕ, ∀ n : ℕ, y < n → ctx.d (n + m) = ctx.d n :=
    ⟨p, hp, x, hper⟩
  set pm : ℕ := Nat.find hex with hpmdef
  obtain ⟨hpm_pos, y, hy⟩ := Nat.find_spec hex
  have hpm_le : pm ≤ p := Nat.find_min' hex ⟨hp, x, hper⟩
  have hmin : ∀ m, 0 < m → m < pm →
      ¬ ∃ y' : ℕ, ∀ n : ℕ, y' < n → ctx.d (n + m) = ctx.d n := by
    intro m hm0 hmlt hexm
    exact Nat.find_min hex hmlt ⟨hm0, hexm⟩
  have hperm : ∀ n, x < n → ctx.d (n + pm) = ctx.d n := by
    intro n hn
    have hyp : y + 1 ≤ p * (y + 1) := Nat.le_mul_of_pos_left (y + 1) hp
    have hk1 : y < n + p * (y + 1) := by omega
    calc ctx.d (n + pm)
        = ctx.d ((n + pm) + p * (y + 1)) :=
          (boot_digit_add_mul hper (y + 1) (n + pm) (by omega)).symm
      _ = ctx.d ((n + p * (y + 1)) + pm) := by
          have hidx : (n + pm) + p * (y + 1) = (n + p * (y + 1)) + pm := by omega
          rw [hidx]
      _ = ctx.d (n + p * (y + 1)) := hy _ hk1
      _ = ctx.d n := boot_digit_add_mul hper (y + 1) n hn
  have hfloor : pm + 1 ≤ 2 * u * bootOnes ctx.d x pm :=
    minimalPeriod_ones_floor rfl hupos ctx.hd ctx.hnonterm heta hpm_pos hperm hmin
  have hcount : ctx.X / pm * bootOnes ctx.d x pm ≤ (supportShell ctx.d ctx.X).card :=
    periodic_supportShell_card_lower ctx.hd hx hpm_pos hperm
  have h2pm : 2 * pm ≤ ctx.X := by omega
  have h1 : ctx.X / pm * (pm + 1) ≤ ctx.X / pm * (2 * u * bootOnes ctx.d x pm) :=
    Nat.mul_le_mul_left _ hfloor
  have h2 : ctx.X / pm * (2 * u * bootOnes ctx.d x pm)
      = 2 * u * (ctx.X / pm * bootOnes ctx.d x pm) := by ring
  have h3 : 2 * u * (ctx.X / pm * bootOnes ctx.d x pm)
      ≤ 2 * u * (supportShell ctx.d ctx.X).card :=
    Nat.mul_le_mul_left _ hcount
  have h4 : 2 * u * (supportShell ctx.d ctx.X).card
      ≤ 14 * (supportShell ctx.d ctx.X).card :=
    Nat.mul_le_mul_right _ (by omega)
  have h5 : ctx.X / 2 ≤ ctx.X / pm * (pm + 1) := by
    have hd1 : pm * (ctx.X / pm) + ctx.X % pm = ctx.X := Nat.div_add_mod _ _
    have hd2 : 2 * (ctx.X / 2) + ctx.X % 2 = ctx.X := Nat.div_add_mod _ _
    have hmodlt : ctx.X % pm < pm := Nat.mod_lt _ hpm_pos
    have hmod2 : ctx.X % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hge2 : 2 ≤ ctx.X / pm := (Nat.le_div_iff_mul_le hpm_pos).mpr (by omega)
    have hexp : ctx.X / pm * (pm + 1) = pm * (ctx.X / pm) + ctx.X / pm := by ring
    omega
  have hkey : ctx.X / 2 ≤ 14 * (supportShell ctx.d ctx.X).card := by omega
  obtain ⟨L, hL⟩ := ctx.hXdyadic
  have hL28 : 28 ≤ L := carryWord_L_ge_28 ctx hL
  have hX2 : 2 ≤ ctx.X := by
    rw [hL]
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfail := ctx.hfailure
  rw [carryWord_c0_eq] at hfail
  have hkeyR : ((ctx.X / 2 : ℕ) : ℝ)
      ≤ 14 * (((supportShell ctx.d ctx.X).card : ℕ) : ℝ) := by
    exact_mod_cast hkey
  have hhalfN : ctx.X ≤ 2 * (ctx.X / 2) + 1 := by
    have h := Nat.div_add_mod ctx.X 2
    have h2' : ctx.X % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega
  have hhalf : (ctx.X : ℝ) ≤ 2 * ((ctx.X / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hhalfN
  have hX2R : (2 : ℝ) ≤ (ctx.X : ℝ) := by exact_mod_cast hX2
  linarith

/-! ## Part 5.  The per-family voidings on the window-periodic stratum (every scale) -/

/-- **Dyadic value + window periodicity is VOID at every scale** (the `2^493443` floor of
wave 6 is removed on this stratum). -/
theorem shellValueDyadic_void_of_windowPeriodic (ctx : ActualFailureContext)
    (hwp : WindowPeriodic ctx) : ¬ ShellValueDyadic ctx := by
  rintro ⟨t, hdy⟩
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = ((1 : ℤ) : ℝ) / ((1 * 2 ^ t : ℕ) : ℝ) := by
    rw [show realWeightedValue (natBinaryAsReal ctx.d) = 1 / 2 ^ t from hdy]
    push_cast
    ring
  exact pinnedValue_windowPeriodic_void ctx (by norm_num) (by norm_num) heta' hwp

/-- Fifth value + window periodicity is void at every scale. -/
theorem towerFifthValue_void_of_windowPeriodic (ctx : ActualFailureContext)
    (hwp : WindowPeriodic ctx) (t : ℕ) :
    realWeightedValue (natBinaryAsReal ctx.shell.d) ≠ 1 / (5 * 2 ^ t) := by
  intro hval
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = ((1 : ℤ) : ℝ) / ((5 * 2 ^ t : ℕ) : ℝ) := by
    rw [show realWeightedValue (natBinaryAsReal ctx.d) = 1 / (5 * 2 ^ t) from hval]
    push_cast
    ring
  exact pinnedValue_windowPeriodic_void ctx (by norm_num) (by norm_num) heta' hwp

/-- Thirds value + window periodicity is void at every scale. -/
theorem towerThirdsValue_void_of_windowPeriodic (ctx : ActualFailureContext)
    (hwp : WindowPeriodic ctx) (t : ℕ) :
    realWeightedValue (natBinaryAsReal ctx.shell.d) ≠ 2 / (3 * 2 ^ t) := by
  intro hval
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = ((2 : ℤ) : ℝ) / ((3 * 2 ^ t : ℕ) : ℝ) := by
    rw [show realWeightedValue (natBinaryAsReal ctx.d) = 2 / (3 * 2 ^ t) from hval]
    push_cast
    ring
  exact pinnedValue_windowPeriodic_void ctx (by norm_num) (by norm_num) heta' hwp

/-- **All five fixed families are void on the window-periodic stratum at every scale**
(the hit pins `oddpart(Q)` into `{1,3,5,7}`, so the master voiding applies with `u <= 7`). -/
theorem fixedFamilyHit_void_of_windowPeriodic (ctx : ActualFailureContext)
    (hwp : WindowPeriodic ctx) : ¬ FixedFamilyHit ctx := by
  intro hhit
  have hmem := fixedFamilyHit_oddpartQ_mem ctx hhit
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hu7 : ordCompl[2] ctx.Q ≤ 7 := by
    have hmem' : ordCompl[2] ctx.Q = 1 ∨ ordCompl[2] ctx.Q = 3
        ∨ ordCompl[2] ctx.Q = 5 ∨ ordCompl[2] ctx.Q = 7 := by simpa using hmem
    omega
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

/-- Band-2 `(3,1)` void on the window-periodic stratum. -/
theorem returnFixedFamily_void_of_windowPeriodic (ctx : ActualFailureContext)
    (hwp : WindowPeriodic ctx) :
    ¬((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) :=
  fun hh => fixedFamilyHit_void_of_windowPeriodic ctx hwp (Or.inl hh)

/-- Band-3 `(21,3)` void on the window-periodic stratum. -/
theorem densePackFixedFamily_void_of_windowPeriodic (ctx : ActualFailureContext)
    (hwp : WindowPeriodic ctx) :
    ¬((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) :=
  fun hh => fixedFamilyHit_void_of_windowPeriodic ctx hwp (Or.inr (Or.inl hh))

/-- Band-4 `(15,1)` void on the window-periodic stratum. -/
theorem towerFP15_1Family_void_of_windowPeriodic (ctx : ActualFailureContext)
    (hwp : WindowPeriodic ctx) :
    ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 1) :=
  fun hh => fixedFamilyHit_void_of_windowPeriodic ctx hwp (Or.inr (Or.inr (Or.inl hh)))

/-- Band-4 `(15,2)` void on the window-periodic stratum. -/
theorem towerFP15_2Family_void_of_windowPeriodic (ctx : ActualFailureContext)
    (hwp : WindowPeriodic ctx) :
    ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 2) :=
  fun hh =>
    fixedFamilyHit_void_of_windowPeriodic ctx hwp (Or.inr (Or.inr (Or.inr (Or.inl hh))))

/-- Band-4 `(105,7)` void on the window-periodic stratum. -/
theorem towerFP105Family_void_of_windowPeriodic (ctx : ActualFailureContext)
    (hwp : WindowPeriodic ctx) :
    ¬((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 7) :=
  fun hh =>
    fixedFamilyHit_void_of_windowPeriodic ctx hwp (Or.inr (Or.inr (Or.inr (Or.inr hh))))

/-! ## Part 6.  The sharpened deep successors and the additive wiring -/

/-- **The sharpened deep dyadic successor**: every DEEP (`X > 2^493443`) dyadic-value context
is window-periodic.  Strictly weaker demand than `DeepDyadicValueLever`'s outright exclusion:
periodicity is only needed where the section-24 floor then voids the context. -/
def DeepDyadicWindowPeriodicity : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X → ShellValueDyadic ctx →
    WindowPeriodic ctx

/-- The periodicity successor discharges the deep dyadic lever. -/
theorem deepDyadicValueLever_of_windowPeriodicity (h : DeepDyadicWindowPeriodicity) :
    DeepDyadicValueLever :=
  fun ctx hX hdy => shellValueDyadic_void_of_windowPeriodic ctx (h ctx hX hdy) hdy

/-- The periodicity successor discharges the FULL dyadic-value lever (shallow scales by the
wave-6 rigidity, deep scales by the section-24 floor). -/
theorem dyadicValueLever_of_windowPeriodicity (h : DeepDyadicWindowPeriodicity) :
    DyadicValueLever :=
  dyadicValueLever_of_deepScale (deepDyadicValueLever_of_windowPeriodicity h)

/-- The deep fifth-value periodicity successor. -/
def DeepFifthWindowPeriodicity : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
    (∃ t : ℕ, realWeightedValue (natBinaryAsReal ctx.shell.d) = 1 / (5 * 2 ^ t)) →
    WindowPeriodic ctx

/-- The fifth periodicity successor discharges the full fifth-value lever. -/
theorem towerFifthValueLever_of_windowPeriodicity (h : DeepFifthWindowPeriodicity) :
    TowerFifthValueLever := by
  intro ctx t hval
  by_cases hX : 2 ^ 493443 < ctx.X
  · exact towerFifthValue_void_of_windowPeriodic ctx (h ctx hX ⟨t, hval⟩) t hval
  · exact towerFifthValue_void_of_scale ctx (not_lt.mp hX) t hval

/-- The deep thirds-value periodicity successor. -/
def DeepThirdsWindowPeriodicity : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
    (∃ t : ℕ, realWeightedValue (natBinaryAsReal ctx.shell.d) = 2 / (3 * 2 ^ t)) →
    WindowPeriodic ctx

/-- The thirds periodicity successor discharges the full thirds-value lever. -/
theorem towerThirdsValueLever_of_windowPeriodicity (h : DeepThirdsWindowPeriodicity) :
    TowerThirdsValueLever := by
  intro ctx t hval
  by_cases hX : 2 ^ 493443 < ctx.X
  · exact towerThirdsValue_void_of_windowPeriodic ctx (h ctx hX ⟨t, hval⟩) t hval
  · exact towerThirdsValue_void_of_scale ctx (not_lt.mp hX) t hval

/-- The deep fixed-family periodicity successor (one Prop for all five families). -/
def DeepFixedFamilyWindowPeriodicity : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X → FixedFamilyHit ctx →
    WindowPeriodic ctx

/-- The family periodicity successor voids ALL five fixed families on EVERY context. -/
theorem fixedFamilyHit_void_of_windowPeriodicity (h : DeepFixedFamilyWindowPeriodicity)
    (ctx : ActualFailureContext) : ¬ FixedFamilyHit ctx := by
  intro hhit
  by_cases hX : 2 ^ 493443 < ctx.X
  · exact fixedFamilyHit_void_of_windowPeriodic ctx (h ctx hX hhit) hhit
  · exact fixedFamilyHit_void_of_scale ctx (not_lt.mp hX) hhit

/-- The family periodicity successor discharges the deep family voiding Prop of wave 6. -/
theorem deepFixedFamilyVoid_of_windowPeriodicity (h : DeepFixedFamilyWindowPeriodicity) :
    DeepFixedFamilyVoid :=
  fun ctx _ => fixedFamilyHit_void_of_windowPeriodicity h ctx

/-- **The endpoint through the periodicity successor**: `Erdos260Statement` from the deep
dyadic window periodicity plus the lever-shrunk wave-5 surfaces. -/
theorem erdos260_of_dyadicWindowPeriodicity (h : DeepDyadicWindowPeriodicity)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_of_deepDyadicValueLever
    ⟨deepDyadicValueLever_of_windowPeriodicity h, surfaces⟩

/-! ## Part 7.  The honest obstruction inventory (why the bootstrap stops here) -/

/-- **The digit is recovered from the carry PAIR** (backward determinism of the weighted
recursion): `Q*(N+1)*d_{N+1} = 2*R_N - R_{N+1}`.  The single carry value does NOT determine
the next digit (the recursion is non-autonomous: the coefficient moves with `N`). -/
theorem integerCarry_digit_recover (Q : ℕ) (P : ℤ) (d : ℕ → ℕ) (N : ℕ) :
    (Q : ℤ) * ((N + 1 : ℕ) : ℤ) * (d (N + 1) : ℤ)
      = 2 * integerCarry Q P d N - integerCarry Q P d (N + 1) := by
  rw [integerCarry_succ]
  ring

/-- **Why the bounded-state pigeonhole FAILS**: even after dividing out the forced `2^t`
factor, the carry states on the shell window `(X, 2X]` live in `[0, u*(2X+2)]` -- strictly
MORE states than the `X+1` window slots, for every `u >= 1`.  (The carry bound `R_N <= Q(N+2)`
GROWS with `N`; no repeat is forced.) -/
theorem bootstrap_state_count_exceeds_window (u X : ℕ) (hu : 0 < u) :
    X + 1 < u * (2 * X + 2) + 1 := by
  have h1 : 2 * X + 2 ≤ u * (2 * X + 2) := Nat.le_mul_of_pos_left _ hu
  omega

/-! ## Part 8.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the density-bootstrap module. -/
def densityBootstrapStatus : List String :=
  [ "STEP-1 FINDING (the exact relation between the weighted value and manuscript sec. 24): " ++
      "the 24.1 plain doubling orbit does NOT run on the weighted carry (wave 6: digits " ++
      "are invisible mod the odd part u in the WEIGHTED recursion R_{N+1} = 2R_N - " ++
      "Q(N+1)d_{N+1}); 24.2's mechanism runs on the ROTATION MASKS of an exactly-periodic " ++
      "tail, reached from the value identity value = K0/Q (shell_value_eq_K₀_div_Q) " ++
      "through the new weighted periodic-tail identity (2^p-1)^2*R_x = " ++
      "Q*((2^p-1)*(x*M+J) + p*M) (periodicTail_carry_identity) - fully discrete, from the " ++
      "carry recursion plus the bound 0 <= R_N <= Q(N+2) (the deviation transports exactly " ++
      "by T_{k+1} = 2^p*T_k and is affinely bounded).",
    "THE DERIVED 24.2 DIVISIBILITY (the input wave 21 had to ASSUME as hdiv): " ++
      "(2^p-1) | Q*p*M (periodicTail_dvd_Qp), and - the 2-adic sharpening that makes the " ++
      "pinned families work at EVERY t - for Q = u*2^t the whole 2-part cancels against " ++
      "the odd 2^p-1: (2^p-1) | u*p*M (periodicTail_dvd_oddpart).  The effective 24.2 " ++
      "modulus of a pinned value 1/2^t, 1/(5*2^t), 2/(3*2^t) is the tiny odd part u, NOT Q.",
    "THE ORD-FREE 24.1 ORBIT BOUND: the binary-division step on rotation masks is exact " ++
      "and deterministic (bootRot_step, bootStep_unique - the forward determinism of the " ++
      "periodic state, answering the determinism question); at the MINIMAL period the p " ++
      "rotation masks are pairwise distinct (bootRot_injOn_of_min: a collision propagates " ++
      "to a strictly smaller period - no ord_q(2)/primitivity bookkeeping needed), all " ++
      "positive multiples of g = gcd(2^p-1, M), summing to (2^p-1)*k0 (bootRot_sum); with " ++
      "q = (2^p-1)/g | u*p the triangular bound gives THE DENSITY FLOOR p+1 <= 2*u*k0 " ++
      "(minimalPeriod_ones_floor): one period of ANY eventually-periodic realization of a " ++
      "pinned value has ones density > 1/(2u) >= 1/14 - versus c0 = 17/16777216, a margin " ++
      "of ~85000x.  (Manuscript's 1/(3Q) floor sharpened to 1/(2u), scale- and t-free.)",
    "THE WINDOW COUNT (sec. 25.2 segment density on the periodic stratum): onset x <= X " ++
      "and period p <= X/2 put >= (X/p)*k0 >= X/(4u) >= X/28 ones in (X, 2X] " ++
      "(periodic_supportShell_card_lower), against hfailure < 17X/2^24: " ++
      "pinnedValue_windowPeriodic_void - NO pinned-value context (u <= 7) is " ++
      "window-periodic, at EVERY scale X >= 2 (the wave-6 2^493443 floor is REMOVED on " ++
      "this stratum).",
    "CLOSED UNCONDITIONALLY (the window-periodic stratum of all pinned families, every " ++
      "scale): shellValueDyadic_void_of_windowPeriodic, " ++
      "towerFifthValue_void_of_windowPeriodic, towerThirdsValue_void_of_windowPeriodic, " ++
      "fixedFamilyHit_void_of_windowPeriodic + the five per-family forms " ++
      "(returnFixedFamily/densePackFixedFamily/towerFP15_1Family/towerFP15_2Family/" ++
      "towerFP105Family_void_of_windowPeriodic).",
    "WHAT RESISTS AND WHY (honest): the bootstrap does NOT prove the failing word is " ++
      "eventually periodic, so DyadicValueLever stays conditional.  (i) The bounded-state " ++
      "pigeonhole FAILS: the formalized carry bound R_N <= Q(N+2) GROWS with N; dividing " ++
      "by the forced 2^t (two_pow_dvd_integerCarry) leaves ~u*(2X+2) states on a window " ++
      "of X+1 slots - more states than slots for every u >= 1 " ++
      "(bootstrap_state_count_exceeds_window).  (ii) The weighted recursion is " ++
      "NON-AUTONOMOUS: the step coefficient Q(N+1) moves with N, so a carry repeat does " ++
      "not propagate periodicity; the digit is a function of the carry PAIR " ++
      "(integerCarry_digit_recover), and the autonomous companion state is the REAL " ++
      "unweighted tail with no finite state space.  (iii) Exact-periodic words with onset " ++
      "> X or minimal period > X/2 at the failing scale are not counted by the window " ++
      "bound (a block-orbit refinement of 25.2 would extend the period range to " ++
      "~X/(2*u*c0) but cannot remove the onset condition).",
    "THE SHARPEST SURFACE (the deep successors, strictly weaker than wave 6's): " ++
      "DeepDyadicWindowPeriodicity / DeepFifthWindowPeriodicity / " ++
      "DeepThirdsWindowPeriodicity / DeepFixedFamilyWindowPeriodicity demand only that " ++
      "DEEP (X > 2^493443) pinned contexts be window-periodic - the sec. 24 floor then " ++
      "voids them.  Discharges: dyadicValueLever_of_windowPeriodicity (the FULL wave-5 " ++
      "lever), towerFifthValueLever_of_windowPeriodicity, towerThirdsValueLever_of_" ++
      "windowPeriodicity, fixedFamilyHit_void_of_windowPeriodicity (all five families on " ++
      "every context), deepFixedFamilyVoid_of_windowPeriodicity (the wave-6 deep Prop), " ++
      "and the endpoint erdos260_of_dyadicWindowPeriodicity : DeepDyadicWindowPeriodicity " ++
      "-> (DyadicValueLever -> Erdos260DyadicLeverResidual) -> Erdos260Statement.",
    "WIRING IS ADDITIVE: no existing file edited, nothing re-proved; the successors " ++
      "compose with the wave-6 bridges (dyadicValueLever_of_deepScale, " ++
      "erdos260_of_deepDyadicValueLever) and the wave-5 capstone surfaces." ]

theorem densityBootstrapStatus_nonempty : densityBootstrapStatus ≠ [] := by
  simp [densityBootstrapStatus]

/-! ## Part 9.  Axiom-cleanliness audit -/

#print axioms bootRot_zero
#print axioms bootMask_le
#print axioms bootWeight_le
#print axioms boot_digit_add_mul
#print axioms bootBlock_succ
#print axioms integerCarry_add_bootBlock
#print axioms bootBlock_shift
#print axioms periodicTail_carry_identity
#print axioms periodicTail_dvd_Qp
#print axioms periodicTail_dvd_oddpart
#print axioms bootRot_step
#print axioms bootRot_periodic
#print axioms bootRot_sum
#print axioms boot_exists_digit
#print axioms bootRot_pos
#print axioms bootRot_lt
#print axioms bootStep_unique
#print axioms bootRot_injOn_of_min
#print axioms bootSum_distinct_pos
#print axioms eventuallyZero_of_bootOnes_zero
#print axioms minimalPeriod_ones_floor
#print axioms boot_window_sum_const
#print axioms periodic_supportShell_card_lower
#print axioms pinnedValue_windowPeriodic_void
#print axioms shellValueDyadic_void_of_windowPeriodic
#print axioms towerFifthValue_void_of_windowPeriodic
#print axioms towerThirdsValue_void_of_windowPeriodic
#print axioms fixedFamilyHit_void_of_windowPeriodic
#print axioms returnFixedFamily_void_of_windowPeriodic
#print axioms densePackFixedFamily_void_of_windowPeriodic
#print axioms towerFP15_1Family_void_of_windowPeriodic
#print axioms towerFP15_2Family_void_of_windowPeriodic
#print axioms towerFP105Family_void_of_windowPeriodic
#print axioms deepDyadicValueLever_of_windowPeriodicity
#print axioms dyadicValueLever_of_windowPeriodicity
#print axioms towerFifthValueLever_of_windowPeriodicity
#print axioms towerThirdsValueLever_of_windowPeriodicity
#print axioms fixedFamilyHit_void_of_windowPeriodicity
#print axioms deepFixedFamilyVoid_of_windowPeriodicity
#print axioms erdos260_of_dyadicWindowPeriodicity
#print axioms integerCarry_digit_recover
#print axioms bootstrap_state_count_exceeds_window
#print axioms densityBootstrapStatus_nonempty

end

end Erdos260
