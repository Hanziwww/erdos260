import Erdos260.FixedFamilyPeriodicity

/-!
# The hit-to-hit carry analysis at the five fixed data (E.6 / E.11 / E.14)

`FixedFamilyPeriodicity.lean` settled that the old canonical-gap zero-run bridge is DEAD at
every actual context (`actual_zeroRun_void`), and that the correct word-side target is
`FixedFamilyCleanContinuation ctx` (some hit index `k₀` with onset `a k₀ ≤ X` has ALL later
hit gaps equal to the recurrent band).  The missing implication — "fixed datum ⟹ hit gaps
eventually equal the band" — rests on the REAL carry magnitude staying in the E.14 window.
This module formalizes that hit-to-hit carry mechanism exactly.

## Part 1 — the hit-to-hit carry recursion (E.11 in carry form, PROVED)

Between consecutive hits `N = a k` and `N' = a (k+1)` (gap `h = hitGap a k`), the digits are
`0` on `(N, N')` (automatic between hits) and `1` at `N'`, so the integer carry doubles
`h − 1` times and then takes the one-step: with `ρ_k := R_{a k}` (`hitCarry`),

  `ρ_{k+1} = 2^{h_k} · ρ_k − Q · a (k+1)`        (`hitCarry_succ`, `ctxHitCarry_recursion`)

— the manuscript's labelled-fibre transition E.11 transcribed to the genuine word-side
dynamical system.  At actual contexts the carry bounds give `0 < ρ_k ≤ Q(a k + 2)`
(`ctxHitCarry_pos`, `ctxHitCarry_le`), the E.14 envelope.  The mod-`Q` view is GAP-BLIND:
`Q ∣ ρ_k − 2^{a k}·P` (`hitCarry_modQ_positional`) — the residue sees only the position,
never the gap structure, so no mod-q argument can pin a gap.

## Part 2 — the E.14 linearity bridge (PROVED, both directions)

The formal dictionary candidate worked out: the manuscript's E.12 fibre recursion
`B_{y_s} = 2^{γ₀}·B_{x_s} − Q·y_s` on AP fibres `x_s = x₀ + sH` with carries LINEAR in `s`
(`B_{x_s} = B_{x₀} + s·K_Γ`) matches the hit recursion under
(fibre index `s` ↔ hit index `k`, step `H` ↔ gap `g`, fibre slope `K_Γ` ↔ per-hit increment
`δ_k = ρ_{k+1} − ρ_k`).  Under a constant gap `g` the increment obeys the AUTONOMOUS
orbit-shaped step `δ_{k+1} = 2^g·δ_k − Q·g` (`hitCarry_increment_orbitShaped`) — the same
shape as `boundedSlopeStep q K = 2^{canonGap q K}·K − q` under `(K, q) ↔ (δ, Q·g)`; the
pinned band slope is its fixed point (`bandSlope_increment_fixed`).  Rigorously:

* `hitCarry_linear_of_const_gaps` — gaps constant `g` from `k₁` + the E.14 envelope force
  `ρ` EXACTLY linear from `k₁` with slope `β` pinned by `(2^g − 1)·β = Q·g` (the deviation
  `τ_k = (2^g − 1)·δ_k − Q·g` transports by pure doubling `τ_{k+1} = 2^g·τ_k`, and `2^{gk}`
  beats the affine carry envelope, so `τ ≡ 0`).
* `hitCarry_const_gaps_of_linear` — `ρ` linear from `k₀` + positivity force the gaps
  EVENTUALLY constant `= g` with the same pin `(2^g − 1)·β = Q·g` (jumps up need `ρ_k ≤ Q`,
  impossible once `ρ` grows; `β = 0` forces strictly increasing gaps whose up-inequality
  `2^{h−1} ≤ Q·h` dies exponentially).
* `hitCarry_band_unique` — the pin determines the gap: `g ↦ (2^g − 1)/g` is strictly
  monotone (`hitCarry_band_cross_lt`), so a slope `β` satisfies the pin at AT MOST one band.
* `hitCarry_const_gaps_from_onset` — **the onset transfer (the decisive extra)**: in the
  linear regime the jump identity `(2^{h_{k+1}} − 2^{h_k})·ρ_k = Q·h_{k+1} − (2^{h_{k+1}}−1)β`
  with the band pin makes `h_{k+1} = g ⟹ h_k = g` (backward rigidity, `ρ_k > 0`), so the
  eventual constancy PROPAGATES BACK to the linearity onset `k₀` itself.
* `hitCarry_eventuallyLinear_iff_const_gaps` — the clean two-sided abstract bridge:
  `ρ` eventually linear ⟺ gaps eventually constant.

## Part 3 — the named residual and its exact strength (the no-free-lunch verdict)

`FixedFamilyCarryLinear ctx` := some `k₀` with onset `a k₀ ≤ X`, some slope `β` with the
BAND pin `(2^band − 1)·β = Q·band`, and `ρ_{k+1} = ρ_k + β` for all `k ≥ k₀`.  Thanks to the
onset transfer this is **EQUIVALENT** per context (at a fixed-family hit) to the clean
continuation: `fixedFamilyCleanContinuation_iff_carryLinear`.  Hence the deep form
`DeepFixedFamilyCarryLinear` is equivalent to `DeepFixedFamilyCleanContinuation`, to
`DeepFixedFamilyWindowPeriodicity`, and to `DeepFixedFamilyVoid` — the honest no-free-lunch
pattern: the E.14 carry-linearity reformulation IS the residual in carry coordinates, not a
strictly weaker waypoint.  The onset-free forms (`FixedFamilyEventualCleanContinuation` ⟺
`FixedFamilyCarryEventuallyLinear`) are also equivalent TO EACH OTHER, but are NOT shown to
re-enter the voiding chain: the window-periodicity payoff needs the onset `≤ X`.

## Part 4 — the tower-data verdict (honest)

The formalized class-2 tower atoms were checked for AP/linearity data on the carries: the
active-floor/SDR records (`Class2HallIndexSDRResidual`, `Class2SemiperiodicIndexSDRResidual`,
`Class2TowerGenuineLeaf`) carry LANDING data (`hlands`: hit indices land in the support
shell), Hall/counting data, and word-side window matches (`hmatch` against the rational
completion `dyadicDigit q₀ (cen k)`); `TowerL31I31Core` routes by the orbit band readout;
`carry_tracks_slopeOrbit` tracks carries mod `q` only (gap-blind, and its zero-run hypothesis
is void).  NONE of them constrain the integer-carry MAGNITUDE at class-2 routed members, so
nothing in-tree supplies `FixedFamilyCarryLinear`.  What remains is exactly the manuscript's
recurrence/SCC persistence (the I.3.1 refined recurrent tower classes): that recurrent states
sit on AP fibres with carries linear in the fibre index — formalized here as the precise,
named, and provably exact (equivalent, not weaker) residual.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Part 0.  Elementary growth and power helpers -/

/-- `2n ≤ 2^n` for `n ≥ 1`. -/
theorem hitToHit_two_mul_le_two_pow {n : ℕ} (hn : 1 ≤ n) : 2 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have h2 : (2 : ℕ) ≤ 2 ^ n := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      have hp : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by
        rw [pow_succ]; ring
      omega

/-- Eventual exponential domination: `A·m + B < 2^m` for every `m ≥ 2(A + B + 2)`. -/
theorem hitToHit_linear_lt_two_pow (A B : ℕ) :
    ∀ m, 2 * (A + B + 2) ≤ m → A * m + B < 2 ^ m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
      have hn1 : 1 ≤ A + B + 2 := by omega
      have h2n : 2 * (A + B + 2) ≤ 2 ^ (A + B + 2) := hitToHit_two_mul_le_two_pow hn1
      have hlt : A + B + 2 < 2 ^ (A + B + 2) := Nat.lt_two_pow_self
      have hpow : (2 : ℕ) ^ (2 * (A + B + 2)) = 2 ^ (A + B + 2) * 2 ^ (A + B + 2) := by
        rw [two_mul, pow_add]
      calc A * (2 * (A + B + 2)) + B
          < 2 * (A + B + 2) * (A + B + 2) := by nlinarith
        _ ≤ 2 ^ (A + B + 2) * (A + B + 2) := Nat.mul_le_mul h2n le_rfl
        _ ≤ 2 ^ (A + B + 2) * 2 ^ (A + B + 2) := Nat.mul_le_mul le_rfl (le_of_lt hlt)
        _ = 2 ^ (2 * (A + B + 2)) := hpow.symm
  | succ m hm ih =>
      have hA : A < 2 ^ m := by
        have h1 : A ≤ 2 * (A + B + 2) := by omega
        exact lt_of_le_of_lt (le_trans h1 hm) Nat.lt_two_pow_self
      calc A * (m + 1) + B = (A * m + B) + A := by ring
        _ < 2 ^ m + 2 ^ m := Nat.add_lt_add ih hA
        _ = 2 ^ (m + 1) := by rw [pow_succ]; ring

/-- Monotone power comparison transported to `ℤ`. -/
theorem hitToHit_pow_le_pow {s t : ℕ} (h : s ≤ t) : (2 : ℤ) ^ s ≤ 2 ^ t := by
  exact_mod_cast Nat.pow_le_pow_right (by norm_num) h

/-- `1 ≤ 2^g` in `ℤ`. -/
theorem hitToHit_one_le_pow (g : ℕ) : (1 : ℤ) ≤ 2 ^ g := by
  have h : (1 : ℕ) ≤ 2 ^ g := Nat.two_pow_pos g
  exact_mod_cast h

/-- Strict power comparison reflects to exponents. -/
theorem hitToHit_lt_of_pow_lt {s t : ℕ} (h : (2 : ℤ) ^ s < 2 ^ t) : s < t := by
  by_contra hc
  push Not at hc
  exact absurd (hitToHit_pow_le_pow hc) (not_le.mpr h)

/-- Power equality reflects to exponents. -/
theorem hitToHit_eq_of_pow_eq {s t : ℕ} (h : (2 : ℤ) ^ s = 2 ^ t) : s = t := by
  have hn : (2 : ℕ) ^ s = 2 ^ t := by exact_mod_cast h
  exact Nat.pow_right_injective (by norm_num) hn

/-- A sequence of naturals that is non-increasing past `K` is eventually constant
(strong induction on the value at `K`; no choice needed beyond the ambient classical). -/
theorem hitToHit_antitone_eventually_const (f : ℕ → ℕ) :
    ∀ (v K : ℕ), f K ≤ v → (∀ k, K ≤ k → f (k + 1) ≤ f k) →
      ∃ k₁, K ≤ k₁ ∧ ∀ k, k₁ ≤ k → f k = f k₁ := by
  intro v
  induction v with
  | zero =>
      intro K hv hanti
      refine ⟨K, le_rfl, ?_⟩
      intro k hk
      have hchain : ∀ j, K ≤ j → f j ≤ f K := by
        intro j hj
        induction j, hj using Nat.le_induction with
        | base => exact le_rfl
        | succ j hj ih => exact le_trans (hanti j hj) ih
      have h := hchain k hk
      omega
  | succ v ih =>
      intro K hv hanti
      by_cases hconst : ∀ k, K ≤ k → f k = f K
      · exact ⟨K, le_rfl, fun k hk => hconst k hk⟩
      · push Not at hconst
        obtain ⟨j, hjK, hjne⟩ := hconst
        have hchain : ∀ k, K ≤ k → f k ≤ f K := by
          intro k hk
          induction k, hk using Nat.le_induction with
          | base => exact le_rfl
          | succ k hk ih' => exact le_trans (hanti k hk) ih'
        have hjlt : f j < f K := lt_of_le_of_ne (hchain j hjK) hjne
        have hjv : f j ≤ v := by omega
        have hanti' : ∀ k, j ≤ k → f (k + 1) ≤ f k := fun k hk =>
          hanti k (le_trans hjK hk)
        obtain ⟨k₁, hk₁j, hk₁⟩ := ih j hjv hanti'
        exact ⟨k₁, le_trans hjK hk₁j, hk₁⟩

/-! ## Part 1.  The hit-to-hit carry recursion (manuscript E.11 in carry form) -/

/-- Positions advance by the gap: `a (k+1) = a k + hitGap a k` for a strictly monotone
enumeration (the `ℕ`-subtraction in `hitGap` is genuine). -/
theorem hitGap_position_step {a : ℕ → ℕ} (ha : StrictMono a) (k : ℕ) :
    a (k + 1) = a k + hitGap a k := by
  have h : a k < a (k + 1) := ha (by omega)
  unfold hitGap
  omega

/-- Every gap of a strictly monotone enumeration is at least `1`. -/
theorem one_le_hitGap {a : ℕ → ℕ} (ha : StrictMono a) (k : ℕ) : 1 ≤ hitGap a k := by
  have h : a k < a (k + 1) := ha (by omega)
  unfold hitGap
  omega

/-- **The HIT-INDEXED integer carry** `ρ_k := R_{a k}` — the genuine word-side dynamical
system of the fixed-family analysis. -/
def hitCarry (Q : ℕ) (P : ℤ) (d a : ℕ → ℕ) (k : ℕ) : ℤ :=
  integerCarry Q P d (a k)

@[simp] theorem hitCarry_def (Q : ℕ) (P : ℤ) (d a : ℕ → ℕ) (k : ℕ) :
    hitCarry Q P d a k = integerCarry Q P d (a k) := rfl

/-- **The hit-to-hit carry recursion (E.11 in carry form)**: between consecutive hits the
digits are `0` strictly between (automatic from the hit enumeration) and `1` at the right
endpoint, so the carry doubles `h − 1` times and then takes the one-step:
`ρ_{k+1} = 2^{hitGap a k} · ρ_k − Q · a (k+1)`.  Holds for EVERY numerator `P` — it is an
algebraic identity of the recursion, independent of the value hypothesis. -/
theorem hitCarry_succ {d a : ℕ → ℕ} (hd : BinaryDigits d) (hseq : HitSequence d a)
    (Q : ℕ) (P : ℤ) (k : ℕ) :
    hitCarry Q P d a (k + 1)
      = 2 ^ hitGap a k * hitCarry Q P d a k - (Q : ℤ) * (a (k + 1) : ℤ) := by
  have hadj := hseq.adjacent hd k
  have hg1 : 1 ≤ hitGap a k := one_le_hitGap hseq.strict k
  have hsucc : a (k + 1) = a k + hitGap a k := hitGap_position_step hseq.strict k
  obtain ⟨g', hg'⟩ : ∃ g', hitGap a k = g' + 1 := ⟨hitGap a k - 1, by omega⟩
  have hzero : ∀ j : ℕ, a k < j → j ≤ a k + g' → d j = 0 := by
    intro j hj1 hj2
    exact hadj.2.2.2 j hj1 (by omega)
  have hrun := integerCarry_add_of_zero_digits Q P d (a k) g' hzero
  have hone : d (a k + g' + 1) = 1 := by
    have he : a k + g' + 1 = a (k + 1) := by omega
    rw [he]
    exact hseq.hit (k + 1)
  have hstep := integerCarry_succ_of_one Q P d hone
  have hidx : a (k + 1) = a k + g' + 1 := by omega
  simp only [hitCarry_def]
  rw [hidx, hstep, hrun, hg', pow_succ]
  ring

/-- On a non-terminating rational word every hit carry is strictly positive
(the E.14 lower window edge). -/
theorem hitCarry_pos {Q : ℕ} {P : ℤ} {d a : ℕ → ℕ} (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hnonterm : ¬ EventuallyZero d) (k : ℕ) :
    0 < hitCarry Q P d a k :=
  integerCarry_pos_of_not_eventuallyZero hQ hd heta hnonterm (a k)

/-- The E.14 upper window edge at hit positions: `ρ_k ≤ Q·(a k + 2)` — the carry never
escapes the linear envelope of its position. -/
theorem hitCarry_le {Q : ℕ} {P : ℤ} {d a : ℕ → ℕ} (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) (k : ℕ) :
    hitCarry Q P d a k ≤ (Q : ℤ) * ((a k : ℤ) + 2) := by
  have h := (integerCarry_bounds_of_rational_value (Q := Q) (P := P) (d := d)
    (a k) hQ hd heta).2
  have hc : (((a k) + 2 : ℕ) : ℤ) = (a k : ℤ) + 2 := by push_cast; ring
  rw [hitCarry_def, ← hc]
  exact h

/-- **Mod-`Q` GAP-BLINDNESS**: `Q ∣ ρ_k − 2^{a k}·P` — the residue of the hit carry mod `Q`
is a function of the hit POSITION alone (total exponent), never of the gap path that reached
it.  This is the precise form of "no mod-q argument can pin a gap: doubling mod q is
gap-blind". -/
theorem hitCarry_modQ_positional (Q : ℕ) (P : ℤ) (d a : ℕ → ℕ) (k : ℕ) :
    (Q : ℤ) ∣ hitCarry Q P d a k - 2 ^ (a k) * P :=
  dvd_integerCarry_sub_pow_mul Q P d (a k)

/-! ## Part 2.  The E.14 linearity bridge (abstract, both directions)

Throughout: `Q` the denominator, `a` the (strictly monotone) hit enumeration, `rho` any
sequence obeying the hit recursion `ρ_{k+1} = 2^{h_k}·ρ_k − Q·a(k+1)`.  All hypotheses are
exactly what `hitCarry` supplies at an actual context. -/

/-- Closed form of a constant-increment tail: `ρ_{k₀+m} = ρ_{k₀} + m·β`. -/
theorem bridge_closed_form {rho : ℕ → ℤ} {k₀ : ℕ} {β : ℤ}
    (hlin : ∀ k, k₀ ≤ k → rho (k + 1) = rho k + β) :
    ∀ m : ℕ, rho (k₀ + m) = rho k₀ + (m : ℤ) * β := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have h := hlin (k₀ + m) (Nat.le_add_right _ _)
      have he : k₀ + (m + 1) = (k₀ + m) + 1 := rfl
      rw [he, h, ih]
      push_cast
      ring

/-- A positive sequence with a constant-increment tail has nonnegative increment. -/
theorem bridge_beta_nonneg {rho : ℕ → ℤ} (hpos : ∀ k, 0 < rho k) {k₀ : ℕ} {β : ℤ}
    (hlin : ∀ k, k₀ ≤ k → rho (k + 1) = rho k + β) : 0 ≤ β := by
  by_contra hneg
  push Not at hneg
  have hβ1 : β ≤ -1 := by omega
  obtain ⟨m, hm⟩ : ∃ m : ℕ, rho k₀ < (m : ℤ) := by
    refine ⟨(rho k₀).toNat + 1, ?_⟩
    have h := Int.self_le_toNat (rho k₀)
    push_cast
    linarith
  have hcf := bridge_closed_form hlin m
  have hp := hpos (k₀ + m)
  rw [hcf] at hp
  have hmul : (m : ℤ) * β ≤ (m : ℤ) * (-1) :=
    mul_le_mul_of_nonneg_left hβ1 (by positivity)
  linarith

/-- **(E.14 increment identity)** On a linear tail the recursion reads
`(2^{h_k} − 1)·ρ_k − Q·a(k+1) = β`. -/
theorem bridge_beta_eq {Q : ℕ} {a : ℕ → ℕ} {rho : ℕ → ℤ}
    (hrec : ∀ k, rho (k + 1) = 2 ^ hitGap a k * rho k - (Q : ℤ) * (a (k + 1) : ℤ))
    {k₀ : ℕ} {β : ℤ} (hlin : ∀ k, k₀ ≤ k → rho (k + 1) = rho k + β)
    {k : ℕ} (hk : k₀ ≤ k) :
    ((2 : ℤ) ^ hitGap a k - 1) * rho k - (Q : ℤ) * (a (k + 1) : ℤ) = β := by
  have h1 := hrec k
  have h2 := hlin k hk
  linear_combination h2 - h1

/-- **(E.14 jump identity)** Consecutive increment identities eliminate the positions:
`(2^{h_{k+1}} − 2^{h_k})·ρ_k = Q·h_{k+1} − (2^{h_{k+1}} − 1)·β` — the gap JUMP is pinned by
the carry magnitude and the slope. -/
theorem bridge_gap_jump {Q : ℕ} {a : ℕ → ℕ} {rho : ℕ → ℤ} (ha : StrictMono a)
    (hrec : ∀ k, rho (k + 1) = 2 ^ hitGap a k * rho k - (Q : ℤ) * (a (k + 1) : ℤ))
    {k₀ : ℕ} {β : ℤ} (hlin : ∀ k, k₀ ≤ k → rho (k + 1) = rho k + β)
    {k : ℕ} (hk : k₀ ≤ k) :
    ((2 : ℤ) ^ hitGap a (k + 1) - 2 ^ hitGap a k) * rho k
      = (Q : ℤ) * (hitGap a (k + 1) : ℤ) - ((2 : ℤ) ^ hitGap a (k + 1) - 1) * β := by
  have e1 := bridge_beta_eq hrec hlin hk
  have e2 := bridge_beta_eq hrec hlin (Nat.le_succ_of_le hk)
  have hl := hlin k hk
  have hstep : ((a (k + 1 + 1)) : ℤ) = (a (k + 1) : ℤ) + (hitGap a (k + 1) : ℤ) := by
    exact_mod_cast hitGap_position_step ha (k + 1)
  linear_combination e2 - e1 - ((2 : ℤ) ^ hitGap a (k + 1) - 1) * hl + (Q : ℤ) * hstep

/-- **The orbit-shaped increment step (the formal dictionary)**: under a constant gap `g`
the per-hit increment `δ_k = ρ_{k+1} − ρ_k` obeys the AUTONOMOUS recursion
`δ_{k+1} = 2^g·δ_k − Q·g` — the exact shape of the E.13 slope map
`boundedSlopeStep q K = 2^{canonGap q K}·K − q` under the dictionary `(K, q) ↔ (δ, Q·g)`
(fibre slope `K_Γ` ↔ per-hit carry increment; orbit modulus `q` ↔ `Q·H` with AP step
`H = g`, manuscript E.5/E.12). -/
theorem hitCarry_increment_orbitShaped {Q : ℕ} {a : ℕ → ℕ} {rho : ℕ → ℤ}
    (ha : StrictMono a)
    (hrec : ∀ k, rho (k + 1) = 2 ^ hitGap a k * rho k - (Q : ℤ) * (a (k + 1) : ℤ))
    {k₁ g : ℕ} (hg : ∀ k, k₁ ≤ k → hitGap a k = g)
    {k : ℕ} (hk : k₁ ≤ k) :
    rho (k + 1 + 1) - rho (k + 1) = 2 ^ g * (rho (k + 1) - rho k) - (Q : ℤ) * (g : ℤ) := by
  have r1 := hrec k
  have r2 := hrec (k + 1)
  rw [hg k hk] at r1
  rw [hg (k + 1) (Nat.le_succ_of_le hk)] at r2
  have hstep : ((a (k + 1 + 1)) : ℤ) = (a (k + 1) : ℤ) + (g : ℤ) := by
    have h := hitGap_position_step ha (k + 1)
    rw [hg (k + 1) (Nat.le_succ_of_le hk)] at h
    exact_mod_cast h
  linear_combination r2 - r1 - (Q : ℤ) * hstep

/-- The pinned band slope is the FIXED POINT of the orbit-shaped increment map:
`(2^g − 1)·β = Q·g  ⟹  2^g·β − Q·g = β`. -/
theorem bandSlope_increment_fixed {Q g : ℕ} {β : ℤ}
    (h : ((2 : ℤ) ^ g - 1) * β = (Q : ℤ) * (g : ℤ)) :
    2 ^ g * β - (Q : ℤ) * (g : ℤ) = β := by
  linear_combination h

/-- **CONST ⟹ LINEAR (the E.14 window lock)**: if the gaps are constant `= g` from `k₁` and
the carry obeys the E.14 envelope `0 ≤ ρ_k ≤ Q(a k + 2)`, then `ρ` is EXACTLY linear from
`k₁`, with slope pinned by `(2^g − 1)·β = Q·g`.  Mechanism: the deviation
`τ_k = (2^g − 1)(ρ_{k+1} − ρ_k) − Q·g` transports by pure doubling `τ_{k+1} = 2^g·τ_k`,
and `2^{g·m}` beats the affine envelope, so `τ ≡ 0` on the tail. -/
theorem hitCarry_linear_of_const_gaps {Q : ℕ} {a : ℕ → ℕ} {rho : ℕ → ℤ}
    (hQ : 0 < Q) (ha : StrictMono a)
    (hrec : ∀ k, rho (k + 1) = 2 ^ hitGap a k * rho k - (Q : ℤ) * (a (k + 1) : ℤ))
    (hnn : ∀ k, 0 ≤ rho k)
    (hub : ∀ k, rho k ≤ (Q : ℤ) * ((a k : ℤ) + 2))
    {k₁ g : ℕ} (hg1 : 1 ≤ g) (hg : ∀ k, k₁ ≤ k → hitGap a k = g) :
    ∃ β : ℤ, ((2 : ℤ) ^ g - 1) * β = (Q : ℤ) * (g : ℤ) ∧
      ∀ k, k₁ ≤ k → rho (k + 1) = rho k + β := by
  have hstep : ∀ k, k₁ ≤ k → a (k + 1) = a k + g := by
    intro k hk
    have h := hitGap_position_step ha k
    rw [hg k hk] at h
    exact h
  have hAP : ∀ m : ℕ, a (k₁ + m) = a k₁ + m * g := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have he : k₁ + (m + 1) = (k₁ + m) + 1 := rfl
        rw [he, hstep (k₁ + m) (Nat.le_add_right _ _), ih]
        ring
  have haub : ∀ j, k₁ ≤ j → (a j : ℤ) ≤ (a k₁ : ℤ) + (j : ℤ) * (g : ℤ) := by
    intro j hj
    obtain ⟨m, rfl⟩ : ∃ m, j = k₁ + m := ⟨j - k₁, by omega⟩
    have h := hAP m
    have hcast : ((a (k₁ + m)) : ℤ) = (a k₁ : ℤ) + (m : ℤ) * (g : ℤ) := by
      exact_mod_cast h
    rw [hcast]
    have hm : (m : ℤ) ≤ ((k₁ + m : ℕ) : ℤ) := by push_cast; omega
    have hg0 : (0 : ℤ) ≤ (g : ℤ) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hm hg0
    linarith
  set c : ℕ := Q * (a k₁ + 2) + Q * g with hc
  have hcz : ((c : ℕ) : ℤ) = (Q : ℤ) * ((a k₁ : ℤ) + 2) + (Q : ℤ) * (g : ℤ) := by
    rw [hc]; push_cast; ring
  have hρb : ∀ j, k₁ ≤ j → rho j ≤ (c : ℤ) + (Q : ℤ) * (g : ℤ) * (j : ℤ) := by
    intro j hj
    have h1 := hub j
    have h2 := haub j hj
    have hq0 : (0 : ℤ) ≤ (Q : ℤ) := by positivity
    have h3 : (Q : ℤ) * ((a j : ℤ) + 2)
        ≤ (Q : ℤ) * (((a k₁ : ℤ) + (j : ℤ) * (g : ℤ)) + 2) := by
      apply mul_le_mul_of_nonneg_left _ hq0
      linarith
    have h4 : (Q : ℤ) * (((a k₁ : ℤ) + (j : ℤ) * (g : ℤ)) + 2)
        = (Q : ℤ) * ((a k₁ : ℤ) + 2) + (Q : ℤ) * (g : ℤ) * (j : ℤ) := by ring
    have h5 : (0 : ℤ) ≤ (Q : ℤ) * (g : ℤ) := by positivity
    rw [hcz]
    linarith
  have hρb' : ∀ j, k₁ ≤ j → rho (j + 1) ≤ (c : ℤ) + (Q : ℤ) * (g : ℤ) * (j : ℤ) := by
    intro j hj
    have h2 := hub (j + 1)
    have h3 := haub (j + 1) (Nat.le_succ_of_le hj)
    have hq0 : (0 : ℤ) ≤ (Q : ℤ) := by positivity
    have hcast : (((j + 1 : ℕ)) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
    rw [hcast] at h3
    have h4 : (Q : ℤ) * ((a (j + 1) : ℤ) + 2)
        ≤ (Q : ℤ) * (((a k₁ : ℤ) + ((j : ℤ) + 1) * (g : ℤ)) + 2) := by
      apply mul_le_mul_of_nonneg_left _ hq0
      linarith
    have h5 : (Q : ℤ) * (((a k₁ : ℤ) + ((j : ℤ) + 1) * (g : ℤ)) + 2)
        = ((Q : ℤ) * ((a k₁ : ℤ) + 2) + (Q : ℤ) * (g : ℤ))
          + (Q : ℤ) * (g : ℤ) * (j : ℤ) := by ring
    rw [hcz]
    linarith
  have hδb : ∀ j, k₁ ≤ j →
      |rho (j + 1) - rho j| ≤ 2 * (c : ℤ) + 2 * ((Q : ℤ) * (g : ℤ) * (j : ℤ)) := by
    intro j hj
    have h1 := hnn j
    have h2 := hnn (j + 1)
    have h3 := hρb j hj
    have h4 := hρb' j hj
    have hc0 : (0 : ℤ) ≤ (c : ℤ) := by positivity
    have hqg0 : (0 : ℤ) ≤ (Q : ℤ) * (g : ℤ) * (j : ℤ) := by positivity
    rw [abs_le]
    constructor <;> linarith
  set τ : ℕ → ℤ :=
    fun k => ((2 : ℤ) ^ g - 1) * (rho (k + 1) - rho k) - (Q : ℤ) * (g : ℤ) with hτ
  have hτstep : ∀ k, k₁ ≤ k → τ (k + 1) = 2 ^ g * τ k := by
    intro k hk
    have hd := hitCarry_increment_orbitShaped ha hrec hg hk
    simp only [hτ]
    linear_combination ((2 : ℤ) ^ g - 1) * hd
  have hτiter : ∀ k, k₁ ≤ k → ∀ m : ℕ, τ (k + m) = 2 ^ (g * m) * τ k := by
    intro k hk m
    induction m with
    | zero => simp
    | succ m ih =>
        have he : k + (m + 1) = (k + m) + 1 := rfl
        have hexp : g + g * m = g * (m + 1) := by ring
        rw [he, hτstep (k + m) (le_trans hk (Nat.le_add_right k m)), ih,
          ← mul_assoc, ← pow_add, hexp]
  set E : ℕ := 2 ^ g * (2 * c) + Q * g with hE
  set F : ℕ := 2 ^ g * (2 * (Q * g)) with hF
  have hτb : ∀ j, k₁ ≤ j → |τ j| ≤ (E : ℤ) + (F : ℤ) * (j : ℤ) := by
    intro j hj
    have h1 := hδb j hj
    have htri : |τ j| ≤ ((2 : ℤ) ^ g - 1) * |rho (j + 1) - rho j| + (Q : ℤ) * (g : ℤ) := by
      simp only [hτ]
      have ha0 : ((2 : ℤ) ^ g - 1) * (rho (j + 1) - rho j) - (Q : ℤ) * (g : ℤ)
          = ((2 : ℤ) ^ g - 1) * (rho (j + 1) - rho j) + (-((Q : ℤ) * (g : ℤ))) := by ring
      rw [ha0]
      have ha1 := abs_add_le (((2 : ℤ) ^ g - 1) * (rho (j + 1) - rho j))
        (-((Q : ℤ) * (g : ℤ)))
      rw [abs_neg] at ha1
      have ha2 : |((2 : ℤ) ^ g - 1) * (rho (j + 1) - rho j)|
          = ((2 : ℤ) ^ g - 1) * |rho (j + 1) - rho j| := by
        rw [abs_mul, abs_of_nonneg (by linarith [hitToHit_one_le_pow g])]
      have ha3 : |(Q : ℤ) * (g : ℤ)| = (Q : ℤ) * (g : ℤ) := abs_of_nonneg (by positivity)
      linarith
    have h2 : ((2 : ℤ) ^ g - 1) * |rho (j + 1) - rho j|
        ≤ (2 : ℤ) ^ g * (2 * (c : ℤ) + 2 * ((Q : ℤ) * (g : ℤ) * (j : ℤ))) :=
      mul_le_mul (by linarith [hitToHit_one_le_pow g]) h1 (abs_nonneg _) (by positivity)
    have h3 : (E : ℤ) + (F : ℤ) * (j : ℤ)
        = (2 : ℤ) ^ g * (2 * (c : ℤ) + 2 * ((Q : ℤ) * (g : ℤ) * (j : ℤ)))
          + (Q : ℤ) * (g : ℤ) := by
      rw [hE, hF]; push_cast; ring
    rw [h3]
    linarith
  have hτzero : ∀ k, k₁ ≤ k → τ k = 0 := by
    intro k hk
    by_contra hne
    have h1 : (1 : ℤ) ≤ |τ k| := Int.one_le_abs hne
    obtain ⟨m, hm⟩ := carryWord_exists_mul_add_lt_two_pow (E + F * (k + 1)) 1
    have hb := hτb (k + m) (le_trans hk (Nat.le_add_right k m))
    have hit := hτiter k hk m
    have habs : |τ (k + m)| = 2 ^ (g * m) * |τ k| := by
      rw [hit, abs_mul, abs_pow, abs_two]
    have hgm : m ≤ g * m := Nat.le_mul_of_pos_left m (by omega)
    have hpow : (2 : ℤ) ^ m ≤ 2 ^ (g * m) := hitToHit_pow_le_pow hgm
    have hge : (2 : ℤ) ^ m ≤ |τ (k + m)| := by
      have h2 : (2 : ℤ) ^ (g * m) * 1 ≤ 2 ^ (g * m) * |τ k| :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      rw [habs]
      linarith
    have hcast1 : (((k + m : ℕ)) : ℤ) = (k : ℤ) + (m : ℤ) := by push_cast; ring
    rw [hcast1] at hb
    have hmz : ((E + F * (k + 1) : ℕ) : ℤ) * (1 + (m : ℤ)) < (2 : ℤ) ^ m := by
      exact_mod_cast hm
    have hle2 : (E : ℤ) + (F : ℤ) * ((k : ℤ) + (m : ℤ))
        ≤ ((E + F * (k + 1) : ℕ) : ℤ) * (1 + (m : ℤ)) := by
      push_cast
      nlinarith [Int.natCast_nonneg E, Int.natCast_nonneg F, Int.natCast_nonneg k,
        Int.natCast_nonneg m,
        mul_nonneg (Int.natCast_nonneg E) (Int.natCast_nonneg m),
        mul_nonneg (mul_nonneg (Int.natCast_nonneg F) (Int.natCast_nonneg k))
          (Int.natCast_nonneg m)]
    linarith
  have h0 := hτzero k₁ le_rfl
  simp only [hτ] at h0
  have hgt : (0 : ℤ) < (2 : ℤ) ^ g - 1 := by
    have h2 : (2 : ℤ) ≤ 2 ^ g := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ g := hitToHit_pow_le_pow hg1
    linarith
  refine ⟨rho (k₁ + 1) - rho k₁, by linarith, ?_⟩
  intro k hk
  have hk0 := hτzero k hk
  simp only [hτ] at hk0
  have heq : ((2 : ℤ) ^ g - 1) * (rho (k + 1) - rho k)
      = ((2 : ℤ) ^ g - 1) * (rho (k₁ + 1) - rho k₁) := by linarith
  have hcancel := mul_left_cancel₀ (ne_of_gt hgt) heq
  linarith

/-- **LINEAR ⟹ CONST (eventually)**: if `ρ` is positive, obeys the hit recursion, and is
linear from `k₀`, then the gaps are EVENTUALLY constant `= g` with the slope pin
`(2^g − 1)·β = Q·g`.  Mechanism (the E.14 window analysis): an upward gap jump needs
`ρ_k ≤ Q` (impossible once `ρ` grows, `β ≥ 1`), so the gaps are eventually non-increasing,
hence constant; `β = 0` would force strictly increasing gaps whose up-inequality
`2^{h−1} ≤ Q·h` dies against exponential growth. -/
theorem hitCarry_const_gaps_of_linear {Q : ℕ} {a : ℕ → ℕ} {rho : ℕ → ℤ}
    (hQ : 0 < Q) (ha : StrictMono a)
    (hrec : ∀ k, rho (k + 1) = 2 ^ hitGap a k * rho k - (Q : ℤ) * (a (k + 1) : ℤ))
    (hpos : ∀ k, 0 < rho k)
    {k₀ : ℕ} {β : ℤ} (hlin : ∀ k, k₀ ≤ k → rho (k + 1) = rho k + β) :
    ∃ g k₁ : ℕ, k₀ ≤ k₁ ∧ ((2 : ℤ) ^ g - 1) * β = (Q : ℤ) * (g : ℤ) ∧
      ∀ k, k₁ ≤ k → hitGap a k = g := by
  have hβ0 : 0 ≤ β := bridge_beta_nonneg hpos hlin
  -- an upward gap jump pins the carry below Q and the gap below the exponential threshold
  have hup : ∀ k, k₀ ≤ k → hitGap a k < hitGap a (k + 1) →
      rho k ≤ (Q : ℤ) ∧ 2 ^ (hitGap a (k + 1) - 1) ≤ Q * hitGap a (k + 1) := by
    intro k hk hlt
    have hjump := bridge_gap_jump ha hrec hlin hk
    obtain ⟨m, hm1⟩ : ∃ m, hitGap a (k + 1) = m + 1 :=
      ⟨hitGap a (k + 1) - 1, by omega⟩
    have hm0 : hitGap a k ≤ m := by omega
    have hsub : hitGap a (k + 1) - 1 = m := by omega
    have hcast : (2 : ℤ) ^ hitGap a k ≤ 2 ^ m := hitToHit_pow_le_pow hm0
    have hsplit : (2 : ℤ) ^ hitGap a (k + 1) = 2 * 2 ^ m := by
      rw [hm1, pow_succ]; ring
    rw [hsplit] at hjump
    have hZnn : (0 : ℤ) ≤ ((2 : ℤ) * 2 ^ m - 1) * β := by
      apply mul_nonneg _ hβ0
      have := hitToHit_one_le_pow m
      linarith
    have haux : (0 : ℤ) ≤ ((2 : ℤ) ^ m - 2 ^ hitGap a k) * rho k :=
      mul_nonneg (by linarith) (le_of_lt (hpos k))
    have hexp : ((2 : ℤ) * 2 ^ m - 2 ^ hitGap a k) * rho k
        = (2 : ℤ) ^ m * rho k + ((2 : ℤ) ^ m - 2 ^ hitGap a k) * rho k := by ring
    have hkey : (2 : ℤ) ^ m * rho k ≤ (Q : ℤ) * ((hitGap a (k + 1) : ℕ) : ℤ) := by
      linarith
    constructor
    · have hQ0 : (0 : ℤ) ≤ (Q : ℤ) := by positivity
      have hm2 : (m : ℤ) + 1 ≤ (2 : ℤ) ^ m := by
        have h : m < 2 ^ m := Nat.lt_two_pow_self
        have h' : (m : ℤ) < (2 : ℤ) ^ m := by exact_mod_cast h
        linarith
      have hcast2 : ((hitGap a (k + 1) : ℕ) : ℤ) = (m : ℤ) + 1 := by
        rw [hm1]; push_cast; ring
      rw [hcast2] at hkey
      have h3 : (Q : ℤ) * ((m : ℤ) + 1) ≤ (Q : ℤ) * (2 : ℤ) ^ m :=
        mul_le_mul_of_nonneg_left hm2 hQ0
      have h4 : (2 : ℤ) ^ m * rho k ≤ (2 : ℤ) ^ m * (Q : ℤ) := by
        calc (2 : ℤ) ^ m * rho k ≤ (Q : ℤ) * ((m : ℤ) + 1) := hkey
          _ ≤ (Q : ℤ) * (2 : ℤ) ^ m := h3
          _ = (2 : ℤ) ^ m * (Q : ℤ) := by ring
      exact le_of_mul_le_mul_left h4 (by positivity)
    · have hx1 : (1 : ℤ) ≤ rho k := hpos k
      have h6 : (2 : ℤ) ^ m * 1 ≤ (2 : ℤ) ^ m * rho k :=
        mul_le_mul_of_nonneg_left hx1 (by positivity)
      have h5 : (2 : ℤ) ^ m ≤ (Q : ℤ) * ((hitGap a (k + 1) : ℕ) : ℤ) := by linarith
      have h7 : (2 : ℕ) ^ m ≤ Q * hitGap a (k + 1) := by exact_mod_cast h5
      rw [hsub]
      exact h7
  rcases hβ0.lt_or_eq with hβpos | hβz
  · -- β ≥ 1: ρ grows, so eventually no upward jumps; non-increasing gaps stabilize
    have hβ1 : (1 : ℤ) ≤ β := hβpos
    have hbigρ : ∀ k, k₀ + Q ≤ k → (Q : ℤ) < rho k := by
      intro k hk
      obtain ⟨m, rfl⟩ : ∃ m, k = k₀ + m := ⟨k - k₀, by omega⟩
      have hcf := bridge_closed_form hlin m
      have hmQ : Q ≤ m := by omega
      have hm : (Q : ℤ) ≤ (m : ℤ) := by exact_mod_cast hmQ
      have hmul : (m : ℤ) * 1 ≤ (m : ℤ) * β :=
        mul_le_mul_of_nonneg_left hβ1 (by positivity)
      have hp := hpos k₀
      rw [hcf]
      linarith
    have hanti : ∀ k, k₀ + Q ≤ k → hitGap a (k + 1) ≤ hitGap a k := by
      intro k hk
      by_contra hcon
      push Not at hcon
      have h := (hup k (by omega) hcon).1
      exact absurd h (not_le.mpr (hbigρ k hk))
    obtain ⟨k₁, hk₁K, hk₁const⟩ :=
      hitToHit_antitone_eventually_const (hitGap a) (hitGap a (k₀ + Q)) (k₀ + Q)
        le_rfl hanti
    refine ⟨hitGap a k₁, k₁, by omega, ?_, hk₁const⟩
    have hg1 := hk₁const (k₁ + 1) (Nat.le_succ k₁)
    have hjump := bridge_gap_jump ha hrec hlin (show k₀ ≤ k₁ by omega)
    rw [hg1] at hjump
    have hz : ((2 : ℤ) ^ hitGap a k₁ - 2 ^ hitGap a k₁) * rho k₁ = 0 := by ring
    linarith
  · -- β = 0: ρ constant forces strictly increasing gaps, killed by the up-inequality
    exfalso
    have hconst : ∀ k, k₀ ≤ k → rho k = rho k₀ := by
      intro k hk
      obtain ⟨m, rfl⟩ : ∃ m, k = k₀ + m := ⟨k - k₀, by omega⟩
      have h := bridge_closed_form hlin m
      rw [← hβz] at h
      simpa using h
    have hstrict : ∀ k, k₀ ≤ k → hitGap a k < hitGap a (k + 1) := by
      intro k hk
      have e1 := bridge_beta_eq hrec hlin hk
      have e2 := bridge_beta_eq hrec hlin (Nat.le_succ_of_le hk)
      rw [hconst k hk] at e1
      rw [hconst (k + 1) (Nat.le_succ_of_le hk)] at e2
      rw [← hβz] at e1 e2
      have hA : ((a (k + 1)) : ℤ) < ((a (k + 1 + 1)) : ℤ) := by
        exact_mod_cast ha (Nat.lt_succ_self (k + 1))
      have hQpos : (0 : ℤ) < (Q : ℤ) := by exact_mod_cast hQ
      have hα := hpos k₀
      have hAA : (Q : ℤ) * ((a (k + 1)) : ℤ) < (Q : ℤ) * ((a (k + 1 + 1)) : ℤ) :=
        mul_lt_mul_of_pos_left hA hQpos
      have hlt : ((2 : ℤ) ^ hitGap a k - 1) * rho k₀
          < ((2 : ℤ) ^ hitGap a (k + 1) - 1) * rho k₀ := by linarith
      have hpw : (2 : ℤ) ^ hitGap a k < 2 ^ hitGap a (k + 1) := by
        have h := lt_of_mul_lt_mul_right hlt (le_of_lt hα)
        linarith
      exact hitToHit_lt_of_pow_lt hpw
    have hmono : ∀ m : ℕ, hitGap a k₀ + m ≤ hitGap a (k₀ + m) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          have h := hstrict (k₀ + m) (Nat.le_add_right _ _)
          have hgoal : hitGap a k₀ + (m + 1) ≤ hitGap a (k₀ + m + 1) := by omega
          exact hgoal
    set M : ℕ := 2 * (Q + Q + 2) with hM
    have hbig : M + 1 ≤ hitGap a (k₀ + M + 1) := by
      have h : hitGap a k₀ + (M + 1) ≤ hitGap a (k₀ + M + 1) := hmono (M + 1)
      have h1 := one_le_hitGap ha k₀
      omega
    obtain ⟨_, hupineq⟩ :=
      hup (k₀ + M) (Nat.le_add_right _ _) (hstrict (k₀ + M) (Nat.le_add_right _ _))
    obtain ⟨t, ht⟩ : ∃ t, hitGap a (k₀ + M + 1) = t + 1 :=
      ⟨hitGap a (k₀ + M + 1) - 1, by
        have := one_le_hitGap ha (k₀ + M + 1)
        omega⟩
    have htM : M ≤ t := by omega
    have hsub : hitGap a (k₀ + M + 1) - 1 = t := by omega
    rw [hsub, ht, Nat.mul_succ] at hupineq
    have hev : Q * t + Q < 2 ^ t := hitToHit_linear_lt_two_pow Q Q t (by omega)
    exact absurd hupineq (not_le.mpr hev)

/-- The cross-multiplied band monotonicity: for `1 ≤ g < g'`,
`(2^g − 1)·g' < (2^{g'} − 1)·g` — i.e. `g ↦ (2^g − 1)/g` is strictly increasing. -/
theorem hitCarry_band_cross_lt {g g' : ℕ} (hg : 1 ≤ g) (hlt : g < g') :
    ((2 : ℤ) ^ g - 1) * (g' : ℤ) < ((2 : ℤ) ^ g' - 1) * (g : ℤ) := by
  have hlt' : g + 1 ≤ g' := hlt
  clear hlt
  induction g', hlt' using Nat.le_induction with
  | base =>
      have hp : (2 : ℤ) ^ (g + 1) = 2 * 2 ^ g := by rw [pow_succ]; ring
      have h1 : (1 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hg
      have h2 : (2 : ℤ) ≤ 2 ^ g := by
        calc (2 : ℤ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ g := hitToHit_pow_le_pow hg
      have h3 : (2 : ℤ) ^ g * 1 ≤ (2 : ℤ) ^ g * (g : ℤ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      rw [mul_one] at h3
      push_cast
      rw [hp]
      nlinarith
  | succ g' hg' ih =>
      have hp : (2 : ℤ) ^ (g' + 1) = 2 * 2 ^ g' := by rw [pow_succ]; ring
      have h1 : (1 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hg
      have h2 : (2 : ℤ) ^ g ≤ 2 ^ g' := hitToHit_pow_le_pow (by omega)
      have h3 : (2 : ℤ) ^ g' * 1 ≤ (2 : ℤ) ^ g' * (g : ℤ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      rw [mul_one] at h3
      push_cast
      push_cast at ih
      rw [hp]
      nlinarith

/-- **The slope pins the band uniquely**: a single slope `β` can satisfy
`(2^g − 1)·β = Q·g` at AT MOST one positive band `g`. -/
theorem hitCarry_band_unique {Q g g' : ℕ} {β : ℤ} (hQ : 0 < Q) (hg : 1 ≤ g) (hg' : 1 ≤ g')
    (h1 : ((2 : ℤ) ^ g - 1) * β = (Q : ℤ) * (g : ℤ))
    (h2 : ((2 : ℤ) ^ g' - 1) * β = (Q : ℤ) * (g' : ℤ)) : g = g' := by
  have hQpos : (0 : ℤ) < (Q : ℤ) := by exact_mod_cast hQ
  have hgpos : (0 : ℤ) < (g : ℤ) := by exact_mod_cast hg
  have hβpos : 0 < β := by
    by_contra hcon
    push Not at hcon
    have hf : (0 : ℤ) ≤ (2 : ℤ) ^ g - 1 := by linarith [hitToHit_one_le_pow g]
    have hle : ((2 : ℤ) ^ g - 1) * β ≤ ((2 : ℤ) ^ g - 1) * 0 :=
      mul_le_mul_of_nonneg_left hcon hf
    rw [mul_zero, h1] at hle
    have := mul_pos hQpos hgpos
    linarith
  have hβne : β ≠ 0 := ne_of_gt hβpos
  rcases lt_trichotomy g g' with hlt | heq | hgt
  · exfalso
    have hcross := hitCarry_band_cross_lt hg hlt
    have e3 : ((2 : ℤ) ^ g - 1) * (g' : ℤ) * β = ((2 : ℤ) ^ g' - 1) * (g : ℤ) * β := by
      have e1 : (((2 : ℤ) ^ g - 1) * β) * (g' : ℤ)
          = ((Q : ℤ) * (g : ℤ)) * (g' : ℤ) := by rw [h1]
      have e2 : (((2 : ℤ) ^ g' - 1) * β) * (g : ℤ)
          = ((Q : ℤ) * (g' : ℤ)) * (g : ℤ) := by rw [h2]
      linear_combination e1 - e2
    have e4 := mul_right_cancel₀ hβne e3
    exact absurd e4 (ne_of_lt hcross)
  · exact heq
  · exfalso
    have hcross := hitCarry_band_cross_lt hg' hgt
    have e3 : ((2 : ℤ) ^ g' - 1) * (g : ℤ) * β = ((2 : ℤ) ^ g - 1) * (g' : ℤ) * β := by
      have e1 : (((2 : ℤ) ^ g - 1) * β) * (g' : ℤ)
          = ((Q : ℤ) * (g : ℤ)) * (g' : ℤ) := by rw [h1]
      have e2 : (((2 : ℤ) ^ g' - 1) * β) * (g : ℤ)
          = ((Q : ℤ) * (g' : ℤ)) * (g : ℤ) := by rw [h2]
      linear_combination e2 - e1
    have e4 := mul_right_cancel₀ hβne e3
    exact absurd e4 (ne_of_lt hcross)

/-- **The onset transfer (backward rigidity)**: in the linear regime with band-pinned slope,
`h_{k+1} = g` forces `h_k = g` (the jump identity degenerates to
`(2^g − 2^{h_k})·ρ_k = 0` with `ρ_k > 0`), so an eventual gap seed propagates back to the
linearity onset `k₀`: ALL gaps from `k₀` equal `g`. -/
theorem hitCarry_const_gaps_from_onset {Q : ℕ} {a : ℕ → ℕ} {rho : ℕ → ℤ}
    (ha : StrictMono a)
    (hrec : ∀ k, rho (k + 1) = 2 ^ hitGap a k * rho k - (Q : ℤ) * (a (k + 1) : ℤ))
    (hpos : ∀ k, 0 < rho k)
    {k₀ g : ℕ} {β : ℤ}
    (hlin : ∀ k, k₀ ≤ k → rho (k + 1) = rho k + β)
    (hβ : ((2 : ℤ) ^ g - 1) * β = (Q : ℤ) * (g : ℤ))
    {k₁ : ℕ} (hk₁ : k₀ ≤ k₁) (hseed : ∀ k, k₁ ≤ k → hitGap a k = g) :
    ∀ k, k₀ ≤ k → hitGap a k = g := by
  have hback : ∀ k, k₀ ≤ k → hitGap a (k + 1) = g → hitGap a k = g := by
    intro k hk hnext
    have hjump := bridge_gap_jump ha hrec hlin hk
    rw [hnext] at hjump
    have h0 : ((2 : ℤ) ^ g - 2 ^ hitGap a k) * rho k = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h | h
    · have hpe : (2 : ℤ) ^ hitGap a k = 2 ^ g := by linarith
      exact hitToHit_eq_of_pow_eq hpe
    · exact absurd h (ne_of_gt (hpos k))
  have hdesc : ∀ m k, k₀ ≤ k → k + m = k₁ → hitGap a k = g := by
    intro m
    induction m with
    | zero =>
        intro k hk he
        have hke : k = k₁ := by omega
        rw [hke]
        exact hseed k₁ le_rfl
    | succ m ih =>
        intro k hk he
        exact hback k hk (ih (k + 1) (by omega) (by omega))
  intro k hk
  rcases Nat.lt_or_ge k k₁ with h | h
  · exact hdesc (k₁ - k) k hk (by omega)
  · exact hseed k h

/-- **The two-sided abstract bridge (the headline)**: for a positive solution of the hit
recursion inside the E.14 envelope, the hit-carry sequence is EVENTUALLY LINEAR if and only
if the hit gaps are EVENTUALLY CONSTANT. -/
theorem hitCarry_eventuallyLinear_iff_const_gaps {Q : ℕ} {a : ℕ → ℕ} {rho : ℕ → ℤ}
    (hQ : 0 < Q) (ha : StrictMono a)
    (hrec : ∀ k, rho (k + 1) = 2 ^ hitGap a k * rho k - (Q : ℤ) * (a (k + 1) : ℤ))
    (hpos : ∀ k, 0 < rho k)
    (hub : ∀ k, rho k ≤ (Q : ℤ) * ((a k : ℤ) + 2)) :
    (∃ k₀ : ℕ, ∃ β : ℤ, ∀ k, k₀ ≤ k → rho (k + 1) = rho k + β)
      ↔ (∃ k₁ g : ℕ, ∀ k, k₁ ≤ k → hitGap a k = g) := by
  constructor
  · rintro ⟨k₀, β, hlin⟩
    obtain ⟨g, k₁, _, _, hconst⟩ :=
      hitCarry_const_gaps_of_linear hQ ha hrec hpos hlin
    exact ⟨k₁, g, hconst⟩
  · rintro ⟨k₁, g, hconst⟩
    have hg1 : 1 ≤ g := by
      have h := one_le_hitGap ha k₁
      rw [hconst k₁ le_rfl] at h
      exact h
    obtain ⟨β, _, hlin⟩ :=
      hitCarry_linear_of_const_gaps hQ ha hrec (fun k => le_of_lt (hpos k)) hub hg1 hconst
    exact ⟨k₁, β, hlin⟩

/-! ## Part 3.  The context instantiation (the actual hit-carry system) -/

/-- The canonical carry numerator of an actual failure context — the SAME `choose` through
which `class1SlopeDatum` (and hence the five fixed families) is routed. -/
def ctxCarryP (ctx : ActualFailureContext) : ℤ := ctx.shell.hrational.choose

theorem ctxCarryP_spec (ctx : ActualFailureContext) :
    realWeightedValue (natBinaryAsReal ctx.d) = (ctxCarryP ctx : ℝ) / (ctx.Q : ℝ) :=
  ctx.shell.hrational.choose_spec

/-- **The hit-indexed carry sequence of the context**: `ρ_k = R_{a k}` along the canonical
N.24 hit enumeration, at the canonical numerator. -/
def ctxHitCarry (ctx : ActualFailureContext) (k : ℕ) : ℤ :=
  hitCarry ctx.Q (ctxCarryP ctx) ctx.d ctx.n24CarryData.a k

/-- **E.11 in carry form at every actual context, for EVERY numerator** `P`:
`R_{a(k+1)} = 2^{hitGap k}·R_{a k} − Q·a(k+1)`. -/
theorem ctx_hitCarry_succ (ctx : ActualFailureContext) (P : ℤ) (k : ℕ) :
    hitCarry ctx.Q P ctx.d ctx.n24CarryData.a (k + 1)
      = 2 ^ hitGap ctx.n24CarryData.a k * hitCarry ctx.Q P ctx.d ctx.n24CarryData.a k
        - (ctx.Q : ℤ) * (ctx.n24CarryData.a (k + 1) : ℤ) :=
  hitCarry_succ ctx.hd ctx.n24CarryData.carry.hits ctx.Q P k

/-- The canonical instance of the hit-to-hit recursion. -/
theorem ctxHitCarry_recursion (ctx : ActualFailureContext) (k : ℕ) :
    ctxHitCarry ctx (k + 1)
      = 2 ^ hitGap ctx.n24CarryData.a k * ctxHitCarry ctx k
        - (ctx.Q : ℤ) * (ctx.n24CarryData.a (k + 1) : ℤ) :=
  ctx_hitCarry_succ ctx (ctxCarryP ctx) k

/-- Positivity of the actual hit carries (E.14 lower edge; from non-termination). -/
theorem ctxHitCarry_pos (ctx : ActualFailureContext) (k : ℕ) : 0 < ctxHitCarry ctx k :=
  hitCarry_pos (a := ctx.n24CarryData.a) ctx.hQ ctx.hd (ctxCarryP_spec ctx)
    ctx.hnonterm k

/-- The actual hit carries obey the E.14 envelope `ρ_k ≤ Q·(a k + 2)`. -/
theorem ctxHitCarry_le (ctx : ActualFailureContext) (k : ℕ) :
    ctxHitCarry ctx k ≤ (ctx.Q : ℤ) * ((ctx.n24CarryData.a k : ℤ) + 2) :=
  hitCarry_le (a := ctx.n24CarryData.a) ctx.hQ ctx.hd (ctxCarryP_spec ctx) k

/-- Gap-blindness of the mod-`Q` view at the actual context. -/
theorem ctxHitCarry_modQ_positional (ctx : ActualFailureContext) (k : ℕ) :
    (ctx.Q : ℤ) ∣ ctxHitCarry ctx k - 2 ^ (ctx.n24CarryData.a k) * ctxCarryP ctx :=
  hitCarry_modQ_positional ctx.Q (ctxCarryP ctx) ctx.d ctx.n24CarryData.a k

/-- The context-level two-sided bridge: the actual hit-carry sequence is eventually linear
iff the actual hit gaps are eventually constant. -/
theorem ctxHitCarry_eventuallyLinear_iff_const_gaps (ctx : ActualFailureContext) :
    (∃ k₀ : ℕ, ∃ β : ℤ, ∀ k, k₀ ≤ k → ctxHitCarry ctx (k + 1) = ctxHitCarry ctx k + β)
      ↔ (∃ k₁ g : ℕ, ∀ k, k₁ ≤ k → hitGap ctx.n24CarryData.a k = g) :=
  hitCarry_eventuallyLinear_iff_const_gaps ctx.hQ ctx.n24CarryData.carry.hits.strict
    (ctxHitCarry_recursion ctx) (ctxHitCarry_pos ctx) (ctxHitCarry_le ctx)

/-! ## Part 4.  The named residual and the per-context equivalences -/

/-- **The E.14 hit-carry linearity residual (onset form)**: some hit index `k₀` with
window-compatible onset `a k₀ ≤ X` and some slope `β` satisfying the BAND pin
`(2^band − 1)·β = Q·band` such that the hit-carry increments are constant `= β` from `k₀`.
This is the manuscript's "recurrent states sit on AP fibres with carries linear in the
fibre index" (E.12/E.14), transcribed to the hit-indexed carry system. -/
def FixedFamilyCarryLinear (ctx : ActualFailureContext) : Prop :=
  ∃ k₀ : ℕ, ∃ β : ℤ,
    ctx.n24CarryData.a k₀ ≤ ctx.X ∧
    ((2 : ℤ) ^ fixedFamilyRecurrentBand ctx - 1) * β
      = (ctx.Q : ℤ) * (fixedFamilyRecurrentBand ctx : ℤ) ∧
    ∀ k, k₀ ≤ k → ctxHitCarry ctx (k + 1) = ctxHitCarry ctx k + β

/-- The onset-free clean continuation: ALL hit gaps from SOME index equal the band
(no window-onset demand). -/
def FixedFamilyEventualCleanContinuation (ctx : ActualFailureContext) : Prop :=
  ∃ k₁ : ℕ, ∀ k, k₁ ≤ k → hitGap ctx.n24CarryData.a k = fixedFamilyRecurrentBand ctx

/-- The onset-free carry linearity: band-pinned slope, increments constant from SOME index
(no window-onset demand). -/
def FixedFamilyCarryEventuallyLinear (ctx : ActualFailureContext) : Prop :=
  ∃ k₀ : ℕ, ∃ β : ℤ,
    ((2 : ℤ) ^ fixedFamilyRecurrentBand ctx - 1) * β
      = (ctx.Q : ℤ) * (fixedFamilyRecurrentBand ctx : ℤ) ∧
    ∀ k, k₀ ≤ k → ctxHitCarry ctx (k + 1) = ctxHitCarry ctx k + β

/-- **CC ⟹ CL (genuine, via the E.14 window lock)**: the clean continuation forces the hit
carry EXACTLY linear from the same onset, with the band-pinned slope. -/
theorem fixedFamilyCarryLinear_of_cleanContinuation (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hcc : FixedFamilyCleanContinuation ctx) :
    FixedFamilyCarryLinear ctx := by
  obtain ⟨k₀, honset, hg⟩ := hcc
  have hband := fixedFamilyRecurrentBand_bounds ctx hhit
  obtain ⟨β, hβ, hlin⟩ :=
    hitCarry_linear_of_const_gaps ctx.hQ ctx.n24CarryData.carry.hits.strict
      (ctxHitCarry_recursion ctx) (fun k => le_of_lt (ctxHitCarry_pos ctx k))
      (ctxHitCarry_le ctx) (le_trans (by norm_num) hband.1) hg
  exact ⟨k₀, β, honset, hβ, hlin⟩

/-- **CL ⟹ CC (genuine, via eventual constancy + band uniqueness + the onset transfer)**:
band-pinned hit-carry linearity from a window-compatible onset forces ALL hit gaps from
that onset to equal the band. -/
theorem fixedFamilyCleanContinuation_of_carryLinear (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hcl : FixedFamilyCarryLinear ctx) :
    FixedFamilyCleanContinuation ctx := by
  obtain ⟨k₀, β, honset, hβ, hlin⟩ := hcl
  have hband := fixedFamilyRecurrentBand_bounds ctx hhit
  have hstrict := ctx.n24CarryData.carry.hits.strict
  obtain ⟨g, k₁, hk₁, hgβ, hgconst⟩ :=
    hitCarry_const_gaps_of_linear ctx.hQ hstrict (ctxHitCarry_recursion ctx)
      (ctxHitCarry_pos ctx) hlin
  have hg1 : 1 ≤ g := by
    have h := one_le_hitGap hstrict k₁
    rw [hgconst k₁ le_rfl] at h
    exact h
  have hgeq : g = fixedFamilyRecurrentBand ctx :=
    hitCarry_band_unique ctx.hQ hg1 (le_trans (by norm_num) hband.1) hgβ hβ
  rw [hgeq] at hgβ hgconst
  have hall := hitCarry_const_gaps_from_onset hstrict (ctxHitCarry_recursion ctx)
    (ctxHitCarry_pos ctx) hlin hβ hk₁ hgconst
  exact ⟨k₀, honset, hall⟩

/-- **THE PER-CONTEXT EQUIVALENCE (no free lunch, sharpest form)**: at a fixed-family hit,
the E.6/E.7 clean continuation IS the E.14 band-pinned hit-carry linearity.  The carry
reformulation is the residual itself in carry coordinates — neither weaker nor stronger. -/
theorem fixedFamilyCleanContinuation_iff_carryLinear (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) :
    FixedFamilyCleanContinuation ctx ↔ FixedFamilyCarryLinear ctx :=
  ⟨fixedFamilyCarryLinear_of_cleanContinuation ctx hhit,
   fixedFamilyCleanContinuation_of_carryLinear ctx hhit⟩

/-- The onset-free forms are likewise equivalent to each other. -/
theorem fixedFamilyEventualCleanContinuation_iff_carryEventuallyLinear
    (ctx : ActualFailureContext) (hhit : FixedFamilyHit ctx) :
    FixedFamilyEventualCleanContinuation ctx ↔ FixedFamilyCarryEventuallyLinear ctx := by
  have hband := fixedFamilyRecurrentBand_bounds ctx hhit
  have hstrict := ctx.n24CarryData.carry.hits.strict
  constructor
  · rintro ⟨k₁, hg⟩
    obtain ⟨β, hβ, hlin⟩ :=
      hitCarry_linear_of_const_gaps ctx.hQ hstrict (ctxHitCarry_recursion ctx)
        (fun k => le_of_lt (ctxHitCarry_pos ctx k)) (ctxHitCarry_le ctx)
        (le_trans (by norm_num) hband.1) hg
    exact ⟨k₁, β, hβ, hlin⟩
  · rintro ⟨k₀, β, hβ, hlin⟩
    obtain ⟨g, k₁, _, hgβ, hgconst⟩ :=
      hitCarry_const_gaps_of_linear ctx.hQ hstrict (ctxHitCarry_recursion ctx)
        (ctxHitCarry_pos ctx) hlin
    have hg1 : 1 ≤ g := by
      have h := one_le_hitGap hstrict k₁
      rw [hgconst k₁ le_rfl] at h
      exact h
    have hgeq : g = fixedFamilyRecurrentBand ctx :=
      hitCarry_band_unique ctx.hQ hg1 (le_trans (by norm_num) hband.1) hgβ hβ
    rw [hgeq] at hgconst
    exact ⟨k₁, hgconst⟩

/-- The onset form trivially yields the onset-free form. -/
theorem fixedFamilyCarryEventuallyLinear_of_carryLinear (ctx : ActualFailureContext)
    (h : FixedFamilyCarryLinear ctx) : FixedFamilyCarryEventuallyLinear ctx := by
  obtain ⟨k₀, β, _, hβ, hlin⟩ := h
  exact ⟨k₀, β, hβ, hlin⟩

/-- The clean continuation trivially yields the eventual clean continuation. -/
theorem fixedFamilyEventualCleanContinuation_of_cleanContinuation
    (ctx : ActualFailureContext) (h : FixedFamilyCleanContinuation ctx) :
    FixedFamilyEventualCleanContinuation ctx := by
  obtain ⟨k₀, _, hg⟩ := h
  exact ⟨k₀, hg⟩

/-! ## Part 5.  The deep residual and the conditional chains (additive wiring) -/

/-- **The deep carry-linearity residual** — one Prop for all five fixed families, demanded
only at `X > 2^493443` on fixed-family hits. -/
def DeepFixedFamilyCarryLinear : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X → FixedFamilyHit ctx →
    FixedFamilyCarryLinear ctx

/-- The onset-free deep form (recorded for honesty; NOT shown to re-enter the voiding). -/
def DeepFixedFamilyCarryEventuallyLinear : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X → FixedFamilyHit ctx →
    FixedFamilyCarryEventuallyLinear ctx

/-- The deep clean continuation and the deep carry linearity are EQUIVALENT. -/
theorem deepFixedFamilyCleanContinuation_iff_carryLinear :
    DeepFixedFamilyCleanContinuation ↔ DeepFixedFamilyCarryLinear := by
  constructor
  · intro h ctx hX hhit
    exact fixedFamilyCarryLinear_of_cleanContinuation ctx hhit (h ctx hX hhit)
  · intro h ctx hX hhit
    exact fixedFamilyCleanContinuation_of_carryLinear ctx hhit (h ctx hX hhit)

/-- The deep carry linearity is EQUIVALENT to the deep family voiding (the no-free-lunch
pattern, inherited through the clean continuation). -/
theorem deepFixedFamilyCarryLinear_iff_void :
    DeepFixedFamilyCarryLinear ↔ DeepFixedFamilyVoid :=
  deepFixedFamilyCleanContinuation_iff_carryLinear.symm.trans
    deepFixedFamilyCleanContinuation_iff_void

/-- The deep carry linearity is EQUIVALENT to the deep window periodicity supply. -/
theorem deepFixedFamilyCarryLinear_iff_windowPeriodicity :
    DeepFixedFamilyCarryLinear ↔ DeepFixedFamilyWindowPeriodicity :=
  deepFixedFamilyCleanContinuation_iff_carryLinear.symm.trans
    deepFixedFamilyCleanContinuation_iff_windowPeriodicity

/-- The carry linearity discharges the bootstrap successor Prop. -/
theorem deepFixedFamilyWindowPeriodicity_of_carryLinear
    (h : DeepFixedFamilyCarryLinear) : DeepFixedFamilyWindowPeriodicity :=
  deepFixedFamilyWindowPeriodicity_of_cleanContinuation
    (deepFixedFamilyCleanContinuation_iff_carryLinear.mpr h)

/-- Under the carry linearity ALL FIVE fixed families are void at EVERY scale. -/
theorem fixedFamilyHit_void_of_carryLinear (h : DeepFixedFamilyCarryLinear)
    (ctx : ActualFailureContext) : ¬ FixedFamilyHit ctx :=
  fixedFamilyHit_void_of_cleanContinuation
    (deepFixedFamilyCleanContinuation_iff_carryLinear.mpr h) ctx

/-- The carry linearity discharges the wave-6 deep family voiding Prop. -/
theorem deepFixedFamilyVoid_of_carryLinear (h : DeepFixedFamilyCarryLinear) :
    DeepFixedFamilyVoid :=
  deepFixedFamilyCarryLinear_iff_void.mp h

/-- Band-2 `(3,1)` void under the carry linearity. -/
theorem returnFixedFamily_void_of_carryLinear (h : DeepFixedFamilyCarryLinear)
    (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) :=
  returnFixedFamily_void_of_cleanContinuation
    (deepFixedFamilyCleanContinuation_iff_carryLinear.mpr h) ctx

/-- Band-3 `(21,3)` void under the carry linearity. -/
theorem densePackFixedFamily_void_of_carryLinear (h : DeepFixedFamilyCarryLinear)
    (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) :=
  densePackFixedFamily_void_of_cleanContinuation
    (deepFixedFamilyCleanContinuation_iff_carryLinear.mpr h) ctx

/-- Band-4 `(15,1)` void under the carry linearity. -/
theorem towerFP15_1Family_void_of_carryLinear (h : DeepFixedFamilyCarryLinear)
    (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 1) :=
  towerFP15_1Family_void_of_cleanContinuation
    (deepFixedFamilyCleanContinuation_iff_carryLinear.mpr h) ctx

/-- Band-4 `(15,2)` void under the carry linearity. -/
theorem towerFP15_2Family_void_of_carryLinear (h : DeepFixedFamilyCarryLinear)
    (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 2) :=
  towerFP15_2Family_void_of_cleanContinuation
    (deepFixedFamilyCleanContinuation_iff_carryLinear.mpr h) ctx

/-- Band-4 `(105,7)` void under the carry linearity. -/
theorem towerFP105Family_void_of_carryLinear (h : DeepFixedFamilyCarryLinear)
    (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 7) :=
  towerFP105Family_void_of_cleanContinuation
    (deepFixedFamilyCleanContinuation_iff_carryLinear.mpr h) ctx

/-- The collapsed tower escape surface under the carry linearity. -/
theorem towerEscapeLever_of_carryLinear (h : DeepFixedFamilyCarryLinear)
    (ctx : ActualFailureContext) (hesc : TowerEscape ctx) : TowerEscapeLever ctx :=
  towerEscapeLever_of_cleanContinuation
    (deepFixedFamilyCleanContinuation_iff_carryLinear.mpr h) ctx hesc

/-- The tower capstone field bridge under the carry linearity. -/
theorem towerFixedPointResidual_of_carryLinear (h : DeepFixedFamilyCarryLinear)
    (hres : TowerLeverResidual) : TowerFixedPointResidual :=
  towerFixedPointResidual_of_cleanContinuation
    (deepFixedFamilyCleanContinuation_iff_carryLinear.mpr h) hres

/-- The deep carry linearity yields the onset-free deep form (one direction only:
the converse would need the constancy onset back inside the window, which the onset-free
form does not carry — recorded honestly as NOT proved). -/
theorem deepFixedFamilyCarryEventuallyLinear_of_carryLinear
    (h : DeepFixedFamilyCarryLinear) : DeepFixedFamilyCarryEventuallyLinear :=
  fun ctx hX hhit => fixedFamilyCarryEventuallyLinear_of_carryLinear ctx (h ctx hX hhit)

/-- The deep voiding vacuously yields the onset-free deep form (so the onset-free form is
weaker-or-equal; equivalence is NOT claimed). -/
theorem deepFixedFamilyCarryEventuallyLinear_of_void (h : DeepFixedFamilyVoid) :
    DeepFixedFamilyCarryEventuallyLinear :=
  fun ctx hX hhit => absurd hhit (h ctx hX)

/-! ## Part 6.  Machine-readable status (honest) -/

/-- The precise status of the hit-to-hit carry analysis after this module. -/
def hitToHitCarryStatus : List String :=
  [ "THE HIT-TO-HIT CARRY RECURSION (PROVED, unconditional): between consecutive hits " ++
      "the digits are 0 strictly between (HitSequence.adjacent) and 1 at the right " ++
      "endpoint, so with rho_k := R_{a k} (hitCarry): rho_{k+1} = 2^{hitGap k} * rho_k " ++
      "- Q * a(k+1) (hitCarry_succ; ctx forms ctx_hitCarry_succ for EVERY P, " ++
      "ctxHitCarry_recursion at the canonical P = ctx.shell.hrational.choose, the SAME " ++
      "choice class1SlopeDatum routes through).  This is the manuscript E.11 in carry " ++
      "form - the genuine word-side dynamical system.  The E.14 window is formal: " ++
      "0 < rho_k (ctxHitCarry_pos) and rho_k <= Q(a k + 2) (ctxHitCarry_le).",
    "MOD-Q GAP-BLINDNESS (PROVED): Q | rho_k - 2^{a k} * P (hitCarry_modQ_positional) - " ++
      "the residue of the hit carry mod Q is a function of the hit POSITION alone, " ++
      "never of the gap path; no mod-q argument can pin a gap.",
    "THE E.14 LINEARITY BRIDGE (PROVED, BOTH DIRECTIONS): " ++
      "(a) hitCarry_linear_of_const_gaps - constant gaps g + the carry envelope force " ++
      "rho EXACTLY linear from the same onset with slope pinned by (2^g - 1) beta = Q g " ++
      "(the deviation tau_k = (2^g - 1) delta_k - Q g transports by pure doubling and " ++
      "2^{gm} beats the affine envelope, so tau = 0); " ++
      "(b) hitCarry_const_gaps_of_linear - linear rho + positivity force the gaps " ++
      "EVENTUALLY constant with the same pin (upward jumps need rho_k <= Q, dead once " ++
      "rho grows; beta = 0 forces strictly increasing gaps killed by 2^{h-1} <= Qh); " ++
      "(c) hitCarry_band_unique - the pin determines the band uniquely " ++
      "((2^g - 1)/g strictly monotone, hitCarry_band_cross_lt); " ++
      "(d) the iff: hitCarry_eventuallyLinear_iff_const_gaps / " ++
      "ctxHitCarry_eventuallyLinear_iff_const_gaps.",
    "THE ONSET TRANSFER (PROVED - the decisive extra beyond the eventual bridge): in " ++
      "the linear regime with band-pinned slope the jump identity " ++
      "(2^{h_{k+1}} - 2^{h_k}) rho_k = Q h_{k+1} - (2^{h_{k+1}} - 1) beta degenerates " ++
      "at h_{k+1} = g to (2^g - 2^{h_k}) rho_k = 0 with rho_k > 0, so h_k = g - " ++
      "backward rigidity (hitCarry_const_gaps_from_onset): eventual constancy " ++
      "propagates BACK to the linearity onset.  Hence the onset survives and the " ++
      "linearity Prop hits FixedFamilyCleanContinuation exactly.",
    "THE FORMAL DICTIONARY (PROVED shape-match + documented): under constant gap g the " ++
      "per-hit increment delta_k = rho_{k+1} - rho_k obeys the AUTONOMOUS orbit-shaped " ++
      "step delta_{k+1} = 2^g delta_k - Q g (hitCarry_increment_orbitShaped) - the " ++
      "shape of boundedSlopeStep q K = 2^{canonGap q K} K - q under (K, q) <-> " ++
      "(delta, Q*g); the manuscript E.12 fibre slope K_Gamma <-> the per-hit carry " ++
      "increment, AP step H <-> the gap g, modulus q ~ odd part of Q*H (E.5); the " ++
      "band slope is the fixed point (bandSlope_increment_fixed).  The five fixed " ++
      "data's orbit APs (gapOrbit_*) are the H = band instances.",
    "THE NAMED RESIDUAL AND ITS EXACT STRENGTH (the no-free-lunch verdict, PROVED): " ++
      "FixedFamilyCarryLinear ctx (onset a k0 <= X + band-pinned slope + linear tail) " ++
      "is EQUIVALENT per fixed-family context to FixedFamilyCleanContinuation ctx " ++
      "(fixedFamilyCleanContinuation_iff_carryLinear; CC=>CL is the window lock, " ++
      "CL=>CC is eventual constancy + band uniqueness + onset transfer).  Deep forms: " ++
      "deepFixedFamilyCleanContinuation_iff_carryLinear, " ++
      "deepFixedFamilyCarryLinear_iff_void, " ++
      "deepFixedFamilyCarryLinear_iff_windowPeriodicity - the carry reformulation is " ++
      "the residual ITSELF in carry coordinates, not a strictly weaker waypoint.  The " ++
      "onset-free pair (FixedFamilyEventualCleanContinuation <-> " ++
      "FixedFamilyCarryEventuallyLinear, " ++
      "fixedFamilyEventualCleanContinuation_iff_carryEventuallyLinear) is equivalent " ++
      "WITHIN itself but only weaker-or-equal vs the voiding " ++
      "(deepFixedFamilyCarryEventuallyLinear_of_void / _of_carryLinear); its converse " ++
      "(eventual => onset) is NOT claimed - the onset placement is the exact gap.",
    "CONSUMERS WIRED (additive): deepFixedFamilyWindowPeriodicity_of_carryLinear " ++
      "(discharges the bootstrap successor), fixedFamilyHit_void_of_carryLinear (ALL " ++
      "FIVE families void at every scale), deepFixedFamilyVoid_of_carryLinear, the " ++
      "five per-family forms returnFixedFamily_void_of_carryLinear / " ++
      "densePackFixedFamily_void_of_carryLinear / towerFP15_1Family_/_15_2Family_/" ++
      "_105Family_void_of_carryLinear, towerEscapeLever_of_carryLinear, " ++
      "towerFixedPointResidual_of_carryLinear.",
    "TOWER-DATA VERDICT (honest): the formalized class-2 tower atoms were checked for " ++
      "AP/linearity data on the carries.  Class2HallIndexSDRResidual / " ++
      "Class2SemiperiodicIndexSDRResidual / Class2TowerGenuineLeaf carry LANDING data " ++
      "(hlands: hit indices land in the support shell), Hall/counting marginals, and " ++
      "word-side window matches (hmatch vs the rational completion dyadicDigit q0 cen); " ++
      "TowerL31I31Core routes by the orbit band readout (towerClsOfShell); " ++
      "carry_tracks_slopeOrbit tracks the carries mod q only (gap-blind) and its " ++
      "zero-run hypothesis is VOID at actual contexts (actual_zeroRun_void).  NONE of " ++
      "the in-tree tower atoms constrain the integer-carry MAGNITUDE at class-2 routed " ++
      "members, so nothing in-tree supplies FixedFamilyCarryLinear.  What remains is " ++
      "the manuscript's recurrence/SCC persistence (I.3.1 refined recurrent tower " ++
      "classes): recurrent states sit on AP fibres with carries linear in the fibre " ++
      "index - now formalized as the precise named residual, proved EXACTLY equivalent " ++
      "to the clean continuation.",
    "NOT CLOSED (honest): the five fixed families are NOT voided unconditionally here.  " ++
      "The deliverable is the complete carry-side mechanism: the recursion, the E.14 " ++
      "window, the two-sided linearity bridge with the onset transfer, the band " ++
      "uniqueness, and the proof that the E.14 linearity residual is EQUIVALENT to the " ++
      "clean continuation (hence to the voiding at deep scales) - future work must " ++
      "supply the linearity (equivalently the AP-fibre structure of recurrent states) " ++
      "from the unformalized Appendix-E recurrence persistence; no in-tree tower atom " ++
      "does." ]

theorem hitToHitCarryStatus_nonempty : hitToHitCarryStatus ≠ [] := by
  simp [hitToHitCarryStatus]

/-! ## Part 7.  Axiom-cleanliness audit -/

#print axioms hitToHit_two_mul_le_two_pow
#print axioms hitToHit_linear_lt_two_pow
#print axioms hitToHit_antitone_eventually_const
#print axioms hitGap_position_step
#print axioms one_le_hitGap
#print axioms hitCarry_succ
#print axioms hitCarry_pos
#print axioms hitCarry_le
#print axioms hitCarry_modQ_positional
#print axioms bridge_closed_form
#print axioms bridge_beta_nonneg
#print axioms bridge_beta_eq
#print axioms bridge_gap_jump
#print axioms hitCarry_increment_orbitShaped
#print axioms bandSlope_increment_fixed
#print axioms hitCarry_linear_of_const_gaps
#print axioms hitCarry_const_gaps_of_linear
#print axioms hitCarry_band_cross_lt
#print axioms hitCarry_band_unique
#print axioms hitCarry_const_gaps_from_onset
#print axioms hitCarry_eventuallyLinear_iff_const_gaps
#print axioms ctxCarryP_spec
#print axioms ctx_hitCarry_succ
#print axioms ctxHitCarry_recursion
#print axioms ctxHitCarry_pos
#print axioms ctxHitCarry_le
#print axioms ctxHitCarry_modQ_positional
#print axioms ctxHitCarry_eventuallyLinear_iff_const_gaps
#print axioms fixedFamilyCarryLinear_of_cleanContinuation
#print axioms fixedFamilyCleanContinuation_of_carryLinear
#print axioms fixedFamilyCleanContinuation_iff_carryLinear
#print axioms fixedFamilyEventualCleanContinuation_iff_carryEventuallyLinear
#print axioms fixedFamilyCarryEventuallyLinear_of_carryLinear
#print axioms fixedFamilyEventualCleanContinuation_of_cleanContinuation
#print axioms deepFixedFamilyCleanContinuation_iff_carryLinear
#print axioms deepFixedFamilyCarryLinear_iff_void
#print axioms deepFixedFamilyCarryLinear_iff_windowPeriodicity
#print axioms deepFixedFamilyWindowPeriodicity_of_carryLinear
#print axioms fixedFamilyHit_void_of_carryLinear
#print axioms deepFixedFamilyVoid_of_carryLinear
#print axioms returnFixedFamily_void_of_carryLinear
#print axioms densePackFixedFamily_void_of_carryLinear
#print axioms towerFP15_1Family_void_of_carryLinear
#print axioms towerFP15_2Family_void_of_carryLinear
#print axioms towerFP105Family_void_of_carryLinear
#print axioms towerEscapeLever_of_carryLinear
#print axioms towerFixedPointResidual_of_carryLinear
#print axioms deepFixedFamilyCarryEventuallyLinear_of_carryLinear
#print axioms deepFixedFamilyCarryEventuallyLinear_of_void
#print axioms hitToHitCarryStatus_nonempty

end

end Erdos260
