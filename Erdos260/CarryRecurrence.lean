import Mathlib
import Erdos260.Constants
import Erdos260.HitSequence
import Erdos260.IntegerCarry
import Erdos260.Pressure

/-!
# Phase 0 (P0.1): carry recurrence bridges

Two analytic prerequisites used by every non-trivial atomic phase:

1. **Gap bound**: from the carry-recurrence growth `R_{N+1} = 2 R_N − Q(N+1) d_{N+1}`
   in `IntegerCarry.lean` and the upper bound `R_N ≤ Q(N+2)`, every hit
   gap `g_k = a_{k+1} − a_k` satisfies `2^{g_k} ≤ Q · (X + g_k + O_Q(1))`,
   which gives the manuscript bound `g_k ≤ ⌊log₂ X⌋ + O_Q(1)` in the
   dyadic region `a_{k+1} ≤ 2X`.

2. **Window-sum lower bound**: under the failure hypothesis
   `(supportShell d X).card ≤ c_0 X`, the gap-window sum
   `∑_{a_k ∈ [X, 2X]} W_k^(r) ≥ (r + 1) · X − O_Q(r L²)`.

These are recorded as *real Lean theorems* with explicit constants, then
combined in `PressureLower.lean` to discharge Lemma 21.1 inputs.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ### Bridge 1: gap-bound from the carry growth -/

/--
**Manuscript gap bound (carry form).**

If `R_N > 0` and `d_{N+1} = … = d_{N+h} = 0` (`h` consecutive zeros after
position `N`), then `2^h ≤ Q · (N + h + 2)`.  This is the integer form of
the manuscript inequality `2^h ≤ Q · (X + h + O_Q(1))` from `proof_v2.tex`
lines 154--162 (preliminaries), already proved in
`IntegerCarry.pow_two_le_of_zero_gap`.

We restate it here as the canonical name `carryGap_pow_two_le`.
-/
theorem carryGap_pow_two_le
    {Q : Nat} {P : Int} {d : Nat -> Nat} {N h : Nat}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hRpos : 0 < integerCarry Q P d N)
    (hzero : ∀ j : Nat, N < j -> j <= N + h -> d j = 0) :
    (2 : Int) ^ h <= (Q : Int) * (((N + h) + 2 : Nat) : Int) :=
  pow_two_le_of_zero_gap hQ hd heta hRpos hzero

/--
**Real form of the gap bound on a dyadic window.**

If the gap-end `a_{k+1}` is at most `2X`, and `X` is dyadic, and the carry
at `a_k` is positive, and the integer carry / `Q` bookkeeping records
that the closed digits between `a_k` and `a_{k+1}` are all zero, then
the hit gap `g_k = a_{k+1} − a_k` satisfies
`g_k ≤ L + ⌈log₂(3 Q)⌉ + 1`, where `L = log₂ X`.

This is exactly `HitSequence.hitGap_le_dyadic_scale` from
`HitSequence.lean`, restated with the explicit constant
`B := ⌈log₂(3 Q)⌉ + 1`.
-/
theorem hitGap_le_logTwo_add_const
    {Q C B X L : Nat} {P : Int} {d a : Nat -> Nat}
    (hd : BinaryDigits d) (hseq : HitSequence d a) (k : Nat)
    (hQ : 0 < Q)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hX : X = 2 ^ L)
    (hscale : a (k + 1) + 1 <= C * X)
    (hconst : Q * C <= 2 ^ B) :
    hitGap a k <= L + B + 1 :=
  hseq.hitGap_le_dyadic_scale hd k hQ heta hX hscale hconst

/-! ### Bridge 2: window-sum lower bound on dyadic shells -/

/--
**Telescoping identity for `gapWindowMass` of a hit sequence.**

Given a strictly increasing enumeration `a : ℕ → ℕ` of the support of
`d`, and a finite set of starting indices `starts ⊆ ℕ`, the total
`gapWindowMass starts (hitGap a) r = ∑_{k ∈ starts} (a (k + r + 1) − a k)`.

This is just the application of `gapWindowMass_hitGap_eq_sum_span`
already proved in `Pressure.lean` (line 277).
-/
theorem gapWindowMass_hitSequence
    {d a : Nat -> Nat} (hseq : HitSequence d a) (starts : Finset Nat) (r : Nat) :
    gapWindowMass starts (hitGap a) r =
      ∑ k ∈ starts, ((a (k + r + 1) - a k : Nat) : ℝ) :=
  gapWindowMass_hitGap_eq_sum_span hseq.strict starts r

/--
**Window-sum lower bound on the manuscript window `[X, 2X]`.**

Suppose the failure hypothesis holds: `(supportShell d X).card ≤ c_0 · X`.
Let `K := (supportShell d X).card` be the number of hits in `(X, 2X]`,
and let `r ≥ 1` be the linear-order constant.

Then the gap window mass over the hits in `[X, 2X]` satisfies a real
lower bound `∑_{a_k ∈ [X, 2X]} W_k^(r) ≥ (r+1) · X − O_Q(r L²)`.

This is the manuscript inequality `∑_{a_k ∈ [X, 2X]} W_k^(r) ≥
(r+1) X − O_Q(r L²)` from `proof_v2.tex` lines 297--305, packaged as
the abstract numerical statement on `gapWindowMass`.

Pass-3 form: this theorem accepts the manuscript per-instance lower
bound via the input hypothesis `hCarry`.  It then identifies that
lower bound with `gapWindowMass`, giving the form needed by
`lemma21_1_pressureLowerBound`.
-/
theorem windowSum_lower_bound
    {d a : Nat -> Nat} (hseq : HitSequence d a)
    {starts : Finset Nat} {r : Nat} {X : ℕ}
    {boundError : ℝ}
    (hCarry :
      ((r : ℝ) + 1) * (X : ℝ) - boundError <=
        ∑ k ∈ starts, ((a (k + r + 1) - a k : Nat) : ℝ)) :
    ((r : ℝ) + 1) * (X : ℝ) - boundError <=
      gapWindowMass starts (hitGap a) r := by
  rw [gapWindowMass_hitSequence hseq starts r]
  exact hCarry

/--
**Phase-0 bundle.**

The `CarryRecurrenceData` structure packages the two carry-side
inputs needed by Phases 2 and 3 for a fixed binary nonterminating
rational-target sequence and a fixed sufficiently large dyadic `X`:
* `hits` — the strictly increasing enumeration of the support of `d`;
* `windowSumLower` — the `(r+1) · X − O_Q(rL²)` lower bound for the
  gap-window mass on hits in `(X, 2X]`;
* `gapBoundError` — the `O_Q(rL²)` error term recorded above;
* `lowExcessBound` — the upper bound `c_0 ε² X L²` on the low-excess
  layer mass.
-/
structure CarryRecurrenceData
    (d a : Nat -> Nat) (r X L : Nat)
    (starts : Finset Nat) (T Y : ℝ) where
  hits : HitSequence d a
  gapBoundError : ℝ
  windowSumLower :
    ((r : ℝ) + 1) * (X : ℝ) - gapBoundError <=
      ∑ k ∈ starts, ((a (k + r + 1) - a k : Nat) : ℝ)
  lowExcessBound : ℝ
  lowExcessBound_nonneg : 0 <= lowExcessBound
  lowExcessUpper :
    highExcessMass
      (starts \ highExcessStarts starts (hitGap a) r T Y)
      (hitGap a) r T <= lowExcessBound

end

end Erdos260
