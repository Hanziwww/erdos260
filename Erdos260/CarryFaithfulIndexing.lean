import Erdos260.CarryRecurrence21

/-!
# O2 faithful indexing: the carry transcript determines the digits

This module formalizes the load-bearing *injectivity* claim behind the O2 / RISK b
ambient-support obligation of the Erdős-#260 manuscript (Appendix AD/AK,
`lem:ad-summed-ambient-support`):

> the disjoint phase slices inject into the underlying start/threshold event set,
> the phase being **determined by the endpoint/carry transcript**.

The manuscript states this faithfulness in prose.  Here it is reduced to a clean,
machine-checked statement about the carry recurrence (§21.1) of
`Erdos260.CarryRecurrence21`: the carry transcript `N ↦ R_N` of a digit sequence
`d` (together with the free `0`-th digit) **uniquely determines** `d`.

Concretely, rearranging the recurrence (21.1) `R_{N+1} = 2R_N − Q(N+1)d_{N+1}` gives
the digit-recovery identity `Q(N+1)·d_{N+1} = 2R_N − R_{N+1}`, so once `Q ≠ 0` the
positive-index digits are a function of two consecutive carries.  Iterating:

* `carry_determines_digit`   — one step of recovery;
* `carry_determines_digits`  — the whole positive tail is recovered;
* `carry_faithful_index`     — equal `0`-th digit + equal transcript ⇒ equal sequence;
* `o2_carry_transcript_injective` — the forgetful map `d ↦ (d₀, R_•)` is injective,
  the precise "phase determined by the carry transcript" backbone of O2.

This converts the prose assertion into a `sorry`-free lemma.  It does **not** close
the full O2 atom (the geometric disjointness `M_tot ≤ X·|I_j|` of the ambient slices
remains the open analytic step); it supplies the injectivity half that O2 asserts.
-/

namespace Erdos260.CarryFaithfulIndexing

open Erdos260.CarryRecurrence21

/-- **Digit-recovery identity** — the recurrence (21.1) rearranged: the off-carry
transfer `Q·(N+1)·d_{N+1}` equals the carry drop `2R_N − R_{N+1}`. -/
theorem carry_digit_identity (P₀ Q : ℤ) (d : ℕ → ℤ) (N : ℕ) :
    Q * ((N : ℤ) + 1) * d (N + 1) = 2 * carry P₀ Q d N - carry P₀ Q d (N + 1) := by
  rw [carry_succ]; ring

/-- Two consecutive equal carries (at `N` and `N+1`) of two digit sequences force the
digit at `N+1` to agree, provided `Q ≠ 0`. -/
theorem carry_determines_digit (P₀ Q : ℤ) (d d' : ℕ → ℤ) (N : ℕ) (hQ : Q ≠ 0)
    (hN : carry P₀ Q d N = carry P₀ Q d' N)
    (hN1 : carry P₀ Q d (N + 1) = carry P₀ Q d' (N + 1)) :
    d (N + 1) = d' (N + 1) := by
  have hpos : (0 : ℤ) < (N : ℤ) + 1 := by positivity
  have hcoef : Q * ((N : ℤ) + 1) ≠ 0 := mul_ne_zero hQ hpos.ne'
  have h : Q * ((N : ℤ) + 1) * d (N + 1) = Q * ((N : ℤ) + 1) * d' (N + 1) := by
    calc Q * ((N : ℤ) + 1) * d (N + 1)
        = 2 * carry P₀ Q d N - carry P₀ Q d (N + 1) := carry_digit_identity P₀ Q d N
      _ = 2 * carry P₀ Q d' N - carry P₀ Q d' (N + 1) := by rw [hN, hN1]
      _ = Q * ((N : ℤ) + 1) * d' (N + 1) := (carry_digit_identity P₀ Q d' N).symm
  exact mul_left_cancel₀ hcoef h

/-- **The carry transcript determines every positive-index digit.**  If the carries of
`d` and `d'` agree at every `N` (and `Q ≠ 0`), then `d n = d' n` for all `n ≥ 1`. -/
theorem carry_determines_digits (P₀ Q : ℤ) (d d' : ℕ → ℤ) (hQ : Q ≠ 0)
    (h : ∀ N, carry P₀ Q d N = carry P₀ Q d' N) :
    ∀ n, 1 ≤ n → d n = d' n := by
  intro n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  exact carry_determines_digit P₀ Q d d' N hQ (h N) (h (N + 1))

/-- **Faithful index.**  The carry transcript together with the (free) `0`-th digit is a
*faithful* encoding of the whole digit sequence: equal `0`-th digit and equal transcript
force the sequences to be equal. -/
theorem carry_faithful_index (P₀ Q : ℤ) (d d' : ℕ → ℤ) (hQ : Q ≠ 0)
    (h0 : d 0 = d' 0)
    (h : ∀ N, carry P₀ Q d N = carry P₀ Q d' N) :
    d = d' := by
  funext n
  cases n with
  | zero => exact h0
  | succ m => exact carry_determines_digits P₀ Q d d' hQ h (m + 1) (by omega)

/-- **O2 injectivity backbone (`Q ≠ 0`).**  The forgetful map sending a digit sequence to
its `0`-th digit and its carry transcript, `d ↦ (d 0, N ↦ R_N)`, is injective.  This is the
machine-checked form of the manuscript's "the phase is determined by the carry transcript"
— the injectivity half of the O2 / RISK b ambient-support obligation. -/
theorem o2_carry_transcript_injective (P₀ Q : ℤ) (hQ : Q ≠ 0) :
    Function.Injective (fun d : ℕ → ℤ => (d 0, carry P₀ Q d)) := by
  intro d d' h
  have h0 : d 0 = d' 0 := congrArg Prod.fst h
  have hc : carry P₀ Q d = carry P₀ Q d' := congrArg Prod.snd h
  exact carry_faithful_index P₀ Q d d' hQ h0 (fun N => congrFun hc N)

/-- The genuine (greedy) carry of §21.1 is a faithful encoding too: its digit at each
positive step is read back from two consecutive greedy carries. -/
theorem greedy_digit_from_carry (P₀ Q : ℤ) (N : ℕ) :
    Q * ((N : ℤ) + 1) * greedyDigit P₀ Q (N + 1)
      = 2 * greedyCarry P₀ Q N - greedyCarry P₀ Q (N + 1) := by
  rw [greedyCarry_succ]; ring

end Erdos260.CarryFaithfulIndexing
