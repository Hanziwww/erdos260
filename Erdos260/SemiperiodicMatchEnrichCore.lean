import Erdos260.SemiperiodicWindowCore
import Erdos260.RunCylinderBridge
import Erdos260.RunL4I52Core

/-!
# Deriving the §25.1 match: `MatchedDescentWindows` from the actual carry's cylinder geometry

`SemiperiodicWindowCore.lean` (wave-17) reduced the shared DensePack/Tower/Run SDR to the single
named residual `MatchedDescentWindows ctx` — the §25.1 *match*, that each genuine descent window of
the **actual** shell word `ctx.shell.d` agrees pointwise with the residual-center orbit word
`dyadicDigit q₀ a`.  It further observed that this reduces one notch to two cylinder-geometry inputs:

* **(i)** `ctx.shell.d` is the *mask word of its own mask point*, and
* **(ii)** that mask point shares the residual center's depth-`n` dyadic cylinder over the window,

with the equal-cylinder consequence of (ii) already proved in
`RunCylinderBridge.maskWord_eq_dyadicDigit_of_dyadicCylinder`.

This file (NEW; it edits no existing file) **derives** the match rather than carrying it as a
hypothesis, by genuinely *proving (i)* and wiring it through the equal-cylinder bridge.  The honest
result is that `MatchedDescentWindows ctx` is reduced to a **single** irreducible Prop — the §25.1
cylinder match of (ii) — with everything else (including the formerly-residual *periodicity of the
globally non-periodic actual word*) discharged.

## What is genuinely PROVED here (no `sorry`/`axiom`/`admit`/`native_decide`)

* **(i), CLOSED — the mask word of its own mask point.**  `windowCylinderValue d s N` is the integer
  whose `N`-bit binary representation (MSB-first) is `d (s+0), …, d (s+N−1)`, and
  `windowMaskPoint d s N = windowCylinderValue d s N / 2ᴺ` is the corresponding dyadic real.  Then
  `binaryDigitWord_windowMaskPoint`: for a binary word `d` the mask word of `windowMaskPoint d s N`
  recovers `d` on `[0, N)` *exactly* — `binaryDigitWord (windowMaskPoint d s N) j = d (s+j)`.  This is
  the genuine finite binary digit-extraction (`testBit_sumBits`), needing no infinitary uniqueness
  hypothesis: it is a self-contained `N`-bit fact.
* **The match from the equal-cylinder bridge.**  `windowMatch_dyadicDigit_of_cylinder`: if the mask
  point `windowMaskPoint d s N` shares the depth-`N` dyadic cylinder of the rational center `a/q₀`
  (input (ii)), then `WindowMatch d (dyadicDigit q₀ a) s N` holds — the actual word IS the orbit word
  on the window.  Proof: feed (i) and (ii) to `maskWord_eq_dyadicDigit_of_dyadicCylinder`.
* **`MatchedDescentWindows` DERIVED.**  `matchedDescentWindows_of_cylinderMatchData`: packaging the
  per-start cylinder geometry (ii) + the §24 period-density floor + the bounded-period calibration
  into `DescentCylinderMatchData ctx`, the match is built per window and `MatchedDescentWindows ctx`
  follows through `MatchedSemiperiodicWindow.ofDyadicMatch` (periodicity of `dyadicDigit q₀ a` is
  free).  The former hard half — periodicity of the actual non-periodic `ctx.shell.d` — never appears:
  it is the transfer's job, already proved in `SemiperiodicWindowCore`.
* **Canonical residual center.**  `descentCylinderMatchData_canonical` instantiates the packet at the
  *actual* shell's §25.1 residual center `residualCenterOfFailingShell (runFOfShell ctx)` (denominator
  `2Q+1` from the shell), so the only inputs are the genuine geometric ones.  `dyadicDigit_shift`
  records that the per-window center numerators are the `2^{φ}`-shifts of the fixed center — the
  manuscript phase.

## The sharp residual (audit verdict)

After this file the lone surviving residual is `Section251CylinderMatchResidual ctx`:

> under `NoLargeRun ctx` (`runClsOfShell ctx k ≠ 1`, no large run on the genuine starts), the §25.1
> cylinder match data `DescentCylinderMatchData ctx` exists.

`matchedDescentWindows_of_section251` proves `Section251CylinderMatchResidual ctx → NoLargeRun ctx →
MatchedDescentWindows ctx`.  The residual is exactly the **§25.1/25.2 dyadic-cylinder reduction for
the actual carry**: that the actual shell digits in each descent window spell the depth-`(spread+1)`
cylinder index of the (phase-shifted) residual center `a_k/q₀`.  Establishing it requires the carry
relation `M·Qp − ν·D = R` with the singular-square residual bound `|R|·2ⁿ < D·Qp` for the actual
shell windows (the `DirtyCrossing`/`CoareaOldNew` old/new cylinder split, fed to
`Residual.residual_cylinder_dichotomy`); `NoLargeRun` then routes that dichotomy to the
**equal-cylinder** branch — excluding the adjacent-cylinder dense/all-zero blocks (the large runs,
class `1`) and the Lemma 25.2 dense branch — which is precisely where the closed equal-cylinder bridge
of this file applies.  That carry geometry is the genuine irreducible combinatorial core and is the
single remaining input.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

/-! ## Part A — Finite binary digit extraction: the mask word of its own mask point (input (i)) -/

/-- A length-`N` sum of bits is bounded by `2ᴺ`: `∑_{i<N} c i · 2ⁱ < 2ᴺ` whenever each `c i ≤ 1`. -/
theorem sumBits_lt {c : ℕ → ℕ} (hc : ∀ i, c i ≤ 1) :
    ∀ N, (∑ i ∈ Finset.range N, c i * 2 ^ i) < 2 ^ N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h1 : c N * 2 ^ N ≤ 2 ^ N := by
      have : c N * 2 ^ N ≤ 1 * 2 ^ N := Nat.mul_le_mul (hc N) (le_refl (2 ^ N))
      simpa using this
    omega

/-- **Finite binary bit extraction.**  For a bit sequence `c` (`c i ≤ 1`), the `e`-th binary digit of
the integer `∑_{i<N} c i · 2ⁱ` is `c e`: `(∑_{i<N} c i · 2ⁱ) / 2ᵉ % 2 = c e` for `e < N`.  This is the
self-contained `N`-bit content behind "the mask word of its own mask point". -/
theorem testBit_sumBits {c : ℕ → ℕ} (hc : ∀ i, c i ≤ 1) :
    ∀ N e, e < N → (∑ i ∈ Finset.range N, c i * 2 ^ i) / 2 ^ e % 2 = c e := by
  intro N
  induction N with
  | zero => intro e he; exact absurd he (Nat.not_lt_zero e)
  | succ N ih =>
    intro e he
    rw [Finset.sum_range_succ]
    rcases (Nat.lt_succ_iff.mp he).lt_or_eq with he' | he'
    · -- `e < N`: the new top term `c N · 2ᴺ` does not affect bit `e`.
      have hsplit : c N * 2 ^ N = 2 ^ e * (c N * 2 ^ (N - e)) := by
        have hpow : 2 ^ N = 2 ^ e * 2 ^ (N - e) := by
          rw [← pow_add]; congr 1; omega
        rw [hpow]; ring
      rw [hsplit, Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ e)]
      have heven : c N * 2 ^ (N - e) = 2 * (c N * 2 ^ (N - e - 1)) := by
        have hpow : 2 ^ (N - e) = 2 * 2 ^ (N - e - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [hpow]; ring
      rw [heven, Nat.add_mul_mod_self_left]
      exact ih e he'
    · -- `e = N`: bit `N` is `c N` because the lower part is `< 2ᴺ`.
      subst he'
      have hlt : (∑ i ∈ Finset.range e, c i * 2 ^ i) < 2 ^ e := sumBits_lt hc e
      rw [mul_comm (c e) (2 ^ e), Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ e),
        Nat.div_eq_of_lt hlt, Nat.zero_add, Nat.mod_eq_of_lt (by have := hc e; omega)]

/-- The depth-`N` cylinder *value* of a word `d` over the window `[s, s+N)`: the integer whose
`N`-bit MSB-first binary representation is `d (s+0), …, d (s+N−1)`. -/
def windowCylinderValue (d : ℕ → ℕ) (s N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range N, d (s + i) * 2 ^ (N - 1 - i)

/-- The MSB-first window value re-indexed into LSB-first form `∑_{i<N} d(s+(N−1−i))·2ⁱ`. -/
theorem windowCylinderValue_eq_reflect (d : ℕ → ℕ) (s N : ℕ) :
    windowCylinderValue d s N = ∑ i ∈ Finset.range N, d (s + (N - 1 - i)) * 2 ^ i := by
  unfold windowCylinderValue
  rw [← Finset.sum_range_reflect (fun i => d (s + i) * 2 ^ (N - 1 - i)) N]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  have hee : N - 1 - (N - 1 - i) = i := by omega
  simp only [hee]

/-- The window value is a genuine `N`-bit number — it lies in the depth-`N` cylinder index range. -/
theorem windowCylinderValue_lt {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) (s N : ℕ) :
    windowCylinderValue d s N < 2 ^ N := by
  rw [windowCylinderValue_eq_reflect]
  exact sumBits_lt (fun i => hd _) N

/-- **Bit `j` of the window value is `d (s+j)`** — the MSB-first digit-extraction. -/
theorem windowCylinderValue_testBit {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s N j : ℕ} (hj : j < N) :
    windowCylinderValue d s N / 2 ^ (N - 1 - j) % 2 = d (s + j) := by
  rw [windowCylinderValue_eq_reflect]
  have key : (∑ i ∈ Finset.range N, d (s + (N - 1 - i)) * 2 ^ i) / 2 ^ (N - 1 - j) % 2
      = d (s + (N - 1 - (N - 1 - j))) :=
    testBit_sumBits (c := fun i => d (s + (N - 1 - i))) (fun i => hd _) N (N - 1 - j) (by omega)
  rw [key]
  congr 1
  omega

/-! ## Part B — The mask point and input (i) for `binaryDigitWord` -/

/-- The depth-`N` *mask point* of a word `d` over `[s, s+N)`: the dyadic real
`windowCylinderValue d s N / 2ᴺ`, whose first `N` binary digits are `d (s+0), …, d (s+N−1)`. -/
def windowMaskPoint (d : ℕ → ℕ) (s N : ℕ) : ℝ :=
  (windowCylinderValue d s N : ℝ) / (2 : ℝ) ^ N

/-- The mask point is nonnegative. -/
theorem windowMaskPoint_nonneg (d : ℕ → ℕ) (s N : ℕ) : 0 ≤ windowMaskPoint d s N := by
  unfold windowMaskPoint; positivity

/-- The depth-`N` cylinder index of the mask point is exactly the window value. -/
theorem cylinderIndex_windowMaskPoint (d : ℕ → ℕ) (s N : ℕ) :
    cylinderIndex N (windowMaskPoint d s N) = windowCylinderValue d s N := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  unfold cylinderIndex windowMaskPoint
  rw [mul_comm, div_mul_cancel₀ _ h2.ne']
  exact Nat.floor_natCast _

/-- The mask point lies in its own depth-`N` dyadic cylinder, indexed by the window value. -/
theorem dyadicCylinder_windowMaskPoint (d : ℕ → ℕ) (s N : ℕ) :
    DyadicCylinder N (windowCylinderValue d s N) (windowMaskPoint d s N) := by
  have h := dyadicCylinder_cylinderIndex (n := N) (windowMaskPoint_nonneg d s N)
  rwa [cylinderIndex_windowMaskPoint] at h

/--
**(i), CLOSED — the mask word of its own mask point.**

For a binary word `d` (`d i ≤ 1`), the mask word of `windowMaskPoint d s N` recovers `d` on the whole
prefix `[0, N)`: `binaryDigitWord (windowMaskPoint d s N) j = d (s+j)` for `j < N`.
-/
theorem binaryDigitWord_windowMaskPoint {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s N j : ℕ}
    (hj : j < N) :
    binaryDigitWord (windowMaskPoint d s N) j = d (s + j) := by
  rw [binaryDigitWord_eq_cylinderBit hj (cylinderIndex_windowMaskPoint d s N)]
  exact windowCylinderValue_testBit hd hj

/-! ## Part C — Feeding the equal-cylinder bridge: the per-window §25.1 match -/

/--
**The §25.1 window match from the equal-cylinder bridge.**

If the mask point `windowMaskPoint d s N` shares the depth-`N` dyadic cylinder of the rational center
`a/q₀` (input (ii)), then the actual word `d` agrees with the residual-center orbit word
`dyadicDigit q₀ a` on the window: `WindowMatch d (dyadicDigit q₀ a) s N`.  Proof: combine input (i)
(`binaryDigitWord_windowMaskPoint`) with the closed bridge
`maskWord_eq_dyadicDigit_of_dyadicCylinder`.
-/
theorem windowMatch_dyadicDigit_of_cylinder {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1)
    {s N q0 a : ℕ} (hq0 : 0 < q0)
    (hcyl : DyadicCylinder N (windowCylinderValue d s N) ((a : ℝ) / (q0 : ℝ))) :
    WindowMatch d (dyadicDigit q0 a) s N := by
  intro i hi
  have hbridge := maskWord_eq_dyadicDigit_of_dyadicCylinder hq0
    (windowMaskPoint_nonneg d s N)
    (rfl : windowCylinderValue d s N = windowCylinderValue d s N)
    (dyadicCylinder_windowMaskPoint d s N) hcyl i hi
  exact (binaryDigitWord_windowMaskPoint hd hi).symm.trans hbridge

/-- The per-window center numerator is a `2^{φ}`-shift of the fixed center: `dyadicDigit q₀ a` at the
shifted index `s+i` equals `dyadicDigit q₀ (2ˢ·a)` at `i`.  This is the manuscript window *phase* —
the per-start numerator `a k` of the cylinder packet is the `2^{φ_k}`-shift of the residual center. -/
theorem dyadicDigit_shift (q0 a s i : ℕ) :
    dyadicDigit q0 a (s + i) = dyadicDigit q0 (2 ^ s * a) i := by
  have h : 2 ^ (s + i) * a = 2 ^ i * (2 ^ s * a) := by rw [pow_add]; ring
  unfold dyadicDigit dyadicResidue
  rw [h]

/-! ## Part D — Deriving `MatchedDescentWindows` from the §25.1 cylinder geometry -/

/--
**The §25.1 cylinder-match data — the isolated geometric residual.**

For a fixed odd residual-center denominator `q₀ > 1` and a per-start numerator `a k` (the
`2^{φ_k}`-shift of the center), the data packages, for each genuine DensePack start `k`:

* **(ii)** the depth-`(spread+1)` cylinder match — the actual shell digits in the descent window
  `[k+r, k+r+spread]` spell the cylinder index of `a k / q₀`;
* the §24 period-density floor `ρ_D·ord ≤ wt(period)` on the orbit word `dyadicDigit q₀ (a k)`;
* the bounded-period calibration `Classical.choose hXdyadic + ord ≤ spread + 2`.

These are exactly the two cylinder-geometry inputs plus the (Q-calibrated, separately flagged) §24
floor; everything else needed for `MatchedDescentWindows` is derived.
-/
structure DescentCylinderMatchData (ctx : ActualFailureContext) where
  /-- The reduced odd residual-center denominator. -/
  q0 : ℕ
  /-- The per-start center numerator (the `2^{φ_k}`-shifted residual center). -/
  a : ℕ → ℕ
  /-- `q₀ > 1`. -/
  hq0 : 1 < q0
  /-- `q₀` is odd (so `dyadicDigit q₀ ·` is periodic with period `ord_{q₀}(2)`). -/
  hodd : Odd q0
  /-- **(ii) the §25.1 cylinder match** for each genuine start. -/
  hcyl : ∀ k ∈ genuineDensePackStarts ctx,
    DyadicCylinder (proofV4DensePackSpread ctx.shell + 1)
      (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
        (proofV4DensePackSpread ctx.shell + 1))
      ((a k : ℝ) / (q0 : ℝ))
  /-- The §24 period-density floor on the orbit word. -/
  hdens : ∀ k ∈ genuineDensePackStarts ctx,
    manuscriptRhoD * (orderOf (2 : ZMod q0) : ℝ)
      ≤ (windowWeight (dyadicDigit q0 (a k)) 0 (orderOf (2 : ZMod q0)) : ℝ)
  /-- The bounded-period calibration. -/
  hpb : Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod q0)
      ≤ proofV4DensePackSpread ctx.shell + 2

/--
**`MatchedDescentWindows` is DERIVED from the §25.1 cylinder geometry.**

Given the per-start cylinder-match data, each descent window of the *actual* shell word matches the
residual-center orbit word `dyadicDigit q₀ (a k)` (via the equal-cylinder bridge), and
`MatchedSemiperiodicWindow.ofDyadicMatch` supplies the (free) periodicity and the §24 floor, so the
whole `MatchedDescentWindows ctx` follows.  The former residual — periodicity of the globally
non-periodic `ctx.shell.d` — never reappears; it was already discharged by the transfer machinery.
-/
theorem matchedDescentWindows_of_cylinderMatchData (ctx : ActualFailureContext)
    (data : DescentCylinderMatchData ctx) : MatchedDescentWindows ctx := by
  have hd : ∀ i, ctx.shell.d i ≤ 1 := fun i => by
    rcases ctx.shell.hd i with h | h <;> omega
  have hClen : 1 ≤ Classical.choose ctx.shell.hXdyadic := by
    have := ctx.shell_carryLarge; omega
  intro k hk
  have hmatch : WindowMatch ctx.shell.d (dyadicDigit data.q0 (data.a k))
      (k + ctx.n24CarryData.r) (proofV4DensePackSpread ctx.shell + 1) :=
    windowMatch_dyadicDigit_of_cylinder hd (by have := data.hq0; omega) (data.hcyl k hk)
  have hpb := data.hpb
  refine ⟨MatchedSemiperiodicWindow.ofDyadicMatch data.hq0 data.hodd (by omega)
    (data.hdens k hk) hmatch, ?_⟩
  exact hpb

/-! ## Part E — The canonical residual center and the no-large-run characterization -/

/-- The §25.1 residual center of the *actual* failing shell (denominator `2Q+1` from `ctx.shell.Q`),
re-exported from `RunL4I52Core`. -/
def canonicalCenter (ctx : ActualFailureContext) : ResidualCenter :=
  residualCenterOfFailingShell (runFOfShell ctx)

/-- **The §25.1 cylinder packet at the actual shell's canonical residual center.**  Only the genuine
geometric inputs remain: the per-window cylinder match (ii), the §24 floor, and the period
calibration; `q₀ > 1` and oddness are the *derived* reduced data of the actual shell. -/
def descentCylinderMatchData_canonical (ctx : ActualFailureContext)
    (a : ℕ → ℕ)
    (hcyl : ∀ k ∈ genuineDensePackStarts ctx,
      DyadicCylinder (proofV4DensePackSpread ctx.shell + 1)
        (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
          (proofV4DensePackSpread ctx.shell + 1))
        ((a k : ℝ) / ((canonicalCenter ctx).q0 : ℝ)))
    (hdens : ∀ k ∈ genuineDensePackStarts ctx,
      manuscriptRhoD * (orderOf (2 : ZMod (canonicalCenter ctx).q0) : ℝ)
        ≤ (windowWeight (dyadicDigit (canonicalCenter ctx).q0 (a k)) 0
            (orderOf (2 : ZMod (canonicalCenter ctx).q0)) : ℝ))
    (hpb : Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod (canonicalCenter ctx).q0)
        ≤ proofV4DensePackSpread ctx.shell + 2) :
    DescentCylinderMatchData ctx where
  q0 := (canonicalCenter ctx).q0
  a := a
  hq0 := runFOfShell_q0_gt_one ctx
  hodd := runFOfShell_q0_odd ctx
  hcyl := hcyl
  hdens := hdens
  hpb := hpb

/-- The class hypothesis **no large run** on the genuine DensePack starts: the L.4.1 trichotomy never
selects the local-spike (large-run) class `1`.  This is what excludes the adjacent-cylinder
dense/all-zero blocks and the Lemma 25.2 dense branch, leaving the equal-cylinder match. -/
def NoLargeRun (ctx : ActualFailureContext) : Prop :=
  ∀ k ∈ genuineDensePackStarts ctx, runClsOfShell ctx k ≠ 1

/--
**The sharp surviving residual.**

Under no large run, the §25.1 cylinder-match data exists.  This is the genuine combinatorial core —
the dyadic-cylinder reduction for the actual carry (the carry relation `M·Qp − ν·D = R` with the
singular-square bound `|R|·2ⁿ < D·Qp` for the actual shell windows, routed by `NoLargeRun` to the
equal-cylinder branch via `Residual.residual_cylinder_dichotomy`).  Everything downstream of it is
proved.
-/
def Section251CylinderMatchResidual (ctx : ActualFailureContext) : Prop :=
  NoLargeRun ctx → Nonempty (DescentCylinderMatchData ctx)

/-- **`MatchedDescentWindows` from the sharp residual + the no-large-run hypothesis.**  This exhibits
the complete reduction: the only thing left to prove is `Section251CylinderMatchResidual ctx` (the
§25.1 cylinder geometry of the actual carry). -/
theorem matchedDescentWindows_of_section251 (ctx : ActualFailureContext)
    (hnlr : NoLargeRun ctx) (h : Section251CylinderMatchResidual ctx) :
    MatchedDescentWindows ctx :=
  matchedDescentWindows_of_cylinderMatchData ctx (h hnlr).some

/-! ## Part F — Non-vacuity: the new bridge fires on genuine words -/

/-- **Non-vacuity of (i) on the constant word.**  The mask point of the all-ones word recovers `1`s. -/
theorem binaryDigitWord_windowMaskPoint_const {N j : ℕ} (hj : j < N) :
    binaryDigitWord (windowMaskPoint (fun _ => 1) 0 N) j = 1 :=
  binaryDigitWord_windowMaskPoint (fun _ => le_refl 1) hj

/-- **Non-vacuity of (i) on a genuine alternating orbit word.**  The mask point of `dyadicDigit 3 1`
(the `1/3` orbit, the canonical run obstruction word) recovers it exactly on the window — so the
mask-word-of-its-own-mask-point identity is non-trivial, not a constant/zero shortcut. -/
theorem binaryDigitWord_windowMaskPoint_dyadic (s N j : ℕ) (hj : j < N) :
    binaryDigitWord (windowMaskPoint (dyadicDigit 3 1) s N) j = dyadicDigit 3 1 (s + j) :=
  binaryDigitWord_windowMaskPoint (fun i => dyadicDigit_le_one (by norm_num) 1 i) hj

/-! ## Part G — Honest residual inventory -/

/-- The precise status of the §25.1 match after this module. -/
def semiperiodicMatchEnrichResiduals : List String :=
  [ "CLOSED (input (i), the mask word of its own mask point) — binaryDigitWord_windowMaskPoint: for " ++
      "a binary word d, the mask word of windowMaskPoint d s N equals d on [0,N) exactly. Built on " ++
      "the finite N-bit digit extraction testBit_sumBits (∑ c i 2^i bit e = c e); NO infinitary " ++
      "uniqueness hypothesis is needed — it is a self-contained finite fact.",
    "CLOSED (the per-window match) — windowMatch_dyadicDigit_of_cylinder: input (i) + input (ii) " ++
      "(the mask point shares the depth-N cylinder of a/q₀) fed to the closed equal-cylinder bridge " ++
      "RunCylinderBridge.maskWord_eq_dyadicDigit_of_dyadicCylinder give WindowMatch d (dyadicDigit " ++
      "q₀ a) s N — the actual word IS the orbit word on the window.",
    "DERIVED (the headline) — matchedDescentWindows_of_cylinderMatchData: from the per-start " ++
      "DescentCylinderMatchData (the §25.1 cylinder geometry + §24 floor + period calibration), " ++
      "MatchedDescentWindows ctx follows through MatchedSemiperiodicWindow.ofDyadicMatch (periodicity " ++
      "of dyadicDigit q₀ a is free). The formerly-residual periodicity of the globally non-periodic " ++
      "ctx.shell.d NEVER reappears — it is the already-proved transfer's job.",
    "DERIVED (canonical center) — descentCylinderMatchData_canonical: the packet at the actual " ++
      "shell's §25.1 residual center residualCenterOfFailingShell (runFOfShell ctx) (denominator " ++
      "2Q+1 from ctx.shell.Q); q₀>1 and odd are the DERIVED reduced data. dyadicDigit_shift records " ++
      "the per-window numerators as the 2^{φ}-shifts of the fixed center (the manuscript phase).",
    "RESIDUAL (the single irreducible core) — Section251CylinderMatchResidual ctx: NoLargeRun ctx → " ++
      "Nonempty (DescentCylinderMatchData ctx). This is the §25.1/25.2 dyadic-cylinder reduction for " ++
      "the ACTUAL carry: that the actual shell digits in each descent window spell the depth-(spread+" ++
      "1) cylinder index of the phase-shifted residual center a_k/q₀. It requires the carry relation " ++
      "M·Qp − ν·D = R with the singular-square bound |R|·2ⁿ < D·Qp for the actual shell windows " ++
      "(the DirtyCrossing/CoareaOldNew old/new cylinder split, fed to residual_cylinder_dichotomy); " ++
      "NoLargeRun (runClsOfShell ≠ 1) routes the resulting dichotomy to the EQUAL-cylinder branch, " ++
      "excluding the adjacent-cylinder dense/all-zero blocks (the large runs) and the Lemma 25.2 " ++
      "dense branch. matchedDescentWindows_of_section251 closes everything ELSE.",
    "CALIBRATION (ρ_D Q-dependence — flagged, not blocking) — the §24 floor hdens on dyadicDigit q₀ " ++
      "(a k) is the separately flagged 1/(4Q) calibration; the construction here is parametric in " ++
      "manuscriptRhoD and stays correct under either calibration, consuming hdens as an input.",
    "NON-DEGENERATE — binaryDigitWord_windowMaskPoint_const / _dyadic witness the mask-point " ++
      "identity on the all-ones word AND the genuine alternating 1/3 orbit dyadicDigit 3 1; no " ++
      "vacuous/constant-zero shortcut.",
    "REDUCED (wave-19) — DirtyCrossingCylinderCore reduces Section251CylinderMatchResidual to a " ++
      "two-field SingularSquareCertificate via the carry-cylinder reduction " ++
      "dyadicCylinder_center_of_singularSquare. The singular-square bound ALONE excludes the UPPER " ++
      "adjacency kν = kM+1 (cylinder_succ_excluded_of_singularSquare — the window point M/D = kM/2ⁿ " ++
      "is EXACTLY dyadic), so only the CARRY (lower) neighbour kM = kν+1 needs the NoLargeRun " ++
      "boundary-run exclusion. section251CylinderMatchResidual_of_certificate then DERIVES the " ++
      "residual from the certificate's two genuine fields: (D1) hbound |R|·2ⁿ < D·q₀ for the ACTUAL " ++
      "shell windows (the §25.3 Diophantine heart) and (D2) hcarry the NoLargeRun carry routing. The " ++
      "§24 ρ_D period-density floor (the 1/(4Q) Q-calibration) + the bounded-period calibration stay " ++
      "separately FLAGGED, not fixed. Non-vacuous on the 1/3 orbit " ++
      "(singularSquare_reduction_fires_orbit)." ]

theorem semiperiodicMatchEnrichResiduals_nonempty : semiperiodicMatchEnrichResiduals ≠ [] := by
  simp [semiperiodicMatchEnrichResiduals]

/-! ## Part H — Axiom-cleanliness audit -/

#print axioms testBit_sumBits
#print axioms windowCylinderValue_testBit
#print axioms binaryDigitWord_windowMaskPoint
#print axioms windowMatch_dyadicDigit_of_cylinder
#print axioms dyadicDigit_shift
#print axioms matchedDescentWindows_of_cylinderMatchData
#print axioms descentCylinderMatchData_canonical
#print axioms matchedDescentWindows_of_section251
#print axioms binaryDigitWord_windowMaskPoint_dyadic

end

end Erdos260
