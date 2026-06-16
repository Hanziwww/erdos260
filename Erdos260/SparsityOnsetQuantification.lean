import Erdos260.MultiScaleRigidity
import Erdos260.Erdos260WindowOnesCapstone

/-!
# Sparsity-onset quantification — the obligation-layer threshold anatomy, the producing-side
two-context transport, and the exact onset functions demanded by both consumers
(`SparsityOnsetQuantification`)

This module (NEW; it edits no existing file) mines the quantifier structure of the
sparsity-onset atom at the OBLIGATION layer and delivers the transport/reduction theorems
feeding the two open consumers: the pinned-family sibling gap (`SiblingShellInFiringWindow`,
`MultiScaleRigidity`) and the Return-lane window-ones atom (`ReturnWindowOnesBound`,
`DirtySliceEnvelope` / `Erdos260WindowOnesCapstone`).

## Goal 1 — the obligation-layer verdict (read from the actual Lean definitions)

**What `hlarge` actually says.**  An `ActualFailureContext` carries
`hlarge : manuscriptLargeThresholdOf Q d hd hnonterm ≤ X`, and the threshold computes EXACTLY
(`manuscriptLargeThresholdOf_eq`):

  `manuscriptLargeThresholdOf Q d = firstPositiveSupportThreshold d + 2 ^ (log₂(4Q) + 26)`

(the `max` in the raw definition collapses: the Appendix N start threshold is the carry term
PLUS the word term, so it dominates).  Its content is therefore exactly two facts about the
ctx's OWN shell: carry-largeness (`B + 25 ≤ L`) and support positivity below `X`.  It is a
LOWER bound on the single scale `X` and quantifies NOTHING about shells between the threshold
and `X`: `hfailure` lives at `X` only, and no field of the context (nor of
`GlobalPerFailureAssembly.perFailureAssembly`, nor of `Erdos260ClosureCertificate.perFailure`)
mentions any other scale.  Decisively, the obligation signature does NOT carry the
counterexample sequence `a` or the ratio hypothesis `a n / n → ∞`: inside a ctx the word `d`
is an arbitrary rational-valued nonterminating binary word with ONE failing shell, so the
all-large-scales tail is NOT recoverable from the obligation data.

**What the PRODUCING side has.**  The contradiction machine (`TargetBridge.lean` →
`theoremA_of_analytic_inputs`) never builds a context from "failure at one X" alone: the
genuine counterexample word `tailDigit a N` has sparse shells at ALL sufficiently large
scales (`counterexample_shellsAtAllLargeScales`), and Theorem A refutes failure at EVERY
dyadic `X ≥ startThreshold` once the obligations are discharged.  So on the producing side a
SECOND context at any sufficiently large scale over the SAME word is constructible — and this
module constructs it: `ObligationScaleFamily` packages a word with an onset-bounded sparsity
tail, `ObligationScaleFamily.ctxAt` builds a genuine `ActualFailureContext` at EVERY scale
`2^L` with `L ≥ scaleFloor = max onset (log₂ threshold + 1)`, and
`counterexampleScaleFamily` instantiates the family for the real counterexample data.  The
two-context transport is `ObligationScaleFamily.twoContext_transport`.

## Goal 1 — the threshold-size verdict (exact)

* `manuscriptLargeThresholdOf_eq`: the exact closed form above.  The threshold depends ONLY on
  `(Q, d)` — NOT on the pin depth `t` and NOT on the context scale.
* `manuscriptLargeThresholdOf_le_linear`: the `Q`-part is explicit and linear,
  `threshold ≤ fPST(d) + 2^28 · Q`.
* `manuscriptLargeThresholdOf_le_pinned`: for pinned families (`Q ≤ 7·2^t`),
  `threshold ≤ fPST(d) + 2^(t+31)`.
* `manuscriptLargeThresholdOf_le_cap`: the conditional cap check — if the word part satisfies
  `fPST(d) ≤ 2^493442` and `Q ≤ 2^493414`, then `threshold ≤ 2^493443` (inside the firing
  window cap).
* **BUT the word part `firstPositiveSupportThreshold d` is an opaque `Classical.choose`
  witness** of `∃ n ≥ 1, d n = 1` (not even the least one): it is `≥ 1`
  (`manuscriptLargeThresholdOf_lower`) and admits NO derivable upper bound.  And decisively:
  even a cap-checkable threshold would NOT close consumer 1, because the sibling needs
  SPARSITY at the window scale, which is supplied by the (uncontrolled) sublinearity onset,
  not by the threshold.  The threshold is the obligation's gate, not the failure supply.

## Goal 2 — consumer 1 (pinned families / `SiblingShellInFiringWindow`)

* `ObligationScaleFamily.siblingShell_of_cover` / `siblingShell_at`: a family with
  `onset ≤ 493443` and `Q ≤ 2^(max onset 5)` supplies the sibling at EVERY context over its
  word — in particular at every `ctxAt` context (`pinned families void there:
  `shellValueDyadic_void_at`, `fixedFamilyHit_void_at`, `towerFifthValue_void_at`,
  `towerThirdsValue_void_at`).
* `multiScaleSiblingSupply_of_coveringFamilies` + `erdos260_of_coveringFamilies`: if every
  deep context is covered by SOME onset-capped family, the full `MultiScaleSiblingSupply`
  fires and the endpoint follows through the wave-6 chain.
* `ObligationScaleFamily.onset_above_cap_of_pinned` (honest, the flip): a PINNED family word
  forces `onset > 493443` — the pin and an onset-capped tail cannot coexist, so no
  unconditional closure is possible by this route; the residual remains EXACTLY the onset
  bound.

## Goal 3 — consumer 2 (`ReturnWindowOnesBound`): the quantified reduction

The demanded envelope is `|returnWindowOnes ctx| + 1 ≤ liftLevelBound X` where
`liftLevelBound` is the INVERSE TOWER (`log*`, `ReturnM2J4Core`) — far smaller than `L + 1`.
The all-scales `c0`-sparsity CANNOT reach it (the provable count is `supportCount d (F+W)`,
which `c0`-sparsity bounds only by `~ c0·(F+W) + 2^onset` — `X`-linear).  The honest
deliverable is the reduction with the EXACT onset function that would suffice:

* `EpsShellSparseFrom d ε L0` — ε-sparsity at all scales `≥ L0` (the ε-version with onset);
  `SparsityOnsetFunction d f` — an onset function `∀ ε > 0, EpsShellSparseFrom d ε (f ε)`
  (`exists_sparsityOnsetFunction_of_sublinear`: the counterexample word HAS one, with
  uncontrolled values).
* `supportCount_le_of_epsSparseFrom` — the counting engine: ε-sparsity with onset `L0` gives
  `supportCount d M ≤ 2^L0·(1+ε) + 2·ε·M` at EVERY scale `M` (dyadic-shell summation).
* `WindowOnesOnsetGate` + `returnWindowOnesBound_of_onsetGate`: the explicit gate
  `2^L0·(1+ε) + 2·ε·(F+W) + 1 ≤ liftLevelBound X` implies `ReturnWindowOnesBound ctx`
  (hence the full `SliceDirtyEnvelope`, via the public `DirtySliceEnvelope` bridges).
* `windowOnesOnsetGate_of_explicit` / `windowOnesOnsetGate_of_onsetFunction`: the split
  sufficient form — `ε ≤ 1`, `2^(L0+2) ≤ liftLevelBound X − 1`, and
  `4·ε·(F+W) ≤ liftLevelBound X − 1`.  Reading it off: the onset must satisfy
  `L0 ≤ log₂(liftLevelBound X − 1) − 2` (DOUBLY small: log of the inverse tower) and
  `ε ≈ (liftLevelBound X)/(4·(F+W))`.  This is the exact quantitative residual.
* `ReturnWindowOnesOnsetSupply` (the NAMED residual, guarded exactly like the capstone's
  `ReturnWindowOnesField`) + `returnWindowOnesField_of_onsetSupply` +
  `Erdos260SparsityOnsetResidual` / `erdos260_of_sparsityOnsetResidual`: the endpoint wiring
  into `Erdos260WindowOnesCapstone`.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only — no existing
module is edited.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The obligation-layer threshold anatomy (goal 1 — exact) -/

/-- **The exact closed form of the obligation threshold**: the `max` in
`manuscriptLargeThresholdOf` collapses (the Appendix N start threshold is the carry term plus
the word term, hence dominates), leaving the word part `firstPositiveSupportThreshold d` plus
the explicit carry part `2^(log₂(4Q) + 26)`.  The threshold depends only on `(Q, d)` — not on
any pin depth `t`, not on the context scale. -/
theorem manuscriptLargeThresholdOf_eq (Q : ℕ) (d : ℕ → ℕ) (hd : BinaryDigits d)
    (hnonterm : ¬ EventuallyZero d) :
    manuscriptLargeThresholdOf Q d hd hnonterm
      = firstPositiveSupportThreshold d hd hnonterm
        + 2 ^ (Nat.log 2 (Q * 4) + 26) := by
  unfold manuscriptLargeThresholdOf appendixNChainCompressionStartThreshold
  rw [max_eq_right (Nat.le_add_left _ _)]
  congr 1

/-- The word part is genuinely present: `fPST(d) + 2^26 ≤ threshold`.  (`fPST` itself is an
opaque `Classical.choose` support witness with `fPST ≥ 1` and `d fPST = 1` — no upper bound
on it is derivable.) -/
theorem manuscriptLargeThresholdOf_lower (Q : ℕ) (d : ℕ → ℕ) (hd : BinaryDigits d)
    (hnonterm : ¬ EventuallyZero d) :
    firstPositiveSupportThreshold d hd hnonterm + 2 ^ 26
      ≤ manuscriptLargeThresholdOf Q d hd hnonterm := by
  rw [manuscriptLargeThresholdOf_eq]
  exact Nat.add_le_add_left (Nat.pow_le_pow_right (by norm_num) (by omega)) _

/-- The carry part of the threshold is explicit and `Q`-linear:
`threshold ≤ fPST(d) + 2^28 · Q`. -/
theorem manuscriptLargeThresholdOf_le_linear (Q : ℕ) (hQ : 0 < Q) (d : ℕ → ℕ)
    (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d) :
    manuscriptLargeThresholdOf Q d hd hnonterm
      ≤ firstPositiveSupportThreshold d hd hnonterm + 2 ^ 28 * Q := by
  rw [manuscriptLargeThresholdOf_eq]
  refine Nat.add_le_add_left ?_ _
  have h1 : (2:ℕ) ^ Nat.log 2 (Q * 4) ≤ Q * 4 := Nat.pow_log_le_self 2 (by omega)
  calc (2:ℕ) ^ (Nat.log 2 (Q * 4) + 26)
      = 2 ^ Nat.log 2 (Q * 4) * 2 ^ 26 := pow_add 2 _ 26
    _ ≤ (Q * 4) * 2 ^ 26 := Nat.mul_le_mul h1 (le_refl _)
    _ = 2 ^ 28 * Q := by ring

/-- **The pinned-family threshold bound**: for a pinned denominator `Q ≤ 7 · 2^t` the carry
part of the threshold is at most `2^(t+31)` — the threshold does NOT depend on `t` beyond the
size of `Q` itself. -/
theorem manuscriptLargeThresholdOf_le_pinned {Q t : ℕ} (hQ7 : Q ≤ 7 * 2 ^ t)
    (d : ℕ → ℕ) (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d) :
    manuscriptLargeThresholdOf Q d hd hnonterm
      ≤ firstPositiveSupportThreshold d hd hnonterm + 2 ^ (t + 31) := by
  rw [manuscriptLargeThresholdOf_eq]
  refine Nat.add_le_add_left ?_ _
  have hle : Q * 4 ≤ 2 ^ (t + 5) := by
    calc Q * 4 ≤ 7 * 2 ^ t * 4 := Nat.mul_le_mul hQ7 (le_refl 4)
      _ = 28 * 2 ^ t := by ring
      _ ≤ 32 * 2 ^ t := Nat.mul_le_mul (by norm_num) (le_refl _)
      _ = 2 ^ (t + 5) := by
          rw [show (32:ℕ) = 2 ^ 5 from rfl, ← pow_add]
          congr 1
          omega
  have hlog : Nat.log 2 (Q * 4) ≤ t + 5 := by
    have h := Nat.log_mono_right (b := 2) hle
    rwa [Nat.log_pow (by norm_num)] at h
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The conditional cap check (the consumer-1 size question, answered exactly)**: if the
word part is below `2^493442` and `Q ≤ 2^493414`, then the whole threshold sits below the
firing-window cap `2^493443`.  Honesty: the word part is an opaque `Classical.choose` and
this hypothesis is NOT discharged anywhere; moreover even a capped threshold supplies no
sparsity at window scales — the failure supply (onset), not the threshold, is binding. -/
theorem manuscriptLargeThresholdOf_le_cap {Q : ℕ} (d : ℕ → ℕ) (hd : BinaryDigits d)
    (hnonterm : ¬ EventuallyZero d)
    (hword : firstPositiveSupportThreshold d hd hnonterm ≤ 2 ^ 493442)
    (hQcap : Q ≤ 2 ^ 493414) :
    manuscriptLargeThresholdOf Q d hd hnonterm ≤ 2 ^ 493443 := by
  rw [manuscriptLargeThresholdOf_eq]
  have h4Q : Q * 4 ≤ 2 ^ 493416 := by
    calc Q * 4 ≤ 2 ^ 493414 * 4 := Nat.mul_le_mul hQcap (le_refl 4)
      _ = 2 ^ 493416 := by
          rw [show (4:ℕ) = 2 ^ 2 from rfl, ← pow_add]
  have hlog : Nat.log 2 (Q * 4) ≤ 493416 := by
    have h := Nat.log_mono_right (b := 2) h4Q
    rwa [Nat.log_pow (by norm_num)] at h
  have hcarry : (2:ℕ) ^ (Nat.log 2 (Q * 4) + 26) ≤ 2 ^ 493442 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsum : (2:ℕ) ^ 493443 = 2 ^ 493442 + 2 ^ 493442 := by
    rw [show (493443 : ℕ) = 493442 + 1 from rfl, pow_succ, Nat.mul_two]
  rw [hsum]
  exact Nat.add_le_add hword hcarry

/-! ## Part 2.  The producing-side scale family and the two-context transport (goal 1/2)

The obligation signature does not carry the counterexample data, but the producing side does:
a word with an onset-bounded all-large-scales sparsity tail yields a GENUINE
`ActualFailureContext` at every sufficiently large dyadic scale.  This is the formal content
of "X was arbitrary beyond a fixed threshold" (manuscript H.5/H.6, ~line 2812): the
manuscript quantifier supplies one context per scale, and the family below packages ALL of
them over one word. -/

/-- **The producing-side scale family**: a rational-valued nonterminating binary word together
with an onset-bounded sparsity tail — exactly the data the bridge layer
(`counterexample_shellsAtAllLargeScales`) extracts from a genuine counterexample, and exactly
what is needed to build failure contexts at every large scale. -/
structure ObligationScaleFamily where
  /-- The denominator. -/
  Q : ℕ
  /-- The digit word. -/
  d : ℕ → ℕ
  hQ : 0 < Q
  hd : BinaryDigits d
  hnonterm : ¬ EventuallyZero d
  hrational :
    ∃ P : ℤ, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)
  /-- The sparsity-tail onset (the uncontrolled quantity). -/
  onset : ℕ
  /-- The all-large-scales sparsity tail at the manuscript constant `c0`. -/
  sparse : ∀ L : ℕ, onset ≤ L → ShellSparseAt d L

namespace ObligationScaleFamily

/-- The obligation threshold of the family word. -/
def threshold (fam : ObligationScaleFamily) : ℕ :=
  manuscriptLargeThresholdOf fam.Q fam.d fam.hd fam.hnonterm

/-- The dyadic log-gate above the threshold. -/
def startLog (fam : ObligationScaleFamily) : ℕ :=
  Nat.log 2 fam.threshold + 1

theorem threshold_lt_pow_startLog (fam : ObligationScaleFamily) :
    fam.threshold < 2 ^ fam.startLog :=
  Nat.lt_pow_succ_log_self (by norm_num) _

/-- The family scale floor: beyond both the sparsity onset and the threshold gate. -/
def scaleFloor (fam : ObligationScaleFamily) : ℕ :=
  max fam.onset fam.startLog

/-- **THE SECOND-CONTEXT CONSTRUCTOR (the two-context transport, producing side)**: at EVERY
scale `2^L` with `L ≥ scaleFloor`, the family word yields a genuine `ActualFailureContext` —
all ten fields, including the obligation-layer `hlarge` and the strict failure `hfailure`. -/
def ctxAt (fam : ObligationScaleFamily) (L : ℕ) (hL : fam.scaleFloor ≤ L) :
    ActualFailureContext where
  Q := fam.Q
  d := fam.d
  X := 2 ^ L
  hQ := fam.hQ
  hd := fam.hd
  hnonterm := fam.hnonterm
  hrational := fam.hrational
  hXdyadic := ⟨L, rfl⟩
  hlarge := by
    have h1 : fam.threshold < 2 ^ fam.startLog := fam.threshold_lt_pow_startLog
    have h2 : (2:ℕ) ^ fam.startLog ≤ 2 ^ L :=
      Nat.pow_le_pow_right (by norm_num) (le_trans (le_max_right _ _) hL)
    exact le_trans h1.le h2
  hfailure := fam.sparse L (le_trans (le_max_left _ _) hL)

@[simp] theorem ctxAt_Q (fam : ObligationScaleFamily) (L : ℕ)
    (hL : fam.scaleFloor ≤ L) : (fam.ctxAt L hL).Q = fam.Q := rfl

@[simp] theorem ctxAt_d (fam : ObligationScaleFamily) (L : ℕ)
    (hL : fam.scaleFloor ≤ L) : (fam.ctxAt L hL).d = fam.d := rfl

@[simp] theorem ctxAt_X (fam : ObligationScaleFamily) (L : ℕ)
    (hL : fam.scaleFloor ≤ L) : (fam.ctxAt L hL).X = 2 ^ L := rfl

/-- **The two-context transport**: over one family word, failure contexts exist at ANY two
scales beyond the floor — the structure the obligation layer alone cannot supply. -/
theorem twoContext_transport (fam : ObligationScaleFamily) {L L' : ℕ}
    (hL : fam.scaleFloor ≤ L) (hL' : fam.scaleFloor ≤ L') :
    ∃ ctx ctx' : ActualFailureContext,
      ctx.d = fam.d ∧ ctx'.d = fam.d ∧ ctx.Q = fam.Q ∧ ctx'.Q = fam.Q ∧
        ctx.X = 2 ^ L ∧ ctx'.X = 2 ^ L' :=
  ⟨fam.ctxAt L hL, fam.ctxAt L' hL', rfl, rfl, rfl, rfl, rfl, rfl⟩

end ObligationScaleFamily

/-- **The family of the genuine counterexample (the producing side, instantiated)**: rational
tail value plus `a n / n → ∞` yield an `ObligationScaleFamily` over `tailDigit a N` — the
onset is the (uncontrolled) `Classical.choose` of the bridge tail
`counterexample_shellsAtAllLargeScales`. -/
def counterexampleScaleFamily {a : ℕ → ℤ} {N Q : ℕ} {P : ℤ} (hQ : 0 < Q)
    (ha : StrictMono a) (hpos : ∀ n : ℕ, N ≤ n → 0 < a n)
    (hratio :
      Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop)
    (hval : realWeightedValue (natBinaryAsReal (tailDigit a N)) = (P : ℝ) / (Q : ℝ)) :
    ObligationScaleFamily where
  Q := Q
  d := tailDigit a N
  hQ := hQ
  hd := tailDigit_binary a N
  hnonterm := (not_eventuallyZero_iff_nonterminating (tailDigit_binary a N)).2
    (tailDigit_nonterminating_of_eventually_pos ha hpos)
  hrational := ⟨P, hval⟩
  onset := Classical.choose (counterexample_shellsAtAllLargeScales ha hpos hratio)
  sparse := Classical.choose_spec (counterexample_shellsAtAllLargeScales ha hpos hratio)

/-- **THE PRODUCING-SIDE QUANTIFIER VERDICT, formalized**: from the genuine counterexample
data, a SECOND failure context over the same word exists at EVERY sufficiently large dyadic
scale.  (The floor combines the sparsity onset and the threshold gate; both are finite, and
neither is bounded by any fixed cap.) -/
theorem counterexample_secondContext_at_all_large_scales {a : ℕ → ℤ} {N Q : ℕ} {P : ℤ}
    (hQ : 0 < Q) (ha : StrictMono a) (hpos : ∀ n : ℕ, N ≤ n → 0 < a n)
    (hratio :
      Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop)
    (hval : realWeightedValue (natBinaryAsReal (tailDigit a N)) = (P : ℝ) / (Q : ℝ)) :
    ∃ L1 : ℕ, ∀ L : ℕ, L1 ≤ L →
      ∃ ctx : ActualFailureContext,
        ctx.d = tailDigit a N ∧ ctx.Q = Q ∧ ctx.X = 2 ^ L := by
  refine ⟨(counterexampleScaleFamily hQ ha hpos hratio hval).scaleFloor,
    fun L hL => ?_⟩
  exact ⟨(counterexampleScaleFamily hQ ha hpos hratio hval).ctxAt L hL, rfl, rfl, rfl⟩

/-! ## Part 3.  Consumer 1: the sibling transport and the conditional voidings -/

namespace ObligationScaleFamily

/-- **The sibling transport (consumer 1)**: an onset-capped family (`onset ≤ 493443`,
`Q ≤ 2^(max onset 5)`) supplies `SiblingShellInFiringWindow` at EVERY context over its word —
the gap of `MultiScaleRigidity`, discharged from the family data. -/
theorem siblingShell_of_cover (fam : ObligationScaleFamily)
    (hcap : fam.onset ≤ 493443) (ctx : ActualFailureContext)
    (hword : ctx.d = fam.d) (hQwin : ctx.Q ≤ 2 ^ max fam.onset 5) :
    SiblingShellInFiringWindow ctx := by
  refine ⟨max fam.onset 5, le_max_right _ _, max_le hcap (by norm_num), hQwin, ?_⟩
  rw [hword]
  exact fam.sparse _ (le_max_left _ _)

/-- The sibling at every family context. -/
theorem siblingShell_at (fam : ObligationScaleFamily)
    (hcap : fam.onset ≤ 493443) (hQwin : fam.Q ≤ 2 ^ max fam.onset 5)
    {L : ℕ} (hL : fam.scaleFloor ≤ L) :
    SiblingShellInFiringWindow (fam.ctxAt L hL) :=
  fam.siblingShell_of_cover hcap (fam.ctxAt L hL) rfl hQwin

/-- Dyadic-value pins void at every context of an onset-capped family. -/
theorem shellValueDyadic_void_at (fam : ObligationScaleFamily)
    (hcap : fam.onset ≤ 493443) (hQwin : fam.Q ≤ 2 ^ max fam.onset 5)
    {L : ℕ} (hL : fam.scaleFloor ≤ L) :
    ¬ ShellValueDyadic (fam.ctxAt L hL) :=
  shellValueDyadic_void_of_sibling _ (fam.siblingShell_at hcap hQwin hL)

/-- All five fixed families void at every context of an onset-capped family. -/
theorem fixedFamilyHit_void_at (fam : ObligationScaleFamily)
    (hcap : fam.onset ≤ 493443) (hQwin : fam.Q ≤ 2 ^ max fam.onset 5)
    {L : ℕ} (hL : fam.scaleFloor ≤ L) :
    ¬ FixedFamilyHit (fam.ctxAt L hL) :=
  fixedFamilyHit_void_of_sibling _ (fam.siblingShell_at hcap hQwin hL)

/-- Fifth-value pins void at every context of an onset-capped family. -/
theorem towerFifthValue_void_at (fam : ObligationScaleFamily)
    (hcap : fam.onset ≤ 493443) (hQwin : fam.Q ≤ 2 ^ max fam.onset 5)
    {L : ℕ} (hL : fam.scaleFloor ≤ L) (t : ℕ) :
    realWeightedValue (natBinaryAsReal (fam.ctxAt L hL).shell.d) ≠ 1 / (5 * 2 ^ t) :=
  towerFifthValue_void_of_sibling _ (fam.siblingShell_at hcap hQwin hL) t

/-- Thirds-value pins void at every context of an onset-capped family. -/
theorem towerThirdsValue_void_at (fam : ObligationScaleFamily)
    (hcap : fam.onset ≤ 493443) (hQwin : fam.Q ≤ 2 ^ max fam.onset 5)
    {L : ℕ} (hL : fam.scaleFloor ≤ L) (t : ℕ) :
    realWeightedValue (natBinaryAsReal (fam.ctxAt L hL).shell.d) ≠ 2 / (3 * 2 ^ t) :=
  towerThirdsValue_void_of_sibling _ (fam.siblingShell_at hcap hQwin hL) t

/-- **The honest flip (no unconditional closure by this route)**: a PINNED family word
(`P/(u·2^t)`, `u ≤ 7`, `t` below the window scale) forces the family onset ABOVE the cap —
the pin and an onset-capped tail cannot coexist (`onset_above_cap_of_rep`, transported). -/
theorem onset_above_cap_of_pinned (fam : ObligationScaleFamily) {u t : ℕ} {P : ℤ}
    (hu7 : u ≤ 7) (hupos : 0 < u)
    (heta : realWeightedValue (natBinaryAsReal fam.d)
      = (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ))
    (ht : t ≤ 2 ^ max fam.onset 5) : 493443 < fam.onset :=
  onset_above_cap_of_rep hu7 hupos fam.hd fam.hnonterm heta fam.sparse ht

end ObligationScaleFamily

/-- **The covering-families supply**: if every deep context is covered by SOME onset-capped
family over its own word, the full multi-scale sibling supply of `MultiScaleRigidity`
fires. -/
theorem multiScaleSiblingSupply_of_coveringFamilies
    (h : ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
      ∃ fam : ObligationScaleFamily,
        fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5) :
    MultiScaleSiblingSupply := by
  intro ctx hX
  obtain ⟨fam, hcap, hword, hQwin⟩ := h ctx hX
  exact fam.siblingShell_of_cover hcap ctx hword hQwin

/-- The consumer-1 conditional endpoint through the covering-families supply. -/
theorem erdos260_of_coveringFamilies
    (h : ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
      ∃ fam : ObligationScaleFamily,
        fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) :
    Erdos260Statement :=
  erdos260_of_multiScaleSiblingSupply
    { supply := multiScaleSiblingSupply_of_coveringFamilies h
      surfaces := surfaces }

/-! ## Part 4.  Consumer 2: the ε-onset counting engine and the quantified reduction -/

/-- **ε-sparsity with onset**: every dyadic shell at scale `≥ L0` is ε-sparse.  This is the
ε-version of the failure tail; the bridge supplies it for every `ε > 0` with UNCONTROLLED
`L0` (`exists_epsShellSparseFrom_of_sublinear`). -/
def EpsShellSparseFrom (d : ℕ → ℕ) (ε : ℝ) (L0 : ℕ) : Prop :=
  ∀ L : ℕ, L0 ≤ L →
    ((supportShell d (2 ^ L)).card : ℝ) ≤ ε * ((2 ^ L : ℕ) : ℝ)

/-- The family tail is the `c0`-instance of ε-sparsity with onset. -/
theorem ObligationScaleFamily.epsShellSparseFrom_c0 (fam : ObligationScaleFamily) :
    EpsShellSparseFrom fam.d erdos260Constants.c0 fam.onset :=
  fun L hL => (fam.sparse L hL).le

/-- Sublinearity gives ε-sparsity with SOME onset, for every `ε > 0`. -/
theorem exists_epsShellSparseFrom_of_sublinear {d : ℕ → ℕ}
    (hsub : DyadicShellSublinearReal d) {ε : ℝ} (hε : 0 < ε) :
    ∃ L0 : ℕ, EpsShellSparseFrom d ε L0 := by
  have h := hsub ε hε
  rw [Filter.eventually_atTop] at h
  obtain ⟨L0, hL0⟩ := h
  exact ⟨L0, fun L hL => (hL0 L hL).le⟩

/-- **An onset function**: a single function `f` bounding the onset for EVERY `ε > 0` — the
exact shape of the residual demanded by consumer 2. -/
def SparsityOnsetFunction (d : ℕ → ℕ) (f : ℝ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → EpsShellSparseFrom d ε (f ε)

/-- The counterexample word HAS an onset function (with uncontrolled values) — choice over
the sublinearity tail. -/
theorem exists_sparsityOnsetFunction_of_sublinear {d : ℕ → ℕ}
    (hsub : DyadicShellSublinearReal d) :
    ∃ f : ℝ → ℕ, SparsityOnsetFunction d f := by
  classical
  refine ⟨fun ε =>
    if h : 0 < ε then Classical.choose (exists_epsShellSparseFrom_of_sublinear hsub h)
    else 0, ?_⟩
  intro ε hε
  simp only [dif_pos hε]
  exact Classical.choose_spec (exists_epsShellSparseFrom_of_sublinear hsub hε)

/-- **The dyadic counting engine, power scales**: ε-sparsity with onset `L0` bounds the FULL
counting function at every power scale: `A_S(2^K) ≤ 2^L0 + ε·2^K` (sub-onset positions paid
in full, each shell above the onset paid at ε). -/
theorem supportCount_pow_le_of_epsSparseFrom {d : ℕ → ℕ} {ε : ℝ} {L0 : ℕ}
    (hε : 0 ≤ ε) (hsp : EpsShellSparseFrom d ε L0) :
    ∀ K : ℕ, L0 ≤ K → (supportCount d (2 ^ K) : ℝ) ≤ 2 ^ L0 + ε * 2 ^ K := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    have hb : supportCount d (2 ^ L0) ≤ 2 ^ L0 := supportIn_card_le d (2 ^ L0)
    have hbR : (supportCount d (2 ^ L0) : ℝ) ≤ (2:ℝ) ^ L0 := by exact_mod_cast hb
    have hnn : (0:ℝ) ≤ ε * (2:ℝ) ^ L0 := mul_nonneg hε (by positivity)
    linarith
  | succ K hK ih =>
    have hstep : supportCount d (2 ^ (K + 1))
        = supportCount d (2 ^ K) + (supportShell d (2 ^ K)).card := by
      rw [pow_succ, Nat.mul_comm]
      exact supportCount_two_mul_eq_add_shell d (2 ^ K)
    have hshR : ((supportShell d (2 ^ K)).card : ℝ) ≤ ε * (2:ℝ) ^ K := by
      have h := hsp K hK
      push_cast at h
      exact h
    have hcastR : (supportCount d (2 ^ (K + 1)) : ℝ)
        = (supportCount d (2 ^ K) : ℝ) + ((supportShell d (2 ^ K)).card : ℝ) := by
      rw [hstep]
      push_cast
      ring
    rw [hcastR]
    have hring : ε * (2:ℝ) ^ (K + 1) = ε * 2 ^ K + ε * 2 ^ K := by ring
    linarith

/-- **The dyadic counting engine, all scales**: ε-sparsity with onset `L0` gives
`A_S(M) ≤ 2^L0·(1+ε) + 2·ε·M` at EVERY scale `M`. -/
theorem supportCount_le_of_epsSparseFrom {d : ℕ → ℕ} {ε : ℝ} {L0 : ℕ}
    (hε : 0 ≤ ε) (hsp : EpsShellSparseFrom d ε L0) (M : ℕ) :
    (supportCount d M : ℝ) ≤ 2 ^ L0 * (1 + ε) + 2 * ε * M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have h0 : supportCount d 0 = 0 := by
      have hsub : supportIn d 0 ⊆ (∅ : Finset ℕ) := by
        intro n hn
        rw [mem_supportIn] at hn
        obtain ⟨h1, h2, _⟩ := hn
        exfalso
        omega
      have hcard := Finset.card_le_card hsub
      simpa [supportCount] using hcard
    rw [h0]
    have hp : (0:ℝ) < (2:ℝ) ^ L0 := by positivity
    push_cast
    nlinarith
  · have hKL0 : L0 ≤ max (Nat.log 2 M + 1) L0 := le_max_right _ _
    have hMle : M ≤ 2 ^ max (Nat.log 2 M + 1) L0 := by
      have h1 : M < 2 ^ (Nat.log 2 M + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
      have h2 : (2:ℕ) ^ (Nat.log 2 M + 1) ≤ 2 ^ max (Nat.log 2 M + 1) L0 :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      exact le_trans h1.le h2
    have hmono : supportCount d M ≤ supportCount d (2 ^ max (Nat.log 2 M + 1) L0) :=
      supportCount_mono d hMle
    have hmonoR : (supportCount d M : ℝ)
        ≤ (supportCount d (2 ^ max (Nat.log 2 M + 1) L0) : ℝ) := by
      exact_mod_cast hmono
    have hbound := supportCount_pow_le_of_epsSparseFrom hε hsp _ hKL0
    have hKsmall : (2:ℕ) ^ max (Nat.log 2 M + 1) L0 ≤ 2 ^ L0 + 2 * M := by
      rcases max_cases (Nat.log 2 M + 1) L0 with ⟨heq, _⟩ | ⟨heq, _⟩
      · rw [heq]
        have hple : 2 ^ Nat.log 2 M ≤ M := Nat.pow_log_le_self 2 (by omega)
        calc (2:ℕ) ^ (Nat.log 2 M + 1) = 2 * 2 ^ Nat.log 2 M := by
              rw [pow_succ, Nat.mul_comm]
          _ ≤ 2 * M := Nat.mul_le_mul (le_refl 2) hple
          _ ≤ 2 ^ L0 + 2 * M := Nat.le_add_left _ _
      · rw [heq]
        exact Nat.le_add_right _ _
    have hKR : (2:ℝ) ^ max (Nat.log 2 M + 1) L0 ≤ (2:ℝ) ^ L0 + 2 * (M:ℝ) := by
      exact_mod_cast hKsmall
    have hmul : ε * (2:ℝ) ^ max (Nat.log 2 M + 1) L0
        ≤ ε * ((2:ℝ) ^ L0 + 2 * (M:ℝ)) :=
      mul_le_mul_of_nonneg_left hKR hε
    have hexp : ε * ((2:ℝ) ^ L0 + 2 * (M:ℝ)) = ε * (2:ℝ) ^ L0 + 2 * ε * (M:ℝ) := by
      ring
    have hgoal : (2:ℝ) ^ L0 * (1 + ε) = (2:ℝ) ^ L0 + ε * (2:ℝ) ^ L0 := by ring
    linarith

/-- **The onset gate (consumer 2, the quantified demand)**: ε-sparsity of the context word
with onset `L0`, against the explicit arithmetic gate
`2^L0·(1+ε) + 2·ε·(F+W) + 1 ≤ liftLevelBound X`.  Note `liftLevelBound` is the INVERSE TOWER
(`log* X`), so the gate forces `L0 ≲ log₂(log* X)` and `ε ≲ (log* X)/(F+W)`. -/
def WindowOnesOnsetGate (ctx : ActualFailureContext) (ε : ℝ) (L0 : ℕ) : Prop :=
  0 ≤ ε ∧ EpsShellSparseFrom ctx.d ε L0 ∧
    (2:ℝ) ^ L0 * (1 + ε) + 2 * ε * (lowScaleCeiling ctx) + 1
      ≤ (liftLevelBound ctx.shell.X : ℝ)

/-- The gate discharges the support-form atom of `DirtySliceEnvelope`. -/
theorem lowScaleSupportBound_of_onsetGate (ctx : ActualFailureContext) {ε : ℝ} {L0 : ℕ}
    (h : WindowOnesOnsetGate ctx ε L0) : LowScaleSupportBound ctx := by
  obtain ⟨hε, hsp, hgate⟩ := h
  have hcount := supportCount_le_of_epsSparseFrom hε hsp (lowScaleCeiling ctx)
  have hreal : (supportCount ctx.d (lowScaleCeiling ctx) : ℝ) + 1
      ≤ (liftLevelBound ctx.shell.X : ℝ) := by linarith
  have hnat : supportCount ctx.d (lowScaleCeiling ctx) + 1
      ≤ liftLevelBound ctx.shell.X := by exact_mod_cast hreal
  unfold LowScaleSupportBound
  exact hnat

/-- **THE REDUCTION (consumer 2)**: the onset gate implies the Return-lane window-ones atom
`ReturnWindowOnesBound`. -/
theorem returnWindowOnesBound_of_onsetGate (ctx : ActualFailureContext) {ε : ℝ} {L0 : ℕ}
    (h : WindowOnesOnsetGate ctx ε L0) : ReturnWindowOnesBound ctx :=
  returnWindowOnesBound_of_lowScaleSupport ctx (lowScaleSupportBound_of_onsetGate ctx h)

/-- The full dirty-slice envelope from the onset gate. -/
theorem sliceDirtyEnvelope_of_onsetGate (ctx : ActualFailureContext) {ε : ℝ} {L0 : ℕ}
    (h : WindowOnesOnsetGate ctx ε L0) : SliceDirtyEnvelope ctx :=
  sliceDirtyEnvelope_of_windowOnesBound ctx (returnWindowOnesBound_of_onsetGate ctx h)

/-- **The split sufficient form (what an onset function must deliver)**: `ε ≤ 1`,
`2^(L0+2) ≤ liftLevelBound X − 1`, and `4·ε·(F+W) ≤ liftLevelBound X − 1` imply the gate —
i.e. the onset must satisfy `L0 ≤ log₂(liftLevelBound X − 1) − 2` (doubly small: a log of the
inverse tower) and `ε` must scale like `(liftLevelBound X)/(F+W)`. -/
theorem windowOnesOnsetGate_of_explicit (ctx : ActualFailureContext) {ε : ℝ} {L0 : ℕ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hsp : EpsShellSparseFrom ctx.d ε L0)
    (hpow : (2:ℝ) ^ (L0 + 2) ≤ (liftLevelBound ctx.shell.X : ℝ) - 1)
    (hlin : 4 * ε * (lowScaleCeiling ctx) ≤ (liftLevelBound ctx.shell.X : ℝ) - 1) :
    WindowOnesOnsetGate ctx ε L0 := by
  refine ⟨hε0, hsp, ?_⟩
  have hp : (0:ℝ) ≤ (2:ℝ) ^ L0 := by positivity
  have hmul : (2:ℝ) ^ L0 * ε ≤ (2:ℝ) ^ L0 * 1 := mul_le_mul_of_nonneg_left hε1 hp
  have hpow1 : (2:ℝ) ^ (L0 + 1) = (2:ℝ) ^ L0 * 2 := by ring
  have hpow2 : (2:ℝ) ^ (L0 + 2) = (2:ℝ) ^ L0 * 4 := by ring
  linarith

/-- The split form against an onset function: pick any `0 < ε ≤ 1` clearing the linear gate;
the onset demand is `2^(f ε + 2) ≤ liftLevelBound X − 1`. -/
theorem windowOnesOnsetGate_of_onsetFunction (ctx : ActualFailureContext) {f : ℝ → ℕ}
    (hf : SparsityOnsetFunction ctx.d f) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hpow : (2:ℝ) ^ (f ε + 2) ≤ (liftLevelBound ctx.shell.X : ℝ) - 1)
    (hlin : 4 * ε * (lowScaleCeiling ctx) ≤ (liftLevelBound ctx.shell.X : ℝ) - 1) :
    WindowOnesOnsetGate ctx ε (f ε) :=
  windowOnesOnsetGate_of_explicit ctx hε0.le hε1 (hf ε hε0) hpow hlin

/-- **THE NAMED ONSET RESIDUAL (consumer 2)**: under the VERBATIM guards of the capstone's
window-ones entry field, some `(ε, L0)` clears the onset gate.  This is the exact onset
content that would discharge `ReturnWindowOnesBound` — and through it the full
`SliceDirtyEnvelope` and the capstone chain. -/
def ReturnWindowOnesOnsetSupply : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    ∃ (ε : ℝ) (L0 : ℕ), WindowOnesOnsetGate ctx ε L0

/-- The onset supply discharges the capstone's window-ones entry field. -/
theorem returnWindowOnesField_of_onsetSupply (h : ReturnWindowOnesOnsetSupply) :
    ReturnWindowOnesField := by
  intro ctx hA hB hC hD
  obtain ⟨ε, L0, hgate⟩ := h ctx hA hB hC hD
  exact returnWindowOnesBound_of_onsetGate ctx hgate

/-- **The consumer-2 endpoint surface**: the onset supply plus the 12 verbatim capstone
fields (as a function of the discharged entry field). -/
structure Erdos260SparsityOnsetResidual where
  /-- The named onset residual (the only content not closed by this module). -/
  onsetSupply : ReturnWindowOnesOnsetSupply
  /-- The remaining capstone surface, given the discharged window-ones entry field. -/
  surfaces : ReturnWindowOnesField → Erdos260WindowOnesResidual

/-- The final statement from the sparsity-onset residual, through the wave-13 capstone. -/
theorem Erdos260SparsityOnsetResidual.toStatement (R : Erdos260SparsityOnsetResidual) :
    Erdos260Statement :=
  erdos260_of_windowOnesResidual
    (R.surfaces (returnWindowOnesField_of_onsetSupply R.onsetSupply))

/-- The consumer-2 conditional endpoint. -/
theorem erdos260_of_sparsityOnsetResidual (R : Erdos260SparsityOnsetResidual) :
    Erdos260Statement :=
  R.toStatement

/-! ## Part 5.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the sparsity-onset quantification module. -/
def sparsityOnsetQuantificationStatus : List String :=
  [ "THE OBLIGATION-LAYER VERDICT (goal 1, read from the actual Lean definitions): " ++
      "hlarge : manuscriptLargeThresholdOf Q d hd hnonterm <= X computes EXACTLY to " ++
      "firstPositiveSupportThreshold d + 2^(log2(4Q) + 26) (manuscriptLargeThresholdOf_eq " ++
      "- the max in the raw definition collapses).  Its content is two facts about the " ++
      "ctx's OWN shell (carry-largeness B+25 <= L and support positivity below X); it is " ++
      "a LOWER bound on the single scale X and says NOTHING about shells between the " ++
      "threshold and X - hfailure lives at X only, and no field of ActualFailureContext, " ++
      "GlobalPerFailureAssembly.perFailureAssembly, or " ++
      "Erdos260ClosureCertificate.perFailure mentions any other scale.  Decisively, the " ++
      "obligation signature does NOT carry the counterexample sequence a or the ratio " ++
      "hypothesis a n / n -> infinity: inside a ctx the word is an arbitrary " ++
      "rational-valued nonterminating binary word with ONE failing shell, so the " ++
      "all-large-scales tail is NOT recoverable from the obligation data.",
    "THE PRODUCING-SIDE VERDICT (goal 1, formalized): the contradiction machine derives " ++
      "the full sparsity tail for the genuine counterexample word " ++
      "(counterexample_shellsAtAllLargeScales) and refutes failure at EVERY dyadic " ++
      "X >= startThreshold; a SECOND ActualFailureContext over the same word IS " ++
      "constructible at every scale 2^L with L >= scaleFloor = max(onset, log2(threshold) " ++
      "+ 1): ObligationScaleFamily.ctxAt builds all ten fields including hlarge and the " ++
      "strict hfailure; counterexampleScaleFamily instantiates the family from the real " ++
      "counterexample data; twoContext_transport / " ++
      "counterexample_secondContext_at_all_large_scales are the transport records.  The " ++
      "manuscript H.5 quantifier ('X arbitrary beyond a fixed threshold') is exactly this " ++
      "family - but its onset constituent is the uncontrolled sublinearity onset, not the " ++
      "threshold.",
    "THE THRESHOLD-SIZE VERDICT (goal 1, exact): threshold = fPST(d) + 2^(log2(4Q)+26); " ++
      "it depends only on (Q, d), NOT on the pin depth t and NOT on the scale.  Q-part: " ++
      "<= 2^28 * Q (manuscriptLargeThresholdOf_le_linear); pinned families Q <= 7*2^t: " ++
      "<= fPST + 2^(t+31) (manuscriptLargeThresholdOf_le_pinned); conditional cap check: " ++
      "fPST <= 2^493442 and Q <= 2^493414 give threshold <= 2^493443 " ++
      "(manuscriptLargeThresholdOf_le_cap).  HONEST: fPST = firstPositiveSupportThreshold " ++
      "is an opaque Classical.choose witness of (exists n >= 1, d n = 1) - NOT the least " ++
      "one - with fPST >= 1 (manuscriptLargeThresholdOf_lower) and NO derivable upper " ++
      "bound.  AND the threshold is not the binding constraint anyway: the sibling needs " ++
      "SPARSITY at a window scale, supplied only by the uncontrolled sublinearity onset.",
    "CONSUMER 1 (sibling gap; conditional, NO closure): an onset-capped family " ++
      "(onset <= 493443, Q <= 2^max(onset,5)) supplies SiblingShellInFiringWindow at " ++
      "EVERY context over its word (siblingShell_of_cover / siblingShell_at), voiding " ++
      "all pinned-value families there (shellValueDyadic_void_at, fixedFamilyHit_void_at, " ++
      "towerFifthValue_void_at, towerThirdsValue_void_at); covering families discharge " ++
      "the full MultiScaleSiblingSupply (multiScaleSiblingSupply_of_coveringFamilies) and " ++
      "the endpoint (erdos260_of_coveringFamilies).  THE FLIP (honest): a pinned family " ++
      "word forces onset > 493443 (onset_above_cap_of_pinned) - the pin and an " ++
      "onset-capped tail cannot coexist, so no unconditional closure is possible by this " ++
      "route; the residual remains EXACTLY the onset bound of MultiScaleRigidity.",
    "CONSUMER 2 (ReturnWindowOnesBound; the quantified reduction, NEW): the demanded " ++
      "envelope liftLevelBound X is the INVERSE TOWER log* X (ReturnM2J4Core), so " ++
      "all-scales c0-sparsity CANNOT reach it (the provable count supportCount d (F+W) " ++
      "is X-linear under c0-sparsity: ~ 2^onset + 2 c0 (F+W)).  The honest reduction: " ++
      "EpsShellSparseFrom d eps L0 (eps-sparsity with onset) gives supportCount d M <= " ++
      "2^L0 (1+eps) + 2 eps M at EVERY M (supportCount_le_of_epsSparseFrom, dyadic shell " ++
      "summation), hence WindowOnesOnsetGate (2^L0 (1+eps) + 2 eps (F+W) + 1 <= " ++
      "liftLevelBound X) implies ReturnWindowOnesBound " ++
      "(returnWindowOnesBound_of_onsetGate) and the full SliceDirtyEnvelope " ++
      "(sliceDirtyEnvelope_of_onsetGate).  Split sufficient form " ++
      "(windowOnesOnsetGate_of_explicit): eps <= 1, 2^(L0+2) <= liftLevelBound X - 1, " ++
      "4 eps (F+W) <= liftLevelBound X - 1 - i.e. the onset function must satisfy " ++
      "f(eps) <= log2(log* X - 1) - 2 with eps ~ (log* X)/(F+W): DOUBLY small.  The " ++
      "counterexample word HAS an onset function with uncontrolled values " ++
      "(exists_sparsityOnsetFunction_of_sublinear).",
    "THE NAMED RESIDUALS AND WIRING (additive only): consumer 2's named atom is " ++
      "ReturnWindowOnesOnsetSupply (the onset gate under the VERBATIM guards of the " ++
      "wave-13 capstone entry field); returnWindowOnesField_of_onsetSupply discharges " ++
      "ReturnWindowOnesField, and Erdos260SparsityOnsetResidual / " ++
      "erdos260_of_sparsityOnsetResidual reach Erdos260Statement through " ++
      "erdos260_of_windowOnesResidual.  Consumer 1's residual remains " ++
      "SiblingShellInFiringWindow / MultiScaleSiblingSupply (MultiScaleRigidity), now " ++
      "dischargeable from covering ObligationScaleFamily data.  Nothing re-proved, no " ++
      "existing file edited, no ctx claimed empty.",
    "WHAT RESISTS AND WHY: both consumers reduce to onset bounds that the formalized " ++
      "structure cannot place - consumer 1 needs the c0-onset under 493443 (refuted on " ++
      "pinned words by onset_above_cap_of_pinned, so only non-pinned words could comply " ++
      "- exactly the contradiction shape, hence genuinely open), consumer 2 needs " ++
      "f(eps) ~ log2(log* X) (doubly small, far below any bound the bridge's " ++
      "filter-extracted onset provides).  The threshold route is closed off exactly: the " ++
      "threshold is checkable-small modulo fPST, but it gates the obligation, not the " ++
      "failure supply." ]

theorem sparsityOnsetQuantificationStatus_nonempty :
    sparsityOnsetQuantificationStatus ≠ [] := by
  simp [sparsityOnsetQuantificationStatus]

/-! ## Part 6.  Axiom-cleanliness audit -/

#print axioms manuscriptLargeThresholdOf_eq
#print axioms manuscriptLargeThresholdOf_lower
#print axioms manuscriptLargeThresholdOf_le_linear
#print axioms manuscriptLargeThresholdOf_le_pinned
#print axioms manuscriptLargeThresholdOf_le_cap
#print axioms ObligationScaleFamily.ctxAt
#print axioms ObligationScaleFamily.twoContext_transport
#print axioms counterexampleScaleFamily
#print axioms counterexample_secondContext_at_all_large_scales
#print axioms ObligationScaleFamily.siblingShell_of_cover
#print axioms ObligationScaleFamily.siblingShell_at
#print axioms ObligationScaleFamily.shellValueDyadic_void_at
#print axioms ObligationScaleFamily.fixedFamilyHit_void_at
#print axioms ObligationScaleFamily.towerFifthValue_void_at
#print axioms ObligationScaleFamily.towerThirdsValue_void_at
#print axioms ObligationScaleFamily.onset_above_cap_of_pinned
#print axioms multiScaleSiblingSupply_of_coveringFamilies
#print axioms erdos260_of_coveringFamilies
#print axioms ObligationScaleFamily.epsShellSparseFrom_c0
#print axioms exists_epsShellSparseFrom_of_sublinear
#print axioms exists_sparsityOnsetFunction_of_sublinear
#print axioms supportCount_pow_le_of_epsSparseFrom
#print axioms supportCount_le_of_epsSparseFrom
#print axioms lowScaleSupportBound_of_onsetGate
#print axioms returnWindowOnesBound_of_onsetGate
#print axioms sliceDirtyEnvelope_of_onsetGate
#print axioms windowOnesOnsetGate_of_explicit
#print axioms windowOnesOnsetGate_of_onsetFunction
#print axioms returnWindowOnesField_of_onsetSupply
#print axioms Erdos260SparsityOnsetResidual.toStatement
#print axioms erdos260_of_sparsityOnsetResidual
#print axioms sparsityOnsetQuantificationStatus_nonempty

end

end Erdos260
