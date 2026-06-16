import Erdos260.SparsityOnsetQuantification
import Erdos260.FixedFamilyPeriodicity

/-!
# The onset-bound closure at the covering-family consumer (`OnsetBoundClosure`)

This module (NEW; it edits no existing file) works the single remaining consumer of the
onset function bound: the COVERING-FAMILY lane of `SparsityOnsetQuantification` —

* the consumer: `erdos260_of_coveringFamilies` / `multiScaleSiblingSupply_of_coveringFamilies`,
  whose hypothesis demands, at EVERY deep context (`2^493443 < ctx.X`), an onset-capped
  `ObligationScaleFamily` over the context's word:
  `fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2^(max fam.onset 5)`.

The manuscript's wave-13 patch (subsection "Fixed-cycle instantiation of Proposition 24.3",
plus the E.7 remark "(band-saturated fixed cycles)" and the H.6 onset remark) routes the
fixed-cycle cases through the CONSTANT-density mechanism of Proposition 24.3: along a fixed
certified cycle the per-period ones floor is a fixed constant, so the collision with the
sparsity hypothesis "requires no coordination between the repetition scale and the sparsity
onset" — the onset is controlled by the cycle data alone.  This module formalizes exactly
that instantiation and wires it into the consumer.

## What is PROVED here (all unconditional; no fabrication)

### The fixed-cycle onset bound (the constant-density count, PIN-FREE)

* `bootOnes_pos_of_nonterminating` — a non-terminating word that is eventually `p`-periodic
  carries at least ONE one per period window (the backward/forward orbit of any hit tiles
  the tail).
* `periodic_no_sparse_shell` — **THE ONSET BOUND**: a word with eventual period
  `p ≤ 2^19 = 524288` and periodicity onset `x` has NO `c0`-sparse shell at ANY scale
  `2^L` with `x ≤ 2^L` and `28 ≤ L`.  The count is `|shell| ≥ 2^L/p ≥ 2^(L-19) =
  (32/2^24)·2^L > (17/2^24)·2^L = c0·2^L` — the density floor is CONSTANT (`≥ 1/p`), so
  the sparsity onset of such a word is pushed past EVERY scale: the bound is read off the
  cycle datum `p` alone, not from any dynamic onset function.  (The analytic ceiling of
  the mechanism is `p < 2^24/17 ≈ 986895`; the dyadic-clean cap `2^19` covers every
  certified cycle in tree — the five fixed data have band periods `2, 3, 4`.)
* Decisively pin-free: unlike the in-tree voidings on the window-periodic stratum
  (`pinnedValue_windowPeriodic_void`, `thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven`),
  NO value pin `P/(u·2^t)` with `u ≤ 7` and no `ordCompl[2] Q ≤ 7` guard is consumed —
  arbitrary `Q`, arbitrary word value; only the certified period enters.

### The certified-cycle stratum is VOID at both consumer interfaces

* `CertifiedCycleWindow ctx` — the fixed-cycle stratum: eventual periodicity with onset
  `≤ ctx.X` and period `≤ 2^19` (every fixed certified cycle instantiates this).
* `certifiedCycleWindow_void` — NO failing context lies on the stratum, at EVERY scale
  (no deep-scale floor, no enumeration of the five data consumed).
* `obligationScaleFamily_void_of_periodic` / `obligationScaleFamily_word_aperiodic` —
  NO `ObligationScaleFamily` (ANY onset, ANY `Q`) exists over a certified-cycle-periodic
  word: the family's own sparse tail collides with the constant floor.  Covering families
  are FORCED to be off-cycle — so restricting the consumer's demand to the off-cycle
  stratum discards nothing (`coveringFamily_forces_offCycle`).

### The fixed-cycle instantiation at the five certified data

* `certifiedCycleWindow_of_cleanContinuation` — at a fixed-family hit
  (`(q,K₀) ∈ {(3,1),(21,3),(15,1),(15,2),(105,7)}`) the E.6/E.7 clean continuation
  (`FixedFamilyCleanContinuation`) IS certified-cycle periodicity: period = the recurrent
  band `∈ {2,3,4}` (`fixedFamilyRecurrentBand_bounds`), onset = the continuation onset.
* `fixedFamily_cleanContinuation_void` — the instantiated collision: a fixed-family hit
  with clean continuation is absurd at EVERY scale, pin-free.
* `constGap_continuation_void` — the general certified-cycle form: ANY eventual constant
  hit gap `g` with `0 < g ≤ 2^19` and onset `≤ X` is absurd — every certified cycle
  period in this range is covered, not only the five enumerated bands.

### The consumer wiring (additive; the exact hypothesis shape)

* `coveringDemand_at_certifiedCycleWindow` — the consumer's per-context demand holds
  (vacuously: the context is void) on the certified-cycle stratum.
* `OffCycleCoveringSupply` — **the minimal named residual**: the consumer's verbatim
  covering hypothesis demanded ONLY at deep contexts OFF the certified-cycle stratum.
* `coveringFamilies_of_offCycle` — the residual rebuilds the consumer's FULL hypothesis.
* `coveringFamilies_iff_offCycle` — the reduction is LOSSLESS (mutual implication, no
  strength gap): the consumer's demand is equivalent to its off-cycle restriction.
* `multiScaleSiblingSupply_of_offCycleCovering` / `erdos260_of_offCycleCovering` — the
  consumer's exact endpoint shapes, taken from the residual.

## The honest verdict (read this before consuming)

The covering-family consumer is NOT closed outright — and provably cannot be by this
route alone: the in-tree flip (`ObligationScaleFamily.onset_above_cap_of_pinned`,
re-exported here as `offCycleResidual_pinned_flip`) shows a PINNED family word forces
`onset > 493443`, so on pinned words the demanded family cannot exist; the genuine
counterexample word's onset function is uncontrolled
(`exists_sparsityOnsetFunction_of_sublinear`).  What this module CLOSES is the
fixed-cycle stratum of the demand — the exact cases the manuscript's wave-13 patch routes
through the constant-density instantiation of Proposition 24.3 — and it does so
unconditionally and pin-free, with the consumer rewired to the named off-cycle residual
with NO loss of strength.  What would close the residual: for every deep context off the
certified-cycle stratum, an onset-capped (`≤ 493443`) sparsity tail over the context's
word with `Q` inside the firing window — i.e. exactly the onset function bound at
aperiodic words, which no in-tree statement supplies (the bridge's filter-extracted onset
is uncontrolled, and the obligation layer carries no second scale).

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only — no existing
module is edited.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The ones-per-period supply: non-termination meets eventual periodicity -/

/-- **The ones-per-period floor**: a non-terminating word that is eventually `p`-periodic
(onset `x`) has at least one ONE in the base window `(x, x+p]` — any hit beyond the onset
reduces into the base window along the period orbit, so an all-zero window would force the
word to terminate. -/
theorem bootOnes_pos_of_nonterminating {d : ℕ → ℕ} {x p : ℕ}
    (hnonterm : ¬ EventuallyZero d) (hp : 0 < p)
    (hper : ∀ n, x < n → d (n + p) = d n) :
    1 ≤ bootOnes d x p := by
  by_contra hcon
  have hzero : bootOnes d x p = 0 := by omega
  have hwin : ∀ j, j < p → d (x + j + 1) = 0 := by
    intro j hj
    have hle : d (x + j + 1) ≤ ∑ i ∈ Finset.range p, d (x + i + 1) :=
      Finset.single_le_sum (f := fun i => d (x + i + 1))
        (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
    have hle' : d (x + j + 1) ≤ bootOnes d x p := hle
    omega
  refine hnonterm ⟨x + 1, fun n hn => ?_⟩
  have hdm : p * ((n - (x + 1)) / p) + (n - (x + 1)) % p = n - (x + 1) :=
    Nat.div_add_mod _ _
  have hneq : n = x + (n - (x + 1)) % p + 1 + p * ((n - (x + 1)) / p) := by omega
  rw [hneq, boot_digit_add_mul hper ((n - (x + 1)) / p)
    (x + (n - (x + 1)) % p + 1) (by omega)]
  exact hwin _ (Nat.mod_lt _ hp)

/-! ## Part 2.  The fixed-cycle onset bound: no sparse shell along a certified cycle -/

/-- **THE FIXED-CYCLE ONSET BOUND**: a word with eventual period `p ≤ 2^19` (onset `x`)
has NO `c0`-sparse shell at ANY scale `2^L` with `x ≤ 2^L`, `28 ≤ L`.  The constant
density floor `1/p ≥ 1/2^19 = 32/2^24` beats the sparsity cap `c0 = 17/2^24` at every
scale — the manuscript's "onset-free structure" of the fixed-cycle instantiation of
Proposition 24.3: the bound is computed from the cycle period alone, with no value pin
and no dynamic onset function. -/
theorem periodic_no_sparse_shell {d : ℕ → ℕ} {x p L : ℕ}
    (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d)
    (hp : 0 < p) (hple : p ≤ 524288)
    (hper : ∀ n, x < n → d (n + p) = d n)
    (hx : x ≤ 2 ^ L) (hL : 28 ≤ L) :
    ¬ ShellSparseAt d L := by
  intro hsparse
  have hones : 1 ≤ bootOnes d x p := bootOnes_pos_of_nonterminating hnonterm hp hper
  have hcount : 2 ^ L / p * bootOnes d x p ≤ (supportShell d (2 ^ L)).card :=
    periodic_supportShell_card_lower hd hx hp hper
  have hsplit : (2 : ℕ) ^ L = 2 ^ (L - 19) * 2 ^ 19 := by
    rw [← pow_add]
    congr 1
    omega
  have hdiv : 2 ^ (L - 19) ≤ 2 ^ L / p := by
    refine (Nat.le_div_iff_mul_le hp).mpr ?_
    calc 2 ^ (L - 19) * p ≤ 2 ^ (L - 19) * 524288 := Nat.mul_le_mul (le_refl _) hple
      _ = 2 ^ (L - 19) * 2 ^ 19 := by norm_num
      _ = 2 ^ L := hsplit.symm
  have hcard : 2 ^ (L - 19) ≤ (supportShell d (2 ^ L)).card := by
    calc 2 ^ (L - 19) = 2 ^ (L - 19) * 1 := (mul_one _).symm
      _ ≤ 2 ^ L / p * bootOnes d x p := Nat.mul_le_mul hdiv hones
      _ ≤ (supportShell d (2 ^ L)).card := hcount
  have hsp0 : ((supportShell d (2 ^ L)).card : ℝ)
      < erdos260Constants.c0 * ((2 ^ L : ℕ) : ℝ) := hsparse
  rw [carryWord_c0_eq] at hsp0
  have hcardR : ((2 ^ (L - 19) : ℕ) : ℝ) ≤ ((supportShell d (2 ^ L)).card : ℝ) := by
    exact_mod_cast hcard
  have hXR : ((2 ^ L : ℕ) : ℝ) = ((2 ^ (L - 19) : ℕ) : ℝ) * 524288 := by
    rw [hsplit]
    push_cast
    norm_num
  have hpos : (0 : ℝ) < ((2 ^ (L - 19) : ℕ) : ℝ) := by positivity
  rw [hXR] at hsp0
  linarith

/-! ## Part 3.  The certified-cycle stratum is void at both consumer interfaces -/

/-- **The certified-cycle stratum**: the context word is eventually periodic with onset
`≤ ctx.X` and period `≤ 2^19` — the exact word-side trace of a fixed certified cycle
(the five surviving fixed data have band periods `2, 3, 4`; the cap `2^19` covers every
certified period the constant-density mechanism can absorb dyadically). -/
def CertifiedCycleWindow (ctx : ActualFailureContext) : Prop :=
  ∃ x p : ℕ, x ≤ ctx.X ∧ 0 < p ∧ p ≤ 524288 ∧
    ∀ n, x < n → ctx.d (n + p) = ctx.d n

/-- **The stratum voiding at the context interface**: NO failing context lies on the
certified-cycle stratum — at EVERY scale (no deep floor), for EVERY `Q` (no pin, no odd
part guard).  The context's own failing shell collides with the constant floor. -/
theorem certifiedCycleWindow_void (ctx : ActualFailureContext)
    (h : CertifiedCycleWindow ctx) : False := by
  obtain ⟨x, p, hx, hp, hple, hper⟩ := h
  obtain ⟨L, hL⟩ := ctx.hXdyadic
  have hL28 : 28 ≤ L := carryWord_L_ge_28 ctx hL
  refine periodic_no_sparse_shell ctx.hd ctx.hnonterm hp hple hper
    (by rw [← hL]; exact hx) hL28 ?_
  show ((supportShell ctx.d (2 ^ L)).card : ℝ)
      < erdos260Constants.c0 * ((2 ^ L : ℕ) : ℝ)
  rw [← hL]
  exact ctx.hfailure

/-- The certified-cycle stratum sits inside the bootstrap's window-periodic stratum
(the period cap `2^19` is far below `X/2 ≥ 2^27`). -/
theorem windowPeriodic_of_certifiedCycleWindow (ctx : ActualFailureContext)
    (h : CertifiedCycleWindow ctx) : WindowPeriodic ctx := by
  obtain ⟨x, p, hx, hp, hple, hper⟩ := h
  obtain ⟨L, hL⟩ := ctx.hXdyadic
  have hL28 : 28 ≤ L := carryWord_L_ge_28 ctx hL
  have h2p : 2 * p ≤ ctx.X := by
    rw [hL]
    calc 2 * p ≤ 2 * 524288 := by omega
      _ = 2 ^ 20 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ⟨x, p, hx, hp, h2p, hper⟩

/-- **The stratum voiding at the family interface**: NO `ObligationScaleFamily` — ANY
onset, ANY `Q` — exists over a word with eventual period `p ≤ 2^19`: the family's own
all-large-scales sparse tail collides with the constant floor at any scale past both the
family onset and the periodicity onset. -/
theorem obligationScaleFamily_void_of_periodic (fam : ObligationScaleFamily)
    {x p : ℕ} (hp : 0 < p) (hple : p ≤ 524288)
    (hper : ∀ n, x < n → fam.d (n + p) = fam.d n) : False := by
  set L : ℕ := max (max fam.onset x) 28 with hLdef
  have hL28 : 28 ≤ L := le_max_right _ _
  have hxL : x ≤ L := le_trans (le_max_right _ _) (le_max_left _ _)
  have hx : x ≤ 2 ^ L := le_trans hxL (Nat.le_of_lt Nat.lt_two_pow_self)
  have honset : fam.onset ≤ L := le_trans (le_max_left _ _) (le_max_left _ _)
  exact periodic_no_sparse_shell fam.hd fam.hnonterm hp hple hper hx hL28
    (fam.sparse L honset)

/-- Every covering family's word is certified-cycle APERIODIC (the `∀`-form record):
no eventual period `≤ 2^19` from any onset. -/
theorem obligationScaleFamily_word_aperiodic (fam : ObligationScaleFamily) :
    ∀ x p : ℕ, 0 < p → p ≤ 524288 →
      ¬ (∀ n, x < n → fam.d (n + p) = fam.d n) :=
  fun _ p hp hple hper => obligationScaleFamily_void_of_periodic fam hp hple hper

/-- **The restriction is forced**: a context admitting ANY covering family (the consumer's
per-context demand) is automatically OFF the certified-cycle stratum — so demanding the
family only at off-cycle contexts discards nothing. -/
theorem coveringFamily_forces_offCycle (ctx : ActualFailureContext)
    (h : ∃ fam : ObligationScaleFamily,
      fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5) :
    ¬ CertifiedCycleWindow ctx := by
  obtain ⟨fam, _, hword, _⟩ := h
  rintro ⟨x, p, hx, hp, hple, hper⟩
  rw [hword] at hper
  exact obligationScaleFamily_void_of_periodic fam hp hple hper

/-! ## Part 4.  The fixed-cycle instantiation at the certified data -/

/-- **The five certified data land on the stratum**: at a fixed-family hit, the E.6/E.7
clean continuation IS certified-cycle periodicity — period = the recurrent band
`∈ {2, 3, 4}` (`fixedFamilyRecurrentBand_bounds`), onset = the continuation onset.  No
scale hypothesis is consumed (unlike the in-tree `windowPeriodic_of_cleanContinuation`,
which needs `8 ≤ X` for the `2p ≤ X` margin). -/
theorem certifiedCycleWindow_of_cleanContinuation (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hcc : FixedFamilyCleanContinuation ctx) :
    CertifiedCycleWindow ctx := by
  obtain ⟨k₀, honset, hg⟩ := hcc
  obtain ⟨hb2, hb4⟩ := fixedFamilyRecurrentBand_bounds ctx hhit
  have hseq : HitSequence ctx.d ctx.n24CarryData.a := ctx.n24CarryData.carry.hits
  exact ⟨ctx.n24CarryData.a k₀, fixedFamilyRecurrentBand ctx, honset, by omega, by omega,
    digit_periodic_of_const_gaps ctx.hd hseq hg⟩

/-- **THE FIXED-CYCLE INSTANTIATION, closed**: a fixed-family hit with the E.6/E.7 clean
continuation is absurd at EVERY scale — pin-free (no `u ≤ 7`, no odd-part guard), with no
deep-scale floor and no five-pair value enumeration: the certified band period alone
collides with the context's own failing shell through the constant-density count. -/
theorem fixedFamily_cleanContinuation_void (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hcc : FixedFamilyCleanContinuation ctx) : False :=
  certifiedCycleWindow_void ctx (certifiedCycleWindow_of_cleanContinuation ctx hhit hcc)

/-- **The general certified-cycle collision**: ANY eventual constant hit gap `g` with
`0 < g ≤ 2^19` and window-compatible onset is absurd — every certified cycle period in
the dyadic absorption range is covered, not only the five enumerated bands. -/
theorem constGap_continuation_void (ctx : ActualFailureContext) {k₀ g : ℕ}
    (hg0 : 0 < g) (hgle : g ≤ 524288)
    (honset : ctx.n24CarryData.a k₀ ≤ ctx.X)
    (hgap : ∀ k, k₀ ≤ k → hitGap ctx.n24CarryData.a k = g) : False := by
  have hseq : HitSequence ctx.d ctx.n24CarryData.a := ctx.n24CarryData.carry.hits
  exact certifiedCycleWindow_void ctx
    ⟨ctx.n24CarryData.a k₀, g, honset, hg0, hgle,
      digit_periodic_of_const_gaps ctx.hd hseq hgap⟩

/-! ## Part 5.  The consumer wiring: the off-cycle covering supply -/

/-- The consumer's per-context demand holds on the certified-cycle stratum — vacuously,
because the context itself is void there. -/
theorem coveringDemand_at_certifiedCycleWindow (ctx : ActualFailureContext)
    (hwp : CertifiedCycleWindow ctx) :
    ∃ fam : ObligationScaleFamily,
      fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5 :=
  (certifiedCycleWindow_void ctx hwp).elim

/-- **THE MINIMAL NAMED RESIDUAL**: the covering-family consumer's VERBATIM hypothesis,
demanded only at deep contexts OFF the certified-cycle stratum.  What would supply it: an
onset-capped (`≤ 493443`) all-large-scales sparsity tail over the word of every deep
aperiodic context, with `Q` inside the firing window — exactly the onset function bound
at aperiodic words.  (On pinned words the flip `offCycleResidual_pinned_flip` shows the
demanded family cannot exist, so only non-pinned aperiodic words can comply.) -/
def OffCycleCoveringSupply : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
    ¬ CertifiedCycleWindow ctx →
    ∃ fam : ObligationScaleFamily,
      fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5

/-- The off-cycle residual rebuilds the consumer's FULL covering hypothesis: on-stratum
contexts are void, off-stratum contexts are supplied. -/
theorem coveringFamilies_of_offCycle (h : OffCycleCoveringSupply) :
    ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
      ∃ fam : ObligationScaleFamily,
        fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5 := by
  intro ctx hX
  by_cases hwp : CertifiedCycleWindow ctx
  · exact coveringDemand_at_certifiedCycleWindow ctx hwp
  · exact h ctx hX hwp

/-- **The reduction is LOSSLESS**: the consumer's covering hypothesis is EQUIVALENT to
its off-cycle restriction — no strength gap in either direction. -/
theorem coveringFamilies_iff_offCycle :
    (∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
      ∃ fam : ObligationScaleFamily,
        fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5)
    ↔ OffCycleCoveringSupply := by
  constructor
  · exact fun h ctx hX _ => h ctx hX
  · exact coveringFamilies_of_offCycle

/-- The off-cycle residual discharges the full multi-scale sibling supply — the
consumer's exact intermediate demand (`MultiScaleSiblingSupply`). -/
theorem multiScaleSiblingSupply_of_offCycleCovering (h : OffCycleCoveringSupply) :
    MultiScaleSiblingSupply :=
  multiScaleSiblingSupply_of_coveringFamilies (coveringFamilies_of_offCycle h)

/-- **The consumer endpoint from the off-cycle residual**: `Erdos260Statement` through
the covering-family lane, with the certified-cycle stratum of the demand PROVED and only
the off-cycle covering supply (plus the wave-5 surfaces) consumed. -/
theorem erdos260_of_offCycleCovering (h : OffCycleCoveringSupply)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) :
    Erdos260Statement :=
  erdos260_of_coveringFamilies (coveringFamilies_of_offCycle h) surfaces

/-- The flip transported to the residual (re-export, recorded for the residual's honest
shape): a PINNED family word still forces the onset above the cap — the off-cycle
residual cannot be discharged at pinned words; only non-pinned aperiodic words could
comply. -/
theorem offCycleResidual_pinned_flip (fam : ObligationScaleFamily) {u t : ℕ} {P : ℤ}
    (hu7 : u ≤ 7) (hupos : 0 < u)
    (heta : realWeightedValue (natBinaryAsReal fam.d)
      = (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ))
    (ht : t ≤ 2 ^ max fam.onset 5) : 493443 < fam.onset :=
  fam.onset_above_cap_of_pinned hu7 hupos heta ht

/-! ## Part 6.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the onset-bound closure module. -/
def onsetBoundClosureStatus : List String :=
  [ "THE CONSUMER (located exactly): erdos260_of_coveringFamilies / " ++
      "multiScaleSiblingSupply_of_coveringFamilies (SparsityOnsetQuantification) - at " ++
      "every deep context (2^493443 < ctx.X) it demands an ObligationScaleFamily over " ++
      "the context word with onset <= 493443, ctx.d = fam.d, and ctx.Q <= " ++
      "2^(max fam.onset 5); the discharged supply is MultiScaleSiblingSupply " ++
      "(MultiScaleRigidity), consumed as the four deep pinned-value voidings.",
    "THE FIXED-CYCLE ONSET BOUND (NEW, proved, pin-free): a word with eventual period " ++
      "p <= 2^19 has NO c0-sparse shell at any scale 2^L >= max(onset, 2^28): the " ++
      "constant per-period floor 1/p >= 32/2^24 beats c0 = 17/2^24 at every scale " ++
      "(periodic_no_sparse_shell, from bootOnes_pos_of_nonterminating + " ++
      "periodic_supportShell_card_lower).  This is the manuscript's onset-free " ++
      "constant-density mechanism of the fixed-cycle instantiation of Prop 24.3: the " ++
      "bound reads ONLY the cycle period - no value pin u <= 7, no oddpart(Q) guard, " ++
      "no dynamic onset function, no deep-scale floor.  Analytic ceiling p < 2^24/17; " ++
      "dyadic-clean cap 2^19 covers every certified cycle in tree (bands 2/3/4).",
    "THE STRATUM VOIDINGS (proved): certifiedCycleWindow_void - no failing context " ++
      "lies on the certified-cycle stratum at ANY scale; " ++
      "obligationScaleFamily_void_of_periodic / obligationScaleFamily_word_aperiodic - " ++
      "no covering family (ANY onset, ANY Q) exists over a certified-cycle-periodic " ++
      "word; coveringFamily_forces_offCycle - the consumer demand itself forces the " ++
      "off-cycle stratum, so the residual restriction discards nothing.",
    "THE FIXED-CYCLE INSTANTIATION AT THE FIVE DATA (proved): " ++
      "certifiedCycleWindow_of_cleanContinuation - at (3,1),(21,3),(15,1),(15,2),(105,7) " ++
      "the E.6/E.7 clean continuation IS the stratum (period = band in {2,3,4}, no " ++
      "8 <= X hypothesis); fixedFamily_cleanContinuation_void - hit + clean " ++
      "continuation absurd at EVERY scale, pin-free; constGap_continuation_void - the " ++
      "general form at ANY constant hit gap 0 < g <= 2^19.",
    "THE CONSUMER WIRING (additive, exact shapes): OffCycleCoveringSupply (the minimal " ++
      "named residual: the verbatim covering hypothesis demanded only off the " ++
      "certified-cycle stratum) -> coveringFamilies_of_offCycle rebuilds the full " ++
      "hypothesis -> multiScaleSiblingSupply_of_offCycleCovering / " ++
      "erdos260_of_offCycleCovering are the consumer's exact endpoint shapes.  " ++
      "LOSSLESS: coveringFamilies_iff_offCycle (equivalence, no strength gap).",
    "HONEST VERDICT: the covering-family consumer is NOT closed outright - the " ++
      "fixed-cycle stratum of its demand is now PROVED (vacuous by the constant-density " ++
      "collision) and the demand is losslessly confined to the off-cycle stratum; the " ++
      "residual OffCycleCoveringSupply remains genuinely open: pinned words force " ++
      "onset > 493443 (offCycleResidual_pinned_flip, the in-tree flip), and the " ++
      "bridge's onset function for the genuine counterexample word is uncontrolled " ++
      "(exists_sparsityOnsetFunction_of_sublinear).  WHAT WOULD CLOSE IT: an " ++
      "onset-capped (<= 493443) sparsity tail with Q inside the firing window for " ++
      "every deep context over a non-pinned aperiodic word - the onset function bound " ++
      "at exactly the words where neither the carry rigidity (pin) nor the " ++
      "constant-density floor (cycle) applies." ]

theorem onsetBoundClosureStatus_nonempty : onsetBoundClosureStatus ≠ [] := by
  simp [onsetBoundClosureStatus]

/-! ## Part 7.  Axiom-cleanliness audit -/

#print axioms bootOnes_pos_of_nonterminating
#print axioms periodic_no_sparse_shell
#print axioms certifiedCycleWindow_void
#print axioms windowPeriodic_of_certifiedCycleWindow
#print axioms obligationScaleFamily_void_of_periodic
#print axioms obligationScaleFamily_word_aperiodic
#print axioms coveringFamily_forces_offCycle
#print axioms certifiedCycleWindow_of_cleanContinuation
#print axioms fixedFamily_cleanContinuation_void
#print axioms constGap_continuation_void
#print axioms coveringDemand_at_certifiedCycleWindow
#print axioms coveringFamilies_of_offCycle
#print axioms coveringFamilies_iff_offCycle
#print axioms multiScaleSiblingSupply_of_offCycleCovering
#print axioms erdos260_of_offCycleCovering
#print axioms offCycleResidual_pinned_flip
#print axioms onsetBoundClosureStatus_nonempty

end

end Erdos260
